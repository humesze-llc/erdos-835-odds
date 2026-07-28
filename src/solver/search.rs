//! Chronological-backtracking DPLL over `O_k` (spec section 4).
//!
//! No clause learning in v1. Variable order is minimum remaining values with
//! ties broken by lowest vertex index; value order is lowest permitted colour
//! first. Restarts are not implemented, so completeness is unconditional: the
//! search returns UNSAT only after the space is exhausted, and every early exit
//! returns UNKNOWN.

use super::engine::{Engine, UNASSIGNED};
use super::link::{check_link, LinkPlan, RungVerdict};
use super::{BranchOrder, Config, Outcome, SymmetryMode};
use crate::check;
use crate::combi::Combi;
use crate::interrupt::Interrupt;
use crate::stats::{RungStats, Stats};
use crate::util::{fmt_bytes, Rng};
use crate::witness::Witness;
use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Clone, Copy, Debug)]
struct Decision {
    var: u32,
    mask: u32,
    remaining: u32,
    chosen: u8,
}

#[derive(Serialize, Deserialize)]
struct CheckpointFile {
    schema: u32,
    k: u32,
    mode: String,
    fingerprint: String,
    /// `(vertex, remaining colour mask, chosen colour)` per decision level.
    decisions: Vec<(u32, u32, u8)>,
    decisions_count: u64,
    conflicts: u64,
    propagations: u64,
    backtracks: u64,
    elapsed_ms: u64,
    rng_state: u64,
    link_cursor: u64,
    #[serde(default)]
    orbit_branch: usize,
    /// True if the snapshot was taken while the top decision was in conflict
    /// and the backtrack had not happened yet. Replay must reproduce that
    /// conflict rather than treat it as corruption.
    #[serde(default)]
    in_conflict: bool,
}

/// Partitions of `n` in descending order, deterministically ordered. One per
/// conjugacy class of `S_n`.
fn partitions(n: u32) -> Vec<Vec<u32>> {
    fn go(rem: u32, max: u32, cur: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
        if rem == 0 {
            out.push(cur.clone());
            return;
        }
        let hi = max.min(rem);
        for p in (1..=hi).rev() {
            cur.push(p);
            go(rem - p, p, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    go(n, n, &mut Vec::new(), &mut out);
    out
}

pub struct Solver {
    pub e: Engine,
    decisions: Vec<Decision>,
    interrupt: Interrupt,
    rng: Rng,
    link: Option<LinkPlan>,
    link_scan_guard: u64,
    next_checkpoint: Option<Duration>,
    next_rung: Duration,
    tick: u64,
    resumed_elapsed: Duration,
    orbit_parts: Vec<Vec<u32>>,
    orbit_branch: usize,
    resume_conflict: bool,
}

impl Solver {
    pub fn new(cfg: Config, interrupt: Interrupt) -> Result<Solver> {
        let c = Combi::new(cfg.k)?;
        let stats = Stats::new(
            cfg.k,
            "solve",
            c.num_vertices,
            c.colors,
            c.m,
            cfg.seed,
            cfg.stats_file.as_deref(),
        )?;
        let seed = cfg.seed;
        let branch = cfg.branch_order;
        let t = cfg.link_level;
        let rung_levels = cfg.rung_check.clone();
        let rung_interval = cfg.rung_interval;
        let cp_interval = cfg.checkpoint_interval;
        // t must satisfy 1 <= t <= k-1; outside that range lambda is empty (or
        // k-t underflows) and the link cells stop being distinct vertices.
        let t = c.clamp_link_level(t);
        let link = if branch == BranchOrder::Link {
            Some(LinkPlan::new(&c, t, seed))
        } else {
            None
        };
        let mut e = Engine::new(c, cfg, stats)?;
        for t in &rung_levels {
            e.stats.rungs.insert(*t, RungStats::default());
        }
        Ok(Solver {
            decisions: Vec::new(),
            interrupt,
            rng: Rng::new(seed),
            link,
            link_scan_guard: 0,
            next_checkpoint: cp_interval,
            next_rung: rung_interval,
            tick: 0,
            resumed_elapsed: Duration::ZERO,
            orbit_parts: partitions(e.c.k),
            orbit_branch: 0,
            resume_conflict: false,
            e,
        })
    }

    // -- root ---------------------------------------------------------------

    /// Symmetry breaking (spec section 4, mandatory at root).
    ///
    /// The `k+1` members of `N[v0]` carry distinct colours in any solution, so
    /// a permutation of colour labels puts `v0` at colour 0 and its neighbours,
    /// in increasing vertex-index order, at colours `1..=k`. This removes
    /// solutions only up to relabelling, so it is complete.
    fn root_setup(&mut self) -> Result<bool> {
        if self.e.cfg.symmetry != SymmetryMode::None {
            let m0 = self.e.c.unrank(0);
            self.e.enqueue_assignment(0, m0, 0);
            let mut nb: Vec<(u32, u32)> = self
                .e
                .c
                .neighbors(m0)
                .map(|m| (self.e.c.rank(m), m))
                .collect();
            nb.sort_unstable();
            for (i, (idx, mask)) in nb.iter().enumerate() {
                self.e.enqueue_assignment(*idx, *mask, (i + 1) as u8);
            }
        }
        Ok(self.e.propagate())
    }

    /// `φ(z)` for `z ∈ C_0 = [n] \ T_0`: the colour the root breaking gives to
    /// the neighbour `u_z = C_0 \ {z}` of `v0`. Indexed by position in the
    /// ascending list of `C_0`.
    fn phi(&self) -> Vec<u8> {
        let k = self.e.c.k;
        let c0: Vec<u32> = (k - 1..2 * k - 1).collect();
        let mut us: Vec<(u32, usize)> = c0
            .iter()
            .enumerate()
            .map(|(pos, &z)| {
                let mask = c0
                    .iter()
                    .filter(|&&y| y != z)
                    .fold(0u32, |a, &y| a | (1u32 << y));
                (self.e.c.rank(mask), pos)
            })
            .collect();
        us.sort_unstable();
        let mut phi = vec![0u8; k as usize];
        for (i, (_, pos)) in us.iter().enumerate() {
            phi[*pos] = (i + 1) as u8;
        }
        phi
    }

    /// Apply the orbit branch `b`: fix the colours of the `k` vertices
    /// `λ' ∪ {x}`, `x ∈ C_0`, where `λ' = {0..k-3}`, according to the canonical
    /// permutation of the `b`-th conjugacy class of `Sym(C_0)`.
    fn apply_orbit_branch(&mut self, b: usize) -> bool {
        let k = self.e.c.k as usize;
        let ku = self.e.c.k;
        let c0: Vec<u32> = (ku - 1..2 * ku - 1).collect();
        // λ' = T_0 minus its largest element, i.e. {0, ..., k-3}
        let lam: u32 = (0..k.saturating_sub(2)).fold(0u32, |a, x| a | (1u32 << x));
        let phi = self.phi();
        let parts = &self.orbit_parts[b];
        // canonical h of this cycle type, as consecutive cycles over positions
        let mut h = vec![0usize; k];
        let mut off = 0usize;
        for &p in parts {
            let p = p as usize;
            for j in 0..p {
                h[off + j] = off + (j + 1) % p;
            }
            off += p;
        }
        for (pos, &x) in c0.iter().enumerate() {
            let wmask = lam | (1u32 << x);
            debug_assert_eq!(wmask.count_ones(), self.e.c.r);
            let widx = self.e.c.rank(wmask);
            self.e.enqueue_assignment(widx, wmask, phi[h[pos]]);
        }
        true
    }

    // -- main loop ----------------------------------------------------------

    pub fn run(&mut self) -> Result<Outcome> {
        self.e.stats.observe_memory(self.e.state_bytes());
        if !self.root_setup()? {
            self.finish("UNSAT");
            return Ok(Outcome::Unsat);
        }
        let out = if self.e.cfg.symmetry == SymmetryMode::Orbit {
            self.run_orbit_branches()?
        } else {
            if let Some(p) = self.e.cfg.resume.clone() {
                self.replay(&p)?;
            }
            self.search()?
        };
        if out == Outcome::Sat {
            self.on_sat()?;
        }
        self.finish(out.label());
        Ok(out)
    }

    /// The orbit reduction is a disjunction: the instance is UNSAT only if
    /// every conjugacy-class branch is UNSAT, and any UNKNOWN branch makes the
    /// whole answer UNKNOWN.
    fn run_orbit_branches(&mut self) -> Result<Outcome> {
        let n = self.orbit_parts.len();
        let start = if let Some(p) = self.e.cfg.resume.clone() {
            self.replay_branch_index(&p)?
        } else {
            0
        };
        for b in start..n {
            self.orbit_branch = b;
            if self.e.cfg.verbose > 0 && !self.e.cfg.quiet {
                eprintln!(
                    "orbit branch {}/{}  cycle type {:?}",
                    b + 1,
                    n,
                    self.orbit_parts[b]
                );
            }
            self.e.push_level();
            let ok = self.apply_orbit_branch(b) && self.e.propagate();
            if ok {
                if b == start {
                    if let Some(p) = self.e.cfg.resume.clone() {
                        self.replay(&p)?;
                    }
                }
                match self.search()? {
                    Outcome::Sat => return Ok(Outcome::Sat),
                    Outcome::Unsat => {}
                    o @ Outcome::Unknown(_) => return Ok(o),
                }
            } else {
                self.e.stats.conflict(self.e.conflict_rule);
            }
            self.e.pop_level();
        }
        Ok(Outcome::Unsat)
    }

    fn search(&mut self) -> Result<Outcome> {
        let nv = self.e.c.num_vertices;
        let mut conflict = std::mem::take(&mut self.resume_conflict);
        loop {
            self.tick += 1;
            if self.tick % 256 == 0 {
                if let Some(o) = self.periodic(conflict)? {
                    return Ok(o);
                }
            }

            if conflict {
                self.e.stats.conflict(self.e.conflict_rule);
                if self.e.conflict_log.is_some() {
                    let lvl = self.decisions.len();
                    let rule = crate::stats::RULE_NAMES[self.e.conflict_rule as usize];
                    self.e
                        .log_event(&format!("{{\"e\":\"x\",\"lvl\":{lvl},\"rule\":\"{rule}\"}}"));
                }
                conflict = false;
                loop {
                    let Some(d) = self.decisions.last_mut() else {
                        return Ok(Outcome::Unsat);
                    };
                    let (var, mask) = (d.var, d.mask);
                    d.remaining &= !(1u32 << d.chosen);
                    let rem = d.remaining;
                    self.e.pop_level();
                    if rem != 0 {
                        let c = rem.trailing_zeros() as u8;
                        self.decisions.last_mut().unwrap().chosen = c;
                        self.e.push_level();
                        self.e.stats.decisions += 1;
                        self.log_decision(var, c);
                        self.e.enqueue_assignment(var, mask, c);
                        if !self.e.propagate() {
                            conflict = true;
                        }
                        break;
                    }
                    self.decisions.pop();
                    self.e.stats.backtracks += 1;
                }
                continue;
            }

            if self.e.assigned == nv {
                return Ok(Outcome::Sat);
            }

            let sel = match self.e.cfg.branch_order {
                BranchOrder::Mrv => self.e.select_mrv(),
                BranchOrder::Link => match self.select_link()? {
                    LinkSel::Var(v) => Some(v),
                    LinkSel::Conflict => {
                        conflict = true;
                        continue;
                    }
                    LinkSel::Exhausted => self.e.select_mrv(),
                },
            };
            let Some((v, mask)) = sel else {
                if self.e.assigned == nv {
                    return Ok(Outcome::Sat);
                }
                bail!(
                    "internal: no branching variable but {} of {} vertices are assigned",
                    self.e.assigned,
                    nv
                );
            };
            let d = self.e.eff_dom(v);
            if d == 0 {
                conflict = true;
                continue;
            }
            let c = d.trailing_zeros() as u8;
            self.decisions.push(Decision {
                var: v,
                mask,
                remaining: d,
                chosen: c,
            });
            self.e.push_level();
            self.e.stats.decisions += 1;
            self.log_decision(v, c);
            self.e.enqueue_assignment(v, mask, c);
            if !self.e.propagate() {
                conflict = true;
            }
        }
    }

    fn log_decision(&mut self, v: u32, c: u8) {
        if self.e.conflict_log.is_some() {
            let lvl = self.decisions.len();
            self.e
                .log_event(&format!("{{\"e\":\"d\",\"lvl\":{lvl},\"v\":{v},\"c\":{c}}}"));
        }
    }

    // -- periodic work ------------------------------------------------------

    fn periodic(&mut self, in_conflict: bool) -> Result<Option<Outcome>> {
        let elapsed = self.e.stats.elapsed() + self.resumed_elapsed;

        if self.interrupt.take_dump() {
            self.e.stats.observe_memory(self.e.state_bytes());
            self.e.stats.emit(crate::stats::StatsFormat::Jsonl);
        }
        if self.interrupt.stop_requested() {
            self.checkpoint_now(in_conflict)?;
            return Ok(Some(Outcome::Unknown("interrupted".into())));
        }
        if let Some(t) = self.e.cfg.timeout {
            if elapsed >= t {
                self.checkpoint_now(in_conflict)?;
                return Ok(Some(Outcome::Unknown(format!("timeout after {t:?}"))));
            }
        }
        if let Some(mc) = self.e.cfg.max_conflicts {
            if self.e.stats.conflicts >= mc {
                self.checkpoint_now(in_conflict)?;
                return Ok(Some(Outcome::Unknown(format!("conflict limit {mc}"))));
            }
        }

        let sb = self.e.state_bytes();
        self.e.stats.observe_memory(sb);
        if let Some(lim) = self.e.cfg.memory_limit {
            let used = crate::util::rss_bytes().unwrap_or(sb);
            if used > lim {
                self.checkpoint_now(in_conflict)?;
                return Ok(Some(Outcome::Unknown(format!(
                    "memory limit {} exceeded ({} in use)",
                    fmt_bytes(lim),
                    fmt_bytes(used)
                ))));
            }
        }

        if !self.e.cfg.rung_check.is_empty()
            && self.e.cfg.branch_order == BranchOrder::Mrv
            && elapsed >= self.next_rung
        {
            self.next_rung = elapsed + self.e.cfg.rung_interval;
            if let Some(o) = self.rung_pass()? {
                return Ok(Some(o));
            }
        }

        if let (Some(iv), Some(_)) = (self.e.cfg.checkpoint_interval, &self.e.cfg.checkpoint) {
            let due = self.next_checkpoint.unwrap_or(iv);
            if elapsed >= due {
                self.checkpoint_now(in_conflict)?;
                self.next_checkpoint = Some(elapsed + iv);
                self.e.stats.checkpoint_next = self.next_checkpoint;
            }
        }

        if !self.e.cfg.quiet && self.e.stats.due(self.e.cfg.stats_interval) {
            self.e.stats.emit(self.e.cfg.stats_format);
        }
        Ok(None)
    }

    // -- rungs --------------------------------------------------------------

    /// Sample links at every configured level and check any that happen to be
    /// fully assigned. Under `--branch-order mrv` `completed` normally stays at
    /// zero; that is expected, not a bug (spec section 8).
    fn rung_pass(&mut self) -> Result<Option<Outcome>> {
        let levels = self.e.cfg.rung_check.clone();
        let sample = self.e.cfg.rung_sample;
        for t in levels {
            if t == 0 || t >= self.e.c.k {
                continue;
            }
            let total = self.e.c.link_count(t).max(1);
            for _ in 0..sample {
                let idx = self.rng.below(total);
                let lambda = self.e.c.unrank_lambda(t, idx);
                let cells = self.e.c.link_region(lambda, t);
                let verdict = {
                    let e = &self.e;
                    check_link(&e.c, t, &cells, |v| {
                        let x = e.color[v as usize];
                        if x == UNASSIGNED {
                            None
                        } else {
                            Some(x)
                        }
                    })
                };
                let rs = self.e.stats.rungs.entry(t).or_default();
                rs.checked += 1;
                match verdict {
                    RungVerdict::Incomplete { .. } => {}
                    RungVerdict::Pass => {
                        rs.completed += 1;
                        rs.passed += 1;
                    }
                    RungVerdict::Fail(msg) => {
                        rs.completed += 1;
                        rs.failed += 1;
                        eprintln!(
                            "\nRUNG FAILURE  t={t}  lambda={lambda:#x}  idx={idx}\n  {msg}"
                        );
                        self.e.log_event(&format!(
                            "{{\"e\":\"rung\",\"t\":{t},\"lambda\":{lambda},\"msg\":\"{}\"}}",
                            msg.replace('"', "'")
                        ));
                        return Ok(None);
                    }
                }
            }
        }
        Ok(None)
    }

    // -- link-ordered branching ---------------------------------------------

    fn select_link(&mut self) -> Result<LinkSel> {
        let t = self.e.c.clamp_link_level(self.e.cfg.link_level);
        if !self.e.c.valid_link_level(t) {
            return Ok(LinkSel::Exhausted);
        }
        self.e.maybe_compact_heaps();
        if self.link.is_none() {
            self.link = Some(LinkPlan::new(&self.e.c, t, self.e.cfg.seed));
        }
        self.link_scan_guard = 0;
        loop {
            let (best, complete) = {
                let plan = self.link.as_ref().unwrap();
                let mut best: Option<(u32, u32)> = None;
                let mut all = true;
                for cell in &plan.cells {
                    if self.e.is_assigned(cell.vertex) {
                        continue;
                    }
                    all = false;
                    let p = self.e.eff_dom(cell.vertex).count_ones();
                    match best {
                        None => best = Some((p, cell.vertex)),
                        Some((bp, bv)) if p < bp || (p == bp && cell.vertex < bv) => {
                            best = Some((p, cell.vertex))
                        }
                        _ => {}
                    }
                }
                (best, all)
            };
            if let Some((_, v)) = best {
                return Ok(LinkSel::Var((v, self.e.c.unrank(v))));
            }
            if complete {
                let (lambda, verdict) = {
                    let plan = self.link.as_ref().unwrap();
                    let e = &self.e;
                    (
                        plan.lambda,
                        check_link(&e.c, t, &plan.cells, |v| {
                            let x = e.color[v as usize];
                            if x == UNASSIGNED {
                                None
                            } else {
                                Some(x)
                            }
                        }),
                    )
                };
                let rs = self.e.stats.rungs.entry(t).or_default();
                rs.checked += 1;
                match verdict {
                    RungVerdict::Pass => {
                        rs.completed += 1;
                        rs.passed += 1;
                    }
                    RungVerdict::Fail(msg) => {
                        rs.completed += 1;
                        rs.failed += 1;
                        eprintln!("\nRUNG FAILURE  t={t}  lambda={lambda:#x}\n  {msg}");
                        self.e.conflict_rule = crate::stats::Rule::B;
                        return Ok(LinkSel::Conflict);
                    }
                    RungVerdict::Incomplete { .. } => unreachable!("region reported complete"),
                }
            }
            self.link_scan_guard += 1;
            if self.link_scan_guard > self.e.c.link_count(t).min(1 << 16) {
                return Ok(LinkSel::Exhausted);
            }
            let c = &self.e.c;
            self.link.as_mut().unwrap().advance(c);
        }
    }

    // -- checkpointing ------------------------------------------------------

    fn fingerprint(cfg: &Config) -> String {
        format!(
            "k{} sym{:?} prop{:?} card{} anch{} reach{} order{:?} link{} seed{}",
            cfg.k,
            cfg.symmetry,
            cfg.propagator,
            cfg.cardinality,
            cfg.anchors,
            cfg.anchor_reach,
            cfg.branch_order,
            cfg.link_level,
            cfg.seed
        )
    }

    pub fn checkpoint_now(&mut self, in_conflict: bool) -> Result<()> {
        let Some(path) = self.e.cfg.checkpoint.clone() else {
            return Ok(());
        };
        let cp = CheckpointFile {
            schema: 1,
            k: self.e.cfg.k,
            mode: "solve".into(),
            fingerprint: Self::fingerprint(&self.e.cfg),
            decisions: self
                .decisions
                .iter()
                .map(|d| (d.var, d.remaining, d.chosen))
                .collect(),
            decisions_count: self.e.stats.decisions,
            conflicts: self.e.stats.conflicts,
            propagations: self.e.stats.propagations,
            backtracks: self.e.stats.backtracks,
            elapsed_ms: (self.e.stats.elapsed() + self.resumed_elapsed).as_millis() as u64,
            rng_state: self.rng.state(),
            link_cursor: self.link.as_ref().map(|l| l.cursor).unwrap_or(0),
            orbit_branch: self.orbit_branch,
            in_conflict,
        };
        let tmp = path.with_extension("tmp");
        std::fs::write(&tmp, serde_json::to_vec_pretty(&cp)?)
            .with_context(|| format!("writing checkpoint {}", tmp.display()))?;
        std::fs::rename(&tmp, &path)?;
        self.e.stats.checkpoint_last = Some(self.e.stats.elapsed());
        Ok(())
    }

    fn load_checkpoint(&self, path: &Path) -> Result<CheckpointFile> {
        let raw = std::fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        let cp: CheckpointFile = serde_json::from_slice(&raw)?;
        if cp.schema != 1 {
            bail!("checkpoint schema {} is not supported", cp.schema);
        }
        if cp.k != self.e.cfg.k {
            bail!("checkpoint is for k = {} but k = {} was requested", cp.k, self.e.cfg.k);
        }
        let want = Self::fingerprint(&self.e.cfg);
        if cp.fingerprint != want {
            bail!(
                "checkpoint was produced with a different configuration:\n  saved: {}\n  now:   {}",
                cp.fingerprint,
                want
            );
        }
        Ok(cp)
    }

    fn replay_branch_index(&mut self, path: &Path) -> Result<usize> {
        Ok(self.load_checkpoint(path)?.orbit_branch)
    }

    /// Replay a checkpoint. Propagation is deterministic, so replaying the
    /// decision sequence reconstructs the exact state the checkpoint described.
    fn replay(&mut self, path: &Path) -> Result<()> {
        let cp = self.load_checkpoint(path)?;
        for (i, (var, remaining, chosen)) in cp.decisions.iter().enumerate() {
            let mask = self.e.c.unrank(*var);
            self.decisions.push(Decision {
                var: *var,
                mask,
                remaining: *remaining,
                chosen: *chosen,
            });
            self.e.push_level();
            self.e.enqueue_assignment(*var, mask, *chosen);
            if !self.e.propagate() {
                // A snapshot taken between "propagation failed" and "backtrack"
                // legitimately ends on a conflicting decision. Reproduce that
                // state; the resumed search backtracks out of it exactly as the
                // original run would have.
                if cp.in_conflict && i + 1 == cp.decisions.len() {
                    self.resume_conflict = true;
                } else {
                    bail!(
                        "checkpoint replay hit a conflict at decision {i} (vertex {var}, \
                         colour {chosen}); the checkpoint does not match this build"
                    );
                }
            }
        }
        self.e.stats.decisions = cp.decisions_count;
        self.e.stats.conflicts = cp.conflicts;
        self.e.stats.propagations = cp.propagations;
        self.e.stats.backtracks = cp.backtracks;
        self.rng = Rng::from_state(cp.rng_state);
        self.resumed_elapsed = Duration::from_millis(cp.elapsed_ms);
        if let Some(l) = self.link.as_mut() {
            let c = &self.e.c;
            l.seek(c, cp.link_cursor);
        }
        Ok(())
    }

    // -- SAT handling -------------------------------------------------------

    fn on_sat(&mut self) -> Result<PathBuf> {
        // Always run the full N_j distribution check on every completed class
        // before a witness is written (spec section 7).
        for cls in 0..self.e.c.colors as usize {
            if let Err(msg) = self.e.verify_class(cls) {
                bail!("SEV-1: solver reported SAT but class verification failed: {msg}");
            }
        }
        let colors = self.e.colors_snapshot();
        let path = self
            .e
            .cfg
            .witness_out
            .clone()
            .unwrap_or_else(|| PathBuf::from(format!("odd835-solve-k{}.wit", self.e.cfg.k)));
        let w = Witness::Partition {
            k: self.e.cfg.k,
            colors,
        };
        w.write(&path)?;
        // Re-read from disk and verify with the independent checker.
        let report = check::check_file(&path, Some(self.e.cfg.k))?;
        if !report.ok() {
            report.print();
            bail!("SEV-1: solver reported SAT but the independent checker rejected the witness");
        }
        if !self.e.cfg.quiet {
            println!("\nwitness written to {}", path.display());
            report.print();
        }
        Ok(path)
    }

    fn finish(&mut self, outcome: &str) {
        self.e.flush_log();
        if !self.e.cfg.quiet {
            self.e.stats.observe_memory(self.e.state_bytes());
            self.e.stats.emit_final(self.e.cfg.stats_format, outcome);
        }
    }

}

enum LinkSel {
    Var((u32, u32)),
    Conflict,
    Exhausted,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SymmetryMode;

    fn solver(k: u32, sym: SymmetryMode) -> Solver {
        let mut cfg = Config::new(k);
        cfg.quiet = true;
        cfg.symmetry = sym;
        Solver::new(cfg, Interrupt::new()).unwrap()
    }

    #[test]
    fn partitions_are_the_conjugacy_classes() {
        // p(k) for k = 1..12
        let expect = [1usize, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77];
        for (i, e) in expect.iter().enumerate() {
            let n = i as u32 + 1;
            let ps = partitions(n);
            assert_eq!(ps.len(), *e, "p({n})");
            for p in &ps {
                assert_eq!(p.iter().sum::<u32>(), n, "partition of {n}: {p:?}");
                assert!(p.windows(2).all(|w| w[0] >= w[1]), "must be descending");
            }
            let mut d = ps.clone();
            d.sort();
            d.dedup();
            assert_eq!(d.len(), ps.len(), "partitions of {n} must be distinct");
        }
    }

    /// The orbit reduction is only sound if `φ` is exactly the colour map that
    /// colour-symmetry breaking produces on the neighbours of `v0`. If this
    /// drifts, the reduction fixes the wrong colours and can lose solutions.
    #[test]
    fn phi_matches_what_root_breaking_assigns() {
        for k in [2u32, 4, 6, 8, 10] {
            let mut s = solver(k, SymmetryMode::Color);
            assert!(s.root_setup().unwrap(), "root propagation must not conflict");
            let phi = s.phi();
            let c0: Vec<u32> = (k - 1..2 * k - 1).collect();
            let mut seen = std::collections::HashSet::new();
            for (pos, &z) in c0.iter().enumerate() {
                let mask = c0
                    .iter()
                    .filter(|&&y| y != z)
                    .fold(0u32, |a, &y| a | (1u32 << y));
                let idx = s.e.c.rank(mask) as usize;
                assert_eq!(
                    s.e.color[idx], phi[pos],
                    "k={k}: phi({z}) = {} but u_z actually has colour {}",
                    phi[pos], s.e.color[idx]
                );
                assert!(phi[pos] >= 1 && phi[pos] <= k as u8, "phi must land in 1..=k");
                assert!(seen.insert(phi[pos]), "phi must be injective");
            }
            assert_eq!(seen.len(), k as usize);
        }
    }

    /// The `k+1` vertices containing `λ' = {0..k-3}` are `v0` plus the `w_x`,
    /// they are pairwise at intersection `k-2` (so Rule B forces them rainbow),
    /// and `v0` is the one holding colour 0. This is the lemma that makes `ψ` a
    /// bijection onto `1..=k`.
    #[test]
    fn orbit_branch_targets_are_a_forced_rainbow() {
        for k in [4u32, 6, 8, 10] {
            let c = crate::combi::Combi::new(k).unwrap();
            let lam: u32 = (0..k - 2).fold(0u32, |a, x| a | (1u32 << x));
            assert_eq!(lam.count_ones(), k - 2);
            let containing: Vec<u32> = (0..c.n)
                .filter(|x| lam & (1 << x) == 0)
                .map(|x| lam | (1u32 << x))
                .collect();
            assert_eq!(containing.len() as u32, k + 1, "k={k}");
            assert!(containing.contains(&c.unrank(0)), "v0 must be one of them");
            for i in 0..containing.len() {
                for j in i + 1..containing.len() {
                    assert_eq!(
                        (containing[i] & containing[j]).count_ones(),
                        k - 2,
                        "k={k}: pair must meet in k-2 points"
                    );
                }
            }
        }
    }

    /// Every orbit branch must assign exactly the `k` vertices `w_x`, and the
    /// colours it assigns must be a permutation of `1..=k`.
    #[test]
    fn every_orbit_branch_assigns_a_permutation() {
        for k in [2u32, 4, 6] {
            let mut s = solver(k, SymmetryMode::Orbit);
            assert!(s.root_setup().unwrap());
            let before = s.e.assigned;
            let nbranches = s.orbit_parts.len();
            for b in 0..nbranches {
                s.e.push_level();
                assert!(s.apply_orbit_branch(b));
                // drain the queued assignments without running to fixpoint
                let ok = s.e.propagate();
                if ok {
                    // The w_x need not be *newly* assigned — at k=2 the root
                    // breaking already colours the whole graph, and a branch
                    // whose cycle type happens to agree with it is consistent
                    // without adding anything. What must hold either way is
                    // that the colours on the w_x are a permutation of 1..=k.
                    let c0: Vec<u32> = (k - 1..2 * k - 1).collect();
                    let lam: u32 = (0..k.saturating_sub(2)).fold(0u32, |a, x| a | (1u32 << x));
                    let mut cols: Vec<u8> = c0
                        .iter()
                        .map(|&x| {
                            let idx = s.e.c.rank(lam | (1u32 << x)) as usize;
                            s.e.color[idx]
                        })
                        .collect();
                    cols.sort_unstable();
                    let want: Vec<u8> = (1..=k as u8).collect();
                    assert_eq!(cols, want, "k={k} branch {b} must colour w_x with 1..=k");
                }
                s.e.pop_level();
                assert_eq!(s.e.assigned, before, "branch {b} must undo cleanly");
            }
        }
    }
}
