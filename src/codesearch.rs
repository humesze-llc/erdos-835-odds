//! `odd835 code` — search for a *single* perfect 1-code in `O_k`.
//!
//! This is a different constraint from the partition and gets its own engine:
//! every closed neighbourhood must contain exactly one member of `S`, rather
//! than one vertex of each colour. It exists because spec section 7 requires
//! both polarities of the single-code oracle (`k=4,6` SAT; `k=8,10` UNSAT).
//!
//! It is emphatically *not* the partition search restricted to one class — see
//! spec section 10, "do not search one color class at a time". Nothing here
//! feeds the `solve` path.

use crate::combi::Combi;
use crate::interrupt::Interrupt;
use crate::solver::{Config, Outcome, SymmetryMode};
use crate::stats::{Rule, Stats};
use crate::witness::Witness;
use crate::{check, util::Bitset};
use anyhow::{bail, Context, Result};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::path::PathBuf;


const UNKNOWN: u8 = 0;
const IN: u8 = 1;
const OUT: u8 = 2;

struct Decision {
    /// Remaining unknown members of the branching centre, still to be tried.
    candidates: Vec<(u32, u32)>,
    next: usize,
}

pub struct CodeSolver {
    c: Combi,
    cfg: Config,
    pub stats: Stats,
    interrupt: Interrupt,

    status: Vec<u8>,
    in_count: Vec<u8>,
    unk_count: Vec<u8>,

    trail: Vec<(u32, u32, u8)>,
    trail_levels: Vec<usize>,

    in_total: u64,
    unknown_total: u64,

    queue: VecDeque<(u32, u32)>,
    in_queue: Bitset,
    heaps: Vec<BinaryHeap<Reverse<u32>>>,
    heap_total: usize,
    heap_compact_at: usize,

    decisions: Vec<Decision>,
    conflict_rule: Rule,
    tick: u64,
}

impl CodeSolver {
    pub fn new(cfg: Config, interrupt: Interrupt) -> Result<CodeSolver> {
        let c = Combi::new(cfg.k)?;
        let stats = Stats::new(
            cfg.k,
            "code",
            c.num_vertices,
            c.colors,
            c.m,
            cfg.seed,
            cfg.stats_file.as_deref(),
        )?;
        let nv = c.num_vertices as usize;
        let ncol = c.colors as usize;
        Ok(CodeSolver {
            status: vec![UNKNOWN; nv],
            in_count: vec![0; nv],
            unk_count: vec![c.colors as u8; nv],
            trail: Vec::with_capacity(1 << 16),
            trail_levels: Vec::with_capacity(1 << 12),
            in_total: 0,
            unknown_total: c.num_vertices,
            queue: VecDeque::with_capacity(1 << 12),
            in_queue: Bitset::new(nv),
            heaps: (0..=ncol).map(|_| BinaryHeap::new()).collect(),
            heap_total: 0,
            heap_compact_at: 1 << 20,
            decisions: Vec::new(),
            conflict_rule: Rule::A,
            tick: 0,
            c,
            cfg,
            stats,
            interrupt,
        })
    }

    fn state_bytes(&self) -> u64 {
        (self.status.capacity()
            + self.in_count.capacity()
            + self.unk_count.capacity()
            + self.trail.capacity() * 12
            + self.heap_total * 4) as u64
            + self.in_queue.bytes()
    }

    // -- state --------------------------------------------------------------

    fn push_level(&mut self) {
        self.trail_levels.push(self.trail.len());
        self.stats.depth_current = self.trail_levels.len();
        self.stats.depth_max = self.stats.depth_max.max(self.stats.depth_current);
    }

    fn pop_level(&mut self) {
        let mark = self.trail_levels.pop().expect("pop below root");
        while self.trail.len() > mark {
            let (v, mask, s) = self.trail.pop().unwrap();
            self.status[v as usize] = UNKNOWN;
            self.unknown_total += 1;
            if s == IN {
                self.in_total -= 1;
            }
            let mut masks = [0u32; 18];
            let cnt = self.c.closed_nbhd_masks(mask, &mut masks);
            for &mm in masks.iter().take(cnt) {
                let ci = self.c.rank(mm) as usize;
                self.unk_count[ci] += 1;
                if s == IN {
                    if self.in_count[ci] == 1 {
                        // this neighbourhood stops being covered
                        self.stats.saturated -= 1;
                    }
                    self.in_count[ci] -= 1;
                }
                let p = self.unk_count[ci] as usize;
                if self.in_count[ci] == 0 && p < self.c.colors as usize {
                    self.heaps[p].push(Reverse(ci as u32));
                    self.heap_total += 1;
                }
            }
        }
        self.stats.depth_current = self.trail_levels.len();
        self.stats.note_assigned(self.c.num_vertices - self.unknown_total);
    }

    fn set_status(&mut self, v: u32, mask: u32, s: u8) -> bool {
        let vi = v as usize;
        if self.status[vi] == s {
            return true;
        }
        if self.status[vi] != UNKNOWN {
            self.conflict_rule = Rule::A;
            return false;
        }
        self.trail.push((v, mask, s));
        self.status[vi] = s;
        self.unknown_total -= 1;
        if s == IN {
            self.in_total += 1;
        }
        self.stats
            .note_assigned(self.c.num_vertices - self.unknown_total);

        let mut ok = true;
        if self.cfg.cardinality {
            if self.in_total > self.c.m || self.in_total + self.unknown_total < self.c.m {
                self.conflict_rule = Rule::C;
                ok = false;
            }
        }

        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(mask, &mut masks);
        for &mm in masks.iter().take(cnt) {
            let ci = self.c.rank(mm) as usize;
            self.unk_count[ci] -= 1;
            if s == IN {
                self.in_count[ci] += 1;
                if self.in_count[ci] > 1 {
                    self.conflict_rule = Rule::A;
                    ok = false;
                }
                if self.in_count[ci] == 1 {
                    self.stats.saturated += 1;
                }
            }
            let p = self.unk_count[ci] as usize;
            if self.in_count[ci] == 0 && p < self.c.colors as usize {
                self.heaps[p].push(Reverse(ci as u32));
                self.heap_total += 1;
            }
            if self.in_queue.test_and_set(ci) {
                self.queue.push_back((ci as u32, mm));
            }
        }
        ok
    }

    /// The exactly-one constraint on one closed neighbourhood.
    fn center_rule(&mut self, center_mask: u32) -> bool {
        let ci = self.c.rank(center_mask) as usize;
        let inc = self.in_count[ci];
        let unk = self.unk_count[ci];
        if inc > 1 {
            self.conflict_rule = Rule::B;
            return false;
        }
        if inc == 0 && unk == 0 {
            self.conflict_rule = Rule::B;
            return false;
        }
        if inc == 0 && unk > 1 {
            return true;
        }
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(center_mask, &mut masks);
        if inc == 1 {
            // everything else in this neighbourhood is out
            for &mm in masks.iter().take(cnt) {
                let idx = self.c.rank(mm);
                if self.status[idx as usize] == UNKNOWN {
                    self.stats.forced(Rule::A);
                    if !self.set_status(idx, mm, OUT) {
                        return false;
                    }
                }
            }
        } else {
            // inc == 0 && unk == 1: the last unknown member must be in
            for &mm in masks.iter().take(cnt) {
                let idx = self.c.rank(mm);
                if self.status[idx as usize] == UNKNOWN {
                    self.stats.forced(Rule::B);
                    return self.set_status(idx, mm, IN);
                }
            }
        }
        true
    }

    fn propagate(&mut self) -> bool {
        while let Some((ci, mm)) = self.queue.pop_front() {
            self.in_queue.clear(ci as usize);
            self.stats.propagations += 1;
            if !self.center_rule(mm) {
                while let Some((c2, _)) = self.queue.pop_front() {
                    self.in_queue.clear(c2 as usize);
                }
                return false;
            }
        }
        true
    }

    // -- branching ----------------------------------------------------------

    fn compact_heaps(&mut self) {
        let mut total = 0;
        for p in 0..self.heaps.len() {
            let old = std::mem::take(&mut self.heaps[p]);
            let mut keep: Vec<Reverse<u32>> = old
                .into_iter()
                .filter(|Reverse(v)| {
                    let vi = *v as usize;
                    self.in_count[vi] == 0 && self.unk_count[vi] as usize == p
                })
                .collect();
            keep.sort_unstable();
            keep.dedup();
            total += keep.len();
            self.heaps[p] = BinaryHeap::from(keep);
        }
        self.heap_total = total;
        self.heap_compact_at = (total * 4).max(1 << 20);
    }

    /// The centre with the fewest unknown members among those not yet covered.
    fn select_center(&mut self) -> Option<u32> {
        if self.heap_total > self.heap_compact_at {
            self.compact_heaps();
        }
        for p in 1..self.c.colors as usize {
            loop {
                let v = match self.heaps[p].peek() {
                    Some(Reverse(v)) => *v,
                    None => break,
                };
                let vi = v as usize;
                if self.in_count[vi] == 0 && self.unk_count[vi] as usize == p {
                    return Some(v);
                }
                self.heaps[p].pop();
                self.heap_total -= 1;
            }
        }
        self.stats.full_scans += 1;
        let mut best: Option<(u8, u32)> = None;
        for v in 0..self.c.num_vertices as u32 {
            if self.in_count[v as usize] != 0 {
                continue;
            }
            let u = self.unk_count[v as usize];
            match best {
                None => best = Some((u, v)),
                Some((bu, _)) if u < bu => best = Some((u, v)),
                _ => {}
            }
        }
        best.map(|(_, v)| v)
    }

    fn candidates_of(&self, center: u32) -> Vec<(u32, u32)> {
        let cmask = self.c.unrank(center);
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(cmask, &mut masks);
        let mut out = Vec::with_capacity(cnt);
        for &mm in masks.iter().take(cnt) {
            let idx = self.c.rank(mm);
            if self.status[idx as usize] == UNKNOWN {
                out.push((idx, mm));
            }
        }
        out.sort_unstable();
        out
    }

    // -- driver -------------------------------------------------------------

    pub fn run(&mut self) -> Result<Outcome> {
        self.stats.observe_memory(self.state_bytes());
        // Symmetry: O_k is vertex transitive under S_{2k-1}, and automorphisms
        // map perfect codes to perfect codes, so if any perfect code exists
        // then one containing vertex 0 exists. This is a complete reduction.
        if self.cfg.symmetry == SymmetryMode::Color {
            let m0 = self.c.unrank(0);
            if !self.set_status(0, m0, IN) || !self.propagate() {
                self.finish("UNSAT");
                return Ok(Outcome::Unsat);
            }
        }
        let out = self.search()?;
        if out == Outcome::Sat {
            self.on_sat()?;
        }
        self.finish(out.label());
        Ok(out)
    }

    fn search(&mut self) -> Result<Outcome> {
        let mut conflict = false;
        loop {
            self.tick += 1;
            if self.tick % 256 == 0 || conflict {
                if let Some(o) = self.periodic()? {
                    return Ok(o);
                }
            }
            if conflict {
                self.stats.conflicts += 1;
                self.stats.conflicts_by_rule[self.conflict_rule as usize] += 1;
                conflict = false;
                loop {
                    if self.decisions.is_empty() {
                        return Ok(Outcome::Unsat);
                    }
                    self.pop_level();
                    let d = self.decisions.last_mut().unwrap();
                    if d.next < d.candidates.len() {
                        let (v, mask) = d.candidates[d.next];
                        d.next += 1;
                        self.push_level();
                        self.stats.decisions += 1;
                        if !self.set_status(v, mask, IN) || !self.propagate() {
                            conflict = true;
                        }
                        break;
                    }
                    self.decisions.pop();
                    self.stats.backtracks += 1;
                }
                continue;
            }

            let Some(center) = self.select_center() else {
                return Ok(Outcome::Sat);
            };
            let cands = self.candidates_of(center);
            if cands.is_empty() {
                conflict = true;
                self.conflict_rule = Rule::B;
                continue;
            }
            let (v, mask) = cands[0];
            self.decisions.push(Decision {
                candidates: cands,
                next: 1,
            });
            self.push_level();
            self.stats.decisions += 1;
            if !self.set_status(v, mask, IN) || !self.propagate() {
                conflict = true;
            }
        }
    }

    fn periodic(&mut self) -> Result<Option<Outcome>> {
        let elapsed = self.stats.elapsed();
        if self.interrupt.take_dump() {
            self.stats.observe_memory(self.state_bytes());
            self.stats.emit(crate::stats::StatsFormat::Jsonl);
        }
        if self.interrupt.stop_requested() {
            return Ok(Some(Outcome::Unknown("interrupted".into())));
        }
        if let Some(t) = self.cfg.timeout {
            if elapsed >= t {
                return Ok(Some(Outcome::Unknown(format!("timeout after {t:?}"))));
            }
        }
        if let Some(mc) = self.cfg.max_conflicts {
            if self.stats.conflicts >= mc {
                return Ok(Some(Outcome::Unknown(format!("conflict limit {mc}"))));
            }
        }
        let sb = self.state_bytes();
        self.stats.observe_memory(sb);
        if let Some(lim) = self.cfg.memory_limit {
            let used = crate::util::rss_bytes().unwrap_or(sb);
            if used > lim {
                return Ok(Some(Outcome::Unknown(format!(
                    "memory limit {} exceeded",
                    crate::util::fmt_bytes(lim)
                ))));
            }
        }
        if !self.cfg.quiet && self.stats.due(self.cfg.stats_interval) {
            self.stats.emit(self.cfg.stats_format);
        }
        Ok(None)
    }

    fn on_sat(&mut self) -> Result<PathBuf> {
        let members: Vec<u32> = (0..self.c.num_vertices as u32)
            .filter(|v| self.status[*v as usize] == IN)
            .collect();
        if members.len() as u64 != self.c.m {
            bail!(
                "SEV-1: code search reported SAT with {} members, expected m = {}",
                members.len(),
                self.c.m
            );
        }
        let path = self
            .cfg
            .witness_out
            .clone()
            .unwrap_or_else(|| PathBuf::from(format!("odd835-code-k{}.wit", self.cfg.k)));
        Witness::Code {
            k: self.cfg.k,
            members,
        }
        .write(&path)
        .with_context(|| format!("writing {}", path.display()))?;
        let report = check::check_file(&path, Some(self.cfg.k))?;
        if !report.ok() {
            report.print();
            bail!("SEV-1: code search reported SAT but the independent checker rejected it");
        }
        if !self.cfg.quiet {
            println!("\nwitness written to {}", path.display());
            report.print();
        }
        Ok(path)
    }

    fn finish(&mut self, outcome: &str) {
        if !self.cfg.quiet {
            self.stats.observe_memory(self.state_bytes());
            self.stats.emit_final(self.cfg.stats_format, outcome);
        }
    }
}

