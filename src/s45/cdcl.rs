//! CDCL(T) for S(4,5,v): CaDiCaL does the learning, [`Engine`] does the theory.
//!
//! # Why this shape
//!
//! The plain CNF encoding hands CaDiCaL `C(v,4)` at-least-one clauses *plus*
//! `C(v,4)·C(v-4,2)` pairwise at-most-one binaries — 819,945 clauses at v=21.
//! Measured (RETARGET.md §2): CaDiCaL 1.9.5 could not refute v=15 branch 0 in
//! >20 minutes, where the native exact-cover search closes both branches in
//! 13m36s. The pairwise blow-up destroys the structure the engine exploits.
//!
//! So the split here is: **CaDiCaL gets the at-least-one clauses only**, and
//! the at-most-one side becomes theory propagation with two-literal reasons,
//! materialised only when actually used. That is 5,985 clauses instead of
//! 819,945 at v=21, and CaDiCaL still learns from every exclusion because each
//! one arrives with a reason it can resolve against.
//!
//! # Trail mirroring
//!
//! CaDiCaL owns the trail; the engine shadows it. Chronological backtracking
//! is switched off (`chrono=0`) so that `notify_backtrack` is the only way
//! assignments are ever retracted and levels stay monotone — without that,
//! out-of-order assignments at lower levels would desynchronise the mirror
//! silently.
//!
//! Implications are streamed straight off `Engine::trail`: everything the
//! cascade in `set_in` derived past the `sent` cursor is something CaDiCaL has
//! not been told. Redundant emissions are safe — `external_propagate.cpp:262`
//! ignores an already-true literal and turns an already-false one into a
//! conflict with the reason we supply.

use crate::engine::{Engine, Why, IN, OUT};
use crate::ipasir::{Propagator, Solver, SATISFIABLE, UNSATISFIABLE};
use std::time::{Duration, Instant};

/// Option index `o` is DIMACS variable `o + 1`.
#[inline]
fn lit_in(o: usize) -> i32 {
    o as i32 + 1
}
#[inline]
fn lit_out(o: usize) -> i32 {
    -(o as i32 + 1)
}
#[inline]
fn opt_of(lit: i32) -> usize {
    (lit.unsigned_abs() - 1) as usize
}

#[derive(Default, Clone, Copy)]
pub struct Stats {
    pub theory_props: u64,
    pub reason_clauses: u64,
    pub cover_conflicts: u64,
    pub card_conflicts: u64,
    pub match_conflicts: u64,
    pub models_checked: u64,
}

pub struct Cover {
    eng: Engine,
    /// How much of `eng.trail()` CaDiCaL has already seen.
    sent: usize,
    /// `sent` as of each `notify_new_decision_level`, for exact restore.
    sent_at_level: Vec<usize>,

    /// Reason for the literal most recently returned by `propagate`.
    reason: [i32; 2],
    reason_pos: usize,

    /// Pending external (conflict) clause, streamed out one literal at a time.
    clause: Vec<i32>,
    clause_pos: usize,

    deadline: Option<Instant>,
    stop: bool,
    /// Branch with the engine's MRV rule instead of CaDiCaL's VSIDS.
    mrv: bool,
    /// Send only forced placements, explained by resolution, instead of every
    /// exclusion. See [`Cover::explain_item`].
    tight: bool,
    /// For each option the tight mode propagated, the 4-set that forced it —
    /// needed because reasons are asked for long after the fact, by which
    /// time the item is covered and can no longer be found by search.
    forced_by: Vec<u32>,
    /// Scratch for building variable-length reason and conflict clauses.
    reason_buf: Vec<i32>,
    /// Dedup stamps, so one placed block appears once however many of an
    /// item's candidates it knocked out.
    seen: Vec<u32>,
    stamp: u32,
    pub stats: Stats,
    pub model: Vec<u32>,
}

impl Cover {
    pub fn with_mrv(mut self, on: bool) -> Cover {
        self.mrv = on;
        self
    }

    pub fn with_tight(mut self, on: bool) -> Cover {
        self.tight = on;
        self
    }

    pub fn new(eng: Engine, timeout: Option<Duration>) -> Cover {
        let n = eng.n_opts;
        Cover {
            eng,
            tight: false,
            forced_by: vec![u32::MAX; n],
            reason_buf: Vec::new(),
            seen: vec![0; n],
            stamp: 0,
            sent: 0,
            sent_at_level: Vec::new(),
            reason: [0; 2],
            reason_pos: 0,
            clause: Vec::new(),
            clause_pos: 0,
            deadline: timeout.map(|t| Instant::now() + t),
            stop: false,
            mrv: false,
            stats: Stats::default(),
            model: Vec::new(),
        }
    }

    pub fn engine(&self) -> &Engine {
        &self.eng
    }

    /// Cardinality conflict: more blocks placed than the design can hold. No
    /// clause in the formula says this, so the theory has to. The reason is
    /// the whole IN set — weak, but it is also a rule that has never fired in
    /// practice (`cardinality 0` across every measured run).
    fn card_clause(&mut self) {
        self.clause.clear();
        for (o, &st) in self.eng.status.iter().enumerate() {
            if st == IN {
                self.clause.push(lit_out(o));
            }
        }
        self.clause_pos = 0;
        self.stats.card_conflicts += 1;
    }

    /// Two IN options sharing a 4-set, if that is really what happened.
    ///
    /// `set_in` reports `Why::Cover` for two different situations: a genuine
    /// collision with another IN block, and a *cascade* failure where some
    /// 4-set ran out of candidates. Only the first has a two-literal lemma.
    /// The second has no second block to name, and emitting `(¬o)` alone would
    /// claim that block `o` belongs to no design whatsoever — unsound, and
    /// silently so, since it prunes real solutions while still terminating
    /// with a confident UNSAT.
    ///
    /// An emptied 4-set needs no help from us: its at-least-one clause is in
    /// the formula and goes falsified as soon as the pending exclusions are
    /// streamed, so CaDiCaL derives that conflict itself with a real
    /// antecedent. Returning `false` here means "say nothing".
    fn overlap_clause(&mut self, o: usize) -> bool {
        let stride = self.eng.v as usize - 4;
        let mut other = usize::MAX;
        'outer: for &ii in self.eng.opt_items_of(o).iter() {
            for k in 0..stride {
                let c = self.eng.item_opt(ii as usize, k);
                if c != o && self.eng.status[c] == IN {
                    other = c;
                    break 'outer;
                }
            }
        }
        if other == usize::MAX {
            return false;
        }
        self.clause.clear();
        self.clause.push(lit_out(o));
        self.clause.push(lit_out(other));
        self.clause_pos = 0;
        self.stats.cover_conflicts += 1;
        true
    }

    /// Explain item `ii` in terms of *placed blocks*, skipping `except`.
    ///
    /// This is what makes the tight mode possible. Start from the at-least-one
    /// clause of `ii`, which is valid outright:
    ///
    /// ```text
    ///     z_1 ∨ z_2 ∨ … ∨ z_{v-4}
    /// ```
    ///
    /// Each `z_j` that the engine excluded was excluded because some placed
    /// block `x_j` overlaps it in a 4-set, and `(¬x_j ∨ ¬z_j)` is valid. One
    /// resolution step per candidate replaces `z_j` by `¬x_j`:
    ///
    /// ```text
    ///     [except] ∨ ¬x_1 ∨ ¬x_2 ∨ …
    /// ```
    ///
    /// Still valid, being resolution over valid clauses — and now every
    /// literal names something CaDiCaL *knows*, because each `x_j` is a block
    /// CaDiCaL itself assigned. Candidates excluded by CaDiCaL directly keep
    /// their original literal `z_j`, which is already false to it.
    ///
    /// So the clause is falsified except for `except`, which is exactly what a
    /// reason clause has to be — without CaDiCaL ever being told about the
    /// `5·(v-5)` individual exclusions that placing a block causes.
    ///
    /// Blocks are deduplicated: one block usually kills several candidates of
    /// the same 4-set.
    fn explain_item(&mut self, ii: usize, except: usize) {
        let stride = self.eng.v as usize - 4;
        self.reason_buf.clear();
        if except != usize::MAX {
            self.reason_buf.push(lit_in(except));
        }
        self.stamp += 1;
        let s = self.stamp;
        for k in 0..stride {
            let z = self.eng.item_opt(ii, k);
            if z == except {
                continue;
            }
            assert_eq!(
                self.eng.status[z], OUT,
                "candidate {z} of 4-set {ii} is {} not OUT (except={except}, avail={}, cov={})",
                self.eng.status[z],
                self.eng.item_avail_of(ii),
                self.eng.item_is_covered(ii)
            );
            match self.eng.cause_of(z) {
                Engine::NO_CAUSE => {
                    // CaDiCaL excluded this one itself; its own literal is
                    // already false, so there is nothing to resolve.
                    self.reason_buf.push(lit_in(z));
                }
                x => {
                    if self.seen[x as usize] != s {
                        self.seen[x as usize] = s;
                        self.reason_buf.push(lit_out(x as usize));
                    }
                }
            }
        }
    }

    /// Re-derives the validity of a clause built by [`Cover::explain_item`],
    /// by checking the resolution actually covers the at-least-one clause:
    /// every candidate of `ii` must be accounted for, either by appearing
    /// literally, by being the propagated literal, or by having its excluding
    /// block named. Anything else means the clause claims more than the
    /// theory proved.
    fn check_item_lemma(&self, ii: usize, except: usize) {
        let stride = self.eng.v as usize - 4;
        for k in 0..stride {
            let z = self.eng.item_opt(ii, k);
            if z == except || self.reason_buf.contains(&lit_in(z)) {
                continue;
            }
            let x = self.eng.cause_of(z);
            assert!(
                x != Engine::NO_CAUSE && self.reason_buf.contains(&lit_out(x as usize)),
                "candidate {z} of 4-set {ii} is unaccounted for: the clause does not \
                 follow from at-least-one plus at-most-one"
            );
        }
    }

    /// Structural check that a pending clause is a lemma the theory can
    /// actually justify. This is the guard rail for the whole refutation: a
    /// sound UNSAT needs *every* clause handed to CaDiCaL to be globally
    /// valid, so anything that is neither an at-most-one binary nor a
    /// "not all of these blocks together" lemma is a bug, not a conflict.
    fn debug_check_lemma(&self) {
        match self.clause.len() {
            0 => panic!("empty external clause"),
            1 => panic!("unit external clause {} is not a theory lemma", self.clause[0]),
            2 => {
                // The at-most-one binary. Validity is purely structural — the
                // two blocks share a 4-subset, so no design holds both — and
                // that is checked directly. Falsification is deliberately not
                // checked here: this clause is emitted precisely when CaDiCaL
                // has placed a block the engine already excluded, so the two
                // views of `status` differ, and CaDiCaL's is the relevant one.
                let a = self.eng.opt_mask_of(opt_of(self.clause[0]));
                let b = self.eng.opt_mask_of(opt_of(self.clause[1]));
                assert!(self.clause[0] < 0 && self.clause[1] < 0);
                assert!(
                    (a & b).count_ones() >= 4,
                    "binary lemma over blocks sharing only {} points",
                    (a & b).count_ones()
                );
            }
            // Longer clauses are checked where they are built, by
            // `check_falsified` and `check_item_lemma`. Re-checking here would
            // be wrong, not merely redundant: a pending clause survives
            // backtracking on purpose (see `notify_backtrack`), and after one
            // it is still *valid* but no longer *falsified*.
            _ => {}
        }
    }

    /// Every literal is false right now. Necessary for a conflict clause, and
    /// the property that makes a reason clause unit. Only meaningful at the
    /// moment of construction.
    fn check_falsified(&self, except: usize) {
        for &l in &self.reason_buf {
            if except != usize::MAX && opt_of(l) == except {
                continue;
            }
            let st = self.eng.status[opt_of(l)];
            assert_eq!(
                st,
                if l < 0 { IN } else { OUT },
                "literal {l} is not falsified at construction"
            );
        }
    }
}

impl Propagator for Cover {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for &l in lits {
            let o = opt_of(l);
            self.eng.conflict_item = usize::MAX;
            let ok = if l > 0 {
                self.eng.set_in(o)
            } else {
                self.eng.set_out(o)
            };
            if !ok && self.clause.is_empty() {
                match self.eng.last_why {
                    Why::Cover if l > 0 && self.eng.status[o] == OUT => {
                        // CaDiCaL placed a block the engine had already ruled
                        // out. In eager mode the pending exclusion would have
                        // reached it first; in tight mode nothing was pending,
                        // so this is where it finds out. Handing back the
                        // at-most-one binary is lazy clause generation: the
                        // constraint materialises exactly when it is violated,
                        // and once learned it never has to fire again.
                        let x = self.eng.cause_of(o);
                        assert!(x != Engine::NO_CAUSE, "excluded with no cause and then placed");
                        self.clause.clear();
                        self.clause.push(lit_out(o));
                        self.clause.push(lit_out(x as usize));
                        self.clause_pos = 0;
                        self.stats.cover_conflicts += 1;
                    }
                    Why::Cover => {
                        let ii = self.eng.conflict_item;
                        if ii != usize::MAX && self.tight {
                            // A 4-set with no candidates left. In eager mode
                            // CaDiCaL sees this itself once the exclusions are
                            // streamed; in tight mode they never are, so the
                            // resolved form is the only way it learns.
                            self.explain_item(ii, usize::MAX);
                            self.check_item_lemma(ii, usize::MAX);
                            self.check_falsified(usize::MAX);
                            self.clause.clear();
                            self.clause.extend_from_slice(&self.reason_buf);
                            self.clause_pos = 0;
                            self.stats.cover_conflicts += 1;
                        } else if l > 0 && self.eng.status[o] == IN {
                            self.overlap_clause(o);
                        }
                    }
                    Why::Cardinality => self.card_clause(),
                    Why::Matching => self.card_clause(),
                }
            }
        }
        if !self.tight {
            // Eager mode leaves the at-least-one rule to CaDiCaL's watched
            // literals, so the queue is filled but never drained; drop it or
            // it grows without bound over a long run.
            self.eng.clear_forced();
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.sent_at_level.push(self.sent);
        self.eng.push_level();
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        while self.eng.level() > new_level {
            self.eng.pop_level();
            self.sent = self.sent_at_level.pop().expect("level underflow");
        }
        // Anything queued above the backtrack point is gone with it.
        debug_assert!(self.sent <= self.eng.trail().len());
        self.sent = self.sent.min(self.eng.trail().len());
        // The pending clause is deliberately NOT dropped here. Every clause
        // this propagator produces is a globally valid theory lemma, so it
        // stays true at the lower level -- and dropping one mid-stream would
        // make `add_external_clause_lit` answer 0 on the first call, which
        // CaDiCaL reads as the empty clause and reports UNSAT. That failure is
        // silent and total, so the invariant is worth stating: a clause is
        // cleared only by the code that finishes streaming it.
    }

    fn propagate(&mut self) -> i32 {
        // A pending conflict outranks any implication.
        if !self.clause.is_empty() {
            return 0;
        }
        if self.tight {
            // Send only placements the unit rule forces. The exclusions that
            // produced them stay inside the engine, which is the entire point:
            // CaDiCaL runs a full BCP pass after every literal `cb_propagate`
            // returns (external_propagate.cpp:262), so one block placement
            // costing `5·(v-5)` callbacks in eager mode costs at most a
            // handful here.
            while let Some(y) = self.eng.pop_forced() {
                if self.eng.status[y] != crate::engine::UNKNOWN {
                    continue; // queued optimistically, since gone stale
                }
                // The 4-set that forced it: uncovered, and down to this one.
                let ii = self
                    .eng
                    .opt_items_of(y)
                    .iter()
                    .map(|&i| i as usize)
                    .find(|&i| !self.eng.item_is_covered(i) && self.eng.item_avail_of(i) == 1);
                let Some(ii) = ii else { continue };
                self.forced_by[y] = ii as u32;
                self.reason_pos = 0;
                self.stats.theory_props += 1;
                return lit_in(y);
            }
            return 0;
        }
        let trail = self.eng.trail();
        while self.sent < trail.len() {
            let (o, st) = trail[self.sent];
            self.sent += 1;
            if st != OUT {
                continue;
            }
            let cause = self.eng.cause_of(o as usize);
            if cause == Engine::NO_CAUSE {
                continue; // CaDiCaL assigned this one itself
            }
            let _ = cause;
            self.reason_pos = 0;
            self.stats.theory_props += 1;
            return lit_out(o as usize);
        }
        0
    }

    /// Reasons are rebuilt on demand, never cached from the last `propagate`.
    ///
    /// CaDiCaL keeps external propagations *unexplained* until it needs them:
    /// `analyze.cpp:283` asks for the reason of a literal assigned arbitrarily
    /// far back, mid-conflict-analysis. Answering with the most recent reason
    /// instead trips `assert (val (pos0) >= 0)` in `handle_external_clause`,
    /// because the stale clause is conflicting at a point where the solver has
    /// forbidden itself from backtracking.
    ///
    /// Rebuilding is exact: `y` is still assigned while it is being analysed,
    /// so `cause_of(y)` is the option that excluded it, and that option was
    /// assigned earlier — which is also the topological order CaDiCaL asserts.
    /// In tight mode the answer is variable-length, so it is rebuilt into
    /// `reason_buf` on the first call of a query and streamed from there.
    /// `forced_by` is what makes the rebuild possible: by the time CaDiCaL
    /// asks, the 4-set has been covered by the very placement being explained
    /// and can no longer be found by searching for an availability of one.
    fn add_reason_clause_lit(&mut self, propagated: i32) -> i32 {
        if self.tight {
            if self.reason_pos == 0 {
                debug_assert!(propagated > 0, "tight mode propagates placements");
                let y = opt_of(propagated);
                let ii = self.forced_by[y];
                assert!(ii != u32::MAX, "no recorded forcing 4-set for {propagated}");
                self.explain_item(ii as usize, y);
                self.check_item_lemma(ii as usize, y);
                self.check_falsified(y);
            }
            return if self.reason_pos < self.reason_buf.len() {
                self.reason_pos += 1;
                self.reason_buf[self.reason_pos - 1]
            } else {
                self.reason_pos = 0;
                self.stats.reason_clauses += 1;
                0
            };
        }
        if self.reason_pos == 0 {
            debug_assert!(propagated < 0, "eager mode propagates exclusions");
            let y = opt_of(propagated);
            let x = self.eng.cause_of(y);
            assert!(x != Engine::NO_CAUSE, "no recorded cause for {propagated}");
            self.reason = [propagated, lit_out(x as usize)];
        }
        if self.reason_pos < self.reason.len() {
            self.reason_pos += 1;
            self.reason[self.reason_pos - 1]
        } else {
            self.reason_pos = 0;
            self.stats.reason_clauses += 1;
            0
        }
    }

    fn has_external_clause(&mut self) -> Option<bool> {
        if self.clause.is_empty() {
            None
        } else {
            // Hundreds of clauses per branch, so this is free — and it is the
            // difference between a refutation and a confident wrong answer.
            self.debug_check_lemma();
            Some(false)
        }
    }

    fn add_external_clause_lit(&mut self) -> i32 {
        assert!(!self.clause.is_empty(), "streaming an empty external clause");
        if self.clause_pos < self.clause.len() {
            self.clause_pos += 1;
            self.clause[self.clause_pos - 1]
        } else {
            self.clause.clear();
            self.clause_pos = 0;
            0
        }
    }

    /// Optionally hand CaDiCaL the engine's branching rule instead of VSIDS.
    ///
    /// This is the "static structure above, learning below" split: MRV over
    /// 4-sets knows something about exact cover that activity scores have to
    /// rediscover, while conflict analysis still runs underneath. Off by
    /// default because overriding decisions also discards everything VSIDS has
    /// learned about which variables matter — which way it lands is a
    /// measurement, not a prediction.
    fn decide(&mut self) -> i32 {
        if !self.mrv {
            return 0;
        }
        self.eng.select_option().map_or(0, lit_in)
    }

    fn check_found_model(&mut self, model: &[i32]) -> bool {
        self.stats.models_checked += 1;
        let mut blocks: Vec<u32> = Vec::new();
        for &l in model {
            if l > 0 {
                blocks.push(self.eng.opt_mask_of(opt_of(l)));
            }
        }
        // At-least-one came from the clauses, at-most-one from propagation, so
        // a model has exactly `n_blocks` blocks by construction. Reaching this
        // means the two halves disagree, which is the one bug that could fake
        // a refutation -- so it aborts rather than trying to recover. "Too few
        // blocks" in particular cannot be answered with a clause, because the
        // obvious one (not all of these IN) is not a valid lemma.
        assert_eq!(
            blocks.len(),
            self.eng.n_blocks,
            "model has {} blocks, expected {} -- propagator and formula disagree",
            blocks.len(),
            self.eng.n_blocks
        );
        self.model = blocks;
        true
    }

    fn terminated(&mut self) -> bool {
        if self.stop {
            return true;
        }
        if let Some(d) = self.deadline {
            if Instant::now() >= d {
                self.stop = true;
            }
        }
        self.stop
    }
}

pub enum Answer {
    Sat(Vec<u32>),
    Unsat,
    Unknown,
}

/// Enumerates every design in one branch, up to `limit`.
///
/// Each model is excluded by the clause "not all of these blocks together",
/// which is sound because two distinct designs have equal size, so neither
/// contains the other. Exists for validation rather than search: at v=11 the
/// answer is a number an independent enumeration also produces (48 designs
/// containing the level-1 spread), and *any* unsound lemma shows up as a
/// count that is too low. A refutation is only as trustworthy as the last
/// check that could have caught it being wrong.
pub fn enumerate_branch(v: u32, units: &[usize], tight: bool, limit: usize) -> usize {
    let mut blocking: Vec<Vec<i32>> = Vec::new();
    let mut found = 0;
    while found < limit {
        let (ans, _) = solve_branch_with(v, units, &blocking, false, false, tight, None, true);
        match ans {
            Answer::Sat(blocks) => {
                let eng = Engine::new(v, false);
                let clause: Vec<i32> = blocks.iter().map(|&m| lit_out(eng.rank(m) as usize)).collect();
                blocking.push(clause);
                found += 1;
            }
            _ => break,
        }
    }
    found
}

/// Runs one level-2 branch through CDCL(T).
///
/// `units` are the symmetry-breaking blocks, asserted at the root.
pub fn solve_branch(
    v: u32,
    units: &[usize],
    use_matching: bool,
    mrv: bool,
    tight: bool,
    timeout: Option<Duration>,
    quiet: bool,
) -> (Answer, Stats) {
    solve_branch_with(v, units, &[], use_matching, mrv, tight, timeout, quiet)
}

fn solve_branch_with(
    v: u32,
    units: &[usize],
    extra: &[Vec<i32>],
    use_matching: bool,
    mrv: bool,
    tight: bool,
    timeout: Option<Duration>,
    quiet: bool,
) -> (Answer, Stats) {
    let eng = Engine::new(v, use_matching);
    let n_opts = eng.n_opts;
    let n_items = eng.n_items;
    let stride = v as usize - 4;

    let mut s = Solver::new();
    // Mirroring is only exact while the trail is level-monotone, and CaDiCaL
    // accepts `chrono` only before the first other API call.
    assert!(s.set_option("chrono", 0), "could not disable chronological backtracking");
    s.reserve(n_opts as i32);

    for ii in 0..n_items {
        let alo: Vec<i32> = (0..stride).map(|k| lit_in(eng.item_opt(ii, k))).collect();
        s.add_clause(&alo);
    }
    // Root closure. The symmetry units are not just placements: each one
    // excludes `5·(v-5)` overlapping blocks, and those exclusions are facts at
    // level 0. Asserting them here rather than discovering them lazily is what
    // keeps the search off a cliff — `handle_external_clause` answers a
    // *unit* external clause with a bare `backtrack()`, which goes all the way
    // to level 0, so every lazily-derived at-most-one binary that happens to
    // involve a root-fixed block costs a full restart. With a third of the
    // variables root-fixed, that is most of them.
    let mut root = Engine::new(v, false);
    for &o in units {
        s.add_clause(&[lit_in(o)]);
        assert!(root.set_in(o), "symmetry units are inconsistent at the root");
    }
    let mut fixed = 0;
    for o in 0..n_opts {
        if root.status[o] == crate::engine::OUT {
            s.add_clause(&[lit_out(o)]);
            fixed += 1;
        }
    }
    for c in extra {
        s.add_clause(c);
    }

    let observed: Vec<i32> = (1..=n_opts as i32).collect();
    let mut prop = Cover::new(eng, timeout).with_mrv(mrv).with_tight(tight);

    if !quiet {
        eprintln!(
            "  CDCL(T): {} vars, {} at-least-one clauses, {} units + {} root exclusions, matching {}, mode {}",
            n_opts,
            n_items,
            units.len(),
            fixed,
            if use_matching { "on" } else { "off" },
            if tight { "tight" } else { "eager" }
        );
    }

    let r = s.solve_with(&mut prop, &observed, tight);
    if !quiet {
        s.print_statistics();
    }
    let stats = prop.stats;
    let ans = match r {
        SATISFIABLE => Answer::Sat(std::mem::take(&mut prop.model)),
        UNSATISFIABLE => Answer::Unsat,
        _ => Answer::Unknown,
    };
    (ans, stats)
}
