//! S(4,5,v) as exact cover, with the triple-derived perfect-matching propagator.
//!
//! Items are the 4-subsets of `[v]`, options the 5-subsets; a block set is a
//! selection of options covering every item exactly once.
//!
//! The propagator that matters is **not** on the items×options bipartite graph.
//! Each option covers 5 items, so that structure is exact cover by 5-sets —
//! NP-complete, with no exact polynomial filtering. Régin does not apply.
//!
//! The exactly-filterable structure sits one level down: for every 3-subset `T`
//! of `[v]`, the 4-sets `T ∪ {x}` are each covered by a unique block, and every
//! block containing `T` has the form `T ∪ {x,y}`. So **the blocks through `T`
//! induce a perfect matching on the `v-3` points outside `T`**. There are
//! `C(v,3)` such graphs, each option is an edge in exactly `C(5,3) = 10` of
//! them, and `deg_T(x)` is literally `avail[T ∪ {x}]` — so the counting rule is
//! subsumed and the new inference is perfect-matching feasibility (Tutte), via
//! blossom because these graphs are not bipartite.

use super::blossom::Blossom;
use std::collections::VecDeque;

pub const UNKNOWN: u8 = 0;
pub const IN: u8 = 1;
pub const OUT: u8 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    Cover,
    Cardinality,
    Matching,
}

pub struct Engine {
    pub v: u32,
    pub n_items: usize,
    pub n_opts: usize,
    pub n_blocks: usize,
    pub p: usize, // v - 3, points outside a triple

    binom: Vec<u64>,
    opt_mask: Vec<u32>,
    /// option -> its 5 item indices
    opt_items: Vec<[u32; 5]>,
    /// item -> its (v-4) option indices, stride `v-4`
    item_opts: Vec<u32>,
    /// triple -> the `v-3` outside points, stride `p`
    tri_pts: Vec<u8>,
    /// triple -> item index of `T ∪ {pts[i]}`, stride `p`
    tri_item: Vec<u32>,
    /// triple -> option index of `T ∪ {pts[i], pts[j]}`, stride `p*p`
    tri_opt: Vec<u32>,
    pub n_triples: usize,

    pub status: Vec<u8>,
    /// Antecedent of an OUT, for CDCL(T) reason clauses. Meaningless unless
    /// `status[o] == OUT`; never read on undo, so `pop_level` leaves it alone.
    cause: Vec<u32>,
    item_cov: Vec<u8>,
    item_avail: Vec<u32>,
    pub n_in: usize,

    trail: Vec<(u32, u8)>,
    levels: Vec<usize>,

    force_q: VecDeque<u32>,
    dirty_q: VecDeque<u32>,
    in_dirty: Vec<bool>,

    blossom: Blossom,
    sub: Blossom,

    pub use_matching: bool,
    pub use_filter: bool,
    pub filtered: u64,
    pub explain_buf: Vec<u32>,
    pub conflicts: u64,
    pub decisions: u64,
    pub props: u64,
    pub by_rule: [u64; 3],
    pub last_why: Why,
    /// The 4-set left with no candidates, valid when `last_why == Cover` and
    /// the failure came from exhaustion rather than a collision.
    pub conflict_item: usize,
}

fn binom_table() -> Vec<u64> {
    let w = 33usize;
    let mut t = vec![0u64; w * w];
    for n in 0..w {
        t[n * w] = 1;
        for r in 1..=n {
            t[n * w + r] = t[(n - 1) * w + r - 1] + if r <= n - 1 { t[(n - 1) * w + r] } else { 0 };
        }
    }
    t
}

impl Engine {
    #[inline]
    fn c(&self, n: u32, r: u32) -> u64 {
        if r > n || n > 32 {
            0
        } else {
            self.binom[n as usize * 33 + r as usize]
        }
    }

    /// Colex rank, `rank(S) = Σ C(s_i, i+1)`. Valid for any subset size, and
    /// maps `r`-subsets of `[v]` bijectively onto `[0, C(v,r))`.
    #[inline]
    pub fn rank(&self, mut mask: u32) -> u32 {
        let mut s = 0u64;
        let mut j = 0u32;
        while mask != 0 {
            let q = mask.trailing_zeros();
            mask &= mask - 1;
            s += self.c(q, j + 1);
            j += 1;
        }
        s as u32
    }

    pub fn new(v: u32, use_matching: bool) -> Engine {
        assert!((9..=25).contains(&v), "v out of supported range");
        assert_eq!((v - 3) % 2, 0, "v-3 must be even for the triple matchings");
        let binom = binom_table();
        let cc = |n: u32, r: u32| binom[n as usize * 33 + r as usize];
        let n_items = cc(v, 4) as usize;
        let n_opts = cc(v, 5) as usize;
        let n_triples = cc(v, 3) as usize;
        let p = (v - 3) as usize;
        assert_eq!(n_items % 5, 0);
        let n_blocks = n_items / 5;

        let mut e = Engine {
            v,
            n_items,
            n_opts,
            n_blocks,
            p,
            binom,
            opt_mask: vec![0; n_opts],
            opt_items: vec![[0; 5]; n_opts],
            item_opts: vec![0; n_items * (v as usize - 4)],
            tri_pts: vec![0; n_triples * p],
            tri_item: vec![0; n_triples * p],
            tri_opt: vec![0; n_triples * p * p],
            n_triples,
            status: vec![UNKNOWN; n_opts],
            cause: vec![u32::MAX; n_opts],
            item_cov: vec![0; n_items],
            item_avail: vec![(v - 4); n_items],
            n_in: 0,
            trail: Vec::with_capacity(1 << 14),
            levels: Vec::with_capacity(1 << 10),
            force_q: VecDeque::with_capacity(1 << 10),
            dirty_q: VecDeque::with_capacity(1 << 12),
            in_dirty: vec![false; n_triples],
            blossom: Blossom::new(),
            sub: Blossom::new(),
            use_matching,
            use_filter: false,
            filtered: 0,
            explain_buf: Vec::new(),
            conflicts: 0,
            decisions: 0,
            props: 0,
            by_rule: [0; 3],
            last_why: Why::Cover,
            conflict_item: usize::MAX,
        };

        // ---- precompute every incidence table -----------------------------
        for a in 0..v {
            for b in a + 1..v {
                for c in b + 1..v {
                    for d in c + 1..v {
                        for f in d + 1..v {
                            let m = (1 << a) | (1 << b) | (1 << c) | (1 << d) | (1 << f);
                            let oi = e.rank(m) as usize;
                            e.opt_mask[oi] = m;
                            let mut k = 0;
                            let mut rest = m;
                            while rest != 0 {
                                let bit = rest & rest.wrapping_neg();
                                rest &= rest - 1;
                                e.opt_items[oi][k] = e.rank(m & !bit);
                                k += 1;
                            }
                        }
                    }
                }
            }
        }
        let stride = v as usize - 4;
        for a in 0..v {
            for b in a + 1..v {
                for c in b + 1..v {
                    for d in c + 1..v {
                        let im = (1 << a) | (1 << b) | (1 << c) | (1 << d);
                        let ii = e.rank(im) as usize;
                        let mut k = 0;
                        for x in 0..v {
                            if im & (1 << x) != 0 {
                                continue;
                            }
                            e.item_opts[ii * stride + k] = e.rank(im | (1 << x));
                            k += 1;
                        }
                        debug_assert_eq!(k, stride);
                    }
                }
            }
        }
        for a in 0..v {
            for b in a + 1..v {
                for c in b + 1..v {
                    let tm = (1 << a) | (1 << b) | (1 << c);
                    let t = e.rank(tm) as usize;
                    let pts: Vec<u32> = (0..v).filter(|x| tm & (1 << x) == 0).collect();
                    debug_assert_eq!(pts.len(), p);
                    for (i, &x) in pts.iter().enumerate() {
                        e.tri_pts[t * p + i] = x as u8;
                        e.tri_item[t * p + i] = e.rank(tm | (1 << x));
                        for (j, &y) in pts.iter().enumerate() {
                            if i < j {
                                let oi = e.rank(tm | (1 << x) | (1 << y));
                                e.tri_opt[t * p * p + i * p + j] = oi;
                                e.tri_opt[t * p * p + j * p + i] = oi;
                            }
                        }
                    }
                }
            }
        }
        e
    }

    // -- level management ---------------------------------------------------

    pub fn push_level(&mut self) {
        self.levels.push(self.trail.len());
    }

    pub fn pop_level(&mut self) {
        let mark = self.levels.pop().expect("pop below root");
        while self.trail.len() > mark {
            let (o, st) = self.trail.pop().unwrap();
            let o = o as usize;
            let items = self.opt_items[o];
            if st == IN {
                self.n_in -= 1;
                for &ii in items.iter() {
                    self.item_cov[ii as usize] = 0;
                }
            } else {
                // LIFO order guarantees item_cov holds the same value now as it
                // did on the forward pass, so this mirrors set_out exactly.
                for &ii in items.iter() {
                    if self.item_cov[ii as usize] == 0 {
                        self.item_avail[ii as usize] += 1;
                    }
                }
            }
            self.status[o] = UNKNOWN;
        }
    }

    pub fn level(&self) -> usize {
        self.levels.len()
    }

    // -- exact-cover propagation -------------------------------------------

    #[inline]
    fn mark_dirty(&mut self, om: u32) {
        if !self.use_matching {
            return;
        }
        let mut pts = [0u32; 5];
        let mut k = 0;
        let mut rest = om;
        while rest != 0 {
            pts[k] = rest.trailing_zeros();
            rest &= rest - 1;
            k += 1;
        }
        const T3: [[usize; 3]; 10] = [
            [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4],
            [0, 3, 4], [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4],
        ];
        for c in T3.iter() {
            let tm = (1 << pts[c[0]]) | (1 << pts[c[1]]) | (1 << pts[c[2]]);
            let t = self.rank(tm) as usize;
            if !self.in_dirty[t] {
                self.in_dirty[t] = true;
                self.dirty_q.push_back(t as u32);
            }
        }
    }

    /// Options excluded here have no antecedent inside the engine.
    pub const NO_CAUSE: u32 = u32::MAX;

    /// The 5 items (4-subsets) covered by option `o`.
    pub fn opt_items_of(&self, o: usize) -> [u32; 5] {
        self.opt_items[o]
    }

    /// The `k`-th of the `v-4` options covering item `ii`.
    pub fn item_opt(&self, ii: usize, k: usize) -> usize {
        self.item_opts[ii * (self.v as usize - 4) + k] as usize
    }

    /// Point set of option `o` as a bitmask.
    pub fn opt_mask_of(&self, o: usize) -> u32 {
        self.opt_mask[o]
    }

    /// Read-only view of the assignment trail, oldest first. CDCL(T) streams
    /// implications off the tail of this; see `cdcl::Cover::propagate`.
    pub fn trail(&self) -> &[(u32, u8)] {
        &self.trail
    }

    /// The IN option that forced `o` OUT, or [`Engine::NO_CAUSE`] when `o` was
    /// excluded directly rather than by a cascade. This is what turns an
    /// exclusion into a two-literal reason clause.
    pub fn cause_of(&self, o: usize) -> u32 {
        self.cause[o]
    }

    /// Drop pending unit-rule work. Used by the eager CDCL mode, where the
    /// at-least-one side belongs to CaDiCaL's watched literals, so the queue
    /// is filled but never drained and would otherwise grow without bound.
    pub fn clear_forced(&mut self) {
        self.force_q.clear();
    }

    /// Next option the unit rule forced, if any. Callers must re-check its
    /// status: the queue is filled optimistically and entries go stale.
    pub fn pop_forced(&mut self) -> Option<usize> {
        self.force_q.pop_front().map(|o| o as usize)
    }

    /// Remaining candidates for item `ii`. Meaningless once `ii` is covered.
    pub fn item_avail_of(&self, ii: usize) -> u32 {
        self.item_avail[ii]
    }

    pub fn item_is_covered(&self, ii: usize) -> bool {
        self.item_cov[ii] != 0
    }

    pub fn set_out(&mut self, o: usize) -> bool {
        self.set_out_because(o, Engine::NO_CAUSE)
    }

    pub fn set_out_because(&mut self, o: usize, cause: u32) -> bool {
        match self.status[o] {
            OUT => return true,
            IN => {
                self.last_why = Why::Cover;
                return false;
            }
            _ => {}
        }
        self.status[o] = OUT;
        self.cause[o] = cause;
        self.trail.push((o as u32, OUT));
        let items = self.opt_items[o];
        let stride = self.v as usize - 4;
        let mut ok = true;
        for &ii in items.iter() {
            let ii = ii as usize;
            if self.item_cov[ii] != 0 {
                continue;
            }
            self.item_avail[ii] -= 1;
            if self.item_avail[ii] == 0 {
                self.last_why = Why::Cover;
                self.conflict_item = ii;
                ok = false;
            } else if self.item_avail[ii] == 1 {
                for k in 0..stride {
                    let cand = self.item_opts[ii * stride + k];
                    if self.status[cand as usize] == UNKNOWN {
                        self.force_q.push_back(cand);
                        break;
                    }
                }
            }
        }
        let om = self.opt_mask[o];
        self.mark_dirty(om);
        ok
    }

    pub fn set_in(&mut self, o: usize) -> bool {
        match self.status[o] {
            IN => return true,
            OUT => {
                self.last_why = Why::Cover;
                return false;
            }
            _ => {}
        }
        self.status[o] = IN;
        self.trail.push((o as u32, IN));
        self.n_in += 1;
        if self.n_in > self.n_blocks {
            self.last_why = Why::Cardinality;
            return false;
        }
        let items = self.opt_items[o];
        // Cover first, then exclude: set_out must see the covered flag already
        // set, or it would decrement availability for items that no longer need it.
        for &ii in items.iter() {
            if self.item_cov[ii as usize] != 0 {
                self.last_why = Why::Cover;
                return false;
            }
            self.item_cov[ii as usize] = 1;
        }
        let stride = self.v as usize - 4;
        for &ii in items.iter() {
            let ii = ii as usize;
            for k in 0..stride {
                let other = self.item_opts[ii * stride + k] as usize;
                if other != o && !self.set_out_because(other, o as u32) {
                    return false;
                }
            }
        }
        let om = self.opt_mask[o];
        self.mark_dirty(om);
        true
    }

    // -- the triple perfect-matching propagator -----------------------------

    /// `T`'s remaining points must admit a perfect matching using only options
    /// still available. Blocks already chosen through `T` have covered both of
    /// their points, which removes them from the graph.
    fn check_triple(&mut self, t: usize) -> bool {
        let p = self.p;
        let mut local = [0usize; 32];
        let mut nv = 0usize;
        for i in 0..p {
            let ii = self.tri_item[t * p + i] as usize;
            if self.item_cov[ii] == 0 {
                local[nv] = i;
                nv += 1;
            }
        }
        if nv % 2 != 0 {
            self.last_why = Why::Matching;
            return false;
        }
        if nv == 0 {
            return true;
        }
        self.blossom.reset(nv);
        for a in 0..nv {
            for b in a + 1..nv {
                let oi = self.tri_opt[t * p * p + local[a] * p + local[b]] as usize;
                if self.status[oi] == UNKNOWN {
                    self.blossom.add_edge(a, b);
                }
            }
        }
        if !self.blossom.has_perfect_matching() {
            self.last_why = Why::Matching;
            return false;
        }
        if !self.use_filter {
            return true;
        }
        // Régin's step, adapted to general graphs: an available edge that lies
        // in no perfect matching of G_T can never be a block, because the
        // blocks through T *are* a perfect matching. Edges of the matching we
        // just found are trivially in one, so only the rest need testing.
        let mut keep = [false; 32];
        for a in 0..nv {
            let m = self.blossom.mate_of(a);
            if m >= 0 {
                keep[a] = true;
            }
        }
        let _ = keep;
        let mut doomed: [u32; 256] = [0; 256];
        let mut nd = 0usize;
        for a in 0..nv {
            for b in a + 1..nv {
                if self.blossom.mate_of(a) == b as i32 {
                    continue; // in the witness matching, certainly allowed
                }
                let oi = self.tri_opt[t * p * p + local[a] * p + local[b]] as usize;
                if self.status[oi] != UNKNOWN {
                    continue;
                }
                // does a perfect matching exist that uses edge (a,b)?
                self.sub.reset(nv - 2);
                let mut map = [0usize; 32];
                let mut k = 0usize;
                for x in 0..nv {
                    if x != a && x != b {
                        map[x] = k;
                        k += 1;
                    }
                }
                for x in 0..nv {
                    if x == a || x == b {
                        continue;
                    }
                    for y in x + 1..nv {
                        if y == a || y == b {
                            continue;
                        }
                        let o2 = self.tri_opt[t * p * p + local[x] * p + local[y]] as usize;
                        if self.status[o2] == UNKNOWN {
                            self.sub.add_edge(map[x], map[y]);
                        }
                    }
                }
                if !self.sub.has_perfect_matching() && nd < 256 {
                    doomed[nd] = oi as u32;
                    nd += 1;
                }
            }
        }
        for i in 0..nd {
            self.filtered += 1;
            if !self.set_out(doomed[i] as usize) {
                return false;
            }
        }
        true
    }

    fn clear_queues(&mut self) {
        self.force_q.clear();
        while let Some(t) = self.dirty_q.pop_front() {
            self.in_dirty[t as usize] = false;
        }
    }

    /// Cheap exact-cover fixpoint first, then the expensive matching sweep,
    /// deduplicated by triple. Same shape as odd835's deferred Régin pass.
    pub fn propagate(&mut self) -> bool {
        loop {
            if let Some(o) = self.force_q.pop_front() {
                self.props += 1;
                if !self.set_in(o as usize) {
                    self.by_rule[self.last_why as usize] += 1;
                    self.clear_queues();
                    return false;
                }
                continue;
            }
            if self.use_matching {
                if let Some(t) = self.dirty_q.pop_front() {
                    self.in_dirty[t as usize] = false;
                    self.props += 1;
                    if !self.check_triple(t as usize) {
                        self.by_rule[self.last_why as usize] += 1;
                        self.clear_queues();
                        return false;
                    }
                    continue;
                }
            }
            return true;
        }
    }

    pub fn enqueue(&mut self, o: usize) {
        self.force_q.push_back(o as u32);
    }

    // -- branching ----------------------------------------------------------

    /// Minimum-remaining-values over items: the uncovered item with the fewest
    /// remaining options, and that list. Exactly one of them must be chosen, so
    /// branching over it is complete.
    pub fn select(&self) -> Option<(usize, Vec<usize>)> {
        let stride = self.v as usize - 4;
        let mut best: Option<(u32, usize)> = None;
        for ii in 0..self.n_items {
            if self.item_cov[ii] != 0 {
                continue;
            }
            let a = self.item_avail[ii];
            match best {
                None => best = Some((a, ii)),
                Some((b, _)) if a < b => best = Some((a, ii)),
                _ => {}
            }
            if a <= 2 {
                break;
            }
        }
        let (_, ii) = best?;
        let mut opts = Vec::new();
        for k in 0..stride {
            let o = self.item_opts[ii * stride + k] as usize;
            if self.status[o] == UNKNOWN {
                opts.push(o);
            }
        }
        Some((ii, opts))
    }

    /// MRV without the allocation: the first still-open option of the
    /// most-constrained uncovered item. This is the branching rule the DPLL
    /// search uses, exposed for CDCL(T)'s `cb_decide` so the two halves can be
    /// compared with only the decision heuristic changing.
    pub fn select_option(&self) -> Option<usize> {
        let stride = self.v as usize - 4;
        let mut best: Option<(u32, usize)> = None;
        for ii in 0..self.n_items {
            if self.item_cov[ii] != 0 {
                continue;
            }
            let a = self.item_avail[ii];
            if best.map_or(true, |(b, _)| a < b) {
                best = Some((a, ii));
                if a <= 2 {
                    break;
                }
            }
        }
        let (_, ii) = best?;
        (0..stride)
            .map(|k| self.item_opts[ii * stride + k] as usize)
            .find(|&o| self.status[o] == UNKNOWN)
    }

    pub fn all_covered(&self) -> bool {
        self.n_in == self.n_blocks
    }

    pub fn blocks(&self) -> Vec<u32> {
        (0..self.n_opts)
            .filter(|&o| self.status[o] == IN)
            .map(|o| self.opt_mask[o])
            .collect()
    }

    /// Symmetry breaking, sound for existence.
    ///
    /// The blocks through `{0,1,2}` form a perfect matching on the other `v-3`
    /// points. The stabiliser of `{0,1,2}` in `S_v` acts as the full symmetric
    /// group on those points, so any solution can be relabelled to make that
    /// matching `(3,4), (5,6), …`. Fixing all `(v-3)/2` of those blocks removes
    /// solutions only up to relabelling.
    pub fn break_symmetry(&mut self) {
        for o in self.symmetry_units() {
            self.enqueue(o);
        }
    }

    /// The level-1 blocks as option indices, for callers that assert them as
    /// unit clauses rather than pushing them onto a queue.
    pub fn symmetry_units(&self) -> Vec<usize> {
        let mut out = Vec::new();
        let mut a = 3u32;
        while a + 1 < self.v {
            let m = 0b111 | (1 << a) | (1 << (a + 1));
            out.push(self.rank(m) as usize);
            a += 2;
        }
        out
    }

    /// Partitions of `n` with every part >= 2 — the surviving level-2 branches.
    ///
    /// A part `l = 1` means `M'` agrees with `P'` on that pair, so the blocks
    /// `{0,1,3,x,x'}` and `{0,1,2,x,x'}` both exist and share the FOUR points
    /// `{0,1,x,x'}`. That 4-set would be covered twice, so such a branch is
    /// infeasible with no search. Count is `p(n) - p(n-1)`: 22 -> 7 at v=21.
    pub fn level2_branches(&self) -> Vec<Vec<u32>> {
        let n = (self.v - 3) / 2 - 1;
        fn go(rem: u32, mx: u32, cur: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
            if rem == 0 {
                out.push(cur.clone());
                return;
            }
            let hi = mx.min(rem);
            for q in (2..=hi).rev() {
                if rem - q == 1 {
                    continue; // a remainder of 1 forces a part of 1
                }
                cur.push(q);
                go(rem - q, q, cur, out);
                cur.pop();
            }
        }
        let mut out = Vec::new();
        go(n, n, &mut Vec::new(), &mut out);
        out
    }

    /// Fix the level-2 spread at `T2 = {0,1,3}` for branch `lam`.
    ///
    /// The shared level-1 block `{0,1,2,3,4}` already pins 2<->4; this fixes the
    /// rest of the matching on `{5..v-1}` to the canonical representative of
    /// `lam`'s cycle type. Complete over all branches — see RETARGET.md for the
    /// verified orbit decomposition and `tools_soundness_check.py`.
    pub fn break_symmetry_level2(&mut self, lam: &[u32]) {
        for o in self.level2_units(lam) {
            self.enqueue(o);
        }
    }

    /// The level-2 blocks for branch `lam` as option indices.
    pub fn level2_units(&self, lam: &[u32]) -> Vec<usize> {
        let mut out = Vec::new();
        let base: Vec<u32> = (5..self.v).collect();
        let t2 = 1u32 | 2 | 8; // {0,1,3}
        let mut off = 0usize;
        for &l in lam {
            let l = l as usize;
            debug_assert!(l >= 2);
            for i in 0..l {
                let b = base[2 * (off + i) + 1];
                let a = base[2 * (off + (i + 1) % l)];
                let m = t2 | (1u32 << a) | (1u32 << b);
                debug_assert_eq!(m.count_ones(), 5);
                out.push(self.rank(m) as usize);
            }
            off += l;
        }
        out
    }

    /// Explanation for a triple-matching conflict, as a CDCL(T) reason clause.
    ///
    /// `G_T` has no perfect matching, so at least one of the currently-removed
    /// edges must come back. The raw reason is "every removed edge in this
    /// triple"; the useful reason is a **deletion-minimal** subset that still
    /// kills feasibility on its own. Each minimality test is one blossom call
    /// on a subgraph, so this is polynomial — the cost is a measured curve, not
    /// a cliff, and only a large *minimal* witness would be structural trouble.
    ///
    /// Returns `(raw, minimal, live_vertices)`; the minimal set is left in
    /// `self.explain_buf` as option indices.
    pub fn explain_triple(&mut self, t: usize) -> Option<(usize, usize, usize)> {
        let p = self.p;
        let mut local = [0usize; 32];
        let mut nv = 0usize;
        for i in 0..p {
            if self.item_cov[self.tri_item[t * p + i] as usize] == 0 {
                local[nv] = i;
                nv += 1;
            }
        }
        if nv == 0 || nv % 2 != 0 {
            return None;
        }
        // partition the pairs into available and removed
        let mut avail: Vec<(usize, usize)> = Vec::new();
        let mut removed: Vec<(usize, usize)> = Vec::new();
        for a in 0..nv {
            for b in a + 1..nv {
                let oi = self.tri_opt[t * p * p + local[a] * p + local[b]] as usize;
                if self.status[oi] == OUT {
                    removed.push((a, b));
                } else {
                    avail.push((a, b));
                }
            }
        }
        // feasibility with `keep` (a subset of `removed`) restored
        let mut feasible = |bl: &mut Blossom, keep: &[bool], rem: &Vec<(usize, usize)>| -> bool {
            bl.reset(nv);
            for &(a, b) in avail.iter() {
                bl.add_edge(a, b);
            }
            for (i, &(a, b)) in rem.iter().enumerate() {
                if keep[i] {
                    bl.add_edge(a, b);
                }
            }
            bl.has_perfect_matching()
        };
        let n = removed.len();
        let mut keep = vec![false; n];
        if feasible(&mut self.sub, &keep, &removed) {
            return None; // not actually a conflict
        }
        // deletion filter: restore e; if still infeasible, e was not needed
        for i in 0..n {
            keep[i] = true;
            if !feasible(&mut self.sub, &keep, &removed) {
                // still infeasible without e -> e is not part of the reason
            } else {
                keep[i] = false; // e is needed, keep it removed
            }
        }
        self.explain_buf.clear();
        for (i, &(a, b)) in removed.iter().enumerate() {
            if !keep[i] {
                self.explain_buf
                    .push(self.tri_opt[t * p * p + local[a] * p + local[b]]);
            }
        }
        Some((n, self.explain_buf.len(), nv))
    }

    pub fn state_bytes(&self) -> u64 {
        ((self.opt_mask.len() + self.opt_items.len() * 5 + self.item_opts.len()
            + self.tri_item.len() + self.tri_opt.len()) * 4
            + self.tri_pts.len()
            + self.status.len()
            + self.item_cov.len()
            + self.item_avail.len() * 4
            + self.trail.capacity() * 8
            + self.in_dirty.len()) as u64
    }
}
