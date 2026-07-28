//! Search state and propagation (spec sections 2 and 3).
//!
//! State layout, per spec section 2:
//!
//! ```text
//! color: Vec<u8>    // 0..=k, or UNASSIGNED = 0xFF
//! dom:   Vec<u32>   // bitmask of still-permitted colours, bits 0..=k
//! trail: Vec<(u32, u32)>   // (vertex, previous dom)
//! ```
//!
//! Undo pops trail entries back to a recorded offset, restoring `dom` and
//! clearing `color`. O(1) per entry. No adjacency list exists anywhere; every
//! neighbour is recomputed from bitmasks.

use super::{Config, PropagatorMode};
use crate::combi::Combi;
use crate::stats::{Rule, Stats};
use crate::util::Bitset;
use anyhow::Result;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::fs::File;
use std::io::{BufWriter, Write};

pub const UNASSIGNED: u8 = 0xFF;
/// Cap on the `assign_stack` scan performed when a class gains a new anchor.
/// Beyond this the anchor is simply not created: fewer anchors weakens Rules
/// D/E but can never make them unsound. In practice classes grow together, so
/// the `A`-th member of a class arrives while only ~`A*(k+1)` vertices are
/// assigned and the cap never binds.
const ANCHOR_INIT_SCAN_CAP: usize = 1 << 16;

#[derive(Clone, Debug)]
struct Anchor {
    idx: u32,
    mask: u32,
    /// `c_a` for `a = 0..=k-2`.
    same: Vec<u32>,
    /// `d_a` per other class: `other[class * (k-1) + a]`.
    other: Vec<u32>,
}

pub struct Engine {
    pub c: Combi,
    pub cfg: Config,
    pub stats: Stats,

    pub color: Vec<u8>,
    pub dom: Vec<u32>,
    sat_count: Vec<u8>,

    trail: Vec<(u32, u32)>,
    trail_levels: Vec<usize>,
    assign_stack: Vec<(u32, u32, u8)>,
    assign_levels: Vec<usize>,

    pub assigned: u64,
    pub size: Vec<u64>,
    avail: Vec<u64>,
    pub closed: u32,

    anchors: Vec<Vec<Anchor>>,
    nd_targets: Vec<u64>,
    me_targets: Vec<u64>,

    prop_queue: VecDeque<(u32, u32)>,
    in_prop: Bitset,
    force_queue: VecDeque<(u32, u32, u8)>,
    /// Centres awaiting a Régin pass. Deferring the (expensive) matching filter
    /// until the (cheap) counting fixpoint is reached, and deduplicating by
    /// centre, cuts the number of filter calls by roughly an order of
    /// magnitude: one propagation round touches each centre many times.
    match_queue: VecDeque<(u32, u32)>,
    in_match: Bitset,

    heaps: Vec<BinaryHeap<Reverse<u32>>>,
    heap_total: usize,
    heap_compact_at: usize,

    pub conflict_rule: Rule,
    pub conflict_log: Option<BufWriter<File>>,
}

impl Engine {
    pub fn new(c: Combi, cfg: Config, stats: Stats) -> Result<Engine> {
        let nv = c.num_vertices as usize;
        let ncol = c.colors as usize;
        let full_dom = if ncol >= 32 { u32::MAX } else { (1u32 << ncol) - 1 };
        let nd_targets = c.rule_d_targets();
        let me_targets = c.rule_e_targets();
        let conflict_log = match &cfg.conflict_log {
            Some(p) => Some(BufWriter::new(File::create(p)?)),
            None => None,
        };
        let mut e = Engine {
            color: vec![UNASSIGNED; nv],
            dom: vec![full_dom; nv],
            sat_count: vec![0u8; nv],
            trail: Vec::with_capacity(1 << 16),
            trail_levels: Vec::with_capacity(1 << 12),
            assign_stack: Vec::with_capacity(1 << 12),
            assign_levels: Vec::with_capacity(1 << 12),
            assigned: 0,
            size: vec![0; ncol],
            avail: vec![c.num_vertices; ncol],
            closed: 0,
            anchors: vec![Vec::new(); ncol],
            nd_targets,
            me_targets,
            prop_queue: VecDeque::with_capacity(1 << 12),
            in_prop: Bitset::new(nv),
            force_queue: VecDeque::with_capacity(1 << 10),
            match_queue: VecDeque::with_capacity(1 << 12),
            in_match: Bitset::new(nv),
            heaps: (0..=ncol).map(|_| BinaryHeap::new()).collect(),
            heap_total: 0,
            heap_compact_at: 1 << 20,
            conflict_rule: Rule::A,
            conflict_log,
            c,
            cfg,
            stats,
        };
        e.stats.dom_total = e.avail.iter().sum();
        Ok(e)
    }

    // -- basic accessors ----------------------------------------------------

    /// Effective domain: `dom` masked by the colours Rule C has closed. Closed
    /// colours are struck lazily at read time rather than by touching every
    /// domain vector (spec section 3, Rule C).
    #[inline(always)]
    pub fn eff_dom(&self, v: u32) -> u32 {
        let d = self.dom[v as usize];
        if self.color[v as usize] == UNASSIGNED {
            d & !self.closed
        } else {
            d
        }
    }

    #[inline(always)]
    pub fn is_assigned(&self, v: u32) -> bool {
        self.color[v as usize] != UNASSIGNED
    }

    pub fn state_bytes(&self) -> u64 {
        (self.color.capacity()
            + self.dom.capacity() * 4
            + self.sat_count.capacity()
            + self.trail.capacity() * 8
            + self.assign_stack.capacity() * 12
            + self.trail_levels.capacity() * 8
            + self.assign_levels.capacity() * 8
            + self.heap_total * 4) as u64
            + self.in_prop.bytes()
            + self.in_match.bytes()
    }

    // -- level management ---------------------------------------------------

    pub fn push_level(&mut self) {
        self.trail_levels.push(self.trail.len());
        self.assign_levels.push(self.assign_stack.len());
        self.stats.depth_current = self.trail_levels.len();
        self.stats.depth_max = self.stats.depth_max.max(self.stats.depth_current);
    }

    pub fn pop_level(&mut self) {
        let a_mark = self.assign_levels.pop().expect("pop_level below root");
        let t_mark = self.trail_levels.pop().expect("pop_level below root");
        self.undo_to(a_mark, t_mark);
        self.stats.depth_current = self.trail_levels.len();
    }

    fn undo_to(&mut self, a_mark: usize, t_mark: usize) {
        while self.assign_stack.len() > a_mark {
            let (v, mask, c) = *self.assign_stack.last().unwrap();
            let cls = c as usize;
            // Anchors are appended in assignment order, so if `v` became an
            // anchor it is the newest one of its class.
            if self.cfg.anchors > 0 {
                let pop = matches!(self.anchors[cls].last(), Some(a) if a.idx == v);
                if pop {
                    self.anchors[cls].pop();
                }
            }
            self.rule_de_undo(mask, c);
            self.assign_stack.pop();
            self.color[v as usize] = UNASSIGNED;
            self.assigned -= 1;
            if self.cfg.cardinality && self.size[cls] == self.c.m {
                self.closed &= !(1u32 << c);
            }
            if self.size[cls] == self.c.m {
                self.stats.classes_closed = self.stats.classes_closed.saturating_sub(1);
            }
            self.size[cls] -= 1;
            self.avail[cls] += 1;
            self.stats.dom_total += 1;
            // v is unassigned again, currently holding the singleton {c}
            self.stats.dom_singletons += 1;
            self.sat_dec(mask);
            // re-establish the MRV heap invariant for the restored vertex
            self.heap_push(v, 1);
        }
        while self.trail.len() > t_mark {
            let (v, prev) = self.trail.pop().unwrap();
            let vi = v as usize;
            let cur = self.dom[vi];
            let mut restored = prev & !cur;
            while restored != 0 {
                let b = restored.trailing_zeros() as usize;
                restored &= restored - 1;
                self.avail[b] += 1;
                self.stats.dom_total += 1;
            }
            if self.color[vi] == UNASSIGNED {
                if prev.count_ones() == 1 {
                    self.stats.dom_singletons += 1;
                }
                if cur.count_ones() == 1 {
                    self.stats.dom_singletons -= 1;
                }
            }
            self.dom[vi] = prev;
            self.heap_push(v, prev.count_ones() as usize);
        }
    }

    // -- MRV bookkeeping ----------------------------------------------------

    /// Invariant: every unassigned `v` with `popcount(dom[v]) = p < colors`
    /// appears in `heaps[p]`. The top bucket is deliberately not materialised:
    /// at `k = 16` that alone would be 1.2 GiB, and it is only ever consulted
    /// when no vertex has been narrowed at all.
    #[inline]
    fn heap_push(&mut self, v: u32, p: usize) {
        if p < self.c.colors as usize {
            self.heaps[p].push(Reverse(v));
            self.heap_total += 1;
        }
    }

    fn compact_heaps(&mut self) {
        let mut seen = Bitset::new(self.c.num_vertices as usize);
        let mut total = 0usize;
        for p in 0..self.heaps.len() {
            let old = std::mem::take(&mut self.heaps[p]);
            let mut keep: Vec<Reverse<u32>> = Vec::new();
            for Reverse(v) in old.into_iter() {
                let vi = v as usize;
                if self.color[vi] != UNASSIGNED {
                    continue;
                }
                if self.dom[vi].count_ones() as usize != p {
                    continue;
                }
                if !seen.test_and_set(vi) {
                    continue;
                }
                keep.push(Reverse(v));
            }
            for Reverse(v) in &keep {
                seen.clear(*v as usize);
            }
            total += keep.len();
            self.heaps[p] = BinaryHeap::from(keep);
        }
        self.heap_total = total;
        self.heap_compact_at = (total * 4).max(1 << 20);
    }

    /// Bound the MRV index. Every domain write pushes an entry — including undo
    /// — so without a periodic sweep the heaps grow with total work rather than
    /// with live state. `select_mrv` does this on its own; link-ordered
    /// branching does not go through it, so it must call this itself.
    pub fn maybe_compact_heaps(&mut self) {
        if self.heap_total > self.heap_compact_at {
            self.compact_heaps();
        }
    }

    /// Minimum-remaining-values selection, ties broken by lowest vertex index
    /// (spec section 4). Stale heap entries are discarded lazily; each entry is
    /// popped at most once per push, so the amortised cost is O(log n).
    pub fn select_mrv(&mut self) -> Option<(u32, u32)> {
        self.maybe_compact_heaps();
        for p in 1..self.c.colors as usize {
            loop {
                let v = match self.heaps[p].peek() {
                    Some(Reverse(v)) => *v,
                    None => break,
                };
                let vi = v as usize;
                if self.color[vi] == UNASSIGNED && self.dom[vi].count_ones() as usize == p {
                    return Some((v, self.c.unrank(v)));
                }
                self.heaps[p].pop();
                self.heap_total -= 1;
            }
        }
        if self.assigned == self.c.num_vertices {
            return None;
        }
        // Every unassigned vertex still has a full domain (or the invariant was
        // lost); fall back to a linear scan. Counted so it shows up in stats.
        self.stats.full_scans += 1;
        let mut best: Option<(u32, u32)> = None;
        for v in 0..self.c.num_vertices as u32 {
            if self.color[v as usize] != UNASSIGNED {
                continue;
            }
            let p = self.dom[v as usize].count_ones();
            match best {
                None => best = Some((p, v)),
                Some((bp, _)) if p < bp => best = Some((p, v)),
                _ => {}
            }
            if best.map(|(p, _)| p) == Some(1) {
                break;
            }
        }
        best.map(|(_, v)| (v, self.c.unrank(v)))
    }

    // -- saturation telemetry -----------------------------------------------

    #[inline]
    fn sat_inc(&mut self, vmask: u32) {
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(vmask, &mut masks);
        for &mm in masks.iter().take(cnt) {
            let ci = self.c.rank(mm) as usize;
            self.sat_count[ci] += 1;
            if self.sat_count[ci] as u32 == self.c.colors {
                self.stats.saturated += 1;
            }
        }
    }

    #[inline]
    fn sat_dec(&mut self, vmask: u32) {
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(vmask, &mut masks);
        for &mm in masks.iter().take(cnt) {
            let ci = self.c.rank(mm) as usize;
            if self.sat_count[ci] as u32 == self.c.colors {
                self.stats.saturated -= 1;
            }
            self.sat_count[ci] -= 1;
        }
    }

    // -- queues -------------------------------------------------------------

    #[inline]
    fn enqueue_prop(&mut self, v: u32, mask: u32) {
        if self.in_prop.test_and_set(v as usize) {
            self.prop_queue.push_back((v, mask));
        }
    }

    fn clear_queues(&mut self) {
        while let Some((v, _)) = self.prop_queue.pop_front() {
            self.in_prop.clear(v as usize);
        }
        while let Some((v, _)) = self.match_queue.pop_front() {
            self.in_match.clear(v as usize);
        }
        self.force_queue.clear();
    }

    pub fn enqueue_assignment(&mut self, v: u32, mask: u32, c: u8) {
        self.force_queue.push_back((v, mask, c));
    }

    // -- Rule A: assignment -------------------------------------------------

    pub fn assign(&mut self, v: u32, mask: u32, c: u8) -> bool {
        let vi = v as usize;
        let cb = 1u32 << c;
        if self.color[vi] != UNASSIGNED {
            if self.color[vi] == c {
                return true;
            }
            self.conflict_rule = Rule::A;
            return false;
        }
        if self.dom[vi] & cb == 0 {
            self.conflict_rule = Rule::A;
            return false;
        }
        if self.cfg.cardinality {
            if self.closed & cb != 0 || self.size[c as usize] + 1 > self.c.m {
                self.conflict_rule = Rule::C;
                return false;
            }
        }

        let old = self.dom[vi];
        self.trail.push((v, old));
        self.dom[vi] = cb;
        if old.count_ones() == 1 {
            self.stats.dom_singletons -= 1;
        }
        // Class membership is updated *before* the availability sweep below:
        // `size[c] + avail[c]` is invariant across an assignment to colour `c`
        // (one unassigned permitter becomes one member), and checking the Rule C
        // bound halfway through the update would see a spurious shortfall.
        self.color[vi] = c;
        self.assigned += 1;
        self.size[c as usize] += 1;
        let mut class_verified = true;
        if self.size[c as usize] == self.c.m {
            self.stats.classes_closed += 1;
            if self.cfg.cardinality {
                self.closed |= cb;
            }
            // --verify-classes: run the full N_j distribution check on any class
            // that does complete (spec section 7). A failure here means a
            // completed class is not a Steiner system, which the rest of the
            // engine would have had to miss.
            if self.cfg.verify_classes {
                if let Err(msg) = self.verify_class(c as usize) {
                    if self.cfg.verbose > 0 {
                        eprintln!("\nclass {c} completed but failed verification: {msg}");
                    }
                    class_verified = false;
                }
            }
        }
        // v leaves the unassigned pool: every colour it still permitted loses
        // one availability slot.
        let mut card_ok = true;
        let mut rest = old;
        while rest != 0 {
            let b = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            self.avail[b] -= 1;
            self.stats.dom_total -= 1;
            if self.cfg.cardinality && self.size[b] + self.avail[b] < self.c.m {
                card_ok = false;
            }
        }
        self.assign_stack.push((v, mask, c));
        self.sat_inc(mask);
        self.stats.note_assigned(self.assigned);

        // Rules D and E run against the anchor set as it stood *before* v could
        // join it, and the undo path mirrors that order exactly.
        let de_ok = self.rule_de_update(mask, c);
        let anchor_ok = self.maybe_add_anchor(v, mask, c);

        if !class_verified {
            self.conflict_rule = Rule::D;
            return false;
        }
        if !card_ok {
            self.conflict_rule = Rule::C;
            return false;
        }
        if !de_ok || !anchor_ok {
            return false;
        }

        // Rule A proper: strike c from every neighbour's domain.
        let mut nbrs = [0u32; 17];
        let mut n = 0usize;
        for nm in self.c.neighbors(mask) {
            nbrs[n] = nm;
            n += 1;
        }
        for &nm in nbrs.iter().take(n) {
            let ni = self.c.rank(nm);
            if !self.clear_color(ni, nm, c, Rule::A) {
                return false;
            }
        }
        self.enqueue_prop(v, mask);
        true
    }

    /// Remove colour `c` from vertex `u`'s domain. `rule` is the attribution
    /// for any conflict this uncovers.
    fn clear_color(&mut self, u: u32, umask: u32, c: u8, rule: Rule) -> bool {
        let ui = u as usize;
        let cb = 1u32 << c;
        let old = self.dom[ui];
        if old & cb == 0 {
            return true;
        }
        if self.color[ui] != UNASSIGNED {
            // an assigned vertex has dom = 1<<color, so this is color[u] == c:
            // two adjacent vertices with the same colour
            self.conflict_rule = rule;
            return false;
        }
        let new = old & !cb;
        self.trail.push((u, old));
        self.dom[ui] = new;
        self.heap_push(u, new.count_ones() as usize);
        if new.count_ones() == 1 {
            self.stats.dom_singletons += 1;
        }
        if old.count_ones() == 1 {
            self.stats.dom_singletons -= 1;
        }
        self.avail[c as usize] -= 1;
        self.stats.dom_total -= 1;
        if self.cfg.cardinality && self.size[c as usize] + self.avail[c as usize] < self.c.m {
            self.conflict_rule = Rule::C;
            return false;
        }
        let eff = new & !self.closed;
        if eff == 0 {
            self.conflict_rule = rule;
            return false;
        }
        if eff.count_ones() == 1 {
            self.stats.forced(rule);
            self.force_queue
                .push_back((u, umask, eff.trailing_zeros() as u8));
        }
        self.enqueue_prop(u, umask);
        true
    }

    // -- Rule B: closed-neighbourhood counting ------------------------------

    fn rule_b_vertex(&mut self, _v: u32, vmask: u32) -> bool {
        let matching = self.cfg.propagator == PropagatorMode::Matching;
        if !self.rule_b_center(vmask) {
            return false;
        }
        if matching {
            self.enqueue_match(vmask);
        }
        let mut nbrs = [0u32; 17];
        let mut n = 0usize;
        for nm in self.c.neighbors(vmask) {
            nbrs[n] = nm;
            n += 1;
        }
        for &nm in nbrs.iter().take(n) {
            if !self.rule_b_center(nm) {
                return false;
            }
            if matching {
                self.enqueue_match(nm);
            }
        }
        true
    }

    #[inline]
    fn enqueue_match(&mut self, center_mask: u32) {
        let ci = self.c.rank(center_mask);
        if self.in_match.test_and_set(ci as usize) {
            self.match_queue.push_back((ci, center_mask));
        }
    }

    /// `|N[center]| = k+1` equals the number of colours, so every colour must
    /// occur exactly once. Counting how many members still permit each colour
    /// gives conflict at 0 and a forced assignment at 1.
    fn rule_b_center(&mut self, center: u32) -> bool {
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(center, &mut masks);
        let ncol = self.c.colors as usize;
        let mut permit = [0u8; 18];
        let mut only = [0u32; 18];
        let mut only_mask = [0u32; 18];
        let mut assigned_bits = 0u32;
        for &mm in masks.iter().take(cnt) {
            let idx = self.c.rank(mm);
            let ii = idx as usize;
            let col = self.color[ii];
            let d = if col == UNASSIGNED {
                self.dom[ii] & !self.closed
            } else {
                1u32 << col
            };
            if d == 0 {
                self.conflict_rule = Rule::B;
                return false;
            }
            if col != UNASSIGNED {
                let b = 1u32 << col;
                if assigned_bits & b != 0 {
                    // two assigned members share a colour; they need not be
                    // adjacent, so Rule A cannot see this
                    self.conflict_rule = Rule::B;
                    return false;
                }
                assigned_bits |= b;
            }
            let mut rest = d;
            while rest != 0 {
                let b = rest.trailing_zeros() as usize;
                rest &= rest - 1;
                permit[b] += 1;
                only[b] = idx;
                only_mask[b] = mm;
            }
        }
        for cc in 0..ncol {
            if assigned_bits & (1u32 << cc) != 0 {
                continue;
            }
            match permit[cc] {
                0 => {
                    self.conflict_rule = Rule::B;
                    return false;
                }
                1 => {
                    self.stats.forced(Rule::B);
                    self.force_queue
                        .push_back((only[cc], only_mask[cc], cc as u8));
                }
                _ => {}
            }
        }
        true
    }

    // -- Rules D and E: intersection counts ---------------------------------

    fn rule_de_update(&mut self, vmask: u32, c: u8) -> bool {
        if self.cfg.anchors == 0 {
            return true;
        }
        let km1 = (self.c.k - 1) as usize;
        let mut ok = true;
        let mut hit_d = false;
        let mut hit_e = false;
        for cls in 0..self.c.colors as usize {
            for ai in 0..self.anchors[cls].len() {
                let amask = self.anchors[cls][ai].mask;
                let a = (amask & vmask).count_ones() as usize;
                let active = self.c.rule_de_active(a as u32);
                let mir = km1 - 1 - a;
                if cls == c as usize {
                    self.anchors[cls][ai].same[a] += 1;
                    if active {
                        let s = self.anchors[cls][ai].same[a] as u64
                            + self.anchors[cls][ai].same[mir] as u64;
                        if s > self.nd_targets[a] {
                            ok = false;
                            hit_d = true;
                        }
                    }
                } else {
                    let base = c as usize * km1;
                    self.anchors[cls][ai].other[base + a] += 1;
                    if active {
                        let s = self.anchors[cls][ai].other[base + a] as u64
                            + self.anchors[cls][ai].other[base + mir] as u64;
                        if s > self.me_targets[a] {
                            ok = false;
                            hit_e = true;
                        }
                    }
                }
            }
        }
        if !ok {
            self.conflict_rule = if hit_e && !hit_d { Rule::E } else { Rule::D };
        }
        ok
    }

    fn rule_de_undo(&mut self, vmask: u32, c: u8) {
        if self.cfg.anchors == 0 {
            return;
        }
        let km1 = (self.c.k - 1) as usize;
        for cls in 0..self.c.colors as usize {
            for ai in 0..self.anchors[cls].len() {
                let amask = self.anchors[cls][ai].mask;
                let a = (amask & vmask).count_ones() as usize;
                if cls == c as usize {
                    self.anchors[cls][ai].same[a] -= 1;
                } else {
                    self.anchors[cls][ai].other[c as usize * km1 + a] -= 1;
                }
            }
        }
    }

    fn maybe_add_anchor(&mut self, v: u32, vmask: u32, c: u8) -> bool {
        if self.cfg.anchors == 0 {
            return true;
        }
        let cls = c as usize;
        if self.anchors[cls].len() >= self.cfg.anchors {
            return true;
        }
        if self.assign_stack.len() > ANCHOR_INIT_SCAN_CAP {
            return true;
        }
        let km1 = (self.c.k - 1) as usize;
        let mut same = vec![0u32; km1];
        let mut other = vec![0u32; km1 * self.c.colors as usize];
        for &(oi, om, oc) in &self.assign_stack {
            if oi == v {
                continue;
            }
            let a = ((om & vmask).count_ones()) as usize;
            if oc == c {
                same[a] += 1;
            } else {
                other[oc as usize * km1 + a] += 1;
            }
        }
        let mut ok = true;
        for a in 0..km1 {
            if !self.c.rule_de_active(a as u32) {
                continue;
            }
            let mir = km1 - 1 - a;
            if same[a] as u64 + same[mir] as u64 > self.nd_targets[a] {
                self.conflict_rule = Rule::D;
                ok = false;
            }
            for other_cls in 0..self.c.colors as usize {
                if other_cls == cls {
                    continue;
                }
                let base = other_cls * km1;
                if other[base + a] as u64 + other[base + mir] as u64 > self.me_targets[a] {
                    self.conflict_rule = Rule::E;
                    ok = false;
                }
            }
        }
        self.anchors[cls].push(Anchor {
            idx: v,
            mask: vmask,
            same,
            other,
        });
        self.stats.anchor_inits += 1;
        ok
    }

    /// Rule D/E reachability direction (`--anchor-reach`). For a class that is
    /// close to complete, the counts already achieved plus the vertices still
    /// eligible at the two mirrored intersection sizes must be able to reach
    /// the target. Costs a full scan per anchor, so it only runs when the class
    /// is within 10% of `m`.
    pub fn anchor_reach_check(&mut self, cls: usize) -> bool {
        if !self.cfg.anchor_reach || self.cfg.anchors == 0 {
            return true;
        }
        if self.size[cls] * 10 < self.c.m * 9 {
            return true;
        }
        let km1 = (self.c.k - 1) as usize;
        let bit = 1u32 << cls;
        let n_anchors = self.anchors[cls].len();
        for ai in 0..n_anchors {
            let amask = self.anchors[cls][ai].mask;
            let mut eligible = vec![0u64; km1];
            for v in 0..self.c.num_vertices as u32 {
                if self.color[v as usize] != UNASSIGNED {
                    continue;
                }
                if self.dom[v as usize] & !self.closed & bit == 0 {
                    continue;
                }
                let a = (self.c.unrank(v) & amask).count_ones() as usize;
                eligible[a] += 1;
            }
            for a in 0..km1 {
                if !self.c.rule_de_active(a as u32) {
                    continue;
                }
                let mir = km1 - 1 - a;
                let have = self.anchors[cls][ai].same[a] as u64
                    + self.anchors[cls][ai].same[mir] as u64;
                if have + eligible[a] + eligible[mir] < self.nd_targets[a] {
                    self.conflict_rule = Rule::D;
                    return false;
                }
            }
        }
        true
    }

    // -- fixpoint -----------------------------------------------------------

    pub fn propagate(&mut self) -> bool {
        loop {
            if let Some((v, mask, c)) = self.force_queue.pop_front() {
                self.stats.propagations += 1;
                if !self.assign(v, mask, c) {
                    self.clear_queues();
                    return false;
                }
                continue;
            }
            if let Some((v, mask)) = self.prop_queue.pop_front() {
                self.in_prop.clear(v as usize);
                self.stats.propagations += 1;
                if !self.rule_b_vertex(v, mask) {
                    self.clear_queues();
                    return false;
                }
                continue;
            }
            // Counting has reached a fixpoint. Only now pay for Régin.
            if let Some((ci, mask)) = self.match_queue.pop_front() {
                self.in_match.clear(ci as usize);
                self.stats.propagations += 1;
                if !self.rule_matching_center(mask) {
                    self.clear_queues();
                    return false;
                }
                continue;
            }
            // Fixpoint. The Rule D/E reachability direction is the only check
            // that needs a settled state; it self-gates on class completion, so
            // this is a handful of integer comparisons in the normal case.
            if self.cfg.anchor_reach && self.cfg.anchors > 0 {
                for cls in 0..self.c.colors as usize {
                    if !self.anchor_reach_check(cls) {
                        self.clear_queues();
                        return false;
                    }
                }
            }
            return true;
        }
    }

    // -- matching propagator (see matching.rs) ------------------------------

    fn rule_matching_center(&mut self, center: u32) -> bool {
        let mut masks = [0u32; 18];
        let cnt = self.c.closed_nbhd_masks(center, &mut masks);
        let ncol = self.c.colors as usize;
        let mut doms = [0u32; 18];
        let mut idxs = [0u32; 18];
        for i in 0..cnt {
            let idx = self.c.rank(masks[i]);
            idxs[i] = idx;
            let col = self.color[idx as usize];
            doms[i] = if col == UNASSIGNED {
                self.dom[idx as usize] & !self.closed
            } else {
                1u32 << col
            };
        }
        let mut keep = [0u32; 18];
        if !super::matching::filter(&doms[..cnt], ncol, &mut keep[..cnt]) {
            self.conflict_rule = Rule::Matching;
            return false;
        }
        for i in 0..cnt {
            let removed = doms[i] & !keep[i];
            if removed == 0 {
                continue;
            }
            let mut rest = removed;
            while rest != 0 {
                let b = rest.trailing_zeros() as u8;
                rest &= rest - 1;
                if !self.clear_color(idxs[i], masks[i], b, Rule::Matching) {
                    return false;
                }
            }
        }
        true
    }

    // -- verification -------------------------------------------------------

    /// Full structural verification of a completed class against the exact
    /// `N_j` distribution (`--verify-classes`, and always before writing a
    /// witness on SAT).
    pub fn verify_class(&self, cls: usize) -> std::result::Result<(), String> {
        let members: Vec<u32> = (0..self.c.num_vertices as u32)
            .filter(|v| self.color[*v as usize] as usize == cls)
            .map(|v| self.c.unrank(v))
            .collect();
        if members.len() as u64 != self.c.m {
            return Err(format!(
                "class {cls} has {} members, expected {}",
                members.len(),
                self.c.m
            ));
        }
        let km1 = (self.c.k - 1) as usize;
        let targets = &self.nd_targets;
        for (i, &b) in members.iter().enumerate() {
            let mut prof = vec![0u64; km1];
            for (j, &o) in members.iter().enumerate() {
                if i == j {
                    continue;
                }
                prof[(b & o).count_ones() as usize] += 1;
            }
            for a in 0..km1 {
                let mir = km1 - 1 - a;
                if prof[a] + prof[mir] != targets[a] {
                    return Err(format!(
                        "class {cls}: block {b:#x} has c_{a}+c_{mir} = {} but N_{} = {}",
                        prof[a] + prof[mir],
                        a + 1,
                        targets[a]
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn colors_snapshot(&self) -> Vec<u8> {
        self.color.clone()
    }

    /// Microbenchmark hook: run Rule B over the closed neighbourhoods of one
    /// vertex without letting the resulting forced assignments change state.
    pub fn bench_rule_b(&mut self, mask: u32) -> bool {
        let v = self.c.rank(mask);
        let r = self.rule_b_vertex(v, mask);
        self.force_queue.clear();
        while let Some((u, _)) = self.prop_queue.pop_front() {
            self.in_prop.clear(u as usize);
        }
        r
    }

    pub fn log_event(&mut self, s: &str) {
        if let Some(w) = self.conflict_log.as_mut() {
            let _ = writeln!(w, "{s}");
        }
    }

    pub fn flush_log(&mut self) {
        if let Some(w) = self.conflict_log.as_mut() {
            let _ = w.flush();
        }
    }
}
