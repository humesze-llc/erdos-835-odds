//! Combinatorial core (spec sections 1 and 2).
//!
//! `O_k` has vertex set the `(k-1)`-subsets of `[n]` with `n = 2k-1`, and
//! `T ~ U` iff `T ∩ U = ∅`. Vertices are `u32` bitmasks indexed by colex rank.
//!
//! This module also derives the exact block-intersection distributions `N_j`
//! and `M_j` of the structure theorem and the Rule D / Rule E targets that
//! follow from them. Nothing here is hardcoded from the spec's tables; the
//! tables are asserted against these functions in the oracle suite.

use anyhow::{bail, Result};

pub const MAX_BITS: u32 = 32;
const LO_BITS: u32 = 16;
const LO_SIZE: usize = 1 << LO_BITS;
const HI_BITS: u32 = 15;
const HI_SIZE: usize = 1 << HI_BITS;

// ---------------------------------------------------------------------------
// Binomials
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Binom {
    table: Vec<u64>,
    w: usize,
}

impl Default for Binom {
    fn default() -> Self {
        Self::new()
    }
}

impl Binom {
    pub fn new() -> Self {
        let w = MAX_BITS as usize + 1;
        let mut table = vec![0u64; w * w];
        for n in 0..w {
            table[n * w] = 1;
            for r in 1..=n {
                let up_left = table[(n - 1) * w + (r - 1)];
                let up = if r <= n - 1 { table[(n - 1) * w + r] } else { 0 };
                table[n * w + r] = up_left + up;
            }
        }
        Binom { table, w }
    }

    #[inline]
    pub fn c(&self, n: u32, r: u32) -> u64 {
        if r > n || n >= self.w as u32 {
            return 0;
        }
        self.table[n as usize * self.w + r as usize]
    }
}

// ---------------------------------------------------------------------------
// Combi: everything derived from k
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Combi {
    /// The problem parameter. Always even, 2..=16.
    pub k: u32,
    /// Ground set size, `2k - 1`.
    pub n: u32,
    /// Vertex subset size, `k - 1`.
    pub r: u32,
    /// Number of colours, `k + 1`. Never configurable (spec section 1).
    pub colors: u32,
    /// `C(2k-1, k-1)`.
    pub num_vertices: u64,
    /// Perfect-code size, `|V| / (k+1)`.
    pub m: u64,
    /// Bitmask of `[n]`.
    pub full: u32,
    pub binom: Binom,
    low_rank: Vec<u32>,
    high_rank: Vec<u32>,
}

impl Combi {
    /// Reject odd `k` here, at construction, with the structure-theorem reason
    /// (spec section 1, consequence 1).
    pub fn new(k: u32) -> Result<Self> {
        if k < 2 || k > 16 {
            bail!("k = {k} is out of range; this tool supports 2 <= k <= 16");
        }
        if k % 2 != 0 {
            bail!(
                "k = {k} is odd, so no partition of O_{k} into {kk} perfect 1-codes can exist.\n\
                 The structure theorem gives, for a colour class B and any block B in it,\n\
                     N_0(B) = (1 + k*(-1)^k) / (k+1) = (1 - {k}) / {kk} = {v},\n\
                 the number of blocks of the class disjoint from B. A count cannot be\n\
                 negative, so there is nothing to search. Use an even k.",
                k = k,
                kk = k + 1,
                v = (1i64 - k as i64) as f64 / (k as f64 + 1.0)
            );
        }
        let binom = Binom::new();
        let n = 2 * k - 1;
        let r = k - 1;
        let num_vertices = binom.c(n, r);
        let colors = k + 1;
        debug_assert!(num_vertices % colors as u64 == 0);
        let m = num_vertices / colors as u64;
        let full = if n >= 32 { u32::MAX } else { (1u32 << n) - 1 };

        // Colex rank split into a 16-bit low table and a (popcount_low, 15-bit
        // high) table so rank() is two array reads in the hot loop.
        let mut low_rank = vec![0u32; LO_SIZE];
        for (mask, slot) in low_rank.iter_mut().enumerate() {
            let mut sum = 0u32;
            let mut j = 0u32;
            let mut rest = mask as u32;
            while rest != 0 {
                let q = rest.trailing_zeros();
                rest &= rest - 1;
                sum += binom.c(q, j + 1) as u32;
                j += 1;
            }
            *slot = sum;
        }
        let high_rank = if n > LO_BITS {
            let mut hr = vec![0u32; (LO_BITS as usize + 1) * HI_SIZE];
            for p in 0..=LO_BITS {
                for h in 0..HI_SIZE {
                    let mut sum = 0u32;
                    let mut j = p;
                    let mut rest = h as u32;
                    while rest != 0 {
                        let q = rest.trailing_zeros();
                        rest &= rest - 1;
                        sum += binom.c(LO_BITS + q, j + 1) as u32;
                        j += 1;
                    }
                    hr[p as usize * HI_SIZE + h] = sum;
                }
            }
            hr
        } else {
            Vec::new()
        };

        Ok(Combi {
            k,
            n,
            r,
            colors,
            num_vertices,
            m,
            full,
            binom,
            low_rank,
            high_rank,
        })
    }

    // -- ranking ------------------------------------------------------------

    /// Colex rank, table driven. `mask` must be a valid vertex (popcount `r`,
    /// all bits below `n`).
    #[inline(always)]
    pub fn rank(&self, mask: u32) -> u32 {
        debug_assert_eq!(mask.count_ones(), self.r);
        debug_assert_eq!(mask & !self.full, 0);
        let lo = (mask & 0xFFFF) as usize;
        let hi = (mask >> LO_BITS) as usize;
        let mut v = self.low_rank[lo];
        if hi != 0 {
            v += self.high_rank[(lo.count_ones() as usize) * HI_SIZE + hi];
        }
        v
    }

    /// Reference implementation of the colex rank straight from the definition
    /// `rank(S) = sum_i C(s_i, i+1)`. Used by tests and the independent checker.
    pub fn rank_ref(&self, mask: u32) -> u32 {
        let mut sum = 0u64;
        let mut j = 0u32;
        let mut rest = mask;
        while rest != 0 {
            let q = rest.trailing_zeros();
            rest &= rest - 1;
            sum += self.binom.c(q, j + 1);
            j += 1;
        }
        sum as u32
    }

    /// Greedy colex unranking, top index down.
    pub fn unrank(&self, idx: u32) -> u32 {
        let mut rem = idx as u64;
        let mut mask = 0u32;
        for i in (0..self.r).rev() {
            let mut s = i;
            while self.binom.c(s + 1, i + 1) <= rem {
                s += 1;
            }
            mask |= 1u32 << s;
            rem -= self.binom.c(s, i + 1);
        }
        debug_assert_eq!(rem, 0);
        mask
    }

    // -- adjacency ----------------------------------------------------------

    /// The `k` neighbours of `mask`: the complement of `mask` in `[n]` has
    /// exactly `k` bits, and dropping each in turn gives every `(k-1)`-subset
    /// disjoint from `mask`.
    #[inline(always)]
    pub fn neighbors(&self, mask: u32) -> NeighborIter {
        let comp = self.full & !mask;
        NeighborIter { comp, rest: comp }
    }

    /// Fill `out` with the `k+1` masks of the closed neighbourhood `N[center]`,
    /// centre first. Returns the count.
    #[inline(always)]
    pub fn closed_nbhd_masks(&self, center: u32, out: &mut [u32]) -> usize {
        out[0] = center;
        let comp = self.full & !center;
        let mut rest = comp;
        let mut i = 1;
        while rest != 0 {
            let b = rest & rest.wrapping_neg();
            rest &= rest - 1;
            out[i] = comp & !b;
            i += 1;
        }
        i
    }

    // -- structure theorem --------------------------------------------------

    /// Exact numerators of `N_j` over the common denominator `k+1`:
    /// `C(k,j) * (C(k,j) + (-1)^(k+j) * k)`.
    pub fn n_num(&self) -> Vec<i128> {
        let k = self.k as i128;
        (0..=self.k)
            .map(|j| {
                let c = self.binom.c(self.k, j) as i128;
                let s = if (self.k + j) % 2 == 0 { 1i128 } else { -1 };
                c * (c + s * k)
            })
            .collect()
    }

    /// Exact numerators of `M_j` over `k+1`: `C(k,j) * (C(k,j) - (-1)^(k+j))`.
    pub fn m_num(&self) -> Vec<i128> {
        (0..=self.k)
            .map(|j| {
                let c = self.binom.c(self.k, j) as i128;
                let s = if (self.k + j) % 2 == 0 { 1i128 } else { -1 };
                c * (c - s)
            })
            .collect()
    }

    /// `N_j = C(k,j) * (C(k,j) + (-1)^(k+j) * k) / (k+1)`: blocks of the *same*
    /// class meeting a fixed block of that class in exactly `j` points.
    ///
    /// The quotient is **not** integral for every even `k`: it fails at `k = 8`
    /// and `k = 14`, which is exactly the arithmetic obstruction that makes
    /// those two rungs UNSAT. `N_j` is a count, so a non-integral value proves
    /// no Steiner system `S(k-1,k,2k)` exists, hence no perfect 1-code and no
    /// partition. Where the value is fractional this returns the floor, which
    /// is a sound Rule D bound either way: if a solution exists the value is
    /// integral and the floor is exact, and if none exists nothing can be
    /// wrongly pruned. See `distribution_integral`.
    pub fn n_dist(&self) -> Vec<u64> {
        let d = self.k as i128 + 1;
        self.n_num().into_iter().map(|x| (x / d).max(0) as u64).collect()
    }

    /// `M_j = C(k,j) * (C(k,j) - (-1)^(k+j)) / (k+1)`: blocks of one *other*
    /// class meeting a fixed block in exactly `j` points. Same integrality
    /// caveat as `n_dist`.
    pub fn m_dist(&self) -> Vec<u64> {
        let d = self.k as i128 + 1;
        self.m_num().into_iter().map(|x| (x / d).max(0) as u64).collect()
    }

    /// The `j` at which `N_j` or `M_j` fails to be an integer. Non-empty only
    /// for `k = 8` and `k = 14` in range; a non-empty result is a proof that
    /// no `S(k-1,k,2k)` exists.
    pub fn divisibility_obstruction(&self) -> Vec<(char, u32, i128)> {
        let d = self.k as i128 + 1;
        let mut out = Vec::new();
        for (j, x) in self.n_num().into_iter().enumerate() {
            if x % d != 0 {
                out.push(('N', j as u32, x));
            }
        }
        for (j, x) in self.m_num().into_iter().enumerate() {
            if x % d != 0 {
                out.push(('M', j as u32, x));
            }
        }
        out
    }

    pub fn distribution_integral(&self) -> bool {
        self.divisibility_obstruction().is_empty()
    }

    /// `Cat(k) = C(2k,k)/(k+1)`, the size of a colour class in `J(2k,k)`.
    pub fn catalan(&self) -> u64 {
        self.binom.c(2 * self.k, self.k) / (self.k as u64 + 1)
    }

    /// Rule D targets, indexed by `a = 0..=k-2`: `c_a + c_{k-2-a} = N_{a+1}`.
    ///
    /// Derivation (spec section 1, "Translating to O_k"): with `∞ = 2k-1`, the
    /// `O_k` vertex `T` is the block pair `{T ∪ {∞}, V \ T}`. For `T' ≠ T` with
    /// `a = |T ∩ T'|` the four induced block intersections have sizes `a+1`
    /// twice and `k-1-a` twice, so summing over the class gives
    /// `N_{a+1} = c_a + c_{k-1-(a+1)} = c_a + c_{k-2-a}`.
    pub fn rule_d_targets(&self) -> Vec<u64> {
        let n = self.n_dist();
        (0..=self.k - 2).map(|a| n[(a + 1) as usize]).collect()
    }

    /// Rule E targets, indexed by `a = 0..=k-2`: `d_a + d_{k-2-a} = M_{a+1}`.
    pub fn rule_e_targets(&self) -> Vec<u64> {
        let m = self.m_dist();
        (0..=self.k - 2).map(|a| m[(a + 1) as usize]).collect()
    }

    /// Whether Rules D/E should test intersection size `a`. `a ∈ {0, k-2}` is
    /// implied by Rule B (see ARCHITECTURE.md) and can never fire.
    #[inline]
    pub fn rule_de_active(&self, a: u32) -> bool {
        a >= 1 && a + 1 <= self.k - 2
    }

    // -- link regions (spec section 4) --------------------------------------

    /// Valid link levels are `1 ≤ t ≤ k-1`. `t = 0` is a single vertex and
    /// `t ≥ k` would make `λ` empty (or worse, underflow `k-t`), which also
    /// breaks the distinctness that the whole construction relies on:
    /// `λ ∪ B` and `λ ∪ B'` collide exactly when they are complementary, and
    /// `λ ≠ ∅` is what rules that out.
    #[inline]
    pub fn valid_link_level(&self, t: u32) -> bool {
        t >= 1 && t < self.k
    }

    /// Clamp a requested link level into the usable range.
    pub fn clamp_link_level(&self, t: u32) -> u32 {
        t.clamp(1, self.k - 1)
    }

    /// Number of `O_k` vertices in a level-`t` link region: `C(k+t, t)`.
    pub fn link_size(&self, t: u32) -> u64 {
        if !self.valid_link_level(t) {
            return 0;
        }
        self.binom.c(self.k + t, t)
    }

    /// Number of distinct `λ` at level `t`: the `(k-t)`-subsets of `[2k]`.
    pub fn link_count(&self, t: u32) -> u64 {
        if !self.valid_link_level(t) {
            return 0;
        }
        self.binom.c(2 * self.k, self.k - t)
    }

    /// Unrank a `(k-t)`-subset of `[2k]` (colex) as a bitmask over `[2k]`.
    pub fn unrank_lambda(&self, t: u32, idx: u64) -> u32 {
        if !self.valid_link_level(t) {
            return 0;
        }
        let size = self.k - t;
        let mut rem = idx;
        let mut mask = 0u32;
        for i in (0..size).rev() {
            let mut s = i;
            while self.binom.c(s + 1, i + 1) <= rem {
                s += 1;
            }
            mask |= 1u32 << s;
            rem -= self.binom.c(s, i + 1);
        }
        mask
    }

    /// Map a `k`-subset `s` of `[2k]` to its `O_k` vertex mask.
    /// `∞ = 2k-1`; if `∞ ∈ s` the vertex is `s \ {∞}`, else it is `V \ s`.
    #[inline]
    pub fn block_to_vertex(&self, s: u32) -> u32 {
        let inf = 1u32 << (2 * self.k - 1);
        if s & inf != 0 {
            s & !inf
        } else {
            self.full & !s
        }
    }

    /// The `O_k` vertices of the level-`t` link region of `λ`, together with the
    /// index (within the sorted ground set `[2k] \ λ`) of the `t`-subset `B`
    /// that produced them. Returned in a deterministic order.
    pub fn link_region(&self, lambda: u32, t: u32) -> Vec<LinkCell> {
        let ground: Vec<u32> = (0..2 * self.k).filter(|i| lambda & (1 << i) == 0).collect();
        let w = ground.len();
        let tt = t as usize;
        let mut out = Vec::with_capacity(self.link_size(t) as usize);
        if tt > w {
            return out;
        }
        let mut combo: Vec<usize> = (0..tt).collect();
        loop {
            let mut s = lambda;
            let mut pos = 0u32;
            for &c in &combo {
                s |= 1u32 << ground[c];
                pos |= 1u32 << c;
            }
            let vmask = self.block_to_vertex(s);
            out.push(LinkCell {
                vertex: self.rank(vmask),
                vmask,
                points: pos,
            });
            if !next_combination(&mut combo, w) {
                return out;
            }
        }
    }

    /// Every `(t-1)`-subset of the link ground set `[2k] \ λ`, as position
    /// bitmasks. Used by the rung check (each colour class restricted to the
    /// region must be an `S(t-1, t, k+t)`, so each of these must be covered
    /// exactly once per colour).
    #[allow(dead_code)]
    pub fn link_subsets(&self, w: usize, size: usize) -> Vec<u32> {
        let mut out = Vec::new();
        if size > w {
            return out;
        }
        let mut combo: Vec<usize> = (0..size).collect();
        loop {
            let mut pos = 0u32;
            for &c in &combo {
                pos |= 1u32 << c;
            }
            out.push(pos);
            if !next_combination(&mut combo, w) {
                return out;
            }
        }
    }
}

/// Advance `combo` (strictly increasing indices into `0..w`) to the next
/// combination in lexicographic order. Returns false when exhausted.
fn next_combination(combo: &mut [usize], w: usize) -> bool {
    let t = combo.len();
    if t == 0 {
        return false;
    }
    let mut i = t;
    loop {
        if i == 0 {
            return false;
        }
        i -= 1;
        if combo[i] < w - t + i {
            combo[i] += 1;
            for j in i + 1..t {
                combo[j] = combo[j - 1] + 1;
            }
            return true;
        }
    }
}

/// One cell of a link region: an `O_k` vertex plus the `t`-subset (as a bitmask
/// over positions in the sorted ground set `[2k] \ λ`) that generated it.
#[derive(Clone, Copy, Debug)]
pub struct LinkCell {
    pub vertex: u32,
    #[allow(dead_code)]
    pub vmask: u32,
    pub points: u32,
}

pub struct NeighborIter {
    comp: u32,
    rest: u32,
}

impl Iterator for NeighborIter {
    type Item = u32;
    #[inline(always)]
    fn next(&mut self) -> Option<u32> {
        if self.rest == 0 {
            return None;
        }
        let b = self.rest & self.rest.wrapping_neg();
        self.rest &= self.rest - 1;
        Some(self.comp & !b)
    }
}

// ---------------------------------------------------------------------------
// info subcommand
// ---------------------------------------------------------------------------

pub fn print_info(c: &Combi) {
    use crate::util::{commas, fmt_bytes};
    let nd = c.n_dist();
    let md = c.m_dist();
    println!("odd835 info");
    println!("  k                    {}", c.k);
    println!("  ground set [n]       n = 2k-1 = {}", c.n);
    println!("  vertices             (k-1)-subsets of [n], |V| = C({},{}) = {}", c.n, c.r, commas(c.num_vertices));
    println!("  adjacency            T ~ U  iff  T n U = empty");
    println!("  degree               {}", c.k);
    println!("  closed nbhd size     {}", c.colors);
    println!("  colours              {} (fixed, never configurable)", c.colors);
    println!("  perfect code size m  {}", commas(c.m));
    println!("  Cat(k) = C(2k,k)/(k+1)  {}", commas(c.catalan()));
    println!();
    println!("  state memory         color {}   dom {}   sat {}",
        fmt_bytes(c.num_vertices),
        fmt_bytes(c.num_vertices * 4),
        fmt_bytes(c.num_vertices));
    println!();
    println!("  block intersection distribution (structure theorem, exact)");
    let nn = c.n_num();
    let mn = c.m_num();
    let den = c.k as i128 + 1;
    let render = |num: i128| -> String {
        if num % den == 0 {
            commas((num / den) as u64)
        } else {
            format!("{}/{}", num, den)
        }
    };
    print!("    j    ");
    for j in 0..=c.k {
        print!("{:>14}", j);
    }
    println!();
    print!("    N_j  ");
    for j in 0..=c.k {
        print!("{:>14}", render(nn[j as usize]));
    }
    println!();
    print!("    M_j  ");
    for j in 0..=c.k {
        print!("{:>14}", render(mn[j as usize]));
    }
    println!();
    println!(
        "    sum N_j = sum M_j = Cat(k) = {}  (exact as rationals)",
        commas(c.catalan())
    );
    let obstruction = c.divisibility_obstruction();
    if !obstruction.is_empty() {
        println!();
        println!("  *** DIVISIBILITY OBSTRUCTION ***");
        println!("    N_j / M_j are counts of blocks, so they must be integers. At k = {} they", c.k);
        println!("    are not:");
        for (which, j, num) in obstruction.iter().take(6) {
            println!("      {which}_{j} = {num}/{den}");
        }
        if obstruction.len() > 6 {
            println!("      ... and {} more", obstruction.len() - 6);
        }
        println!("    No Steiner system S({},{},{}) exists, hence no perfect 1-code in O_{}", c.k - 1, c.k, 2 * c.k, c.k);
        println!("    and no partition. The search will still prove it the hard way; this is the");
        println!("    arithmetic reason a blind search may take effectively forever here.");
        println!("    Rule D/E targets below are floors, which remain sound bounds.");
    }
    println!();
    println!("  Rule D / Rule E targets in O_k coordinates");
    println!("    a      a'=k-2-a   N_(a+1) = c_a + c_a'    M_(a+1) = d_a + d_a'   checked");
    for a in 0..=c.k - 2 {
        let ap = c.k - 2 - a;
        if a > ap {
            continue;
        }
        println!(
            "    {:<6} {:<10} {:>18}   {:>20}   {}",
            a,
            ap,
            commas(nd[(a + 1) as usize]),
            commas(md[(a + 1) as usize]),
            if c.rule_de_active(a) { "yes" } else { "no (implied by Rule B)" }
        );
    }
    println!();
    println!("  link regions");
    for t in 1..=4.min(c.k - 1) {
        println!(
            "    t = {}   |region| = C(k+t,t) = {:<10}  lambda count = C(2k,k-t) = {}",
            t,
            commas(c.link_size(t)),
            commas(c.link_count(t))
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn odd_k_is_rejected() {
        for k in [3u32, 5, 7, 9, 11, 13, 15] {
            let e = match Combi::new(k) {
                Ok(_) => panic!("odd k = {k} must be rejected"),
                Err(e) => e.to_string(),
            };
            assert!(e.contains("odd"), "message for k={k} should explain oddness");
        }
    }

    #[test]
    fn derived_constants_match_spec_table() {
        let expect: &[(u32, u64, u32, u64)] = &[
            (2, 3, 3, 1),
            (4, 35, 5, 7),
            (6, 462, 7, 66),
            (8, 6435, 9, 715),
            (10, 92378, 11, 8398),
            (12, 1352078, 13, 104006),
            (14, 20058300, 15, 1337220),
            (16, 300540195, 17, 17678835),
        ];
        for &(k, v, cols, m) in expect {
            let c = Combi::new(k).unwrap();
            assert_eq!(c.num_vertices, v, "|V| for k={k}");
            assert_eq!(c.colors, cols, "colors for k={k}");
            assert_eq!(c.m, m, "m for k={k}");
        }
    }

    #[test]
    fn rank_tables_agree_with_reference() {
        for k in [2u32, 4, 6, 8, 10, 12] {
            let c = Combi::new(k).unwrap();
            for i in 0..c.num_vertices as u32 {
                let mask = c.unrank(i);
                assert_eq!(c.rank(mask), c.rank_ref(mask), "k={k} idx={i}");
                assert_eq!(c.rank(mask), i, "k={k} idx={i}");
            }
        }
    }

    #[test]
    fn n_and_m_distributions_match_spec_k10() {
        let c = Combi::new(10).unwrap();
        assert_eq!(c.n_dist(), vec![1, 0, 225, 1200, 4200, 5544, 4200, 1200, 225, 0, 1]);
        assert_eq!(c.m_dist(), vec![0, 10, 180, 1320, 3990, 5796, 3990, 1320, 180, 10, 0]);
        assert_eq!(c.catalan(), 16796);
    }

    #[test]
    fn de_targets_match_spec_k16() {
        let c = Combi::new(16).unwrap();
        let d = c.rule_d_targets();
        let e = c.rule_e_targets();
        let nexp = [0u64, 960, 17920, 196560, 1118208, 3779776, 7687680, 9755460];
        let mexp = [16u64, 840, 18480, 194740, 1122576, 3771768, 7699120, 9742590];
        for a in 0..8usize {
            assert_eq!(d[a], nexp[a], "N_{} at a={}", a + 1, a);
            assert_eq!(e[a], mexp[a], "M_{} at a={}", a + 1, a);
        }
    }

    #[test]
    fn distributions_sum_to_catalan() {
        // The individual N_j / M_j are not integral for every even k (they are
        // not at k=8 or k=14), but the sums are exactly Cat(k) as rationals:
        // sum_j C(k,j)^2 = C(2k,k) and sum_j (-1)^j C(k,j) = 0.
        for k in [2u32, 4, 6, 8, 10, 12, 14, 16] {
            let c = Combi::new(k).unwrap();
            let cat = c.catalan() as i128;
            let d = k as i128 + 1;
            assert_eq!(c.n_num().iter().sum::<i128>(), cat * d, "sum N_j, k={k}");
            assert_eq!(c.m_num().iter().sum::<i128>(), cat * d, "sum M_j, k={k}");
            let nd = c.n_dist();
            let md = c.m_dist();
            assert_eq!(nd[0], 1);
            assert_eq!(nd[k as usize], 1);
            assert_eq!(nd[1], 0);
            assert_eq!(nd[k as usize - 1], 0);
            assert_eq!(md[0], 0);
            assert_eq!(md[k as usize], 0);
            assert_eq!(md[1], k as u64);
        }
    }

    #[test]
    fn divisibility_obstruction_is_exactly_k8_and_k14() {
        for k in [2u32, 4, 6, 10, 12, 16] {
            assert!(
                Combi::new(k).unwrap().distribution_integral(),
                "k={k} should have integral N_j / M_j"
            );
        }
        for k in [8u32, 14] {
            let c = Combi::new(k).unwrap();
            assert!(
                !c.distribution_integral(),
                "k={k} must expose the divisibility obstruction"
            );
            // it first appears at j = 3
            assert_eq!(c.divisibility_obstruction()[0].1, 3, "k={k}");
        }
    }

    #[test]
    fn link_region_sizes() {
        let c = Combi::new(16).unwrap();
        assert_eq!(c.link_size(2), 153);
        assert_eq!(c.link_size(3), 969);
        let lambda = c.unrank_lambda(2, 0);
        assert_eq!(lambda.count_ones(), 14);
        let region = c.link_region(lambda, 2);
        assert_eq!(region.len(), 153);
        let mut seen: Vec<u32> = region.iter().map(|x| x.vertex).collect();
        seen.sort_unstable();
        seen.dedup();
        assert_eq!(seen.len(), 153, "link cells must be distinct vertices");
    }
}
