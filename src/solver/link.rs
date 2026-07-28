//! Link-ordered branching and rung checks (spec section 4 / section 8).
//!
//! For a level `t` and a `(k-t)`-subset `λ ⊂ [2k]`, the `k`-sets `λ ∪ B` for
//! `B ∈ binom([2k]\λ, t)` map to `C(k+t, t)` distinct `O_k` vertices. The
//! structure theorem forces the colours on that region to form a large set
//! `LS(t-1, t, k+t)`: each colour class restricted to the region must be a
//! Steiner system `S(t-1, t, k+t)`, i.e. every `(t-1)`-subset of the `k+t`
//! remaining ground points is covered exactly once per colour.
//!
//! `t = 1` degenerates to "every closed neighbourhood is rainbow", which is
//! exactly Rule B; `t >= 2` is genuinely stronger and is what makes the rung
//! check worth running.

use crate::combi::{Combi, LinkCell};
use crate::util::Rng;

pub struct LinkPlan {
    pub t: u32,
    pub total: u64,
    pub cursor: u64,
    pub lambda: u32,
    pub cells: Vec<LinkCell>,
}

impl LinkPlan {
    pub fn new(c: &Combi, t: u32, seed: u64) -> LinkPlan {
        let total = c.link_count(t);
        // A seeded starting offset keeps runs deterministic while letting the
        // operator explore different regions.
        let cursor = if seed == 0 {
            0
        } else {
            Rng::new(seed).below(total.max(1))
        };
        let mut p = LinkPlan {
            t,
            total,
            cursor,
            lambda: 0,
            cells: Vec::new(),
        };
        p.load(c, cursor);
        p
    }

    fn load(&mut self, c: &Combi, cursor: u64) {
        self.cursor = cursor % self.total.max(1);
        self.lambda = c.unrank_lambda(self.t, self.cursor);
        self.cells = c.link_region(self.lambda, self.t);
    }

    /// Move to the next `λ`. Colex order makes consecutive `λ` overlap heavily,
    /// which is what makes the cascade in the spec work.
    pub fn advance(&mut self, c: &Combi) {
        let next = (self.cursor + 1) % self.total.max(1);
        self.load(c, next);
    }

    pub fn seek(&mut self, c: &Combi, cursor: u64) {
        self.load(c, cursor);
    }
}

/// Colex rank of a `size`-subset of positions, used to index the `(t-1)`-subset
/// coverage table.
fn pos_rank(c: &Combi, mut mask: u32) -> usize {
    let mut sum = 0u64;
    let mut j = 0u32;
    while mask != 0 {
        let q = mask.trailing_zeros();
        mask &= mask - 1;
        sum += c.binom.c(q, j + 1);
        j += 1;
    }
    sum as usize
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RungVerdict {
    /// The region is not fully assigned; nothing can be concluded.
    Incomplete { assigned: usize, total: usize },
    Pass,
    Fail(String),
}

/// Verify that a fully assigned link region induces the large set
/// `LS(t-1, t, k+t)`. `color_of(vertex) -> Option<u8>`.
pub fn check_link<F>(c: &Combi, plan_t: u32, cells: &[LinkCell], color_of: F) -> RungVerdict
where
    F: Fn(u32) -> Option<u8>,
{
    let mut colors = Vec::with_capacity(cells.len());
    let mut assigned = 0usize;
    for cell in cells {
        match color_of(cell.vertex) {
            Some(x) => {
                colors.push(x);
                assigned += 1;
            }
            None => colors.push(u8::MAX),
        }
    }
    if assigned != cells.len() {
        return RungVerdict::Incomplete {
            assigned,
            total: cells.len(),
        };
    }
    if plan_t == 0 {
        return RungVerdict::Pass;
    }
    let w = (c.k + plan_t) as usize;
    let sub = plan_t - 1;
    let nsub = c.binom.c(w as u32, sub) as usize;
    let ncol = c.colors as usize;
    let mut cover = vec![0u32; nsub * ncol];

    for (cell, &col) in cells.iter().zip(colors.iter()) {
        // every (t-1)-subset of this cell's t-subset
        let pts = cell.points;
        if sub == 0 {
            cover[col as usize] += 1;
            continue;
        }
        let mut rest = pts;
        while rest != 0 {
            let drop = rest & rest.wrapping_neg();
            rest &= rest - 1;
            let p = pts & !drop;
            let r = pos_rank(c, p);
            cover[r * ncol + col as usize] += 1;
        }
    }
    for r in 0..nsub {
        for col in 0..ncol {
            let v = cover[r * ncol + col];
            if v != 1 {
                return RungVerdict::Fail(format!(
                    "(t-1)-subset #{r} is covered {v} times by colour {col}, expected exactly 1"
                ));
            }
        }
    }
    RungVerdict::Pass
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::neighbors_from_definition;
    use crate::designs::FANO;

    /// A single perfect code induces `S(t-1,t,k+t)` on every link region, since
    /// it is one class of the (hypothetical) partition. Verified here against
    /// the Fano code at `k = 4`, `t = 2`, by colouring code members 0 and
    /// everything else with a filler colour that is ignored.
    #[test]
    fn fano_link_regions_induce_the_large_set_class() {
        let c = Combi::new(4).unwrap();
        let members: Vec<u32> = FANO.iter().map(|b| c.rank(*b)).collect();
        let t = 2;
        for idx in 0..c.link_count(t) {
            let lambda = c.unrank_lambda(t, idx);
            let cells = c.link_region(lambda, t);
            assert_eq!(cells.len(), c.link_size(t) as usize);
            // count how many cells are code members; for an S(1,2,6) class the
            // members must form a perfect matching on the 6 remaining points
            let hits: Vec<&LinkCell> = cells
                .iter()
                .filter(|x| members.contains(&x.vertex))
                .collect();
            assert_eq!(hits.len(), 3, "lambda {lambda:#x}");
            let mut cover = 0u32;
            for h in &hits {
                assert_eq!(h.points.count_ones(), 2);
                assert_eq!(cover & h.points, 0, "blocks overlap: lambda {lambda:#x}");
                cover |= h.points;
            }
            assert_eq!(cover.count_ones(), 6);
        }
    }

    /// `t = 1` carries no information beyond Rule B.
    ///
    /// A level-1 region is `k+1` vertices that must be rainbow. There are two
    /// shapes, depending on whether `λ` contains `∞ = 2k-1`:
    ///
    ///   * `∞ ∉ λ` — the region is literally a closed neighbourhood `N[λ]`;
    ///   * `∞ ∈ λ` — the region is the `k+1` vertices containing a fixed
    ///     `(k-2)`-set, which pairwise meet in `k-2` points.
    ///
    /// In both cases *every pair* in the region lies in a common closed
    /// neighbourhood, so Rule B alone forces the region rainbow. That is why
    /// `--rung-check 1` would be pure overhead and the interesting levels start
    /// at `t = 2`.
    #[test]
    fn level_one_link_adds_nothing_to_rule_b() {
        for k in [4u32, 6] {
            let c = Combi::new(k).unwrap();
            // precompute every closed neighbourhood as a sorted mask list
            let all = crate::check::subsets_of_size((1u32 << c.n) - 1, c.r);
            let nbhds: Vec<Vec<u32>> = all
                .iter()
                .map(|&t| {
                    let mut v = neighbors_from_definition(t, c.n, c.r);
                    v.push(t);
                    v.sort_unstable();
                    v
                })
                .collect();
            for idx in 0..c.link_count(1).min(300) {
                let lambda = c.unrank_lambda(1, idx);
                let cells = c.link_region(lambda, 1);
                assert_eq!(cells.len() as u32, k + 1, "lambda {lambda:#x}");
                let masks: Vec<u32> = cells.iter().map(|x| x.vmask).collect();
                let mut d = masks.clone();
                d.sort_unstable();
                d.dedup();
                assert_eq!(d.len(), masks.len(), "region has duplicates");
                for i in 0..masks.len() {
                    for j in i + 1..masks.len() {
                        let shared = nbhds
                            .iter()
                            .filter(|nb| nb.contains(&masks[i]) && nb.contains(&masks[j]))
                            .count();
                        assert!(
                            shared >= 1,
                            "k={k} lambda={lambda:#x}: {:#x} and {:#x} share no closed nbhd",
                            masks[i],
                            masks[j]
                        );
                    }
                }
            }
        }
    }
}
