//! Independent checker (spec section 6).
//!
//! This module shares nothing with the solver except `rank`/`unrank` and the
//! binomial table. Every combinatorial property below is recomputed here from
//! the definitions in spec section 1:
//!
//!   * vertices are the `(k-1)`-subsets of `[n]`, `n = 2k-1`;
//!   * `T ~ U` iff `T ∩ U = ∅`;
//!   * `N[T] = {T} ∪ N(T)`.
//!
//! In particular the neighbour enumeration here does *not* call
//! `Combi::neighbors`. It enumerates every `(k-1)`-subset of `[n] \ T` with its
//! own generic subset generator; that these are precisely the vertices disjoint
//! from `T` is immediate (`U ∩ T = ∅` and `U ⊆ [n]` give `U ⊆ [n] \ T`), and the
//! oracle suite additionally confirms it by brute-force pairwise disjointness
//! testing at `k ≤ 8`.

use crate::combi::Combi;
use crate::witness::Witness;
use anyhow::{bail, Result};
use std::path::Path;

#[derive(Debug, Clone)]
pub struct CheckItem {
    pub name: &'static str,
    pub pass: bool,
    pub detail: String,
}

#[derive(Debug, Clone)]
pub struct CheckReport {
    pub kind: String,
    pub k: u32,
    pub items: Vec<CheckItem>,
}

impl CheckReport {
    pub fn ok(&self) -> bool {
        self.items.iter().all(|i| i.pass)
    }
    pub fn print(&self) {
        println!("check  kind={}  k={}", self.kind, self.k);
        for i in &self.items {
            println!(
                "  [{}] {:<28} {}",
                if i.pass { "ok " } else { "FAIL" },
                i.name,
                i.detail
            );
        }
        println!(
            "  => {}",
            if self.ok() { "WITNESS VALID" } else { "WITNESS INVALID" }
        );
    }
}

// ---------------------------------------------------------------------------
// Independent combinatorial primitives
// ---------------------------------------------------------------------------

/// All `size`-subsets of `set` (a bitmask), as bitmasks. Written here from
/// scratch; deliberately generic and slow rather than reusing the solver's
/// specialised neighbour iterator.
pub fn subsets_of_size(set: u32, size: u32) -> Vec<u32> {
    let bits: Vec<u32> = (0..32).filter(|i| set & (1 << i) != 0).collect();
    let w = bits.len();
    let s = size as usize;
    let mut out = Vec::new();
    if s > w {
        return out;
    }
    let mut idx: Vec<usize> = (0..s).collect();
    loop {
        let mut m = 0u32;
        for &i in &idx {
            m |= 1 << bits[i];
        }
        out.push(m);
        if s == 0 {
            return out;
        }
        let mut i = s;
        loop {
            if i == 0 {
                return out;
            }
            i -= 1;
            if idx[i] < w - s + i {
                idx[i] += 1;
                for j in i + 1..s {
                    idx[j] = idx[j - 1] + 1;
                }
                break;
            }
            if i == 0 {
                return out;
            }
        }
    }
}

/// Neighbours of `t` in `O_k`, from the definition: the `(k-1)`-subsets of
/// `[n]` disjoint from `t`.
pub fn neighbors_from_definition(t: u32, n: u32, r: u32) -> Vec<u32> {
    let ground = (1u32 << n) - 1;
    subsets_of_size(ground & !t, r)
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

pub fn check_file(path: &Path, expect_k: Option<u32>) -> Result<CheckReport> {
    let w = Witness::read(path)?;
    if let Some(k) = expect_k {
        if w.k() != k {
            bail!("witness is for k = {} but -k {} was given", w.k(), k);
        }
    }
    check_witness(&w)
}

pub fn check_witness(w: &Witness) -> Result<CheckReport> {
    match w {
        Witness::Partition { k, colors } => check_partition(*k, colors),
        Witness::Code { k, members } => check_code_witness(*k, members),
    }
}

// ---------------------------------------------------------------------------
// Partition witness
// ---------------------------------------------------------------------------

fn check_partition(k: u32, colors: &[u8]) -> Result<CheckReport> {
    let c = Combi::new(k)?;
    let n = c.n;
    let r = c.r;
    let nv = c.num_vertices as usize;
    let ncol = (k + 1) as usize;
    let m = c.m;
    let mut items = Vec::new();

    if colors.len() != nv {
        bail!("witness has {} entries, O_{k} has {nv} vertices", colors.len());
    }

    // (1) every vertex has exactly one colour in 0..=k
    let bad: Vec<usize> = colors
        .iter()
        .enumerate()
        .filter(|(_, x)| **x as u32 > k)
        .map(|(i, _)| i)
        .take(4)
        .collect();
    items.push(CheckItem {
        name: "one colour per vertex",
        pass: bad.is_empty(),
        detail: if bad.is_empty() {
            format!("{nv} vertices, colours in 0..={k}")
        } else {
            format!("out-of-range colours at vertices {bad:?}")
        },
    });

    // Recompute every vertex mask independently and confirm the colex indexing
    // agrees with the reference formula. Bail early if not: everything below
    // depends on the index <-> mask correspondence.
    let mut masks = vec![0u32; nv];
    {
        let mut ok = true;
        let all = subsets_of_size((1u32 << n) - 1, r);
        if all.len() != nv {
            bail!("independent enumeration found {} vertices, expected {nv}", all.len());
        }
        for mask in all {
            let idx = c.rank_ref(mask) as usize;
            if idx >= nv || masks[idx] != 0 {
                ok = false;
                break;
            }
            masks[idx] = mask;
        }
        // vertex 0 is the colex-least subset, whose mask may legitimately be
        // small but never zero for r >= 1
        ok &= masks.iter().all(|m| m.count_ones() == r);
        items.push(CheckItem {
            name: "colex index is a bijection",
            pass: ok,
            detail: format!("{nv} distinct (k-1)-subsets of [{n}]"),
        });
        if !ok {
            return Ok(CheckReport { kind: "partition".into(), k, items });
        }
    }

    // (2) every vertex has exactly k neighbours
    let mut degree_ok = true;
    let mut degree_detail = format!("all degrees = {k}");
    for (i, &mask) in masks.iter().enumerate() {
        let nb = neighbors_from_definition(mask, n, r);
        if nb.len() != k as usize {
            degree_ok = false;
            degree_detail = format!("vertex {i} has degree {}", nb.len());
            break;
        }
    }
    items.push(CheckItem {
        name: "degree",
        pass: degree_ok,
        detail: degree_detail,
    });

    // (3) every closed neighbourhood carries each colour exactly once
    let mut rainbow_ok = true;
    let mut rainbow_detail = format!("{nv} closed neighbourhoods are rainbow");
    for (i, &mask) in masks.iter().enumerate() {
        let mut seen = 0u32;
        let mut count = 1usize;
        seen |= 1u32 << colors[i];
        for u in neighbors_from_definition(mask, n, r) {
            let ui = c.rank_ref(u) as usize;
            let bit = 1u32 << colors[ui];
            if seen & bit != 0 {
                rainbow_ok = false;
                rainbow_detail = format!(
                    "N[{i}] repeats colour {} (vertex {ui})",
                    colors[ui]
                );
                break;
            }
            seen |= bit;
            count += 1;
        }
        if !rainbow_ok {
            break;
        }
        if count != ncol || seen != (1u32 << ncol) - 1 {
            rainbow_ok = false;
            rainbow_detail = format!("N[{i}] has {count} members / colour set {seen:#x}");
            break;
        }
    }
    items.push(CheckItem {
        name: "closed nbhds rainbow",
        pass: rainbow_ok,
        detail: rainbow_detail,
    });

    // (4) every class has size exactly m
    let mut sizes = vec![0u64; ncol];
    for &x in colors {
        if (x as usize) < ncol {
            sizes[x as usize] += 1;
        }
    }
    let size_ok = sizes.iter().all(|s| *s == m);
    items.push(CheckItem {
        name: "class sizes",
        pass: size_ok,
        detail: if size_ok {
            format!("all {ncol} classes have m = {m}")
        } else {
            format!("sizes {sizes:?}, expected {m}")
        },
    });

    // (5) each class is a perfect 1-code
    let mut cover = vec![0u32; nv];
    let mut code_ok = true;
    let mut code_detail = format!("all {ncol} classes are perfect 1-codes");
    for col in 0..ncol {
        cover.iter_mut().for_each(|x| *x = 0);
        for (i, &mask) in masks.iter().enumerate() {
            if colors[i] as usize != col {
                continue;
            }
            cover[i] += 1;
            for u in neighbors_from_definition(mask, n, r) {
                cover[c.rank_ref(u) as usize] += 1;
            }
        }
        if let Some(pos) = cover.iter().position(|x| *x != 1) {
            code_ok = false;
            code_detail = format!(
                "class {col}: vertex {pos} is covered {} times, expected 1",
                cover[pos]
            );
            break;
        }
    }
    items.push(CheckItem {
        name: "classes are perfect 1-codes",
        pass: code_ok,
        detail: code_detail,
    });

    Ok(CheckReport {
        kind: "partition".into(),
        k,
        items,
    })
}

// ---------------------------------------------------------------------------
// Single-code witness
// ---------------------------------------------------------------------------

fn check_code_witness(k: u32, members: &[u32]) -> Result<CheckReport> {
    let c = Combi::new(k)?;
    let n = c.n;
    let r = c.r;
    let nv = c.num_vertices as usize;
    let m = c.m;
    let mut items = Vec::new();

    let mut sorted = members.to_vec();
    sorted.sort_unstable();
    let distinct = {
        let mut d = sorted.clone();
        d.dedup();
        d.len() == sorted.len()
    };
    let in_range = sorted.last().map(|x| (*x as usize) < nv).unwrap_or(true);
    items.push(CheckItem {
        name: "members well formed",
        pass: distinct && in_range,
        detail: format!("{} members, distinct={distinct}, in range={in_range}", members.len()),
    });

    items.push(CheckItem {
        name: "code size",
        pass: members.len() as u64 == m,
        detail: format!("|S| = {}, expected m = {m}", members.len()),
    });

    if !(distinct && in_range) {
        return Ok(CheckReport { kind: "code".into(), k, items });
    }

    // degree check on the members
    let mut degree_ok = true;
    for &v in &sorted {
        let mask = c.unrank(v);
        if neighbors_from_definition(mask, n, r).len() != k as usize {
            degree_ok = false;
            break;
        }
    }
    items.push(CheckItem {
        name: "degree",
        pass: degree_ok,
        detail: format!("every member has {k} neighbours"),
    });

    // perfect 1-code: cover every vertex exactly once
    let mut cover = vec![0u32; nv];
    for &v in &sorted {
        let mask = c.unrank(v);
        cover[v as usize] += 1;
        for u in neighbors_from_definition(mask, n, r) {
            cover[c.rank_ref(u) as usize] += 1;
        }
    }
    let bad = cover.iter().position(|x| *x != 1);
    items.push(CheckItem {
        name: "perfect 1-code",
        pass: bad.is_none(),
        detail: match bad {
            None => format!("all {nv} vertices covered exactly once"),
            Some(p) => format!("vertex {p} covered {} times", cover[p]),
        },
    });

    Ok(CheckReport {
        kind: "code".into(),
        k,
        items,
    })
}

// ---------------------------------------------------------------------------
// Helpers used by the oracle suite
// ---------------------------------------------------------------------------

/// Is `blocks` a perfect 1-code in `O_k`? Recomputed from the definition.
pub fn is_perfect_code(k: u32, blocks: &[u32]) -> Result<bool> {
    let c = Combi::new(k)?;
    let mut cover = vec![0u32; c.num_vertices as usize];
    for &b in blocks {
        if b.count_ones() != c.r {
            return Ok(false);
        }
        cover[c.rank_ref(b) as usize] += 1;
        for u in neighbors_from_definition(b, c.n, c.r) {
            cover[c.rank_ref(u) as usize] += 1;
        }
    }
    Ok(cover.iter().all(|x| *x == 1))
}

/// Brute-force `c_a` profile of a code: for each block, how many other blocks
/// meet it in exactly `a` points, `a = 0..=k-2`. Used for the ground-truth
/// intersection oracle.
pub fn intersection_profile(k: u32, blocks: &[u32]) -> Vec<Vec<u64>> {
    let mut out = Vec::with_capacity(blocks.len());
    for (i, &b) in blocks.iter().enumerate() {
        let mut d = vec![0u64; (k - 1) as usize];
        for (j, &o) in blocks.iter().enumerate() {
            if i == j {
                continue;
            }
            d[(b & o).count_ones() as usize] += 1;
        }
        out.push(d);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::designs::{FANO, WITT_S4_5_11};

    #[test]
    fn subset_generator() {
        assert_eq!(subsets_of_size(0b1111, 2).len(), 6);
        assert_eq!(subsets_of_size(0b1111, 0), vec![0]);
        assert_eq!(subsets_of_size(0b1111, 4), vec![0b1111]);
        assert_eq!(subsets_of_size(0b1111, 5).len(), 0);
    }

    #[test]
    fn definition_neighbours_match_pairwise_disjointness_small_k() {
        // The strongest possible independence check: brute-force every pair.
        for k in [2u32, 4, 6, 8] {
            let c = Combi::new(k).unwrap();
            let all = subsets_of_size((1u32 << c.n) - 1, c.r);
            assert_eq!(all.len() as u64, c.num_vertices);
            for &t in &all {
                let mut brute: Vec<u32> =
                    all.iter().cloned().filter(|u| *u & t == 0).collect();
                brute.sort_unstable();
                let mut def = neighbors_from_definition(t, c.n, c.r);
                def.sort_unstable();
                assert_eq!(def, brute, "k={k} t={t:#x}");
                assert_eq!(def.len(), k as usize);
            }
        }
    }

    #[test]
    fn fano_and_witt_are_perfect_codes() {
        assert!(is_perfect_code(4, &FANO).unwrap(), "Fano in O_4");
        assert!(is_perfect_code(6, &WITT_S4_5_11).unwrap(), "Witt in O_6");
    }

    #[test]
    fn ground_truth_intersection_profiles() {
        // c_a + c_{k-2-a} must equal N_{a+1} exactly, for real designs.
        for (k, blocks) in [(4u32, &FANO[..]), (6u32, &WITT_S4_5_11[..])] {
            let c = Combi::new(k).unwrap();
            let targets = c.rule_d_targets();
            for prof in intersection_profile(k, blocks) {
                for a in 0..=(k - 2) as usize {
                    let mirror = (k - 2) as usize - a;
                    assert_eq!(
                        prof[a] + prof[mirror],
                        targets[a],
                        "k={k} a={a}: c_a={} c_a'={} target={}",
                        prof[a],
                        prof[mirror],
                        targets[a]
                    );
                }
                // the two cases Rules D/E skip
                assert_eq!(prof[0], 0, "c_0 must be 0 (same-class vertices are non-adjacent)");
                assert_eq!(prof[(k - 2) as usize], 0, "c_{{k-2}} must be 0");
            }
        }
    }
}
