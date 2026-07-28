//! Independent verifier for a claimed S(4,5,v).
//!
//! Shares nothing with the engine — no ranking tables, no incidence tables, no
//! bitmask tricks carried over. It expands every block into its five 4-subsets
//! by explicit enumeration and checks the covering condition directly from the
//! definition: every 4-subset of `[v]` lies in exactly one block.

use anyhow::{bail, Result};
use std::collections::HashMap;
use std::io::Write;

fn points(mask: u32, v: u32) -> Vec<u32> {
    (0..v).filter(|i| mask & (1 << i) != 0).collect()
}

/// `Ok(message)` if `blocks` is a valid S(4,5,v).
pub fn verify(v: u32, blocks: &[u32]) -> std::result::Result<String, String> {
    let n_choose = |n: u64, r: u64| -> u64 {
        let mut x = 1u128;
        for i in 0..r {
            x = x * (n - i) as u128 / (i + 1) as u128;
        }
        x as u64
    };
    let need = n_choose(v as u64, 4);
    let expect_blocks = need / 5;

    for &b in blocks {
        let p = points(b, v);
        if p.len() != 5 {
            return Err(format!("block {b:#x} has {} points, expected 5", p.len()));
        }
        if p.iter().any(|&x| x >= v) {
            return Err(format!("block {b:#x} has a point outside [0,{v})"));
        }
    }
    {
        let mut s: Vec<u32> = blocks.to_vec();
        s.sort_unstable();
        s.dedup();
        if s.len() != blocks.len() {
            return Err("duplicate blocks".into());
        }
    }
    if blocks.len() as u64 != expect_blocks {
        return Err(format!(
            "{} blocks, an S(4,5,{v}) has exactly {expect_blocks}",
            blocks.len()
        ));
    }

    // every 4-subset of a block, counted
    let mut seen: HashMap<[u32; 4], u32> = HashMap::with_capacity(need as usize);
    for &b in blocks {
        let p = points(b, v);
        for drop in 0..5 {
            let mut q = [0u32; 4];
            let mut k = 0;
            for (i, &x) in p.iter().enumerate() {
                if i != drop {
                    q[k] = x;
                    k += 1;
                }
            }
            if let Some(prev) = seen.insert(q, b) {
                return Err(format!(
                    "4-set {:?} appears in blocks {:#x} and {:#x}",
                    q, prev, b
                ));
            }
        }
    }
    if seen.len() as u64 != need {
        return Err(format!("covered {} of {need} 4-subsets", seen.len()));
    }

    // and independently: enumerate all 4-subsets and confirm each was hit
    let mut missing = 0u64;
    for a in 0..v {
        for b2 in a + 1..v {
            for c in b2 + 1..v {
                for d in c + 1..v {
                    if !seen.contains_key(&[a, b2, c, d]) {
                        missing += 1;
                    }
                }
            }
        }
    }
    if missing != 0 {
        return Err(format!("{missing} 4-subsets uncovered"));
    }

    Ok(format!(
        "valid S(4,5,{v}): {} blocks, all {need} 4-subsets covered exactly once",
        blocks.len()
    ))
}

pub fn write_blocks(path: &str, v: u32, blocks: &[u32]) -> Result<()> {
    let mut rows: Vec<Vec<u32>> = blocks.iter().map(|&b| points(b, v)).collect();
    rows.sort();
    let mut f = std::fs::File::create(path)?;
    for r in rows {
        writeln!(
            f,
            "{}",
            r.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
        )?;
    }
    Ok(())
}

pub fn read_blocks(path: &str) -> Result<Vec<u32>> {
    let body = std::fs::read_to_string(path)?;
    let mut out = Vec::new();
    for line in body.lines() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let mut m = 0u32;
        for tok in t.split_whitespace() {
            let x: u32 = tok.parse()?;
            if x >= 32 {
                bail!("point {x} out of range");
            }
            m |= 1 << x;
        }
        out.push(m);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Witt design S(4,5,11) — the same literal data odd835 uses as an
    /// oracle, re-expressed as point lists.
    const WITT: [[u32; 5]; 66] = [
        [0, 1, 2, 3, 9], [0, 1, 2, 4, 7], [0, 1, 2, 5, 6], [0, 1, 2, 8, 10],
        [0, 1, 3, 4, 8], [0, 1, 3, 5, 7], [0, 1, 3, 6, 10], [0, 1, 4, 5, 10],
        [0, 1, 4, 6, 9], [0, 1, 5, 8, 9], [0, 1, 6, 7, 8], [0, 1, 7, 9, 10],
        [0, 2, 3, 4, 5], [0, 2, 3, 6, 8], [0, 2, 3, 7, 10], [0, 2, 4, 6, 10],
        [0, 2, 4, 8, 9], [0, 2, 5, 7, 8], [0, 2, 5, 9, 10], [0, 2, 6, 7, 9],
        [0, 3, 4, 6, 7], [0, 3, 4, 9, 10], [0, 3, 5, 6, 9], [0, 3, 5, 8, 10],
        [0, 3, 7, 8, 9], [0, 4, 5, 6, 8], [0, 4, 5, 7, 9], [0, 4, 7, 8, 10],
        [0, 5, 6, 7, 10], [0, 6, 8, 9, 10], [1, 2, 3, 4, 10], [1, 2, 3, 5, 8],
        [1, 2, 3, 6, 7], [1, 2, 4, 5, 9], [1, 2, 4, 6, 8], [1, 2, 5, 7, 10],
        [1, 2, 6, 9, 10], [1, 2, 7, 8, 9], [1, 3, 4, 5, 6], [1, 3, 4, 7, 9],
        [1, 3, 5, 9, 10], [1, 3, 6, 8, 9], [1, 3, 7, 8, 10], [1, 4, 5, 7, 8],
        [1, 4, 6, 7, 10], [1, 4, 8, 9, 10], [1, 5, 6, 7, 9], [1, 5, 6, 8, 10],
        [2, 3, 4, 6, 9], [2, 3, 4, 7, 8], [2, 3, 5, 6, 10], [2, 3, 5, 7, 9],
        [2, 3, 8, 9, 10], [2, 4, 5, 6, 7], [2, 4, 5, 8, 10], [2, 4, 7, 9, 10],
        [2, 5, 6, 8, 9], [2, 6, 7, 8, 10], [3, 4, 5, 7, 10], [3, 4, 5, 8, 9],
        [3, 4, 6, 8, 10], [3, 5, 6, 7, 8], [3, 6, 7, 9, 10], [4, 5, 6, 9, 10],
        [4, 6, 7, 8, 9], [5, 7, 8, 9, 10],
    ];

    fn witt_masks() -> Vec<u32> {
        WITT.iter().map(|b| b.iter().fold(0u32, |a, &x| a | (1 << x))).collect()
    }

    #[test]
    fn accepts_the_witt_design() {
        let msg = verify(11, &witt_masks()).expect("Witt must verify");
        assert!(msg.contains("valid S(4,5,11)"), "{msg}");
    }

    #[test]
    fn rejects_a_perturbed_design() {
        let mut b = witt_masks();
        // swap a point in one block: still 5 points, still distinct blocks,
        // but the covering breaks
        b[0] = (b[0] & !(1 << 9)) | (1 << 10);
        assert!(verify(11, &b).is_err(), "a perturbed design must be rejected");
    }

    #[test]
    fn rejects_wrong_block_count() {
        let mut b = witt_masks();
        b.pop();
        assert!(verify(11, &b).is_err());
    }

    #[test]
    fn rejects_duplicates() {
        let mut b = witt_masks();
        b[1] = b[0];
        assert!(verify(11, &b).is_err());
    }
}
