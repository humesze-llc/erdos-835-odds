//! The acceptance gate (spec section 7). Every entry has a known answer; the
//! suite exits non-zero if any entry disagrees.

use crate::check::{intersection_profile, is_perfect_code, neighbors_from_definition, subsets_of_size};
use crate::codesearch::CodeSolver;
use crate::combi::Combi;
use crate::designs::{FANO, WITT_S4_5_11};
use crate::interrupt::Interrupt;
use crate::solver::search::Solver;
use crate::solver::{Config, Outcome};
use crate::util::{commas, fmt_hms};
use anyhow::Result;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Expect {
    Sat,
    Unsat,
    /// Informational rung: any outcome is acceptable, the number is the point.
    Informational,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Structural,
    Code,
    Partition,
}

struct Entry {
    name: &'static str,
    kind: Kind,
    k: u32,
    expect: Expect,
    /// Rough expected cost; entries above the budget are skipped under --quick.
    heavy: bool,
    note: &'static str,
}

const ENTRIES: &[Entry] = &[
    // structural
    Entry { name: "rank-roundtrip", kind: Kind::Structural, k: 12, expect: Expect::Sat, heavy: false, note: "unrank(rank(S)) == S for all vertices, k <= 12" },
    Entry { name: "degree",         kind: Kind::Structural, k: 12, expect: Expect::Sat, heavy: false, note: "every vertex has exactly k neighbours, k <= 12" },
    Entry { name: "symmetry",       kind: Kind::Structural, k: 10, expect: Expect::Sat, heavy: false, note: "u in N(v) <=> v in N(u), k <= 10" },
    Entry { name: "fano",           kind: Kind::Structural, k: 4,  expect: Expect::Sat, heavy: false, note: "the 7 Fano lines are a perfect 1-code in O_4" },
    Entry { name: "witt",           kind: Kind::Structural, k: 6,  expect: Expect::Sat, heavy: false, note: "the 66 blocks of S(4,5,11) are a perfect 1-code in O_6" },
    Entry { name: "dist-sums",      kind: Kind::Structural, k: 16, expect: Expect::Sat, heavy: false, note: "sum N_j == sum M_j == Cat(k), all even k <= 16" },
    Entry { name: "dist-endpoints", kind: Kind::Structural, k: 16, expect: Expect::Sat, heavy: false, note: "N_0=N_k=1, N_1=N_{k-1}=0, M_0=M_k=0, M_1=k" },
    Entry { name: "dist-tables",    kind: Kind::Structural, k: 16, expect: Expect::Sat, heavy: false, note: "generated tables match the spec tables at k=10 and k=16" },
    Entry { name: "dist-groundtruth", kind: Kind::Structural, k: 6, expect: Expect::Sat, heavy: false, note: "Fano and Witt brute-force profiles match the N_j formula" },
    Entry { name: "skip-cases",     kind: Kind::Structural, k: 8,  expect: Expect::Sat, heavy: false, note: "a in {0, k-2} is implied by Rule B, k <= 8" },
    Entry { name: "rules-agree",    kind: Kind::Structural, k: 6,  expect: Expect::Sat, heavy: true,  note: "M4.5 gate: every rule toggle preserves the answer" },
    // single perfect codes
    Entry { name: "code-k4",  kind: Kind::Code, k: 4,  expect: Expect::Sat,   heavy: false, note: "the Fano plane" },
    Entry { name: "code-k6",  kind: Kind::Code, k: 6,  expect: Expect::Sat,   heavy: false, note: "the Witt design S(4,5,11)" },
    Entry { name: "code-k8",  kind: Kind::Code, k: 8,  expect: Expect::Unsat, heavy: true,  note: "requires S(6,7,15), which fails divisibility" },
    Entry { name: "code-k10", kind: Kind::Code, k: 10, expect: Expect::Unsat, heavy: true,  note: "requires S(8,9,19), whose derived S(4,5,15) does not exist" },
    // partitions
    Entry { name: "part-k2",  kind: Kind::Partition, k: 2,  expect: Expect::Sat,   heavy: false, note: "positive control, must be instant" },
    Entry { name: "part-k4",  kind: Kind::Partition, k: 4,  expect: Expect::Unsat, heavy: false, note: "no LS(3,4,8)" },
    Entry { name: "part-k6",  kind: Kind::Partition, k: 6,  expect: Expect::Unsat, heavy: true,  note: "no LS(5,6,12)" },
    Entry { name: "part-k8",  kind: Kind::Partition, k: 8,  expect: Expect::Unsat, heavy: true,  note: "no perfect code at all" },
    Entry { name: "part-k10", kind: Kind::Partition, k: 10, expect: Expect::Unsat, heavy: true,  note: "no perfect code at all" },
    Entry { name: "part-k12", kind: Kind::Partition, k: 12, expect: Expect::Unsat, heavy: true,  note: "THE GATE - report wall time prominently" },
    Entry { name: "part-k14", kind: Kind::Partition, k: 14, expect: Expect::Informational, heavy: true, note: "UNSAT for an arithmetic reason the search cannot see; a timeout here is not a defect" },
    Entry { name: "part-k16", kind: Kind::Partition, k: 16, expect: Expect::Informational, heavy: true, note: "the actual target; outcome unknown" },
];

pub fn run(only: Option<&str>, budget: Duration, quick: bool) -> Result<bool> {
    println!(
        "odd835 oracle   budget {}/entry{}\n",
        fmt_hms(budget),
        if quick { "   (--quick: heavy entries skipped)" } else { "" }
    );
    println!(
        "{:<18} {:<6} {:>12} {:>10} {:>14} {:>12}  {}",
        "entry", "k", "expected", "got", "wall", "conflicts", "note"
    );
    println!("{}", "-".repeat(120));

    let mut all_ok = true;
    let mut ran = 0usize;
    for e in ENTRIES {
        if let Some(f) = only {
            if !e.name.contains(f) {
                continue;
            }
        } else if e.expect == Expect::Informational {
            // never part of the default gate; ask for them by name
            continue;
        }
        if quick && e.heavy && only.is_none() {
            println!(
                "{:<18} {:<6} {:>12} {:>10} {:>14} {:>12}  {}",
                e.name, e.k, label(e.expect), "skipped", "-", "-", e.note
            );
            continue;
        }
        ran += 1;
        let t0 = Instant::now();
        let (got, conflicts, detail) = match e.kind {
            Kind::Structural => run_structural(e.name)?,
            Kind::Code => run_code(e.k, budget)?,
            Kind::Partition => run_partition(e.k, budget)?,
        };
        let wall = t0.elapsed();
        let pass = match e.expect {
            Expect::Informational => true,
            Expect::Sat => got == "SAT",
            Expect::Unsat => got == "UNSAT",
        };
        all_ok &= pass;
        println!(
            "{:<18} {:<6} {:>12} {:>10} {:>14} {:>12}  {}{}",
            e.name,
            e.k,
            label(e.expect),
            got,
            format!("{:.3}s", wall.as_secs_f64()),
            commas(conflicts),
            if pass { "" } else { "*** DISAGREES *** " },
            if detail.is_empty() { e.note.to_string() } else { detail }
        );
    }
    println!("{}", "-".repeat(120));
    println!(
        "{} entr{} run, {}",
        ran,
        if ran == 1 { "y" } else { "ies" },
        if all_ok { "all agree" } else { "DISAGREEMENTS PRESENT" }
    );
    Ok(all_ok)
}

fn label(e: Expect) -> &'static str {
    match e {
        Expect::Sat => "SAT",
        Expect::Unsat => "UNSAT",
        Expect::Informational => "(info)",
    }
}

/// The oracle runs the *measured-best* configuration, not the CLI defaults:
/// `--symmetry orbit --propagator matching`. RESULTS.md records the ablation
/// that justifies it. Both settings are provably answer-preserving, and the
/// `rules-agree` entry below checks that empirically.
fn oracle_cfg(k: u32, budget: Duration) -> Config {
    let mut c = Config::new(k);
    c.timeout = Some(budget);
    c.quiet = true;
    c.symmetry = crate::solver::SymmetryMode::Orbit;
    c.propagator = crate::solver::PropagatorMode::Matching;
    c.witness_out = Some(std::env::temp_dir().join(format!("odd835-oracle-k{k}.wit")));
    c
}

fn run_partition(k: u32, budget: Duration) -> Result<(String, u64, String)> {
    let cfg = oracle_cfg(k, budget);
    let mut s = Solver::new(cfg, Interrupt::new())?;
    let out = s.run()?;
    let conflicts = s.e.stats.conflicts;
    let detail = match &out {
        Outcome::Unknown(why) => why.clone(),
        _ => String::new(),
    };
    Ok((out.label().to_string(), conflicts, detail))
}

fn run_code(k: u32, budget: Duration) -> Result<(String, u64, String)> {
    let cfg = oracle_cfg(k, budget);
    let mut s = CodeSolver::new(cfg, Interrupt::new())?;
    let out = s.run()?;
    let conflicts = s.stats.conflicts;
    let detail = match &out {
        Outcome::Unknown(why) => why.clone(),
        _ => String::new(),
    };
    Ok((out.label().to_string(), conflicts, detail))
}

// ---------------------------------------------------------------------------
// Structural oracles
// ---------------------------------------------------------------------------

fn run_structural(name: &str) -> Result<(String, u64, String)> {
    let r = match name {
        "rank-roundtrip" => o_rank_roundtrip(),
        "degree" => o_degree(),
        "symmetry" => o_symmetry(),
        "fano" => o_fano(),
        "witt" => o_witt(),
        "dist-sums" => o_dist_sums(),
        "dist-endpoints" => o_dist_endpoints(),
        "dist-tables" => o_dist_tables(),
        "dist-groundtruth" => o_dist_groundtruth(),
        "skip-cases" => o_skip_cases(),
        "rules-agree" => o_rules_agree(),
        other => Err(format!("unknown structural oracle `{other}`")),
    };
    Ok(match r {
        Ok(msg) => ("SAT".to_string(), 0, msg),
        Err(msg) => ("FAIL".to_string(), 0, msg),
    })
}

type OResult = std::result::Result<String, String>;

fn o_rank_roundtrip() -> OResult {
    for k in [2u32, 4, 6, 8, 10, 12] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        for i in 0..c.num_vertices as u32 {
            let m = c.unrank(i);
            if m.count_ones() != c.r {
                return Err(format!("k={k}: unrank({i}) has popcount {}", m.count_ones()));
            }
            if c.rank(m) != i {
                return Err(format!("k={k}: rank(unrank({i})) = {}", c.rank(m)));
            }
            if c.rank_ref(m) != i {
                return Err(format!("k={k}: rank_ref disagrees at {i}"));
            }
        }
    }
    Ok("k in {2,4,6,8,10,12}, all vertices".into())
}

fn o_degree() -> OResult {
    for k in [2u32, 4, 6, 8, 10, 12] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        for i in 0..c.num_vertices as u32 {
            let m = c.unrank(i);
            let mut n = 0;
            let mut seen = std::collections::HashSet::new();
            for nb in c.neighbors(m) {
                if nb & m != 0 {
                    return Err(format!("k={k}: neighbour {nb:#x} of {m:#x} is not disjoint"));
                }
                if nb.count_ones() != c.r {
                    return Err(format!("k={k}: neighbour has wrong size"));
                }
                seen.insert(nb);
                n += 1;
            }
            if n != k as usize || seen.len() != k as usize {
                return Err(format!("k={k}: vertex {i} has degree {n} ({} distinct)", seen.len()));
            }
        }
    }
    Ok("k in {2,4,6,8,10,12}, all vertices, degree = k".into())
}

fn o_symmetry() -> OResult {
    for k in [2u32, 4, 6, 8, 10] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        for i in 0..c.num_vertices as u32 {
            let m = c.unrank(i);
            for nb in c.neighbors(m) {
                if !c.neighbors(nb).any(|x| x == m) {
                    return Err(format!("k={k}: {m:#x} ~ {nb:#x} but not conversely"));
                }
            }
        }
    }
    Ok("k in {2,4,6,8,10}, adjacency is symmetric".into())
}

fn o_fano() -> OResult {
    match is_perfect_code(4, &FANO) {
        Ok(true) => Ok("7 lines cover all 35 vertices of O_4 exactly once".into()),
        Ok(false) => Err("Fano lines are not a perfect 1-code in O_4".into()),
        Err(e) => Err(e.to_string()),
    }
}

fn o_witt() -> OResult {
    match is_perfect_code(6, &WITT_S4_5_11) {
        Ok(true) => Ok("66 blocks cover all 462 vertices of O_6 exactly once".into()),
        Ok(false) => Err("S(4,5,11) is not a perfect 1-code in O_6".into()),
        Err(e) => Err(e.to_string()),
    }
}

/// `sum_j N_j == sum_j M_j == Cat(k)`. Checked on the exact numerators over
/// `k+1`, because the individual terms are not integers at `k = 8` and `k = 14`
/// while the sums still are.
fn o_dist_sums() -> OResult {
    let mut nonintegral = Vec::new();
    for k in [2u32, 4, 6, 8, 10, 12, 14, 16] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        let cat = c.catalan() as i128;
        let d = k as i128 + 1;
        let sn: i128 = c.n_num().iter().sum();
        let sm: i128 = c.m_num().iter().sum();
        if sn != cat * d || sm != cat * d {
            return Err(format!(
                "k={k}: sum N_j = {sn}/{d}, sum M_j = {sm}/{d}, Cat(k) = {cat}"
            ));
        }
        if !c.distribution_integral() {
            nonintegral.push(k);
        }
    }
    if nonintegral != vec![8u32, 14] {
        return Err(format!(
            "expected the divisibility obstruction at k = 8, 14 only; got {nonintegral:?}"
        ));
    }
    Ok("all even k <= 16; N_j/M_j non-integral exactly at k = 8, 14".into())
}

fn o_dist_endpoints() -> OResult {
    for k in [2u32, 4, 6, 8, 10, 12, 14, 16] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        let n = c.n_dist();
        let m = c.m_dist();
        let ku = k as usize;
        if n[0] != 1 || n[ku] != 1 {
            return Err(format!("k={k}: N_0={} N_k={}", n[0], n[ku]));
        }
        if n[1] != 0 || n[ku - 1] != 0 {
            return Err(format!("k={k}: N_1={} N_(k-1)={}", n[1], n[ku - 1]));
        }
        if m[0] != 0 || m[ku] != 0 {
            return Err(format!("k={k}: M_0={} M_k={}", m[0], m[ku]));
        }
        if m[1] != k as u64 {
            return Err(format!("k={k}: M_1={} expected {k}", m[1]));
        }
    }
    Ok("all even k <= 16".into())
}

fn o_dist_tables() -> OResult {
    let c10 = Combi::new(10).map_err(|e| e.to_string())?;
    let n10 = vec![1u64, 0, 225, 1200, 4200, 5544, 4200, 1200, 225, 0, 1];
    let m10 = vec![0u64, 10, 180, 1320, 3990, 5796, 3990, 1320, 180, 10, 0];
    if c10.n_dist() != n10 {
        return Err(format!("k=10 N_j = {:?}", c10.n_dist()));
    }
    if c10.m_dist() != m10 {
        return Err(format!("k=10 M_j = {:?}", c10.m_dist()));
    }
    let c16 = Combi::new(16).map_err(|e| e.to_string())?;
    let nexp = [0u64, 960, 17920, 196560, 1118208, 3779776, 7687680, 9755460];
    let mexp = [16u64, 840, 18480, 194740, 1122576, 3771768, 7699120, 9742590];
    let d = c16.rule_d_targets();
    let e = c16.rule_e_targets();
    for a in 0..8usize {
        if d[a] != nexp[a] {
            return Err(format!("k=16 N_{} = {} expected {}", a + 1, d[a], nexp[a]));
        }
        if e[a] != mexp[a] {
            return Err(format!("k=16 M_{} = {} expected {}", a + 1, e[a], mexp[a]));
        }
    }
    Ok("k=10 N_j/M_j and k=16 Rule D/E targets match the spec tables".into())
}

fn o_dist_groundtruth() -> OResult {
    for (k, blocks) in [(4u32, &FANO[..]), (6u32, &WITT_S4_5_11[..])] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        let targets = c.rule_d_targets();
        let km1 = (k - 1) as usize;
        for (bi, prof) in intersection_profile(k, blocks).into_iter().enumerate() {
            for a in 0..km1 {
                let mir = km1 - 1 - a;
                if prof[a] + prof[mir] != targets[a] {
                    return Err(format!(
                        "k={k} block {bi}: c_{a} + c_{mir} = {} but N_{} = {}",
                        prof[a] + prof[mir],
                        a + 1,
                        targets[a]
                    ));
                }
            }
        }
    }
    Ok("Fano (k=4) and Witt (k=6) profiles match c_a + c_(k-2-a) = N_(a+1)".into())
}

/// The two intersection sizes Rules D/E deliberately skip. Both are forced by
/// Rule B, which is why checking them at runtime can never fire:
///
///   * `a = 0`     — the two vertices are adjacent, so Rule A already forbids
///                   the same colour, hence `c_0 = 0`.
///   * `a = k-2`   — the two vertices lie in a unique common closed
///                   neighbourhood, so Rule B forbids the same colour, hence
///                   `c_{k-2} = 0`. The same partition of the intersection-
///                   `(k-2)` vertices into the `k` closed neighbourhoods
///                   `N[u]`, `u ∈ N(T)`, gives `d_0 = 1` and `d_{k-2} = k-1`.
fn o_skip_cases() -> OResult {
    for k in [4u32, 6, 8] {
        let c = Combi::new(k).map_err(|e| e.to_string())?;
        let all = subsets_of_size((1u32 << c.n) - 1, c.r);
        for &t in &all {
            let nbrs = neighbors_from_definition(t, c.n, c.r);
            if nbrs.len() != k as usize {
                return Err(format!("k={k}: degree {} != {k}", nbrs.len()));
            }
            // a = 0 -> adjacent
            for &u in &all {
                if u != t && (u & t) == 0 && !nbrs.contains(&u) {
                    return Err(format!("k={k}: |T n U| = 0 but U is not a neighbour"));
                }
            }
            // a = k-2 -> unique common closed neighbourhood, and the blocks
            // N[u] \ {T, u} partition the intersection-(k-2) vertices
            let far: Vec<u32> = all
                .iter()
                .cloned()
                .filter(|u| *u != t && (u & t).count_ones() == k - 2)
                .collect();
            if far.len() != (k * (k - 1)) as usize {
                return Err(format!(
                    "k={k}: |X_(k-2)(T)| = {} expected {}",
                    far.len(),
                    k * (k - 1)
                ));
            }
            let mut seen = std::collections::HashMap::new();
            for &u in &nbrs {
                let mut block = neighbors_from_definition(u, c.n, c.r);
                block.push(u);
                let members: Vec<u32> = block
                    .into_iter()
                    .filter(|x| *x != t && *x != u && (x & t).count_ones() == k - 2)
                    .collect();
                if members.len() != (k - 1) as usize {
                    return Err(format!(
                        "k={k}: N[u] contributes {} intersection-(k-2) vertices, expected {}",
                        members.len(),
                        k - 1
                    ));
                }
                for m in members {
                    if seen.insert(m, u).is_some() {
                        return Err(format!(
                            "k={k}: vertex {m:#x} lies in two of the k blocks; d_(k-2) would exceed k-1"
                        ));
                    }
                }
            }
            if seen.len() != far.len() {
                return Err(format!(
                    "k={k}: blocks cover {} of {} intersection-(k-2) vertices",
                    seen.len(),
                    far.len()
                ));
            }
            // a = k-2 vertices share a common neighbour with T, so Rule B sees them
            for &u in &far {
                let common = nbrs
                    .iter()
                    .filter(|x| {
                        let mut nb = neighbors_from_definition(**x, c.n, c.r);
                        nb.push(**x);
                        nb.contains(&u) && nb.contains(&t)
                    })
                    .count();
                if common != 1 {
                    return Err(format!(
                        "k={k}: T and U at intersection k-2 share {common} common closed neighbourhoods, expected 1"
                    ));
                }
            }
        }
    }
    Ok("c_0 = c_(k-2) = 0 and d_0 = 1, d_(k-2) = k-1 are forced by Rule B, k <= 8".into())
}

/// M4.5 gate: the structural rules are redundancy, not semantics. Toggling any
/// of them must change only the time and the conflict count, never the answer.
/// Run over every rung that terminates for *all* variants within the budget.
fn o_rules_agree() -> OResult {
    use crate::solver::{BranchOrder, PropagatorMode, SymmetryMode};
    let variants: &[(&str, fn(&mut Config))] = &[
        ("baseline", |_c| {}),
        ("no-cardinality", |c| c.cardinality = false),
        ("anchors-0", |c| c.anchors = 0),
        ("anchors-4", |c| c.anchors = 4),
        ("anchors-64", |c| c.anchors = 64),
        ("anchor-reach", |c| c.anchor_reach = true),
        ("matching", |c| c.propagator = PropagatorMode::Matching),
        ("branch-link", |c| c.branch_order = BranchOrder::Link),
        ("symmetry-none", |c| c.symmetry = SymmetryMode::None),
        ("symmetry-orbit", |c| c.symmetry = SymmetryMode::Orbit),
    ];
    let mut report = Vec::new();
    for k in [2u32, 4] {
        let mut answers: Vec<(&str, String)> = Vec::new();
        for (name, tweak) in variants {
            let mut c = Config::new(k);
            c.quiet = true;
            c.timeout = Some(Duration::from_secs(60));
            c.witness_out = Some(std::env::temp_dir().join(format!("odd835-rule-k{k}.wit")));
            tweak(&mut c);
            let mut s = Solver::new(c, Interrupt::new()).map_err(|e| e.to_string())?;
            let o = s.run().map_err(|e| e.to_string())?;
            answers.push((name, o.label().to_string()));
        }
        let base = answers[0].1.clone();
        for (name, got) in &answers {
            if *got != base {
                return Err(format!(
                    "k={k}: baseline says {base} but variant `{name}` says {got}"
                ));
            }
        }
        report.push(format!("k={k}:{base}"));
    }
    // k=6 only terminates for the variants that carry the matching propagator,
    // so compare those against each other rather than against a timeout.
    let mut k6 = Vec::new();
    for (name, sym, prop) in [
        ("orbit+matching", SymmetryMode::Orbit, PropagatorMode::Matching),
        ("color+matching", SymmetryMode::Color, PropagatorMode::Matching),
    ] {
        let mut c = Config::new(6);
        c.quiet = true;
        c.symmetry = sym;
        c.propagator = prop;
        c.timeout = Some(Duration::from_secs(3600));
        c.witness_out = Some(std::env::temp_dir().join("odd835-rule-k6.wit"));
        let mut s = Solver::new(c, Interrupt::new()).map_err(|e| e.to_string())?;
        let o = s.run().map_err(|e| e.to_string())?;
        k6.push((name, o.label().to_string()));
    }
    if k6[0].1 != k6[1].1 {
        return Err(format!(
            "k=6: {} says {} but {} says {}",
            k6[0].0, k6[0].1, k6[1].0, k6[1].1
        ));
    }
    report.push(format!("k=6:{}", k6[0].1));
    Ok(format!(
        "{} variants agree at {}",
        variants.len(),
        report.join(" ")
    ))
}
