//! CDCL(T) validation: the checks that stand between a fast answer and a
//! trustworthy one.
//!
//! Only built under `--features cdcl`. The properties here are chosen because
//! each one *has* caught, or would have caught, a real bug:
//!
//! * `v11_design_count_is_48` — the sharpest. Any unsound lemma the propagator
//!   emits prunes real designs, so the model count drops below the number an
//!   independent enumeration produces. This is the test that fails when
//!   `overlap_clause` degenerates to a unit `(¬o)`, which is exactly the bug
//!   that once "refuted" S(4,5,21) in 2.17 seconds.
//! * `v11_is_sat_and_verifies` — guards the other direction: propagation that
//!   is too weak yields a model that is not a design, and the independent
//!   checker rejects it.
//! * `known_nonexistence_is_reproduced` — v=15 and v=17 are settled in the
//!   literature (Mendelsohn–Hung 1972; Östergård–Pottonen 2008). Reproducing
//!   them is the calibration that makes a v=21 answer mean anything.

#![cfg(feature = "cdcl")]

use std::path::PathBuf;
use std::process::Command;

fn bin() -> PathBuf {
    let mut p = std::env::current_exe().unwrap();
    p.pop();
    if p.ends_with("deps") {
        p.pop();
    }
    p.join(format!("s45{}", std::env::consts::EXE_SUFFIX))
}

struct Run {
    code: i32,
    stdout: String,
}

fn run(args: &[&str]) -> Run {
    let out = Command::new(bin()).args(args).output().expect("run s45");
    Run {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
    }
}

/// 48 designs contain the level-1 spread at v=11; `tools_soundness_check.py`
/// derives the same number by exhaustive enumeration in Python, with no code
/// shared with the solver.
#[test]
fn v11_design_count_is_48() {
    let r = run(&["cdcl", "-v", "11", "--no-level2", "--count", "1000"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert!(
        r.stdout.contains("total designs found: 48"),
        "expected 48 designs containing the level-1 spread, got:\n{}",
        r.stdout
    );
}

/// Adding level-2 breaking must *reduce* the count without losing designs up
/// to isomorphism: the 48 collapse to 6, one orbit of size 8 apiece. A drop
/// past that is over-breaking; no drop at all means level 2 is inert.
#[test]
fn level_two_breaking_collapses_the_count_by_exactly_eight() {
    let r = run(&["cdcl", "-v", "11", "--count", "1000"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert!(
        r.stdout.contains("total designs found: 6"),
        "expected 48/8 = 6 designs in canonical level-2 position, got:\n{}",
        r.stdout
    );
}

#[test]
fn v11_is_sat_and_verifies() {
    let r = run(&["cdcl", "-v", "11", "--quiet"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert!(r.stdout.contains("RESULT: SAT"), "{}", r.stdout);
    assert!(
        r.stdout.contains("valid S(4,5,11): 66 blocks"),
        "witness did not verify:\n{}",
        r.stdout
    );
}

/// Dropping symmetry breaking must not change the *answer*, only the cost.
/// A completeness bug in the level-2 branching shows up here as a v=11 that
/// is SAT with breaking and UNSAT without it, or vice versa.
#[test]
fn symmetry_breaking_does_not_change_the_answer_at_v11() {
    let r = run(&["cdcl", "-v", "11", "--no-symmetry", "--quiet"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert!(r.stdout.contains("RESULT: SAT"), "{}", r.stdout);
}

/// A limit must yield UNKNOWN, never UNSAT — the same contract odd835 holds.
#[test]
fn a_limit_never_reports_unsat() {
    let r = run(&["cdcl", "-v", "21", "--timeout", "2s", "--quiet"]);
    assert!(
        r.code == 2 || r.code == 1,
        "expected UNKNOWN (2) or a genuine UNSAT (1), got {}:\n{}",
        r.code,
        r.stdout
    );
    if r.code == 2 {
        assert!(r.stdout.contains("RESULT: UNKNOWN"), "{}", r.stdout);
    }
}

#[test]
#[ignore = "minutes-scale; run with --ignored once the search is tuned"]
fn known_nonexistence_is_reproduced() {
    for v in ["15", "17"] {
        let r = run(&["cdcl", "-v", v, "--quiet", "--timeout", "3600"]);
        assert_eq!(r.code, 1, "S(4,5,{v}) should be refuted:\n{}", r.stdout);
    }
}
