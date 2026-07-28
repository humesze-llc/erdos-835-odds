//! Integration tests: spec section 7 structural oracles plus everything
//! through `k = 6` end to end (spec section 11, deliverable 2).
//!
//! These drive the built binary rather than library internals, so they cover
//! argument parsing, exit codes, the witness format and the independent
//! checker in the same way an operator would.
//!
//! Rungs that do not terminate with the current engine (`k >= 8` partition,
//! `k >= 8` single code) are covered by `no_false_unsat_under_a_limit`, which
//! asserts the property that actually matters: a limit must yield UNKNOWN,
//! never UNSAT.

use std::path::PathBuf;
use std::process::Command;

fn bin() -> PathBuf {
    let mut p = std::env::current_exe().unwrap();
    p.pop();
    if p.ends_with("deps") {
        p.pop();
    }
    p.join(format!("odd835{}", std::env::consts::EXE_SUFFIX))
}

fn tmp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join("odd835-it");
    std::fs::create_dir_all(&d).unwrap();
    d.join(name)
}

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

static WITNESS_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn run(args: &[&str]) -> Run {
    // On SAT the solver writes a witness, and without --witness-out it picks a
    // CWD-relative default that depends only on k. Tests run in parallel, so
    // several k=2 solves would race on the same file and read each other's
    // half-written output. Give every invocation its own path.
    let mut owned: Vec<String> = args.iter().map(|s| s.to_string()).collect();
    let searching = matches!(args.first().copied(), Some("solve") | Some("code"));
    if searching && !args.iter().any(|a| *a == "--witness-out") {
        let n = WITNESS_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let p = tmp(&format!("auto-{}-{n}.wit", std::process::id()));
        owned.push("--witness-out".into());
        owned.push(p.to_string_lossy().into_owned());
    }
    let out = Command::new(bin())
        .args(&owned)
        .output()
        .unwrap_or_else(|e| panic!("running {:?}: {e}", bin()));
    Run {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// The tuned configuration; see RESULTS.md.
const BEST: [&str; 4] = ["--symmetry", "orbit", "--propagator", "matching"];

// ---------------------------------------------------------------------------
// Exit-code contract (spec section 4)
// ---------------------------------------------------------------------------

#[test]
fn odd_k_is_rejected_with_an_explanation() {
    for k in ["3", "7", "15"] {
        let r = run(&["solve", "-k", k]);
        assert_eq!(r.code, 3, "odd k must be an input error");
        assert!(
            r.stderr.contains("odd") && r.stderr.contains("negative"),
            "message for k={k} must explain the structure-theorem reason, got: {}",
            r.stderr
        );
    }
}

#[test]
fn out_of_range_k_is_rejected() {
    for k in ["0", "18", "100"] {
        assert_eq!(run(&["solve", "-k", k]).code, 3, "k={k}");
    }
}

#[test]
fn info_matches_the_spec_constants_table() {
    let cases = [
        (2u32, "|V| = C(3,1) = 3", "perfect code size m  1"),
        (4, "|V| = C(7,3) = 35", "perfect code size m  7"),
        (6, "|V| = C(11,5) = 462", "perfect code size m  66"),
        (8, "|V| = C(15,7) = 6,435", "perfect code size m  715"),
        (10, "|V| = C(19,9) = 92,378", "perfect code size m  8,398"),
        (12, "|V| = C(23,11) = 1,352,078", "perfect code size m  104,006"),
        (14, "|V| = C(27,13) = 20,058,300", "perfect code size m  1,337,220"),
        (16, "|V| = C(31,15) = 300,540,195", "perfect code size m  17,678,835"),
    ];
    for (k, v, m) in cases {
        let r = run(&["info", "-k", &k.to_string()]);
        assert_eq!(r.code, 0, "info k={k}");
        assert!(r.stdout.contains(v), "k={k}: missing `{v}`\n{}", r.stdout);
        assert!(r.stdout.contains(m), "k={k}: missing `{m}`\n{}", r.stdout);
        assert!(
            r.stdout.contains(&format!("colours              {}", k + 1)),
            "k={k}: colour count must be k+1"
        );
    }
}

#[test]
fn info_reports_the_divisibility_obstruction_at_k8_and_k14_only() {
    for k in [8u32, 14] {
        let r = run(&["info", "-k", &k.to_string()]);
        assert!(
            r.stdout.contains("DIVISIBILITY OBSTRUCTION"),
            "k={k} must report the obstruction"
        );
    }
    for k in [2u32, 4, 6, 10, 12, 16] {
        let r = run(&["info", "-k", &k.to_string()]);
        assert!(
            !r.stdout.contains("DIVISIBILITY OBSTRUCTION"),
            "k={k} must not report an obstruction"
        );
    }
}

// ---------------------------------------------------------------------------
// Structural oracles
// ---------------------------------------------------------------------------

#[test]
fn structural_oracles_pass() {
    for name in [
        "rank-roundtrip",
        "degree",
        "symmetry",
        "fano",
        "witt",
        "dist-sums",
        "dist-endpoints",
        "dist-tables",
        "dist-groundtruth",
        "skip-cases",
    ] {
        let r = run(&["oracle", "--only", name]);
        assert_eq!(r.code, 0, "oracle {name} failed:\n{}", r.stdout);
        assert!(r.stdout.contains("all agree"), "oracle {name}:\n{}", r.stdout);
    }
}

// ---------------------------------------------------------------------------
// End-to-end search, both polarities
// ---------------------------------------------------------------------------

#[test]
fn partition_k2_is_sat_and_the_witness_verifies() {
    let w = tmp("p2.wit");
    let mut a = vec!["solve", "-k", "2", "--witness-out", w.to_str().unwrap()];
    a.extend_from_slice(&BEST);
    let r = run(&a);
    assert_eq!(r.code, 0, "k=2 must be SAT:\n{}\n{}", r.stdout, r.stderr);
    assert!(r.stdout.contains("RESULT: SAT"));
    let c = run(&["check", "-k", "2", "--witness", w.to_str().unwrap()]);
    assert_eq!(c.code, 0, "witness must verify:\n{}", c.stdout);
    assert!(c.stdout.contains("WITNESS VALID"));
}

#[test]
fn partition_k4_and_k6_are_unsat() {
    for k in ["4", "6"] {
        let mut a = vec!["solve", "-k", k];
        a.extend_from_slice(&BEST);
        let r = run(&a);
        assert_eq!(r.code, 1, "k={k} must be UNSAT:\n{}\n{}", r.stdout, r.stderr);
        assert!(r.stdout.contains("RESULT: UNSAT"));
    }
}

#[test]
fn code_k4_finds_a_fano_equivalent_and_k6_a_witt_equivalent() {
    for (k, m) in [("4", 7usize), ("6", 66)] {
        let w = tmp(&format!("c{k}.wit"));
        let r = run(&["code", "-k", k, "--witness-out", w.to_str().unwrap()]);
        assert_eq!(r.code, 0, "code k={k} must be SAT:\n{}\n{}", r.stdout, r.stderr);
        let c = run(&["check", "-k", k, "--witness", w.to_str().unwrap()]);
        assert_eq!(c.code, 0, "code witness k={k}:\n{}", c.stdout);
        assert!(c.stdout.contains("WITNESS VALID"));
        let body = std::fs::read_to_string(&w).unwrap();
        let members = body.lines().skip_while(|l| *l != "data").skip(1).count();
        assert_eq!(members, m, "code k={k} must have m = {m} members");
    }
}

// ---------------------------------------------------------------------------
// The property that must never break
// ---------------------------------------------------------------------------

/// A limit must produce UNKNOWN (exit 2). Printing UNSAT because a budget ran
/// out is the one failure this project cannot survive (spec section 4).
#[test]
fn no_false_unsat_under_a_limit() {
    for k in ["6", "8", "10"] {
        let mut a = vec!["solve", "-k", k, "--max-conflicts", "50"];
        a.extend_from_slice(&BEST);
        let r = run(&a);
        assert_eq!(
            r.code, 2,
            "k={k} under a 50-conflict limit must be UNKNOWN, got:\n{}",
            r.stdout
        );
        assert!(r.stdout.contains("RESULT: UNKNOWN"));
        assert!(!r.stdout.contains("RESULT: UNSAT"));
    }
    for k in ["8", "10"] {
        let r = run(&["code", "-k", k, "--timeout", "1s"]);
        assert_eq!(r.code, 2, "code k={k} under a 1s timeout must be UNKNOWN");
    }
}

/// Build the tuned configuration with `overrides` replacing a flag rather than
/// repeating it — clap rejects a repeated argument outright.
fn tuned(symmetry: &str, propagator: &str, extra: &[&str]) -> Vec<String> {
    let mut a: Vec<String> = ["--symmetry", symmetry, "--propagator", propagator]
        .iter()
        .map(|s| s.to_string())
        .collect();
    a.extend(extra.iter().map(|s| s.to_string()));
    a
}

/// Toggling a structural rule may change the time and the conflict count but
/// never the answer (spec milestone M4.5).
#[test]
fn rule_toggles_preserve_answers() {
    let variants: Vec<(&str, Vec<String>)> = vec![
        ("baseline", tuned("orbit", "matching", &[])),
        ("no-cardinality", tuned("orbit", "matching", &["--no-cardinality"])),
        ("anchors=0", tuned("orbit", "matching", &["--anchors", "0"])),
        ("anchors=4", tuned("orbit", "matching", &["--anchors", "4"])),
        ("anchors=64", tuned("orbit", "matching", &["--anchors", "64"])),
        ("anchor-reach", tuned("orbit", "matching", &["--anchor-reach"])),
        ("verify-classes", tuned("orbit", "matching", &["--verify-classes"])),
        ("link t=2", tuned("orbit", "matching", &["--branch-order", "link", "--link-level", "2"])),
        ("link t=3", tuned("orbit", "matching", &["--branch-order", "link", "--link-level", "3"])),
        ("propagator=count", tuned("orbit", "count", &[])),
        ("symmetry=color", tuned("color", "matching", &[])),
        ("symmetry=none", tuned("none", "matching", &[])),
        ("cli defaults", vec![]),
    ];
    for (k, expect) in [("2", 0), ("4", 1)] {
        for (name, v) in &variants {
            let mut a: Vec<String> = vec!["solve".into(), "-k".into(), k.to_string()];
            a.extend(v.iter().cloned());
            let refs: Vec<&str> = a.iter().map(String::as_str).collect();
            let r = run(&refs);
            assert_eq!(
                r.code, expect,
                "k={k} variant `{name}` changed the answer:\n{}\n{}",
                r.stdout, r.stderr
            );
        }
    }
}

/// The orbit reduction is a complete symmetry reduction, so it must agree with
/// plain colour breaking wherever both terminate. `k = 2` is the load-bearing
/// case: it is the only SAT partition instance available, so a reduction that
/// lost solutions would show up there.
#[test]
fn orbit_reduction_agrees_with_colour_breaking() {
    for (k, expect) in [("2", 0), ("4", 1)] {
        let a = run(&[
            "solve", "-k", k, "--symmetry", "color", "--propagator", "matching",
        ]);
        let b = run(&[
            "solve", "-k", k, "--symmetry", "orbit", "--propagator", "matching",
        ]);
        assert_eq!(a.code, expect, "k={k} colour:\n{}", a.stdout);
        assert_eq!(b.code, expect, "k={k} orbit:\n{}", b.stdout);
    }
}

/// The same comparison at `k = 6`, which is the strongest available evidence
/// that the orbit reduction preserves answers on a non-trivial instance.
/// Ignored by default because the colour-breaking arm takes tens of minutes —
/// that gap is the whole point of the reduction. Run with
/// `cargo test --release --test oracles -- --ignored`.
#[test]
#[ignore]
fn orbit_reduction_agrees_with_colour_breaking_k6() {
    let a = run(&[
        "solve", "-k", "6", "--symmetry", "color", "--propagator", "matching",
    ]);
    let b = run(&[
        "solve", "-k", "6", "--symmetry", "orbit", "--propagator", "matching",
    ]);
    assert_eq!(a.code, 1, "k=6 colour must be UNSAT:\n{}", a.stdout);
    assert_eq!(b.code, 1, "k=6 orbit must be UNSAT:\n{}", b.stdout);
}

// ---------------------------------------------------------------------------
// Witness handling and the checker
// ---------------------------------------------------------------------------

#[test]
fn checker_rejects_a_corrupted_witness() {
    let good = tmp("g2.wit");
    let mut a = vec!["solve", "-k", "2", "--witness-out", good.to_str().unwrap()];
    a.extend_from_slice(&BEST);
    assert_eq!(run(&a).code, 0);

    let body = std::fs::read_to_string(&good).unwrap();
    let mut lines: Vec<String> = body.lines().map(str::to_string).collect();
    let di = lines.iter().position(|l| l == "data").unwrap();
    // recolour every vertex 0: class sizes and rainbow both break
    let n = lines[di + 1].len();
    lines[di + 1] = "0".repeat(n);
    let bad = tmp("b2.wit");
    std::fs::write(&bad, lines.join("\n") + "\n").unwrap();

    let c = run(&["check", "-k", "2", "--witness", bad.to_str().unwrap()]);
    assert_eq!(c.code, 1, "a corrupted witness must be rejected:\n{}", c.stdout);
    assert!(c.stdout.contains("WITNESS INVALID"));
}

#[test]
fn checker_rejects_a_witness_for_the_wrong_k() {
    let w = tmp("g2b.wit");
    let mut a = vec!["solve", "-k", "2", "--witness-out", w.to_str().unwrap()];
    a.extend_from_slice(&BEST);
    assert_eq!(run(&a).code, 0);
    let c = run(&["check", "-k", "4", "--witness", w.to_str().unwrap()]);
    assert_eq!(c.code, 3, "k mismatch is an input error");
}

// ---------------------------------------------------------------------------
// Observability and endurance
// ---------------------------------------------------------------------------

#[test]
fn jsonl_telemetry_is_complete_and_parseable() {
    let f = tmp("stats.jsonl");
    let _ = std::fs::remove_file(&f);
    let mut a = vec![
        "solve", "-k", "6",
        "--timeout", "3s",
        "--stats-interval", "200ms",
        "--stats-format", "jsonl",
        "--stats-file", f.to_str().unwrap(),
    ];
    a.extend_from_slice(&BEST);
    let r = run(&a);
    assert_eq!(r.code, 2, "3s is not enough for k=6, expect UNKNOWN");

    let body = std::fs::read_to_string(&f).unwrap();
    let lines: Vec<&str> = body.lines().filter(|l| !l.is_empty()).collect();
    assert!(lines.len() >= 3, "expected several telemetry records, got {}", lines.len());

    // every field spec section 8 asks for must be present in every record
    let required = [
        "schema_version", "run_id", "k", "wall_ms",
        "assigned", "assigned_high_water", "saturated", "classes_closed",
        "decisions", "propagations", "conflicts", "backtracks", "restarts",
        "depth_current", "depth_max",
        "conflicts_per_sec", "propagations_per_sec", "decisions_per_sec",
        "dom_total", "dom_mean", "dom_singletons",
        "conflicts_by_rule", "forced_by_rule", "rungs",
        "stall_ms", "rss_bytes", "elapsed_ms", "cpu_ms",
        "checkpoint_last_ms", "checkpoint_next_ms",
    ];
    for l in &lines {
        let v: serde_json::Value = serde_json::from_str(l).expect("each line must be JSON");
        for key in required {
            assert!(v.get(key).is_some(), "record is missing `{key}`:\n{l}");
        }
        for rule in ["a", "b", "c", "d", "e", "matching"] {
            assert!(
                v["conflicts_by_rule"].get(rule).is_some(),
                "conflicts_by_rule is missing `{rule}`"
            );
        }
    }
    let last: serde_json::Value = serde_json::from_str(lines.last().unwrap()).unwrap();
    assert_eq!(last["outcome"], "UNKNOWN");
    assert_eq!(last["final"], true);
}

#[test]
fn checkpoint_resume_reproduces_the_run_exactly() {
    let mut a = vec!["solve", "-k", "6", "--stats-format", "json", "--stats-interval", "999999s"];
    a.extend_from_slice(&BEST);
    let base = run(&a);
    assert_eq!(base.code, 1);
    let baseline: serde_json::Value = serde_json::from_str(
        base.stdout.lines().filter(|l| l.starts_with('{')).next_back().unwrap(),
    )
    .unwrap();

    for limit in ["20000", "90000"] {
        let cp = tmp(&format!("r{limit}.ckpt"));
        let _ = std::fs::remove_file(&cp);
        let mut a = vec![
            "solve", "-k", "6", "--max-conflicts", limit,
            "--checkpoint", cp.to_str().unwrap(),
            "--stats-format", "json", "--stats-interval", "999999s",
        ];
        a.extend_from_slice(&BEST);
        assert_eq!(run(&a).code, 2, "the limited run must stop as UNKNOWN");
        assert!(cp.exists(), "a checkpoint must have been written");

        let mut a = vec![
            "solve", "-k", "6", "--resume", cp.to_str().unwrap(),
            "--stats-format", "json", "--stats-interval", "999999s",
        ];
        a.extend_from_slice(&BEST);
        let res = run(&a);
        assert_eq!(res.code, 1, "resume must reach UNSAT:\n{}\n{}", res.stdout, res.stderr);
        let v: serde_json::Value = serde_json::from_str(
            res.stdout.lines().filter(|l| l.starts_with('{')).next_back().unwrap(),
        )
        .unwrap();
        assert_eq!(
            v["conflicts"], baseline["conflicts"],
            "resume from {limit} must reproduce the conflict count exactly"
        );
        assert_eq!(v["decisions"], baseline["decisions"]);
    }
}

#[test]
fn a_resume_with_a_different_configuration_is_refused() {
    let cp = tmp("mismatch.ckpt");
    let _ = std::fs::remove_file(&cp);
    let mut a = vec![
        "solve", "-k", "6", "--max-conflicts", "5000",
        "--checkpoint", cp.to_str().unwrap(),
        "--stats-format", "json", "--stats-interval", "999999s",
    ];
    a.extend_from_slice(&BEST);
    assert_eq!(run(&a).code, 2);
    // resume with a different propagator
    let r = run(&[
        "solve", "-k", "6", "--symmetry", "orbit", "--propagator", "count",
        "--resume", cp.to_str().unwrap(),
    ]);
    assert_eq!(r.code, 3, "a configuration mismatch must be an error");
    assert!(r.stderr.contains("different configuration"));
}

#[test]
fn conflict_log_is_replayable_jsonl() {
    let f = tmp("conflicts.jsonl");
    let _ = std::fs::remove_file(&f);
    let mut a = vec![
        "solve", "-k", "4", "--conflict-log", f.to_str().unwrap(),
        "--stats-format", "json", "--stats-interval", "999999s",
    ];
    a.extend_from_slice(&BEST);
    assert_eq!(run(&a).code, 1);
    let body = std::fs::read_to_string(&f).unwrap();
    let mut decisions = 0;
    let mut conflicts = 0;
    for l in body.lines().filter(|l| !l.is_empty()) {
        let v: serde_json::Value = serde_json::from_str(l).expect("conflict log must be JSONL");
        match v["e"].as_str().unwrap() {
            "d" => {
                assert!(v["v"].is_number() && v["c"].is_number() && v["lvl"].is_number());
                decisions += 1;
            }
            "x" => {
                assert!(v["rule"].is_string() && v["lvl"].is_number());
                conflicts += 1;
            }
            other => panic!("unexpected event `{other}`"),
        }
    }
    assert!(decisions > 0 && conflicts > 0, "log must record both events");
}

#[test]
fn determinism_byte_for_byte() {
    let mut a = vec!["solve", "-k", "6", "--stats-format", "json", "--stats-interval", "999999s"];
    a.extend_from_slice(&BEST);
    let mut sigs = Vec::new();
    for _ in 0..2 {
        let r = run(&a);
        let v: serde_json::Value = serde_json::from_str(
            r.stdout.lines().filter(|l| l.starts_with('{')).next_back().unwrap(),
        )
        .unwrap();
        sigs.push(format!(
            "{}|{}|{}|{}|{}",
            v["conflicts"], v["decisions"], v["propagations"], v["backtracks"], v["depth_max"]
        ));
    }
    assert_eq!(sigs[0], sigs[1], "identical inputs must give an identical trace");
}

#[test]
fn bench_runs() {
    let r = run(&["bench", "-k", "8", "--seconds", "1"]);
    assert_eq!(r.code, 0, "{}", r.stderr);
    assert!(r.stdout.contains("Rule B"));
    assert!(r.stdout.contains("neighbour enumeration"));
}
