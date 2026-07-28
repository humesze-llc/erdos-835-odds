// The default build stays unsafe-free. Under `--features cdcl` the ban relaxes
// to `deny`, and the single `allow` lives in `ipasir`, the FFI boundary.
#![cfg_attr(not(feature = "cdcl"), forbid(unsafe_code))]
#![cfg_attr(feature = "cdcl", deny(unsafe_code))]
//! `s45` — existence search for the Steiner system S(4,5,v).
//!
//! Why this instance: a perfect 1-code in the odd graph `O_16` requires
//! `S(15,16,32)`, and deriving that 11 times gives `S(4,5,21)`. So refuting
//! `S(4,5,21)` kills `k = 16` for Erdős #835 — and stands alone as a named open
//! problem in design theory. `S(4,5,15)` is the calibration rung: admissible,
//! but nonexistent since Mendelsohn–Hung 1972, and plain CDCL on the pairwise
//! CNF does not reproduce that at interactive timescales.
//!
//! Outcomes follow the odd835 contract exactly: SAT 0, UNSAT 1, UNKNOWN 2,
//! ERROR 3. A limit never prints UNSAT.

mod blossom;
#[cfg(feature = "cdcl")]
mod cdcl;
mod engine;
#[cfg(feature = "cdcl")]
mod ipasir;
mod verify;

use engine::{Engine, Why};
use std::process::ExitCode;
use std::time::{Duration, Instant};

const EXIT_ERROR: u8 = 3;

#[derive(PartialEq, Eq, Debug)]
enum Outcome {
    Sat,
    Unsat,
    Unknown(String),
}

struct Opts {
    v: u32,
    matching: bool,
    symmetry: bool,
    timeout: Option<Duration>,
    max_conflicts: Option<u64>,
    quiet: bool,
    filter: bool,
    level2: bool,
}

struct Decision {
    opts: Vec<usize>,
    next: usize,
}

fn search(e: &mut Engine, o: &Opts) -> Outcome {
    let t0 = Instant::now();
    let mut decisions: Vec<Decision> = Vec::new();
    let mut conflict = false;
    let mut tick = 0u64;
    let mut last_report = Instant::now();

    loop {
        tick += 1;
        if tick % 512 == 0 {
            if let Some(t) = o.timeout {
                if t0.elapsed() >= t {
                    return Outcome::Unknown(format!("timeout after {:?}", t));
                }
            }
            if let Some(m) = o.max_conflicts {
                if e.conflicts >= m {
                    return Outcome::Unknown(format!("conflict limit {m}"));
                }
            }
            if !o.quiet && last_report.elapsed() >= Duration::from_secs(5) {
                last_report = Instant::now();
                eprintln!(
                    "  t={:>6.1}s  blocks {:>5}/{:<5} depth {:<5} decisions {:<12} conflicts {:<12} \
                     [cover {} card {} match {}]",
                    t0.elapsed().as_secs_f64(),
                    e.n_in,
                    e.n_blocks,
                    decisions.len(),
                    e.decisions,
                    e.conflicts,
                    e.by_rule[Why::Cover as usize],
                    e.by_rule[Why::Cardinality as usize],
                    e.by_rule[Why::Matching as usize],
                );
            }
        }

        if conflict {
            e.conflicts += 1;
            conflict = false;
            loop {
                if decisions.is_empty() {
                    return Outcome::Unsat;
                }
                e.pop_level();
                let d = decisions.last_mut().unwrap();
                if d.next < d.opts.len() {
                    let pick = d.opts[d.next];
                    d.next += 1;
                    e.push_level();
                    e.decisions += 1;
                    e.enqueue(pick);
                    if !e.propagate() {
                        conflict = true;
                    }
                    break;
                }
                decisions.pop();
            }
            continue;
        }

        let Some((_item, opts)) = e.select() else {
            // no uncovered item remains
            return if e.all_covered() {
                Outcome::Sat
            } else {
                // every item covered but block count wrong is impossible;
                // guard anyway rather than claim a result
                Outcome::Unknown("internal: covered but block count mismatch".into())
            };
        };
        if opts.is_empty() {
            conflict = true;
            continue;
        }
        let pick = opts[0];
        decisions.push(Decision { opts, next: 1 });
        e.push_level();
        e.decisions += 1;
        e.enqueue(pick);
        if !e.propagate() {
            conflict = true;
        }
    }
}


/// Knuth's random-probing estimator for the size of the backtracking tree.
/// Descend from the root picking uniformly among the options the solver would
/// try; the expectation of the accumulated weight is the node count. Variance
/// is huge, so report the distribution, not just the mean.
fn estimate(e: &mut Engine, probes: usize, seed: u64) {
    let mut st = seed | 1;
    let mut rng = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    let mut totals: Vec<f64> = Vec::with_capacity(probes);
    let mut depths: Vec<usize> = Vec::with_capacity(probes);
    let mut sols = 0usize;
    for _ in 0..probes {
        let mut w = 1.0f64;
        let mut total = 1.0f64;
        let mut pushed = 0usize;
        loop {
            let Some((_it, opts)) = e.select() else {
                sols += 1;
                break;
            };
            let d = opts.len();
            if d == 0 {
                break;
            }
            w *= d as f64;
            total += w;
            let pick = opts[(rng() as usize) % d];
            e.push_level();
            pushed += 1;
            e.enqueue(pick);
            if !e.propagate() {
                break;
            }
        }
        for _ in 0..pushed {
            e.pop_level();
        }
        totals.push(total);
        depths.push(pushed);
    }
    totals.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let mean: f64 = totals.iter().sum::<f64>() / probes as f64;
    let med = totals[probes / 2];
    let gm = (totals.iter().map(|x| x.ln()).sum::<f64>() / probes as f64).exp();
    let dmean: f64 = depths.iter().sum::<usize>() as f64 / probes as f64;
    println!("  probes            {probes}");
    println!("  mean  nodes       {mean:.3e}   <- the estimator");
    println!("  median nodes      {med:.3e}");
    println!("  geometric mean    {gm:.3e}");
    println!("  p95 / max         {:.3e} / {:.3e}", totals[probes * 95 / 100], totals[probes - 1]);
    println!("  mean probe depth  {dmean:.1}");
    println!("  probes reaching a full cover: {sols}");
}

fn run(o: Opts) -> anyhow::Result<Outcome> {
    let t0 = Instant::now();
    let mut e = Engine::new(o.v, o.matching);
    e.use_filter = o.filter;
    if !o.quiet {
        println!(
            "s45  v={}  items={}  options={}  blocks={}  triples={} (perfect matchings on {} points)",
            o.v, e.n_items, e.n_opts, e.n_blocks, e.n_triples, e.p
        );
        println!(
            "     propagator: exact-cover{}   symmetry: {}   tables {:.1} MiB, built in {:.2}s",
            if o.matching { if o.filter { " + triple blossom + edge filter" } else { " + triple blossom" } } else { " only" },
            if o.symmetry { "spread through {0,1,2}" } else { "none" },
            e.state_bytes() as f64 / (1024.0 * 1024.0),
            t0.elapsed().as_secs_f64()
        );
    }

    e.push_level();
    if o.symmetry {
        e.break_symmetry();
    }
    let mut out = if !e.propagate() {
        Outcome::Unsat
    } else if o.symmetry && o.level2 {
        // Level-2 orbit branching: a disjunction, so UNSAT only if every branch
        // is UNSAT, and any UNKNOWN branch makes the whole answer UNKNOWN.
        let branches = e.level2_branches();
        if !o.quiet {
            println!("     level-2 branches: {} (surviving; p(n)-p(n-1))  {:?}",
                     branches.len(), branches);
        }
        let mut acc = Outcome::Unsat;
        for (bi, lam) in branches.iter().enumerate() {
            e.push_level();
            e.break_symmetry_level2(lam);
            let live = e.propagate();
            if live {
                match search(&mut e, &o) {
                    // do NOT pop: the caller reads e.blocks() off this level
                    Outcome::Sat => { acc = Outcome::Sat; break; }
                    Outcome::Unsat => {}
                    u @ Outcome::Unknown(_) => { acc = u; e.pop_level(); break; }
                }
            } else if !o.quiet {
                println!("     branch {}/{} {:?}: refuted at setup",
                         bi + 1, branches.len(), lam);
            }
            e.pop_level();
        }
        acc
    } else {
        search(&mut e, &o)
    };

    if out == Outcome::Sat {
        let blocks = e.blocks();
        match verify::verify(o.v, &blocks) {
            Ok(msg) => {
                if !o.quiet {
                    println!("verify: {msg}");
                }
                let path = format!("s45_{}_blocks.txt", o.v);
                verify::write_blocks(&path, o.v, &blocks)?;
                if !o.quiet {
                    println!("blocks written to {path}");
                }
            }
            Err(msg) => {
                anyhow::bail!("SEV-1: search reported SAT but verification failed: {msg}");
            }
        }
    }

    if !o.quiet {
        println!(
            "\n  wall {:.2}s   decisions {}   conflicts {}   propagations {}",
            t0.elapsed().as_secs_f64(),
            e.decisions,
            e.conflicts,
            e.props
        );
        println!("  edges filtered out by matching: {}", e.filtered);
        println!(
            "  conflicts by rule:  cover {}   cardinality {}   matching {}",
            e.by_rule[Why::Cover as usize],
            e.by_rule[Why::Cardinality as usize],
            e.by_rule[Why::Matching as usize]
        );
    }
    if let Outcome::Unknown(ref why) = out {
        let _ = why;
    }
    if out == Outcome::Sat && o.quiet {
        out = Outcome::Sat;
    }
    Ok(out)
}

fn parse_dur(s: &str) -> anyhow::Result<Duration> {
    let s = s.trim();
    let idx = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    let n: u64 = s[..idx].parse()?;
    Ok(match &s[idx..] {
        "" | "s" => Duration::from_secs(n),
        "m" => Duration::from_secs(n * 60),
        "h" => Duration::from_secs(n * 3600),
        "d" => Duration::from_secs(n * 86400),
        u => anyhow::bail!("unknown duration unit `{u}`"),
    })
}

fn usage() -> ! {
    eprintln!(
        "s45 — existence search for the Steiner system S(4,5,v)

USAGE
  s45 solve -v <V> [OPTIONS]
  s45 verify -v <V> <blocks.txt>
  s45 info  -v <V>

OPTIONS
  --no-matching        disable the triple blossom propagator (exact cover only)
  --filter             also remove edges in no perfect matching (Regin analogue)
  --no-symmetry        disable the {{0,1,2}} spread symmetry break
  --no-level2          disable the level-2 orbit branching at {{0,1,3}}
  --timeout <30s|5m>
  --max-conflicts <N>
  --quiet

EXIT   0 SAT   1 UNSAT   2 UNKNOWN   3 ERROR   (a limit never prints UNSAT)"
    );
    std::process::exit(EXIT_ERROR as i32)
}

fn main() -> ExitCode {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        eprintln!("s45: internal assertion failure -> ERROR (exit 3)");
        std::process::exit(EXIT_ERROR as i32);
    }));

    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
    }
    let get = |flag: &str| -> Option<String> {
        args.iter().position(|a| a == flag).and_then(|i| args.get(i + 1).cloned())
    };
    let has = |flag: &str| args.iter().any(|a| a == flag);

    let v: u32 = match get("-v").or_else(|| get("--v")) {
        Some(s) => match s.parse() {
            Ok(x) => x,
            Err(_) => usage(),
        },
        None => usage(),
    };

    let res = (|| -> anyhow::Result<ExitCode> {
        match args[0].as_str() {
            "info" => {
                let e = Engine::new(v, true);
                println!(
                    "S(4,5,{v}):  items C(v,4) = {}   options C(v,5) = {}   blocks = {}",
                    e.n_items, e.n_opts, e.n_blocks
                );
                println!(
                    "  triples C(v,3) = {}, each a perfect matching on v-3 = {} points",
                    e.n_triples, e.p
                );
                println!("  incidence: options x 10 = {}", e.n_opts * 10);
                println!("  tables {:.1} MiB", e.state_bytes() as f64 / (1024.0 * 1024.0));
                Ok(ExitCode::SUCCESS)
            }
            "verify" => {
                let path = args.last().unwrap();
                let blocks = verify::read_blocks(path)?;
                match verify::verify(v, &blocks) {
                    Ok(msg) => {
                        println!("{msg}");
                        Ok(ExitCode::SUCCESS)
                    }
                    Err(msg) => {
                        println!("INVALID: {msg}");
                        Ok(ExitCode::from(1))
                    }
                }
            }
            "estimate" => {
                let mut e = Engine::new(v, !has("--no-matching"));
                e.use_filter = has("--filter");
                e.push_level();
                if !has("--no-symmetry") {
                    e.break_symmetry();
                }
                if !e.propagate() {
                    println!("root propagation refutes v={v}: tree size 0");
                    return Ok(ExitCode::from(1));
                }
                let probes: usize =
                    get("--probes").and_then(|s| s.parse().ok()).unwrap_or(2000);
                println!("tree-size estimate for S(4,5,{v})");
                if has("--no-level2") {
                    estimate(&mut e, probes, 12345);
                } else {
                    // tree size is the SUM over the level-2 branches
                    let branches = e.level2_branches();
                    println!("  summing over {} level-2 branches {:?}", branches.len(), branches);
                    for lam in &branches {
                        e.push_level();
                        e.break_symmetry_level2(lam);
                        if e.propagate() {
                            println!("  branch {:?}:", lam);
                            estimate(&mut e, probes, 12345);
                        } else {
                            println!("  branch {:?}: refuted at setup, 0 nodes", lam);
                        }
                        e.pop_level();
                    }
                }
                Ok(ExitCode::SUCCESS)
            }
            "solve" => {
                let o = Opts {
                    v,
                    matching: !has("--no-matching"),
                    symmetry: !has("--no-symmetry"),
                    timeout: match get("--timeout") {
                        Some(s) => Some(parse_dur(&s)?),
                        None => None,
                    },
                    max_conflicts: get("--max-conflicts").and_then(|s| s.parse().ok()),
                    quiet: has("--quiet"),
                    filter: has("--filter"),
                    level2: !has("--no-level2"),
                };
                let quiet = o.quiet;
                let out = run(o)?;
                let (label, code) = match &out {
                    Outcome::Sat => ("SAT", 0u8),
                    Outcome::Unsat => ("UNSAT", 1),
                    Outcome::Unknown(w) => {
                        if !quiet {
                            println!("\nRESULT: UNKNOWN  ({w})");
                        } else {
                            println!("RESULT: UNKNOWN  ({w})");
                        }
                        return Ok(ExitCode::from(2));
                    }
                };
                println!(
                    "\nRESULT: {label}{}",
                    if code == 1 { "  (search space exhausted)" } else { "" }
                );
                Ok(ExitCode::from(code))
            }
            #[cfg(feature = "cdcl")]
            "cdcl" => {
                let e = Engine::new(v, false);
                let level1 = if has("--no-symmetry") { Vec::new() } else { e.symmetry_units() };
                let branches: Vec<Vec<u32>> = if has("--no-level2") || has("--no-symmetry") {
                    vec![Vec::new()]
                } else {
                    e.level2_branches()
                };
                let only: Option<usize> = get("--branch").and_then(|s| s.parse().ok());
                let matching = has("--matching");
                let tight = !has("--eager");
                let quiet = has("--quiet");
                let timeout = match get("--timeout") {
                    Some(s) => Some(parse_dur(&s)?),
                    None => None,
                };
                let t0 = Instant::now();

                if has("--count") {
                    let limit: usize = get("--count").and_then(|s| s.parse().ok()).unwrap_or(1000);
                    let mut total = 0;
                    for (bi, lam) in branches.iter().enumerate() {
                        let mut units = level1.clone();
                        units.extend(e.level2_units(lam));
                        let n = cdcl::enumerate_branch(v, &units, tight, limit);
                        println!("branch {bi} lambda {lam:?}: {n} designs");
                        total += n;
                    }
                    println!("\ntotal designs found: {total}");
                    return Ok(ExitCode::SUCCESS);
                }

                let mut unknown: Option<String> = None;
                let mut sat: Option<Vec<u32>> = None;
                for (bi, lam) in branches.iter().enumerate() {
                    if only.map_or(false, |k| k != bi) {
                        continue;
                    }
                    let mut units = level1.clone();
                    units.extend(e.level2_units(lam));
                    if !quiet {
                        println!("branch {bi}/{} lambda {lam:?}", branches.len());
                    }
                    // Each branch gets whatever is left of the global budget,
                    // so --timeout bounds the whole run and not each piece.
                    let left = match timeout {
                        Some(t) => match t.checked_sub(t0.elapsed()) {
                            Some(d) if !d.is_zero() => Some(d),
                            _ => {
                                unknown = Some("timeout".into());
                                break;
                            }
                        },
                        None => None,
                    };
                    let (ans, st) = cdcl::solve_branch(v, &units, matching, has("--mrv"), tight, left, quiet);
                    if !quiet {
                        println!(
                            "  theory props {}  reasons {}  conflicts [cover {} card {} match {}]",
                            st.theory_props, st.reason_clauses,
                            st.cover_conflicts, st.card_conflicts, st.match_conflicts
                        );
                    }
                    match ans {
                        cdcl::Answer::Unsat => {}
                        cdcl::Answer::Sat(b) => {
                            sat = Some(b);
                            break;
                        }
                        cdcl::Answer::Unknown => {
                            unknown = Some(format!("branch {bi} hit a limit"));
                            break;
                        }
                    }
                }

                println!("\nwall {:.2}s", t0.elapsed().as_secs_f64());
                if let Some(blocks) = sat {
                    // A refutation nobody can check is worth nothing, and so is
                    // a witness nobody can check; verify before claiming SAT.
                    match verify::verify(v, &blocks) {
                        Ok(msg) => println!("{msg}"),
                        Err(msg) => anyhow::bail!("search reported SAT but verification failed: {msg}"),
                    }
                    let path = get("--witness-out").unwrap_or_else(|| format!("s45_{v}_blocks.txt"));
                    verify::write_blocks(&path, v, &blocks)?;
                    println!("witness written to {path}");
                    println!("\nRESULT: SAT");
                    return Ok(ExitCode::SUCCESS);
                }
                if let Some(w) = unknown {
                    println!("\nRESULT: UNKNOWN  ({w})");
                    return Ok(ExitCode::from(2));
                }
                println!("\nRESULT: UNSAT  (search space exhausted)");
                Ok(ExitCode::from(1))
            }
            _ => usage(),
        }
    })();

    match res {
        Ok(c) => c,
        Err(e) => {
            eprintln!("s45: {e:#}");
            ExitCode::from(EXIT_ERROR)
        }
    }
}
