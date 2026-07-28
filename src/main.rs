#![forbid(unsafe_code)]
//! `odd835` — a finite search engine for Erdős Problem #835.
//!
//! Decides, for even `k`, whether the odd graph `O_k` admits a partition of its
//! vertex set into `k+1` perfect 1-codes — equivalently whether the Johnson
//! graph `J(2k,k)` has chromatic number `k+1`.
//!
//! See ARCHITECTURE.md for the encoding, the propagators, and the correctness
//! arguments; RESULTS.md for measurements.

mod bench;
mod check;
mod codesearch;
mod combi;
mod designs;
mod interrupt;
mod oracle;
mod solver;
mod stats;
mod util;
mod witness;

use anyhow::{bail, Result};
use clap::{ArgAction, Args, Parser, Subcommand, ValueEnum};
use combi::Combi;
use interrupt::Interrupt;
use solver::{BranchOrder, Config, Outcome, PropagatorMode, SymmetryMode};
use stats::StatsFormat;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

const EXIT_ERROR: u8 = 3;

#[derive(Parser)]
#[command(
    name = "odd835",
    version,
    about = "Finite search engine for Erdos Problem #835",
    long_about = "Decides whether the odd graph O_k admits a partition of its vertex set into \
                  k+1 perfect 1-codes. The number of colours is always exactly k+1 and is not \
                  configurable. Only even k are meaningful; odd k is rejected at argument-parse \
                  time with the structure-theorem reason.\n\n\
                  The per-option defaults below are the ones the build spec names. They are NOT \
                  the fastest configuration. Measured best (see RESULTS.md):\n\n    \
                  odd835 solve -k K --symmetry orbit --propagator matching \\\n        \
                  --branch-order link --link-level 2 --anchors 0\n\n\
                  On k=6, the largest rung this engine closes, the defaults do not finish in \
                  180 s (47.8M conflicts); the line above proves UNSAT in 22.7 s (70,572 \
                  conflicts). Both settings are answer-preserving."
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Print derived constants and exit.
    Info {
        #[arg(short = 'k', long = "k")]
        k: u32,
    },
    /// Search for a (K+1)-colouring of O_K.
    Solve(SolveArgs),
    /// Search for a single perfect 1-code in O_K.
    Code(SolveArgs),
    /// Independently verify a claimed colouring or code.
    Check {
        #[arg(short = 'k', long = "k")]
        k: Option<u32>,
        #[arg(long)]
        witness: PathBuf,
    },
    /// Run the known-answer test suite.
    Oracle {
        /// Run only entries whose name contains this substring.
        #[arg(long)]
        only: Option<String>,
        /// Per-entry wall-clock budget.
        #[arg(long, value_parser = parse_dur, default_value = "300s")]
        budget: Duration,
        /// Skip entries expected to take longer than the budget.
        #[arg(long, action = ArgAction::SetTrue)]
        quick: bool,
    },
    /// Propagator and neighbour-enumeration microbenchmarks.
    Bench {
        #[arg(short = 'k', long = "k")]
        k: u32,
        #[arg(long, default_value_t = 3)]
        seconds: u64,
    },
}

#[derive(Args, Clone)]
struct SolveArgs {
    #[arg(short = 'k', long = "k", help = "even integer, 2..=16")]
    k: u32,
    #[arg(long, value_parser = parse_dur, help = "e.g. 30s, 45m, 12h, 7d")]
    timeout: Option<Duration>,
    #[arg(long)]
    max_conflicts: Option<u64>,
    #[arg(long, default_value_t = 0, help = "RNG seed; default 0 (fully deterministic)")]
    seed: u64,
    #[arg(long, value_enum, default_value_t = SymmetryArg::Color)]
    symmetry: SymmetryArg,
    #[arg(long, value_enum, default_value_t = PropagatorArg::Count)]
    propagator: PropagatorArg,
    #[arg(long, action = ArgAction::SetTrue, help = "enable Rule C [default: on]")]
    cardinality: bool,
    #[arg(long, action = ArgAction::SetTrue, help = "disable Rule C")]
    no_cardinality: bool,
    #[arg(long, default_value_t = 16, help = "anchors per class for Rules D/E, 0 disables")]
    anchors: usize,
    #[arg(long, action = ArgAction::SetTrue, help = "also enforce the D/E reachability direction")]
    anchor_reach: bool,
    #[arg(long, value_enum, default_value_t = BranchArg::Mrv)]
    branch_order: BranchArg,
    #[arg(long, default_value_t = 3, help = "t for link branching")]
    link_level: u32,
    #[arg(long, value_delimiter = ',', help = "comma-separated t values, e.g. 2,3,4")]
    rung_check: Vec<u32>,
    #[arg(long, default_value_t = 64)]
    rung_sample: usize,
    #[arg(long, value_parser = parse_dur, default_value = "60s")]
    rung_interval: Duration,
    #[arg(long, value_parser = parse_dur, default_value = "5s")]
    stats_interval: Duration,
    #[arg(long, value_enum, default_value_t = FormatArg::Human)]
    stats_format: FormatArg,
    #[arg(long)]
    stats_file: Option<PathBuf>,
    #[arg(long)]
    checkpoint: Option<PathBuf>,
    #[arg(long, value_parser = parse_dur)]
    checkpoint_interval: Option<Duration>,
    #[arg(long)]
    resume: Option<PathBuf>,
    #[arg(long)]
    witness_out: Option<PathBuf>,
    #[arg(long, help = "replayable JSONL trace for independent UNSAT auditing")]
    conflict_log: Option<PathBuf>,
    /// Abort with UNKNOWN if resident memory exceeds this (e.g. 8GiB).
    /// Required by milestone M6; not part of the section 5 option list.
    #[arg(long, value_parser = parse_size)]
    memory_limit: Option<u64>,
    #[arg(long, action = ArgAction::SetTrue, help = "run the full N_j check on every completed class")]
    verify_classes: bool,
    #[arg(long, default_value_t = 1, help = "no-op in v1")]
    threads: usize,
    #[arg(short = 'v', long, action = ArgAction::Count)]
    verbose: u8,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum SymmetryArg {
    None,
    Color,
    /// `color` plus the root orbit disjunction (see ARCHITECTURE.md).
    Orbit,
}
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum PropagatorArg {
    Count,
    Matching,
}
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum BranchArg {
    Mrv,
    Link,
}
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum FormatArg {
    Human,
    Json,
    Jsonl,
}

fn parse_dur(s: &str) -> Result<Duration, String> {
    util::parse_duration(s).map_err(|e| e.to_string())
}
fn parse_size(s: &str) -> Result<u64, String> {
    util::parse_bytes(s).map_err(|e| e.to_string())
}

impl SolveArgs {
    fn to_config(&self) -> Result<Config> {
        if self.no_cardinality && self.cardinality {
            bail!("--cardinality and --no-cardinality are mutually exclusive");
        }
        let mut c = Config::new(self.k);
        c.timeout = self.timeout;
        c.max_conflicts = self.max_conflicts;
        c.seed = self.seed;
        c.symmetry = match self.symmetry {
            SymmetryArg::None => SymmetryMode::None,
            SymmetryArg::Color => SymmetryMode::Color,
            SymmetryArg::Orbit => SymmetryMode::Orbit,
        };
        c.propagator = match self.propagator {
            PropagatorArg::Count => PropagatorMode::Count,
            PropagatorArg::Matching => PropagatorMode::Matching,
        };
        c.cardinality = !self.no_cardinality;
        c.anchors = self.anchors;
        c.anchor_reach = self.anchor_reach;
        c.branch_order = match self.branch_order {
            BranchArg::Mrv => BranchOrder::Mrv,
            BranchArg::Link => BranchOrder::Link,
        };
        // clamped again inside the solver, but normalise here so --help,
        // the checkpoint fingerprint and the stats all agree
        c.link_level = self.link_level.clamp(1, (self.k.max(2) - 1).max(1));
        c.rung_check = self.rung_check.clone();
        c.rung_sample = self.rung_sample;
        c.rung_interval = self.rung_interval;
        c.stats_interval = self.stats_interval;
        c.stats_format = match self.stats_format {
            FormatArg::Human => StatsFormat::Human,
            FormatArg::Json => StatsFormat::Json,
            FormatArg::Jsonl => StatsFormat::Jsonl,
        };
        c.stats_file = self.stats_file.clone();
        c.checkpoint = self.checkpoint.clone();
        c.checkpoint_interval = self.checkpoint_interval;
        c.resume = self.resume.clone();
        c.witness_out = self.witness_out.clone();
        c.conflict_log = self.conflict_log.clone();
        c.memory_limit = self.memory_limit;
        c.verify_classes = self.verify_classes;
        c.threads = self.threads;
        c.verbose = self.verbose;
        Ok(c)
    }
}

fn main() -> ExitCode {
    // An internal assertion failure must exit 3, not 101.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        eprintln!("odd835: internal assertion failure -> ERROR (exit 3)");
        std::process::exit(EXIT_ERROR as i32);
    }));

    match real_main() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("odd835: {e:#}");
            ExitCode::from(EXIT_ERROR)
        }
    }
}

fn real_main() -> Result<ExitCode> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Info { k } => {
            let c = Combi::new(k)?;
            combi::print_info(&c);
            Ok(ExitCode::SUCCESS)
        }
        Cmd::Check { k, witness } => {
            let report = check::check_file(&witness, k)?;
            report.print();
            Ok(if report.ok() {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        Cmd::Solve(args) => {
            let cfg = args.to_config()?;
            // Constructing Combi is what rejects odd k, with the reason.
            Combi::new(cfg.k)?;
            let irq = Interrupt::new();
            irq.install()?;
            if !interrupt::SIGNALS_AVAILABLE && cfg.verbose > 0 {
                eprintln!(
                    "note: built without the `signals` feature (or not on unix); \
                     SIGINT/SIGUSR1 handling is inactive"
                );
            }
            let mut s = solver::search::Solver::new(cfg, irq)?;
            let out = s.run()?;
            report_outcome(&out);
            Ok(ExitCode::from(out.exit_code() as u8))
        }
        Cmd::Code(args) => {
            let cfg = args.to_config()?;
            Combi::new(cfg.k)?;
            let irq = Interrupt::new();
            irq.install()?;
            let mut s = codesearch::CodeSolver::new(cfg, irq)?;
            let out = s.run()?;
            report_outcome(&out);
            Ok(ExitCode::from(out.exit_code() as u8))
        }
        Cmd::Oracle { only, budget, quick } => {
            let ok = oracle::run(only.as_deref(), budget, quick)?;
            Ok(if ok { ExitCode::SUCCESS } else { ExitCode::from(1) })
        }
        Cmd::Bench { k, seconds } => {
            bench::run(k, seconds)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn report_outcome(out: &Outcome) {
    match out {
        Outcome::Sat => println!("\nRESULT: SAT"),
        Outcome::Unsat => println!("\nRESULT: UNSAT  (search space exhausted)"),
        Outcome::Unknown(why) => println!("\nRESULT: UNKNOWN  ({why})"),
    }
}
