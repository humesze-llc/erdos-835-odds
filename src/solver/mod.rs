//! The partition solver: configuration, engine state, propagation, search.

pub mod engine;
pub mod link;
pub mod matching;
pub mod search;

use crate::stats::StatsFormat;
use std::path::PathBuf;
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymmetryMode {
    None,
    /// Spec section 4: consume the `(k+1)!` colour symmetry by fixing `N[v0]`.
    Color,
    /// `Color`, plus a root-level disjunction that consumes the `S(C_0)` factor
    /// of the residual vertex automorphism group. See ARCHITECTURE.md for the
    /// correctness argument; it is a complete reduction, not a heuristic.
    Orbit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PropagatorMode {
    Count,
    Matching,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchOrder {
    Mrv,
    Link,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub k: u32,
    pub timeout: Option<Duration>,
    pub max_conflicts: Option<u64>,
    pub seed: u64,
    pub symmetry: SymmetryMode,
    pub propagator: PropagatorMode,
    pub cardinality: bool,
    pub anchors: usize,
    pub anchor_reach: bool,
    pub branch_order: BranchOrder,
    pub link_level: u32,
    pub rung_check: Vec<u32>,
    pub rung_sample: usize,
    pub rung_interval: Duration,
    pub stats_interval: Duration,
    pub stats_format: StatsFormat,
    pub stats_file: Option<PathBuf>,
    pub checkpoint: Option<PathBuf>,
    pub checkpoint_interval: Option<Duration>,
    pub resume: Option<PathBuf>,
    pub witness_out: Option<PathBuf>,
    pub conflict_log: Option<PathBuf>,
    pub memory_limit: Option<u64>,
    pub verify_classes: bool,
    pub threads: usize,
    pub verbose: u8,
    /// Suppress the live display entirely (used by the oracle harness).
    pub quiet: bool,
}

impl Config {
    pub fn new(k: u32) -> Config {
        Config {
            k,
            timeout: None,
            max_conflicts: None,
            seed: 0,
            symmetry: SymmetryMode::Color,
            propagator: PropagatorMode::Count,
            cardinality: true,
            anchors: 16,
            anchor_reach: false,
            branch_order: BranchOrder::Mrv,
            link_level: 3,
            rung_check: Vec::new(),
            rung_sample: 64,
            rung_interval: Duration::from_secs(60),
            stats_interval: Duration::from_secs(5),
            stats_format: StatsFormat::Human,
            stats_file: None,
            checkpoint: None,
            checkpoint_interval: None,
            resume: None,
            witness_out: None,
            conflict_log: None,
            memory_limit: None,
            verify_classes: false,
            threads: 1,
            verbose: 0,
            quiet: false,
        }
    }
}

/// Spec section 4: three outcomes that must never be conflated, plus ERROR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Sat,
    Unsat,
    Unknown(String),
}

impl Outcome {
    pub fn label(&self) -> &'static str {
        match self {
            Outcome::Sat => "SAT",
            Outcome::Unsat => "UNSAT",
            Outcome::Unknown(_) => "UNKNOWN",
        }
    }
    pub fn exit_code(&self) -> i32 {
        match self {
            Outcome::Sat => 0,
            Outcome::Unsat => 1,
            Outcome::Unknown(_) => 2,
        }
    }
}
