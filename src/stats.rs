//! Observability (spec section 8). Every field in the human display is also
//! present in the JSONL record; nothing is human-only.

use crate::util::{commas, cpu_time, fmt_bytes, fmt_hms, fmt_rate, fmt_sci, rss_bytes};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Write};
use std::path::Path;
use std::time::{Duration, Instant};

pub const RULE_NAMES: [&str; 6] = ["a", "b", "c", "d", "e", "matching"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
    Matching = 5,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatsFormat {
    Human,
    Json,
    Jsonl,
}

#[derive(Clone, Debug, Default)]
pub struct RungStats {
    pub checked: u64,
    pub passed: u64,
    pub failed: u64,
    pub completed: u64,
}

#[derive(Clone, Copy, Debug, Default)]
struct Sample {
    at: Duration,
    decisions: u64,
    conflicts: u64,
    propagations: u64,
}

pub struct Stats {
    pub run_id: String,
    pub k: u32,
    pub mode: &'static str,
    pub num_vertices: u64,
    pub colors: u32,
    pub m: u64,
    pub start: Instant,

    // coverage
    pub assigned: u64,
    pub assigned_high_water: u64,
    pub high_water_at: Duration,
    pub saturated: u64,
    pub classes_closed: u32,

    // search
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub backtracks: u64,
    pub restarts: u64,
    pub depth_current: usize,
    pub depth_max: usize,

    // domains
    pub dom_total: u64,
    pub dom_singletons: u64,

    // attribution
    pub conflicts_by_rule: [u64; 6],
    pub forced_by_rule: [u64; 6],

    // rungs
    pub rungs: BTreeMap<u32, RungStats>,

    // health / bookkeeping
    pub state_bytes: u64,
    pub peak_state_bytes: u64,
    pub peak_rss_bytes: u64,
    pub checkpoint_last: Option<Duration>,
    pub checkpoint_next: Option<Duration>,
    pub full_scans: u64,
    pub anchor_inits: u64,

    last_sample: Sample,
    last_emit: Option<Instant>,
    painted_lines: usize,
    jsonl: Option<BufWriter<File>>,
}

impl Stats {
    pub fn new(
        k: u32,
        mode: &'static str,
        num_vertices: u64,
        colors: u32,
        m: u64,
        seed: u64,
        stats_file: Option<&Path>,
    ) -> anyhow::Result<Stats> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        let run_id = format!(
            "{:016x}",
            nanos ^ (std::process::id() as u64).wrapping_mul(0x9E3779B97F4A7C15) ^ seed
        );
        let jsonl = match stats_file {
            Some(p) => Some(BufWriter::new(
                OpenOptions::new().create(true).append(true).open(p)?,
            )),
            None => None,
        };
        Ok(Stats {
            run_id,
            k,
            mode,
            num_vertices,
            colors,
            m,
            start: Instant::now(),
            assigned: 0,
            assigned_high_water: 0,
            high_water_at: Duration::ZERO,
            saturated: 0,
            classes_closed: 0,
            decisions: 0,
            propagations: 0,
            conflicts: 0,
            backtracks: 0,
            restarts: 0,
            depth_current: 0,
            depth_max: 0,
            dom_total: 0,
            dom_singletons: 0,
            conflicts_by_rule: [0; 6],
            forced_by_rule: [0; 6],
            rungs: BTreeMap::new(),
            state_bytes: 0,
            peak_state_bytes: 0,
            peak_rss_bytes: 0,
            checkpoint_last: None,
            checkpoint_next: None,
            full_scans: 0,
            anchor_inits: 0,
            last_sample: Sample::default(),
            last_emit: None,
            painted_lines: 0,
            jsonl,
        })
    }

    #[inline]
    pub fn elapsed(&self) -> Duration {
        self.start.elapsed()
    }

    #[inline]
    pub fn note_assigned(&mut self, assigned: u64) {
        self.assigned = assigned;
        if assigned > self.assigned_high_water {
            self.assigned_high_water = assigned;
            self.high_water_at = self.start.elapsed();
        }
    }

    #[inline]
    pub fn conflict(&mut self, rule: Rule) {
        self.conflicts += 1;
        self.conflicts_by_rule[rule as usize] += 1;
    }

    #[inline]
    pub fn forced(&mut self, rule: Rule) {
        self.forced_by_rule[rule as usize] += 1;
    }

    pub fn stall(&self) -> Duration {
        self.start.elapsed().saturating_sub(self.high_water_at)
    }

    pub fn rss(&self) -> u64 {
        rss_bytes().unwrap_or(self.state_bytes)
    }

    pub fn observe_memory(&mut self, state_bytes: u64) {
        self.state_bytes = state_bytes;
        self.peak_state_bytes = self.peak_state_bytes.max(state_bytes);
        if let Some(r) = rss_bytes() {
            self.peak_rss_bytes = self.peak_rss_bytes.max(r);
        } else {
            self.peak_rss_bytes = self.peak_state_bytes;
        }
    }

    /// True when at least `interval` has passed since the previous emission.
    pub fn due(&self, interval: Duration) -> bool {
        match self.last_emit {
            None => true,
            Some(t) => t.elapsed() >= interval,
        }
    }

    pub fn emit(&mut self, format: StatsFormat) {
        let now = Instant::now();
        let elapsed = self.start.elapsed();
        let cur = Sample {
            at: elapsed,
            decisions: self.decisions,
            conflicts: self.conflicts,
            propagations: self.propagations,
        };
        let window = (cur.at.as_secs_f64() - self.last_sample.at.as_secs_f64()).max(1e-9);
        let rates = (
            (cur.decisions - self.last_sample.decisions) as f64 / window,
            (cur.conflicts - self.last_sample.conflicts) as f64 / window,
            (cur.propagations - self.last_sample.propagations) as f64 / window,
        );
        let line = self.json_line(rates);
        if let Some(w) = self.jsonl.as_mut() {
            let _ = writeln!(w, "{line}");
            let _ = w.flush();
        }
        match format {
            StatsFormat::Human => self.paint(rates),
            StatsFormat::Json | StatsFormat::Jsonl => {
                println!("{line}");
            }
        }
        self.last_sample = cur;
        self.last_emit = Some(now);
    }

    /// Final snapshot; never repaints in place.
    pub fn emit_final(&mut self, format: StatsFormat, outcome: &str) {
        let elapsed = self.start.elapsed();
        let cur = Sample {
            at: elapsed,
            decisions: self.decisions,
            conflicts: self.conflicts,
            propagations: self.propagations,
        };
        let window = cur.at.as_secs_f64().max(1e-9);
        let rates = (
            cur.decisions as f64 / window,
            cur.conflicts as f64 / window,
            cur.propagations as f64 / window,
        );
        let mut line = self.json_line(rates);
        // splice the outcome into the JSON record
        line.pop();
        let _ = write!(line, ",\"outcome\":\"{outcome}\",\"final\":true}}");
        if let Some(w) = self.jsonl.as_mut() {
            let _ = writeln!(w, "{line}");
            let _ = w.flush();
        }
        match format {
            StatsFormat::Human => {
                self.painted_lines = 0;
                self.paint(rates);
                println!("outcome         {outcome}");
            }
            StatsFormat::Json | StatsFormat::Jsonl => println!("{line}"),
        }
    }

    fn json_line(&self, rates: (f64, f64, f64)) -> String {
        let mut s = String::with_capacity(1400);
        let e = self.start.elapsed();
        let _ = write!(
            s,
            "{{\"schema_version\":1,\"run_id\":\"{}\",\"mode\":\"{}\",\"k\":{},\"wall_ms\":{}",
            self.run_id,
            self.mode,
            self.k,
            e.as_millis()
        );
        let _ = write!(
            s,
            ",\"num_vertices\":{},\"colors\":{},\"m\":{}",
            self.num_vertices, self.colors, self.m
        );
        let _ = write!(
            s,
            ",\"assigned\":{},\"assigned_pct\":{:.6},\"assigned_high_water\":{},\"high_water_ms\":{}",
            self.assigned,
            pct(self.assigned, self.num_vertices),
            self.assigned_high_water,
            self.high_water_at.as_millis()
        );
        let _ = write!(
            s,
            ",\"saturated\":{},\"saturated_pct\":{:.6},\"classes_closed\":{}",
            self.saturated,
            pct(self.saturated, self.num_vertices),
            self.classes_closed
        );
        let _ = write!(
            s,
            ",\"decisions\":{},\"propagations\":{},\"conflicts\":{},\"backtracks\":{},\"restarts\":{}",
            self.decisions, self.propagations, self.conflicts, self.backtracks, self.restarts
        );
        let _ = write!(
            s,
            ",\"depth_current\":{},\"depth_max\":{}",
            self.depth_current, self.depth_max
        );
        let _ = write!(
            s,
            ",\"decisions_per_sec\":{:.3},\"conflicts_per_sec\":{:.3},\"propagations_per_sec\":{:.3}",
            rates.0, rates.1, rates.2
        );
        let unassigned = self.num_vertices.saturating_sub(self.assigned);
        let _ = write!(
            s,
            ",\"dom_total\":{},\"dom_mean\":{:.4},\"dom_singletons\":{}",
            self.dom_total,
            if unassigned == 0 { 0.0 } else { self.dom_total as f64 / unassigned as f64 },
            self.dom_singletons
        );
        s.push_str(",\"conflicts_by_rule\":{");
        for (i, n) in RULE_NAMES.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(s, "\"{n}\":{}", self.conflicts_by_rule[i]);
        }
        s.push_str("},\"forced_by_rule\":{");
        for (i, n) in RULE_NAMES.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(s, "\"{n}\":{}", self.forced_by_rule[i]);
        }
        s.push_str("},\"rungs\":{");
        for (i, (t, r)) in self.rungs.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(
                s,
                "\"{t}\":{{\"checked\":{},\"passed\":{},\"failed\":{},\"completed\":{}}}",
                r.checked, r.passed, r.failed, r.completed
            );
        }
        s.push('}');
        let _ = write!(
            s,
            ",\"stall_ms\":{},\"rss_bytes\":{},\"peak_rss_bytes\":{},\"state_bytes\":{}",
            self.stall().as_millis(),
            self.rss(),
            self.peak_rss_bytes.max(self.rss()),
            self.state_bytes
        );
        let _ = write!(
            s,
            ",\"elapsed_ms\":{},\"cpu_ms\":{}",
            e.as_millis(),
            cpu_time().map(|d| d.as_millis()).unwrap_or(0)
        );
        let _ = write!(
            s,
            ",\"checkpoint_last_ms\":{},\"checkpoint_next_ms\":{}",
            self.checkpoint_last.map(|d| d.as_millis() as i128).unwrap_or(-1),
            self.checkpoint_next.map(|d| d.as_millis() as i128).unwrap_or(-1)
        );
        let _ = write!(
            s,
            ",\"full_scans\":{},\"anchor_inits\":{}}}",
            self.full_scans, self.anchor_inits
        );
        s
    }

    fn paint(&mut self, rates: (f64, f64, f64)) {
        let mut out = String::with_capacity(2048);
        if self.painted_lines > 0 {
            let _ = write!(out, "\x1b[{}A", self.painted_lines);
        }
        let bar = "─".repeat(74);
        let mut lines = 0usize;
        macro_rules! ln {
            ($($a:tt)*) => {{
                let _ = write!(out, $($a)*);
                out.push_str("\x1b[K\n");
                lines += 1;
            }};
        }
        ln!(
            "odd835  {}  k={}  |V|={}  colors={}  m={}      elapsed {}",
            self.mode,
            self.k,
            commas(self.num_vertices),
            self.colors,
            commas(self.m),
            fmt_hms(self.start.elapsed())
        );
        ln!("{bar}");
        ln!(
            "assigned    {:>16} / {:<16} {:>6.1}%   high-water {}",
            commas(self.assigned),
            commas(self.num_vertices),
            pct(self.assigned, self.num_vertices),
            commas(self.assigned_high_water)
        );
        ln!(
            "saturated ► {:>16} / {:<16} {:>6.1}%",
            commas(self.saturated),
            commas(self.num_vertices),
            pct(self.saturated, self.num_vertices)
        );
        ln!("classes closed         {:>4} / {}", self.classes_closed, self.colors);
        let unassigned = self.num_vertices.saturating_sub(self.assigned);
        ln!(
            "domains     Σ {:<12} mean {:<8.2} singletons {}",
            fmt_sci(self.dom_total as f64),
            if unassigned == 0 { 0.0 } else { self.dom_total as f64 / unassigned as f64 },
            commas(self.dom_singletons)
        );
        ln!("{bar}");
        ln!(
            "decisions   {:>16}      conflicts   {:>16}",
            commas(self.decisions),
            commas(self.conflicts)
        );
        ln!(
            "propagations{:>16}      backtracks  {:>16}",
            fmt_sci(self.propagations as f64),
            commas(self.backtracks)
        );
        ln!(
            "depth        cur {:<12}     max {:<12}  restarts {}",
            commas(self.depth_current as u64),
            commas(self.depth_max as u64),
            self.restarts
        );
        ln!(
            "rate        {:>8} conf/s   {:>8} prop/s   {:>8} dec/s",
            fmt_rate(rates.1),
            fmt_rate(rates.2),
            fmt_rate(rates.0)
        );
        ln!("{bar}");
        let tot: u64 = self.conflicts_by_rule.iter().sum();
        let mut attr = String::new();
        for (i, n) in RULE_NAMES.iter().enumerate() {
            let _ = write!(
                attr,
                "{} {:.1}%  ",
                n.to_uppercase(),
                if tot == 0 { 0.0 } else { 100.0 * self.conflicts_by_rule[i] as f64 / tot as f64 }
            );
        }
        ln!("conflicts by  {}", attr.trim_end());
        let mut rung = String::new();
        for (t, r) in &self.rungs {
            let _ = write!(
                rung,
                "t={} {} done / {} ok / {} fail   ",
                t, r.completed, r.passed, r.failed
            );
        }
        ln!(
            "rungs         {}",
            if rung.is_empty() { "(none configured)".to_string() } else { rung.trim_end().to_string() }
        );
        ln!("stall         {} since high-water", fmt_hms(self.stall()));
        ln!(
            "memory        {} RSS   peak {}   checkpoint {}",
            fmt_bytes(self.rss()),
            fmt_bytes(self.peak_rss_bytes.max(self.rss())),
            match self.checkpoint_next {
                Some(d) => format!("in {}", fmt_hms(d.saturating_sub(self.start.elapsed()))),
                None => "off".to_string(),
            }
        );
        print!("{out}");
        let _ = std::io::stdout().flush();
        self.painted_lines = lines;
    }
}

fn pct(a: u64, b: u64) -> f64 {
    if b == 0 {
        0.0
    } else {
        100.0 * a as f64 / b as f64
    }
}
