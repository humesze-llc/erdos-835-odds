//! `odd835 bench` — propagator and neighbour-enumeration microbenchmarks
//! (spec section 5). Uses `std::time` rather than criterion so the default
//! build keeps to the four authorised dependencies.

use crate::combi::Combi;
use crate::interrupt::Interrupt;
use crate::solver::engine::Engine;
use crate::solver::Config;
use crate::stats::Stats;
use crate::util::{commas, fmt_rate, Rng};
use anyhow::Result;
use std::time::{Duration, Instant};

fn timed<F: FnMut() -> u64>(label: &str, budget: Duration, mut f: F) -> f64 {
    let t0 = Instant::now();
    let mut ops = 0u64;
    while t0.elapsed() < budget {
        ops += f();
    }
    let secs = t0.elapsed().as_secs_f64();
    let rate = ops as f64 / secs;
    println!(
        "  {:<34} {:>14} ops   {:>10}/s",
        label,
        commas(ops),
        fmt_rate(rate)
    );
    rate
}

pub fn run(k: u32, seconds: u64) -> Result<()> {
    let c = Combi::new(k)?;
    let budget = Duration::from_secs(seconds.max(1));
    println!(
        "odd835 bench  k={k}  |V|={}  colours={}  budget {}s/case\n",
        commas(c.num_vertices),
        c.colors,
        seconds
    );

    let mut rng = Rng::new(1);
    let nv = c.num_vertices;

    timed("unrank", budget, || {
        let mut acc = 0u32;
        for _ in 0..10_000 {
            acc ^= c.unrank(rng.below(nv) as u32);
        }
        std::hint::black_box(acc);
        10_000
    });

    let sample: Vec<u32> = (0..4096).map(|_| c.unrank(rng.below(nv) as u32)).collect();

    timed("rank (table)", budget, || {
        let mut acc = 0u32;
        for &m in &sample {
            acc ^= c.rank(m);
        }
        std::hint::black_box(acc);
        sample.len() as u64
    });

    timed("rank (reference loop)", budget, || {
        let mut acc = 0u32;
        for &m in &sample {
            acc ^= c.rank_ref(m);
        }
        std::hint::black_box(acc);
        sample.len() as u64
    });

    timed("neighbour enumeration (masks)", budget, || {
        let mut acc = 0u32;
        for &m in &sample {
            for nb in c.neighbors(m) {
                acc ^= nb;
            }
        }
        std::hint::black_box(acc);
        (sample.len() as u64) * k as u64
    });

    timed("neighbour enumeration + rank", budget, || {
        let mut acc = 0u32;
        for &m in &sample {
            for nb in c.neighbors(m) {
                acc ^= c.rank(nb);
            }
        }
        std::hint::black_box(acc);
        (sample.len() as u64) * k as u64
    });

    timed("closed neighbourhood gather", budget, || {
        let mut buf = [0u32; 18];
        let mut acc = 0u32;
        for &m in &sample {
            let n = c.closed_nbhd_masks(m, &mut buf);
            for &x in buf.iter().take(n) {
                acc ^= c.rank(x);
            }
        }
        std::hint::black_box(acc);
        (sample.len() as u64) * (k as u64 + 1)
    });

    // Rule B over a live engine, with the root symmetry-breaking assignments in
    // place so domains are realistic.
    let mut cfg = Config::new(k);
    cfg.quiet = true;
    let c2 = Combi::new(k)?;
    let stats = Stats::new(k, "bench", c2.num_vertices, c2.colors, c2.m, 0, None)?;
    let mut e = Engine::new(c2, cfg, stats)?;
    let m0 = e.c.unrank(0);
    e.enqueue_assignment(0, m0, 0);
    let mut nb: Vec<(u32, u32)> = e.c.neighbors(m0).map(|m| (e.c.rank(m), m)).collect();
    nb.sort_unstable();
    for (i, (idx, mask)) in nb.iter().enumerate() {
        e.enqueue_assignment(*idx, *mask, (i + 1) as u8);
    }
    let _ = e.propagate();
    let _ = &Interrupt::new();

    let mut i = 0usize;
    timed("Rule B (one vertex, k+1 nbhds)", budget, || {
        for _ in 0..1024 {
            let m = sample[i % sample.len()];
            i += 1;
            let _ = e.bench_rule_b(m);
        }
        1024
    });

    println!(
        "\n  each Rule B application touches (k+1)^2 = {} vertices",
        (k + 1) * (k + 1)
    );
    Ok(())
}
