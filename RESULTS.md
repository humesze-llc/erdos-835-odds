# odd835 — results

Everything here is measured. Where a rung did not finish it says so; nothing in
this file reports UNSAT because a budget ran out.

**Machine.** Windows 11 Pro 26200, x86-64, 32 logical cores. Rust 1.95.0 stable,
`--release` (`opt-level=3`, `lto=fat`, `codegen-units=1`), single threaded
(`--threads` is a no-op in v1). The spec targets Ubuntu 24.04; the only
platform-dependent behaviour is RSS reporting — `/proc/self/statm` is Linux
only, so on Windows the memory column is the engine's own state accounting
(`color + dom + sat_count + trail + assign stack + MRV heaps + queue bitsets`),
which is a floor on RSS, not RSS itself.

---

## 1. Headline

`k = 6` is the largest rung this engine closes. **`k = 8` and above do not
terminate**, so the `k = 12` gate the spec calls decisive is *not* met. The
`k = 12` number the spec asks to be reported before anything else is: **no
result — the search does not exhaust the space.** What can be reported for
`k ≥ 8` is progress inside a fixed budget, which is in §3.

Two changes, neither of which the spec's default configuration includes, are
what make `k = 6` finish at all:

| change | effect at `k = 6` |
|---|---|
| `--propagator matching` | 204,087,009 conflicts in 900 s without terminating → 243,410 conflicts total. **≥2,900× fewer conflicts**, and max depth 79 → 22. |
| `--symmetry orbit` | > 900 s → 56 s. Roughly **10×**. |
| `--branch-order link --link-level 2` | 243,410 → 70,572 conflicts, and ~2.4× wall. |

Combined, `k = 6` goes from "does not finish in 15 minutes" to **22.7 s**.

---

## 2. Rung status

Configuration: `--symmetry orbit --propagator matching --branch-order link
--link-level 2 --anchors 0`. Serial, nothing else running on the machine.

### Partitions (`solve`)

| k | \|V\| | expected | outcome | wall | conflicts | decisions | high-water | depth max | peak state |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 3 | SAT | **SAT** | 0.56 s | 0 | 0 | 3 / 3 | 1 | 0.6 MiB |
| 4 | 35 | UNSAT | **UNSAT** | 0.02 s | 6 | 2 | 25 / 35 | 2 | 0.6 MiB |
| 6 | 462 | UNSAT | **UNSAT** | **22.7 s** | 70,572 | 132,273 | 213 / 462 | 17 | 3.3 MiB |
| 8 | 6,435 | UNSAT | UNKNOWN | >300 s | 350,353 | 675,583 | 261 / 6,435 | 78 | 1.4 MiB |
| 10 | 92,378 | UNSAT | UNKNOWN | >300 s | 150,656 | 283,391 | 653 / 92,378 | 237 | 4.7 MiB |
| 12 | 1,352,078 | UNSAT | UNKNOWN | >300 s | 66,602 | 133,375 | 686 / 1,352,078 | 285 | 11.1 MiB |
| 14 | 20,058,300 | UNSAT | UNKNOWN | >181 s | 15,662 | 31,743 | 954 / 20,058,300 | 470 | 124.8 MiB |
| 16 | 300,540,195 | unknown | UNKNOWN | >182 s | 7,854 | 16,383 | 1,367 / 300,540,195 | 748 | **1,797 MiB** |

The `k = 2` SAT witness was written to disk and re-read and verified by the
independent checker before success was reported, as were both `code` witnesses.

For contrast, the CLI defaults (`--symmetry color --propagator count
--branch-order mrv --anchors 16`) at `k = 6`: **UNKNOWN** after 180 s and
47,825,644 conflicts, high-water 128 of 462. The tuned configuration proves the
same instance in 22.7 s and 70,572 conflicts.

### Single perfect 1-codes (`code`)

| k | \|V\| | m | expected | outcome | wall | conflicts | high-water |
|---|---|---|---|---|---|---|---|
| 4 | 35 | 7 | SAT | **SAT** | 0.04 s | 0 | 35 / 35 |
| 6 | 462 | 66 | SAT | **SAT** | 0.15 s | 8 | 462 / 462 |
| 8 | 6,435 | 715 | UNSAT | UNKNOWN | >180 s | 2,511,960 | 3,135 / 6,435 |
| 10 | 92,378 | 8,398 | UNSAT | UNKNOWN | >180 s | 1,028,536 | 11,060 / 92,378 |

`k = 4` recovers a Fano-equivalent 7-block code and `k = 6` a Witt-equivalent
66-block code, both verified independently. Both polarities of the oracle are
therefore demonstrated on the SAT side; the UNSAT side (`k = 8, 10`) is not
reached.

### Divisibility, and what it means for k = 8 and k = 14

`N_j` and `M_j` are counts of blocks, so they must be integers. They are not, at
exactly two values of `k` in range:

| k | first non-integral term |
|---|---|
| 8 | `N_3 = 896/3`, `M_3 = 1064/3` |
| 14 | `N_3 = 25480/3`, `M_3 = 26572/3` |

So no Steiner system `S(k-1,k,2k)` exists at `k = 8` or `k = 14`, hence no
perfect 1-code in `O_8` or `O_14` and no partition. `odd835 info -k 8` and
`-k 14` print this. The spec attributes an "arithmetic reason" to `k = 14` only
and warns that a blind search there may take effectively forever; the same
argument applies verbatim to `k = 8`, which explains why `k = 8` — only 6,435
vertices, one rung above a rung that closes in 23 s — is so much harder than its
size suggests. The engine does not short-circuit on it: the spec asks for a
search, so the search runs.

---

## 3. Ablation

Wall times in this section were measured with **8 runs in parallel** on 32
cores, so they are consistent with each other but inflated relative to §2.
Conflicts, high-water and depth are unaffected by that.

For rungs that do not terminate, "conflicts" is not a quality measure — a
variant that explores a worse part of the tree faster looks better on it. The
useful column there is **high-water** (deepest assignment count reached), which
is the spec's own progress metric.

### 3.1 k = 6 — time to a proven answer

| variant | outcome | wall | conflicts | depth max |
|---|---|---|---|---|
| `link t=2, anchors=0` | UNSAT | **28.6 s** | **70,572** | 17 |
| `link t=2, anchors=0, --no-cardinality` | UNSAT | 28.7 s | 70,572 | 17 |
| `link t=2` (anchors=16) | UNSAT | 31.2 s | 70,572 | 17 |
| `link t=4` | UNSAT | 41.1 s | 189,148 | 21 |
| `link t=3` | UNSAT | 44.9 s | 116,387 | 20 |
| `anchors=0` (mrv) | UNSAT | 61.4 s | 243,410 | 22 |
| `anchors=4` (mrv) | UNSAT | 63.4 s | 243,410 | 22 |
| baseline `anchors=16` (mrv) | UNSAT | 68.2 s | 243,410 | 22 |
| `--no-cardinality` (mrv) | UNSAT | 68.0 s | 243,410 | 22 |
| `--anchor-reach` (mrv) | UNSAT | 68.2 s | 243,410 | 22 |
| `anchors=64` (mrv) | UNSAT | 69.8 s | 243,410 | 22 |
| `link t=1` | UNSAT | 220.8 s | 793,917 | 22 |
| `symmetry=color`, `link t=2` | UNKNOWN | >900 s | 2,647,517 | 24 |
| `symmetry=color` (mrv) | UNKNOWN | >900 s | 3,842,517 | 24 |
| `symmetry=none` (mrv) | UNKNOWN | >900 s | 4,286,972 | 30 |
| `propagator=count` | UNKNOWN | >900 s | **204,087,009** | 79 |

Read this table top down and the ordering of what matters is unambiguous:

1. **The matching propagator is not optional.** Counting alone burns 204 million
   conflicts in 900 s and is still nowhere near done, at nearly four times the
   depth. It is ~55× slower per conflict and still wins by a factor of thousands.
2. **The orbit symmetry reduction is worth ~10×**, and its absence is what
   `symmetry=color` and `symmetry=none` cost.
3. **`link t=2` branching is worth ~2.4×** and 3.4× in conflicts. `t=1` is much
   worse than MRV — expected, since a level-1 region is exactly what Rule B
   already saturates (see ARCHITECTURE.md §6), so it is a bad variable order with
   no compensating inference. `t=3` and `t=4` are worse than `t=2`: bigger
   regions dilute the concentration effect.
4. **Rules C, D and E contribute nothing measurable.** `anchors` 0/4/16/64,
   `--no-cardinality` and `--anchor-reach` all produce *the identical conflict
   count*, 243,410. They are not changing the search at all, only its cost.

### 3.2 Rule attribution

The spec's tuning criterion is explicit: under 1% of conflicts and `--anchors`
should drop to 0. Measured share of conflicts by rule, at the tuned
configuration:

| rung | A | B | C | D | E | matching |
|---|---|---|---|---|---|---|
| k=6 | 4% | 94% | 0% | 0% | 0.1% | 1% |
| k=8 | 6% | 93% | 0% | 0% | 0% | <1% |
| k=10 | 9% | 89% | 0% | 0% | 0% | <1% |
| k=12 | 11% | 86% | 0% | 0% | 0% | 1% |

Rule B does essentially all the work. Rule E is the only one of D/E that ever
fires — at `k = 4` it produces *every* conflict in the search — but by `k = 6` it
is down to 0.1% and by `k = 8` it is gone. Rule C never fires at all, which is
consistent with it being strictly implied: if every closed neighbourhood is
rainbow then each class is a perfect 1-code and its size is forced.

**Conclusion: `--anchors 0`.** The anchor machinery costs an `A·(k+1)` popcount
sweep per assignment plus an assignment-stack scan per anchor creation, and buys
nothing above `k = 4`.

### 3.3 k = 8, 10, 12 — progress inside 120 s

Ordered by high-water, the metric that actually reflects penetration.

| k | variant | high-water | / \|V\| | conflicts | depth max |
|---|---|---|---|---|---|
| 8 | `link t=1` | 260 | 6,435 | 159,018 | 128 |
| 8 | `link t=2` | 256 | 6,435 | 104,886 | 77 |
| 8 | baseline (mrv) | 250 | 6,435 | 73,209 | 77 |
| 8 | `symmetry=color` | 141 | 6,435 | 163,459 | 50 |
| 8 | `propagator=count` | 146 | 6,435 | 12,615,192 | 107 |
| 10 | `link t=2` | **653** | 92,378 | 43,471 | 237 |
| 10 | `color`, `link t=2` | 611 | 92,378 | 41,009 | 225 |
| 10 | baseline (mrv) | 292 | 92,378 | 33,952 | 111 |
| 10 | `link t=3` | 227 | 92,378 | 30,080 | 80 |
| 10 | `propagator=count` | 119 | 92,378 | 5,220,196 | 82 |
| 12 | `link t=1` | **896** | 1,352,078 | 14,853 | 439 |
| 12 | `link t=2` | 686 | 1,352,078 | 18,068 | 285 |
| 12 | baseline (mrv) | 421 | 1,352,078 | 14,302 | 200 |
| 12 | `link t=3` | 339 | 1,352,078 | 11,139 | 148 |
| 12 | `propagator=count` | 76 | 1,352,078 | 2,685,424 | 45 |

Link branching penetrates 1.6–2.1× further than MRV at `k = 10` and `k = 12`,
which is the spec's stated condition for making it the default. Note the
high-water numbers in absolute terms: 686 of 1,352,078 vertices at `k = 12` is
0.05%. The search is not close.

---

## 4. Recommended configuration

```
odd835 solve -k K \
    --symmetry orbit \
    --propagator matching \
    --branch-order link --link-level 2 \
    --anchors 0
```

Justification, in order of measured impact: matching ≥2,900× (§3.1), orbit ~10×
(§3.1), link `t=2` ~2.4× (§3.1), anchors 0 because Rules D/E contribute 0% of
conflicts above `k = 4` and cost a per-assignment sweep (§3.2). `--cardinality`
may be left on; it is free and measurably inert.

The CLI defaults are the ones the build spec names, not these. `odd835 --help`
prints the recommendation.

### Memory at scale

Measured solver state (the engine's own accounting: `color + dom + sat_count +
trail + assign stack + MRV heaps + queue bitsets`):

| k | \|V\| | measured | spec estimate (`color + dom`) |
|---|---|---|---|
| 6 | 462 | 3.3 MiB | — |
| 10 | 92,378 | 4.7 MiB | 0.5 MiB |
| 12 | 1,352,078 | 11.1 MiB | 6.5 MiB |
| 14 | 20,058,300 | 124.8 MiB | 95.6 MiB |
| 16 | 300,540,195 | **1,797 MiB** | 1,434 MiB |

`k = 16` fits in **1.8 GiB of solver state**, comfortably inside the spec's
8 GiB target. The gap to the spec's estimate is the `sat_count` array (one byte
per vertex, 287 MiB at `k = 16`) that backs the `saturated` metric, plus the two
propagation-queue bitsets (37 MiB each). The engine allocates, builds its rank
tables, runs, and reports at `k = 16` — it reached depth 748 and assigned 1,367
vertices in 182 s. Scale is not the binding constraint; search is.

One memory bug worth recording because it only shows up under link branching:
the MRV min-heaps are pushed to on *undo* as well as on domain narrowing, so they
grow with total work rather than live state. `select_mrv` sweeps them, but
link-ordered branching never calls it. That leaked 147 MiB at `k = 6`, where the
live state is 5 MiB — and would have been fatal at `k = 16`. `select_link` now
sweeps too.

---

## 5. Verification status

| gate | status |
|---|---|
| M1 combinatorics core | pass — `rank-roundtrip`, `degree`, `symmetry` for `k ≤ 12`; `info` matches the spec constants table exactly at all eight `k` |
| M2 independent checker | pass — Fano and Witt both validate as perfect 1-codes; checker neighbours cross-checked against brute-force pairwise disjointness for `k ≤ 8` |
| M3 solver, small | pass through `k = 6`, both polarities; every SAT round-trips through `check`. **`k = 8` not reached.** |
| M4 observability | pass — every §8 counter present in JSONL; human display repaints; `SIGINT`/`SIGUSR1` behind the `signals` feature (Unix) |
| M4.5 structural propagators | pass — 13 rule/flag variants agree at `k = 2, 4`; `orbit` and `color` agree at `k = 2, 4, 6` |
| M5 scale | **partial** — `k = 10` and `k = 12` do not terminate; ablation delivered above |
| M6 endurance | pass — `k = 6` killed at four different points, each resume reaches a bit-identical result (243,410 conflicts / 461,246 decisions) |

Two bugs found late that are worth recording, because both were silent:
`--link-level t ≥ k` underflowed `k - t` and hung (release builds wrap rather
than panic), and the code solver's `saturated` counter was never decremented on
undo, reporting 201,954,243 covered neighbourhoods out of 6,435.

### Test suite

`cargo test --release`: **32 unit tests + 19 integration tests, all passing**,
~150 s. One further test is `#[ignore]`d — the `k = 6` orbit-vs-colour
comparison, whose colour-breaking arm takes tens of minutes; it has been run
separately and passes (both arms UNSAT).

The property that matters most has its own test: `no_false_unsat_under_a_limit`
drives `k = 6, 8, 10` under a 50-conflict cap and a 1 s timeout and asserts every
one exits UNKNOWN (2), never UNSAT.

`odd835 oracle --quick` runs 14 entries and all agree. A full `odd835 oracle`
run reports `part-k8` and above as UNKNOWN, i.e. as disagreements with the
spec's expected UNSAT, and exits non-zero — which is the correct behaviour for a
gate the engine does not clear.

### Rung checks

Exercised at `k = 6`, `t = 2`: **14 regions completed, 14 passed, 0 failed**
under `--branch-order link`; 1 completed out of 448 sampled under MRV, which is
the behaviour the spec predicts for MRV. Zero failures is expected rather than
lucky — ARCHITECTURE.md §6 shows the level-`t` large-set condition decomposes
into level-1 conditions that Rule B already enforces, so the rung check is a bug
detector, not a propagator.

---

## 6. What would move the needle

Stated plainly, because the ablation says the current engine has run out of the
easy factors:

1. **Conflict-driven backjumping or clause learning.** The spec excludes it from
   v1, and it is now clearly the dominant missing piece. Depth-max at `k = 12` is
   439 with a high-water of 896: the search reaches deep, fails, and backtracks
   chronologically to a recent and usually irrelevant decision, re-deriving the
   same contradiction. Every other lever measured here is worth 2–10×; this one
   addresses the actual failure mode.
2. **Consuming the rest of the automorphism group.** `--symmetry orbit` removes
   the `S(C_0)` factor (`k!` → `p(k)`, i.e. 479,001,600 → 77 at `k = 12`) and is
   worth ~10× on its own. `S(λ') ≅ S_{k-2}` and the centraliser of `h` remain —
   another `(k-2)!` at worst. Canonical augmentation would consume it, at
   considerable risk of exactly the false-UNSAT failure this project cannot
   survive.
3. **A stronger-than-neighbourhood propagator.** Régin filtering is already
   exact *per closed neighbourhood*; the next step would be reasoning across
   overlapping neighbourhoods, which is where the remaining structure lives.

Nothing in the measurements suggests `k = 16` is reachable by scaling the
current approach. `k = 12` alone is roughly `10^3` times more vertices than `k = 6`
(and vastly more than that in search space), and `k = 6` already takes 22.7 s
with all three multipliers applied.
