# Build spec: `odd835` — a finite search engine for Erdős Problem #835

You are building a standalone Rust CLI tool. Read this entire document before writing code. The
mathematics section is normative — if your implementation disagrees with it, your implementation is
wrong. Do not improvise the combinatorics.

---

## 1. What the tool decides

For an even integer `k`, decide whether the **odd graph** `O_k` admits a partition of its vertex set
into `k+1` perfect 1-codes. Equivalently, whether there is a `(k+1)`-coloring of `O_k` in which every
closed neighborhood is rainbow.

This is exactly equivalent to Erdős Problem #835 at `k`: whether the Johnson graph `J(2k,k)` has
chromatic number `k+1`. You do not need to understand why; you need to implement `O_k` correctly.

### Definitions (normative)

Let `n = 2k - 1` and let the ground set be `[n] = {0, 1, ..., n-1}`.

- **Vertices** of `O_k` are the `(k-1)`-subsets of `[n]`. There are `C(2k-1, k-1)` of them.
- **Adjacency**: `T ~ U` if and only if `T ∩ U = ∅`.
- **Degree**: every vertex has exactly `k` neighbors. If `T` is a vertex, its complement
  `[n] \ T` has size `k`, and the neighbors of `T` are precisely the `k` subsets obtained by
  deleting one element from that complement.
- **Closed neighborhood** `N[T] = {T} ∪ N(T)` has exactly `k+1` vertices.
- **The constraint**: assign each vertex one of `k+1` colors so that for every vertex `T`, the
  `k+1` vertices of `N[T]` carry `k+1` distinct colors.

Because `|N[T]| = k+1` equals the number of colors, this is a *permutation* constraint, not a
mere all-different constraint. Every color appears exactly once in every closed neighborhood.

**The number of colors is always exactly `k+1`. Do not expose it as an option.** With any other
number of colors the problem is a different, weaker problem that says nothing about #835.

### The structure theorem (proven — this is why the tool is shaped the way it is)

A `(k+1)`-coloring of `J(2k,k)` has color classes that are exactly Steiner systems `S(k-1,k,2k)`.
For any such design and any block `B`, inclusion–exclusion over the points of `B` gives the number
of blocks disjoint from `B`:

```
N_0(B) = (1 + k·(-1)^k) / (k+1)
```

Two consequences, both used by this tool:

1. **Odd `k` is impossible.** For odd `k > 1` the expression is negative. The tool must reject odd
   `k` at argument-parse time with an explanatory message, not attempt a search.
2. **Complement closure.** For even `k` the value is exactly 1, and the only `k`-subset disjoint
   from `B` is `B^c`, so `B ∈ 𝓑 ⟹ B^c ∈ 𝓑`. Every color class is closed under complementation.

Consequence 2 is the entire reason this tool searches `O_k` rather than `J(2k,k)` directly. Blocks
come in complementary pairs carrying the same color, so the `C(2k,k)` vertices of `J(2k,k)` collapse
to `C(2k-1,k-1)` — at `k=16` that is 300,540,195 instead of 601,080,390. **The 2× reduction is not
a heuristic or an approximation; it is exact and it is theorem-backed.** Do not "generalize" the
tool to `J(2k,k)` or to odd `k`.

The same computation yields the full block intersection distribution, which §3 turns into
propagators. For a fixed block `B` in class `i`, the number of blocks meeting it in exactly `j`
points is, exactly:

```
N_j = C(k,j) · ( C(k,j) + (-1)^(k+j)·k ) / (k+1)      same class
M_j = C(k,j) · ( C(k,j) - (-1)^(k+j)   ) / (k+1)      any other class
```

Both sum to `Cat(k) = C(2k,k)/(k+1)` over `j = 0..k`. These are equalities, not bounds.

### Translating to `O_k`

The propagators in §3 need these in `O_k` coordinates. Fix `∞ = 2k-1` and let `V = [2k-1]`. An
`O_k` vertex `T` corresponds to the complementary block pair `{T ∪ {∞}, V \ T}`. For two distinct
vertices `T, T'` with `a = |T ∩ T'|`, the four induced block intersections have sizes `a+1` (twice)
and `k-1-a` (twice). So if

```
c_a = #{ T' in the same class as T, T' ≠ T : |T ∩ T'| = a }        a = 0 .. k-2
d_a = #{ T'' in one specific other class   : |T ∩ T''| = a }        a = 0 .. k-2
```

then the theorem forces, **exactly**, for every `a`:

```
c_a + c_{k-2-a} = N_{a+1}
d_a + d_{k-2-a} = M_{a+1}
```

Derive these in code from `N_j`/`M_j`; do not hardcode them.

### Derived constants

Perfect code size `m = C(2k-1, k-1) / (k+1)`. This is always an exact integer for even `k`.

| k | \|V(O_k)\| | colors | m | `color: Vec<u8>` | `dom: Vec<u32>` |
|---|---|---|---|---|---|
| 2 | 3 | 3 | 1 | — | — |
| 4 | 35 | 5 | 7 | — | — |
| 6 | 462 | 7 | 66 | — | — |
| 8 | 6,435 | 9 | 715 | — | — |
| 10 | 92,378 | 11 | 8,398 | 0.1 MiB | 0.4 MiB |
| 12 | 1,352,078 | 13 | 104,006 | 1.3 MiB | 5.2 MiB |
| 14 | 20,058,300 | 15 | 1,337,220 | 19.1 MiB | 76.5 MiB |
| 16 | 300,540,195 | 17 | 17,678,835 | 286.6 MiB | 1.1 GiB |

`k = 16` is the target. Everything below it is a calibration rung with a known answer.

---

## 2. Representation

### Vertex encoding

Since `2k-1 ≤ 31` for all `k ≤ 16`, a `(k-1)`-subset of `[2k-1]` fits in a `u32` bitmask. Use
bitmasks everywhere in the hot path.

Index vertices by **colex rank**:

```
rank({s_0 < s_1 < ... < s_{k-2}}) = Σ_{i=0}^{k-2} C(s_i, i+1)
```

This is a bijection onto `[0, C(2k-1, k-1))`. Unrank greedily from the top index down. Precompute a
binomial table `C[n][r]` for `n ≤ 31`, `r ≤ 16` as `u64` at startup.

Provide and test both directions:

```rust
fn rank(mask: u32) -> u32;
fn unrank(idx: u32) -> u32;   // returns a bitmask
```

`u32` indices suffice: the largest count is 300,540,195 < 2^32.

### Neighbor enumeration

Do **not** build an adjacency list. At `k=16` that would be 4.8 billion entries. Compute neighbors
on demand:

```rust
// complement of `mask` within [2k-1] has exactly k bits set;
// clearing each of those bits in turn gives the k neighbors
fn neighbors(mask: u32, n: u32) -> impl Iterator<Item = u32>
```

Neighbor enumeration is the single hottest operation in the program. Make it branch-free where
possible (iterate set bits of the complement with `trailing_zeros` and `x & (x-1)`).

### Search state

```rust
color: Vec<u8>       // 0..=k, or U8_UNASSIGNED = 0xFF
dom:   Vec<u32>      // bitmask of still-permitted colors, bits 0..=k
trail: Vec<(u32 /*vertex index*/, u32 /*previous dom*/)>
levels: Vec<usize>   // trail offsets marking decision levels
assigned: usize
```

Undo is: pop trail entries back to the recorded offset, restoring `dom` and clearing `color`. O(1)
per entry.

---

## 3. Propagation

Maintain a queue of vertices whose domain has changed. Run to fixpoint.

**Rule A — assignment.** When vertex `v` is assigned color `c`: set `color[v] = c`,
`dom[v] = 1 << c`, and for each `u ∈ N(v)` clear bit `c` from `dom[u]`. If any `dom[u]` becomes
empty → conflict. If any `dom[u]` becomes a singleton → enqueue as a forced assignment.

**Rule B — closed-neighborhood counting.** When `dom[v]` changes, for each of the `k+1` closed
neighborhoods containing `v` (namely `N[v]` and `N[u]` for each `u ∈ N(v)`), and for each color
`c`, count how many members of that neighborhood still permit `c`:

- count 0 and no member already colored `c` → conflict
- count 1 and no member already colored `c` → force that member to `c`
- a color appearing on two assigned members → conflict

Rule B is what makes this tractable; Rule A alone is far too weak. Each application touches
`(k+1)^2 = 289` vertices at `k=16` — cheap, and it is where nearly all inference comes from.

**Rule C — class cardinality.** Every class must end at exactly `m`. Maintain, per color `i`,
`size[i]` (assigned) and `avail[i]` (unassigned vertices whose domain still permits `i`).
`avail[i]` is decremented in O(1) whenever bit `i` is cleared from an unassigned vertex's domain.
Then:

- `size[i] > m` → conflict
- `size[i] + avail[i] < m` → conflict
- `size[i] == m` → color `i` is closed; strike it from remaining domains lazily (keep a
  `closed: u32` bitmask and mask it in at domain-read time rather than touching 300M vectors)

Cheap, obviously correct, and not implied by Rules A or B.

**Rule D — same-class intersection counts.** Designate the first `A` vertices assigned to each
class as *anchors*. For each anchor `T` maintain `c_a(T)` as defined in §1. On assigning `T'` to
`T`'s class, compute `a = popcount(T & T')` and increment. Then:

- `c_a + c_{k-2-a} > N_{a+1}` → conflict
- when class `i` is near completion, `c_a + c_{k-2-a}` plus the count of still-eligible vertices
  at those two intersection sizes `< N_{a+1}` → conflict (the reachability direction; more
  expensive, gate it behind `--anchor-reach`)

**Rule E — cross-class intersection counts.** Same mechanism with `d_a` against anchors of every
*other* class, target `M_{a+1}`. This is the more important of the two: §10 requires growing all
`k+1` classes simultaneously, and Rule E is the only mechanism in the engine that actually couples
them. Without it that instruction is a principle with nothing behind it.

**Skip `a ∈ {0, k-2}` in Rules D and E.** Those two cases are already implied by Rule B —
`c_0 = c_{k-2} = 0` because same-class vertices are non-adjacent and any two vertices at
intersection `k-2` share a unique common neighbor; and `d_0 = 1`, `d_{k-2} = k-1` follow from
the closed neighborhoods `N[U_y]`. Checking them costs time and can never fire. The inference
lives at `1 ≤ a ≤ k-3`, which corresponds to vertex pairs too far apart for local propagation to
reach. Assert the skipped cases once in the test suite, then never again at runtime.

Cost: `A·(k+1)` popcounts per assignment. At `A = 16`, `k = 16` that is 272, against the 289
vertices Rule B already touches — roughly a 2× hot-loop cost. `A` is a tuning parameter
(`--anchors`, default 16); measure the tradeoff on the `k = 10` and `k = 12` rungs before
committing to a value for `k = 16`.

**Optional stronger propagator** (`--propagator matching`, build it second): each closed
neighborhood is a perfect matching constraint between `k+1` vertices and `k+1` colors, so a
Hall-violator / Régin-style filtering pass prunes strictly more than counting. Implement counting
first, get it correct, then add matching behind a flag and verify both agree on all oracles.

**What will not work, so you don't try.** The equitable-partition and Delsarte conditions on the
color partition have been checked and are automatically satisfied for every `k` — they are global
spectral statements that cannot be maintained incrementally against a partial assignment, and they
carry no information even when complete. Likewise `(A+I)x_i = 1` is the rainbow constraint
rewritten and has no independent content. Record both in `ARCHITECTURE.md` as considered and
rejected.

---

## 4. Search

Chronological backtracking DPLL. No clause learning in v1.

- **Variable order**: minimum remaining values (fewest bits in `dom`), ties broken by lowest vertex
  index for determinism.
- **Value order**: lowest permitted color first.
- **Restarts**: optional, off by default; if added they must not compromise completeness.

### Link-ordered branching (`--branch-order link`)

Pure MRV will never assemble a complete *link*, which makes the rung checks in §5 dead weight —
they can only fire on regions that happen to be fully assigned, and MRV scatters assignments.
Branch deliberately instead.

For a level `t` and a `(k-t)`-subset `λ ⊂ [2k]`, the `k`-sets `λ ∪ B` for `B ∈ binom([2k]\λ, t)`
map to `C(k+t, t)` distinct `O_k` vertices (distinct because `λ ≠ ∅` rules out complementary
collisions). The theorem forces the colors on that region to form a large set `LS(t-1, t, k+t)`.

At `k = 16` a `t = 2` link is 153 vertices and a `t = 3` link is 969 — small enough to saturate
deliberately. Choose `λ`, drive the search to complete its link region, verify the induced large
set, then move to an overlapping `λ'`. Completing a link forces a globally rigid substructure and
cascades hard through Rules B–E. This is what converts the tower from an assertion into a
propagator, and it is the only branching mode under which `--rung-check` is worth running.

Keep `mrv` as the default until `link` is measured to beat it on the `k = 10` and `k = 12` rungs.

### Symmetry breaking (root level, mandatory)

The `(k+1)!` color symmetry can be consumed entirely and safely:

1. Pick the seed vertex `v0 = unrank(0)`.
2. Assign `color[v0] = 0`.
3. Assign the `k` neighbors of `v0`, in increasing vertex-index order, the colors `1, 2, ..., k`.

This is without loss of generality: in any solution the `k+1` members of `N[v0]` carry distinct
colors, so a permutation of color labels puts them in this configuration. Applying it is complete —
it removes solutions only up to relabeling.

Do not add lexicographic symmetry-breaking constraints beyond this without a written correctness
argument. Getting symmetry breaking wrong turns a SAT instance into a false UNSAT, which is the
worst possible failure mode for this project.

### Termination semantics

Three outcomes, and they must never be conflated:

| outcome | meaning | exit code |
|---|---|---|
| `SAT` | a full valid coloring was found and written out | 0 |
| `UNSAT` | the search space was exhausted | 1 |
| `UNKNOWN` | timeout, conflict limit, memory limit, or interrupt | 2 |
| `ERROR` | internal assertion failure or bad input | 3 |

**Never print `UNSAT` because a limit was reached.** A timeout is `UNKNOWN`. This rule is
non-negotiable; the whole point of the tool is that its `UNSAT` can be trusted.

On `SAT`, write the coloring to disk and then re-verify it with the independent checker (§6)
before reporting success.

---

## 5. CLI

```
odd835 <SUBCOMMAND>

  info    -k <K>                        print derived constants and exit
  solve   -k <K> [OPTIONS]              search for a (K+1)-coloring of O_K
  code    -k <K> [OPTIONS]              search for a single perfect 1-code in O_K
  check   -k <K> --witness <FILE>       independently verify a claimed coloring or code
  oracle  [--only <NAME>]               run the known-answer test suite
  bench   -k <K>                        propagator and neighbor-enumeration microbenchmarks
```

### `solve` / `code` options

```
  -k, --k <K>                     even integer, 2..=16 (required)
      --timeout <DURATION>        e.g. 30s, 45m, 12h, 7d
      --max-conflicts <N>
      --seed <N>                  RNG seed; default 0 (fully deterministic)
      --symmetry <MODE>           none | color        [default: color]
      --propagator <MODE>         count | matching    [default: count]
      --cardinality               enable Rule C       [default: on; --no-cardinality to disable]
      --anchors <A>               anchors per class for Rules D/E, 0 disables  [default: 16]
      --anchor-reach              also enforce the D/E reachability direction  [default: off]
      --branch-order <MODE>       mrv | link          [default: mrv]
      --link-level <T>            t for link branching                [default: 3]
      --rung-check <LEVELS>       comma-separated t values, e.g. 2,3,4
      --rung-sample <N>           links to sample per check pass  [default: 64]
      --rung-interval <DURATION>  how often to run a rung pass    [default: 60s]
      --stats-interval <DURATION> [default: 5s]
      --stats-format <FMT>        human | json | jsonl  [default: human]
      --stats-file <PATH>         write jsonl telemetry here in addition to stdout
      --checkpoint <PATH>
      --checkpoint-interval <DURATION>
      --resume <PATH>
      --witness-out <PATH>        where to write a solution on SAT
      --conflict-log <PATH>       replayable trace for independent UNSAT auditing
      --threads <N>               [default: 1]
  -v, --verbose                   repeatable
```

`--threads` may be a no-op in v1. Do not build parallelism before single-threaded correctness and
the `k=12` rung are done.

---

## 6. Independent checker

`check` must share **no code** with the solver beyond `rank`/`unrank`. Write it separately, from the
definitions in §1. Given a witness file it verifies:

1. every vertex has exactly one color in `0..=k`
2. every vertex has exactly `k` neighbors
3. every closed neighborhood contains each color exactly once
4. every color class has size exactly `m`
5. each color class is a perfect 1-code: every vertex is at distance ≤ 1 from exactly one member

If the solver and the checker ever disagree, that is a `SEV-1` bug — stop and fix it before running
anything larger.

---

## 7. Oracle suite (`odd835 oracle`)

This is the acceptance gate. Every entry has a known answer. Report a table of pass/fail plus wall
time per entry, and exit non-zero if any entry disagrees.

### Structural oracles

| name | assertion |
|---|---|
| `rank-roundtrip` | `unrank(rank(S)) == S` for all vertices, `k ≤ 12` |
| `degree` | every vertex has exactly `k` neighbors, `k ≤ 12` |
| `symmetry` | `u ∈ N(v)` ⟺ `v ∈ N(u)`, `k ≤ 10` |
| `fano` | the 7 lines of the Fano plane form a perfect 1-code in `O_4` |
| `witt` | the 66 blocks of `S(4,5,11)` form a perfect 1-code in `O_6` |

For `fano` and `witt`, hardcode the designs as literal data in the test file. Do not generate them.

### Single-code oracles (`code` mode)

| k | expected | why |
|---|---|---|
| 4 | SAT | the Fano plane |
| 6 | SAT | the Witt design `S(4,5,11)` |
| 8 | UNSAT | requires `S(6,7,15)`, which fails divisibility |
| 10 | UNSAT | requires `S(8,9,19)`, whose derived `S(4,5,15)` does not exist |

Both polarities matter. An engine that returns UNSAT for everything passes half a suite and is
worthless.

### Partition oracles (`solve` mode)

| k | \|V\| | expected | notes |
|---|---|---|---|
| 2 | 3 | **SAT** | positive control, must be instant |
| 4 | 35 | UNSAT | instant |
| 6 | 462 | UNSAT | instant |
| 8 | 6,435 | UNSAT | seconds |
| 10 | 92,378 | UNSAT | minutes at most |
| 12 | 1,352,078 | UNSAT | **the gate** — report wall time prominently |
| 14 | 20,058,300 | UNSAT | see warning below |
| 16 | 300,540,195 | unknown | the actual target |

**Warning about `k = 14`.** It is UNSAT, but for an arithmetic reason (`k+1 = 15` is composite) that
the search cannot perceive. A blind search may take effectively forever. Use `k=14` as a throughput
and memory scaling measurement, not as a termination test. Do not treat a `k=14` timeout as a
defect.

### Intersection-distribution oracles

Rules D and E are only as good as the targets they enforce, so test the targets directly. A
completed class at `k = 16` takes 17,678,835 assignments, so a check that only fires on completion
is useless — these must be unit tests against known data.

`k = 10`, per class of 16,796 blocks:

| j | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| N_j | 1 | 0 | 225 | 1,200 | 4,200 | 5,544 | 4,200 | 1,200 | 225 | 0 | 1 |
| M_j | 0 | 10 | 180 | 1,320 | 3,990 | 5,796 | 3,990 | 1,320 | 180 | 10 | 0 |

`k = 16`, per class of 35,357,670 blocks — the Rule D / Rule E targets, as `c_a + c_{k-2-a}`:

| a | 0+14 | 1+13 | 2+12 | 3+11 | 4+10 | 5+9 | 6+8 | 7+7 |
|---|---|---|---|---|---|---|---|---|
| N_{a+1} | 0 | 960 | 17,920 | 196,560 | 1,118,208 | 3,779,776 | 7,687,680 | 9,755,460 |
| M_{a+1} | 16 | 840 | 18,480 | 194,740 | 1,122,576 | 3,771,768 | 7,699,120 | 9,742,590 |

Required tests:

- `Σ_j N_j == Σ_j M_j == Cat(k)` for all even `k ≤ 16`
- `N_0 = N_k = 1`, `N_1 = N_{k-1} = 0`, `M_0 = M_k = 0`, `M_1 = k`
- the generated tables match the two above, exactly
- **ground truth**: compute the actual distribution of the Fano perfect code in `O_4` and the Witt
  code in `O_6` by brute force and check it against the formula. These are the only two cases where
  a real design exists to test against — use them.
- the skipped cases: verify by exhaustive search at `k ≤ 8` that `c_0 = c_{k-2} = 0` and
  `d_0 = 1`, `d_{k-2} = k-1` hold in every valid partial coloring Rule B admits, confirming they
  are redundant at runtime

Also retain a `--verify-classes` flag that runs the full distribution check on any class that does
complete, and always run it before writing a witness on `SAT`.

---

## 8. Observability

This is a first-class requirement, not decoration. A run may last weeks; the operator must be able
to tell at a glance whether it is making progress or stalled.

### Counters to maintain

**Coverage ("targets hit")**

- `assigned` — vertices with a color, and percentage of `|V|`
- `assigned_high_water` — deepest assignment count ever reached, and the timestamp
- `saturated` — closed neighborhoods that are fully assigned and rainbow, and percentage of `|V|`.
  **This is the primary "targets hit" metric**: there are exactly `|V|` closed neighborhoods, and
  a solution saturates all of them.
- `classes_closed` — color classes that have reached size `m` and passed the `N_j` check, out of
  `k+1`

**Search**

- `decisions`, `propagations`, `conflicts`, `backtracks`, `restarts`
- `depth_current`, `depth_max`
- rates: conflicts/sec, propagations/sec, decisions/sec (windowed over the last interval, not
  cumulative averages)

**Domains**

- `dom_total` — Σ popcount(dom) over unassigned vertices
- `dom_mean`, `dom_singletons`

**Propagator attribution** — conflicts and forced assignments broken out by which rule produced
them: `rule_a`, `rule_b`, `rule_c`, `rule_d`, `rule_e`, `matching`. This is the most important
diagnostic in the tool. If Rules D and E are contributing under 1% of conflicts they are not paying
for their hot-loop cost and `--anchors` should drop to 0; if they are contributing 20%+, raise it.
You cannot tune the anchor count without this breakdown, so build it in from the start rather than
bolting it on.

**Rungs** — per configured level `t`: links checked, links passed, links failed, and links
*completed* (fully assigned, which is what makes a check possible at all). A failed link is a
global contradiction; log it loudly with the offending `λ`. Under `--branch-order mrv` expect
`completed` to stay at zero — that is the expected behavior, not a bug.

**Health**

- `stall` — time since `assigned_high_water` last advanced. The single most useful number on the
  display.
- `rss_bytes`, `elapsed`, `cpu_time`
- `checkpoint_last`, `checkpoint_next`

### Human display

Repaint in place every `--stats-interval`:

```
odd835  k=16  |V|=300,540,195  colors=17  m=17,678,835      elapsed 2:14:07
──────────────────────────────────────────────────────────────────────────
assigned        142,883,201 / 300,540,195   47.5%   high-water 149,201,334
saturated  ►     98,441,002 / 300,540,195   32.8%
classes closed            0 / 17
domains         Σ 1.84e9   mean 3.41   singletons 12,004,551
──────────────────────────────────────────────────────────────────────────
decisions         4,120,883      conflicts        3,998,201
propagations         8.4e11      backtracks       3,998,188
depth              cur 1,204     max 1,881
rate            12.4k conf/s     2.1M prop/s
──────────────────────────────────────────────────────────────────────────
conflicts by    A 0.4%   B 71.2%   C 6.1%   D 8.8%   E 13.5%
rungs           t=3  8,412 done / 8,412 ok / 0 fail    t=4  991 / 991 / 0
stall           0:04:12 since high-water
memory          4.1 GiB RSS        checkpoint in 0:02:48
```

### Machine format

`--stats-format jsonl` emits one flat JSON object per interval, same fields, snake_case, plus
`schema_version`, `k`, `run_id`, `wall_ms`. Everything above must be present in JSONL — never
human-only. `--stats-file` writes JSONL regardless of the stdout format so a run can be watched
and archived at once.

### Signals

- `SIGINT` — stop cleanly, write a checkpoint, print a final summary, exit `UNKNOWN` (2)
- `SIGUSR1` — dump a full stats snapshot immediately without stopping

---

## 9. Milestones

Deliver in this order. Each milestone has a gate; do not start the next until the gate passes.

**M1 — combinatorics core.** `rank`/`unrank`, neighbor enumeration, `info`.
*Gate:* `rank-roundtrip`, `degree`, `symmetry` oracles pass for `k ≤ 12`; `info` matches the
constants table in §1 exactly.

**M2 — independent checker.** `check` written from scratch per §6, plus the `fano` and `witt`
oracles.
*Gate:* both designs validate as perfect 1-codes.

**M3 — solver, small.** Rules A and B, DPLL, color symmetry breaking, `solve` and `code`.
*Gate:* every oracle through `k = 8` passes, both polarities, and every SAT result round-trips
through `check`.

**M4 — observability.** All of §8.
*Gate:* a `k = 6` run produces a coherent human display and valid JSONL; `SIGUSR1` and `SIGINT`
behave.

**M4.5 — structural propagators.** Rules C, D, E and link-ordered branching.
*Gate:* every oracle through `k = 8` still passes with each rule independently on and off — the
rules are redundancy, not semantics, so toggling them must never change an answer, only the time
and conflict count. Any disagreement means a rule is wrong; a wrong Rule D or E produces a false
UNSAT, which is the failure mode this project cannot survive.

**M5 — scale.** Profile and optimize. Cache-friendly layout, no allocation in the hot loop.
*Gate:* `k = 10` partition UNSAT reproducibly; report `k = 12` wall time. **Report the `k=12`
number before doing anything else — it decides whether the project continues.**

Also deliver an **ablation table** at `k = 10` and `k = 12`: wall time, conflicts, and peak RSS for
each of `--anchors 0 / 4 / 16 / 64`, with and without `--cardinality`, `--anchor-reach`, and
`--branch-order link`. Choose the `k = 16` configuration from measurement, not from this document —
my cost estimates are estimates.

**M6 — endurance.** Checkpoint/resume, conflict log, memory ceiling enforcement.
*Gate:* a `k = 12` run can be killed at an arbitrary point, resumed from checkpoint, and reach the
identical result.

---

## 10. Constraints and non-goals

- **Rust**, stable toolchain, `#![forbid(unsafe_code)]` unless you can show a profiled reason,
  and then only in an isolated, documented module.
- Dependencies: `clap` (derive), `serde` + `serde_json`, `anyhow`. `criterion` for benches.
  Nothing else without asking.
- **Deterministic**: identical inputs and seed produce an identical trace, byte for byte.
- **No GPU.** This is a branch-heavy, pointer-chasing, latency-bound workload. Nothing here
  vectorizes usefully.
- **No adjacency list, ever.** Neighbors are computed from bitmasks.
- **No generic SAT encoding.** For reference, the CNF for `k=12` is ~1.48 billion clauses and for
  `k=16` about 736 billion. That path is closed; this tool exists because of it.
- **Do not search one color class at a time.** It looks natural and it is a trap: completing a
  single class in isolation is equivalent to constructing a Steiner system whose existence is an
  open problem, and it discards all the cross-class propagation that makes the partition
  constraint tight. Grow all `k+1` classes simultaneously, vertex by vertex.
- Target machine: Ubuntu 24.04, x86-64. Assume 32 GiB RAM for `k ≤ 14`; the `k = 16` configuration
  should fit in under 8 GiB of solver state and must report its own high-water RSS.

## 11. Deliverables

1. The `odd835` binary with all subcommands in §5.
2. `cargo test` covering §7 structural oracles and everything through `k = 8`.
3. `odd835 oracle` runnable end-to-end, exiting non-zero on any disagreement.
4. A `RESULTS.md` recording, for each rung `k = 2..12`: outcome, wall time, conflicts, peak RSS,
   and the machine it ran on — plus the M5 ablation table and a recommended `k = 16` configuration
   with the measurements that justify it.
5. A short `ARCHITECTURE.md` covering the encoding, the propagators, and specifically:
   - the correctness argument for the symmetry breaking in §4
   - the derivation of the Rule D / E targets from `N_j` and `M_j`, including why
     `a ∈ {0, k-2}` is skipped
   - the approaches considered and rejected (spectral / Delsarte, the `(A+I)x = 1` eigenvector
     form, generic SAT encoding, one-class-at-a-time search), each with the reason