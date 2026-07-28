# odd835 — architecture

For an even `k`, `odd835` decides whether the odd graph `O_k` admits a partition
of its vertex set into `k+1` perfect 1-codes; equivalently whether the Johnson
graph `J(2k,k)` has chromatic number `k+1`. This document covers the encoding,
the propagators, the correctness arguments for every reduction the search
applies, and the approaches that were considered and rejected.

`RESULTS.md` has the measurements. Read that first if you want the numbers.

---

## 1. Encoding

`n = 2k-1`, ground set `[n] = {0..n-1}`. Vertices are the `(k-1)`-subsets of
`[n]`; `T ~ U` iff `T ∩ U = ∅`. Since `2k-1 ≤ 31` for every supported `k`, a
vertex is a `u32` bitmask.

**Indexing.** Colex rank, `rank(S) = Σ_i C(s_i, i+1)`, a bijection onto
`[0, C(2k-1,k-1))`. `u32` suffices: the largest count is 300,540,195 < 2^32.

`rank` is the single hottest operation in the program, so it is table driven.
The mask is split at bit 16; `LOW[m & 0xFFFF]` holds the colex contribution of
the low bits and `HIGH[popcount(low)][m >> 16]` the contribution of the high
bits, offset by however many set bits precede them. Two array reads, no loop.
The tables are `k`-independent (`C(s, i+1)` does not mention `k`) and cost about
2.5 MiB. `Combi::rank_ref` keeps the definition-following loop for tests and the
checker; `odd835 bench` measures the table at ~840 M ranks/s against ~87 M/s for
the loop.

**Neighbours are never stored.** The complement of `T` in `[n]` has exactly `k`
bits, and clearing each in turn enumerates every `(k-1)`-subset disjoint from
`T`. At `k=16` an adjacency list would be 4.8 billion entries; the iterator is
`x & (x-1)` bit stepping and runs at ~1.7 G masks/s.

**Search state.**

```
color: Vec<u8>    // 0..=k, or UNASSIGNED = 0xFF
dom:   Vec<u32>   // still-permitted colours, bits 0..=k
trail: Vec<(u32 vertex, u32 previous dom)>
```

Undo pops trail entries back to a recorded offset. Everything else — class
sizes, per-colour availability, anchor counters, saturation counts, the MRV
index — is restored in lockstep from the same two stacks (`trail` and
`assign_stack`), so a backtrack is O(entries undone) with no scanning.

The number of colours is always exactly `k+1` and is not exposed as an option.
With any other number the problem is a different, weaker problem.

---

## 2. Why `O_k` and not `J(2k,k)`

A `(k+1)`-colouring of `J(2k,k)` has colour classes that are Steiner systems
`S(k-1,k,2k)`. Inclusion–exclusion over the points of a block `B` gives the
number of blocks of the class disjoint from `B`:

```
N_0(B) = (1 + k·(-1)^k) / (k+1)
```

For odd `k > 1` that is negative, so odd `k` is rejected at construction with
the reason printed. For even `k` it is exactly 1, and the only `k`-set disjoint
from `B` is `B^c`, so every class is closed under complementation. Blocks come
in complementary pairs of the same colour, which collapses `C(2k,k)` vertices to
`C(2k-1,k-1)` — at `k=16`, 300,540,195 instead of 601,080,390. The factor of two
is exact and theorem-backed, not an approximation.

### The intersection distributions, and an integrality trap

For a fixed block `B` of class `i`:

```
N_j = C(k,j) · ( C(k,j) + (-1)^(k+j)·k ) / (k+1)      same class
M_j = C(k,j) · ( C(k,j) - (-1)^(k+j)   ) / (k+1)      any other class
```

**These quotients are not integers for every even `k`.** They fail at `k = 8`
and `k = 14`, first at `j = 3`:

| k | first non-integral term |
|---|---|
| 8 | `N_3 = 896/3`, `M_3 = 1064/3` |
| 14 | `N_3 = 25480/3`, `M_3 = 26572/3` |

`N_j` counts blocks, so a fractional value is a proof that no `S(k-1,k,2k)`
exists — hence no perfect 1-code in `O_k` and no partition. This is exactly the
"arithmetic reason" the build spec attributes to `k = 14`, and it applies to
`k = 8` in the same way; it is why both are UNSAT and why a search that cannot
perceive arithmetic finds them so hard. `odd835 info -k 8` and `-k 14` print the
obstruction. Every other even `k ≤ 16` is integral.

The sums are always exactly `Cat(k) = C(2k,k)/(k+1)` as rationals, because
`Σ_j C(k,j)² = C(2k,k)` and `Σ_j (-1)^j C(k,j) = 0`; the oracle checks that on
the exact numerators rather than on the (sometimes fractional) terms.

`Combi::n_dist`/`m_dist` return the floor where the value is fractional. That is
a sound Rule D/E bound in both directions: if a solution exists the value is
integral and the floor is exact, and if none exists nothing can be wrongly
pruned. The tool does **not** short-circuit on the obstruction — the spec asks
for a search, so the search runs.

### Rule D / Rule E targets in `O_k` coordinates

Fix `∞ = 2k-1`, `V = [2k-1]`. The `O_k` vertex `T` is the complementary block
pair `{T ∪ {∞}, V \ T}`. For distinct `T, T'` with `a = |T ∩ T'|` the four
induced block intersections are

```
|(T∪∞) ∩ (T'∪∞)| = a+1          |(V\T) ∩ (V\T')|  = a+1
|(T∪∞) ∩ (V\T')| = k-1-a        |(V\T) ∩ (T'∪∞)|  = k-1-a
```

so summing over a class, with `c_a` and `d_a` as in the spec,

```
N_{a+1} = c_a + c_{k-2-a}        M_{a+1} = d_a + d_{k-2-a}
```

for every `a = 0..k-2`. These are derived in `Combi::rule_d_targets` /
`rule_e_targets` from `N_j`/`M_j`, never hardcoded; the oracle asserts them
against the spec's `k=10` and `k=16` tables and against the brute-force profiles
of the two real designs that exist (Fano at `k=4`, Witt at `k=6`).

### Why `a ∈ {0, k-2}` is skipped

Both cases are consequences of Rule B, so testing them at runtime costs time and
can never fire. The `skip-cases` oracle verifies all of this exhaustively for
`k ≤ 8`:

* `a = 0` — `|T ∩ T'| = 0` means `T` and `T'` are adjacent, so Rule A already
  forbids a shared colour. Hence `c_0 = 0`, and since `N_1 = 0` also
  `c_{k-2} = 0`.
* `a = k-2` — write `T' = (T \ {y}) ∪ {x}` with `y ∈ T`, `x ∉ T`. Then
  `T' ∈ N[u]` for `u = ([n] \ T) \ {x}`, and `T ∈ N[u]` too, so Rule B forbids a
  shared colour. The `k` neighbours `u` of `T` partition the `k(k-1)` vertices at
  intersection `k-2` into `k` blocks of `k-1`, each block sharing exactly one
  closed neighbourhood with `T`.
* That same partition gives Rule E's skipped cases. Each `N[u]`, `u ∈ N(T)`,
  contains exactly one vertex of every colour, so of the `k` neighbours exactly
  one carries colour `ℓ` — that is `d_0 = 1` — and the remaining `k-1`
  neighbourhoods place colour `ℓ` on one of their `k-1` intersection-`(k-2)`
  members, giving `d_{k-2} = k-1`. Consistently, `M_1 = d_0 + d_{k-2} = k`.

The inference therefore lives at `1 ≤ a ≤ k-3`, which is exactly the range of
vertex pairs too far apart for local propagation to reach.

---

## 3. Propagation

A queue of vertices whose domain changed, run to fixpoint.

**Rule A — assignment.** Assigning `v` colour `c` sets `dom[v] = 1<<c` and
clears bit `c` from every `u ∈ N(v)`. An empty domain is a conflict; a singleton
is enqueued as a forced assignment.

**Rule B — closed-neighbourhood counting.** When `dom[v]` changes, each of the
`k+1` closed neighbourhoods containing `v` (`N[v]`, and `N[u]` for `u ∈ N(v)`)
is rescanned. Because `|N[T]| = k+1` equals the number of colours, this is a
permutation constraint, not a mere all-different: every colour occurs exactly
once. Counting supporters of each colour gives conflict at 0 and a forced
assignment at 1, plus an explicit duplicate check — two *assigned* members of
`N[u]` need not be adjacent (two neighbours of `u` meet in `k-2` points), so
Rule A cannot see that clash. Each application touches `(k+1)² = 289` vertices
at `k=16`, and it is where essentially all inference comes from.

**Rule C — class cardinality.** Per colour `i`, `size[i]` (assigned) and
`avail[i]` (unassigned vertices still permitting `i`). Conflicts on
`size[i] > m` and `size[i] + avail[i] < m`. A completed class is struck from
remaining domains lazily via a `closed: u32` mask applied at domain-read time,
rather than by writing to 300M domain vectors.

> One subtlety worth recording, because it was a live bug: `size[i] + avail[i]`
> is *invariant* across an assignment to colour `i` — one unassigned permitter
> becomes one member — so the class counter must be incremented **before** the
> availability sweep. Checking the bound halfway through the update sees a
> spurious shortfall and reports a false conflict. That made `k=2` come out
> UNSAT.

Rule C is genuinely redundant: if every closed neighbourhood is rainbow then
each colour class is a perfect 1-code, so its size is forced to be `m`. It
prunes earlier, it does not change the answer.

**Rules D and E — intersection counts.** The first `A` vertices assigned to each
class become *anchors*. Each anchor `T` carries `c_a(T)` for its own class and
`d_a(T)` per other class; assigning `T'` costs one `popcount(T & T')` per anchor,
`A·(k+1)` per assignment. Conflicts fire when `c_a + c_{k-2-a} > N_{a+1}` or
`d_a + d_{k-2-a} > M_{a+1}` for `1 ≤ a ≤ k-3`.

Rule E is the only mechanism in the engine that couples the classes to each
other, which is what makes "grow all `k+1` classes simultaneously" more than a
slogan. In the measurements it is also the only one of D/E that fires with any
regularity; at `k=4` it produces every conflict in the search.

Undo is symmetric by construction: counters are updated against the anchor set
as it stood *before* the new vertex could join it, and the undo path removes the
anchor first and then decrements, in exact reverse. A new anchor initialises its
counters by scanning the assignment stack. That scan is capped
(`ANCHOR_INIT_SCAN_CAP`, 65536): beyond it the anchor is simply not created,
which weakens Rules D/E but can never make them unsound. In practice classes
grow together, so the `A`-th member of a class arrives while only about
`A·(k+1)` vertices are assigned and the cap never binds.

`--anchor-reach` adds the reachability direction — target minus achieved must
still be reachable from the vertices that remain eligible at the two mirrored
intersection sizes. It costs a full vertex scan per anchor, so it only runs once
a class is within 10% of `m`.

**Régin matching (`--propagator matching`).** Each closed neighbourhood is a
perfect matching constraint between `k+1` vertices and `k+1` colours, so
removing every value that lies in no perfect matching prunes strictly more than
counting — counting is exactly the "some colour has one supporter" special case.

Because the matching is *perfect*, there are no free vertices and the standard
characterisation collapses to a pure SCC condition, which in turn can be
contracted onto the members alone: every colour node has exactly one incoming
matched edge, so `member i → colour c → member m_color[c]` becomes `i → j`. That
turns a 34-node closure into a 17-node one. With cheap pre-exits (all-singleton,
all-full, union too small) and deferral — the expensive filter runs only once the
cheap counting fixpoint is reached, deduplicated by centre — this went from
2.7k to 6.3k conflicts/s at `k=6` while keeping the pruning.

The pruning is worth far more than the cost. At `k=6`, counting alone burns
204,087,009 conflicts in 900 s at depth 79 and is still nowhere near done;
matching finishes the same instance in 243,410 conflicts at depth 22. That is
the single largest factor in this engine.

---

## 4. Search

Chronological backtracking DPLL, no clause learning. Variable order is minimum
remaining values with ties broken by lowest vertex index; value order is lowest
permitted colour first. No restarts, so completeness is unconditional.

**MRV without scanning.** A full `|V|` scan per decision is impossible at scale.
Instead there is one min-heap per domain size; every domain write pushes the
vertex into the heap for its new popcount, and *undo pushes too*, which is what
keeps the invariant (`every unassigned v with popcount p < k+1 is in heaps[p]`)
true across backtracking. Selection peeks, discards stale tops lazily, and
amortises to O(log n) per push. The top bucket is deliberately not materialised
— at `k=16` it alone would be 1.2 GiB — so the rare state where nothing has been
narrowed at all falls back to a linear scan, counted as `full_scans`.

Because undo pushes as well, the heaps accumulate entries in proportion to
*total work*, not live state, and must be swept periodically. `select_mrv` does
that itself; link-ordered branching does not go through it, so `select_link`
calls `maybe_compact_heaps` too. Missing that leaked 147 MiB at `k = 6` — where
the live state is 5 MiB — and would have been fatal at `k = 16`.

**Link-ordered branching (`--branch-order link`).** For a level `t` and a
`(k-t)`-subset `λ ⊂ [2k]`, the `k`-sets `λ ∪ B` map to `C(k+t,t)` distinct `O_k`
vertices (distinct because `λ ≠ ∅` rules out complementary collisions). Branching
inside one link region concentrates assignments so contradictions surface at
shallow depth, instead of MRV scattering them. It is a variable-ordering
heuristic only — see §6.

`t` is clamped to `1 ≤ t ≤ k-1`. Outside that range `λ` is empty, and then
`λ ∪ B` and `λ ∪ B'` *can* be complementary, so the region stops being a set of
distinct vertices and the rung check on it is meaningless. (`t ≥ k` also
underflows `k - t` in unsigned arithmetic, which in release builds turns into a
four-billion-iteration loop rather than a panic — `--link-level 3 -k 2` used to
hang there.)

### Termination semantics

`SAT` (0), `UNSAT` (1), `UNKNOWN` (2), `ERROR` (3), never conflated. Every
limit — timeout, conflict cap, memory ceiling, interrupt — returns UNKNOWN.
`no_false_unsat_under_a_limit` in the integration suite asserts this directly.
On SAT the colouring is written to disk, every class is checked against the full
`N_j` distribution, and the file is re-read and verified by the independent
checker before success is reported.

---

## 5. Symmetry breaking

Getting this wrong turns SAT into false UNSAT, so each reduction is stated with
its argument.

### 5.1 Colour symmetry (`--symmetry color`, default)

Assign `color[v0] = 0` for `v0 = unrank(0)`, then the `k` neighbours of `v0`, in
increasing vertex-index order, the colours `1..k`.

*Argument.* In any solution the `k+1` members of `N[v0]` carry `k+1` distinct
colours. Composing with the colour permutation that sends those to `0..k` in
that order yields another solution — the constraint system is invariant under
relabelling colours — which satisfies the fixed assignment. So a solution exists
iff one exists in this form. This consumes the `(k+1)!` colour symmetry exactly.

### 5.2 Orbit reduction (`--symmetry orbit`)

Colour breaking leaves the whole vertex automorphism group untouched. `Aut(O_k)`
contains `S_{2k-1}` acting on the ground set, and the subgroup preserving the
broken configuration is `Stab(v0) = S(T_0) × S(C_0)` where `T_0 = {0..k-2}` is
`v0` and `C_0 = [n] \ T_0`, of order `(k-1)!·k!` — 86,400 at `k=6`, and
`4.8 × 10^12` at `k=16`. Chronological backtracking re-explores every one of
those copies.

`--symmetry orbit` consumes the `S(C_0)` factor. Let

* `λ' = T_0 \ {k-2} = {0..k-3}`, of size `k-2`;
* `w_x = λ' ∪ {x}` for `x ∈ C_0`, and `u_z = C_0 \ {z}` for `z ∈ C_0` (the
  neighbours of `v0`);
* `φ : C_0 → {1..k}`, `φ(z) = color(u_z)`, fixed by §5.1;
* `ψ : C_0 → {1..k}`, `ψ(x) = color(w_x)`.

**`ψ` is a bijection.** The `k+1` vertices containing `λ'` are `v0` and the
`w_x`; they pairwise meet in `k-2` points, so by §2 each pair shares a closed
neighbourhood and Rule B forces them pairwise distinct. With `k+1` vertices and
`k+1` colours that is a rainbow, and `v0` holds colour 0.

**The action.** For `g ∈ S(C_0)` (extended by the identity on `T_0`), define
`χ' = σ_g ∘ χ ∘ g^{-1}` with `σ_g = φ g φ^{-1}` on `{1..k}` and `σ_g(0) = 0`.
`g` is a graph automorphism and `σ_g` a colour permutation, so `χ'` is a valid
colouring. It respects §5.1: `g` fixes `T_0` pointwise so `χ'(v0) = 0`, and
`χ'(u_z) = σ_g(φ(g^{-1}z)) = φ(z)`. Since `g` fixes `λ'` pointwise,
`g^{-1}(w_x) = w_{g^{-1}x}`, hence

```
h := φ^{-1} ∘ ψ   transforms as   h ↦ g h g^{-1}.
```

So `h ∈ Sym(C_0) ≅ S_k` may be normalised to a canonical representative of its
**conjugacy class** — its cycle type. The solver therefore branches at the root
over the `p(k)` partitions of `k`, fixing all `k` colours `ψ(x) = φ(h(x))` in
each branch, and reports UNSAT only if every branch is UNSAT. This replaces `k!`
symmetric copies with `p(k)` branches: 720 → 11 at `k=6`, and
479,001,600 → 77 at `k=12`.

It is a disjunction, not an assumption: an UNKNOWN in any branch makes the whole
answer UNKNOWN.

What remains unbroken is `S(λ') ≅ S_{k-2}` (which fixes `v0`, every `u_z` and
every `w_x` setwise) together with the centraliser of `h` in `S(C_0)`. Breaking
those would need full canonical augmentation, which is out of scope here.

*Validation.* `orbit_reduction_agrees_with_colour_breaking` runs both modes at
`k = 2, 4, 6` and requires the same answer, including the `k=2` SAT case — a
reduction that lost solutions would show up there first.

### 5.3 Code mode

`odd835 code` fixes `unrank(0) ∈ S`. `O_k` is vertex transitive under
`S_{2k-1}`, and automorphisms map perfect codes to perfect codes, so if any
perfect code exists then one containing vertex 0 exists. Complete.

---

## 6. Rung checks are diagnostics, not inference

The spec's structure theorem forces a level-`t` link region to carry a large set
`LS(t-1, t, k+t)`: each colour class restricted to the region is an
`S(t-1,t,k+t)`. That is correct, and `check_link` verifies it. **It also carries
no pruning power beyond Rule B**, which is worth stating explicitly because it
determines how much the feature is worth.

An `S(t-1,t,k+t)` requires every `(t-1)`-subset `P` of the region's ground set to
be covered exactly once per colour. The cells containing `P` are exactly the
level-1 region of `λ ∪ P` (a `(k-1)`-set), which is `k+1` vertices that pairwise
meet in `k-2` points or are disjoint — either way pairwise forced distinct by
Rules A and B, hence rainbow. So the level-`t` condition is precisely the
conjunction of level-1 conditions over the `(t-1)`-subsets, and every one of
those is already enforced.

Consequently a rung failure can only mean a bug in this program or in the
theorem. It is treated as a conflict (sound either way), logged loudly with the
offending `λ`, and counted separately in the rung statistics. Under
`--branch-order mrv` the `completed` counter stays at zero because MRV rarely
finishes a region — expected, not a defect.

`level_one_link_adds_nothing_to_rule_b` and
`fano_link_regions_induce_the_large_set_class` pin both halves of this down. The
second is the only place a real design is available to test against: the Fano
code's blocks inside every `k=4`, `t=2` region form a perfect matching on the
six remaining points, i.e. an `S(1,2,6)`.

Link *branching* remains useful for a different reason: it changes which
variables get assigned, not what can be inferred.

---

## 7. The independent checker

`odd835 check` shares nothing with the solver except `rank`/`unrank` and the
binomial table. It enumerates vertices with its own generic subset generator,
derives neighbours as "all `(k-1)`-subsets of `[n] \ T`" rather than by the
solver's bit stepping, and verifies, from the definitions:

1. one colour per vertex, in `0..=k`;
2. every vertex has exactly `k` neighbours;
3. every closed neighbourhood carries each colour exactly once;
4. every class has size exactly `m`;
5. every class is a perfect 1-code — built independently, as a cover count over
   all vertices, rather than as a restatement of (3).

`definition_neighbours_match_pairwise_disjointness_small_k` closes the loop by
brute-forcing every vertex pair at `k ≤ 8` and comparing against the definitional
enumeration. A solver/checker disagreement is a SEV-1.

---

## 8. Observability

Every counter in spec section 8 is maintained and is present in the JSONL
record; nothing is human-only. The ones that earn their keep:

* `saturated` — closed neighbourhoods that are fully assigned and rainbow, out
  of exactly `|V|`. The primary "targets hit" metric, maintained incrementally
  (`k+1` increments per assignment, undone on backtrack).
* `assigned_high_water` and `stall` — the pair that tells an operator whether a
  week-long run is progressing or grinding.
* **Propagator attribution.** Conflicts and forced assignments broken out by
  rule. This is the most useful diagnostic in the tool and is why the ablation
  conclusions in RESULTS.md are evidence rather than guesses; it is what showed
  that Rules C and D contribute essentially nothing while E carries real weight
  at small `k`.

`--stats-file` writes JSONL regardless of the stdout format. `SIGINT` stops
cleanly with a checkpoint and exits UNKNOWN; `SIGUSR1` dumps a snapshot. The
flags and the clean-stop path are always compiled; registering the OS handlers
needs `signal-hook`, which is not one of the four authorised dependencies, so it
lives behind the optional `signals` feature (`cargo build --features signals`,
Unix only).

---

## 9. Endurance

A checkpoint stores the decision stack, not the state: `(vertex, remaining
colour mask, chosen colour)` per level, plus the orbit branch, the RNG state and
the counters. Propagation is deterministic, so replaying that sequence rebuilds
the exact state — compact, and self-validating, since a replay that diverges is
detected immediately.

One correctness detail: a snapshot taken between "propagation failed" and
"backtrack" legitimately ends on a *conflicting* decision. The checkpoint
records `in_conflict` so replay reproduces that state instead of rejecting the
file as corrupt. Without it, resume failed roughly whenever the checkpoint
landed on a conflict — which, at a few hundred thousand conflicts per second, is
most of the time.

A resume whose configuration fingerprint differs from the checkpoint's is
refused rather than silently reinterpreted.

---

## 10. Considered and rejected

**Spectral / Delsarte and equitable-partition conditions.** Checked, and
automatically satisfied for every `k`. They are global statements about the
completed partition; they cannot be maintained incrementally against a partial
assignment, and they carry no information even when complete. Not implemented.

**The `(A+I)x_i = 1` eigenvector form.** This is the rainbow constraint
rewritten in matrix form. It has no independent content, and evaluating it needs
the full assignment. Not implemented.

**Generic SAT encoding.** The CNF for `k=12` is about 1.48 billion clauses and
for `k=16` about 736 billion. This tool exists because that path is closed.

**One colour class at a time.** Completing a single class in isolation is
equivalent to constructing a Steiner system whose existence is open, and it
discards all the cross-class propagation (Rule E, and most of Rule B's force
events) that makes the partition constraint tight. All `k+1` classes grow
together, vertex by vertex. `odd835 code` is a separate engine for a separate
question, not this search restricted to one class.

**Adjacency lists.** 4.8 billion entries at `k=16`. Neighbours are always
recomputed from bitmasks.

**GPU.** Branch-heavy, pointer-chasing, latency-bound. Nothing here vectorises
usefully.

**Clause learning / conflict-directed backjumping.** Out of scope for v1 per the
spec. It is, on the evidence in RESULTS.md, the single most promising direction
left: the search spends its time re-deriving the same contradictions after
backtracking to an irrelevant recent decision.

**Deeper symmetry breaking than §5.2.** Consuming the residual
`S(λ') ≅ S_{k-2}` and the centraliser of `h` needs canonical augmentation or
lex-leader constraints over the full stabiliser. Both are error-prone in exactly
the direction this project cannot tolerate, and neither was attempted.

---

## 11. Layout

| file | contents |
|---|---|
| `src/combi.rs` | binomials, colex rank/unrank, neighbours, `N_j`/`M_j`, link regions, `info` |
| `src/solver/engine.rs` | state, trail, Rules A–E, MRV heaps, fixpoint |
| `src/solver/matching.rs` | Régin filtering with contracted SCC |
| `src/solver/search.rs` | DPLL, symmetry breaking, orbit branches, checkpoints |
| `src/solver/link.rs` | link regions, rung verification |
| `src/codesearch.rs` | the separate single-perfect-code engine |
| `src/check.rs` | the independent checker |
| `src/designs.rs` | Fano and Witt as literal data |
| `src/oracle.rs` | the known-answer suite |
| `src/stats.rs` | counters, human display, JSONL |
| `tests/oracles.rs` | end-to-end integration tests |
