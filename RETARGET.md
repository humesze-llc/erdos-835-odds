# s45 — retarget state and next build (handoff, 2026-07-27)

Target: refute `S(4,5,21)`. That kills `k = 16` for Erdős #835 (11 derivations
from `S(15,16,32)`, chain verified: every level admissible) and stands alone as
a named open problem.

## Built and measured

`src/s45/` — exact cover over items = 4-subsets, options = 5-subsets, with the
triple-derived perfect-matching propagator, `{0,1,2}` spread symmetry break, and
an independent verifier sharing no code with the engine. Exit contract as
odd835: SAT 0 / UNSAT 1 / UNKNOWN 2 / ERROR 3, a limit never prints UNSAT.

**Spec correction (settled).** The matching structure is *not* on items×options
— each option covers 5 items, so that is exact cover by 5-sets, NP-complete, no
exact polynomial filtering, Régin inapplicable. It is at the **triples**: the
blocks through a 3-set `T` form a perfect matching on the other `v-3` points.
Those graphs are **non-bipartite** → Tutte/Edmonds blossom, not Régin/Hall.
Incidence identity confirms the bookkeeping: each 5-set contains `C(5,3) = 10`
triples and contributes one edge to each, so `options × 10 = triples × edges`
exactly. Also `deg_T(x) = avail[T ∪ {x}]`, so counting is subsumed and the new
inference is matching feasibility/filtering.

### Calibration

| rung | result |
|---|---|
| v=11 | SAT, 4 decisions, 0 conflicts, independently verified |
| v=15 | **UNSAT — 13m36s.** 222,704,346 decisions / 114,754,023 conflicts / 1.27e9 propagations. Mendelsohn–Hung 1972 independently reproduced. Config: `--no-matching` (level-1 + level-2 symmetry, exact-cover propagation only) |

**Gate 1 is met.** For reference, CaDiCaL on the pairwise CNF did not refute
v=15 in ~280 s, and this engine did not in 1,800 s before the level-2 quotient.

#### What produced the win

| step | effect |
|---|---|
| `l >= 2` branch kill (below) | 22 -> 7 branches at v=21, 7 -> 2 at v=15; removes **99.93%** of residual symmetry |
| level-2 quotient | tree 2.13e10 -> **1.67e8**, a **127x** reduction |
| turning the propagator OFF | 565x faster per node, costing only 3.9x in tree size |

The third is counter-intuitive and only visible once tree size is measured
instead of conflict rate: **blossom feasibility and edge filtering are both net
losses under chronological backtracking.** Re-measure after CDCL — the
amortisation argument may reverse it, but it now has to work against a 3.9x
base, not the 58x the truncated-run conflict counts suggested.

Estimator validation: Knuth probing predicted 1.67e8 nodes against an actual
2.23e8 — within 34%, good enough to trust the v=17 / v=21 projections.

#### Tree sizes (Knuth probing, validated above)

| rung | nodes | note |
|---|---|---|
| v=11 | 8.5e1 | every probe reaches a cover |
| v=15 | 1.67e8 (post level-2) | actual 2.23e8 |
| v=17 | 9.4e18 (pre level-2) | expect ~1e17 post; still CDCL territory |

Propagator ladder at v=15, 60 s each:

| level | conflicts | rate |
|---|---|---|
| exact cover only | 9,635,597 | 161k/s |
| + blossom feasibility | 1,090,813 | 18k/s |
| + edge filtering (`--filter`) | 18,694 | 311/s |

**Do not read this as "propagation buys nothing."** It measures time-to-answer
under *chronological* backtracking, where filtering work is discarded on every
backtrack. Under CDCL, filtered edges become propagations that feed conflict
analysis and learned clauses amortise the filtering across the tree. `--filter`
stays toggleable; **re-run this ladder after CDCL lands** — that is the
measurement that decides, not this one.

## Next build, in this order

### 1. Static orbit quotient at the top

Layering rule: **static quotient above, learning below, no interaction surface.**
Mixing dynamic symmetry no-goods with learned clauses is a known soundness-bug
source; do not do it.

*Level 1* (built): blocks through `{0,1,2}` form a perfect matching on the other
`v-3` points; relabel to `(3,4),(5,6),…`. Fixes `(v-3)/2` blocks.

*Level 2* (validated, not yet implemented): at `T₂ = {0,1,3}`, the block
`{0,1,2,3,4}` already matches 2↔4; the rest is a matching `M'` on `{5,…,v-1}`,
`2n` points with `n = m-1`, `m = (v-3)/2`. Residual group there is `S₂ ≀ Sₙ`, and
the orbits of `M'` correspond to cycle types of `P' ∪ M'`, i.e. partitions of
`n`. Branch over `p(n)` canonical representatives.

Canonical rep for partition `λ`: pairs of `P'` in order; a block of `ℓ`
consecutive pairs `(a_i,b_i)` becomes one `2ℓ`-cycle via `M'` edges
`(b_i, a_{i+1})` cyclically; `ℓ = 1` means `M'` agrees with `P'` on that pair.

**Validation status: CLOSED for every rung in play.** Exhaustive orbit BFS
under generators of `S₂ ≀ Sₙ` confirms cycle type is a *complete* invariant (not
merely an invariant), orbit count `= p(n)`, and the canonical reps hit each
orbit exactly once.

* `n ≤ 7` (covers `v ≤ 19`): verified.
* `n = 8` (covers **v = 21**): verified. All 2,027,025 perfect matchings on 16
  points enumerated and classified into 22 cycle types; BFS from the lex-least
  member of each class reproduces the class exactly, and no generator leaves a
  class. Class sizes sum to 2,027,025. Largest orbit `(8,)` = 645,120; smallest
  `(1^8)` = 1.

So the quotient layer rests on exhaustively verified decompositions at both
rungs — which was the precondition for ever trusting a `v = 21` UNSAT.

**Completeness of the branching, verified separately** (`tools_soundness_check.py`).
The decomposition is a fact about matchings and a group; the *branching* being
complete needs four further premises, each tested rather than argued:

| premise | result |
|---|---|
| **A.** `G₁ = S({0,1,2}) × Aut(P)` stabilises the level-1 spread | 0 violations at v=11 and v=15. At v=11 `G₁` is the **full** stabiliser in `S₁₁` (2304 = 2304, equal) — not an overclaim |
| **B.** `stab(T₂)` acts on `{5..v-1}` as the **full** `S₂ ≀ Sₙ` | orders 96 / 7680 as predicted; 48 / 3840 distinct induced actions; every element fixes 3 and 4 pointwise |
| **C.** level-1 is WLOG | 300/300 random relabellings renormalise into level-1 form |
| **D.** canonicalisation preserves designs | 48/48 level-1 designs land in a branch, image still a valid level-1 `S(4,5,11)` |
| negative control | with the within-pair swaps dropped, 36/48 designs can no longer reach their rep — **the test has power** |

A guards the failure mode that fabricates refutations (a group *larger* than the
true stabiliser); B guards its dual (a group too small, so `p(n)` reps are too
few and designs fall between branches).

*Scope.* End-to-end (C, D) can only run where a design exists, so it is `v = 11`
(`n = 3`) only — `S(4,5,13)` is inadmissible and nothing else in range has a
design. All 48 designs have level-2 type `(3,)`; the other two branches are
genuinely empty, which costs nothing. The reps for unoccupied types are still
verified to *have* the type they claim, so no design of those types could be
lost. Premises A and B are structural and verified at two `v`; the orbit
decomposition is verified through `n = 8`.

| v | m | n | branches `p(n)` | replaces `2ⁿ·n!` |
|---|---|---|---|---|
| 15 | 6 | 5 | 7 | 3,840 |
| 17 | 7 | 6 | 11 | 46,080 |
| 21 | 9 | 8 | 22 | 10,321,920 |

#### `T₂ = {0,1,3}` is FROZEN

Two separate claims, with different statuses — do not conflate them:

* **Soundness** does not depend on `{0,1,3}` being the best choice.
  Completeness only requires branching over orbit representatives of the second
  spread under the residual group, which is exactly what the verified
  decomposition licenses *for this `T₂`'s structure*.
* **Structure** is why `{0,1,3}` is the clean choice: it meets `T₁` in two
  points, so the shared level-1 block `{0,1,2,3,4}` pins the pair `(2,4)` and
  leaves precisely the 16-point / 8-pair wreath picture that was verified.

A `T₂` meeting `T₁` in one or zero points puts the second spread on a point set
where the residual group does **not** act as a clean `S₂ ≀ Sₙ` (broken pairs
leave unpaired singletons), and the decomposition would need its own
verification from scratch. So a different `T₂` is **not a tuning knob — it is a
new soundness obligation.** With 22 branches already, the upside from shopping
for a better `T₂` is bounded. Frozen.

#### `l >= 2`: fifteen of the twenty-two branches DO NOT EXIST

A level-2 branch whose cycle type has any part `l = 1` is infeasible with no
search. `l = 1` means `M'` agrees with `P'` on that pair, so the block
`{0,1,3,x,x'}` is chosen while level 1 already fixed `{0,1,2,x,x'}`. Those two
distinct blocks share `{0,1,x,x'}` — **four** points — so that 4-set is covered
twice. Contradiction.

Surviving branches are the partitions of `n` with every part `>= 2`, i.e.
`p(n) - p(n-1)`:

| v | branches | surviving |
|---|---|---|
| 15 | 7 | 2 — `(5)`, `(3,2)` |
| 17 | 11 | 4 |
| 21 | 22 | **7** — `(8) (6,2) (5,3) (4,4) (4,2,2) (3,3,2) (2,2,2,2)` |

Confirmed against data already in hand: at v=11 the only all-parts-`>=2`
partition of 3 is `(3,)`, and all 48 `S(4,5,11)` designs have exactly that type.

**This makes level 3 not worth building.** 99.93% of the residual symmetry sat
in branches that do not exist. Across the 7 survivors the residuals total 6,940,
max 6,144 (on `(2,2,2,2)`), the rest `<= 288`. That is a *proven bound* on what
any further symmetry quotient can achieve — against the ~1e9x needed at v=17.

#### A third level, if it is ever needed

The residual after two spreads is `Aut(P' ∪ M')`, which is **branch-dependent**:
a product of dihedral-type factors per cycle and symmetric factors across
like-length cycles, so it varies across the 22 cycle types. Verification would
therefore be 22 small exhaustive checks, one per type — fix `M₀` and the
level-2 representative, enumerate third matchings, BFS under computed
generators of `Aut(M₀ ∪ M₁)`. The `orbit_check` harness generalises directly and
each check is *smaller* than the n=8 run.

**Do not build this speculatively.** After the level-2 quotient plus CDCL the
residual is already down to those dihedral products, and the deciding
measurement is whether learning eats what is left. If it does, level 3 never
gets built; if it does not, the verification path is known and cheap.

### 2. Plain CNF + CaDiCaL — TRIED, RULED OUT

**The winning config (`--no-matching`) produces no matching conflicts at all.**
Every conflict is an exact-cover conflict, and exact cover is *directly CNF
encodable* — so for that configuration there is no theory to propagate and
**IPASIR-UP may be unnecessary entirely.**

Thread 3 already showed CaDiCaL fails on the pairwise CNF at v=15 in ~280 s —
but that was with **level-1 symmetry breaking only**. Level 2 is what bought
127x here. The cheap experiment nobody has run:

    python tools_gen_cnf.py 15      # emits one CNF per surviving branch
    cadical s45_15_b0.cnf ; cadical s45_15_b1.cnf   # UNSAT iff BOTH are

v=15 emits 2 branches, 3003 vars / 76451 clauses / 11 units fixed each. **Run
this before building anything.** If CaDiCaL now closes v=15 in seconds, the
whole IPASIR-UP plan collapses into "generate CNF, run a stock solver", LRAT
comes free (no theory lemmas -> the RUP problem disappears), and item 2 of the
gate is solved rather than worked around.

*Status: RUN. Result: **the cheap path does not work.*** CaDiCaL 1.9.5 (via
python-sat in a venv) on `s45_15_b0.cnf` — level-1 AND level-2 breaking, 3003
vars / 76451 clauses — did **not** refute branch 0 in >20 minutes. The native
exact-cover engine closes **both** branches in 13m36s.

Encoding validated: `s45_11_b0.cnf` is SAT in 0.00s, so the generator is right
and this is a genuine performance gap, not a broken instance.

**Conclusion: the pairwise AMO encoding destroys the structure the engine
exploits.** CaDiCaL must rediscover exactly-one from `C(v-4,2)` binary clauses
per item, and gets no MRV-over-items and no matching structure at all. Stock
CDCL on CNF is *worse* than hand-rolled DPLL with native propagation here.

So **IPASIR-UP is not avoidable — it is confirmed necessary.** The win has to
come from combining native structure-aware propagation with learning, which is
exactly what a user propagator provides and what neither half delivers alone.
The LRAT/RUP problem therefore stays live (see gate item 2).

### 3. CDCL(T) via IPASIR-UP — BUILT; SOUND; CURRENTLY SLOWER THAN DPLL

*Status: BUILT AND VALIDATED. Performance: **a regression so far.***

CaDiCaL 2.1.3 is vendored under `vendor/cadical` and builds with MSVC (see
`vendor/PATCHES.md`: one source patch, two compat headers). `vendor/shim`
exposes `ExternalPropagator` as C function pointers, because CaDiCaL's own C
API stops at plain IPASIR. `src/s45/ipasir.rs` is the binding and the only
`unsafe` in the tree; `src/s45/cdcl.rs` is the theory.

**Encoding.** CaDiCaL gets the `C(v,4)` at-least-one clauses *only* — 5,985 at
v=21 instead of 819,945. At-most-one becomes theory propagation with
two-literal reasons, materialised only when used. Assertions in CaDiCaL are
left **on**: they caught a real bug (see below).

**Measured, v=15, both branches, level-1 + level-2:**

| engine | result |
| --- | --- |
| native DPLL (`solve`) | UNSAT, 13m36s |
| stock CaDiCaL, pairwise CNF | no answer in >20 min |
| CDCL(T), VSIDS branching | **no answer in 20 min** |
| CDCL(T), engine MRV branching (`--mrv`) | **no answer in 20 min** |

So the current CDCL(T) build is *worse than the DPLL engine it was meant to
replace*, under either branching rule. Restoring MRV was not the missing
piece.

#### Tight mode: resolve the skipped exclusions away

`--eager` (the original) streams every exclusion. The default is now **tight**:
the propagator sends only *forced placements*, and explains them by resolution.
Start from the at-least-one clause of the forcing 4-set, `z_1 ∨ … ∨ z_{v-4}`;
each excluded `z_j` was excluded by some placed block `x_j`, and
`(¬x_j ∨ ¬z_j)` is valid, so one resolution step per candidate yields

```
    y ∨ ¬x_1 ∨ ¬x_2 ∨ …
```

Every literal now names a block CaDiCaL itself assigned, so the clause is unit
under its assignment *without it ever being told about the `5·(v-5)`
individual exclusions*. Where CaDiCaL excluded a candidate itself, that
literal simply stays. `Cover::explain_item`, validated at construction by
`check_item_lemma` (every candidate of the 4-set accounted for) and
`check_falsified`.

At-most-one is then enforced lazily: when CaDiCaL places a block the engine had
excluded, it gets the binary back as a conflict. Classic lazy clause
generation — the constraint materialises exactly when violated.

Effect at v=15: **335.8M theory propagations → 0.65M**, a 500x cut in callback
traffic.

Three bugs surfaced building it, all worth knowing:

* Tight mode initially emitted *nothing* when CaDiCaL placed an
  already-excluded block, so nothing objected and models came back with 457
  blocks instead of 91. The lazy binary is what closes that.
* The falsification check was running at clause *delivery*. Pending clauses
  deliberately survive backtracking (they stay valid, see `notify_backtrack`),
  so after one they are no longer falsified. The check belongs at
  construction, which is where the invariant actually holds.
* `are_reasons_forgettable` must be **mode-dependent**. Short at-most-one
  binaries are the encoding and are worth keeping; long resolved explanations
  are not, and 644k undeletable ones strangle BCP. 146 → 489 external
  conflicts/s on that change alone.

#### The three-hour run — the only budget large enough to mean anything

`s45 cdcl -v 15 --timeout 10800`, tight mode, branch 0 (`lambda [5]`) alone:

```
c conflicts:        20213497     1911.97 per second
c propagations:   3287211562        0.31 M per second
c learned:         20337774      100.61 % per conflict
c learned_lits:  1473966011                  (72.5 literals per clause, pre-shrink)
c shrunken:       503512028       34.16 % of learned literals
c reduced:         17013042       84.17 % per conflict
c restarts:          577244       35.02 interval
RESULT: UNKNOWN     wall 10800.03s
```

**Branch 0 did not close in three hours.** The native DPLL closes *both*
branches in 13m36s.

The load-bearing detail is **throughput decay**. Conflict rate by sample
length: 8,844/s at 60s, 5,926/s at 120s, **1,912/s averaged over three
hours**. Propagation rate falls the same way, 1.38M/s to 0.31M/s. The clause
database outgrows what reduction can control — raw learned clauses average
72.5 literals, and 84% of a conflict's worth of clauses is discarded per
conflict. Against the native engine's ~140k conflicts/s this is a **~73x**
per-conflict penalty at three hours, not the ~16x a one-minute sample shows.

**What this does and does not establish.** It establishes that CDCL(T) is
uncompetitive here on wall clock, decisively: even a generous assumption about
how few conflicts learning ultimately needs cannot survive a 73x and widening
per-conflict cost. It does **not** establish that learning fails to cut the
search, because branch 0 never closed — 20.2M conflicts is a lower bound on
what CDCL(T) needs, and the DPLL engine's ~57M for the same branch is not
directly comparable to an unfinished run. An earlier draft of this section
asserted the stronger claim from an arithmetic slip (a 50M conflict estimate
extrapolated from the 120s rate, against an actual 20.2M). The weaker claim is
the supported one and is sufficient.

#### Reading the cost correctly

An intermediate diagnosis here was **wrong** and is worth recording, because
the mistake is easy to repeat: the propagator's own `cover_conflicts` counter
reads a few hundred per second, which looks like a catastrophic slowdown. It
is not CaDiCaL's conflict rate. CaDiCaL's own statistics on the same run:

```
c conflicts:      520713    8844.38  per second
c propagations: 81266774       1.38M per second
```

8.8k conflicts/s against the native engine's ~140k/s is a **~16x** constant for
learning, clause management and analysis — an ordinary CDCL trade, not a
pathology. Every "no answer in 20 minutes" result above was therefore measured
against too short a budget: the DPLL baseline itself needs 13m36s, so a 16x
slower-per-conflict engine needs conflict counts to drop by more than 16x
before the wall-clock crosses over, and 10-20 minute probes cannot see that.

**Do not tune against the propagator's internal counters.** Use
`c conflicts:` from CaDiCaL's own statistics block.

#### The eager mode's cost, for the record

The `--mrv` run is the diagnostic one: **335,844,625 theory propagations and
156 external conflicts in 20 minutes**, against the DPLL engine's 114,754,023
conflicts in 13m36s. The propagator is doing almost nothing but propagate.

That is structural, not a tuning problem. `external_propagate.cpp:262-278`
runs a full `propagate()` plus `notify_assignments()` after **every single**
literal returned by `cb_propagate`. Placing one block excludes `5·(v-5)`
overlapping blocks — 50 at v=15, 80 at v=21 — so one decision costs 50-80 BCP
passes where the native engine costs one inline loop. The interface returns
one literal at a time, so this cannot be batched away.

Measured: ~280k theory propagations/second, i.e. ~3.5 µs per exclusion, for
work the native engine does in tens of nanoseconds.

**This is the accounting that decides the architecture.** Learning is real but
it is bought at 100x on the propagation side, and at v=15 the trade is
clearly negative. The next thing to try is therefore *fewer* propagations, not
better ones: emit only exclusions that make some 4-set tight (availability
dropping to 1), and let `cb_check_found_model` catch any at-most-one violation
that slips through, since a violation there has a ready two-literal lemma.
That keeps soundness exactly where it is — the final check is already the
backstop — while cutting the callback count by whatever fraction of exclusions
are inert, which the ladder above suggests is most of them.

If that does not close v=15 inside the DPLL engine's 13m36s, the honest
conclusion is that CaDiCaL is the wrong host for this problem and learning
should be added to the native engine instead, where propagation stays inline.

#### The fake refutation — read this before trusting any number here

An earlier build reported **S(4,5,21) UNSAT in 2.17 seconds**, with v=15 at
0.03s and v=17 at 0.19s, all three "confirming" the literature. Every one of
those was wrong.

Cause: `set_in` returns `Why::Cover` for two different events — a genuine
collision with another IN block, and a *cascade* failure where some 4-set ran
out of candidates. The conflict-clause builder assumed the first. On the
second there is no second block to name, so the clause degenerated to the unit
`(¬o)`: "block `o` is in no design at all". Unsound, and silent — it prunes
real solutions while still terminating with a confident UNSAT.

What did **not** catch it: the v=11/15/17 ladder. v=11 stayed SAT because a
solution survived the bad pruning; v=15 and v=17 are genuinely UNSAT, so the
right answer came out for the wrong reason. **A ladder of correct answers is
not a soundness test when the failure mode is over-pruning.**

What did catch it: the result being too good. 2.17s for a named open problem,
against 13m36s for the calibration rung, is not a speedup, it is a symptom.

Two guards now stand where that bug was:

* `Cover::debug_check_lemma` runs in **release** on every emitted clause and
  asserts it is structurally a lemma the theory can justify — an at-most-one
  binary over two blocks that really share a 4-set, or an all-negative
  "not all of these blocks together". A unit clause is a hard panic.
* `s45 cdcl --count` enumerates models by blocking. At v=11 with level-1
  breaking it must find **48** designs, the number
  `tools_soundness_check.py` derives by independent enumeration in Python.
  Any unsound lemma shows up immediately as a count that is too low. This is
  the test that has teeth, because it probes over-pruning directly.

The general lesson for whatever comes next: **UNSAT is only as sound as the
weakest clause ever handed to the solver.** Every clause this propagator can
emit is globally valid by construction — that argument, not the ladder, is
what makes a refutation believable, and it needs re-checking each time a new
rule is added.

#### Explanations for the rules not yet wired in

The hard part is **explanations**, and it must be designed before the solver is
written. Learning is only as good as the clauses the theory propagator can
justify; if explanations default to the full trail, CDCL will run but the
learned clauses will not generalise and the gate fails again for a subtler
reason.

* **Infeasibility at a triple** → Tutte–Berge witness: a set `S` whose deletion
  from `G_T` leaves more than `|S|` odd components. The explanation clause is
  the negated assignments that removed the edges crossing out of those
  components — not the whole trail.
* **Edge filtering** explains the same way one level down: `uv` is forced out
  exactly when `G_T − {u,v}` has no perfect matching, again a Tutte witness.
* **Witness minimisation is a cost curve, not a cliff.** Deletion-minimal
  witnesses are polynomial to compute: each candidate-removal test is a single
  blossom feasibility call on a subgraph, and QuickXplain-style bisection
  reaches a minimal witness of size `w` in roughly `O(w log(n/w))` such calls.
  Large *raw* witnesses therefore convert the question from "does learning
  work" into "what does it cost per conflict" — a measured curve. The
  architecture is only in trouble if the **deletion-minimal** witnesses are
  large. (Minimal here means irreducible, not minimum-cardinality; minimum is
  NP-hard and is not needed.)

### Instrumentation, from the very first CDCL run

Not one number — these, per conflict:

| metric | why |
|---|---|
| raw witness size | the input to minimisation |
| deletion-minimal witness size | the number that actually decides the architecture |
| minimisation wall time | the toll, if raw witnesses are large |
| **LBD** of the learned clause | clause quality. **Width is the wrong metric** — a wide clause that asserts at a low decision level still cuts deep |
| backjump distance | how much tree the clause actually discards |
| **clause participation** | whether each learned clause is ever an antecedent in a later conflict. LBD *predicts* usefulness; participation *measures* it — divergence between the two is the earliest signal that explanations look general but are not |

**Bin every one of these by decision depth.** Early conflicts have small,
localised witnesses almost by construction; what decides *v=15-in-seconds* is
the tail behaviour deep in the tree, and a mean over all conflicts hides it.

**Baseline frame.** `v = 11` closes conflict-free and cannot serve as a
baseline. Use a **capped run — `v = 15`, first ~10,000 conflicts** — re-measured
after *each* layer lands, so every histogram shares a frame and layer effects
show up as drift rather than being inferred from terminal wall clock.

This exists **before the first learned clause is used for anything**, not bolted
on after the first disappointing run. A slow `v = 15` caused by "a toll worth
paying" and one caused by "explanations do not generalise" are indistinguishable
from wall clock alone — which is exactly why the previous gate failure was only
diagnosable in hindsight.

### 3. LRAT emission, per cube, plus the checked-certificate gate

## Block-pair counting is PROVABLY exhausted

`n_j = #{C != B : |B n C| = j}` satisfies `sum_j C(j,i) n_j = C(5,i)(lam_i - 1)`
for `i = 0..4`. That matrix is unit upper-triangular, **det = 1**, so `n_0..n_4`
are *uniquely determined* by `(v,k,t)` — zero degrees of freedom, no slack, no
inequality to derive. Any further constraint must involve **three or more
blocks**.

| v | n_0 | n_1 | n_2 | n_3 |
|---|---|---|---|---|
| 15 | 22 | 100 | 100 | 50 |
| 17 | 60 | 195 | 160 | 60 |
| 21 | **256** | **540** | 320 | 80 |

All non-negative integers, so no divisibility kill (consistent with threads 1–2).
`n_3 = 10*((v-3)/2 - 1)` is already forced by Rule T and `n_2` by the pair/STS
level; only **`n_0` and `n_1`** are long-range and unexploited.

## Open items

* **Explanation extraction — BUILT, UNMEASURED.** `Engine::explain_triple`
  returns a deletion-minimal reason clause for a triple-matching conflict:
  restore each removed edge in turn, keep it only if feasibility is restored.
  Each test is one blossom call, so it is polynomial. Compiles; **never
  exercised**, because the winning config produces no matching conflicts. It
  only becomes relevant if CDCL revives the matching propagator (item 3).
* **`n_0`/`n_1` counting propagator — NOT BUILT.** Anchor-based, equality form
  (the values are determined, not bounded). odd835's precedent says this band
  contributes ~0% of conflicts, so expect little.
* **Witness-cached edge filtering — NOT BUILT.** Cache a perfect matching per
  allowed edge; it stays valid while none of its edges is OUT, which is a `p/2`
  status check instead of a blossom call. Sound by construction: a cache hit can
  only *skip* a removal, never cause one. Only matters if CDCL revives filtering.
* **Re-run the propagator ladder after CDCL lands.** Correctly sequenced — it
  cannot be closed until CDCL exists.

## Gate (amended)

1. ~~**v=15 in seconds.**~~ **MET** — 13m36s, not seconds, but exhausted and
   independently reproduced. See Calibration above.
2. **v=17 with a checked LRAT certificate.** This — not v=15 — is the honest
   predictor for v=21: 476 blocks against 273. Östergård–Pottonen closed it by
   classification, without proof logging, so a certified refutation that does
   not route through years of `S(3,4,16)` classification is a standalone
   artifact worth having **even if v=21 never falls**.
3. Only then spend anything on v=21.

## Closed routes (do not re-open)

* Triple-intersection double counting, single-design and large-set forms, with
  complement closure, fine 4-part profiles and partition capacities: **sat at
  every j**, no exclusion for k=16. Calibrated against k=10, where it is also
  blind — that kill goes through derived designs.
* `S(5,6,22)`: the "v = p+5, p prime ≡ 3 mod 4" pattern is a numerical artifact
  of `v = q+1`, `q ≡ 3 (mod 4)` a prime power, admitting `PSL(2,q)`. No
  nonexistence theorem. `S(5,6,22)` is OPEN and larger than `S(4,5,21)`
  (4,389 blocks vs 1,197), so it is not the target.
* `N_j`/`M_j` non-integrality kills `k = 8` and `k = 14` outright; `k = 16` is
  integral, so no divisibility shortcut exists there.
