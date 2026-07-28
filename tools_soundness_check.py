"""Independent soundness verification of the level-2 orbit branching.

The claim under test is NOT the orbit decomposition (already verified). It is:

  COMPLETENESS: if any S(4,5,v) exists, then one exists satisfying
                level-1 (the {0,1,2} spread) AND one of the p(n) canonical
                level-2 representatives.

Four separate premises, tested separately:
  A. G1 = S({0,1,2}) x Aut(P) really stabilises the level-1 spread.
     Using a group LARGER than the true stabiliser would be unsound.
  B. the subgroup of G1 fixing T2={0,1,3} setwise acts on {5..v-1} as the FULL
     S_2 wr S_n.  If it acted as something smaller, p(n) reps would be too few.
  C. level-1 is WLOG: any labelled design can be relabelled into level-1 form.
  D. end to end: every level-1 design canonicalises to a design that is still
     valid, still level-1, and sits in exactly one branch.
"""
import itertools
import random
from math import factorial


def spread_blocks(v):
    return [frozenset((0, 1, 2, a, a + 1)) for a in range(3, v, 2)]


def residual_group(v):
    """S({0,1,2}) x Aut(P), as explicit permutations of [v]."""
    m = (v - 3) // 2
    pairs = [(3 + 2 * i, 4 + 2 * i) for i in range(m)]
    out = []
    for sig in itertools.permutations((0, 1, 2)):
        for pperm in itertools.permutations(range(m)):
            for flips in itertools.product((0, 1), repeat=m):
                g = [0] * v
                g[0], g[1], g[2] = sig
                for i, (a, b) in enumerate(pairs):
                    t = pairs[pperm[i]]
                    g[a], g[b] = (t[1], t[0]) if flips[i] else (t[0], t[1])
                out.append(tuple(g))
    return out


def apply_perm(g, blocks):
    return frozenset(frozenset(g[x] for x in b) for b in blocks)


def valid_design(bl, v):
    seen = set()
    for b in bl:
        if len(b) != 5:
            return False
        for q in itertools.combinations(sorted(b), 4):
            if q in seen:
                return False
            seen.add(q)
    return len(seen) == len(list(itertools.combinations(range(v), 4)))


# ------------------------------------------------------------------ A
print("A. does G1 actually stabilise the level-1 spread?")
for v in (11, 15):
    G1 = residual_group(v)
    m = (v - 3) // 2
    assert len(G1) == 6 * (2 ** m) * factorial(m)
    S = frozenset(spread_blocks(v))
    bad = sum(1 for g in G1 if apply_perm(g, S) != S)
    print("   v=%-3d |G1| = %-8d elements NOT preserving the spread: %d   %s"
          % (v, len(G1), bad, "OK" if bad == 0 else "UNSOUND"))
    assert bad == 0

v = 11
S = frozenset(spread_blocks(v))
full = set(p for p in itertools.permutations(range(v)) if apply_perm(p, S) == S)
G1s = set(residual_group(v))
print("   v=11 true stabiliser in S_11: %d   G1: %d   G1 <= stab: %s   equal: %s"
      % (len(full), len(G1s), G1s <= full, G1s == full))
assert G1s <= full

# ------------------------------------------------------------------ B
print("\nB. subgroup fixing T2={0,1,3}: full S_2 wr S_n on {5..v-1}?")
for v in (11, 15):
    m = (v - 3) // 2
    n = m - 1
    G1 = residual_group(v)
    T2 = frozenset((0, 1, 3))
    keep = [g for g in G1 if frozenset((g[0], g[1], g[3])) == T2]
    induced = set(tuple(g[x] for x in range(5, v)) for g in keep)
    exp_sub = 2 * (2 ** n) * factorial(n)
    exp_act = (2 ** n) * factorial(n)
    fix34 = all(g[3] == 3 and g[4] == 4 for g in keep)
    ok = len(keep) == exp_sub and len(induced) == exp_act and fix34
    print("   v=%-3d |stab(T2)| = %-6d (expect %-6d)  distinct actions on {5..%d} = %-5d "
          "(expect %-5d)  all fix 3,4: %s   %s"
          % (v, len(keep), exp_sub, v - 1, len(induced), exp_act, fix34,
             "OK" if ok else "MISMATCH"))
    assert ok

# ------------------------------------------------------------------ C/D
print("\nC/D. end to end at v=11 (the only v in range where a design exists)")
v = 11
fives = [frozenset(c) for c in itertools.combinations(range(v), 5)]
cover = {}
for f in fives:
    for q in itertools.combinations(sorted(f), 4):
        cover.setdefault(q, []).append(f)
QUADS = list(itertools.combinations(range(v), 4))


def enumerate_designs(fixed):
    covered = {}
    chosen = list(fixed)
    for f in fixed:
        for q in itertools.combinations(sorted(f), 4):
            if q in covered:
                return []
            covered[q] = f
    out = []

    def rec():
        best, bopts = None, None
        for q in QUADS:
            if q in covered:
                continue
            opts = [f for f in cover[q]
                    if not any(qq in covered
                               for qq in itertools.combinations(sorted(f), 4))]
            if best is None or len(opts) < len(bopts):
                best, bopts = q, opts
                if not opts:
                    break
        if best is None:
            out.append(frozenset(chosen))
            return
        for f in bopts:
            qs = list(itertools.combinations(sorted(f), 4))
            for qq in qs:
                covered[qq] = f
            chosen.append(f)
            rec()
            chosen.pop()
            for qq in qs:
                del covered[qq]
    rec()
    return out


designs = enumerate_designs(spread_blocks(v))
print("   S(4,5,11) designs containing the level-1 spread: %d" % len(designs))
assert designs and all(valid_design(d, v) for d in designs)

random.seed(7)
D0 = next(iter(designs))
c_ok = c_try = 0
for _ in range(300):
    p = list(range(v))
    random.shuffle(p)
    Dp = apply_perm(p, D0)
    thru = [b for b in Dp if {0, 1, 2} <= b]
    rest = sorted(set(range(v)) - {0, 1, 2})
    mates = {}
    for b in thru:
        x, y = sorted(b - {0, 1, 2})
        mates[x] = y
        mates[y] = x
    assert len(thru) == (v - 3) // 2 and set(mates) == set(rest)
    c_try += 1
    g = [0] * v
    g[0], g[1], g[2] = 0, 1, 2
    nxt = 3
    done = set()
    for x in rest:
        if x in done:
            continue
        y = mates[x]
        done |= {x, y}
        g[x] = nxt
        g[y] = nxt + 1
        nxt += 2
    Dn = apply_perm(g, Dp)
    if valid_design(Dn, v) and frozenset(spread_blocks(v)) <= Dn:
        c_ok += 1
print("   C: random relabellings renormalised into level-1 form: %d/%d  %s"
      % (c_ok, c_try, "OK" if c_ok == c_try == 300 else "FAILED"))
assert c_ok == 300

m = (v - 3) // 2
n = m - 1


def partitions(k, mx=None):
    if mx is None:
        mx = k
    if k == 0:
        yield ()
    for q in range(min(k, mx), 0, -1):
        for r in partitions(k - q, q):
            yield (q,) + r


LAMS = [tuple(sorted(l, reverse=True)) for l in partitions(n)]
base = list(range(5, v))


def canon_matching(lam):
    mate = {}
    off = 0
    for l in lam:
        idx = [(base[2 * (off + i)], base[2 * (off + i) + 1]) for i in range(l)]
        for i in range(l):
            if l == 1:
                mate[idx[0][0]] = idx[0][1]
                mate[idx[0][1]] = idx[0][0]
            else:
                b = idx[i][1]
                a = idx[(i + 1) % l][0]
                mate[b] = a
                mate[a] = b
        off += l
    return mate


def cyc_type(mate):
    P = {}
    for i in range(0, len(base), 2):
        P[base[i]] = base[i + 1]
        P[base[i + 1]] = base[i]
    seen, out = set(), []
    for s in base:
        if s in seen:
            continue
        L, x = 0, s
        while x not in seen:
            seen.add(x)
            seen.add(P[x])
            x = mate[P[x]]
            L += 1
        out.append(L)
    return tuple(sorted(out, reverse=True))


T2 = {0, 1, 3}
G1 = residual_group(v)
stabT2 = [g for g in G1 if {g[0], g[1], g[3]} == T2]
CANON = {l: canon_matching(l) for l in LAMS}
assert sorted(cyc_type(CANON[l]) for l in LAMS) == sorted(LAMS)

types_seen = {}
d_ok = 0
for D in designs:
    thru = [b for b in D if T2 <= b]
    assert len(thru) == m
    mates = {}
    for b in thru:
        x, y = sorted(b - T2)
        mates[x] = y
        mates[y] = x
    assert mates[2] == 4, "the shared level-1 block must pin 2<->4"
    Mp = {x: y for x, y in mates.items() if x >= 5}
    ct = cyc_type(Mp)
    types_seen[ct] = types_seen.get(ct, 0) + 1
    target = CANON[ct]
    found = None
    for g in stabT2:
        if all(g[Mp[x]] == target[g[x]] for x in base):
            found = g
            break
    if found is None:
        continue
    Dc = apply_perm(found, D)
    m2 = {}
    for b in [b for b in Dc if T2 <= b]:
        x, y = sorted(b - T2)
        m2[x] = y
        m2[y] = x
    if (valid_design(Dc, v) and frozenset(spread_blocks(v)) <= Dc
            and {x: y for x, y in m2.items() if x >= 5} == target):
        d_ok += 1
print("   D: canonicalised into a branch, image still a valid level-1 design: %d/%d  %s"
      % (d_ok, len(designs), "OK" if d_ok == len(designs) else "FAILED"))
print("      level-2 cycle types occurring: %s" % dict(sorted(types_seen.items())))
print("      branch set is p(%d) = %d reps: %s" % (n, len(LAMS), LAMS))
assert d_ok == len(designs)

# negative control: drop the within-pair swaps -> too small a group
wrong = [g for g in stabT2 if all(g[base[2 * i]] < g[base[2 * i + 1]] for i in range(n))]
lost = 0
for D in designs:
    mates = {}
    for b in [b for b in D if T2 <= b]:
        x, y = sorted(b - T2)
        mates[x] = y
        mates[y] = x
    Mp = {x: y for x, y in mates.items() if x >= 5}
    ct = cyc_type(Mp)
    if not any(all(g[Mp[x]] == CANON[ct][g[x]] for x in base) for g in wrong):
        lost += 1
print("   negative control: with the too-small group (|G|=%d vs %d), designs that can "
      "NO LONGER reach their rep: %d/%d  %s"
      % (len(wrong), len(stabT2), lost, len(designs),
         "<- the test HAS power" if lost > 0 else "(control weak)"))

print("\nVERDICT: level-2 orbit branching is COMPLETE.")
print("  A,B verified exhaustively at v=11 and v=15; C,D end to end at v=11.")
