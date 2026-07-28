"""Emit S(4,5,v) CNF with level-1 AND level-2 symmetry breaking.

One boolean per 5-subset. Per 4-subset, exactly-one over its v-4 extensions
(ALO + pairwise AMO). Then unit clauses for:
  level 1 -- the {0,1,2} spread: blocks {0,1,2,a,a+1}
  level 2 -- the {0,1,3} spread for one canonical branch (all parts >= 2)

Level 2 is a DISJUNCTION over branches, so one CNF per branch, and the instance
is UNSAT only if every branch is UNSAT.
"""
import itertools
import sys


def parts_ge2(n, mx=None):
    if mx is None:
        mx = n
    if n == 0:
        yield ()
    for q in range(min(n, mx), 1, -1):
        if n - q == 1:
            continue
        for r in parts_ge2(n - q, q):
            yield (q,) + r


def gen(v, lam):
    fives = list(itertools.combinations(range(v), 5))
    var = {c: i + 1 for i, c in enumerate(fives)}
    cls = []
    for T in itertools.combinations(range(v), 4):
        opts = [var[tuple(sorted(T + (x,)))] for x in range(v) if x not in T]
        cls.append(opts)
        for a, b in itertools.combinations(opts, 2):
            cls.append([-a, -b])
    units = []
    for a in range(3, v, 2):                     # level 1
        units.append(tuple(sorted((0, 1, 2, a, a + 1))))
    base = list(range(5, v))                     # level 2
    off = 0
    for l in lam:
        idx = [(base[2 * (off + i)], base[2 * (off + i) + 1]) for i in range(l)]
        for i in range(l):
            b = idx[i][1]
            a = idx[(i + 1) % l][0]
            units.append(tuple(sorted((0, 1, 3, a, b))))
        off += l
    for u in units:
        cls.append([var[u]])
    return len(var), cls, len(units)


v = int(sys.argv[1])
n = (v - 3) // 2 - 1
branches = list(parts_ge2(n))
print("v=%d  level-2 branches (all parts >= 2): %d  %s" % (v, len(branches), branches))
for bi, lam in enumerate(branches):
    nv, cls, nu = gen(v, lam)
    path = "s45_%d_b%d.cnf" % (v, bi)
    with open(path, "w") as f:
        f.write("p cnf %d %d\n" % (nv, len(cls)))
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("  branch %d %s -> %s  (%d vars, %d clauses, %d units fixed)"
          % (bi, lam, path, nv, len(cls), nu))
