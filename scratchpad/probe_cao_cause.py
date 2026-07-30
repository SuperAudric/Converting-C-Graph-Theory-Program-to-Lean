#!/usr/bin/env python3
"""M3 -- INSTRUMENT THE FEEDBACK LOOP (doc §12.6 M3).  The mechanism, not the round number.

§12.3 proves the ROUND-1 BARRIER: the round-1 signature of (v,u) is an intersection number of the
coherent X, identical across the X-class, so the base point learns NOTHING directly.  The marking
must travel out to far pairs and come back.  Nobody has measured WHICH far split does the work.

This extracts, for each fused orbital pair, the exact CAUSE CHAIN:

  at the round r* where (v,u) and (v,w) first separate, their signatures differ, and the
  difference is witnessed by specific TRIANGLE TYPES (c1, c2) = (class of (v,x), class of (x,u))
  whose multiplicity differs.  That is literally §12.3's triangle type, so the witness is the
  mechanism.  Each witness class is then traced to its BIRTH round, and the latest-born one is
  recursively explained the same way -- terminating at round 0, where the only new information is
  v's own flag.

Everything is counted from the COHERENT X (not from the raw colouring) -- see §12.3's convention
box: counting from raw conflates 'build X' (unbounded in diameter) with 'the extension' (the term
this measures).
"""
import sys
from collections import defaultdict, Counter
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, all_isos, orbits
from probe_cao_induction import orbital_partition, shrikhande, chang, rook, T8
from probe_cao_net import net
from probe_cao_diameter import prounds, init_pairs


def close_pairs(n, col0):
    rs = []
    for r, c in prounds(n, col0, cap=25):
        rs.append(c)
    return rs


def classes_of(n, col):
    d = defaultdict(set)
    for i in range(n * n):
        d[col[i]].add(i)
    return {frozenset(s) for s in d.values()}


def birth(rounds, r, c, n, cache):
    """First round at which this pair-class already exists as a full class."""
    P = frozenset(i for i in range(n * n) if rounds[r][i] == c)
    for r0 in range(r + 1):
        if r0 not in cache:
            cache[r0] = classes_of(n, rounds[r0])
        if P in cache[r0]:
            return r0, P
    return r, P


def describe(P, n, v):
    """Is this pair-class on v's row / column, and what does it look like?"""
    onrow = any(i // n == v for i in P)
    oncol = any(i % n == v for i in P)
    diag = all(i // n == i % n for i in P)
    tag = "DIAG" if diag else ("v-ROW" if onrow else ("v-COL" if oncol else "FAR"))
    return f"{tag} |{len(P)}|"


def witness(rounds, r, n, p, q):
    """The triangle types whose multiplicity distinguishes pair p from pair q at round r."""
    prev = rounds[r - 1]
    a, b = p // n, p % n
    c, d = q // n, q % n
    Sp = Counter((prev[a * n + x], prev[x * n + b]) for x in range(n))
    Sq = Counter((prev[c * n + x], prev[x * n + d]) for x in range(n))
    diff = {k: Sp[k] - Sq[k] for k in set(Sp) | set(Sq) if Sp[k] != Sq[k]}
    return sorted(diff.items(), key=lambda kv: -abs(kv[1]))


def chain(rounds, n, v, p, q, depth=0, maxdepth=4, cache=None, seen=None):
    """Recursively explain why p and q separated, following the latest-born witness."""
    cache = cache if cache is not None else {}
    seen = seen if seen is not None else set()
    r = next((i for i in range(len(rounds)) if rounds[i][p] != rounds[i][q]), None)
    if r is None or r == 0 or depth > maxdepth:
        return
    ws = witness(rounds, r, n, p, q)
    if not ws:
        return
    (c1, c2), dl = ws[0]
    b1, P1 = birth(rounds, r - 1, c1, n, cache)
    b2, P2 = birth(rounds, r - 1, c2, n, cache)
    pad = "     " + "  " * depth
    print(f"{pad}round {r}: pairs ({p//n},{p%n}) vs ({q//n},{q%n}) split; "
          f"witness triangle type (c1,c2) mult diff {dl:+d}")
    print(f"{pad}   c1 = {describe(P1, n, v)} born r{b1}   "
          f"c2 = {describe(P2, n, v)} born r{b2}   [{len(ws)} differing types]")
    # recurse into the later-born witness class: why did IT split?
    late = (b1, P1, c1) if b1 >= b2 else (b2, P2, c2)
    bl, PL, cl = late
    if bl == 0 or cl in seen:
        print(f"{pad}   -> the deciding class is present at round 0 "
              f"(only new information there is v's flag): CHAIN GROUNDED")
        return
    seen.add(cl)
    # find a sibling: a pair that shared PL's class at round bl-1 but left it
    par = rounds[bl - 1][next(iter(PL))]
    sib = next((i for i in range(n * n)
                if rounds[bl - 1][i] == par and i not in PL), None)
    if sib is None:
        print(f"{pad}   -> deciding class was NOT split from a parent (initial data): GROUNDED")
        return
    print(f"{pad}   -> the deciding class is {describe(PL, n, v)}, born r{bl}; why did it split?")
    chain(rounds, n, v, next(iter(PL)), sib, depth + 1, maxdepth, cache, seen)


def analyse(lab, n, adj, v=0):
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    orb = orbits(n, A)
    m = {}
    oc = [m.setdefault(orb[x], len(m)) for x in range(n)]
    X = close_pairs(n, init_pairs(n, adj, oc))[-1]
    orbl = orbital_partition(n, A)
    byc = defaultdict(set)
    for i in range(n * n):
        byc[X[i]].add(orbl[i])
    fused = {c: o for c, o in byc.items() if len(o) > 1}
    print(f"\n=== {lab}  n={n} |Aut|={len(A)} ===")
    print(f"  root: X-classes {len(set(X))}, orbitals {len(set(orbl))}, fused {len(fused)}")
    if not fused:
        print("  schurian root -- §12.2 discharges it, nothing to explain")
        return
    ini, col0 = {}, [0] * (n * n)
    for a in range(n):
        for b in range(n):
            k = (X[a * n + b], a == v, b == v)
            col0[a * n + b] = ini.setdefault(k, len(ini))
    rounds = close_pairs(n, col0)
    print(f"  extension from coherent X: {len(rounds) - 1} rounds to fixpoint")
    for c in sorted(fused):
        fib = defaultdict(list)
        for u in range(n):
            if X[v * n + u] == c:
                fib[orbl[v * n + u]].append(u)
        if len(fib) < 2:
            continue
        reps = [x[0] for x in fib.values()]
        u, w = reps[0], reps[1]
        print(f"  -- fused X-class {c} on v={v}'s row, fibres {sorted(len(x) for x in fib.values())}:")
        chain(rounds, n, v, v * n + u, v * n + w)


if __name__ == "__main__":
    analyse("Shrikhande", *shrikhande())
    analyse("net(Z4) = CFI[K4]-tw", *net((4,))[:2])
    analyse("Chang-2 (C8)", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
