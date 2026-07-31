#!/usr/bin/env python3
"""M3 FOLLOW-UPS (doc §12.6 M3): (a) ABLATION -- is the cause a single far class, or
over-determined?  (b) POPULATION -- does the depth-3 / (v-ROW r0, FAR r2) law survive inputs
that are not diameter-2 SRGs?

(a) A distinction between two classes c,c' of the round-(r*-1) colouring is NECESSARY when
    merging them makes the target signatures agree (so the separation dies).  If NO single merge
    kills it, the cause is over-determined and "the specific far class whose split causes the
    separation" is not well posed -- the instrument's max-|delta| pick is one path among many.
(b) Deficient roots beyond diameter 2 come from Shrikhande [] C_m (the Doob-graph shape), whose
    automorphism group is built programmatically (Sabidussi-Vizing), plus the VT witness.
"""
import sys
from collections import defaultdict, Counter
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, all_isos, orbits
from probe_cao_induction import orbital_partition, shrikhande, chang
from probe_cao_net import net
from probe_cao_diameter import prounds, init_pairs, bfs_ecc
from probe_cao_diam_deficient import cart, cyc
from probe_cao_cause import close_pairs, birth, describe, witness, classes_of


def ablate(n, rounds, v, u, w):
    """Which class distinctions at round r*-1 are NECESSARY for the separation?"""
    r = next(i for i in range(len(rounds)) if rounds[i][v * n + u] != rounds[i][v * n + w])
    col = rounds[r - 1]
    cls = sorted(set(col))

    def seps(g):
        Su = Counter((g[col[v * n + x]], g[col[x * n + u]]) for x in range(n))
        Sw = Counter((g[col[v * n + x]], g[col[x * n + w]]) for x in range(n))
        return Su != Sw

    base = {c: c for c in cls}
    assert seps(base), "target does not separate at r*"
    nec = []
    for i, c1 in enumerate(cls):
        for c2 in cls[i + 1:]:
            g = dict(base)
            g[c2] = c1
            if not seps(g):
                nec.append((c1, c2))
    # how many merges (greedy, random-free: lowest-index first) before separation dies
    g, merged = dict(base), 0
    reps = list(cls)
    for i, c1 in enumerate(cls):
        for c2 in cls[i + 1:]:
            if g[c2] == g[c1]:
                continue
            old = g[c2]
            for k in g:
                if g[k] == old:
                    g[k] = g[c1]
            merged += 1
            if not seps(g):
                return r, len(cls), nec, merged
    return r, len(cls), nec, None


def analyse_gens(lab, n, adj, gens, v=0, do_ablate=True):
    orb = orbits(n, gens)
    m = {}
    oc = [m.setdefault(orb[x], len(m)) for x in range(n)]
    X = close_pairs(n, init_pairs(n, adj, oc))[-1]
    orbl = orbital_partition(n, gens)
    byc = defaultdict(set)
    for i in range(n * n):
        byc[X[i]].add(orbl[i])
    fused = {c: o for c, o in byc.items() if len(o) > 1}
    print(f"\n=== {lab}  n={n} diam={bfs_ecc(n, adj, 0)} ===")
    print(f"  X-classes {len(set(X))}, orbitals {len(set(orbl))}, fused {len(fused)}")
    if not fused:
        print("  schurian root -- nothing to explain")
        return
    ini, col0 = {}, [0] * (n * n)
    for a in range(n):
        for b in range(n):
            k = (X[a * n + b], a == v, b == v)
            col0[a * n + b] = ini.setdefault(k, len(ini))
    rounds = close_pairs(n, col0)
    cache = {}
    for c in sorted(fused):
        fib = defaultdict(list)
        for x in range(n):
            if X[v * n + x] == c:
                fib[orbl[v * n + x]].append(x)
        if len(fib) < 2:
            continue
        reps = [y[0] for y in fib.values()]
        u, w = reps[0], reps[1]
        p, q = v * n + u, v * n + w
        r = next((i for i in range(len(rounds)) if rounds[i][p] != rounds[i][q]), None)
        if r is None:
            print(f"  class {c}: NEVER separates"); continue
        ws = witness(rounds, r, n, p, q)
        (c1, c2), dl = ws[0]
        b1, P1 = birth(rounds, r - 1, c1, n, cache)
        b2, P2 = birth(rounds, r - 1, c2, n, cache)
        line = (f"  class {c} fibres {sorted(len(y) for y in fib.values())}: sep at r{r}, "
                f"witness ({describe(P1,n,v)} r{b1}, {describe(P2,n,v)} r{b2}), "
                f"{len(ws)} differing types")
        if do_ablate:
            rr, ncls, nec, merged = ablate(n, rounds, v, u, w)
            line += (f"\n      ABLATION: {ncls} classes at r{rr-1}; "
                     f"single merges that KILL the separation: {len(nec)}"
                     f"{' ' + str(nec[:3]) if nec else ' (NONE -> over-determined)'}; "
                     f"greedy merges until it dies: {merged}")
        print(line)


def analyse_auts(lab, n, adj, v=0, **kw):
    A = all_isos(n, adj, wl(n, adj, [0]*n), wl(n, adj, [0]*n), limit=3_000_000)
    analyse_gens(lab, n, adj, A, v, **kw)


def shr_prod(m):
    n1, a1 = shrikhande()
    n2, a2 = cyc(m)
    N, A = cart(n1, a1, n2, a2)
    S = all_isos(n1, a1, wl(n1, a1, [0]*n1), wl(n1, a1, [0]*n1), limit=3_000_000)
    D = [tuple((j+1) % m for j in range(m)), tuple((-j) % m for j in range(m))]
    gens = [tuple(s[i]*n2 + j for i in range(n1) for j in range(n2)) for s in S]
    gens += [tuple(i*n2 + t[j] for i in range(n1) for j in range(n2)) for t in D]
    return N, A, gens


if __name__ == "__main__":
    print("### (a) ABLATION on the original diameter-2 deficient roots")
    analyse_auts("Shrikhande", *shrikhande())
    analyse_auts("net(Z4)", *net((4,))[:2])
    analyse_auts("Chang-2", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
    print("\n### (b) POPULATION beyond diameter 2 -- Shrikhande [] C_m (Doob shape)")
    for m in (3, 5):
        N, A, gens = shr_prod(m)
        analyse_gens(f"Shrikhande [] C_{m}", N, A, gens)
