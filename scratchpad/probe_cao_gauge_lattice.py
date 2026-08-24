"""Which gauges can a Construction-C frame have if the root is to stay ONE orbit?

Aut(E) = gauge x| S_L, so the gauge H must be an S_L-INVARIANT GF(2) subspace of the
edge space of K_L.  Enumerate that lattice exactly (proper RREF canonical forms).
"""
import itertools, sys, networkx as nx

def slots(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]

def perm_bitmaps(n):
    S = slots(n); idx = {s: k for k, s in enumerate(S)}
    return [[idx[tuple(sorted((p[i], p[j])))] for (i, j) in S]
            for p in itertools.permutations(range(n))]

def rref(vectors):
    """canonical RREF basis of the GF(2) span -> distinct tuple iff distinct subspace"""
    basis = {}
    for v in vectors:
        while v:
            h = v.bit_length() - 1
            if h in basis: v ^= basis[h]
            else: basis[h] = v; break
    for h in sorted(basis):                       # back-substitute
        for g in sorted(basis):
            if g > h and (basis[g] >> h) & 1: basis[g] ^= basis[h]
    return tuple(sorted(basis.values(), reverse=True))

def module_of(v, perms):
    bits = [i for i in range(v.bit_length()) if (v >> i) & 1]
    orb = set()
    for pm in perms:
        w = 0
        for i in bits: w |= 1 << pm[i]
        orb.add(w)
    return rref(orb)

def cut_basis(n):
    S = slots(n); idx = {s: k for k, s in enumerate(S)}
    out = []
    for k in range(n):
        v = 0
        for (i, j) in S:
            if (i == k) != (j == k): v |= 1 << idx[(i, j)]
        out.append(v)
    return out

def cycle_dim(n): return n * (n - 1) // 2 - (n - 1)

def iso_reps(n):
    S = slots(n); idx = {s: k for k, s in enumerate(S)}
    reps = []
    for G in nx.graph_atlas_g():
        if G.number_of_nodes() == n and G.number_of_edges() > 0:
            v = 0
            for (a, b) in G.edges(): v |= 1 << idx[tuple(sorted((a, b)))]
            reps.append(v)
    return reps

for n in [int(x) for x in sys.argv[1:]]:
    d = n * (n - 1) // 2
    perms = perm_bitmaps(n)
    cyc = {module_of(v, perms) for v in iso_reps(n)}
    lattice, frontier = set(cyc), set(cyc)
    while frontier:
        new = set()
        for a in frontier:
            for b in cyc:
                s = rref(list(a) + list(b))
                if s not in lattice: new.add(s)
        lattice |= new; frontier = new
    lattice.add(())                                       # the trivial gauge
    cut = rref(cut_basis(n))
    sizes = sorted(len(b) for b in lattice)
    print(f"n={n} edge-dim {d}: {len(lattice)} S_n-invariant subgroups, dims {sizes}"
          f" | cut-space dim {len(cut)} (invariant: {cut in lattice})"
          f" | cycle-space dim {cycle_dim(n)}")
    print(f"      smallest NON-TRIVIAL gauge sizes: "
          f"{[2**k for k in sizes if k > 0][:4]} ... full = 2^{d}")
