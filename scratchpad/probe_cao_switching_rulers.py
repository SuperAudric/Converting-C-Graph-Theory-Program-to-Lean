"""Ruler-freeness of a switching class, measured at 2-WL (the Lean hypothesis),
not 1-WL.  1-WL-discrete => 2-WL-discrete, so the earlier 1-WL counts were only a
LOWER bound on the number of rulers.
"""
import random, sys, time, networkx as nx

def slots(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]

def cut_vectors(n):
    S = slots(n); idx = {s: k for k, s in enumerate(S)}
    out = []
    for m in range(1 << (n - 1)):
        sub = {i for i in range(n - 1) if (m >> i) & 1}
        v = 0
        for (i, j) in S:
            if (i in sub) != (j in sub): v |= 1 << idx[(i, j)]
        out.append(v)
    return out

def adjmat(mask, n, S):
    A = [[0]*n for _ in range(n)]
    for k, (i, j) in enumerate(S):
        if (mask >> k) & 1: A[i][j] = A[j][i] = 1
    return A

def wl2_discrete(mask, n, S):
    A = adjmat(mask, n, S)
    col = [[A[i][j] * 2 + (1 if i == j else 0) for j in range(n)] for i in range(n)]
    prev = len({col[i][j] for i in range(n) for j in range(n)})
    for _ in range(n * n):
        keys = [[None]*n for _ in range(n)]
        for i in range(n):
            ci = col[i]
            for j in range(n):
                keys[i][j] = (ci[j], tuple(sorted((ci[k], col[k][j]) for k in range(n))))
        rank = {k: r for r, k in enumerate(sorted({keys[i][j] for i in range(n) for j in range(n)}))}
        col = [[rank[keys[i][j]] for j in range(n)] for i in range(n)]
        m = len(rank)
        if m == prev: break
        prev = m
    return prev == n * n

def mask_of(G, n):
    S = slots(n); idx = {s: k for k, s in enumerate(S)}
    m = 0
    for a, b in G.edges(): m |= 1 << idx[tuple(sorted((a, b)))]
    return m

def rulers_in_class(mask, n, sample=None, seed=0):
    S = slots(n); cuts = cut_vectors(n)
    if sample and sample < len(cuts):
        cuts = random.Random(seed).sample(cuts, sample)
    return sum(1 for c in cuts if wl2_discrete(mask ^ c, n, S)), len(cuts)

def shrikhande():
    G = nx.Graph(); Z = [(i, j) for i in range(4) for j in range(4)]
    D = {(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)}
    for x, a in enumerate(Z):
        for y, b in enumerate(Z):
            if x < y and (((b[0]-a[0]) % 4, (b[1]-a[1]) % 4) in D or
                          ((a[0]-b[0]) % 4, (a[1]-b[1]) % 4) in D):
                G.add_edge(x, y)
    return G

t0 = time.time()
named = {
    8:  {"K8": nx.complete_graph(8), "C8": nx.cycle_graph(8),
         "K4,4": nx.complete_bipartite_graph(4,4), "Q3": nx.hypercube_graph(3)},
    10: {"Petersen": nx.petersen_graph(), "K5,5": nx.complete_bipartite_graph(5,5),
         "K10": nx.complete_graph(10), "C10": nx.cycle_graph(10)},
}
print("=== 2-WL rulers in DESIGNED switching classes (exhaustive) ===")
for n, gs in named.items():
    for name, G in gs.items():
        G = nx.convert_node_labels_to_integers(G)
        k, tot = rulers_in_class(mask_of(G, n), n)
        print(f"  n={n:2d} {name:9s}: 2-WL-discrete members {k}/{tot}")

print("=== n=16 (sampled 400 of 32768 members per class) ===")
rook = nx.convert_node_labels_to_integers(
    nx.cartesian_product(nx.complete_graph(4), nx.complete_graph(4)))
for name, G in {"rook4x4": rook, "Shrikhande": shrikhande(),
                "Clebsch": nx.complement(rook), "K16": nx.complete_graph(16),
                "Q4": nx.convert_node_labels_to_integers(nx.hypercube_graph(4))}.items():
    k, tot = rulers_in_class(mask_of(G, 16), 16, sample=400)
    print(f"  n=16 {name:11s}: 2-WL-discrete members {k}/{tot} sampled")
print(f"[{time.time()-t0:.0f}s]")

print("=== is Shrikhande in rook(4,4)'s switching class? ===")
S = slots(16); rm = mask_of(rook, 16); shri = shrikhande(); hits = 0
for c in cut_vectors(16):
    m = rm ^ c
    deg = [0]*16
    for k, (i, j) in enumerate(S):
        if (m >> k) & 1: deg[i] += 1; deg[j] += 1
    if sorted(deg) != [6]*16: continue
    G = nx.Graph(); G.add_nodes_from(range(16))
    G.add_edges_from(S[k] for k in range(len(S)) if (m >> k) & 1)
    if nx.is_isomorphic(G, shri): hits += 1
print(f"  switchings of rook(4,4) isomorphic to Shrikhande: {hits}/32768")
