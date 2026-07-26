#!/usr/bin/env python3
"""
PROBE: is a DUAL resolver possible — ONE descent that CONSUMES a symmetry when the
leaves agree and CERTIFIES the rigid decision when they don't?

The disconnect (user's framing): `deepen`/`DeepenAnchor` validates that the deepest
nodes are IDENTICAL (twist verifies -> symmetry consumed). Force needs the OPPOSITE
(the decision is real). Today deepen's failure is only a sound over-split, never a
rigidity certificate — so the two sides cannot be unified.

Candidate fix measured here: replace deepen's *index* pick at each level by MIN OVER
THE CELL, pruned by the automorphisms the ties themselves produce. Then ONE object —
the leaf certificate cert(v) — carries both verdicts:

    cert(a) == cert(b)  ==>  the twist  pi_b^{-1} pi_a  is a verified automorphism  (CONSUME)
    cert(a) != cert(b)  ==>  cert IS an equivariant separating Key                  (FORCE)

Measured:
  (1) ①  EQUIVARIANCE  — cert invariant under relabelling? (min-over-cell vs greedy index-pick)
  (2) DUALITY          — does EVERY cert-tie actually yield a VERIFIED path-fixing automorphism?
                         (if yes, no tie is ever a "stall": the tie reading is complete)
  (3) COST             — leaves explored pruned/unpruned; scaling over a rigid family
  (4) VERDICT PROFILE  — per node: cert-classes, and how many are singleton (rigid decisions)
"""
import sys, random
from itertools import combinations, product
from collections import defaultdict, Counter

sys.setrecursionlimit(10000)

# ---------------------------------------------------------------- graph families
def circ(m, offs=(0, 1, 3)):
    return [[1 if any((i + o) % m == w for o in offs) else 0 for w in range(m)]
            for i in range(m)]

FANO = [[1,1,1,0,0,0,0],[1,0,0,1,1,0,0],[1,0,0,0,0,1,1],
        [0,1,0,1,0,1,0],[0,1,0,0,1,0,1],[0,0,1,1,0,0,1],[0,0,1,0,1,1,0]]
MIXED = [[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]

def rand_incidence(V, W, deg, seed):
    """Random V x W incidence, deg ones per row; retried until F2-kernel is trivial."""
    rnd = random.Random(seed)
    for _ in range(4000):
        rowset = set()
        while len(rowset) < V:
            rowset.add(tuple(sorted(rnd.sample(range(W), deg))))
            if len(rowset) > 3 * V: break
        rows_ = sorted(rowset)[:V]
        if len(rows_) < V: continue
        A = [[1 if w in r else 0 for w in range(W)] for r in rows_]
        # trivial kernel over F2  <=>  rank == W  (no gauge: forces graph rigidity candidate)
        R = [r[:] for r in A]; r = 0
        for c in range(W):
            pr = next((i for i in range(r, len(R)) if R[i][c]), None)
            if pr is None: continue
            R[r], R[pr] = R[pr], R[r]
            for i in range(len(R)):
                if i != r and R[i][c]:
                    R[i] = [a ^ b for a, b in zip(R[i], R[r])]
            r += 1
        if r == W:
            return A
    raise RuntimeError("no full-rank incidence found")

def build_mp(A):
    """Multipede over incidence A (rows = constraints, cols = segments)."""
    V, W = len(A), len(A[0])
    Nb = [[w for w in range(W) if A[v][w]] for v in range(V)]
    idx = 0; aI = {}; bI = {}; midI = {}
    for w in range(W):
        aI[w] = idx; idx += 1
        bI[w] = idx; idx += 1
    for v in range(V):
        for k in range(0, len(Nb[v]) + 1, 2):
            for c in combinations(Nb[v], k):
                midI[(v, frozenset(c))] = idx; idx += 1
    n = idx
    adj = [[0] * n for _ in range(n)]
    for (v, Aset), mi in midI.items():
        for w in Nb[v]:
            t = aI[w] if w in Aset else bI[w]
            adj[mi][t] = 1; adj[t][mi] = 1
    return n, adj

def build_cfi(m, twist=False):
    """CFI over a cycle C_m (the classic 2^{m-1} gauge, WL-hard)."""
    # each cycle edge -> a pair of wire vertices; each cycle node -> even-parity gadget
    idx = 0; wire = {}
    edges = [(i, (i + 1) % m) for i in range(m)]
    for e in edges:
        wire[(e, 0)] = idx; idx += 1
        wire[(e, 1)] = idx; idx += 1
    gadget = {}
    for i in range(m):
        inc = [e for e in edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2 == 0:
                gadget[(i, bits)] = idx; idx += 1
    n = idx
    adj = [[0] * n for _ in range(n)]
    for i in range(m):
        inc = [e for e in edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2: continue
            g = gadget[(i, bits)]
            for k, e in enumerate(inc):
                b = bits[k]
                if twist and e == edges[0] and i == edges[0][1]:
                    b ^= 1
                t = wire[(e, b)]
                adj[g][t] = 1; adj[t][g] = 1
    return n, adj

def relabel(n, adj, sigma):
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            out[sigma[i]][sigma[j]] = adj[i][j]
    return out

# ---------------------------------------------------------------- 1-WL
def refine(n, adj, col):
    col = list(col)
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in range(n) if adj[v][u]))) for v in range(n)]
        order = sorted(set(sig)); rank = {s: i for i, s in enumerate(order)}
        new = [rank[sig[v]] for v in range(n)]
        if new == col: return col
        col = new

def indiv(n, col, v):
    sig = [(col[u], 0 if u == v else 1) for u in range(n)]
    order = sorted(set(sig)); rank = {s: i for i, s in enumerate(order)}
    return [rank[sig[u]] for u in range(n)]

def target_cell(n, col):
    """Lowest-id non-singleton cell — deepen's `chooseIdK`, whole-graph (track A)."""
    d = defaultdict(list)
    for v in range(n): d[col[v]].append(v)
    ns = [c for c in sorted(d) if len(d[c]) >= 2]
    return (ns[0], d[ns[0]]) if ns else (None, None)

# ---------------------------------------------------------------- perms
def is_aut(n, adj, s, col=None):
    if col is not None and any(col[s[i]] != col[i] for i in range(n)): return False
    for i in range(n):
        si = s[i]; ri = adj[i]; rs = adj[si]
        for j in range(n):
            if ri[j] != rs[s[j]]: return False
    return True

def orbits_of(n, gens):
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b: par[a] = b
    return [f(i) for i in range(n)]

def group_order(n, gens, cap=400000):
    if not gens: return 1
    idp = tuple(range(n)); seen = {idp}; frontier = [idp]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(n))
                if q not in seen:
                    seen.add(q); nxt.append(q)
                    if len(seen) > cap: return None
        frontier = nxt
    return len(seen)

# ---------------------------------------------------------------- the dual descent
class Ctx:
    def __init__(self, n, adj, prune=True, leafcap=300000):
        self.n, self.adj = n, adj
        self.prune = prune; self.leafcap = leafcap
        self.leaves = 0; self.pruned = 0; self.blown = False
        self.gens = []                # (perm, path) verified path-fixing automorphisms
        self.ties = 0; self.tie_fail = 0   # (2) DUALITY counters
        self.profile = []             # (depth, |C|, explored, cert-classes, singleton-classes)
        self.root = None

def certify(n, adj, col, parent):
    """Discrete colouring -> canonical form of the COLOURED graph + labelling."""
    lab = [0] * n
    for v in range(n): lab[col[v]] = v
    cert = (tuple(adj[lab[i]][lab[j]] for i in range(n) for j in range(i + 1, n)),
            tuple(parent[lab[i]] for i in range(n)))
    return cert, lab

def covered(ctx, v, explored, path):
    gens = [g for (g, gp) in ctx.gens if all(g[p] == p for p in path)]
    if not gens: return False
    seen = set(explored); frontier = list(explored)
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = g[x]
                if y not in seen:
                    if y == v: return True
                    seen.add(y); nxt.append(y)
        frontier = nxt
    return False

def canon(ctx, col, path, parent=None, depth=0, root=False):
    n, adj = ctx.n, ctx.adj
    col = refine(n, adj, col)
    if parent is None: parent = col
    cid, C = target_cell(n, col)
    if cid is None:
        ctx.leaves += 1
        if ctx.leaves > ctx.leafcap: ctx.blown = True
        return certify(n, adj, col, parent)
    best = None; explored = []; percert = {}
    for v in C:
        if ctx.blown: break
        if ctx.prune and explored and covered(ctx, v, explored, path):
            ctx.pruned += 1; continue
        explored.append(v)
        r = canon(ctx, indiv(n, col, v), path + [v], parent, depth + 1)
        if r is None: continue
        cert, lab = r
        percert[v] = cert
        if best is None or cert < best[0]:
            best = (cert, lab, v)
        elif cert == best[0]:
            # ---- the CONSUME reading: equal leaves => a twist; must VERIFY.
            ctx.ties += 1
            blab = best[1]
            s = [0] * n
            for i in range(n): s[lab[i]] = blab[i]
            if is_aut(n, adj, s, parent) and all(s[p] == p for p in path) and s[v] == best[2]:
                ctx.gens.append((s, tuple(path)))
            else:
                ctx.tie_fail += 1
    klass = defaultdict(list)
    for v, c in percert.items(): klass[c].append(v)
    ctx.profile.append((depth, len(C), len(explored), len(klass),
                        sum(1 for x in klass.values() if len(x) == 1)))
    if root: ctx.root = (C, percert, list(explored))
    return None if best is None else (best[0], best[1])

# ---------------------------------------------------------------- greedy = today's deepen
def greedy_cert(n, adj):
    """deepen's single path: lowest-id cell, LOWEST-INDEX member. Non-invariant by design."""
    col = refine(n, adj, [0] * n); parent = col
    for _ in range(n + 1):
        cid, C = target_cell(n, col)
        if cid is None: return certify(n, adj, col, parent)[0]
        col = refine(n, adj, indiv(n, col, min(C)))
    return None

# ---------------------------------------------------------------- driver
def analyse(name, n, adj, relabels=3, leafcap=200000, show=True):
    col0 = [0] * n
    ctx = Ctx(n, adj, prune=True, leafcap=leafcap)
    canon(ctx, col0, [], root=True)
    ctxU = Ctx(n, adj, prune=False, leafcap=leafcap)
    canon(ctxU, col0, [])
    allg = [g for (g, p) in ctx.gens]
    order = group_order(n, allg)
    orb = orbits_of(n, allg)
    Kv = sum(1 for v in range(n) if Counter(orb)[orb[v]] > 1)

    base = canon(Ctx(n, adj, prune=True, leafcap=leafcap), col0, [])[0]
    bg = greedy_cert(n, adj)
    okmin = okgre = True
    rnd = random.Random(7)
    for _ in range(relabels):
        s = list(range(n)); rnd.shuffle(s)
        a2 = relabel(n, adj, s)
        if canon(Ctx(n, a2, prune=True, leafcap=leafcap), [0] * n, [])[0] != base: okmin = False
        if greedy_cert(n, a2) != bg: okgre = False

    if show:
        print(f"\n===== {name}   n={n} =====")
        print(f"  (3) cost   : pruned leaves={ctx.leaves:>6} (skipped {ctx.pruned:>5})   "
              f"unpruned leaves={'>'+str(leafcap) if ctxU.blown else ctxU.leaves}")
        print(f"      consume: |Aut| from tie-generators = {order}   orbits={len(set(orb))}   "
              f"K(moved)={Kv}  R(Aut-fixed)={n - Kv}")
        print(f"  (1) ①      : min-over-cell cert INVARIANT = {okmin}     "
              f"greedy index-pick cert invariant = {okgre}")
        print(f"  (2) DUALITY: cert-ties={ctx.ties}  ties that FAILED to give a verified "
              f"path-fixing automorphism = {ctx.tie_fail}")
        nodes = len(ctx.profile)
        pure_sym = sum(1 for p in ctx.profile if p[3] == 1)
        pure_rig = sum(1 for p in ctx.profile if p[3] > 1 and p[3] == p[2])
        mixed = nodes - pure_sym - pure_rig
        print(f"  (4) nodes={nodes}: pure-SYMMETRY (1 cert class)={pure_sym}   "
              f"pure-RIGID (all certs distinct)={pure_rig}   MIXED={mixed}")
        C, percert, expl = ctx.root
        kl = defaultdict(list)
        for v, c in percert.items(): kl[c].append(v)
        print(f"      root cell |C|={len(C)} explored={len(expl)} -> {len(kl)} cert-class(es) "
              f"sizes={sorted(len(x) for x in kl.values())}")
    return dict(n=n, leaves=ctx.leaves, unpruned=(None if ctxU.blown else ctxU.leaves),
                aut=order, ties=ctx.ties, tie_fail=ctx.tie_fail, ok=okmin, okgre=okgre,
                R=n - Kv, nodes=len(ctx.profile))


def build_cfi_base(base_edges, m, twist=False):
    """CFI over an arbitrary base graph (edges = list of pairs on m nodes)."""
    idx = 0; wire = {}
    for e in base_edges:
        wire[(e, 0)] = idx; idx += 1
        wire[(e, 1)] = idx; idx += 1
    gadget = {}
    for i in range(m):
        inc = [e for e in base_edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2 == 0:
                gadget[(i, bits)] = idx; idx += 1
    n = idx; adj = [[0] * n for _ in range(n)]
    for i in range(m):
        inc = [e for e in base_edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2: continue
            g = gadget[(i, bits)]
            for k, e in enumerate(inc):
                b = bits[k]
                if twist and e == base_edges[0] and i == base_edges[0][1]: b ^= 1
                t = wire[(e, b)]
                adj[g][t] = 1; adj[t][g] = 1
    return n, adj

def cubic(m, seed):
    rnd = random.Random(seed)
    for _ in range(500):
        pts = [i for i in range(m) for _ in range(3)]
        rnd.shuffle(pts)
        es = set(); ok = True
        for k in range(0, len(pts), 2):
            a, b = pts[k], pts[k+1]
            if a == b or (min(a,b), max(a,b)) in es: ok = False; break
            es.add((min(a,b), max(a,b)))
        if ok: return sorted(es)
    raise RuntimeError("no cubic")


if __name__ == "__main__":
    print("### GAUGE / SYMMETRIC witnesses")
    analyse("mp7 = FANO multipede (|Aut|=1344 expected)", *build_mp(FANO))
    analyse("CFI over C_5 (untwisted)", *build_cfi(5))
    analyse("CFI over C_5 (twisted)", *build_cfi(5, True))

    print("\n### MIXED witness (has Aut-fixed vertices = a real rigid decision)")
    analyse("MIXED multipede", *build_mp(MIXED))

    print("\n### 'circ(5)' — CORE_scoping called this RIGID; scheme symmetry says otherwise")
    analyse("circ(5) multipede", *build_mp(circ(5)))

    print("\n### GENUINELY RIGID multipedes (random full-rank incidence)")
    rows = []
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3),
                              (12, 8, 3, 4), (14, 9, 3, 5), (16, 10, 3, 6)]:
        A = rand_incidence(V, W, deg, seed)
        n, adj = build_mp(A)
        r = analyse(f"rand multipede V={V} W={W}", n, adj, relabels=2)
        rows.append(r)
    print("\n### CFI over random CUBIC bases (the standard WL-hard gauge family)")
    for m in (8, 10, 12, 14):
        es = cubic(m, 11 + m)
        for tw in (False, True):
            n, adj = build_cfi_base(es, m, tw)
            analyse(f"CFI cubic m={m} {'twisted' if tw else 'plain'}", n, adj, relabels=2)

    print("\n  SCALING (rigid family):  n / pruned-leaves / nodes / |Aut| / ① ")
    for r in rows:
        print(f"    n={r['n']:>4}  leaves={r['leaves']:>6}  nodes={r['nodes']:>5}  "
              f"|Aut|={r['aut']:>5}  R={r['R']:>4}  ①={r['ok']}")
