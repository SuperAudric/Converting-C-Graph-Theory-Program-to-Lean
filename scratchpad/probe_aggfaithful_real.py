#!/usr/bin/env python3
# Probe v3 — FAITHFUL to the landed Lean objects. Tests whether the SINGLE-VALUE
# forcedVal read (baseReadPin), aggregated as a SET over a poly gauge-closed
# pinning family, separates orbits on the REAL multipede — for two candidate
# extractions:
#   (a) H = adjacency rows (hsAdj, the step-4/8 landed extraction), vertex-pins;
#   (b) H = the CFI RECOVERED CODE (feet complementarity + gadget parity), the
#       ForcingModel/P2 object.
# Pinning family = {emptyset} u { {e_v} : v }  (singleton vertex pins; gauge-closed).
# baseReadPin(p,v) = encOpt(forcedVal(H u p, x0, v)) in {none, some 0, some 1}.
# aggSet(v) = { baseReadPin(p,v) : p in family }.  Check aggSet(u)=aggSet(w) <=> u~w (Aut orbit).

from itertools import product, combinations
from collections import Counter

def reduce_vec(basis, v):
    for lead, b in basis:
        if v[lead]:
            v = [x ^ y for x, y in zip(v, b)]
    return v
def build_basis(rows, n):
    basis = []
    for r in rows:
        v = reduce_vec(basis, r[:])
        leads = [i for i in range(n) if v[i]]
        if leads: basis.append((leads[0], v))
    return basis
def in_span(basis, target):
    return not any(reduce_vec(basis, target[:]))
def kernel(rows, n):
    return [list(x) for x in product([0,1], repeat=n)
            if all(sum(r[j]*x[j] for j in range(n))%2==0 for r in rows)]

# ---- build the multipede (feet + middles), Neuen-Schweitzer ----
def build_multipede(A):
    V, W = len(A), len(A[0])
    Nb = [[w for w in range(W) if A[v][w]] for v in range(V)]
    idx = 0
    aI, bI = {}, {}
    role = []
    for w in range(W):
        aI[w]=idx; role.append(('seg',w,0)); idx+=1
        bI[w]=idx; role.append(('seg',w,1)); idx+=1
    midI = {}  # (v, frozenset A) -> idx
    for v in range(V):
        d=len(Nb[v])
        for k in range(0,d+1,2):
            for c in combinations(Nb[v],k):
                midI[(v,frozenset(c))]=idx; role.append(('mid',v,frozenset(c))); idx+=1
    n=idx
    adj=[[0]*n for _ in range(n)]
    for v in range(V):
        for (vv,Aset),mi in midI.items():
            if vv!=v: continue
            for w in Nb[v]:
                tgt = aI[w] if w in Aset else bI[w]
                adj[mi][tgt]=1; adj[tgt][mi]=1
    return n, adj, role, Nb, aI, bI, midI

def gauge_orbits(A, role, Nb, aI, bI, midI, n):
    """Orbits under all gauge swap-sets X in ker(A_G) (fine colouring => Aut = gauge)."""
    W=len(A[0])
    ker = kernel([r[:] for r in A], W)
    # each X acts: a(w)<->b(w) for w in X ; m_(v,Aset) -> m_(v, Aset xor (X cap N(v)))
    def act(X, i):
        kind=role[i]
        if kind[0]=='seg':
            _,w,side=kind
            if X[w]: return (aI[w] if side==1 else bI[w])
            return i
        else:
            _,v,Aset=kind
            XN=frozenset(w for w in Nb[v] if X[w])
            return midI[(v, frozenset(Aset ^ XN))]
    # union-find over vertices
    parent=list(range(n))
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def uni(a,b): parent[find(a)]=find(b)
    for X in ker:
        for i in range(n):
            uni(i, act(X,i))
    orb={}
    for i in range(n): orb.setdefault(find(i),[]).append(i)
    return list(orb.values()), ker

def colour(role):
    # fine colouring: seg w -> ('S',w) ; mid of gadget v -> ('M',v)
    out=[]
    for r in role:
        if r[0]=='seg': out.append(('S',r[1]))
        else: out.append(('M',r[1]))
    return out

# ---- extraction (a): adjacency rows ----
def extract_adj(n, adj):
    return [row[:] for row in adj]

# ---- extraction (b): CFI recovered code over vertices ----
# feet: a(w)+b(w)=1  (complementarity)
# middle m_(v,Aset): sum_{w in Aset} a(w) + sum_{w in N(v)\Aset} b(w) + m = 0  (parity gadget)
# We encode homogeneous rows (RHS folded into a witness). For forcedness we use the
# homogeneous LEFT side; the recovered code's rowspace determines forced coords.
def extract_cfi(n, role, Nb, aI, bI, midI):
    rows=[]
    W=max(r[1] for r in role if r[0]=='seg')+1
    for w in range(W):
        r=[0]*n; r[aI[w]]=1; r[bI[w]]=1; rows.append(r)          # a(w)+b(w)=1 (homog. part)
    for (v,Aset),mi in midI.items():
        r=[0]*n
        for w in Nb[v]:
            r[aI[w] if w in Aset else bI[w]]=1
        r[mi]=1
        rows.append(r)
    return rows

def run(name, A):
    print(f"\n########## {name} ##########")
    n, adj, role, Nb, aI, bI, midI = build_multipede(A)
    cols = colour(role)
    orbits, ker = gauge_orbits(A, role, Nb, aI, bI, midI, n)
    v2orb = {}
    for oi,o in enumerate(orbits):
        for v in o: v2orb[v]=oi
    W=len(A[0])
    print(f"n={n} vertices, |gauge|={len(ker)}, #orbits={len(orbits)}")

    # witness x0: any fixed vector; forcedVal returns some(x0 v) on forced coords.
    # Use x0 = 0 (homogeneous); then some(0) vs none is the only signal from value —
    # separation must come from the FORCEDNESS pattern across pins. (Tests the weakest read.)
    # Also test x0 = a pseudo-random gauge-invariant vector (constant on orbits).
    import hashlib
    def x0_orbinv(v):  # gauge-invariant: constant on orbit, 'random' per orbit
        return int(hashlib.md5(str(v2orb[v]).encode()).hexdigest(),16)&1

    for exname, H0 in [("ADJ (hsAdj)", extract_adj(n,adj)), ("CFI recovered code", extract_cfi(n,role,Nb,aI,bI,midI))]:
        for wname, x0 in [("x0=0", lambda v:0), ("x0=orbit-inv", x0_orbinv)]:
            pins = [None] + [v for v in range(n)]   # empty + single vertex pin e_v
            def basis_for(p):
                rows=[r[:] for r in H0]
                if p is not None:
                    e=[0]*n; e[p]=1; rows.append(e)
                return build_basis(rows,n)
            bases = {p: basis_for(p) for p in pins}
            def read(p,v):
                e=[0]*n; e[v]=1
                if in_span(bases[p], e): return 1+x0(v)   # some(x0 v)
                return 0                                   # none
            def aggset(v): return frozenset(read(p,v) for p in pins)
            sig = {v: aggset(v) for v in range(n)}
            # check within each colour cell: aggset equal <=> same orbit
            ok=True; ncell_bad=0
            from collections import defaultdict
            cells=defaultdict(list)
            for v in range(n): cells[cols[v]].append(v)
            for cell,vs in cells.items():
                for i in range(len(vs)):
                    for j in range(i+1,len(vs)):
                        a,b=vs[i],vs[j]
                        if (sig[a]==sig[b]) != (v2orb[a]==v2orb[b]):
                            ok=False; ncell_bad+=1
            # separation power: # distinct read-classes vs # orbits (restricted per cell)
            tot_readclasses=len(set(sig.values()))
            print(f"  [{exname:20}|{wname:12}] recovers orbits per-cell: {str(ok):5} "
                  f"(bad pairs={ncell_bad}); read-classes={tot_readclasses}/{len(orbits)} orbits")

MIXED_BASE = [[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]
def circ(m,offs=(0,1,3)): return [[1 if any((i+o)%m==w for o in offs) else 0 for w in range(m)] for i in range(m)]

if __name__=="__main__":
    run("RIGID m=5 (all middles must split; the >2-cell test)", circ(5))
    run("MIXED (segs 0,1 coupled; rest rigid)", MIXED_BASE)
