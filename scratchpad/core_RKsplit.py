#!/usr/bin/env python3
# Confirm the PLAN's core: the poly iso-invariant split R (rigid) / K (gauge),
# where K = support(ker H) at the vertex level, R = complement. Then:
#  (a) is R separated by the RREF-column read (each R-orbit distinct)?
#  (b) do K vertices tie within their gauge orbits (gauge-related signatures)?
# If yes, the reader = "canonize R (rigid; whole-R-rigid order 9A-9C), tie K" is sound;
# the only carried piece is the iso-invariant ORDER on R (bounded-rank recover core).
from itertools import combinations, product
def circ(m,offs=(0,1,3)): return [[1 if any((i+o)%m==w for o in offs) else 0 for w in range(m)] for i in range(m)]
def build_mp(A):
    V,W=len(A),len(A[0]); Nb=[[w for w in range(W) if A[v][w]] for v in range(V)]
    idx=0; aI={}; bI={}; role=[]
    for w in range(W):
        aI[w]=idx; role.append(('S',w,'a')); idx+=1
        bI[w]=idx; role.append(('S',w,'b')); idx+=1
    midI={}
    for v in range(V):
        for k in range(0,len(Nb[v])+1,2):
            for c in combinations(Nb[v],k): midI[(v,frozenset(c))]=idx; role.append(('M',v,frozenset(c))); idx+=1
    n=idx; adj=[[0]*n for _ in range(n)]
    for (v,Aset),mi in midI.items():
        for w in Nb[v]:
            t=aI[w] if w in Aset else bI[w]; adj[mi][t]=1; adj[t][mi]=1
    return n,adj,role,Nb,aI,bI,midI
def cfi(n,role,Nb,aI,bI,midI):
    rows=[]; W=max(r[1] for r in role if r[0]=='S')+1
    for w in range(W):
        r=[0]*n; r[aI[w]]=1; r[bI[w]]=1; rows.append(r)
    for (v,Aset),mi in midI.items():
        r=[0]*n
        for w in Nb[v]: r[aI[w] if w in Aset else bI[w]]=1
        r[mi]=1; rows.append(r)
    return rows,W
def rref(rows,n):
    R=[r[:] for r in rows]; piv=[]; r=0
    for c in range(n):
        pr=next((i for i in range(r,len(R)) if R[i][c]),None)
        if pr is None: continue
        R[r],R[pr]=R[pr],R[r]
        for i in range(len(R)):
            if i!=r and R[i][c]: R[i]=[a^b for a,b in zip(R[i],R[r])]
        piv.append(c); r+=1
    return R[:r],piv
def base_kernel(A,W):
    return [list(x) for x in product([0,1],repeat=W) if all(sum(A[v][w]*x[w] for w in range(W))%2==0 for v in range(len(A)))]
def orbits(A,role,Nb,aI,bI,midI,n):
    W=len(A[0]); ker=base_kernel(A,W)
    def act(X,i):
        k=role[i]
        if k[0]=='S':
            _,w,s=k; return (aI[w] if s=='b' else bI[w]) if X[w] else i
        _,v,Aset=k; XN=frozenset(w for w in Nb[v] if X[w]); return midI[(v,frozenset(Aset^XN))]
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for X in ker:
        for i in range(n): par[f(i)]=f(act(X,i))
    return {i:f(i) for i in range(n)}

def analyse(name,A):
    print(f"\n===== {name} =====")
    n,adj,role,Nb,aI,bI,midI=build_mp(A)
    v2o=orbits(A,role,Nb,aI,bI,midI,n)
    # K = vertices in a NON-singleton graph-aut orbit; R = fixed points
    from collections import defaultdict, Counter
    osz=Counter(v2o.values())
    K=[v for v in range(n) if osz[v2o[v]]>1]; R=[v for v in range(n) if osz[v2o[v]]==1]
    print(f"n={n}  |R rigid|={len(R)}  |K gauge|={len(K)}  #orbits={len(set(v2o.values()))}")
    # RREF-column signature (natural order) — for DISCRIMINATION check only
    H,_=cfi(n,role,Nb,aI,bI,midI); Rref,piv=rref(H,n)
    def sig(v): return tuple(Rref[k][v] for k in range(len(Rref)))
    sigs={v:sig(v) for v in range(n)}
    # (a) are R vertices pairwise distinct (each R-orbit singleton => must separate)?
    Rsigs=[sigs[v] for v in R]
    a_ok = len(set(Rsigs))==len(R)
    print(f"  (a) R separated by RREF-col signature: {a_ok}  ({len(set(Rsigs))}/{len(R)} distinct)")
    # (b) within each K-orbit, do vertices share a gauge-RELATED signature? Here test the
    #     weaker necessary condition: K-orbit members are NOT forced-distinct by an R-only read.
    #     Model an R-restricted read: signature keyed ONLY by pivot rows whose pivot col is in R.
    Rset=set(R); pivR=[k for k,c in enumerate(piv) if c in Rset]
    def sigR(v): return tuple(Rref[k][v] for k in pivR)   # read only R-supported structure
    b_ok=True; oversep=0
    for orb,mem in defaultdict(list, {o:[v for v in range(n) if v2o[v]==o] for o in set(v2o.values())}).items():
        if len(mem)>1:
            if len({sigR(v) for v in mem})>1: b_ok=False; oversep+=1
    print(f"  (b) K-orbits TIE under R-restricted read (pivots in R only): {b_ok}  (over-split orbits={oversep})")
    # (c) does the R-restricted read still separate all R-orbits?
    c_ok = len({sigR(v) for v in R})==len(R)
    print(f"  (c) R still separated by R-restricted read: {c_ok}  ({len({sigR(v) for v in R})}/{len(R)})")

MIXED=[[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]
if __name__=="__main__":
    analyse("RIGID m=5", circ(5))
    analyse("MIXED (segs 0,1 coupled)", MIXED)
    analyse("PURE-GAUGE m=7", circ(7))
