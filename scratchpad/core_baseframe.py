#!/usr/bin/env python3
# Scope the CORE: does pinning a BASE FRAME (fix orientations of a spanning set of
# segments) + RREF-column read discretize the RIGID coords while leaving the GAUGE
# coords free (tied) — inducing only a PARTIAL order on the rigid subspace, thus
# sidestepping the 2^beta full-order wall? Aggregate over the gauge-orbit of the
# base frame (poly when dim ker is bounded) to tie gauge.
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
def in_rs(R,piv,e):
    e=e[:]
    for k,c in enumerate(piv):
        if e[c]: e=[a^b for a,b in zip(e,R[k])]
    return not any(e)
def base_kernel(A,W):
    return [list(x) for x in product([0,1],repeat=W) if all(sum(A[v][w]*x[w] for w in range(W))%2==0 for v in range(len(A)))]
def graph_orbits(A,role,Nb,aI,bI,midI,n):
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
    return {i:f(i) for i in range(n)}, ker

def analyse(name,A):
    print(f"\n===== {name} =====")
    n,adj,role,Nb,aI,bI,midI=build_mp(A); W=len(A[0])
    v2o,bker=graph_orbits(A,role,Nb,aI,bI,midI,n)
    norb=len(set(v2o.values()))
    ker_supp=set(w for X in bker for w in range(W) if any(X) and X[w])
    print(f"n={n} #orbits={norb} base-ker-dim={len(bin(len(bker))[2:])-1 if len(bker)>1 else 0} gauge-segs={sorted(ker_supp)}")
    H,_=cfi(n,role,Nb,aI,bI,midI)
    # BASE FRAME pinning: fix a(w)=0 for w in a set S (add rows e_{a(w)}). Choose S = ALL segs
    # (a full base orientation, one gauge-coset rep). Gauge-orbit of this frame = flip a<->b on
    # gauge segs => a poly (|ker|) family that is gauge-CLOSED.
    def pin_rows_for(orient):   # orient[w] in {0,1}: pin a(w)=orient? -> pin the chosen foot=0
        rows=[]
        for w in range(W):
            foot = aI[w] if orient[w]==0 else bI[w]
            e=[0]*n; e[foot]=1; rows.append(e)   # forces that foot (=some value)
        return rows
    # gauge-closed family: orient in {0-vector + each kernel element} (the kernel orbit of 0)
    fam = bker  # each kernel elt X gives orientation X (gauge-coset reps under +ker are all of ker from 0)
    def colsig_under(orient):
        R,piv=rref([r[:] for r in H]+pin_rows_for(orient), n)
        forced=[in_rs(R,piv,[1 if j==u else 0 for j in range(n)]) for u in range(n)]
        # RREF-column signature restricted to RIGID (forced) reading; gauge(free) -> sentinel
        def sig(v):
            if not forced[v]: return ('FREE',)
            return tuple(R[k][v] for k in range(len(R)))
        return [sig(v) for v in range(n)], sum(forced)
    per=[colsig_under(o) for o in fam]
    nforced=per[0][1]
    print(f"  base-frame pin: forced coords/frame = {nforced}/{n}  (family size={len(fam)})")
    # aggregate over the gauge-closed family (SET of per-frame signatures)
    agg=[frozenset(per[fi][0][v] for fi in range(len(fam))) for v in range(n)]
    # check orbit recovery per colour cell
    from collections import defaultdict
    cols=[('S',r[1]) if r[0]=='S' else ('M',r[1]) for r in role]
    cells=defaultdict(list)
    for v in range(n): cells[cols[v]].append(v)
    ok=True; bad=0
    for cell,vs in cells.items():
        for i in range(len(vs)):
            for j in range(i+1,len(vs)):
                a,b=vs[i],vs[j]
                if (agg[a]==agg[b])!=(v2o[a]==v2o[b]): ok=False; bad+=1
    print(f"  aggregate over gauge-closed base-frame family recovers orbits: {ok} (bad={bad}) classes={len(set(agg))}/{norb}")

MIXED=[[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]
if __name__=="__main__":
    analyse("RIGID m=5 (trivial gauge)", circ(5))
    analyse("MIXED (segs 0,1 coupled; 2-4 rigid)", MIXED)
    analyse("PURE-GAUGE m=7 (Fano)", circ(7))
