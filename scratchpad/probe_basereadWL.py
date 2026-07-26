#!/usr/bin/env python3
# De-risk the EXACT baseReadWL I will implement in Lean:
#   baseReadWL(pin, v) = multiset over ALL u of ( [adj v u != 0], chi u, encOpt(forcedVal(H u pin, x0, u)) )
# aggregated (readAggB) over a poly gauge-closed pinning family. Check it recovers
# Aut-orbits per colour-cell on the real multipede (feet+middles), incl >2-cells.
# Compare: empty-pin-ONLY (singleton family) vs the full single-vertex-pin family.

from itertools import product, combinations
from collections import Counter, defaultdict

def reduce_vec(basis, v):
    for lead, b in basis:
        if v[lead]: v = [x ^ y for x, y in zip(v, b)]
    return v
def build_basis(rows, n):
    basis = []
    for r in rows:
        v = reduce_vec(basis, r[:])
        leads = [i for i in range(n) if v[i]]
        if leads: basis.append((leads[0], v))
    return basis
def in_span(basis, target): return not any(reduce_vec(basis, target[:]))
def kernel(rows, n):
    return [list(x) for x in product([0,1], repeat=n)
            if all(sum(r[j]*x[j] for j in range(n))%2==0 for r in rows)]
def solve_particular(rows, rhs, n):
    M = [rows[i][:] + [rhs[i]] for i in range(len(rows))]; piv={}; r=0
    for c in range(n):
        pr = next((i for i in range(r,len(M)) if M[i][c]), None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]: M[i]=[a^b for a,b in zip(M[i],M[r])]
        piv[c]=r; r+=1
    x=[0]*n
    for c,rr in piv.items(): x[c]=M[rr][n]
    return x

def build_multipede(A):
    V,W=len(A),len(A[0]); Nb=[[w for w in range(W) if A[v][w]] for v in range(V)]
    idx=0; aI={}; bI={}; role=[]
    for w in range(W):
        aI[w]=idx; role.append(('seg',w,0)); idx+=1
        bI[w]=idx; role.append(('seg',w,1)); idx+=1
    midI={}
    for v in range(V):
        for k in range(0,len(Nb[v])+1,2):
            for c in combinations(Nb[v],k): midI[(v,frozenset(c))]=idx; role.append(('mid',v,frozenset(c))); idx+=1
    n=idx; adj=[[0]*n for _ in range(n)]
    for (v,Aset),mi in midI.items():
        for w in Nb[v]:
            tgt=aI[w] if w in Aset else bI[w]; adj[mi][tgt]=1; adj[tgt][mi]=1
    return n,adj,role,Nb,aI,bI,midI

def orbits_of(A,role,Nb,aI,bI,midI,n):
    W=len(A[0]); ker=kernel([r[:] for r in A],W)
    def act(X,i):
        k=role[i]
        if k[0]=='seg':
            _,w,s=k; return (aI[w] if s==1 else bI[w]) if X[w] else i
        _,v,Aset=k; XN=frozenset(w for w in Nb[v] if X[w]); return midI[(v,frozenset(Aset^XN))]
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for X in ker:
        for i in range(n): par[f(i)]=f(act(X,i))
    v2o={};
    for i in range(n): v2o[i]=f(i)
    return v2o, ker

def colour(role): return [('S',r[1]) if r[0]=='seg' else ('M',r[1]) for r in role]

def cfi_code(n,role,Nb,aI,bI,midI):
    rows=[]; W=max(r[1] for r in role if r[0]=='seg')+1
    for w in range(W):
        r=[0]*n; r[aI[w]]=1; r[bI[w]]=1; rows.append(r)
    for (v,Aset),mi in midI.items():
        r=[0]*n
        for w in Nb[v]: r[aI[w] if w in Aset else bI[w]]=1
        r[mi]=1; rows.append(r)
    return rows,W

def run(name,A):
    print(f"\n######### {name} #########")
    n,adj,role,Nb,aI,bI,midI=build_multipede(A)
    cols=colour(role); v2o,ker=orbits_of(A,role,Nb,aI,bI,midI,n)
    norb=len(set(v2o.values())); print(f"n={n} |gauge|={len(ker)} #orbits={norb}")
    H,W=cfi_code(n,role,Nb,aI,bI,midI)     # CFI recovered code (the faithful extraction)
    # gauge-invariant witness x0: particular solution of H x = rhs where feet get a(w)=0,b(w)=1
    # target: complementarity a+b=1 => rhs for those rows =1; gadget rows =0.
    rhs=[1]*W + [0]*(len(H)-W)
    x0=solve_particular([r[:] for r in H], rhs, n)
    def basis_for(pin):
        rows=[r[:] for r in H]
        if pin is not None:
            e=[0]*n; e[pin]=1; rows.append(e)
        return build_basis(rows,n)
    def forced(basis,u):
        e=[0]*n; e[u]=1; return in_span(basis,e)
    def encOpt(u,basis): return (1+x0[u]) if forced(basis,u) else 0
    def wl(pin_basis, v):
        # multiset over ALL u of (adj v u, chi u, encOpt u)
        return tuple(sorted((1 if adj[v][u] else 0, cols[u], encOpt(u,pin_basis)) for u in range(n)))
    def readagg(pins, v):
        bases=[basis_for(p) for p in pins]
        return frozenset(wl(b,v) for b in bases)
    for label,pins in [("singleton {empty}",[None]), ("empty+vertex-pins",[None]+list(range(n)))]:
        sig={v:readagg(pins,v) for v in range(n)}
        cells=defaultdict(list)
        for v in range(n): cells[cols[v]].append(v)
        ok=True; bad=0
        for cell,vs in cells.items():
            for i in range(len(vs)):
                for j in range(i+1,len(vs)):
                    a,b=vs[i],vs[j]
                    if (sig[a]==sig[b])!=(v2o[a]==v2o[b]): ok=False; bad+=1
        print(f"  [{label:20}] recovers orbits per-cell: {ok}  (bad pairs={bad})  read-classes={len(set(sig.values()))}/{norb}")

MIXED=[[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]
def circ(m,offs=(0,1,3)): return [[1 if any((i+o)%m==w for o in offs) else 0 for w in range(m)] for i in range(m)]
if __name__=="__main__":
    run("RIGID m=5 (>2-cell test)", circ(5))
    run("MIXED (segs 0,1 coupled)", MIXED)
    run("PURE-GAUGE m=7 (Fano)", circ(7))
