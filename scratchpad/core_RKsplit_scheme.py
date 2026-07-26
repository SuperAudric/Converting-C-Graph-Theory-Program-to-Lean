#!/usr/bin/env python3
# ADJUSTED R/K probe (automorphism-split correction). Verifies:
#   (1) K1 := support(ker A_G)  ⊆  K2 := union of nontrivial FULL-Aut orbits
#       where FULL Aut = < linear-gauge swap-sets , SCHEME symmetry (collineations) >.
#   (2) On a SCHEME-SYMMETRIC witness the inclusion is STRICT: K2 ∖ K1 = the scheme
#       coords the ker-H split misses (they must go to consume, not force's R).
#   (3) R2 := FULL-Aut fixed points is separated by the RREF-column read (discriminating
#       power on the genuinely-rigid part); scheme coords are NOT in R2 (correctly excluded).
from itertools import combinations, product
from collections import defaultdict, Counter

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

def uf_orbits(n, perms):
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for p in perms:
        for i in range(n): par[f(i)]=f(p[i])
    return {i:f(i) for i in range(n)}

def linear_gauge_perms(A,role,Nb,aI,bI,midI,n):
    W=len(A[0]); ker=base_kernel(A,W); out=[]
    for X in ker:
        p=list(range(n))
        for i in range(n):
            k=role[i]
            if k[0]=='S':
                _,w,s=k
                if X[w]: p[i]= aI[w] if s=='b' else bI[w]
            else:
                _,v,Aset=k; XN=frozenset(w for w in Nb[v] if X[w]); p[i]=midI[(v,frozenset(Aset^XN))]
        out.append(p)
    return out, ker

def scheme_perm_from_segperm(sigma, role, Nb, aI, bI, midI, n, gadperm):
    # sigma: segment index permutation; gadperm: gadget index permutation (consistent with sigma).
    p=list(range(n))
    for i in range(n):
        k=role[i]
        if k[0]=='S':
            _,w,s=k; w2=sigma[w]; p[i]= aI[w2] if s=='a' else bI[w2]
        else:
            _,v,Aset=k; v2=gadperm[v]; A2=frozenset(sigma[w] for w in Aset); p[i]=midI[(v2,A2)]
    return p

def analyse(name, A, scheme=None):
    # scheme = (segperm, gadperm) a colour-preserving collineation, or None
    n,adj,role,Nb,aI,bI,midI=build_mp(A); W=len(A[0])
    lin,ker=linear_gauge_perms(A,role,Nb,aI,bI,midI,n)
    K1=set(w2 for X in ker for w2 in ([i for i in range(n)]) if False)  # placeholder
    # K1 = coords MOVED by some linear-gauge perm
    K1=set(i for p in lin for i in range(n) if p[i]!=i)
    perms=list(lin)
    if scheme is not None:
        perms.append(scheme_perm_from_segperm(scheme[0],role,Nb,aI,bI,midI,n,scheme[1]))
    v2o=uf_orbits(n,perms)
    osz=Counter(v2o.values())
    K2=set(i for i in range(n) if osz[v2o[i]]>1)
    R2=[i for i in range(n) if osz[v2o[i]]==1]
    print(f"\n===== {name} =====")
    print(f"  n={n}  |K1 linear-gauge|={len(K1)}  |K2 full-Aut gauge|={len(K2)}  |R2 rigid|={len(R2)}  #orbits={len(set(v2o.values()))}")
    print(f"  (1) K1 ⊆ K2 : {K1 <= K2}")
    gap=K2-K1
    print(f"  (2) gap K2∖K1 (scheme coords ker-H MISSES) = {len(gap)}  {'STRICT (scheme present)' if gap else '(none: Aut = linear gauge)'}")
    # (3) RREF-column read separates R2?
    H,_=cfi(n,role,Nb,aI,bI,midI); Rref,piv=rref(H,n)
    def sig(v): return tuple(Rref[k][v] for k in range(len(Rref)))
    Rsigs=[sig(v) for v in R2]
    print(f"  (3) R2 separated by RREF-col signature: {len(set(Rsigs))==len(R2)}  ({len(set(Rsigs))}/{len(R2)})")
    # sanity: scheme coords are NOT in R2 (correctly excluded from force's rigid part)
    if scheme is not None:
        print(f"      scheme gap ⊆ K2 (excluded from R2): {gap <= K2 and gap.isdisjoint(set(R2))}")

def circ(m,offs=(0,1,3)): return [[1 if any((i+o)%m==w for o in offs) else 0 for w in range(m)] for i in range(m)]

# scheme-symmetric witness: TWO identical circ(5) halves side-by-side, colour-linked by a
# half-swap collineation. Segments 0..4 (half A), 5..9 (half B); gadget i covers {i,i+1,i+3}
# within its half. Collineation phi: w -> (w+5)%10 (swap halves), gadget v -> (v+5)%10.
def two_copies(m=5):
    A1=circ(m); V=2*m; W=2*m
    A=[[0]*W for _ in range(V)]
    for i in range(m):
        for w in range(m):
            A[i][w]=A1[i][w]           # half A
            A[m+i][m+w]=A1[i][w]       # half B (identical)
    seg=lambda w:(w+m)%(2*m); gad=lambda v:(v+m)%(2*m)
    return A, ([seg(w) for w in range(2*m)],[gad(v) for v in range(2*m)])

# MIXED-scheme: half A = circ(5) coloured DISTINCTLY (rigid), halves B,C = circ(5) pair colour-linked.
def three_copies_two_linked(m=5):
    A1=circ(m); V=3*m; W=3*m
    A=[[0]*W for _ in range(V)]
    for i in range(m):
        for w in range(m):
            A[i][w]=A1[i][w]; A[m+i][m+w]=A1[i][w]; A[2*m+i][2*m+w]=A1[i][w]
    # collineation swaps ONLY halves B(1) and C(2): seg w in B <-> C, A fixed
    def seg(w):
        if w<m: return w
        if w<2*m: return w+m
        return w-m
    return A, ([seg(w) for w in range(3*m)], [seg(v) for v in range(3*m)])

MIXED=[[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]
if __name__=="__main__":
    analyse("RIGID m=5 (linear-gauge only, no scheme)", circ(5))
    analyse("MIXED linear (segs 0,1 coupled)", MIXED)
    A2c,sc=two_copies(5)
    analyse("SCHEME: two colour-linked rigid halves (pure scheme)", A2c, sc)
    A3c,sc3=three_copies_two_linked(5)
    analyse("MIXED-SCHEME: rigid half A + colour-linked halves B,C", A3c, sc3)
