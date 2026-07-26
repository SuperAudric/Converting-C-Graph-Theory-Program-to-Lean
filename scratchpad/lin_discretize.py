from itertools import combinations
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
for m in [5,8]:
    A=circ(m); n,adj,role,Nb,aI,bI,midI=build_mp(A)
    H,W=cfi(n,role,Nb,aI,bI,midI); R,piv=rref(H,n)
    forced=[in_rs(R,piv,[1 if j==u else 0 for j in range(n)]) for u in range(n)]
    def colsig(v): return tuple(R[k][v] for k in range(len(R)))
    sigs=[colsig(v) for v in range(n)]
    print(f"m={m}: n={n} rank={len(piv)} forced={sum(forced)}/{n} distinct-RREF-col-sigs={len(set(sigs))}/{n}")
    ex=[(w,forced[aI[w]],forced[bI[w]],sigs[aI[w]]!=sigs[bI[w]]) for w in range(3)]
    print(f"   sample (w,a-forced,b-forced,feet-differ)={ex}")
