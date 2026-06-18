from itertools import product
def setup(P,qcoef):
    R=range(P); pts=list(product(R,repeat=4)); N=len(pts); idx={p:i for i,p in enumerate(pts)}
    def Q(x): return (x[0]*x[1]+x[2]*x[2]+qcoef*x[3]*x[3])%P
    Qv=[Q(p) for p in pts]
    iso=[(0 if all(c==0 for c in p) else (1 if Qv[i]==0 else 2)) for i,p in enumerate(pts)]
    isod=[[iso[idx[tuple((pts[z][k]-pts[t][k])%P for k in range(4))]] for t in range(N)] for z in range(N)]
    n0=sum(1 for v in Qv if v==0); typ='+' if n0>P**3 else '-'
    return pts,N,idx,isod,typ
def discrete(N,isod,T):
    keys=set()
    for u in range(N):
        h={}
        for z in range(N):
            if z==u: continue
            k=(tuple(isod[z][t] for t in T), isod[z][u]); h[k]=h.get(k,0)+1
        key=frozenset(h.items())
        if key in keys: return False
        keys.add(key)
    return True
for P,qcoef in [(5,1),(5,2)]:
    pts,N,idx,isod,typ=setup(P,qcoef)
    e=[idx[(0,0,0,0)],idx[(1,0,0,0)],idx[(0,1,0,0)],idx[(0,0,1,0)],idx[(0,0,0,1)]]
    # candidate extra points (symmetry breakers, increasing)
    ex=[(0,0,1,1),(0,0,1,2),(1,1,1,1),(0,0,2,1),(1,2,3,4),(0,0,1,3)]
    exi=[idx[p] for p in ex]
    print(f"q={P} O^{typ}:")
    for k in range(0,5):
        T=e+exi[:k]
        print(f"  frame+{k} (size {5+k}): one-round discrete? {discrete(N,isod,T)}")
