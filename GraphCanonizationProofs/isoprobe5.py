from itertools import product
import time
def study(P, qcoef):
    R=range(P); pts=list(product(R,repeat=4)); N=len(pts); idx={p:i for i,p in enumerate(pts)}
    def Q(x): return (x[0]*x[1]+x[2]*x[2]+qcoef*x[3]*x[3])%P
    Qv=[Q(p) for p in pts]
    iso=[(0 if all(c==0 for c in p) else (1 if Qv[i]==0 else 2)) for i,p in enumerate(pts)]
    # sub table: subi[i][j] = index of pts[i]-pts[j]
    subi=[[idx[tuple((pts[i][k]-pts[j][k])%P for k in range(4))] for j in range(N)] for i in range(N)]
    isod=[[iso[subi[i][j]] for j in range(N)] for i in range(N)]  # isod[z][t]
    n0=sum(1 for v in Qv if v==0); typ='+' if n0>P**3 else '-'
    def discrete(T):  # one-round count injective?
        keys=set()
        for u in range(N):
            h={}
            iu=isod  # iso[z-u] = isod[z][u]
            for z in range(N):
                if z==u: continue
                pat=tuple(isod[z][t] for t in T)
                k=(pat, isod[z][u]); h[k]=h.get(k,0)+1
            key=frozenset(h.items())
            if key in keys: return False
            keys.add(key)
        return True
    e=[idx[(0,0,0,0)],idx[(1,0,0,0)],idx[(0,1,0,0)],idx[(0,0,1,0)],idx[(0,0,0,1)]]
    # greedy from frame, add points until one-round discrete
    def ncls(T):
        s=set()
        for u in range(N):
            h={}
            for z in range(N):
                if z==u: continue
                k=(tuple(isod[z][t] for t in T), isod[z][u]); h[k]=h.get(k,0)+1
            s.add(frozenset(h.items()))
        return len(s)
    T=list(e); t0=time.time()
    while not discrete(T) and len(T)<12:
        best=-1;bp=None
        for p in range(N):
            if p in T: continue
            c=ncls(T+[p])
            if c>best: best=c;bp=p
        T.append(bp)
    print(f"  q={P} O^{typ}: min one-round base (greedy from frame) size = {len(T)} (n={N}, log_q n={4}, ⌈log2 n⌉={N.bit_length()-1}); discrete={discrete(T)}  [{time.time()-t0:.0f}s]")
study(5,1)   # O^+
study(5,2)   # O^-
