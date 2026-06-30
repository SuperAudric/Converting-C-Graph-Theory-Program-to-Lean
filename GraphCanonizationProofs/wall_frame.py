#!/usr/bin/env python3
"""
3b GAP-COVER PROBE: does the canonizer's ACTUAL refinement (plain binary 1-WL on the
similitude orbital scheme = iso/aniso relations only) DISCRETIZE the forms graph at the
O(d) SPANNING frame?

This is regime (I): a spanning anisotropic base makes Stab(base) trivial, so orbits are
singletons and "CellsAreOrbits" = "1-WL is discrete". This is exactly what the C# canonizer
exhibits (single path, base = frame d+1) and what the seal's ZProfileSeparates/Isotropy-
SeparatesAtBase states (separate all vertices). If plain 1-WL discretizes here uniformly,
the route's poly target is achievable with the canonizer's real (rank-3, no chi(detG2))
refinement, and the iterated-chi(detG2) 3c crack is an optimization for a SMALLER base, not
a prerequisite.

Compare against:
 - the SPANNING frame (origin + d independent vectors, anisotropic span)  [regime I]
 - a sequence of growing bases up to the frame (track when 1-WL discretizes = the base size
   the canonizer actually needs = the node-count exponent).
"""
import itertools, time

def nonsquare(q):
    sq={(i*i)%q for i in range(q)}; return next(g for g in range(2,q) if g not in sq)
def make_Q(d,q,eps):
    g=nonsquare(q)
    def Q(x):
        s=0
        if eps==+1:
            for i in range(0,d,2): s+=x[i]*x[i+1]
        else:
            for i in range(0,d-2,2): s+=x[i]*x[i+1]
            s+=x[d-2]*x[d-2]-g*x[d-1]*x[d-1]
        return s%q
    return Q
def sub(a,b,q,d): return tuple((a[i]-b[i])%q for i in range(d))

def wl1_discrete_round(V,Q,q,d,S):
    """Plain binary 1-WL (iso relation), individualize S. Returns (#cells, discrete?, rounds)."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    col=[0]*n
    for p,s in enumerate(S): col[idx[s]]=p+1
    # iso-adjacency lists (binary; the rank-3 similitude scheme's non-trivial relation)
    adj=[[] for _ in range(n)]
    for i in range(n):
        vi=V[i]
        for j in range(n):
            if i!=j and Q(sub(vi,V[j],q,d))==0: adj[i].append(j)
    rounds=0
    for _ in range(n):
        rounds+=1
        sig=[(col[i],tuple(sorted(col[j] for j in adj[i]))) for i in range(n)]
        o={}; nc=[0]*n; k=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=k;k+=1
            nc[i]=o[sig[i]]
        if nc==col: break
        col=nc
    return len(set(col)), (len(set(col))==n), rounds

def indep_anis_spanning(V,Q,q,d):
    """origin + a maximal independent set of vectors whose span is all of K^d, each chosen
    anisotropic where possible (guarantees mu=1 / anisotropic span)."""
    def rank(vs):
        # gaussian elim over GF(q)
        rows=[list(v) for v in vs]; r=0; cols=d
        for c in range(cols):
            piv=None
            for i in range(r,len(rows)):
                if rows[i][c]%q!=0: piv=i;break
            if piv is None: continue
            rows[r],rows[piv]=rows[piv],rows[r]
            inv=pow(rows[r][c],q-2,q)
            rows[r]=[(x*inv)%q for x in rows[r]]
            for i in range(len(rows)):
                if i!=r and rows[i][c]%q!=0:
                    f=rows[i][c]; rows[i]=[(rows[i][k]-f*rows[r][k])%q for k in range(cols)]
            r+=1
            if r==cols: break
        return r
    chosen=[]
    # prefer anisotropic independent vectors
    for v in V:
        if not any(v): continue
        if Q(v)==0: continue
        if rank(chosen+[list(v)])>len(chosen):
            chosen.append(v)
            if len(chosen)==d: break
    # if span<d (rare), top up with any independent vectors
    if len(chosen)<d:
        for v in V:
            if not any(v): continue
            if rank(chosen+[list(v)])>len(chosen):
                chosen.append(v)
                if len(chosen)==d: break
    return [tuple([0]*d)]+chosen   # origin + spanning set

def run(d,q,eps,maxn=20000):
    V=list(itertools.product(range(q),repeat=d))
    if len(V)>maxn:
        print(f"  VO^{'+' if eps>0 else '-'}_{d}({q}): n={len(V)} > cap, skipped"); return
    Q=make_Q(d,q,eps); nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    frame=indep_anis_spanning(V,Q,q,d)
    t0=time.time()
    cells,disc,rounds=wl1_discrete_round(V,Q,q,d,frame)
    # also: growing bases, find minimal |S| at which plain 1-WL discretizes
    minS=None
    for k in range(1,len(frame)+1):
        c,dd,_=wl1_discrete_round(V,Q,q,d,frame[:k])
        if dd: minS=k; break
    print(f"  {nm} n={len(V):6d}: frame |T|={len(frame)} (=d+1={d+1}) -> "
          f"1-WL cells={cells:6d} {'DISCRETE✓' if disc else 'NOT-discrete✗'} (r={rounds}); "
          f"min |S| to discretize = {minS}  [{time.time()-t0:.1f}s]")

if __name__=="__main__":
    print("=== 3b GAP-COVER: plain binary 1-WL discreteness at the O(d) spanning frame ===")
    print("(DISCRETE at the frame => canonizer's real refinement achieves the poly base, no chi(detG2) needed)")
    for q in [3,5,7,11]: run(4,q,-1); run(4,q,+1)
    run(6,3,-1); run(6,3,+1)
    run(6,5,-1); run(6,5,+1)
