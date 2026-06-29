#!/usr/bin/env python3
"""
DEPTH PROBE v2 — generalized to arbitrary base size, to test depth vs BOTH ambient d AND base-depth.
v1 showed depth O(1) at the single-anchor base, but that base's orbit count is d-independent (12).
Here we sweep |S|=2,3,4 (anisotropic mu=1 bases) at d=4,6 so the orbit count grows; if the determination
depth of the iterated chi(detG2) pivot-count still stays O(1), that is the strong uniformity signal.

Observable (cap-respecting, graph-invariant): per vertex v, init = (iso(v-s) for s in S,
chi(detG2(v-s, v-s')) for pairs s<s' in S); iterate pivot-count
  v -> multiset_x ( iso(v-x), [chi(detG2(v-s, x-s))]_{s in S}, col[x] ).
Determination depth = first round the induced partition refines the Stab(S)-orbit partition.
"""
import itertools, time
from collections import defaultdict

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
def add(a,b,q,d): return tuple((a[i]+b[i])%q for i in range(d))
def sub(a,b,q,d): return tuple((a[i]-b[i])%q for i in range(d))
def polar(Q,q,u,v,d): return (Q(add(u,v,q,d))-Q(u)-Q(v))%q
def span_of(q,S,d):
    span={tuple([0]*d)}
    for s in S:
        ns=set()
        for c in range(q):
            cs=tuple((c*s[i])%q for i in range(d))
            for w in span: ns.add(add(w,cs,q,d))
        span=ns
    return span
def normalize_scaling(phi,q):
    for x in phi:
        if x!=0: inv=pow(x,q-2,q); return tuple((inv*y)%q for y in phi)
    return tuple([0]*len(phi))
def orbit_part(V,Q,q,S,d):
    span=span_of(q,S,d); ti=all(Q(w)==0 for w in span); part={}
    for v in V:
        if v in span: part[v]=('in_span',v); continue
        phi=(Q(v),)+tuple(polar(Q,q,v,s,d) for s in S)
        part[v]=('sc',normalize_scaling(phi,q)) if ti else ('ex',phi)
    return part
def refines_list(col, orbv, n):
    m={}
    for i in range(n):
        f=col[i]
        if f in m:
            if m[f]!=orbv[i]: return False
        else: m[f]=orbv[i]
    return True

def first_indep_anis(V,Q,q,d,count):
    chosen=[]; span={tuple([0]*d)}
    for v in V:
        if any(v) and Q(v)!=0 and v not in span:
            chosen.append(v); span=span_of(q,chosen,d)
            if len(chosen)==count: break
    return chosen

def pivot_depth_gen(V,Q,q,d,S,orbv,maxr=40):
    n=len(V); idx={v:i for i,v in enumerate(V)}
    sqset={(i*i)%q for i in range(1,q)}; inv2=pow(2,q-2,q)
    def chi(t):
        t%=q
        return 0 if t==0 else (1 if t in sqset else 2)
    iso=set(w for w in V if Q(w)==0)
    def isob(w): return 1 if w in iso else 0
    def detG2(p,r):
        B=polar(Q,q,p,r,d); h=(B*inv2)%q
        return (Q(p)*Q(r)-h*h)%q
    Vs=[[sub(v,s,q,d) for v in V] for s in S]   # Vs[k][i] = V[i]-S[k]
    pairs=[(a,b) for a in range(len(S)) for b in range(a+1,len(S))]
    init=[]
    for i in range(n):
        toS=tuple(isob(Vs[k][i]) for k in range(len(S)))
        pr =tuple(chi(detG2(Vs[a][i],Vs[b][i])) for (a,b) in pairs)
        init.append(toS+pr)
    o={}; col=[0]*n; t=0
    for i in range(n):
        if init[i] not in o: o[init[i]]=t; t+=1
        col[i]=o[init[i]]
    # precompute fixed geometry per (i,j): (iso(vi-xj), [chi(detG2(vi-s, xj-s))]_s)
    geom=[None]*n
    for i in range(n):
        vi=V[i]; row=[]
        for j in range(n):
            row.append((isob(sub(vi,V[j],q,d)),)+tuple(chi(detG2(Vs[k][i],Vs[k][j])) for k in range(len(S))))
        geom[i]=row
    det_round=0 if refines_list(col,orbv,n) else None
    fix_round=None
    for r in range(1,maxr+1):
        sig=[None]*n
        for i in range(n):
            gi=geom[i]; cnt=defaultdict(int)
            for j in range(n): cnt[gi[j]+(col[j],)]+=1
            sig[i]=(col[i],tuple(sorted(cnt.items())))
        o={}; nc=[0]*n; t=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=t; t+=1
            nc[i]=o[sig[i]]
        stab=(nc==col); col=nc
        if det_round is None and refines_list(col,orbv,n): det_round=r
        if stab: fix_round=r; break
    return det_round, fix_round, len(set(col))

def run(d,q,eps,ksizes):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    z=tuple([0]*d); anis=first_indep_anis(V,Q,q,d,max(ksizes)-1)
    for k in ksizes:
        S=[z]+anis[:k-1]
        orb=orbit_part(V,Q,q,S,d); norb=len(set(orb.values())); orbv=[orb[v] for v in V]
        t0=time.time()
        dr,fr,cells=pivot_depth_gen(V,Q,q,d,S,orbv)
        det="det@%s"%dr if dr is not None else "NO-DET"
        print(f"  {nm} |S|={k} n={len(V):5d}: orbits={norb:4d} | pivot-count: {det}, fix@{fr}, cells={cells:4d} {'OK' if cells==norb else 'MISS'}  [{time.time()-t0:.1f}s]")

if __name__=="__main__":
    print("=== DEPTH vs (ambient d, base-depth |S|): iterated chi(detG2) pivot-count determination depth ===")
    print("--- d=4, q=3 ---"); run(4,3,-1,[2,3,4]); run(4,3,+1,[2,3,4])
    print("--- d=6, q=3 (the scaling signal: same |S| at larger d, AND deeper |S|) ---")
    run(6,3,-1,[2,3,4,5]); run(6,3,+1,[2,3,4,5])
    print("--- d=4, q=5 (uniformity in q at deeper bases) ---"); run(4,5,-1,[2,3]); run(4,5,+1,[2,3])
