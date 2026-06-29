#!/usr/bin/env python3
"""
Faithful, cap-respecting test: does the PAIR observable chi(det G2) (what the seal uses,
graph-invariant) + binary 1-WL determine the orbit at the single-anchor mu=1 base, uniformly in q?
  init colour v = (iso(v-0), iso(v-a), chi(detG2(v-0, v-a)))            [all graph-invariant]
  refine: binary 1-WL  +  also a pivot-pair chi-count variant.
chi(detG2(p,r)) = quad char of  Q(p)Q(r) - (polar(p,r)/2)^2.
"""
import itertools
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
def refines(fine,coarse,V):
    m={}
    for v in V:
        f=fine[v]
        if f in m:
            if m[f]!=coarse[v]: return False
        else: m[f]=coarse[v]
    return True

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d));Q=make_Q(d,q,eps)
    sqset={(i*i)%q for i in range(1,q)}; inv2=pow(2,q-2,q)
    def chi(t):
        t%=q
        return 0 if t==0 else (1 if t in sqset else 2)
    def detG2(p,r):
        B=polar(Q,q,p,r,d)
        return (Q(p)*Q(r) - (B*inv2)%q*((B*inv2)%q))%q
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    a=next(v for v in V if any(v) and Q(v)!=0)
    z=tuple([0]*d); S=[z,a]
    orb=orbit_part(V,Q,q,S,d);norb=len(set(orb.values()))
    n=len(V); idx={v:i for i,v in enumerate(V)}
    iso=set(w for w in V if Q(w)==0)
    def isob(w): return 1 if w in iso else 0
    # init: graph-invariant single-vertex-to-base data
    init={}
    for v in V:
        init[v]=(isob(sub(v,z,q,d)), isob(sub(v,a,q,d)), chi(detG2(sub(v,z,q,d), sub(v,a,q,d))))
    n_init=len(set(init.values())); h_init=refines(init,orb,V)
    # binary 1-WL on top of init
    o={};col=[0]*n;t=0
    for i,v in enumerate(V):
        if init[v] not in o:o[init[v]]=t;t+=1
        col[i]=o[init[v]]
    iso_nz=[w for w in iso if any(w)]
    nbr=[[idx[add(v,w,q,d)] for w in iso_nz] for v in V]
    for _ in range(n):
        sig=[]
        for i in range(n):
            cnt=defaultdict(int)
            for j in nbr[i]: cnt[col[j]]+=1
            sig.append((col[i],tuple(sorted(cnt.items()))))
        o={};nc=[0]*n;t=0
        for i in range(n):
            if sig[i] not in o:o[sig[i]]=t;t+=1
            nc[i]=o[sig[i]]
        if nc==col:break
        col=nc
    n_wl=len(set(col)); h_wl=refines({V[i]:col[i] for i in range(n)},orb,V)
    # pivot-pair chi-count (graph-invariant 2-WL-lite): v -> multiset_x (col0[x], chi(detG2(v-x,?)))
    # color v by multiset over x of (isob(v-x), chi(detG2(sub(v,z),sub(x,z))), chi(detG2(sub(v,a),sub(x,a))), initcol[x])
    o={};c0=[0]*n;t=0
    for i,v in enumerate(V):
        if init[v] not in o:o[init[v]]=t;t+=1
        c0[i]=o[init[v]]
    col2=c0[:]
    for _ in range(n):
        sig=[]
        for i in range(n):
            vi=V[i]; piz=sub(vi,z,q,d); pia=sub(vi,a,q,d)
            cnt=defaultdict(int)
            for j in range(n):
                xj=V[j]
                cnt[(isob(sub(vi,xj,q,d)), chi(detG2(piz,sub(xj,z,q,d))), chi(detG2(pia,sub(xj,a,q,d))), col2[j])]+=1
            sig.append((col2[i],tuple(sorted(cnt.items()))))
        o={};nc=[0]*n;t=0
        for i in range(n):
            if sig[i] not in o:o[sig[i]]=t;t+=1
            nc[i]=o[sig[i]]
        if nc==col2:break
        col2=nc
    n_p=len(set(col2)); h_p=refines({V[i]:col2[i] for i in range(n)},orb,V)
    print(f"  {nm} |S|=2: orbits={norb:4d} | chi-init={n_init:4d}{'✓' if h_init else '✗'} | +1WL={n_wl:4d}{'✓' if h_wl else '✗'} | chi-pivot-count*={n_p:4d}{'✓' if h_p else '✗'}")

if __name__=="__main__":
    print("=== Pair observable chi(detG2) (graph-invariant, seal's tool) at single-anchor mu=1 base ===")
    for q in [3,5,7]:
        run(4,q,-1); run(4,q,+1)
