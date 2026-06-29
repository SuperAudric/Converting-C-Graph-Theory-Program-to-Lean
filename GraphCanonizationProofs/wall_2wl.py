#!/usr/bin/env python3
"""
2-WL vs 1-WL at the single-anisotropic-anchor base (|S|=2, mu=1) where 1-WL over-merged.
Does the PAIR observable (2-WL ~ chi(det G2), the seal's tool) achieve cells=orbits there?
Also reports SelectedCellIsOrbit-style data: are the over-merged cells the ones a canonizer would pick?
"""
import itertools
from collections import defaultdict

def nonsquare(q):
    sq = {(i*i) % q for i in range(q)}
    return next(g for g in range(2, q) if g not in sq)

def make_Q(d, q, eps):
    g = nonsquare(q)
    def Q(x):
        s = 0
        if eps == +1:
            for i in range(0, d, 2): s += x[i]*x[i+1]
        else:
            for i in range(0, d-2, 2): s += x[i]*x[i+1]
            s += x[d-2]*x[d-2] - g*x[d-1]*x[d-1]
        return s % q
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
        if x!=0:
            inv=pow(x,q-2,q); return tuple((inv*y)%q for y in phi)
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

def wl1(V,Q,q,d,S):
    n=len(V); idx={v:i for i,v in enumerate(V)}
    col=[0]*n
    for p,s in enumerate(S): col[idx[s]]=p+1
    adj=[[] for _ in range(n)]
    for i in range(n):
        vi=V[i]
        for j in range(n):
            if i!=j and Q(sub(vi,V[j],q,d))==0: adj[i].append(j)
    for _ in range(n):
        sig=[(col[i],tuple(sorted(col[j] for j in adj[i]))) for i in range(n)]
        o={}; nc=[0]*n; k=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=k;k+=1
            nc[i]=o[sig[i]]
        if nc==col: break
        col=nc
    return {V[i]:col[i] for i in range(n)}

def wl2(V,Q,q,d,S):
    """2-WL. color(u,w); vertex signature = color(v,v) refined. Initial color encodes
    adjacency iso(u-w), membership of u,w in S (by position), and equality."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    pos={s:p+1 for p,s in enumerate(S)}
    def memb(v): return pos.get(v,0)
    # initial pair colour
    col={}
    for i in range(n):
        for j in range(n):
            u,w=V[i],V[j]
            rel = 0 if i==j else (1 if Q(sub(u,w,q,d))==0 else 2)
            col[(i,j)]=(rel,memb(u),memb(w))
    # refine
    for _ in range(2*n):
        newraw={}
        for i in range(n):
            for j in range(n):
                cnt=defaultdict(int)
                for k in range(n):
                    cnt[(col[(i,k)],col[(k,j)])]+=1
                newraw[(i,j)]=(col[(i,j)],tuple(sorted(cnt.items())))
        o={}; nc={}; t=0
        for key,sig in newraw.items():
            if sig not in o: o[sig]=t;t+=1
            nc[key]=o[sig]
        if all(nc[k]==col[k] for k in col): break
        col=nc
    # vertex signature: color(v,v) plus multiset of color(v,x)
    vsig={}
    for i in range(n):
        vsig[V[i]]=(col[(i,i)],tuple(sorted(col[(i,k)] for k in range(n))))
    # relabel
    o={};out={};t=0
    for v in V:
        if vsig[v] not in o: o[vsig[v]]=t;t+=1
        out[v]=o[vsig[v]]
    return out

def first_indep_anis(V,Q,q,d,count):
    chosen=[]; span=span_of(q,[tuple([0]*d)],d)
    for v in V:
        if any(v) and Q(v)!=0 and v not in span:
            chosen.append(v); span=span_of(q,chosen,d)
            if len(chosen)==count: break
    return chosen

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis=first_indep_anis(V,Q,q,d,2)
    for ksz,S in [(1,[tuple([0]*d)]),
                  (2,[tuple([0]*d),anis[0]]),
                  (3,[tuple([0]*d)]+anis[:2])]:
        orb=orbit_part(V,Q,q,S,d)
        c1=wl1(V,Q,q,d,S); c2=wl2(V,Q,q,d,S)
        norb=len(set(orb.values()))
        n1=len(set(c1.values())); n2=len(set(c2.values()))
        h1=refines(c1,orb,V); h2=refines(c2,orb,V)
        print(f"  {nm} |S|={ksz}: orbits={norb:4d} | 1-WL cells={n1:4d} {'✓' if h1 else '✗'} | 2-WL cells={n2:4d} {'✓' if h2 else '✗'}")

if __name__=="__main__":
    print("=== 1-WL vs 2-WL at single-anisotropic-anchor bases (the 1-WL failure point) ===")
    for q in [3,5]:
        run(4,q,-1); run(4,q,+1)
