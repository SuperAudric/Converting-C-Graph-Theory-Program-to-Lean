#!/usr/bin/env python3
"""
MODEL-GAP RESOLUTION (2026-06-30). Does the Lean `CellsAreOrbits` model — 1-WL on the
forms-graph's rank-3 isoClass orbital scheme + base individualization — certify cells=orbits
at the BOUNDED bases the node-count bridge ranges over (SinglePathDisposition = forall S)?

Faithful to source:
  - schemeAdj relation = isoClassK(y - x) in {0:zero, 1:nonzero-isotropic, 2:anisotropic}
    (FieldGeneric.lean:33; rank-3, similitude-invariant — aniso NOT split square/nonsquare).
  - CellsAreOrbits = 1-WL (vertex refinement) on that scheme, seeded individualizedColouring S.
  - Stab(S)-orbit = exact Gram (Q(v), polar(v,s)_s) when span(S) anisotropic (mu=1 delimiter).

Compare, at a BOUNDED base (|S|=2 single anchor) and the LEAF base (|S|=d):
  - wl1 = the 1-WL CellsAreOrbits model  (does it reach orbits?)
  - wl2 = genuine 2-WL on the same scheme (the chi(detG2)-strength fix)
Verdict: if wl1 is STUCK (cells > orbits, i.e. coarser) at |S|=2 but wl2 reaches orbits,
the model gap is real: Route B's 1-WL model fails at bounded bases; needs 2-WL.
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
def refines(fine,coarse,V):
    m={}
    for v in V:
        f=fine[v]
        if f in m:
            if m[f]!=coarse[v]: return False
        else: m[f]=coarse[v]
    return True

def isoclass(Q,q,d,w):
    if all(c==0 for c in w): return 0
    return 1 if Q(w)==0 else 2

def wl1_isoclass(V,Q,q,d,S):
    """1-WL on the rank-3 isoClass scheme + individualize S = the faithful CellsAreOrbits model."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    col=[0]*n
    for p,s in enumerate(S): col[idx[s]]=p+1
    # edge label rel[i][j] = isoClass(V[i]-V[j]) in {0,1,2}
    rel=[[0]*n for _ in range(n)]
    for i in range(n):
        vi=V[i]
        for j in range(n):
            rel[i][j]=isoclass(Q,q,d,sub(vi,V[j],q,d))
    for _ in range(n):
        sig=[(col[i],tuple(sorted((rel[i][j],col[j]) for j in range(n) if j!=i))) for i in range(n)]
        o={};nc=[0]*n;k=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=k;k+=1
            nc[i]=o[sig[i]]
        if nc==col: break
        col=nc
    return {V[i]:col[i] for i in range(n)}

def wl2_isoclass(V,Q,q,d,S):
    """genuine 2-WL on the isoClass scheme + individualize S = the chi(detG2)-strength fix."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    pos={s:p+1 for p,s in enumerate(S)}
    def memb(v): return pos.get(v,0)
    col={}
    for i in range(n):
        for j in range(n):
            col[(i,j)]=(0 if i==j else isoclass(Q,q,d,sub(V[i],V[j],q,d)), memb(V[i]), memb(V[j]))
    for _ in range(2*n):
        newraw={}
        for i in range(n):
            for j in range(n):
                cnt=defaultdict(int)
                for k in range(n): cnt[(col[(i,k)],col[(k,j)])]+=1
                newraw[(i,j)]=(col[(i,j)],tuple(sorted(cnt.items())))
        o={};nc={};t=0
        for key,sig in newraw.items():
            if sig not in o: o[sig]=t;t+=1
            nc[key]=o[sig]
        if all(nc[k]==col[k] for k in col): break
        col=nc
    vsig={V[i]:(col[(i,i)],tuple(sorted(col[(i,k)] for k in range(n)))) for i in range(n)}
    o={};out={};t=0
    for v in V:
        if vsig[v] not in o: o[vsig[v]]=t;t+=1
        out[v]=o[vsig[v]]
    return out

def first_indep_anis(V,Q,q,d,count):
    chosen=[]; span={tuple([0]*d)}
    for v in V:
        if any(v) and Q(v)!=0 and v not in span:
            chosen.append(v); span=span_of(q,chosen,d)
            if len(chosen)==count: break
    return chosen

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d));Q=make_Q(d,q,eps)
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis=first_indep_anis(V,Q,q,d,d)
    bases=[("bounded |S|=2",[tuple([0]*d),anis[0]]),
           (f"leaf   |S|={d}",[tuple([0]*d)]+anis[:d-1])]
    for tag,S in bases:
        orb=orbit_part(V,Q,q,S,d); norb=len(set(orb.values()))
        c1=wl1_isoclass(V,Q,q,d,S); n1=len(set(c1.values())); h1=refines(c1,orb,V)
        c2=wl2_isoclass(V,Q,q,d,S); n2=len(set(c2.values())); h2=refines(c2,orb,V)
        v1="orbits✓" if (h1 and n1==norb) else ("STUCK✗(coarser)" if n1<norb else "splits")
        v2="orbits✓" if (h2 and n2==norb) else ("STUCK✗" if n2<norb else "splits")
        print(f"  {nm} {tag}: orbits={norb:4d} | 1-WL(CellsAreOrbits model) cells={n1:4d} {v1:18s} | 2-WL(fix) cells={n2:4d} {v2}")

if __name__=="__main__":
    print("=== MODEL GAP: 1-WL isoClass scheme (CellsAreOrbits model) vs 2-WL, at bounded vs leaf base ===")
    for q in [3,5]: run(4,q,-1); run(4,q,+1)
    run(6,3,-1)
