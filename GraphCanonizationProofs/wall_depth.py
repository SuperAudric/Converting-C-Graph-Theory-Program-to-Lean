#!/usr/bin/env python3
"""
DEPTH PROBE (the decisive go/no-go for Route B's wall).

The 3c crack: the iterated chi(detG2) pivot-count (graph-invariant 2-WL-lite, cap-respecting)
DETERMINES the Stab(S)-orbit at the bounded single-anchor mu=1 base. The decisive question:
  does the iteration DEPTH (#rounds to determination) stay O(1) as d grows, or grow with d?
    O(1)  -> wall crackable for the family -> Route B reaches poly.
    grows -> the frontier -> same as banked quasipoly -> pivot to Route C.

We instrument the pivot-count refinement and record the FIRST round at which the induced
vertex partition refines the orbit partition (= cell subset orbit = determination achieved;
orbit subset cell is free soundness). Cross-check with FULL binary 2-WL depth at d=4.
Methodology identical to wall_pair.py / wall_2wl.py (same orbit invariant, same observable).
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
    """col: list[int] length n; orbv: list (orbit key per index). True iff col refines orb."""
    m={}
    for i in range(n):
        f=col[i]
        if f in m:
            if m[f]!=orbv[i]: return False
        else: m[f]=orbv[i]
    return True

def pivot_depth(V,Q,q,d,S,orbv,maxr=40):
    """Iterated chi(detG2) pivot-count (the crack). Returns (det_round, fix_round, final_cells).
    Geometry (fixed across rounds) is precomputed; only the iterated colour col2[j] varies."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    z=S[0]; a=S[1]
    sqset={(i*i)%q for i in range(1,q)}; inv2=pow(2,q-2,q)
    def chi(t):
        t%=q
        return 0 if t==0 else (1 if t in sqset else 2)
    iso=set(w for w in V if Q(w)==0)
    def isob(w): return 1 if w in iso else 0
    def detG2(p,r):
        B=polar(Q,q,p,r,d); h=(B*inv2)%q
        return (Q(p)*Q(r) - h*h)%q
    # init colour: graph-invariant single/pair-to-base data
    az=sub(z,z,q,d)
    init=[]
    for v in V:
        init.append((isob(sub(v,z,q,d)), isob(sub(v,a,q,d)),
                     chi(detG2(sub(v,z,q,d), sub(v,a,q,d)))))
    o={}; col=[0]*n; t=0
    for i in range(n):
        if init[i] not in o: o[init[i]]=t; t+=1
        col[i]=o[init[i]]
    # precompute fixed geometry per (i,j): (isob(vi-xj), chi(detG2(vi-z, xj-z)), chi(detG2(vi-a, xj-a)))
    Vz=[sub(v,z,q,d) for v in V]; Va=[sub(v,a,q,d) for v in V]
    geom=[None]*n
    for i in range(n):
        vi=V[i]; piz=Vz[i]; pia=Va[i]; row=[]
        for j in range(n):
            row.append((isob(sub(vi,V[j],q,d)), chi(detG2(piz,Vz[j])), chi(detG2(pia,Va[j]))))
        geom[i]=row
    det_round=None
    if refines_list(col,orbv,n): det_round=0
    fix_round=None
    for r in range(1,maxr+1):
        sig=[None]*n
        for i in range(n):
            gi=geom[i]; cnt=defaultdict(int)
            for j in range(n):
                cnt[gi[j]+(col[j],)]+=1
            sig[i]=(col[i],tuple(sorted(cnt.items())))
        o={}; nc=[0]*n; t=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=t; t+=1
            nc[i]=o[sig[i]]
        stab=(nc==col)
        col=nc
        if det_round is None and refines_list(col,orbv,n): det_round=r
        if stab: fix_round=r; break
    return det_round, fix_round, len(set(col))

def wl2_depth(V,Q,q,d,S,orbv,maxr=20):
    """Full binary 2-WL (pair colours). Cross-check: round at which the induced vertex
    partition first refines the orbit partition. Expensive (O(n^3)/round) -> small d only."""
    n=len(V); pos={s:p+1 for p,s in enumerate(S)}
    def memb(v): return pos.get(v,0)
    col={}
    for i in range(n):
        for j in range(n):
            u,w=V[i],V[j]
            rel=0 if i==j else (1 if Q(sub(u,w,q,d))==0 else 2)
            col[(i,j)]=(rel,memb(u),memb(w))
    def vpart():
        vs=[(col[(i,i)],tuple(sorted(col[(i,k)] for k in range(n)))) for i in range(n)]
        o={}; out=[0]*n; t=0
        for i in range(n):
            if vs[i] not in o: o[vs[i]]=t; t+=1
            out[i]=o[vs[i]]
        return out
    det_round=None
    if refines_list(vpart(),orbv,n): det_round=0
    fix_round=None
    for r in range(1,maxr+1):
        newraw={}
        for i in range(n):
            for j in range(n):
                cnt=defaultdict(int)
                for k in range(n): cnt[(col[(i,k)],col[(k,j)])]+=1
                newraw[(i,j)]=(col[(i,j)],tuple(sorted(cnt.items())))
        o={}; nc={}; t=0
        for key,s in newraw.items():
            if s not in o: o[s]=t; t+=1
            nc[key]=o[s]
        stab=all(nc[k]==col[k] for k in col); col=nc
        if det_round is None and refines_list(vpart(),orbv,n): det_round=r
        if stab: fix_round=r; break
    return det_round, fix_round

def run(d,q,eps,do_wl2=False):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    z=tuple([0]*d); a=next(v for v in V if any(v) and Q(v)!=0); S=[z,a]
    orb=orbit_part(V,Q,q,S,d); norb=len(set(orb.values()))
    orbv=[orb[v] for v in V]
    t0=time.time()
    dr,fr,cells=pivot_depth(V,Q,q,d,S,orbv)
    det = "det@%s"%dr if dr is not None else "NO-DET"
    line=f"  {nm} |S|=2 n={len(V):5d}: orbits={norb:4d} | pivot-count: {det}, fixpoint@{fr}, cells={cells:4d} {'OK' if cells==norb else 'MISS'}"
    if do_wl2:
        wdr,wfr=wl2_depth(V,Q,q,d,S,orbv)
        line+=f" || 2WL: det@{wdr}, fix@{wfr}"
    line+=f"  [{time.time()-t0:.1f}s]"
    print(line)

if __name__=="__main__":
    print("=== WALL DEPTH PROBE: iteration depth of the chi(detG2) pivot-count to DETERMINE the orbit ===")
    print("--- d=4 (q=3 with full-2-WL cross-check; q=5,7 pivot-count only) ---")
    run(4,3,-1,do_wl2=True); run(4,3,+1,do_wl2=True)
    for q in [5,7]:
        run(4,q,-1); run(4,q,+1)
    print("--- d=6 (pivot-count; the scaling signal vs d=4) ---")
    run(6,3,-1); run(6,3,+1)
