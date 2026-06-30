#!/usr/bin/env python3
"""
DESCENT PROBE (2026-06-30) — does the bridge's ACTUAL hypothesis hold at 1-WL?

The node-count bridge is keyed on SelectedCellIsOrbit (the cell `sel` TARGETS is a single
Stab(path)-orbit), NOT the stronger CellsAreOrbits (ALL cells = orbits). The C# prunes only
WITHIN Stab(path)-orbits (CoveredByPathFixingAut), so BranchingNodes=0 forces every SELECTED
cell to be orbit-pure at 1-WL. This probe replicates the actual descent and checks it:

  base=[]; loop: 1-WL refine; selected cell = first (lowest-colour) non-singleton cell;
  CHECK selected cell is orbit-pure (all members one Stab(base)-orbit); individualize its
  min vertex; repeat until discrete.

If selected cell is orbit-pure at EVERY step => SelectedCellIsOrbit holds along the descent
at 1-WL => Route B's bridge hypothesis lives at 1-WL (no 2-WL needed), and BranchingNodes=0
is replicated. (Contrast: my model_gap.py showed CellsAreOrbits — ALL cells — FALSE at the
artificial base {0,a}; that base/cell may simply never be a SELECTED target on the path.)
"""
import itertools

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
    """Stab(S) similitude-orbit: exact Gram when span(S) has an anisotropic vector (mu=1),
    scaling-class when span(S) totally isotropic (mu free)."""
    span=span_of(q,S,d); ti=all(Q(w)==0 for w in span); part={}
    for v in V:
        if v in span: part[v]=('in_span',v); continue
        phi=(Q(v),)+tuple(polar(Q,q,v,s,d) for s in S)
        part[v]=('sc',normalize_scaling(phi,q)) if ti else ('ex',phi)
    return part

def wl1(V,Q,q,d,base):
    """1-WL on the rank-3 isoClass scheme + individualize `base`."""
    n=len(V); idx={v:i for i,v in enumerate(V)}
    col=[0]*n
    for p,s in enumerate(base): col[idx[s]]=p+1
    def iso(w):
        if all(c==0 for c in w): return 0
        return 1 if Q(w)==0 else 2
    rel=[[iso(sub(V[i],V[j],q,d)) for j in range(n)] for i in range(n)]
    for _ in range(n):
        sig=[(col[i],tuple(sorted((rel[i][j],col[j]) for j in range(n) if j!=i))) for i in range(n)]
        o={};nc=[0]*n;k=0
        for i in range(n):
            if sig[i] not in o: o[sig[i]]=k;k+=1
            nc[i]=o[sig[i]]
        if nc==col: break
        col=nc
    return col

def run(d,q,eps,maxn=5000):
    V=list(itertools.product(range(q),repeat=d))
    if len(V)>maxn:
        print(f"  VO^{'+' if eps>0 else '-'}_{d}({q}): n={len(V)}>cap skip"); return
    Q=make_Q(d,q,eps); idx={v:i for i,v in enumerate(V)}; n=len(V)
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    base=[]; step=0; branchnodes=0; worst=0; steps_detail=[]
    while True:
        col=wl1(V,Q,q,d,base)
        # cells
        cells={}
        for i in range(n): cells.setdefault(col[i],[]).append(i)
        nonsing=[(c,mem) for c,mem in cells.items() if len(mem)>1]
        if not nonsing: break  # discrete
        # selected cell = lowest colour-id non-singleton (deterministic, iso-invariant-ish)
        c_sel,mem=min(nonsing,key=lambda x:x[0])
        # orbit-purity of the selected cell under Stab(base)
        orb=orbit_part(V,Q,q,base,d)
        orbs_in_cell=set(orb[V[i]] for i in mem)
        m=len(orbs_in_cell)
        worst=max(worst,m)
        if m>1: branchnodes+=1
        steps_detail.append((len(base),len(mem),m))
        # individualize min vertex of selected cell
        v=min(mem)
        base.append(V[v]); step+=1
        if step>n: print("  (no termination?!)"); break
    verdict="ALL orbit-pure ✓ (BranchingNodes=0, 1-WL suffices)" if branchnodes==0 else f"✗ {branchnodes} branch nodes (max {worst} orbits/cell)"
    print(f"  {nm}: descent {step} steps, leaf=discrete | selected-cell orbit-purity: {verdict}")
    # show the per-step (base_size, sel_cell_size, #orbits_in_sel_cell) for the first few
    head=", ".join(f"|S|={b}:cell{cs}/orb{mo}" for (b,cs,mo) in steps_detail[:6])
    print(f"      steps[:6]: {head}")

def run_defer(d,q,eps,maxn=5000):
    """C#-faithful: DEFERRAL selector — consume an orbit-pure ('symmetric') cell, defer
    multi-orbit cells, count a Phase-2/branch node only when NO orbit-pure cell exists
    (the rigid residue). Replicates ChainDescent.cs:251-281."""
    V=list(itertools.product(range(q),repeat=d))
    if len(V)>maxn: print(f"  skip n={len(V)}"); return
    Q=make_Q(d,q,eps); n=len(V); nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    base=[]; step=0; phase2=0; consumed=0; deferrals=0
    while True:
        col=wl1(V,Q,q,d,base)
        cells={}
        for i in range(n): cells.setdefault(col[i],[]).append(i)
        nonsing=sorted([(c,mem) for c,mem in cells.items() if len(mem)>1])
        if not nonsing: break
        orb=orbit_part(V,Q,q,base,d)
        pick=None
        for ci,(c,mem) in enumerate(nonsing):
            if len(set(orb[V[i]] for i in mem))==1:
                pick=(c,mem)
                if ci>0: deferrals+=1
                break
        if pick is None: phase2+=1; pick=nonsing[0]
        else: consumed+=1
        c,mem=pick; base.append(V[min(mem)]); step+=1
        if step>n: print("  no-term?!"); break
    verdict="SINGLE PATH ✓ (Phase2=0)" if phase2==0 else f"Phase2={phase2} (rigid residue: no orbit-pure cell)"
    print(f"  {nm}: {step} steps | consumed-symmetric={consumed}, deferrals={deferrals}, Phase2={phase2} | {verdict}")

if __name__=="__main__":
    print("=== DESCENT PROBE (naive first-cell selector): is the SELECTED cell orbit-pure at 1-WL? ===")
    for q in [3,5]: run(4,q,-1); run(4,q,+1)
    run(6,3,-1)
    print("=== WITH DEFERRAL (C#-faithful selector): does 1-WL give a single path? ===")
    for q in [3,5]: run_defer(4,q,-1); run_defer(4,q,+1)
    run_defer(6,3,-1)
