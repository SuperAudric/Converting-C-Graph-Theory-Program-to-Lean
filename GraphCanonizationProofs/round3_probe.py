# Round 3: count z isotropic-to-u, stratified by z's class. Compare EXACT-gram strata vs REAL round-2 strata, vs ORBITS.
import itertools
from collections import defaultdict
from model_gap import make_Q, sub, polar, orbit_part, isoclass, first_indep_anis, refines
def ncls(c): return len(set(c.values()))
def same(P,R,V): return refines(P,R,V) and refines(R,P,V)

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); z0=tuple([0]*d); a,b=anis[0],anis[1]; S=[z0,a,b]
    iso={w:isoclass(Q,q,d,w) for w in V}
    orb=orbit_part(V,Q,q,S,d)
    gram={u:(Q(u),polar(Q,q,u,a,d),polar(Q,q,u,b,d)) for u in V}
    # round1 -> round2 colouring C2 (real WL strata)
    C1={u:tuple(iso[sub(u,s,q,d)] for s in S) for u in V}
    sig={}
    for u in V:
        ms={}
        for zz in V:
            if zz==u: continue
            k=(C1[zz],iso[sub(u,zz,q,d)]); ms[k]=ms.get(k,0)+1
        sig[u]=(C1[u],tuple(sorted(ms.items())))
    uq={s:i for i,s in enumerate(set(sig.values()))}; C2={u:uq[sig[u]] for u in V}
    # generic counter: T against a stratifier `cls` (dict u->label): T(u)=tuple over labels of #{z: cls(z)=lbl, Q(u-z)=0}
    def Tprofile(cls):
        labs=sorted(set(cls.values()),key=str); li={l:i for i,l in enumerate(labs)}
        T={}
        for u in V:
            cnt=[0]*len(labs)
            for z in V:
                if z==u: continue
                if iso[sub(u,z,q,d)]==2: continue  # Q(u-z)=0
                cnt[li[cls[z]]]+=1
            T[u]=tuple(cnt)
        return T
    T_exact=Tprofile(gram)          # count against EXACT-gram strata (idealized)
    T_r2   =Tprofile(C2)            # count against REAL round-2 strata (actual WL round 3)
    # also C2 refined by T_r2 = real round-3 colouring C3
    C3={u:(C2[u],T_r2[u]) for u in V}
    tag=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    no=ncls(orb)
    print(f"{tag}: orbits={no}")
    print(f"    T_exact(gram-strata): cls={ncls(T_exact):4d}  == orbits? {same(T_exact,orb,V)}  refines orbits? {refines(T_exact,orb,V)}")
    print(f"    T_r2  (round2-strata): cls={ncls(T_r2):4d}  == orbits? {same(T_r2,orb,V)}  refines orbits? {refines(T_r2,orb,V)}")
    print(f"    C3=C2+T_r2 (real r3) : cls={ncls(C3):4d}  == orbits? {same(C3,orb,V)}")
    if not same(C3,orb,V):
        # residual: orbits merged by C3
        byC3=defaultdict(set)
        for u in V: byC3[C3[u]].add(orb[u])
        mixed=[frozenset(s) for s in byC3.values() if len(s)>1]
        print(f"       real-r3 residual: {len(mixed)} C3-classes each merging >1 orbit (these split at r4)")

for (d,q,eps) in [(4,3,-1),(4,5,-1),(4,3,+1),(4,5,+1),(4,7,-1)]:
    run(d,q,eps)
