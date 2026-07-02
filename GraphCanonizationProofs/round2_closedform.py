# Characterize round 2 = seal's jointIsoCountK-profile over sub-configs of {0,a,b} ?
import itertools
from model_gap import make_Q, sub, orbit_part, isoclass, first_indep_anis, refines
def ncls(c): return len(set(c.values()))
def same(P,R,V): return refines(P,R,V) and refines(R,P,V)

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); z0=tuple([0]*d); a,b=anis[0],anis[1]; S=[z0,a,b]
    iso={w:isoclass(Q,q,d,w) for w in V}
    orb=orbit_part(V,Q,q,S,d)
    # round1 (3iso), round2
    C1={u:tuple(iso[sub(u,s,q,d)] for s in S) for u in V}
    sig={}
    for u in V:
        ms={}
        for zz in V:
            if zz==u: continue
            k=(C1[zz],iso[sub(u,zz,q,d)]); ms[k]=ms.get(k,0)+1
        sig[u]=(C1[u],tuple(sorted(ms.items())))
    uq={s:i for i,s in enumerate(set(sig.values()))}; C2={u:uq[sig[u]] for u in V}
    # jointIsoCountK(u,Ssub) = #{z!=u : Q(z-u)=0, Q(z-t)=0 for t in Ssub}
    subs=[]
    for r in range(0,4):
        for c in itertools.combinations(S,r): subs.append(c)
    def jic(u,Ssub):
        cnt=0
        for z in V:
            if z==u: continue
            if iso[sub(u,z,q,d)]==2: continue     # Q(u-z)=0 required
            ok=True
            for t in Ssub:
                if iso[sub(z,t,q,d)]==2: ok=False; break
            if ok: cnt+=1
        return cnt
    Zprof={u:tuple(jic(u,Ss) for Ss in subs) for u in V}
    # seal-profile ALSO paired with C1 (the base-membership pattern the seal individualizes)
    ZprofC1={u:(C1[u],Zprof[u]) for u in V}
    tag=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    print(f"{tag}: r2={ncls(C2)}  Zprof={ncls(Zprof)}  Zprof+C1={ncls(ZprofC1)}  orbits={ncls(orb)}")
    print(f"    r2 == Zprof+C1 ? {same(C2,ZprofC1,V)}  | r2⊑(Zprof+C1)? {refines(C2,ZprofC1,V)}  | (Zprof+C1)⊑r2? {refines(ZprofC1,C2,V)}")

for (d,q,eps) in [(4,3,-1),(4,5,-1),(4,7,-1),(4,5,+1),(4,3,+1)]:
    run(d,q,eps)
