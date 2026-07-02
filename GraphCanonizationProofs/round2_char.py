import itertools
from model_gap import make_Q, sub, polar, orbit_part, isoclass, first_indep_anis, refines
def leg(a,q):
    a%=q
    return 0 if a==0 else (1 if pow(a,(q-1)//2,q)==1 else -1)
def ncls(c): return len(set(c.values()))
def same(P,Q_,V): return refines(P,Q_,V) and refines(Q_,P,V)
def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); z0=tuple([0]*d); a,b=anis[0],anis[1]; S=[z0,a,b]
    iso={w:isoclass(Q,q,d,w) for w in V}
    orb=orbit_part(V,Q,q,S,d)
    C={u:tuple(iso[sub(u,s,q,d)] for s in S) for u in V}
    # one WL round -> round2
    sig={}
    for u in V:
        ms={}
        for zz in V:
            if zz==u: continue
            k=(C[zz],iso[sub(u,zz,q,d)]); ms[k]=ms.get(k,0)+1
        sig[u]=(C[u],tuple(sorted(ms.items())))
    uq={s:i for i,s in enumerate(set(sig.values()))}; C2={u:uq[sig[u]] for u in V}
    def pf(x,y): return (4*Q(x)*Q(y)-polar(Q,q,x,y,d)**2)%q
    # square-class / chi(det) data to base {0,a,b}: chi(Q(u-s)) + chi(pairForm(u-s,u-t))
    def sqcl(u):
        diffs=[sub(u,s,q,d) for s in S]
        coords=[leg(Q(dd),q) for dd in diffs]
        for i in range(len(S)):
            for j in range(i+1,len(S)):
                coords.append(leg(pf(diffs[i],diffs[j]),q))
        return tuple(coords)
    SC={u:sqcl(u) for u in V}
    print(f"VO^{'+' if eps>0 else '-'}_{d}({q}): r2={ncls(C2)}  sqcl/chi(det)-profile={ncls(SC)}  orbits={ncls(orb)}")
    print(f"    C2 == sqcl? {same(C2,SC,V)} | C2 ⊑ sqcl (C2 finer)? {refines(C2,SC,V)} | sqcl ⊑ C2 (sqcl finer)? {refines(SC,C2,V)}")
for (d,q,eps) in [(4,3,-1),(4,5,-1),(4,7,-1),(4,5,+1)]:
    run(d,q,eps)
