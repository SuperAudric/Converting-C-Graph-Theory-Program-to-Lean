import itertools, sys
from model_gap import make_Q, sub, polar, orbit_part, isoclass, first_indep_anis, refines

def legendre(a,q):
    a%=q
    if a==0: return 0
    return 1 if pow(a,(q-1)//2,q)==1 else -1

def ncls(col): return len(set(col.values()))
def same_partition(P,Q_,V): return refines(P,Q_,V) and refines(Q_,P,V)

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); z0=tuple([0]*d); a,b=anis[0],anis[1]
    S=[z0,a,b]
    iso={w:isoclass(Q,q,d,w) for w in V}
    orb=orbit_part(V,Q,q,S,d); norb=ncls(orb)
    # round 1 = 3iso (isoclass to base)
    C1={u:tuple(iso[sub(u,s,q,d)] for s in S) for u in V}
    cols=[C1]; names=["r1(3iso)"]
    C=C1
    for r in range(2,7):
        sig={}
        for u in V:
            ms={}
            for zz in V:
                if zz==u: continue
                k=(C[zz], iso[sub(u,zz,q,d)]); ms[k]=ms.get(k,0)+1
            sig[u]=(C[u], tuple(sorted(ms.items())))
        uniq={s:i for i,s in enumerate(set(sig.values()))}
        Cn={u:uniq[sig[u]] for u in V}
        stable=(ncls(Cn)==ncls(C))
        cols.append(Cn); names.append(f"r{r}")
        C=Cn
        if stable: break
    line=f"VO^{'+' if eps>0 else '-'}_{d}({q}) n={q**d}: " + " ".join(f"{nm}={ncls(c)}" for nm,c in zip(names,cols)) + f" | orbits={norb}"
    print(line)
    # characterize round 2 (index 1 if present)
    if len(cols)>=2:
        C2=cols[1]
        # candidate square-class invariants for u, over base {0,a,b}
        def chiQ(u,s): return legendre(Q(sub(u,s,q,d)),q)
        cand = {
          "chiQ_to_base (3 coords)": {u:tuple(chiQ(u,s) for s in S) for u in V},
          "chi(Qu),chi(pol_a),chi(pol_b)": {u:(legendre(Q(u),q),legendre(polar(Q,q,u,a,d),q),legendre(polar(Q,q,u,b,d),q)) for u in V},
          "chiQ_to_base + chi(pol_a),chi(pol_b) (5)": {u:tuple(chiQ(u,s) for s in S)+(legendre(polar(Q,q,u,a,d),q),legendre(polar(Q,q,u,b,d),q)) for u in V},
          "chi(Q(u-s)) all s in {0,a,b,a+b}": {u:tuple(legendre(Q(sub(u,s,q,d)),q) for s in [z0,a,b,tuple((a[i]+b[i])%q for i in range(d))]) for u in V},
        }
        print(f"    round2 = {ncls(C2)} classes. Match tests:")
        for nm,cc in cand.items():
            eq = same_partition(C2,cc,V)
            ref = refines(C2,cc,V)  # C2 finer than cand
            refr = refines(cc,C2,V) # cand finer than C2
            print(f"      [{ncls(cc):3d} cls] {nm}: equal={eq} C2⊑cand={ref} cand⊑C2={refr}")
        # does round2 refine to Gram? (it shouldn't fully)
        print(f"      C2 refines orbits(Gram)? {refines(C2,orb,V)} ; orbits refine C2? {refines(orb,C2,V)}")
    # STRATIFIED YIELD: round2->round3. take pairs same-C2 diff-Gram; check r3 separates + margin
    if len(cols)>=3:
        C2=cols[1]; C3=cols[2]
        # group by (C2, differ in orb)
        from collections import defaultdict
        byC2=defaultdict(list)
        for u in V: byC2[C2[u]].append(u)
        pairs_sameC2_diffGram=0; sep_by_r3=0
        margins=[]
        checked=0
        for c2v,us in byC2.items():
            # pick representatives of distinct orbits within this C2 class
            reps={}
            for u in us:
                reps.setdefault(orb[u],u)
            rl=list(reps.values())
            for i in range(len(rl)):
                for j in range(i+1,len(rl)):
                    u,up=rl[i],rl[j]; pairs_sameC2_diffGram+=1
                    if C3[u]!=C3[up]: sep_by_r3+=1
                    checked+=1
        print(f"    STRATIFIED YIELD (r2->r3): pairs (sameC2, diffGram)={pairs_sameC2_diffGram}, separated by r3={sep_by_r3}  -> {'ALL separated' if sep_by_r3==pairs_sameC2_diffGram else 'SOME NOT SEP'}")

for (d,q,eps) in [(4,3,-1),(4,3,+1),(4,5,-1),(4,5,+1),(4,7,-1)]:
    run(d,q,eps)
