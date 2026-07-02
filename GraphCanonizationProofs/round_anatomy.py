#!/usr/bin/env python3
"""
ROUND ANATOMY — what each 1-WL round DETERMINES at a span-dim-2 base (2026-07-02).

β1 (bounded-round) claims a 3-rung information tower:
  round 1 : iso3 to base       (is Q(u-t)=0 ? — presence bits)
  round 2 : square-class (chi) of the Gram to base   (chi-values)
  round 3 : exact Gram to base = orbits              (field values)
VO^- recovers @3, VO^+ @4 (recovery_depth_probe) — this probe checks WHICH invariant each
round's partition EQUALS, to validate the tower and locate the extra plus-type rung.

For each round r we compare the WL partition C_r to reference partitions:
  ISO  = (iso3 u, iso3 u-a, iso3 u-b)
  CHI  = (leg Q(u), leg polar(u,a), leg polar(u,b))        [square-class of Gram to base]
  GRAM = (Q u, polar(u,a), polar(u,b))                     [exact Gram to base]
  ORB  = Stab({0,a,b})-orbits
Ambient 1-WL exactly as recovery_depth_probe (iso3 edge colours, base individualised).
"""
import itertools, sys
from model_gap import make_Q, sub, polar, isoclass, first_indep_anis, orbit_part, refines

def leg(a,q):
    a%=q
    if a==0: return 0
    return 1 if pow(a,(q-1)//2,q)==1 else -1

def eq_part(A,B,V): return refines(A,B,V) and refines(B,A,V)
def ncls(C,V): return len(set(C[v] for v in V))

def wl_round(V,Q,q,d,col):
    n=len(V)
    sig={}
    for v in V:
        row=tuple(sorted((isoclass(Q,q,d,sub(v,z,q,d)), col[z]) for z in V if z!=v))
        sig[v]=(col[v],row)
    uniq={s:i for i,s in enumerate(sorted(set(sig.values()),key=str))}
    return {v:uniq[sig[v]] for v in V}

def run(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); a,b=anis[0],anis[1]
    S=[tuple([0]*d),a,b]
    orb=orbit_part(V,Q,q,S,d)
    ISO ={v:(isoclass(Q,q,d,v),isoclass(Q,q,d,sub(v,a,q,d)),isoclass(Q,q,d,sub(v,b,q,d))) for v in V}
    CHI ={v:(leg(Q(v),q),leg(polar(Q,q,v,a,d),q),leg(polar(Q,q,v,b,d),q)) for v in V}
    GRAM={v:(Q(v),polar(Q,q,v,a,d),polar(Q,q,v,b,d)) for v in V}
    refs=[("ISO",ISO),("CHI",CHI),("GRAM",GRAM),("ORB",orb)]
    nm=f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    print(f"{nm}  |V|={len(V)}  ref#cls: ISO={ncls(ISO,V)} CHI={ncls(CHI,V)} GRAM={ncls(GRAM,V)} ORB={ncls(orb,V)}")
    # initial: base individualised
    col={v:0 for v in V}
    for p,s in enumerate(S): col[s]=p+1
    for r in range(0,7):
        if r>0:
            nc=wl_round(V,Q,q,d,col)
            if ncls(nc,V)==ncls(col,V):
                col=nc; matches=[nm2 for nm2,P in refs if eq_part(col,P,V)]
                print(f"  round {r}: #cls={ncls(col,V):4d}  ==[{','.join(matches) or '-'}]  (STABLE)"); break
            col=nc
        matches=[nm2 for nm2,P in refs if eq_part(col,P,V)]
        print(f"  round {r}: #cls={ncls(col,V):4d}  ==[{','.join(matches) or '-'}]")

if __name__=="__main__":
    for eps in (-1,1): run(4,3,eps)
    for eps in (-1,1): run(4,5,eps)
