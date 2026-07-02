import itertools
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model_gap import make_Q, sub, polar, first_indep_anis, span_of

def check(d,q,eps):
    V=list(itertools.product(range(q),repeat=d)); Q=make_Q(d,q,eps)
    anis=first_indep_anis(V,Q,q,d,d); a,b=anis[0],anis[1]
    W=span_of(q,[a,b],d)
    def gram(v): return (Q(v),polar(Q,q,v,a,d),polar(Q,q,v,b,d))
    # find plane point w and non-plane u with same gram
    gram_plane={gram(w):w for w in W}
    hits=[]
    for u in V:
        if u in W: continue
        g=gram(u)
        if g in gram_plane:
            hits.append((gram_plane[g],u,g))
    aniso_plane = all(Q(w)!=0 for w in W if w!=tuple([0]*d))
    print(f"VO^{'+' if eps>0 else '-'}_{d}({q}): plane anisotropic={aniso_plane}; "
          f"#plane-vs-nonplane same-Gram collisions = {len(hits)}")
    if hits:
        w,u,g=hits[0]
        print(f"   WITNESS: plane w={w} and non-plane u={u} share Gram-to-(a,b)={g}")
        print(f"   -> SameExactGram(w,u) holds but they are DIFFERENT orbits (w singleton in W, u not in W)")
        print(f"   -> WittExtendsToOrbit Q (a,b) is FALSE")
for eps in (-1,1): check(4,3,eps)
for eps in (-1,1): check(4,5,eps)
