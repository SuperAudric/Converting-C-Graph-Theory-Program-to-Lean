from collections import defaultdict
from itertools import product

def run(P, qcoef):
    pts=list(product(range(P),repeat=4))
    def sub(a,b): return tuple((a[i]-b[i])%P for i in range(4))
    # Q = x0 x1 + x2^2 + qcoef*x3^2 ; qcoef=1 -> (depends on -1 sq?), use nonsquare for '-'
    def Q(x): return (x[0]*x[1] + x[2]*x[2] + qcoef*x[3]*x[3])%P
    def iso(w):
        if all(c==0 for c in w): return 0
        return 1 if Q(w)==0 else 2
    def oneround_discrete(T):
        key={}
        for u in pts:
            h=defaultdict(int)
            for z in pts:
                if z==u: continue
                h[(tuple(iso(sub(z,t)) for t in T), iso(sub(z,u)))]+=1
            key[u]=frozenset(h.items())
        return len(set(key.values()))==len(pts)
    e=[(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    n0=sum(1 for x in pts if Q(x)==0)
    # type: O+_4 has n0 = q^3+(q-1)q ; O-_4 has q^3-(q-1)q
    typ = '+' if n0 > P**3 else '-'
    res_frame = oneround_discrete(e)
    # frame + one extra symmetry-breaking point
    extra=(0,0,1,1)
    res_fp = oneround_discrete(e+[extra])
    print(f"  q={P} qcoef={qcoef} type O^{typ} (#Q=0={n0}): std-frame one-round discrete? {res_frame};  frame+{extra} (size6)? {res_fp}")

# squares mod 3: {1}; nonsquare 2.  mod 5: squares {1,4}; nonsquare 2 or 3.
print("d=4:")
run(3,1)   # x2^2+x3^2, -1 nonsq mod3 -> anisotropic plane -> O^-
run(3,2)   # x2^2+2x3^2 : 2 nonsq -> isotropic plane? -> O^+
run(5,1)   # mod5 -1 = 4 = square -> x2^2+x3^2 isotropic -> O^+
run(5,2)   # 2 nonsquare mod5 -> x2^2+2x3^2 anisotropic -> O^-
