import itertools

def legendre(a, q):
    a %= q
    if a == 0: return 0
    return 1 if pow(a, (q-1)//2, q) == 1 else -1

def non_qr(q):
    for n in range(2, q):
        if legendre(n, q) == -1: return n
    return None

def run(q):
    nu = non_qr(q)  # anisotropic minus form Q(x,y)=x^2 - nu*y^2
    def Q(v): return (v[0]*v[0] - nu*v[1]*v[1]) % q
    def polar(u,v): return (2*(u[0]*v[0] - nu*u[1]*v[1])) % q
    def sub(u,v): return ((u[0]-v[0])%q,(u[1]-v[1])%q)
    def pairForm(x,y): return (4*Q(x)*Q(y) - polar(x,y)*polar(x,y)) % q
    def isoClass(v):
        if v==(0,0): return 0
        return 1 if Q(v)==0 else 2
    W = [(x,y) for x in range(q) for y in range(q)]
    a=(1,0); b=(0,1)
    assert Q(a)!=0 and Q(b)!=0 and polar(a,b)==0, (Q(a),Q(b),polar(a,b))
    base=[(0,0),a,b]

    # observable-per-pair used in SeparatedBy: chi(pairForm(t0-w, t-w))
    def sepPair(P, w, wp):
        # exists ordered t,t0 in P, t!=t0, chi differs
        for t in P:
            for t0 in P:
                if t==t0: continue
                cw  = legendre(pairForm(sub(t0,w),  sub(t,w)),  q)
                cwp = legendre(pairForm(sub(t0,wp), sub(t,wp)), q)
                if cw != cwp: return True
        return False

    def sepPairChiIso(P, w, wp):
        # allow chi OR isoClass-to-anchor to separate
        for t in P:
            if isoClass(sub(t,w)) != isoClass(sub(t,wp)): return True
        return sepPair(P,w,wp)

    def closure(sepfn):
        pinned=set(base)
        rounds=0
        while True:
            rounds+=1
            new=set()
            for w in W:
                if w in pinned: continue
                if all(sepfn(pinned,w,wp) for wp in W if wp!=w):
                    new.add(w)
            if not new: break
            pinned |= new
        return len(pinned), rounds

    # (B) real 1-WL color refinement on W (base individualized), edge color = isoClass(w-z)
    def wl_refine():
        color={}
        for w in W:
            color[w]= ('base',w) if w in base else ('gen',)
        rounds=0
        while True:
            rounds+=1
            sig={}
            for w in W:
                ms={}
                for z in W:
                    key=(color[z], isoClass(sub(w,z)))
                    ms[key]=ms.get(key,0)+1
                sig[w]=(color[w], tuple(sorted(ms.items())))
            # relabel
            uniq={s:i for i,s in enumerate(sorted(set(sig.values()), key=str))}
            newcolor={w:uniq[sig[w]] for w in W}
            ncls_new=len(set(newcolor.values()))
            ncls_old=len(set(color.values()))
            color=newcolor
            if ncls_new==ncls_old:
                break
        discrete = (len(set(color.values()))==len(W))
        return len(set(color.values())), len(W), discrete, rounds

    npin_chi,r1 = closure(sepPair)
    npin_ci, r2 = closure(sepPairChiIso)
    ncls, ntot, disc, wr = wl_refine()
    print(f"q={q:3d} nu={nu:2d} |W|={q*q:4d} | closure_chi: pinned={npin_chi:4d} (r={r1}) | closure_chi+iso: pinned={npin_ci:4d} (r={r2}) | 1WL: cls={ncls}/{ntot} discrete={disc} (r={wr})")

for q in [3,5,7,11,13,17,19,23,29,31]:
    run(q)
