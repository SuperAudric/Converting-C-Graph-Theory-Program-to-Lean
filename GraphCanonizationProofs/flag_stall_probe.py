#!/usr/bin/env python3
"""
FLAG LEAD + round-2 characterization — the WL-strata frontier stall evidence (recovery doc §9.8.9).

After the factorization check (`factorization_probe.py`) ruled out a clean assembly, two diagnostics
decide whether the from-scratch WL-strata build has ANY handhold:

  A. WHAT IS round-2 beyond chi(det)?  Reconstruct the true round-2 colouring C2 from candidate
     algebraic invariants (ISO, chi(det)-tuple, actual joint-isotropy COUNTS).  Result: NONE of them,
     nor their combination, equals C2 (incomparable) => C2 is a Stab-invariant COUNT PROFILE
     (a "count of counts"), not the level set of any character => no character-sum handle for L3.

  B. THE FLAG LEAD.  orbits = (gramK, FLAG), FLAG = plane membership (an algebraic locus, not a count
     of counts).  Two tests:
       (1) does the (ISO, complement-class)-stratified isotropic count separate orbits?  -> NO (misses
           gramK's exact bilinear values), so the flag alone doesn't break the crux.
       (2) is FLAG 1-WL-determined EARLIER than orbits (a cheap flag-first decomposition)? -> NO, the
           flag is determined at the same round r* as the orbits.

  VERDICT: the WL-strata frontier STALLS.  gramK recovery is the irreducible circular crux; every clean
  observable misses the exact bilinear values, and the only object carrying them (round-2) has no handle.
  => pivot to Route C (recovery doc §7).
"""
import itertools
from model_gap import make_Q, sub, polar, isoclass, first_indep_anis, orbit_part, refines, span_of

def leg(a, q):
    a %= q; return 0 if a == 0 else (1 if pow(a, (q-1)//2, q) == 1 else -1)
def det_mod(M, q):
    n = len(M)
    if n == 1: return M[0][0] % q
    if n == 2: return (M[0][0]*M[1][1]-M[0][1]*M[1][0]) % q
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])) % q
def gm(vs, Q, q, d): return [[polar(Q, q, x, y, d) for y in vs] for x in vs]
def ncls(C, V): return len(set(C[v] for v in V))
def eqp(A, B, V): return refines(A, B, V) and refines(B, A, V)
def wl_round(V, Q, q, d, col):
    sig = {v: (col[v], tuple(sorted((isoclass(Q,q,d,sub(v,z,q,d)), col[z]) for z in V if z != v))) for v in V}
    o = {s: i for i, s in enumerate(sorted(set(sig.values()), key=str))}
    return {v: o[sig[v]] for v in V}

def run(d, q, eps):
    V = list(itertools.product(range(q), repeat=d)); Q = make_Q(d, q, eps)
    nm = f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis = first_indep_anis(V, Q, q, d, d); a, b = anis[0], anis[1]; S = [tuple([0]*d), a, b]
    W = span_of(q, [a, b], d)
    orb = orbit_part(V, Q, q, S, d); norb = ncls(orb, V)
    GRAM = {v: (Q(v), polar(Q,q,v,a,d), polar(Q,q,v,b,d)) for v in V}
    ISO = {v: (isoclass(Q,q,d,v), isoclass(Q,q,d,sub(v,a,q,d)), isoclass(Q,q,d,sub(v,b,q,d))) for v in V}

    # true round-2 colouring
    col = {v: 0 for v in V}
    for p, s in enumerate(S): col[s] = p+1
    col = wl_round(V, Q, q, d, col); C2 = wl_round(V, Q, q, d, col)

    # A. reconstruct C2 from algebraic invariants
    Iso = {x: set(w for w in V if Q(sub(w,x,q,d)) == 0) for x in [a, b]}
    IsoZ = {z: set(w for w in V if Q(sub(w,z,q,d)) == 0) for z in V}
    Nprof = {z: (len(IsoZ[z]&Iso[a]), len(IsoZ[z]&Iso[b]), len(IsoZ[z]&Iso[a]&Iso[b])) for z in V}
    CHI = {z: tuple(leg(det_mod(gm(c,Q,q,d), q), q) for c in ([z],[z,a],[z,b],[z,a,b])) for z in V}
    both = {v: (ISO[v], CHI[v], Nprof[v]) for v in V}
    print(f"{nm} C2#={ncls(C2,V)} | (ISO,chi,count)#={ncls(both,V)} == C2? {eqp(both,C2,V)}  "
          f"[C2 = Stab-invariant count profile, no character handle]")

    # B. FLAG lead
    def comp3(z):
        if z in W: return 0
        pa = polar(Q,q,z,a,d); pb = polar(Q,q,z,b,d)
        ca = (pa*pow((2*Q(a))%q, q-2, q)) % q; cb = (pb*pow((2*Q(b))%q, q-2, q)) % q
        zW = tuple((ca*a[i]+cb*b[i]) % q for i in range(d))
        return 1 if (Q(z)-Q(zW)) % q == 0 else 2
    COMP = {z: comp3(z) for z in V}; FLAG = {z: (z in W) for z in V}
    strat = {z: (ISO[z], COMP[z]) for z in V}; labels = sorted(set(strat.values()))
    P = {}
    for u in V:
        cnt = {L: 0 for L in labels}
        for z in V:
            if z != u and Q(sub(u,z,q,d)) == 0: cnt[strat[z]] += 1
        P[u] = (ISO[u], COMP[u], tuple(cnt[L] for L in labels))
    col = {v: 0 for v in V}
    for p, s in enumerate(S): col[s] = p+1
    detF = detC = rstar = None
    for r in range(1, 8):
        col = wl_round(V, Q, q, d, col)
        if detF is None and refines(col, FLAG, V): detF = r
        if detC is None and refines(col, COMP, V): detC = r
        if ncls(col, V) == norb: rstar = r; break
    print(f"   ORB#={norb} | (ISO,COMP)-strat count #cls={ncls(P,V)} refines-ORB={refines(P,orb,V)}"
          f" | FLAG@r={detF} COMP@r={detC} orbits@r*={rstar}  [flag NOT earlier than orbits]")

if __name__ == "__main__":
    print("=== WL-strata frontier STALL evidence (round-2 = count-of-counts; FLAG lead negative) ===\n")
    for eps in (-1, 1): run(4, 3, eps)
    for eps in (-1, 1): run(4, 5, eps)
    for eps in (-1, 1): run(4, 7, eps)
