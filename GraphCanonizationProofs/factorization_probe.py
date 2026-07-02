#!/usr/bin/env python3
"""
FACTORIZATION CHECK for the round-3 step lemma L3 (recovery doc §9.8.8 step 2).

Decides whether L3's mixed sum is an ASSEMBLY of landed pieces or a new entangled sum, by
testing the structural claim that makes it an assembly:

  CLAIM 1 (the decider): Zprof(z) = C2(z) is a FUNCTION of gramK(z) = (Qz, polar(z,a), polar(z,b)).
    ==> the round-3 observable n_sigma(u) = #{z: Zprof(z)=sigma, Q(u-z)=0} = sum_{g: F(g)=sigma} T(u;g)
        is a chi(det)-fibre PARTIAL SUM of Piece 1's gram-stratified T  ==> assembly, not from-scratch.
    Test: GRAM partition refines C2 (gramK finer), and C2 does NOT refine GRAM (strictly coarser).

  CLAIM 2 (the mechanism): Zprof = the chi(det G_config)-tuple over configs {z}u S', S' subset {a,b},
    each det G_config a polynomial in gramK(z).  Test: partition by (ISO, chi(det) over the 4 configs)
    equals C2.  Confirms Zprof factors through chi(det) of gramK-quadratics (the seal's configGaussSum_eq_detK).

  CLAIM 3 (d-uniformity of the structure): CLAIM 1 + 2 hold identically at d=4 and d=6.

If 1+2 hold: L3's transform = chi(det)-weighted combos of Piece 1's countHat; the d-dim z-integral is
pure-additive (isoConeSum, landed) reducing to the pencil determinant (landed), leaving a d-independent
2-dim (r,s) residual. => clean assembly. If CLAIM 1 fails, Zprof sees beyond the plane and it is entangled.
"""
import itertools
from model_gap import make_Q, sub, polar, isoclass, first_indep_anis, orbit_part, refines

def leg(a, q):
    a %= q
    if a == 0: return 0
    return 1 if pow(a, (q-1)//2, q) == 1 else -1

def det_mod(M, q):
    n = len(M)
    if n == 1: return M[0][0] % q
    if n == 2: return (M[0][0]*M[1][1] - M[0][1]*M[1][0]) % q
    # n == 3 cofactor
    d = (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
         - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
         + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
    return d % q

def gram_matrix(vs, Q, q, d):
    return [[polar(Q, q, u, v, d) for v in vs] for u in vs]

def wl_round(V, Q, q, d, col):
    sig = {}
    for v in V:
        row = tuple(sorted((isoclass(Q, q, d, sub(v, z, q, d)), col[z]) for z in V if z != v))
        sig[v] = (col[v], row)
    o = {s: i for i, s in enumerate(sorted(set(sig.values()), key=str))}
    return {v: o[sig[v]] for v in V}

def ncls(C, V): return len(set(C[v] for v in V))
def eqp(A, B, V): return refines(A, B, V) and refines(B, A, V)

def run(d, q, eps):
    V = list(itertools.product(range(q), repeat=d)); Q = make_Q(d, q, eps)
    nm = f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis = first_indep_anis(V, Q, q, d, d); a, b = anis[0], anis[1]
    S = [tuple([0]*d), a, b]
    orb = orbit_part(V, Q, q, S, d)
    GRAM = {v: (Q(v), polar(Q,q,v,a,d), polar(Q,q,v,b,d)) for v in V}
    ISO  = {v: (isoclass(Q,q,d,v), isoclass(Q,q,d,sub(v,a,q,d)), isoclass(Q,q,d,sub(v,b,q,d))) for v in V}

    # actual round-2 colouring C2 = refine(refine(base-seed))
    col = {v: 0 for v in V}
    for p, s in enumerate(S): col[s] = p+1
    col = wl_round(V, Q, q, d, col)     # round 1 = ISO
    C2  = wl_round(V, Q, q, d, col)     # round 2 = Zprof

    # chi(det) tuple over configs {z}, {z,a}, {z,b}, {z,a,b}
    CHIDET = {}
    for z in V:
        cfgs = [[z], [z, a], [z, b], [z, a, b]]
        CHIDET[z] = tuple(leg(det_mod(gram_matrix(c, Q, q, d), q), q) for c in cfgs)
    # combined structural predictor = (ISO, CHIDET)
    PRED = {v: (ISO[v], CHIDET[v]) for v in V}

    print(f"{nm} |V|={len(V)}  GRAM#={ncls(GRAM,V)} C2#={ncls(C2,V)} ORB#={ncls(orb,V)} "
          f"CHIDET#={ncls(CHIDET,V)} PRED#={ncls(PRED,V)}")
    # CLAIM 1
    c1a = refines(GRAM, C2, V)      # gramK finer than Zprof  (Zprof = function of gramK)
    c1b = refines(C2, GRAM, V)      # Zprof finer than gramK  (should be FALSE)
    print(f"  CLAIM1  gramK->Zprof (Zprof=fn of gramK): {c1a}   | Zprof->gramK (strictly coarser? expect NOT finer): {c1b}")
    # CLAIM 2
    c2 = eqp(PRED, C2, V)
    print(f"  CLAIM2  (ISO, chi(det)_configs) == C2 : {c2}   [refines each way: "
          f"{refines(PRED,C2,V)}/{refines(C2,PRED,V)}]")

if __name__ == "__main__":
    print("=== FACTORIZATION CHECK: is Zprof a function of gramK, via chi(det)? ===\n")
    for eps in (-1, 1): run(4, 3, eps)
    for eps in (-1, 1): run(4, 5, eps)
    for eps in (-1, 1): run(4, 7, eps)
    print("--- d-uniformity of the structural claim (d=6, q=3) ---")
    for eps in (-1, 1): run(6, 3, eps)
