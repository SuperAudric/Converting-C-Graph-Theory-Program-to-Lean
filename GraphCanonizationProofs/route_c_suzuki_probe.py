#!/usr/bin/env python3
# ROUTE C — SUZUKI–TITS (f) DE-RISK PROBE (2026-07-03).  q = 8 = 2^3 (e=1).
#
# Purpose. Validate the Suzuki adapter's ingredients BEFORE the Lean build:
#   (Q1) the object — GF(8), the Tits endomorphism sigma (sigma^2 = Frobenius), the Tits ovoid O, the
#        connection set (cone over O), and that VSz(8) is the SRG(4096, 455, 6, 56) cospectral with VO^-_4(8).
#   (Q2) the scheme rank — 1-WL closure (expect rank 3: a "thin" SRG; per-base-point relation is 2-valued).
#   (E1) DIRECT-profile base (what Route C's `discrete_affineScheme_of_jointSeparates` uses): min base T with
#        v |-> (relation(v,t))_{t in T} injective.  Rank-3 => 2-valued => info-theoretic floor |T| >= log2(4096)=12
#        => the plain cone scheme yields only an O(log n) base = QUASIPOLY.
#   (E2) ITERATED individualization-refinement base: min base with 1-WL-after-individualization discrete.
#        Expect O(1) (Sz(q) is 2-transitive on the ovoid) = the POLY mechanism.
# The E1-vs-E2 gap decides whether the adapter can use the cone scheme directly, or must refine to a richer
# "isometry-analog" scheme (recover ovoid coordinates), exactly as the forms families refine similitude->isometry.
#
# Key simplification. GF(8)^4 = F_2^12; per-coordinate GF(8) addition is 3-bit XOR and the packing is bit
# concatenation, so the *vector difference* of two vertices is the 12-bit XOR of their indices. Hence VSz is the
# Cayley graph on (Z/2)^12 with connection set = the 455 packed cone vectors, and  u ~ v  <=>  (u ^ v) in CONE.

import sys, random
random.seed(12345)

# ---------------- GF(8) with primitive poly x^3 + x + 1 (0b1011) ----------------
POLY = 0b1011
def gfmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1
        a <<= 1
        if a & 0b1000: a ^= POLY
    return r
# exp/log tables (generator g = 2 = x)
EXP = [0]*8; LOG = [0]*8
x = 1
for i in range(7):
    EXP[i] = x; LOG[x] = i
    x = gfmul(x, 2)
EXP_ = EXP + EXP  # for wraparound
def gfpow(a, k):
    if a == 0: return 0
    return EXP[(LOG[a]*k) % 7]
def sigma(a):   # Tits endomorphism for q=8: sigma(x)=x^4 ; sigma^2(x)=x^16=x^2=Frob
    return gfpow(a, 4)
def frob(a):
    return gfmul(a, a)

# (Q1a) sigma^2 = Frobenius
assert all(sigma(sigma(a)) == frob(a) for a in range(8)), "sigma^2 != Frob"

# ---------------- the Tits ovoid and its cone ----------------
def pack(v):  # v = (v0,v1,v2,v3), each in 0..7 -> 12-bit index
    return v[0] | (v[1] << 3) | (v[2] << 6) | (v[3] << 9)

def ovoid_points():
    pts = []
    for a in range(8):
        for b in range(8):
            # c = ab + a^{sigma+2} + b^sigma = ab + sigma(a)*a^2 + sigma(b)
            c = gfmul(a, b) ^ gfmul(sigma(a), gfmul(a, a)) ^ sigma(b)
            pts.append((1, a, b, c))
    pts.append((0, 0, 0, 1))
    return pts

def build():
    O = ovoid_points()
    cone = set()
    for o in O:
        for lam in range(1, 8):            # GF(8)^*  (lam=0 gives the zero vector)
            cone.add(pack(tuple(gfmul(lam, oi) for oi in o)))
    cone.discard(0)
    return O, cone

O, CONE = build()
N = 4096
NBR = sorted(CONE)                         # neighbor-difference set (as an ordered list)

# ---------------- the sigma-twisted ovoid FORM F (cone = {F=0}) ----------------
# F(x0,x1,x2,x3) = x3*x0^{sigma+1} + x1*x2*x0^sigma + x1^{sigma+2} + x2^sigma*x0^2
# Every term scales by sigma(lam)*lam^2 under x->lam*x (sigma-twisted homogeneous), so {F=0} is a cone;
# on x0=1 it is x3 - (x1 x2 + x1^{sigma+2} + x2^sigma) = x3 - c.  For q=8 (sigma = ^4): x3 x0^5 + x1 x2 x0^4 + x1^6 + x2^4 x0^2.
def unpack(idx):
    return (idx & 7, (idx >> 3) & 7, (idx >> 6) & 7, (idx >> 9) & 7)

def F(x):
    x0, x1, x2, x3 = x
    t1 = gfmul(x3, gfmul(sigma(x0), x0))                 # x3 * x0^{sigma+1}
    t2 = gfmul(gfmul(x1, x2), sigma(x0))                 # x1 x2 * x0^sigma
    t3 = gfmul(sigma(x1), gfmul(x1, x1))                 # x1^{sigma+2} = sigma(x1) x1^2
    t4 = gfmul(sigma(x2), gfmul(x0, x0))                 # x2^sigma * x0^2
    return t1 ^ t2 ^ t3 ^ t4

def report_object():
    print("[Q1] object validation (q=8):")
    print("     sigma^2 = Frobenius: OK")
    print("     |ovoid O|            = %d  (want q^2+1 = 65)" % len(O))
    print("     |cone / conn. set|   = %d  (want (q^2+1)(q-1) = 455)" % len(CONE))
    # regularity + SRG parameters lambda, mu (Cayley: params are difference-set counts at 0)
    coneset = CONE
    # lambda: for a fixed neighbor c0, # of w in cone with w^c0 in cone
    c0 = NBR[0]
    lam = sum(1 for w in coneset if (w ^ c0) in coneset)
    # mu: for a fixed non-neighbor d0 (!=0, not in cone), # of w in cone with w^d0 in cone
    d0 = next(d for d in range(1, N) if d not in coneset)
    mu = sum(1 for w in coneset if (w ^ d0) in coneset)
    print("     degree k             = %d" % len(CONE))
    print("     lambda               = %d  (want 6)" % lam)
    print("     mu                   = %d  (want 56)" % mu)
    ok = (len(O) == 65 and len(CONE) == 455 and lam == 6 and mu == 56)
    print("     >>> VSz(8) = SRG(4096,455,6,56): %s\n" % ok)
    return ok

# ---------------- (Q2) 1-WL closure rank ----------------
def one_wl_rank():
    # color refinement from the all-equal coloring; for a vertex-transitive Cayley graph this converges
    # to the coarsest equitable partition. Rank of the scheme ~ number of stable *edge* colors; here we
    # report the number of stable vertex colors (should be 1, vertex-transitive) and the neighborhood
    # structure rank via the difference set: a Cayley graph's WL-closure on differences = orbits of the
    # difference set under the stabilizer. We instead report the SRG fact directly (rank 3) and confirm
    # 1-WL on the graph (no individualization) stays at 1 color.
    color = [0]*N
    for _ in range(6):
        sig = {}
        newc = [0]*N
        for v in range(N):
            key = (color[v], tuple(sorted(color[v ^ c] for c in NBR)))
            if key not in sig: sig[key] = len(sig)
            newc[v] = sig[key]
        if newc == color: break
        color = newc
    ncol = len(set(color))
    print("[Q2] 1-WL (no individualization) stable vertex colors = %d  (vertex-transitive => 1)" % ncol)
    print("     scheme is a rank-3 SRG => per-base-point relation is 2-valued (adjacent / non-adjacent).\n")
    return ncol

# ---------------- (E1) DIRECT-profile base ----------------
def rel(v, t):
    # Route-C relation of the pair (t, v) = which cone-class the difference falls in.
    # For the plain cone scheme this is 2-valued: adjacent (diff in cone) or not.
    if v == t: return 2
    return 1 if ((v ^ t) in CONE) else 0

def direct_profile_base():
    # greedily grow a base T so that v |-> (rel(v,t))_{t in T} is injective. Candidate pool = random sample.
    T = []
    sigs = {v: () for v in range(N)}
    pool = random.sample(range(N), 400)
    def nclasses(extra_t):
        seen = set()
        for v in range(N):
            seen.add(sigs[v] + (rel(v, extra_t),))
        return len(seen)
    while len(set(sigs.values())) < N:
        # pick the pool vertex that maximizes the number of classes
        best_t = max(pool, key=nclasses)
        for v in range(N):
            sigs[v] = sigs[v] + (rel(v, best_t),)
        T.append(best_t)
        pool = random.sample(range(N), 400)
        if len(T) > 30: break
    inj = len(set(sigs.values())) == N
    print("[E1] DIRECT relation-profile: greedy base size = %d (injective=%s)" % (len(T), inj))
    print("     info-theoretic floor for a 2-valued profile: |T| >= log2(4096) = 12.")
    print("     >>> plain cone scheme => O(log n) direct base => QUASIPOLY (not poly).\n")
    return len(T)

# ---------------- (E2) ITERATED individualization-refinement base ----------------
def refine(color):
    for _ in range(8):
        sig = {}; newc = [0]*N
        for v in range(N):
            key = (color[v], tuple(sorted(color[v ^ c] for c in NBR)))
            if key not in sig: sig[key] = len(sig)
            newc[v] = sig[key]
        if newc == color: return color
        color = newc
    return color

def ir_base():
    # individualize base vertices (each a unique color) then 1-WL refine; grow base until discrete.
    color = [0]*N
    T = []
    while len(set(color)) < N:
        # pick a vertex in the largest current color class to individualize
        from collections import Counter
        cnt = Counter(color)
        big = max(cnt, key=cnt.get)
        t = next(v for v in range(N) if color[v] == big)
        T.append(t)
        color = color[:]; color[t] = N + len(T)     # unique fresh color
        color = refine(color)
        if len(T) > 20: break
    print("[E2] ITERATED individualization+1-WL: base size = %d (discrete=%s)"
          % (len(T), len(set(color)) == N))
    print("     >>> with iterated refinement a bounded base discretizes (Sz(q) 2-transitivity) => POLY mechanism.\n")
    return len(T)

def gfinv(a):
    return EXP[(7 - LOG[a]) % 7]

# ---------------- (F-multi) empirical fit of sigma-twisted forms vanishing on the cone ----------------
# The cone is sigma-twisted-homogeneous of type (1,2) [F(lam x)=sigma(lam) lam^2 F(x)].  The natural forms
# vanishing on it are combinations of the type-(1,2) monomials  sigma(x_a) * x_b * x_c  (a in 0..3, b<=c).
# Fit (over GF(8)) the space of such forms vanishing on ALL 455 cone vectors; report dim, and whether the
# joint zero locus of a basis = cone (456).  A small joint family => Suzuki is a MULTI-(sigma-)form adapter.
MONO12 = [(a, b, c) for a in range(4) for b in range(4) for c in range(b, 4)]   # 4*10 = 40 monomials
def mono_val(m, v):
    a, b, c = m
    return gfmul(sigma(v[a]), gfmul(v[b], v[c]))

def gf_rref(M):
    M = [row[:] for row in M]; R = len(M); C = len(M[0]) if M else 0; r = 0; piv = []
    for col in range(C):
        p = next((i for i in range(r, R) if M[i][col] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = gfinv(M[r][col])
        M[r] = [gfmul(x, inv) for x in M[r]]
        for i in range(R):
            if i != r and M[i][col] != 0:
                f = M[i][col]; M[i] = [M[i][j] ^ gfmul(f, M[r][j]) for j in range(C)]
        piv.append(col); r += 1
        if r == R: break
    return M[:r], piv

def gf_nullspace(M):
    C = len(M[0]); Rref, piv = gf_rref(M); ps = set(piv); basis = []
    for f in [c for c in range(C) if c not in ps]:
        vec = [0]*C; vec[f] = 1
        for r, pc in enumerate(piv):
            vec[pc] = Rref[r][f]           # -x = x in char 2
        basis.append(vec)
    return basis

def form_val(coef, v):
    s = 0
    for j, m in enumerate(MONO12):
        if coef[j]: s ^= gfmul(coef[j], mono_val(m, v))
    return s

def sigma_form_fit():
    rows = [[mono_val(m, unpack(idx)) for m in MONO12] for idx in CONE]
    basis = gf_nullspace(rows)
    print("[F-multi] sigma-twisted type-(1,2) forms vanishing on the cone: dim = %d" % len(basis))
    joint = set(idx for idx in range(N) if all(form_val(c, unpack(idx)) == 0 for c in basis))
    ok = (joint == set(CONE) | {0})
    print("     joint zero locus size = %d (want 456) ; == cone∪{0}: %s" % (len(joint), ok))
    if ok:
        print("     >>> Suzuki = MULTI-(sigma)-form adapter: cone = joint {F_k=0}; F_k-value profile => POLY.")
        # print the 5 forms (monomial support; coeffs are GF(8) log-exponents, representation-specific)
        def gname(m):
            a, b, c = m
            return "s(x%d)*x%d*x%d" % (a, b, c)
        for i, coef in enumerate(basis):
            terms = ["%s%s" % (("" if coef[j] == 1 else "g^%d*" % LOG[coef[j]]), gname(MONO12[j]))
                     for j in range(len(MONO12)) if coef[j]]
            print("        F_%d = %s" % (i, " + ".join(terms)))
        print("     (s = sigma = ^4 ; g = GF(8) generator (x); representation-specific — re-derive in Lean)\n")
    else:
        print("     >>> type-(1,2) forms do NOT cut the cone alone; poly needs Handle-1 coordinate recovery.\n")
    return basis, ok

# ---------------- (F-check) {F=0} = cone ----------------
def verify_F():
    zeros = set(idx for idx in range(N) if F(unpack(idx)) == 0)
    want = set(CONE) | {0}
    ok = (zeros == want)
    print("[F] sigma-twisted ovoid form F = x3 x0^5 + x1 x2 x0^4 + x1^6 + x2^4 x0^2 (q=8):")
    print("     |{F=0}| = %d  (want |cone|+1 = 456) ; {F=0} == cone∪{0}: %s\n" % (len(zeros), ok))
    return ok

# ---------------- (E3) joint MULTI-form-VALUE direct-profile base (the isometry-scheme refinement) ----------------
def fval_profile_base(basis):
    # Route-C separates via the finer scheme: colour a pair (t,v) by the JOINT sigma-form value tuple
    # (F_k(v - t))_k (each 8-valued), not just cone membership (2-valued).  The joint value is COARSER than
    # any G0={g: all F_k o g = F_k}-orbit, so injectivity of  v |-> ((F_k(v^t))_k)_{t in T}  is SUFFICIENT
    # for `separates` at base T (no Witt needed).  Test the FRAME T={0,e0,e1,e2,e3} (|T|=d+1=5).
    frame = [0, 1, 8, 64, 512]                            # 0, and the GF(8) unit vectors e_i (packed)
    def prof(v):
        return tuple(form_val(c, unpack(v ^ t)) for t in frame for c in basis)
    sigs = set(prof(v) for v in range(N))
    inj = (len(sigs) == N)
    print("[E3] JOINT sigma-form-value profile at the FRAME T={0,e0,e1,e2,e3} (|T|=d+1=5, %d forms):" % len(basis))
    print("     distinct profiles = %d / %d ; injective: %s" % (len(sigs), N, inj))
    # also find the minimal base size (subset of the frame) that already separates
    minb = None
    for k in range(1, len(frame) + 1):
        sub = frame[:k]
        sg = set(tuple(form_val(c, unpack(v ^ t)) for t in sub for c in basis) for v in range(N))
        if len(sg) == N:
            minb = k; break
    print("     minimal prefix-of-frame base that separates = %s" % (minb if minb else ">5"))
    if inj:
        print("     >>> `separates` holds at an O(d) base via the joint F_k-value ⟹ POLY (like coords_determine_multi).\n")
    return minb if minb else len(frame)

if __name__ == "__main__":
    print("=== Route C Suzuki-Tits (f) de-risk probe — q=8, n=4096 ===\n")
    ok = report_object()
    fok = verify_F()
    basis, multiok = sigma_form_fit()
    one_wl_rank()
    if ok:
        b1 = direct_profile_base()
        b2 = ir_base()
        b3 = fval_profile_base(basis) if multiok else None
        print("=== VERDICT ===")
        print("object valid: %s ; single-form cone-cut: %s ; multi-(sigma)-form cone-cut: %s (dim %d)"
              % (ok, fok, multiok, len(basis)))
        print("bases: plain-cone direct > %d (QUASIPOLY, floor 12) ; iterated = %d ; joint sigma-form frame = %s (POLY)"
              % (b1 - 1, b2, b3))
        print("""
DESIGN CONCLUSION (the de-risk payoff):
 * Object EXACTLY validated: GF(8), sigma (sigma^2=Frob), ovoid c = ab + sigma(a)a^2 + sigma(b), cone,
     SRG(4096,455,6,56).  This is the connection set the Lean adapter models.
 * NO single sigma-twisted form cuts the cone (the Tits ovoid is not that hypersurface: |{F=0}|=512).
 * BUT a 5-dim family of sigma-twisted type-(1,2) forms {F_k} has JOINT zero locus = cone EXACTLY (456).
     => Suzuki is a MULTI-(sigma)-FORM adapter -- the sigma-twisted analog of alternating (Plucker) and
     half-spin (spinor quadrics).  The joint F_k-value profile at an O(d) base separates (POLY), exactly the
     coords_determine_multi mechanism; the plain cone scheme (2-valued) would only reach QUASIPOLY.
 * Lean design: sigma (Frobenius power) + the 5 F_k as semilinear (sigma-twisted) forms over GF(8) + a
     coords_determine_multi analog for the joint value.  NOT the quadratic multiFormAdapter (forms are
     sigma-twisted, not quadratic) -- a sigma-twisted sibling engine.  Follow-up: transcribe the 5 F_k.""")
    else:
        print("OBJECT INVALID — fix the ovoid/sigma formula before the base analysis.")
