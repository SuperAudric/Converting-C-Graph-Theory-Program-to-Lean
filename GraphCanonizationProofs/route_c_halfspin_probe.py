#!/usr/bin/env python3
# ROUTE C — HALF-SPIN (D5) SPINOR-QUADRIC DE-RISKING PROBE v2 (2026-07-03).
#
# v1 lesson: the naive moment map (w ^ Gamma^a w)_top gave the WRONG forms (they don't vanish on pure
# spinors). v2 uses the BULLETPROOF empirical route: generate genuine pure spinors by the char-free big-cell
# formula, then FIT the degree-2 vanishing ideal. This discovers the correct 10 equations and validates them.
#
# Model. Half-spin S+ = Lambda^even(F_q^5), dim 16.  Coords indexed by even subsets of {1..5}:
#   e (empty), 10 pairs {ij}, 5 quadruples {ijkl}.
# Big-cell pure spinors (Spin-orbit of the vacuum e_empty, the isotropics transverse to K^5) are, char-free,
#   w(b)_empty = 1,   w(b)_{ij} = b_ij,   w(b)_{ijkl} = Pf(b|_{ijkl}) = b_ij b_kl - b_ik b_jl + b_il b_jk
# for an antisymmetric b (10 free params b_ij).  [This is exp(sum b_ij a_i a_j) . e_empty = prod (1+b_ij a_i a_j) e_0;
#  the Lambda^4 coeff is the 4x4 Pfaffian, integral -> valid over F_2 too.]  The big cell is Zariski-dense in the
# spinor variety S_5, so quadrics vanishing on it = quadrics vanishing on S_5.
#
# Validations:
#   (A) dim of the degree-2 vanishing space = 10 over F_q (q=3,5,7,11)  -> "cut by exactly 10 quadrics"
#   (B) a fresh holdout of pure spinors satisfies all fitted quadrics
#   (C) joint polar radical of the 10 forms is TRIVIAL  (= Lean `hjoint`)
#   (D) EXACT point count over F_2 of the common zero locus = 1 + (q-1) prod_{i=1..4}(q^i+1) = 2296
#   (E) randomized count fraction over F_3 matches target/3^16
#   (F) print a clean SO(10)-structured basis of the 10 forms for the Lean port.

from itertools import combinations, product

N = 5
EVEN = [m for m in range(1 << N) if bin(m).count("1") % 2 == 0]   # 16 even subsets (deg 0,2,4)
IDX = {m: k for k, m in enumerate(EVEN)}
PAIRS = [m for m in EVEN if bin(m).count("1") == 2]               # 10
QUADS = [m for m in EVEN if bin(m).count("1") == 4]               # 5
EMPTY = 0

def bit(i, m): return (m >> i) & 1
def elems(m): return [i for i in range(N) if bit(i, m)]

def name(m):
    s = sorted(i + 1 for i in elems(m))
    return "".join(map(str, s)) if s else "e"

# ---- big-cell pure spinor from antisymmetric b (dict {i<j}->val) ----
def pure_spinor(b, q):
    w = [0] * 16
    w[IDX[EMPTY]] = 1 % q
    for m in PAIRS:
        i, j = elems(m)
        w[IDX[m]] = b[(i, j)] % q
    for m in QUADS:
        i, j, k, l = elems(m)                                     # i<j<k<l
        pf = (b[(i, j)] * b[(k, l)] - b[(i, k)] * b[(j, l)] + b[(i, l)] * b[(j, k)]) % q
        w[IDX[m]] = pf
    return w

def rand_b(q, rng):
    return {(i, j): rng() % q for i, j in combinations(range(N), 2)}

# ---- linear algebra mod q (q prime) ----
def rref(M, q):
    M = [row[:] for row in M]; R = len(M); C = len(M[0]) if M else 0; r = 0; piv = []
    for c in range(C):
        p = next((i for i in range(r, R) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = pow(M[r][c], q - 2, q)
        M[r] = [(x * inv) % q for x in M[r]]
        for i in range(R):
            if i != r and M[i][c] % q:
                f = M[i][c]; M[i] = [(M[i][j] - f * M[r][j]) % q for j in range(C)]
        piv.append(c); r += 1
        if r == R: break
    return M[:r], piv

def null_space(M, q):
    # basis of {c : M c = 0}, columns = 136 monomials
    C = len(M[0]); Rref, piv = rref(M, q); pivset = set(piv); free = [c for c in range(C) if c not in pivset]
    basis = []
    for f in free:
        v = [0] * C; v[f] = 1
        for r, pc in enumerate(piv):
            v[pc] = (-Rref[r][f]) % q
        basis.append(v)
    return basis

MONO = [(k, l) for k in range(16) for l in range(k, 16)]          # 136 monomials x_k x_l
def design_row(x, q):
    return [(x[k] * x[l]) % q for (k, l) in MONO]

def fit_quadrics(q, nsamp=400, seed=12345):
    st = [seed]
    def rng():
        st[0] = (st[0] * 1103515245 + 12345) & 0x7fffffff; return st[0]
    rows = [design_row(pure_spinor(rand_b(q, rng), q), q) for _ in range(nsamp)]
    return null_space(rows, q)   # each basis vec = coeff over the 136 monomials

def quad_eval(coef, x, q):
    return sum(coef[t] * x[MONO[t][0]] * x[MONO[t][1]] for t in range(136)) % q

# ---- polar radical of a set of quadric-coefficient vectors ----
def polar_rows(coef, q):
    # build 16x16 polar matrix then return its rows
    Q = {MONO[t]: coef[t] % q for t in range(136) if coef[t] % q}
    def val(x):
        return sum(c * x[k] * x[l] for (k, l), c in Q.items()) % q
    M = []
    for k in range(16):
        row = []
        ek = [0]*16; ek[k] = 1
        for l in range(16):
            el = [0]*16; el[l] = 1
            ekl = [0]*16; ekl[k] += 1; ekl[l] += 1
            row.append((val(ekl) - val(ek) - val(el)) % q)
        M.append(row)
    return M

def joint_radical_dim(basis, q):
    rows = []
    for coef in basis:
        rows.extend(polar_rows(coef, q))
    Rref, piv = rref(rows, q)
    return 16 - len(piv)

# ---- pretty-print a quadric coefficient vector ----
def show(coef, q):
    terms = []
    for t in range(136):
        c = coef[t] % q
        if not c: continue
        cc = c if c <= q // 2 else c - q
        k, l = MONO[t]
        mono = "x%s^2" % name(EVEN[k]) if k == l else "x%s*x%s" % (name(EVEN[k]), name(EVEN[l]))
        terms.append("%+d %s" % (cc, mono))
    return " ".join(terms) if terms else "0"

def target(q):
    p = 1
    for i in range(1, 5): p *= (q ** i + 1)
    return 1 + (q - 1) * p

if __name__ == "__main__":
    print("=== Route C half-spin (D5) spinor-quadric de-risking v2 (empirical fit) ===\n")

    # (A) dimension of the degree-2 vanishing space
    print("[A] dim of degree-2 vanishing ideal (want 10):")
    for q in (3, 5, 7, 11):
        b = fit_quadrics(q)
        print("    q=%-2d : dim = %d" % (q, len(b)))
    print()

    # (B) holdout + (C) polar radical, over q=7
    q = 7
    basis = fit_quadrics(q)
    st = [999]
    def rng():
        st[0] = (st[0]*1103515245+12345) & 0x7fffffff; return st[0]
    ok = all(quad_eval(c, pure_spinor(rand_b(q, rng), q), q) == 0 for c in basis for _ in range(1))
    holdout = all(all(quad_eval(c, pure_spinor(rand_b(q, rng), q), q) == 0 for c in basis) for _ in range(200))
    print("[B] q=7: all %d fitted quadrics vanish on 200 fresh pure spinors: %s" % (len(basis), holdout))
    print("[C] q=7: joint polar radical dim = %d  (want 0 = hjoint)\n" % joint_radical_dim(basis, q))

    # (D) EXACT count over F_2 of the EXPLICIT integer forms (avoids the char-2 function-fitting artifact:
    #     over F_2 distinct polynomials share a function, so re-fitting is degenerate; instead reduce the
    #     integer forms discovered over q=7 -- coeffs in {-1,0,1} -- mod 2 and brute count).
    def lift_int(coef, q):
        return [(c % q) - q if (c % q) > q // 2 else (c % q) for c in coef]
    forms_int = [lift_int(c, 7) for c in basis]           # basis = q=7 fit, coeffs +-1
    def eval_mod(coefI, x, q):
        return sum(coefI[t] * x[MONO[t][0]] * x[MONO[t][1]] for t in range(136)) % q
    cnt = 0
    for x in product(range(2), repeat=16):
        xl = list(x)
        if all(eval_mod(c, xl, 2) == 0 for c in forms_int):
            cnt += 1
    print("[D] q=2: EXACT |common zero locus of the 10 explicit forms| = %d ; target = %d ; MATCH=%s\n"
          % (cnt, target(2), cnt == target(2)))

    # (E) randomized fraction over F_3
    q = 3; basis3 = fit_quadrics(q); st = [7]
    def rng3():
        st[0] = (st[0]*1103515245+12345) & 0x7fffffff; return st[0]
    T = 300000; hit = 0
    for _ in range(T):
        x = [rng3() % q for _ in range(16)]
        if all(quad_eval(c, x, q) == 0 for c in basis3): hit += 1
    print("[E] q=3: sampled fraction = %.5f over %d ; target fraction = %.5f (=%d/3^16)"
          % (hit / T, T, target(q) / 3**16, target(q)))
    print()

    # (F) print a clean basis of the 10 forms (fitted over q=7, reduced representatives)
    print("[F] a basis of the 10 quadrics (q=7 fit, small-residue coeffs):")
    for a, c in enumerate(basis):
        print("    Q_%-2d = %s" % (a, show(c, 7)))
