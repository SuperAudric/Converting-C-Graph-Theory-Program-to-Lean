#!/usr/bin/env python3
# ROUTE C — SUZUKI `SuzukiFormsDetermine` DISCHARGE PROBE (2026-07-04).
#
# Goal: (1) VERIFY the citation `SuzukiFormsDetermine` is correct AS FORMED in Lean, by transcribing the EXACT
#           Lean forms SF0..SF4 (not the probe's fitted nullspace basis) and testing the EXACT statement:
#             Phi(v) := ( SFv(v-t)_k )_{t in frame {0,e0,e1,e2,e3}, k in 0..4}   is INJECTIVE over K^4.
#       (2) test over TWO Suzuki fields GF(8) (q=2^3) and GF(32) (q=2^5) — so it is not a q=8 coincidence.
#       (3) investigate a DIRECT algebraic discharge: is v recoverable from Phi(v) by a low-degree/linear system
#           (discrete derivatives D_j = F(v)+F(v+e_j) in char 2)?  If yes -> a general Lean proof is plausible.
#       (4) cross-check the Lean forms span the same 5-dim sigma-form space the fit found (basis-independence of inj).
#
# Lean forms (char 2, sigma a ring endo with sigma(sigma x)=x^2):
#   SF0 = s(x0)*x0*x3 + s(x0)*x1*x2 + s(x1)*x1^2 + s(x2)*x0^2
#   SF1 = s(x0)*x2^2 + s(x1)*x0*x3 + s(x1)*x1*x2 + s(x3)*x0^2
#   SF2 = s(x0)*x2*x3 + s(x1)*x1*x3 + s(x2)*x0*x2 + s(x3)*x0*x1
#   SF3 = s(x0)*x3^2 + s(x2)*x0*x3 + s(x2)*x1*x2 + s(x3)*x1^2
#   SF4 = s(x1)*x3^2 + s(x2)*x2^2 + s(x3)*x0*x3 + s(x3)*x1*x2
# (s = sigma).  ovoidC(a,b) = a*b + s(a)*a^2 + s(b).

from itertools import product

# ---------- GF(2^n) arithmetic (bit-vector polynomials mod an irreducible) ----------
class GF:
    def __init__(self, n, mod, e):
        self.n = n; self.q = 1 << n; self.mod = mod
        # Tits endomorphism exponent: q = 2^(2e+1), sigma(x) = x^(2^(e+1))
        self.sigexp = 1 << (e + 1)
    def mul(self, a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & self.q: a ^= self.mod
        return r
    def powr(self, a, k):
        r = 1
        while k:
            if k & 1: r = self.mul(r, a)
            a = self.mul(a, a); k >>= 1
        return r
    def sigma(self, a):  # Tits endo
        return self.powr(a, self.sigexp)
    def frob(self, a):
        return self.mul(a, a)

# GF(8): x^3+x+1 = 0b1011 ; q=2^3 -> e=1 -> sigma(x)=x^(2^2)=x^4
GF8  = GF(3, 0b1011, 1)
# GF(32): x^5+x^2+1 = 0b100101 ; q=2^5 -> e=2 -> sigma(x)=x^(2^3)=x^8
GF32 = GF(5, 0b100101, 2)

def check_sigma(F):
    # sigma(sigma(x)) == x^2 for all x
    return all(F.sigma(F.sigma(x)) == F.frob(x) for x in range(F.q))

# ---------- the EXACT Lean forms ----------
def SFforms(F, x0, x1, x2, x3):
    m = F.mul; s = F.sigma; sq = lambda a: F.mul(a, a)
    SF0 = m(m(s(x0), x0), x3) ^ m(m(s(x0), x1), x2) ^ m(s(x1), sq(x1)) ^ m(s(x2), sq(x0))
    SF1 = m(s(x0), sq(x2))    ^ m(m(s(x1), x0), x3) ^ m(m(s(x1), x1), x2) ^ m(s(x3), sq(x0))
    SF2 = m(m(s(x0), x2), x3) ^ m(m(s(x1), x1), x3) ^ m(m(s(x2), x0), x2) ^ m(m(s(x3), x0), x1)
    SF3 = m(s(x0), sq(x3))    ^ m(m(s(x2), x0), x3) ^ m(m(s(x2), x1), x2) ^ m(s(x3), sq(x1))
    SF4 = m(s(x1), sq(x3))    ^ m(s(x2), sq(x2))    ^ m(m(s(x3), x0), x3) ^ m(m(s(x3), x1), x2)
    return (SF0, SF1, SF2, SF3, SF4)

def ovoidC(F, a, b):
    return F.mul(a, b) ^ F.mul(F.sigma(a), F.mul(a, a)) ^ F.sigma(b)

# ---------- sanity: forms cut the cone (vanish on ovoid + infinity, sigma-homogeneous) ----------
def check_cut_cone(F):
    okov = all(all(v == 0 for v in SFforms(F, 1, a, b, ovoidC(F, a, b)))
               for a in range(F.q) for b in range(F.q))
    okinf = all(v == 0 for v in SFforms(F, 0, 0, 0, 1))
    # homogeneity SF_k(l*x) = sigma(l)*l^2*SF_k(x)
    import random
    homok = True
    for _ in range(2000):
        l = random.randrange(F.q); x = [random.randrange(F.q) for _ in range(4)]
        lhs = SFforms(F, F.mul(l, x[0]), F.mul(l, x[1]), F.mul(l, x[2]), F.mul(l, x[3]))
        scale = F.mul(F.sigma(l), F.mul(l, l))
        rhs = tuple(F.mul(scale, v) for v in SFforms(F, *x))
        if lhs != rhs: homok = False; break
    # exact cone count: |{x != 0 : all SF_k(x)=0}|  should be (q^2+1)(q-1)
    conecnt = sum(1 for x in product(range(F.q), repeat=4)
                  if x != (0,0,0,0) and all(v == 0 for v in SFforms(F, *x)))
    target = (F.q*F.q + 1) * (F.q - 1)
    return okov, okinf, homok, conecnt, target

# ---------- the EXACT `SuzukiFormsDetermine` statement: Phi injective over the frame ----------
def phi(F, v):
    # frame t in {0, e0, e1, e2, e3}; in char 2, v - t = v XOR t coordinatewise
    frame = [(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    out = []
    for t in frame:
        w = tuple(v[i] ^ t[i] for i in range(4))
        out.extend(SFforms(F, *w))
    return tuple(out)

def check_determine(F):
    seen = {}
    for v in product(range(F.q), repeat=4):
        p = phi(F, v)
        if p in seen:
            return False, (seen[p], v)   # collision => statement FALSE
        seen[p] = v
    return True, None

# ---------- (3) minimal frame prefix + which base points are needed ----------
def min_frame_prefix(F):
    frame = [(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    for k in range(1, 6):
        sub = frame[:k]
        seen = set(); inj = True
        for v in product(range(F.q), repeat=4):
            p = tuple(y for t in sub for y in SFforms(F, *[v[i]^t[i] for i in range(4)]))
            if p in seen: inj = False; break
            seen.add(p)
        if inj: return k
    return ">5"

if __name__ == "__main__":
    for name, F in (("GF(8) [q=2^3, sigma=x^4]", GF8), ("GF(32) [q=2^5, sigma=x^8]", GF32)):
        print("=== %s ===" % name)
        print("  sigma(sigma x)==x^2 for all x : %s" % check_sigma(F))
        okov, okinf, homok, cc, tgt = check_cut_cone(F)
        print("  forms vanish on affine ovoid : %s" % okov)
        print("  forms vanish at infinity     : %s" % okinf)
        print("  sigma-homogeneous (2k rand)  : %s" % homok)
        print("  |cone| = %d ; target (q^2+1)(q-1) = %d ; MATCH=%s" % (cc, tgt, cc == tgt))
        det, coll = check_determine(F)
        print("  >>> SuzukiFormsDetermine (Phi injective over K^4): %s" % det)
        if not det:
            print("      COLLISION: v=%s  v'=%s  (statement FALSE as formed)" % coll)
        else:
            print("      minimal frame-prefix that already separates: |base| = %s" % min_frame_prefix(F))
        print()
