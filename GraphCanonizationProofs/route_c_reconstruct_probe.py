#!/usr/bin/env python3
"""
ROUTE C DE-RISK — quadric reconstruction from the isotropic cone.

Route C recovers Q (up to scalar) from the graph's connection set = the punctured
isotropic cone  C = {x != 0 : Q(x) = 0}.  Its SOLE correctness hypothesis is:

    the space of homogeneous degree-2 forms vanishing on C is 1-dimensional (= <Q>).

dim = 1  => Q reconstructible up to scalar by ONE linear solve (poly, no WL, no
            orbits) => Route C's front reduction is SOUND at that (eps,d,q).
dim > 1  => the cone under-determines Q (a small-q exception) => Route C needs a
            fix there (extra relations / different base).

Odd q only (the affine-polar / Route C target).  char 2 is a separate track:
over F_{2^k} squaring collapses degree (x^2 = Frobenius), so the degree-2 vanishing
space is structurally different -- handled by the Arf/char-2 substrate, not here.
"""
import itertools
from model_gap import make_Q


def rref_rank(rows, q):
    """Rank over F_q by Gaussian elimination."""
    rows = [r[:] for r in rows]
    if not rows:
        return 0
    ncols = len(rows[0])
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % q != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c] % q, q - 2, q)
        rows[r] = [(x * inv) % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % q != 0:
                f = rows[i][c]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def run(d, q, eps):
    Z = tuple([0] * d)
    V = itertools.product(range(q), repeat=d)
    Q = make_Q(d, q, eps)
    cone = [x for x in V if x != Z and Q(x) % q == 0]
    monos = [(i, j) for i in range(d) for j in range(i, d)]   # x_i x_j, i<=j
    M = len(monos)
    rows = [[(x[i] * x[j]) % q for (i, j) in monos] for x in cone]
    rank = rref_rank(rows, q)
    vanish = M - rank
    nm = f"VO^{'+' if eps > 0 else '-'}_{d}({q})"
    verdict = ("OK  (=1: Q recoverable up to scalar, 1 linear solve)" if vanish == 1
               else "*** AMBIGUOUS (>1): cone under-determines Q ***" if vanish > 1
               else "*** ZERO: no form vanishes?! ***")
    print(f"{nm:14s} n={q**d:6d} |cone|={len(cone):6d} #monos={M:3d} rank={rank:3d} "
          f"vanishDim={vanish}  {verdict}")


if __name__ == "__main__":
    print("=== Route C reconstruction check: dim of degree-2 forms vanishing on the isotropic cone ===")
    print("    (target vanishDim = 1  <=>  Q reconstructible up to scalar, no WL/orbits)\n")
    for eps in (-1, 1):
        for q in (3, 5, 7, 11):
            run(4, q, eps)
        print()
    for eps in (-1, 1):
        for q in (3, 5):
            run(6, q, eps)
    print()
    run(8, 3, -1)
    run(8, 3, +1)
