#!/usr/bin/env python3
"""Probe the fiber structure of `x -> polar Q w x` on the isotropic cone (2026-07-05).

For the hub-lemma counting: I need `exists isotropic a avoiding k hyperplanes w_i^perp`.
Via the scaling bijection x -> lam*x (preserves Qx=0, scales polar Q w x by lam), all
NONZERO fibers of (x |-> polar Q w x) on the cone are equinumerous (= N). Let f0 = tangent
fiber |{Qx=0, polar Q w x = 0}|. Then |cone| = f0 + (q-1)*N.

If  f0 <= N  for every nonzero w, then f0 <= |cone|/q, so union of k tangent fibers has
size <= k|cone|/q < |cone| when q > k  => an avoiding isotropic vector exists, NO character
sums needed. This probe checks f0 <= N (report worst-case f0 - N; must be <= 0), separately
for w anisotropic and w isotropic (both occur: w in {y, z, z-y}).
"""
import itertools

def nonsquare(q):
    sq = {(a*a) % q for a in range(q)}
    return next(n for n in range(1, q) if n not in sq)

def build(d, q, kind):
    coeffs = [1]*d if kind == '+' else [1]*(d-1) + [nonsquare(q)]
    def Q(x): return sum(c*xi*xi for c, xi in zip(coeffs, x)) % q
    def polar(x, y):
        return (Q(tuple((a+b) % q for a, b in zip(x, y))) - Q(x) - Q(y)) % q
    return Q, polar

def run(d, q, kind):
    Q, polar = build(d, q, kind)
    V = list(itertools.product(range(q), repeat=d))
    cone = [x for x in V if Q(x) == 0]
    ncone = len(cone)
    worst_aniso = None   # max (f0 - N) over anisotropic w
    worst_iso = None     # over isotropic w != 0
    for w in V:
        if not any(w): continue
        # fiber sizes of a |-> polar Q w a on the cone
        counts = {}
        for a in cone:
            c = polar(w, a)
            counts[c] = counts.get(c, 0) + 1
        f0 = counts.get(0, 0)
        nz = [counts.get(c, 0) for c in range(1, q)]
        if all(v == 0 for v in nz):
            # w orthogonal to whole cone => w in radical => Q degenerate; skip (nondeg => none)
            N = 0
        else:
            N = min(v for v in nz)  # worst-case nonzero fiber (they should all be equal)
            Nmax = max(nz)
            assert N == Nmax, f"nonzero fibers unequal! w={w} nz={nz}"  # scaling bijection check
        diff = f0 - N
        if Q(w) != 0:
            worst_aniso = diff if worst_aniso is None else max(worst_aniso, diff)
        else:
            worst_iso = diff if worst_iso is None else max(worst_iso, diff)
    return ncone, worst_aniso, worst_iso

if __name__ == '__main__':
    print("  (worst = max(f0 - N); need <= 0 for the clean route)")
    for d, q, kind in [(4,3,'+'),(4,3,'-'),(4,5,'-'),(4,7,'-'),(5,3,'-'),(6,3,'-')]:
        ncone, wa, wi = run(d, q, kind)
        ok = "OK" if (wa is not None and wa <= 0 and (wi is None or wi <= 0)) else "*** f0>N ***"
        print(f"d={d} q={q} {kind}  cone={ncone:5d}  worst(w aniso)={wa}  worst(w iso)={wi}  {ok}")
