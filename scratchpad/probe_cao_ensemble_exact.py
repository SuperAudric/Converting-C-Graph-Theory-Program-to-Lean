"""probe_cao_ensemble_exact.py — is the rung-1 ensemble's 1-WL EXACTLY the degree sequence?

probe_cao_ensemble_audit.py predicted section 6's three numbers (292 cells / 544 orbits / 100 mixed)
from the one-line formula  colour(c,i) = (degree sequence of G_c, deg(i)).  Three numbers agreeing is
strong but is not equality.  This re-runs the real 229406-vertex ensemble and compares the two
partitions ELEMENTWISE, both ways.
"""

from probe_cao_ensemble import build, wl1, kind, L, NC, NS, PAIRS, M0, F0, N

indptr, indices = build()
start = [kind(v) for v in range(N)]
start[M0 + 0] = 3
col, rounds = wl1(indptr, indices, start)
pay = col[:L * NC]
print(f'1-WL stabilized in {rounds} rounds, {len(set(pay))} payload cells', flush=True)


def degs(c):
    d = [0] * L
    for k, (i, j) in enumerate(PAIRS):
        if (c >> k) & 1:
            d[i] += 1
            d[j] += 1
    return d


pred = []
for c in range(NC):
    d = degs(c)
    ds = tuple(sorted(d))
    for i in range(L):
        pred.append((ds, d[i]))
print(f'prediction (degree sequence, own degree): {len(set(pred))} classes', flush=True)

a2b, b2a, ok = {}, {}, True
for v in range(L * NC):
    x, y = pay[v], pred[v]
    if a2b.setdefault(x, y) != y or b2a.setdefault(y, x) != x:
        ok = False
        break
print(f'==> the two partitions are IDENTICAL: {ok}')
