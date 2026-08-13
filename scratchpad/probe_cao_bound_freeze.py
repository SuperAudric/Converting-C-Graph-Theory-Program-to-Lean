"""probe_cao_bound_freeze.py — is FREEZING the frame vertices the level-uniform rule?

section 6d measured the single-copy model M(c) reproducing the ensemble exactly at L=4, 2-WL, whether
or not the frame was frozen.  But at 1-WL the UNFROZEN private-frame model provably disagrees with the
ensemble (section 6a: 538 cells / 6 mixed vs 292 / 100), so section 6d.4 recorded "the collapse is not
level-uniform" as the open worry.

The reader's argument (2026-08-13) predicts the repair: a frame vertex may split into its two
individualization orbits and then NEVER refine further, because for every within-copy path that would
distinguish two frame vertices there is every alternative across the other copies, which balances.
So the faithful model at EVERY level should be

    M_frozen(c) = c's payload (a clique) + the 2d frame vertices, frame vertex colours FROZEN at t

and the 1-WL disagreement should be an artefact of not freezing, not a level-dependence.

PREDICTION, if the rule is right:
    frozen   1-WL  ->  292 cells, identical to the ensemble  (= (degree sequence, own degree))
    unfrozen 1-WL  ->  538 cells, the section 6a control
⚠ lockstep rounds + a shared intern table, or colours from different rounds get compared (8(e)).
"""

from itertools import combinations

L = 6
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k

ROUNDS = L + 2 * NS + 1

NBR = [[] for _ in range(L + 2 * NS)]
for a in range(L):
    for b in range(L):
        if a != b:
            NBR[a].append(b)                       # clique payload
for k in range(NS):
    NBR[L + 2 * k].append(L + 2 * k + 1)           # the connected pair
    NBR[L + 2 * k + 1].append(L + 2 * k)


def nbrs(c):
    """payload -> the frame vertex of its own type, per slot"""
    out = [list(x) for x in NBR]
    for k, (i, j) in enumerate(PAIRS):
        f = L + 2 * k + ((c >> k) & 1)
        out[i].append(f)
        out[j].append(f)
        out[f] += [i, j]
    return out


def wl1_single(c, intern, freeze):
    adj = nbrs(c)
    col = [0] * L + [1 + (v % 2) for v in range(2 * NS)]
    for _ in range(ROUNDS):
        new = []
        for v in range(L + 2 * NS):
            if freeze and v >= L:
                new.append(intern.setdefault(('frozen', col[v]), len(intern)))
                continue
            cnt = {}
            for z in adj[v]:
                cnt[col[z]] = cnt.get(col[z], 0) + 1
            new.append(intern.setdefault((col[v], tuple(sorted(cnt.items()))), len(intern)))
        col = new
    return col[:L]


def degs(c):
    d = [0] * L
    for k, (i, j) in enumerate(PAIRS):
        if (c >> k) & 1:
            d[i] += 1
            d[j] += 1
    return d


def same(a, b, keys):
    m1, m2 = {}, {}
    for k in keys:
        if m1.setdefault(a[k], b[k]) != b[k] or m2.setdefault(b[k], a[k]) != a[k]:
            return False
    return True


if __name__ == '__main__':
    keys = [(c, i) for c in range(NC) for i in range(L)]
    ens = {}
    for c in range(NC):
        d = degs(c)
        ds = tuple(sorted(d))
        for i in range(L):
            ens[(c, i)] = (ds, d[i])
    print(f'L={L}: the ensemble\'s 1-WL payload partition (section 6a, verified elementwise at '
          f'n=229406): {len(set(ens.values()))} cells')

    for freeze in (True, False):
        intern, got = {}, {}
        for c in range(NC):
            cc = wl1_single(c, intern, freeze)
            for i in range(L):
                got[(c, i)] = cc[i]
        n = len(set(got.values()))
        ok = same(ens, got, keys)
        tag = 'FROZEN  ' if freeze else 'unfrozen'
        print(f'  single-copy model, frame {tag}: {n:4d} cells   identical to the ensemble: {ok}')
