"""probe_cao_gauge2_diag.py — is section 3.2c's over-separation CAO-RELEVANT, or only off-diagonal?

probe_cao_gauge2_ablate.py reported the two-copy model strictly finer than the full ensemble on
1936/2016 copy pairs.  That was measured on the partition of payload PAIRS.  CAO propagation is a
statement about the VERTEX partition (2-WL's diagonal cells), and the section 4 / section 5.1 kills
are stated as a SEPARATION VERDICT (do the two copies get distinguished at all).  A pair colouring
can be strictly finer while both of those agree -- e.g. it distinguishes adjacent from non-adjacent
pairs INSIDE one orbit, which says nothing about CAO.

So re-measure the same objects at the two levels that actually carry the claims:
   diagonal   : the partition of payload VERTICES induced by col(x,x)
   verdict    : does the model call the two copies distinct, and does the ensemble?
⚠ At L = 4 every pair of non-isomorphic copies is separated by both, so the VERDICT column cannot
discriminate -- that limitation is the point of reporting it rather than assuming it away.
"""

from itertools import combinations
from probe_cao_gauge2_ablate import build, wl2, L, NS, NC, SLOT


def diag_and_profile(pc, copies):
    """pc maps (x,y) -> colour over payload vertices.  Returns (diagonal partition, per-copy
    multiset profile of pair colours)."""
    diag, prof = {}, {}
    for c in copies:
        prof[c] = {}
    for c in copies:
        for i in range(L):
            diag[(c, i)] = pc[(('p', c, i), ('p', c, i))]
            for j in range(L):
                v = pc[(('p', c, i), ('p', c, j))]
                prof[c][v] = prof[c].get(v, 0) + 1
    return diag, prof


def same_part(a, b, keys):
    m1, m2 = {}, {}
    for k in keys:
        if m1.setdefault(a[k], b[k]) != b[k] or m2.setdefault(b[k], a[k]) != a[k]:
            return False
    return True


if __name__ == '__main__':
    allc = list(range(NC))
    print(f'L={L}, {NC} copies', flush=True)
    full = wl2(*build(allc, True), 'full')

    import io
    import contextlib
    stats = {'diag differs': 0, 'diag same': 0,
             'verdict differs': 0, 'verdict same': 0}
    for (c, cp) in combinations(allc, 2):
        with contextlib.redirect_stdout(io.StringIO()):
            two = wl2(*build([c, cp], False), '')
        dF, pF = diag_and_profile(full, [c, cp])
        dT, pT = diag_and_profile(two, [c, cp])
        keys = [(d, i) for d in (c, cp) for i in range(L)]
        stats['diag same' if same_part(dF, dT, keys) else 'diag differs'] += 1
        vF = pF[c] != pF[cp]
        vT = pT[c] != pT[cp]
        stats['verdict same' if vF == vT else 'verdict differs'] += 1

    tot = NC * (NC - 1) // 2
    print(f'\nover {tot} copy pairs, TWO-COPY model vs FULL ensemble:')
    for k in ('diag same', 'diag differs', 'verdict same', 'verdict differs'):
        print(f'  {k:16s} {stats[k]:5d}')
    print('\n⚠ read with section 3.2c: the pair-colour partition differed on 1936/2016.')
