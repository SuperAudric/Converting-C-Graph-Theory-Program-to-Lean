"""probe_cao_crosscopy.py — does the CROSS-COPY pair colour carry slot-ALIGNMENT data?

The reader's uniformity argument (2026-08-13) closes the cross-copy counting: for a pebbled pair, the
copies other than the <= k pebbled ones contribute [global count] - [copy c] - [copy c'], the global
count is a constant of E(L), and each correction is fixed by that vertex's own M-colour (in a STABLE
colouring col_M(i,i) already determines the multiset {(col_M(i,m), col_M(m,m))}, i.e. the copy's whole
colour profile).  "Uniform minus a uniform selection of <= k is uniform", for any k.

What that argument does NOT reach is z ranging over the FRAME.  The frame is not a copy: it is shared
and finite, so aggregating a cross-copy pair (p(c,i), p(c',l)) over frame vertices sums, over slots k,
the JOINT pair (M(c)-colour of (i, f(k,t)), M(c')-colour of (f(k,t), l)) -- which correlates the two
copies through the slot index.  For the DIAGONAL this is harmless (both ends sit in copy c, so it is
within-M data).  It bites only if cross-copy PAIR colours genuinely carry that alignment.

THE TEST, on real data at L = 4.  Is the ensemble's cross-copy pair colour a function of the PAIR of
M-diagonal-colours alone?
    YES -> cross-copy colours carry no alignment, the sum over all c' is trivially constant in c, and
           the reader's argument closes the induction outright.
    NO  -> alignment is real; the residual obligation is exactly "the joint distribution of
           (M-col(c',l), alignment) over all (c',l) is determined by M-col(c,i)".
Also reported: whether adding delta = c ^ c' as an explicit coordinate suffices, which localizes the
gap if the answer is NO.
"""

from itertools import combinations
from probe_cao_gauge2_ablate import build, wl2_full, L, NS, NC
from probe_cao_bound_single import single_copy

if __name__ == '__main__':
    allc = list(range(NC))
    ecol, everts, eidx = wl2_full(*build(allc, True), 'ensemble')
    n = len(everts)

    intern, mdiag = {}, {}
    for c in allc:
        pc, _ = single_copy(c, intern, True)
        for i in range(L):
            mdiag[(c, i)] = pc[(i, i)]
    print(f'M-diagonal colours: {len(set(mdiag.values()))}', flush=True)

    # hypothesis A: cross-copy colour is a function of (M-col(c,i), M-col(c',l))
    # hypothesis B: ... of (M-col(c,i), M-col(c',l), delta = c ^ c')  -- delta as a raw label
    mapA, mapB = {}, {}
    okA = okB = True
    ncross = 0
    for c in allc:
        for cp in allc:
            if c == cp:
                continue
            for i in range(L):
                for l in range(L):
                    v = ecol[eidx[('p', c, i)] * n + eidx[('p', cp, l)]]
                    ncross += 1
                    kA = (mdiag[(c, i)], mdiag[(cp, l)])
                    if mapA.setdefault(kA, v) != v:
                        okA = False
                    kB = kA + (c ^ cp,)
                    if mapB.setdefault(kB, v) != v:
                        okB = False
    ncol = len({ecol[eidx[('p', c, i)] * n + eidx[('p', cp, l)]]
                for c in allc for cp in allc if c != cp for i in range(L) for l in range(L)})
    print(f'cross-copy pair colours in the ensemble: {ncol}  (over {ncross} ordered cross pairs)')
    print(f'  A: determined by the PAIR of M-diagonal colours alone : {okA}'
          f'   ({len(mapA)} classes)')
    print(f'  B: ... plus delta = c ^ c\'                            : {okB}'
          f'   ({len(mapB)} classes)')

    # and the thing that actually has to be constant: the cross-copy contribution to the DIAGONAL
    contrib = {}
    consistent = True
    for c in allc:
        for i in range(L):
            ms = {}
            for cp in allc:
                if cp == c:
                    continue
                for l in range(L):
                    a = ecol[eidx[('p', c, i)] * n + eidx[('p', cp, l)]]
                    b = ecol[eidx[('p', cp, l)] * n + eidx[('p', c, i)]]
                    ms[(a, b)] = ms.get((a, b), 0) + 1
            key = tuple(sorted(ms.items()))
            if contrib.setdefault(mdiag[(c, i)], key) != key:
                consistent = False
    print(f'  ==> the cross-copy contribution to the DIAGONAL is determined by M-col(c,i): '
          f'{consistent}   ({len(contrib)} distinct contributions)')

    # hypothesis C: the cross-copy colour is the JOINT SLOT ALIGNMENT of the two copies' M-data,
    # i.e. the tuple over (k,t) of (M(c)-colour of (i, f(k,t)), M(c')-colour of (f(k,t), l)).
    # This is what aggregating a cross-copy pair over the shared frame produces, and it is the
    # natural closed form if the frame is the ONLY channel correlating two copies.
    intern2, pf = {}, {}
    for c in allc:
        _, pfc = single_copy(c, intern2, True)
        pf[c] = pfc
    mapC, okC = {}, True
    for c in allc:
        for cp in allc:
            if c == cp:
                continue
            for i in range(L):
                for l in range(L):
                    v = ecol[eidx[('p', c, i)] * n + eidx[('p', cp, l)]]
                    # ⚠ MUST be a MULTISET, not an ordered tuple.  The tuple form encodes both
                    # copies outright: it gave 64512 classes over 64512 pairs, i.e. an INJECTIVE key,
                    # so "determines the colour" was vacuously true.  WL aggregates over z and
                    # produces a multiset, so the multiset is also the faithful form.
                    ms_ = {}
                    for k in range(NS):
                        for t in (0, 1):
                            kk = (pf[c][(i, k, t)], pf[cp][(l, k, t)])
                            ms_[kk] = ms_.get(kk, 0) + 1
                    kC = (mdiag[(c, i)], mdiag[(cp, l)], tuple(sorted(ms_.items())))
                    if mapC.setdefault(kC, v) != v:
                        okC = False
    print(f'  C: determined by M-diagonals + the slot-alignment MULTISET : {okC}'
          f'   ({len(mapC)} classes)')
