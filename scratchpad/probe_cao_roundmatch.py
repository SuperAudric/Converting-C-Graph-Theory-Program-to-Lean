"""probe_cao_roundmatch.py — does the §6d collapse hold ROUND BY ROUND, or only at the fixpoint?

WHY THIS MATTERS.  §6e.5's resolution R1 -- the plan's first-choice route -- proves the collapse by
INDUCTION ON THE WL ROUND.  That presupposes that ensemble-round r corresponds to M-round r (or to
r + s for a fixed offset s).  Every existing measurement (§6d.3) compares only the FIXPOINTS: the
prober runs M for 12 rounds and the ensemble to stability, then compares.  So R1's premise has never
been tested, and it is not free -- the two objects start from different atoms (the ensemble must
EARN the frame types from the individualized m(0); M is handed them), so at minimum there is an
offset, and there may be no round-wise correspondence at all.

WHAT IS MEASURED.  The payload-pair partition of the ensemble after r_e rounds, against the payload-
pair partition of the single-copy frozen model M(c) after r_m rounds, for every (r_e, r_m) in a grid.
Reported as a refinement relation, not a colour count (§7 filter 7).

READING IT.
  a diagonal of IDENTICAL at r_m = r_e + s  ==> R1's premise holds with offset s; the induction has
                                               a well-defined statement to carry.
  IDENTICAL only at the fixpoint             ==> R1 must carry a WEAKER round-indexed invariant that
                                               only closes in the limit -- worth knowing BEFORE
                                               investing in the induction.
  never IDENTICAL off the fixpoint, and the
  relation flips direction with r            ==> the two refinement schedules genuinely interleave;
                                               R3 (bound by M+) becomes the better first target.
"""

import sys
from probe_cao_gauge2_ablate import build, L, NS, NC, SLOT, PAIRS

# ⚠ argv[1] is L, consumed by probe_cao_gauge2_ablate on import -- do NOT reuse that slot.
RE = int(sys.argv[2]) if len(sys.argv) > 2 else 5      # ensemble rounds to record
RM = int(sys.argv[3]) if len(sys.argv) > 3 else 6      # M rounds to record


def wl2_rounds(verts, adj, vcol, rounds, tag):
    """2-WL recording the FULL pair colouring after each round 0..rounds."""
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = [0] * (n * n)
    atoms = {}
    for x in verts:
        a = idx[x]
        for y in verts:
            k = (x == y, (x, y) in adj, vcol[x], vcol[y])
            col[a * n + idx[y]] = atoms.setdefault(k, len(atoms))
    ncol = len(set(col))
    snaps = [list(col)]
    for r in range(1, rounds + 1):
        C = ncol
        colT = [0] * (n * n)
        for a in range(n):
            for b in range(n):
                colT[b * n + a] = col[a * n + b]
        table, new = {}, [0] * (n * n)
        rng = range(n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                rb = colT[b * n:(b + 1) * n]
                cnt = {}
                for z in rng:
                    key = ra[z] * C + rb[z]
                    cnt[key] = cnt.get(key, 0) + 1
                sig = (col[a * n + b], tuple(sorted(cnt.items())))
                t = table.get(sig)
                if t is None:
                    t = table[sig] = len(table)
                new[a * n + b] = t
        stable = len(table) == ncol
        col, ncol = new, len(table)
        snaps.append(list(col))
        print(f'  [{tag}] round {r}: {ncol} pair colours{"  (STABLE)" if stable else ""}',
              flush=True)
        if stable:
            break
    return snaps, idx


def frame_pair_class(k, t, kk, tt):
    return (t, tt, len(set(PAIRS[k]) & set(PAIRS[kk])))


def m_rounds(c, intern, rounds):
    """M(c) frozen, recording the payload-pair colouring after each round 0..rounds."""
    verts = [('p', i) for i in range(L)] + [('f', k, t) for k in range(NS) for t in (0, 1)]
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    adjset = set()

    def add(u, w):
        adjset.add((u, w))
        adjset.add((w, u))

    for a in range(L):
        for b in range(a + 1, L):
            add(('p', a), ('p', b))
    for a in range(L):
        for b in range(L):
            if a != b:
                add(('p', a), ('f', SLOT[(a, b)], (c >> SLOT[(a, b)]) & 1))
    for k in range(NS):
        add(('f', k, 0), ('f', k, 1))

    col = [0] * (n * n)
    frozen = [False] * (n * n)
    for x in verts:
        for y in verts:
            p = idx[x] * n + idx[y]
            if x[0] == 'f' and y[0] == 'f':
                key = ('F',) + frame_pair_class(x[1], x[2], y[1], y[2]) + (x == y,)
                frozen[p] = True
            else:
                key = (x == y, (x, y) in adjset, x[0] == 'p', y[0] == 'p',
                       x[2] if x[0] == 'f' else -1, y[2] if y[0] == 'f' else -1)
            col[p] = intern.setdefault(key, len(intern))

    out = [{(i, j): col[idx[('p', i)] * n + idx[('p', j)]]
            for i in range(L) for j in range(L)}]
    rng = range(n)
    for _ in range(rounds):
        C = max(col) + 1
        new = [0] * (n * n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                p = a * n + b
                if frozen[p]:
                    new[p] = intern.setdefault(('frozen', col[p]), len(intern))
                    continue
                cnt = {}
                for z in rng:
                    key = ra[z] * C + col[z * n + b]
                    cnt[key] = cnt.get(key, 0) + 1
                new[p] = intern.setdefault((col[p], tuple(sorted(cnt.items()))), len(intern))
        col = new
        out.append({(i, j): col[idx[('p', i)] * n + idx[('p', j)]]
                    for i in range(L) for j in range(L)})
    return out


def relation(pa, pb, keys):
    a2b, b2a = {}, {}
    af = bf = True
    for k in keys:
        x, y = pa[k], pb[k]
        if a2b.setdefault(x, y) != y:
            af = False
        if b2a.setdefault(y, x) != x:
            bf = False
    if af and bf:
        return 'IDENT'
    if af:
        return 'E-fine'          # ensemble strictly finer
    if bf:
        return 'M-fine'          # M strictly finer
    return 'INCOMP'


if __name__ == '__main__':
    allc = list(range(NC))
    print(f'L={L}, {NS} slots, {NC} copies; ensemble {L*NC + 2*NS + NC} vertices', flush=True)

    esnaps, eidx = wl2_rounds(*build(allc, True), RE, 'ensemble')
    n = len(eidx)

    intern = {}
    msnaps = {c: m_rounds(c, intern, RM) for c in allc}
    print(f'  [M] {L + 2*NS} vertices per copy, {RM} rounds recorded', flush=True)

    keys = [(c, i, j) for c in allc for i in range(L) for j in range(L)]
    print(f'\nrows = ensemble round, cols = M round.  E-fine = ensemble strictly finer.')
    hdr = '        ' + ''.join(f'{m:>9d}' for m in range(RM + 1))
    print(hdr)
    for re_ in range(len(esnaps)):
        ecol = esnaps[re_]
        etruth = {(c, i, j): ecol[eidx[('p', c, i)] * n + eidx[('p', c, j)]] for (c, i, j) in keys}
        ne = len(set(etruth.values()))
        row = []
        for rm in range(RM + 1):
            mtruth = {(c, i, j): msnaps[c][rm][(i, j)] for (c, i, j) in keys}
            row.append(relation(etruth, mtruth, keys))
        print(f'  e{re_} ({ne:4d})' + ''.join(f'{r:>9s}' for r in row), flush=True)

    print('\nM colour counts per round: '
          + ', '.join(f'r{rm}={len({msnaps[c][rm][(i,j)] for c in allc for i in range(L) for j in range(L)})}'
                      for rm in range(RM + 1)))
