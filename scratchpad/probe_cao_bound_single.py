"""probe_cao_bound_single.py — item 1: is the ensemble's 2-WL bounded by a POLY-SIZE single-copy model?

METHOD (why this is a bound and not a fit).  WL's stable colouring is the COARSEST stable partition
refining the atoms.  So to prove `ensemble-2-WL is coarser than X` it suffices to exhibit ANY stable
partition refining the atoms whose payload part is X -- no computation on the big object needed.
This probe hunts for the right X by testing candidates against L=4 ground truth; the stability proof
is the separate step.

THE CANDIDATE.  Two structural facts point at a single-copy model:

  (a) FRAME-FRAME PAIRS CARRY <= 12 COLOURS, FOR EVERY L.  WL is always coarser than the orbit
      partition, and S_L's orbits on ordered pairs of slots are classified by (t, t', |k ∩ k'|) with
      |k ∩ k'| in {0,1,2}.  So the frame is a FIXED, copy-independent object: it cannot accumulate
      payload data at any round.  (This one is a theorem, not a guess.)

  (b) THE CROSS-COPY CHANNEL MAY AVERAGE AWAY.  At round 1 the colour of (p(c,i), p(c',l)) depends
      only on δ = c ⊕ c' -- adjacency agreement at slot {i,l}, or dist_i(c,c') when i = l.  Summing
      over all c' = c ⊕ δ is then a sum over all δ, which is independent of c.  That is precisely the
      averaging that collapsed 1-WL to the degree sequence in section 6a.

If (a) and (b) both survive to the fixpoint, the ensemble's 2-WL on copy c is determined by
    M(c) = c's payload (a clique) + the 2d frame vertices, frame-frame pairs FROZEN
which has L + 2d = L^2 vertices.  For L=16 that is 256 -- so Shrikhande/rook and CFI[K4] would become
directly computable against a FAITHFUL object, which nothing in this doc has managed.

⚠ Freezing at the ORBIT level is an upper bound on what the ensemble gives the frame, so if M(c)
over-separates that is expected and informative; the ensemble's true frame-frame colouring is read
off here and compared, rather than assumed.

⚠ Copies are separate graphs, so their colours are only comparable if every copy is refined for the
SAME number of rounds under a SHARED intern table (the trap recorded in section 8(e)).
"""

from itertools import combinations
from probe_cao_gauge2_ablate import build, wl2_full, L, NS, NC, SLOT, PAIRS

ROUNDS = 12


def frame_pair_class(k, t, kk, tt):
    return (t, tt, len(set(PAIRS[k]) & set(PAIRS[kk])))


def single_copy(c, intern, freeze):
    """M(c): L payload forming a clique + 2*NS frame vertices, frame-frame pairs frozen at their
    S_L-orbit class.  Returns the payload-pair colouring after ROUNDS lockstep rounds."""
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
            if freeze and x[0] == 'f' and y[0] == 'f':
                key = ('F',) + frame_pair_class(x[1], x[2], y[1], y[2]) + (x == y,)
                frozen[p] = True
            else:
                key = (x == y, (x, y) in adjset,
                       x[0] == 'p', y[0] == 'p',
                       x[2] if x[0] == 'f' else -1, y[2] if y[0] == 'f' else -1)
            col[p] = intern.setdefault(key, len(intern))

    for _ in range(ROUNDS):
        C = max(col) + 1
        new = [0] * (n * n)
        rng = range(n)
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
    out = {(i, j): col[idx[('p', i)] * n + idx[('p', j)]] for i in range(L) for j in range(L)}
    pf = {(i, k, t): col[idx[('p', i)] * n + idx[('f', k, t)]]
          for i in range(L) for k in range(NS) for t in (0, 1)}
    return out, pf


def same_partition(a, b):
    m1, m2 = {}, {}
    for k in a:
        if m1.setdefault(a[k], b[k]) != b[k] or m2.setdefault(b[k], a[k]) != a[k]:
            return False
    return True


if __name__ == '__main__':
    allc = list(range(NC))
    print(f'L={L}: ensemble {L*NC + 2*NS + NC} vertices vs single-copy model {L + 2*NS}', flush=True)
    ecol, everts, eidx = wl2_full(*build(allc, True), 'ensemble')
    n = len(everts)

    # --- fact (a): read the ensemble's own frame-frame colouring and check it against (t,t',|k∩k'|)
    obs, agree = {}, True
    for k in range(NS):
        for t in (0, 1):
            for kk in range(NS):
                for tt in (0, 1):
                    cls = frame_pair_class(k, t, kk, tt)
                    v = ecol[eidx[('f', k, t)] * n + eidx[('f', kk, tt)]]
                    if obs.setdefault(cls, v) != v:
                        agree = False
    nff = len({ecol[eidx[('f', k, t)] * n + eidx[('f', kk, tt)]]
               for k in range(NS) for t in (0, 1) for kk in range(NS) for tt in (0, 1)})
    print(f'  frame-frame pair colours in the ensemble: {nff}  (orbit classes present: {len(obs)})')
    print(f'  ==> frame-frame colouring IS exactly the (t,t\',|k∩k\'|) classification: {agree}')

    # --- the candidate, against ground truth
    truth = {}
    for c in allc:
        for i in range(L):
            for j in range(L):
                truth[(c, i, j)] = ecol[eidx[('p', c, i)] * n + eidx[('p', c, j)]]

    truth_pf = {(c, i, k, t): ecol[eidx[('p', c, i)] * n + eidx[('f', k, t)]]
                for c in allc for i in range(L) for k in range(NS) for t in (0, 1)}

    for freeze in (True, False):
        intern = {}
        cand, cand_pf = {}, {}
        for c in allc:
            pc, pf = single_copy(c, intern, freeze)
            for (i, j), v in pc.items():
                cand[(c, i, j)] = v
            for (i, k, t), v in pf.items():
                cand_pf[(c, i, k, t)] = v
        ok = same_partition(truth, cand)
        nt, nc_ = len(set(truth.values())), len(set(cand.values()))
        print(f'  single-copy model, frame frozen={freeze}: {nc_} colours vs ensemble {nt} '
              f'-> IDENTICAL: {ok}')
        # diagonal / vertex partition, which is what CAO is about
        dt = {(c, i): truth[(c, i, i)] for c in allc for i in range(L)}
        dc = {(c, i): cand[(c, i, i)] for c in allc for i in range(L)}
        print(f'      diagonal      : {len(set(dc.values()))} vs {len(set(dt.values()))} '
              f'-> IDENTICAL: {same_partition(dt, dc)}')
        # payload-frame: the channel that could disagree without showing in the payload restriction
        print(f'      payload-frame : {len(set(cand_pf.values()))} vs '
              f'{len(set(truth_pf.values()))} -> IDENTICAL: '
              f'{same_partition(truth_pf, cand_pf)}')
