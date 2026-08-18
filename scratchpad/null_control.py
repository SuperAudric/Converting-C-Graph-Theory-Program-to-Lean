"""NULL control: is it the scaffold's CROSS-PAIR CONNECTIVITY that splits, or does attaching
anything in a closed family split?

matching scaffold = s disjoint edges, edge t joining the two feet of pair t.  An edge's two ends are
interchangeable, so copy eps and copy eps xor e_t are the SAME attached graph -- the family carries no
cross-pair correlation at all.  If cross-pair connectivity is the mechanism, this must NOT split."""
import random
import numpy as np
import probe_cao_ruler_threshold as T
from probe_cao_ruler_curve import rigid_ruler

def matching_ruler(k):
    A = np.zeros((k, k), dtype=bool)
    for i in range(0, k - 1, 2):
        A[i, i + 1] = A[i + 1, i] = True
    return A

def path_ruler(k):
    A = np.zeros((k, k), dtype=bool)
    for i in range(k - 1):
        A[i, i + 1] = A[i + 1, i] = True
    return A

rng = random.Random(4242)
got = T.find_base(10, rng)
cons, nb, Ab, pairs = got
print(f'=== NULL controls, base n={nb} ===', flush=True)
print('  s   matching (no cross-pair link)   path (linked, symmetric)   cycle   rigid', flush=True)
for s in (4, 5):
    k = 2 * s
    res = {'match': 0, 'path': 0, 'cycle': 0, 'rigid': 0}
    for t in range(4):
        S = rng.sample(range(len(pairs)), s)
        res['match'] += int(T.run(nb, Ab, pairs, S, matching_ruler(k), seeds=(7, 11))[0])
        res['path'] += int(T.run(nb, Ab, pairs, S, path_ruler(k), seeds=(7, 11))[0])
        res['cycle'] += int(T.run(nb, Ab, pairs, S, T.cycle_ruler(k), seeds=(7, 11))[0])
        res['rigid'] += int(T.run(nb, Ab, pairs, S, rigid_ruler(max(k, 7), rng), seeds=(7, 11))[0])
    print(f'  {s}   {res["match"]}/4                            {res["path"]}/4'
          f'                       {res["cycle"]}/4     {res["rigid"]}/4', flush=True)
