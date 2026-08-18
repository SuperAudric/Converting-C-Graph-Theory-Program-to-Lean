"""probe_cao_multipede_curve.py -- the individualization collapse curve, across instance sizes.

The reader's test on a RIGID multipede costs prod |cell|! on the residual cells after free
individualization.  So the question is: is there an instance whose cells collapse SLOWLY enough that
some intermediate step has a small prod |cell|! while still carrying a mixed cell?
"""
import math, random
import numpy as np
from probe_cao_multipede2 import gf2_rank, multipede_adj
from probe_cao_multipede3 import partial_steiner
from probe_cao_multipede_indiv import wl2_diag_col, profile

rng = random.Random(4242)
print(f'{"deg":>3} {"m":>3} {"c":>3} {"n":>4}   collapse curve: prod|cell|! after k individualizations')
for deg in (3, 4):
    for m in (12, 16, 20, 24, 30, 36):
        for ratio in (1.0, 1.3):
            c = int(ratio * m)
            inst = None
            for _ in range(400):
                cons = partial_steiner(m, c, deg, rng)
                if cons is None:
                    continue
                rows = [sum(1 << v for v in N) for N in cons]
                if gf2_rank(rows, m) != m:
                    continue
                n, A = multipede_adj(m, cons)
                if n > 400:
                    break
                d = wl2_diag_col(n, A, np.zeros(n, dtype=np.int64))
                if len(profile(d)[0]) > 1:
                    inst = (n, A)
                    break
            if inst is None:
                continue
            n, A = inst
            init = np.zeros(n, dtype=np.int64)
            curve, k = [], 0
            while k < 12:
                d = wl2_diag_col(n, A, init)
                cells = profile(d)
                ns = [x for x in cells if len(x) > 1]
                cost = 1
                for x in cells:
                    cost *= math.factorial(len(x))
                curve.append(cost)
                if not ns:
                    break
                init = init.copy(); init[ns[0][0]] = k + 1; k += 1
            pretty = ' -> '.join(f'{x:.3g}' if x > 1e6 else str(x) for x in curve)
            print(f'{deg:>3} {m:>3} {c:>3} {n:>4}   {pretty}', flush=True)
