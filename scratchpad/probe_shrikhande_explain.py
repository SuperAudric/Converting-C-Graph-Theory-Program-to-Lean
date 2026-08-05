"""Shrikhande, spelled out: exactly what holds at the CAO root, and what holds after
individualization.  Answers 'is this a CAO-propagation counterexample?' (it is NOT).

Distinguishes the two readings of the condensation claim:
  FROM-version : multiset of paths FROM u  == multiset of paths FROM w, for u,w in one cell
  BETWEEN-vers.: multiset of paths BETWEEN (v,u) determined by [cell(v), adj, cell(u)]
"""
import sys
from probe_pathcondense import (shrikhande, rank_partition, npairclasses, same,
                                orbital_partition, wl2_pair_closure, walk_partition)
from probe_pathanno import simple_paths_profiles
from probe_cao_cleanroom import all_isos, orbits

n, adj = shrikhande()
auts = all_isos(n, adj, [0] * n, [0] * n)
orb = orbits(n, auts)
print(f'Shrikhande  n={n}  |Aut|={len(auts)}')
print(f'  root orbit-cells: {len(set(orb))}  (vertex-transitive)')
print(f'  ==> ROOT CAO HOLDS: the single cell IS the single Aut-orbit.\n')

v = 0
stab = [g for g in auts if g[v] == v]
korb = orbits(n, stab)
groups = {}
for x in range(n):
    groups.setdefault(korb[x], []).append(x)
gl = sorted(groups.values(), key=lambda s: (len(s), s))
print(f'  v = {v},  |Aut_v| = {len(stab)},  Aut_v-orbits: {[len(g) for g in gl]}')
for g in gl:
    print(f'    size {len(g):2d}  adj to v: {adj[v][g[0]]}   {g}')

far = [g for g in gl if adj[v][g[0]] == 0 and len(g) > 1]
A, B = (far[0], far[1]) if len(far[0]) < len(far[1]) else (far[1], far[0])
u, w = A[0], B[0]
print(f'\n  TWO FAR VERTICES IN DIFFERENT Aut_v-ORBITS:  u={u} (orbit size {len(A)}), '
      f'w={w} (orbit size {len(B)})')
print(f'    adj(v,u)={adj[v][u]}  adj(v,w)={adj[v][w]}  '
      f'same root cell? {orb[u]==orb[w]}  (all 16 are one cell)')

cn_u = [x for x in range(n) if adj[v][x] and adj[u][x]]
cn_w = [x for x in range(n) if adj[v][x] and adj[w][x]]
print(f'    common nbrs of v,u = {cn_u}   adjacent to each other? {adj[cn_u[0]][cn_u[1]]}')
print(f'    common nbrs of v,w = {cn_w}   adjacent to each other? {adj[cn_w[0]][cn_w[1]]}')
print('    ^ this is the whole distinction (doc 14.3)\n')

P_orb = orbital_partition(n, auts)
P_2wl = wl2_pair_closure(n, adj)
P_walk = walk_partition(n, adj)
print('  --- AT THE ROOT (before individualizing anything) ---')
print(f'    orbital of (v,u) vs (v,w):  {P_orb[(v,u)]} vs {P_orb[(v,w)]}   '
      f'SAME? {P_orb[(v,u)]==P_orb[(v,w)]}   <-- truth: DIFFERENT orbitals')
print(f'    2-WL class of (v,u) vs (v,w): {P_2wl[(v,u)]} vs {P_2wl[(v,w)]}   '
      f'SAME? {P_2wl[(v,u)]==P_2wl[(v,w)]}   <-- 2-WL fuses them')
print(f'    walk counts equal?            {P_walk[(v,u)]==P_walk[(v,w)]}')
for L in (3, 5, 6, 7):
    A1, A2 = simple_paths_profiles(n, adj, L)
    print(f'    len<={L}: simple-path counts equal? {str(A1[(v,u)]==A1[(v,w)]):5s}   '
          f'annotated equal? {A2[(v,u)]==A2[(v,w)]}')
print(f'    ==> BETWEEN-version of condensation FAILS at the CAO root:')
print(f'        [cell,adj,cell] is identical for (v,u) and (v,w), the path multisets are not.')

print('\n  --- FROM-version (paths FROM a vertex, within a cell) ---')
A1f, _ = simple_paths_profiles(n, adj, 7)
fromprof = {x: tuple(sorted(A1f[(x, y)] for y in range(n))) for x in range(n)}
print(f'    distinct "paths FROM" profiles across the 16 vertices: '
      f'{len(set(fromprof.values()))}  (cells: {len(set(orb))})')
print('    ==> FROM-version HOLDS -- but it is CAO restated, not new information.')

print('\n  --- AFTER INDIVIDUALIZING v (the actual CAO-propagation question) ---')
vcol = [0] * n
c = {(a, b): (vcol[a], vcol[b], adj[a][b], a == b, a == v, b == v)
     for a in range(n) for b in range(n)}
c = rank_partition(c)
for r in range(1, 20):
    nxt = rank_partition({(a, b): (c[(a, b)],
                                   tuple(sorted((c[(a, x)], c[(x, b)]) for x in range(n))))
                          for a in range(n) for b in range(n)})
    sep = nxt[(v, u)] != nxt[(v, w)]
    print(f'    round {r}: (v,u) vs (v,w) separated? {sep}')
    if same(nxt, c):
        break
    c = nxt
    if sep:
        break
fib = [c[(x, x)] for x in range(n)]
target = [korb[x] for x in range(n)]
ok = all((fib[x] == fib[y]) == (target[x] == target[y]) for x in range(n) for y in range(n))
print(f'    final 2-WL fibres = Aut_v-orbits?  {ok}   '
      f'({len(set(fib))} fibres, {len(set(target))} orbits)')
print('    ==> CAO IS PRESERVED. Shrikhande is NOT a counterexample.')
sys.stdout.flush()
