#!/usr/bin/env python3
"""Is the CAO-propagation failure 1-WL-specific, or does 2-WL see the Aut(G)-type too?

After individualizing one line of net(G), 1-WL leaves the q-1 parallel lines in ONE cell
while the orbits split them by Aut(G)-type.  Run 2-WL (pair colouring) on the same
individualized graph and read off the induced vertex partition.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells
from probe_cao_net import net


def twowl(n, adj, vcol):
    col = {}
    for u in range(n):
        for v in range(n):
            col[(u, v)] = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
    rank = {c: i for i, c in enumerate(sorted(set(col.values())))}
    col = {k: rank[v] for k, v in col.items()}
    while True:
        sig = {}
        for u in range(n):
            for v in range(n):
                sig[(u, v)] = (col[(u, v)],
                               tuple(sorted((col[(u, w)], col[(w, v)]) for w in range(n))))
        rank = {s: i for i, s in enumerate(sorted(set(sig.values())))}
        new = {k: rank[s] for k, s in sig.items()}
        if all(new[k] == col[k] for k in col):
            return col
        col = new


for mods in [(4,), (2, 2), (8,), (6,)]:
    n, adj, names, q = net(mods)
    root = wl(n, adj, [0] * n)
    L = names.index(('L', 0, tuple(0 for _ in mods)))
    c1 = wl(n, adj, individualize(n, root, L))
    p2 = twowl(n, adj, c1)
    v2 = [p2[(v, v)] for v in range(n)]
    par = [v for v in range(n) if names[v][0] == 'L' and names[v][1] == 0 and v != L]
    g = defaultdict(list)
    for v in par:
        g[v2[v]].append(names[v][2])
    G = "Z" + "xZ".join(str(m) for m in mods)
    print(f"net({G:8s}) n={n}: 1-WL cell of the {len(par)} parallel lines -> "
          f"2-WL splits it into {len(g)} classes {[sorted(x) for x in g.values()]}")
    print(f"           total cells: 1-WL {len(set(c1))}, 2-WL(diagonal) {len(set(v2))}")
