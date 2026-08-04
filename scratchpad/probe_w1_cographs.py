#!/usr/bin/env python3
"""probe_w1_cographs.py — W1 step 0c: does the COGRAPH family pass the same gate?

docs/chain-descent-wind-down.md §2 W1.  Follow-on to probe_w1_multipartite.py, which passed
(1766 graphs, 0 failures) but on a family canonizable by sorting degrees -- viable, weak as a
headline.  Cographs (P4-free graphs) are the next candidate on the SAME mechanism: their
modular decomposition is a cotree, so 1-WL cells still ought to be modules, but the class is
genuinely named and not degree-sortable.

Same statement, same soundness discipline, same reduction as probe_w1_multipartite -- this file
only swaps the graph generator.  In particular the measured claim is again the
SELECTOR-INDEPENDENT one (every cell at every reached node is a single orbit), which implies
`Deepen.Tinhofer` under any selector and is therefore convention-immune; and `same_orbit`
verdicts are positive certificates only, with `None` tracked as UNKNOWN and never as a pass.

⚠ CEILING, recorded so the result is not over-read.  Cographs are linear-time canonizable via
modular decomposition, so passing here still does not give W4 a "hard family" headline -- see
wind-down §1 (consume lands inside the known-easy Tinhofer hierarchy).  The only place W1 could
produce a genuinely novel claim is a family that is PATH-LOCAL Tinhofer but NOT Tinhofer, which
is DUAL_resolver_scoping.md §8.5's open gap.  This probe does not attempt that.

`module_of` below is the index of the top-level cotree child containing a vertex -- the maximal
modules, i.e. the cograph analogue of the multipartite "parts", used only for the shape tally.

    cd /workspace/scratchpad && python3 -u probe_w1_cographs.py > probe_w1_cographs.out 2>&1
"""

import os
from functools import lru_cache

import probe_w1_multipartite as P


# ---------------------------------------------------------------- cotree generation
@lru_cache(maxsize=None)
def roots(n, lab):
    """Canonical cotree strings on `n` >= 2 vertices whose root is a union (lab=0) / join (lab=1).

    Levels alternate (a union node's children are leaves or join nodes and vice versa), which is
    what makes the cotree -- hence the string -- unique per cograph.  Children are emitted in
    non-decreasing pool order, so the child list is sorted and the string is canonical.
    """
    tag = 'U' if lab == 0 else 'J'
    pool = []
    for s in range(1, n):
        if s == 1:
            pool.append((1, 'x'))
        else:
            for c in roots(s, 1 - lab):
                pool.append((s, c))
    pool.sort()
    out = []

    def rec(start, rem, chosen):
        if rem == 0:
            if len(chosen) >= 2:
                out.append(tag + '(' + ','.join(c for _, c in chosen) + ')')
            return
        for i in range(start, len(pool)):
            s, c = pool[i]
            if s > rem:
                break
            rec(i, rem - s, chosen + [(s, c)])

    rec(0, n, [])
    return tuple(out)


def cographs(n):
    if n == 1:
        return ['x']
    return list(roots(n, 0)) + list(roots(n, 1))


def parse(s, i=0):
    """Recursive descent -> ('x',) | (tag, [children])."""
    if s[i] == 'x':
        return ('x',), i + 1
    tag = s[i]
    i += 2                                   # skip tag and '('
    kids = []
    while True:
        node, i = parse(s, i)
        kids.append(node)
        if s[i] == ',':
            i += 1
        else:                                # ')'
            return (tag, kids), i + 1


def realize(tree):
    """Cotree -> (n, adj, module_of).  Vertices numbered left to right."""
    def assign_edges(node, verts):
        """Edges strictly inside a subtree whose vertex list is already fixed."""
        if node[0] == 'x':
            return None, None, []
        groups, at = [], 0
        for k in node[1]:
            sz = size(k)
            groups.append(verts[at:at + sz])
            at += sz
        edges = []
        if node[0] == 'J':
            for a in range(len(groups)):
                for b in range(a + 1, len(groups)):
                    for u in groups[a]:
                        for w in groups[b]:
                            edges.append((u, w))
        for k, vs in zip(node[1], groups):
            _, _, e = assign_edges(k, vs)
            edges += e
        return None, None, edges

    def size(node):
        return 1 if node[0] == 'x' else sum(size(k) for k in node[1])

    n = size(tree)
    verts = list(range(n))
    _, _, edges = assign_edges(tree, verts) if tree[0] != 'x' else (None, None, [])
    adj = [[0] * n for _ in range(n)]
    for u, w in edges:
        adj[u][w] = adj[w][u] = 1
    module_of = [0] * n
    if tree[0] != 'x':
        at = 0
        for gi, k in enumerate(tree[1]):
            sz = size(k)
            for v in range(at, at + sz):
                module_of[v] = gi
            at += sz
    return n, adj, module_of


def main():
    nmax = int(os.environ.get('W1_NMAX', '9'))
    lines = []

    def log(msg):
        print(msg)
        lines.append(msg)

    log('=' * 96)
    log(f'W1 step 0c — COGRAPHS (P4-free), n <= {nmax}: every cell at every reached node an orbit?')
    log('same statement / soundness / orbit reduction as probe_w1_multipartite (see its header)')
    log('=' * 96)

    results = []
    for n in range(2, nmax + 1):
        cs = cographs(n)
        log(f'\n--- n = {n}  ({len(cs)} cographs up to isomorphism) ---')
        fails = unk = 0
        deep = 0
        maxlev = 0
        for idx, s in enumerate(cs):
            tree, _ = parse(s)
            nn, adj, mod = realize(tree)
            if not P.budget_left(f'cograph n={n} #{idx}'):
                log(f'  SKIPPED (budget) at n={n} #{idx}')
                break
            r = P.walk(nn, adj, mod, log, f'cograph[{s}]')
            f = r.pop('fails')
            if f:
                fails += 1
                log(f'  ⛔ FAIL {s}  ({len(f)} bad nodes) first={f[0]}')
            if r['unknown']:
                unk += 1
                log(f'  ⚠ UNKNOWN {s}  ({r["unknown"]} budget-out pairs)')
            if r['levels'] >= 2:
                deep += 1
            maxlev = max(maxlev, r['levels'])
            results.append(r)
        log(f'  n={n}: {len(cs)} graphs, failures={fails}, unknown={unk}, '
            f'levels>=2 in {deep}, max levels={maxlev}')

    log('\n' + '=' * 96)
    total = len(results)
    tf = sum(1 for r in results if r.get('unknown'))
    log(f'cographs run        : {total}')
    log(f'FAILURES            : 0 unless listed above')
    log(f'graphs with UNKNOWN : {tf}')
    log(f'max levels          : {max([r["levels"] for r in results], default=0)}')
    log(f'non-vacuity levels>=2: {sum(1 for r in results if r["levels"] >= 2)} of {total}')
    log(f'cells in one module : {sum(r["within"] for r in results)}')
    log(f'cells spanning >=2  : {sum(r["spans"] for r in results)}')
    log(f'truncated           : {sum(1 for r in results if r["trunc"])}')
    log(f'SKIPPED (logged)    : {P.SKIPPED}')


if __name__ == '__main__':
    main()
