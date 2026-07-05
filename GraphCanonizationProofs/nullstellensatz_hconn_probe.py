#!/usr/bin/env python3
"""Test connectivity of the `ratio_step` edge-graph on anisotropic vectors (2026-07-05).

`ratio_step` proves: for isotropic a with polar Q a y != 0, the ratio R/Q is preserved
along the edge  y -- y+a  (when y+a is also anisotropic). So if this GRAPH on anisotropic
vectors is CONNECTED, the ratio is globally constant => R = mu*Q. The edge relation:
  y -- y'  iff  Q(y'-y)=0  and  polar Q y (y'-y) != 0   (both anisotropic).
(Diameter-2 was too tight and failed; connectivity via any path length is what the
assembly actually needs -- we can prove `const` from full connectivity.)

Reports: #anisotropic, #components, largest component size. CONNECTED (1 component) is
what we need. Also reports graph diameter of the giant component (informs whether a
bounded-diameter Lean formalization is viable, or we need general path induction).
"""
import itertools
from collections import deque

def nonsquare(q):
    sq = {(a*a) % q for a in range(q)}
    return next(n for n in range(1, q) if n not in sq)

def build(d, q, kind):
    coeffs = [1]*d if kind == '+' else [1]*(d-1) + [nonsquare(q)]
    def Q(x): return sum(c*xi*xi for c, xi in zip(coeffs, x)) % q
    def polar(x, y):
        return (Q(tuple((a+b) % q for a, b in zip(x, y))) - Q(x) - Q(y)) % q
    return Q, polar

def run(d, q, kind, diam=False):
    Q, polar = build(d, q, kind)
    V = list(itertools.product(range(q), repeat=d))
    aniso = [v for v in V if Q(v) != 0]
    idx = {v: i for i, v in enumerate(aniso)}
    n = len(aniso)
    # adjacency: y -- y' iff Q(y'-y)=0 and polar Q y (y'-y) != 0
    adj = [[] for _ in range(n)]
    for i, y in enumerate(aniso):
        for j in range(i+1, n):
            yp = aniso[j]
            diff = tuple((a-b) % q for a, b in zip(yp, y))
            if Q(diff) == 0 and polar(y, diff) != 0:
                adj[i].append(j); adj[j].append(i)
    # components via BFS
    seen = [False]*n
    comps = []
    for s in range(n):
        if seen[s]: continue
        seen[s] = True; comp = [s]; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = True; comp.append(w); dq.append(w)
        comps.append(comp)
    comps.sort(key=len, reverse=True)
    ncomp = len(comps); big = len(comps[0])
    # diameter (BFS from a few sources in the giant comp) -- only if small graph
    dmax = None
    if diam and big <= 700:
        cset = set(comps[0]); srcs = comps[0][:min(30, big)]
        dmax = 0
        for s in srcs:
            dist = {s: 0}; dq = deque([s])
            while dq:
                u = dq.popleft()
                for w in adj[u]:
                    if w not in dist:
                        dist[w] = dist[u]+1; dq.append(w)
            if len(dist) == big:
                dmax = max(dmax, max(dist.values()))
    return n, ncomp, big, dmax

if __name__ == '__main__':
    for d, q, kind in [(4,3,'+'),(4,3,'-'),(4,5,'-'),(4,7,'-'),(5,3,'-'),(6,3,'-')]:
        n, ncomp, big, dmax = run(d, q, kind, diam=True)
        status = "CONNECTED" if ncomp == 1 else f"*** {ncomp} COMPONENTS ***"
        dtxt = f" diam={dmax}" if dmax is not None else ""
        print(f"d={d} q={q} {kind}  aniso={n:5d}  components={ncomp:3d}  giant={big:5d}{dtxt}  {status}")
