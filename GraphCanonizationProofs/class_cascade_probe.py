#!/usr/bin/env python3
"""
CLASS-ANCHORED CASCADE PROBE (2026-07-02).  [pure-python, no numpy]

Tests the *viable* form of the "cascade / web" attack: propagate orbit resolution by refining
against whole resolved colour CLASSES (not singleton anchors). Contrast with the singleton
closure `pin_probe.py` already refuted.

Per good span-dim-2 base {0,a,b} (a,b orthogonal anisotropic) on ambient VO^eps_d(q) (1-WL,
isoClass edges), two cascades from the same base-individualized seed:
  FULL      : standard 1-WL — count isotropic-relations against ALL current colour classes.
  SINGLETON : count ONLY against currently-singleton classes (ambient analogue of pin_probe).

Measured: r* (rounds to stabilize); fan-out[r] = max over round-r classes of #children at r+1
(refinement-tree branching degree); reaches ORBITS?; SINGLETON stall vs orbits.
d-uniformity: FULL r*/fan-out across d at fixed q.  q-scaling: across q at d=4.
"""
import itertools, sys
from array import array
from collections import defaultdict
from model_gap import make_Q, sub, polar, isoclass, first_indep_anis, orbit_part, refines

def build_iso(V, Q, q, d):
    """flat array (n*n) of iso-of-difference: iso_flat[i*n+j] = isoClass(V[i]-V[j])."""
    n = len(V)
    iso_of = {v: isoclass(Q, q, d, v) for v in V}
    flat = array('b', bytes(n * n))
    for i in range(n):
        vi = V[i]; base = i * n
        for j in range(n):
            flat[base + j] = iso_of[sub(vi, V[j], q, d)]
    return flat

def relabel(sigs):
    o = {}; out = [0]*len(sigs)
    for i, s in enumerate(sigs):
        c = o.get(s)
        if c is None:
            c = len(o); o[s] = c
        out[i] = c
    return out, len(o)

def wl_round(flat, n, col, C, singleton_only):
    ok = None
    if singleton_only:
        sizes = [0]*C
        for c in col: sizes[c] += 1
        ok = [sizes[c] == 1 for c in range(C)]
    sigs = [None]*n
    for i in range(n):
        base = i*n
        hist = {}
        ci = col[i]
        for j in range(n):
            if j == i: continue
            cj = col[j]
            if ok is not None and not ok[cj]: continue
            h = hist.get(cj)
            if h is None:
                h = [0,0,0]; hist[cj] = h
            h[flat[base+j]] += 1
        sigs[i] = (ci, tuple(sorted((c, tuple(h)) for c, h in hist.items())))
    return relabel(sigs)

def cascade(flat, n, seed, C0, mode, maxr=14):
    col, C = list(seed), C0
    hist = []
    for r in range(1, maxr+1):
        nc, nC = wl_round(flat, n, col, C, mode == 'singleton')
        kids = defaultdict(set)
        for i in range(n): kids[col[i]].add(nc[i])
        fan = max(len(s) for s in kids.values())
        stable = (nC == C)
        hist.append((nC, fan, stable))
        col, C = nc, nC
        if stable: break
    return col, hist

def run(d, q, eps):
    V = list(itertools.product(range(q), repeat=d)); Q = make_Q(d, q, eps)
    n = len(V); nm = f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis = first_indep_anis(V, Q, q, d, d); a, b = anis[0], anis[1]
    S = [tuple([0]*d), a, b]; ortho = polar(Q, q, a, b, d) == 0
    orb = orbit_part(V, Q, q, S, d); norb = len(set(orb.values()))
    GRAM = {v: (Q(v), polar(Q,q,v,a,d), polar(Q,q,v,b,d)) for v in V}
    ngram = len(set(GRAM.values()))
    flat = build_iso(V, Q, q, d)
    idx = {v: i for i, v in enumerate(V)}
    seed = [0]*n
    for p, s in enumerate(S): seed[idx[s]] = p+1
    print(f"{nm}  |V|={n}  ortho-base={ortho}  GRAM#={ngram}  ORB#={norb}", flush=True)
    for mode in ('full', 'singleton'):
        col, hist = cascade(flat, n, seed, 4, mode)
        col_d = {V[i]: col[i] for i in range(n)}
        is_orb = refines(col_d, orb, V) and refines(orb, col_d, V)
        ref_gram = refines(col_d, GRAM, V)
        tag = 'ORBITS' if is_orb else ('refines-GRAM' if ref_gram else f'STALLED<{norb}')
        seq = ' '.join(f"{c}(fan{f})" for c, f, _ in hist)
        print(f"  {mode:9s}: {seq}  -> {hist[-1][0]} == {tag}", flush=True)
    print(flush=True)

if __name__ == "__main__":
    print("=== CLASS-ANCHORED vs SINGLETON cascade, VO^eps_d(q), good span-dim-2 base ===")
    print("format: <#cls>(fan<max split>) per round -> final == {ORBITS|refines-GRAM|STALLED}\n", flush=True)
    for eps in (-1, 1): run(4, 3, eps)      # q-scaling anchor + d=4
    for eps in (-1, 1): run(4, 5, eps)
    for eps in (-1, 1): run(4, 7, eps)
    for eps in (-1, 1): run(6, 3, eps)      # d-uniformity vs d=4
    for eps in (-1, 1): run(8, 3, eps)      # d-uniformity (expensive; last so prior prints survive)
