#!/usr/bin/env python3
"""probe_w1_multipartite.py — W1 step 0: is the complete-multipartite / cluster family
path-local Tinhofer at EVERY reached node?

docs/chain-descent-wind-down.md §2 W1 (as re-scoped 2026-08-04).

============================================================================================
THE QUESTION
============================================================================================
W1 needs a NAMED family discharging `KeyComplete.handledS_of_reached_tinhofer`, i.e.

    forall reached non-discrete chi,  Deepen.Tinhofer adj chi

The candidate is the complete multipartite graphs (and their complements, the cluster
graphs / disjoint unions of cliques).  Before any Lean is written this must be checked at
EVERY reached node -- the recorded sweep (DUAL_resolver_scoping.md §2.4, 1361 nodes) went to
depth <= 2 only, which is not enough to justify a totality proof.

============================================================================================
WHAT IS MEASURED, AND WHY IT IS CONVENTION-IMMUNE
============================================================================================
This probe checks the SELECTOR-INDEPENDENT statement

    at every reached non-discrete node, EVERY cell is a single orbit of the
    colour-preserving automorphism group

which is strictly stronger than `Deepen.Tinhofer` (that one asks only about the cell
`chooseIdK` selects, and only along one path).  Two consequences:

* It implies path-local Tinhofer under ANY selector, so a positive result transfers to the
  built object regardless of which cell `chooseIdK` picks.
* ⚠ It therefore DODGES the standing convention limit (cao-propagation.md §7.4 / §8.3,
  repeated in probe_route_a.py's header): Python ranks colour ids by `sorted(set(sig))` while
  Lean's `warmRefineVec` ranks by Cantor-paired `sigKey`, so the two disagree on colour-ID
  ORDER.  They agree on the PARTITION -- and 1-WL's output partition is a function of the
  input partition alone, never of the id order.  Since nothing here reads an id order (no
  `chooseIdK`, no "selected cell"), no Lean `#eval` cross-check is owed for a positive result.
  ⛔ Do NOT weaken this probe to the selected-cell-only form without reinstating that check.

============================================================================================
SOUNDNESS -- read before quoting any number
============================================================================================
* Same-orbit verdicts come from `probe_cao_vtcover.iso_exists`, whose positive answers are
  I-R leaves re-verified by `is_perm_aut` -- a POSITIVE result is a certificate, i.e. a
  theorem about the graph.  Per doc §8.1: only `is True` counts as same-orbit and only a
  completed `False` counts as different-orbit; `None` (budget out) is logged as UNKNOWN and
  never conflated with either.
* `probe_orbit_oracle` (doc §8.2, PROVEN BROKEN -- errs by MERGING) is NOT imported.
* Reached-node enumeration mirrors `Descend.Reaches`: root = 1-WL of the constant colouring;
  a step individualizes any vertex that HAS A SAME-COLOUR PARTNER (i.e. lies in a
  non-singleton cell) -- resolver-independent, matching `Descend.Reaches.step`.

============================================================================================
THE NON-VACUITY GATE (the live risk for W1, per the re-scoped wind-down)
============================================================================================
A family whose root refines to discrete satisfies `HandledS` for free
(`Residue.handled_of_root_discrete` already covers that ring) and proves NOTHING.  So a PASS
requires both:

    (a) zero cell-not-an-orbit failures, and
    (b) non-vacuity: descents with >= 2 reached non-discrete nodes on one path,
        i.e. the certificate is exercised at more than the root.

============================================================================================
COVERAGE -- the orbit reduction, and what it does and does not buy
============================================================================================
The reached set is over ORDERED individualization sequences, so an unreduced BFS is
exponential and hits NODE_CAP on anything interesting.  `expansion_vertices` therefore applies
doc §8.4's reduction -- one representative per cell -- but ONLY at a node where every cell was
just certified a single orbit, which is exactly the licence that makes it sound (see its
docstring).  Consequence:

    * `W1_REDUCE=0` -- unreduced baseline; honest but capped.  Recorded first, so the reduced
      run can be cross-checked against it on the graphs both cover.
    * `W1_REDUCE=1` (default) -- exhaustive modulo a certified reduction, reaching much larger n.

Either way every truncation and every budget skip is LOGGED; a `TRUNC` row is NOT exhaustive
coverage and must not be quoted as such.

Run detached and read the log (doc §9 -- do not pipe through `tail`):
    cd /workspace/scratchpad && python3 -u probe_w1_multipartite.py > probe_w1_multipartite.out 2>&1
"""

import os
import time

from probe_cao_cleanroom import wl, individualize, cells, is_perm_aut  # noqa: F401
from probe_cao_vtcover import same_orbit

T0 = time.time()
BUDGET_S = float(60 * 25)
NODE_CAP = 4000               # per graph; every truncation is LOGGED
SKIPPED = []


def budget_left(tag):
    if time.time() - T0 > BUDGET_S:
        SKIPPED.append(tag)
        return False
    return True


# ---------------------------------------------------------------- the family
def complete_multipartite(parts):
    """adj[i][j] = 1 iff i, j lie in DIFFERENT parts.  `parts` = list of part sizes."""
    part_of = []
    for pi, sz in enumerate(parts):
        part_of += [pi] * sz
    n = len(part_of)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j and part_of[i] != part_of[j]:
                adj[i][j] = 1
    return n, adj, part_of


def cluster(parts):
    """The complement: disjoint union of cliques (adj = 1 iff SAME part, i != j)."""
    n, adj, part_of = complete_multipartite(parts)
    for i in range(n):
        for j in range(n):
            if i != j:
                adj[i][j] = 1 - adj[i][j]
    return n, adj, part_of


# ---------------------------------------------------------------- descent (mirrors Descend.Reaches)
def root_colouring(n, adj):
    return wl(n, adj, [0] * n)


def is_discrete(col):
    return len(set(col)) == len(col)


def branch_vertices(col):
    """Vertices with a same-colour partner -- Descend.Reaches.step's side condition."""
    d = cells(col)
    return [v for c, vs in d.items() if len(vs) > 1 for v in vs]


def expansion_vertices(col, certified):
    """Which vertices to descend on.

    ⚠ THE ORBIT REDUCTION (cao-propagation.md §8.4: *"Under CAO, one representative per cell
    suffices when descending: the cell is one orbit, so other representatives give conjugate
    children"*).  It is applied **only at a node where every cell was just CERTIFIED a single
    orbit** -- there, for u, w in one cell there is a verified sigma in IsColAut(adj, col) with
    sigma u = w, and `step` is equivariant, so the subtree at w is an isomorphic copy of the
    subtree at u and carries the same verdict.  Where the node is NOT certified the licence is
    absent and we fall back to every branch vertex.

    This turns "capped at NODE_CAP" into exhaustive coverage modulo a certified reduction; it is
    a soundness-preserving pruning, not a sample.
    """
    d = cells(col)
    if certified and REDUCE:
        return [vs[0] for vs in d.values() if len(vs) > 1]
    return [v for vs in d.values() if len(vs) > 1 for v in vs]


def walk(n, adj, part_of, log, label, cap=NODE_CAP):
    """Combined traversal + check: certify each reached node, then expand it.

    Returns a stats dict.  The certify-then-expand order is what licences the reduction above.
    """
    root = root_colouring(n, adj)
    seen = {tuple(root): 0}
    frontier = [root]
    order = [root]
    nondiscrete = 0
    fails = []
    unknowns = 0
    within = spans = 0
    truncated = False
    while frontier and not truncated:
        nxt = []
        for col in frontier:
            if is_discrete(col):
                continue
            if not budget_left(f'{label}@node'):
                log(f'  SKIPPED (budget) mid-node: {label}')
                truncated = True
                break
            nondiscrete += 1
            verdict, unk, (w, s) = cells_all_orbits(n, adj, col, part_of)
            unknowns += unk
            within += w
            spans += s
            if verdict is False:
                fails.append(col)
            for v in expansion_vertices(col, verdict is True):
                child = wl(n, adj, individualize(n, col, v))
                key = tuple(child)
                if key in seen:
                    continue
                if len(seen) >= cap:
                    truncated = True
                    break
                seen[key] = seen[tuple(col)] + 1
                order.append(child)
                nxt.append(child)
            if truncated:
                break
        frontier = nxt
    depth = longest_nondiscrete_path(n, adj, seen)
    return {'nodes': len(order), 'nondiscrete': nondiscrete, 'levels': depth,
            'within': within, 'spans': spans, 'unknown': unknowns,
            'trunc': truncated, 'fails': fails}


# ---------------------------------------------------------------- the check
def cells_all_orbits(n, adj, col, part_of):
    """Every cell a single orbit?  Returns (verdict, unknowns, shape_counts).

    verdict: True  = every cell certified a single orbit (positive certificates only)
             False = some cell has a pair with a COMPLETED different-orbit verdict
             None  = no failure found but some pair timed out (UNKNOWN, never a pass)
    shape_counts: how many non-singleton cells lie inside ONE part vs span >= 2 parts --
                  the two cases the planned Lean proof splits on.
    """
    unknowns = 0
    within_part = 0
    spans_parts = 0
    verdict = True
    for c, vs in sorted(cells(col).items()):
        if len(vs) < 2:
            continue
        if len({part_of[v] for v in vs}) == 1:
            within_part += 1
        else:
            spans_parts += 1
        rep = vs[0]
        for u in vs[1:]:
            r = same_orbit(n, adj, col, rep, u)
            if r is True:
                continue
            if r is None:
                unknowns += 1
                if verdict is True:
                    verdict = None
            else:
                return False, unknowns, (within_part, spans_parts)
    return verdict, unknowns, (within_part, spans_parts)


def longest_nondiscrete_path(n, adj, seen):
    """Max number of reached NON-DISCRETE nodes on one path -- the non-vacuity measure."""
    best = 0
    for key, d in seen.items():
        if not is_discrete(list(key)):
            best = max(best, d + 1)
    return best


def run(label, n, adj, part_of, log):
    if not budget_left(label):
        log(f'  SKIPPED (budget): {label}')
        return None
    r = walk(n, adj, part_of, log, label)
    fails = r.pop('fails')
    status = 'FAIL' if fails else ('UNKNOWN' if r['unknown'] else 'pass')
    log(f'  {label:34s} n={n:3d} nodes={r["nodes"]:5d} non-disc={r["nondiscrete"]:5d} '
        f'levels={r["levels"]:2d} cells[in-part={r["within"]:5d} spans={r["spans"]:5d}] '
        f'unknown={r["unknown"]:3d} {"TRUNC " if r["trunc"] else ""}{status}')
    if fails:
        log(f'    ⛔ FAILING COLOURINGS ({len(fails)}), first: {fails[0]}')
    r.update({'label': label, 'n': n, 'fails': len(fails)})
    return r


NMAX = int(os.environ.get('W1_NMAX', '10'))
REDUCE = os.environ.get('W1_REDUCE', '1') != '0'


def profiles(nmax=None):
    """Part-size multisets, >= 2 parts, at least one part of size >= 2, total <= nmax."""
    if nmax is None:
        nmax = NMAX
    out = []

    def rec(cur, total, minsz):
        if len(cur) >= 2 and any(s >= 2 for s in cur):
            out.append(tuple(cur))
        for s in range(minsz, nmax - total + 1):
            if total + s > nmax:
                break
            rec(cur + [s], total + s, s)

    rec([], 0, 1)
    return sorted(set(out), key=lambda p: (sum(p), len(p), p))


def main():
    lines = []

    def log(msg):
        print(msg)
        lines.append(msg)

    log('=' * 96)
    log('W1 step 0 — complete multipartite / cluster: is every cell at every reached node an orbit?')
    log('positive verdicts are verified certificates; None = UNKNOWN, never a pass (doc §8.1)')
    log('=' * 96)

    results = []
    for fam, build in (('multipartite', complete_multipartite), ('cluster', cluster)):
        log(f'\n--- {fam} ---')
        for p in profiles():
            n, adj, part_of = build(list(p))
            r = run(f'{fam}{p}', n, adj, part_of, log)
            if r:
                r['family'] = fam
                results.append(r)

    log('\n' + '=' * 96)
    ok = [r for r in results if r['fails'] == 0 and r['unknown'] == 0]
    bad = [r for r in results if r['fails']]
    unk = [r for r in results if r['unknown'] and not r['fails']]
    deep = [r for r in results if r['levels'] >= 2]
    spans = [r for r in results if r['spans'] > 0]
    log(f'graphs run          : {len(results)}')
    log(f'clean pass          : {len(ok)}')
    log(f'FAILURES            : {len(bad)}   {[r["label"] for r in bad][:12]}')
    log(f'unknown (budget)    : {len(unk)}   {[r["label"] for r in unk][:12]}')
    log(f'NON-VACUITY levels>=2: {len(deep)} of {len(results)}   max levels = '
        f'{max([r["levels"] for r in results], default=0)}')
    log(f'cells spanning >=2 parts seen in: {len(spans)} graphs '
        f'(total {sum(r["spans"] for r in results)} cells)  <- the part-swap case')
    log(f'cells inside one part          : total {sum(r["within"] for r in results)} '
        f'  <- the twin-transposition case')
    log(f'truncated at NODE_CAP={NODE_CAP}: {[r["label"] for r in results if r["trunc"]]}')
    log(f'SKIPPED (logged)    : {SKIPPED}')
    log(f'wall clock          : {time.time() - T0:.1f}s')

    verdict = 'PASS' if (not bad and not unk and deep) else 'NOT A PASS'
    log(f'\nGATE: {verdict}  (needs zero failures, zero unknowns, and non-vacuous descents)')


if __name__ == '__main__':
    main()
