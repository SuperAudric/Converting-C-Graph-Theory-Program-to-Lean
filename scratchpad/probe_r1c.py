#!/usr/bin/env python3
"""probe_r1c.py — R1c / M1 / §10 item 2: the E1/E2 descent instrumentation over the FULL sharp
Cayley population (2026-07-31).

docs/chain-descent-cao-propagation.md §10 item 2, §12.5a R1c, §12.6 M1.

============================================================================================
WHAT WAS WRONG, AND WHAT THIS FIXES
============================================================================================
`probe_2wl_sring.py` sweeps the whole population (66,888 connection sets over 38 verified groups of
orders 8–32) and reports **729 NON-SCHURIAN S-rings, 0 two-WL counterexamples** — but it only tests
**depth 1** (individualize the identity, one 2-WL closure).

`probe_cao_induction.py` has the instrument that tests the induction the way a proof needs it — E1/E2,
fibre- and full-schurity at **every node of a descent to discreteness** — but its sharp-Cayley
section iterates **8 groups of order 16 only** and `break`s at `hits > 3` per group, so it exercises
**≤ ~24 inputs, not 729** (§10 item 2 records this).

**This file runs the E1/E2 instrument over the full population.**  Nothing is capped silently: every
group sampled rather than enumerated, and every input whose automorphism search blows its budget, is
counted and printed at the end (§9).

E1 — the induction step on the real input class: check at EVERY node, not just depth 1.  A depth-2
     failure *is* a counterexample to the theorem as stated, with an input no plain-graph sweep can
     produce.
E2 — which hypothesis does the work: record fibre-schurity (diagonal classes == Aut_χ-orbits) AND
     full schurity (pair classes == Aut_χ-ORBITALS) at every node.  If full schurity is ever lost
     while fibre-schurity survives, the target cannot be proved via the stronger "extensions preserve
     schurity" — the fibre hypothesis is load-bearing.

============================================================================================
WHY THIS POPULATION, AND WHY ITS ENTRY TICKET IS GENUINELY PAID
============================================================================================
§7.2: a 2-WL failure REQUIRES a non-schurian one-point extension.  For a Cayley graph the root 2-WL
closure is the Schur ring ⟨S⟩, and its basic sets are exactly the diagonal classes of the one-point
extension at the identity; so **"S-ring non-schurian" IS "the one-point extension at e is
non-schurian"** — the ticket, literally.  If the S-ring is schurian the extension recovers the
`Aut_e`-orbits and no failure is possible.

⚠ Contrast with the CFI population measured earlier today (`probe_step2.py --ticket`): there the ROOT
was non-schurian but every one-point extension was schurian, so the ticket was **UNPAID** and the
2-WL result was worthless.  Here the ticket is paid by construction.  Do not conflate the two.

SOUNDNESS: orbits come from `all_isos` (the validated complete enumeration, §8.1) or from
`iso_exists` (early-exit search, §8.1) — never from `probe_orbit_oracle` (§8.2, PROVEN BROKEN).
`iso_exists` returns None on budget exhaustion; only `is True` is treated as same-orbit.

    cd /workspace/scratchpad && python3 -u probe_r1c.py > probe_r1c.out 2>&1     # run detached (§9)
    python3 -u probe_r1c.py --smoke                                             # one group, timing
"""

import random
import sys
import time
from collections import defaultdict

from probe_cao_cleanroom import wl, individualize, all_isos, orbits
from probe_cao_vtcover import iso_exists
from probe_cao_induction import descend
from probe_2wl_sring import GROUPS, sring, cayley_adj, connected, CAP_SETS

T0 = time.time()
SKIPPED = []
SKIP_N = 0


# ---------------------------------------------------------------- population enumeration
def inverse_classes(mul):
    n = len(mul)
    inv = [next(y for y in range(n) if mul[x][y] == 0) for x in range(n)]
    seen, classes = set(), []
    for x in range(1, n):
        if x in seen:
            continue
        c = {x, inv[x]}
        seen |= c
        classes.append(sorted(c))
    return inv, classes


def sets_for(name, mul):
    """Every inverse-closed connection set, or a logged random sample when there are too many."""
    inv, classes = inverse_classes(mul)
    nsets = 2 ** len(classes)
    if nsets <= CAP_SETS:
        return inv, [frozenset(e for i, c in enumerate(classes) if mask >> i & 1 for e in c)
                     for mask in range(1, nsets)]
    rnd = random.Random(12345)
    out, seen = [], set()
    while len(out) < CAP_SETS:
        mask = rnd.randrange(1, nsets)
        S = frozenset(e for i, c in enumerate(classes) if mask >> i & 1 for e in c)
        if S not in seen:
            seen.add(S)
            out.append(S)
    SKIPPED.append(f"{name}: {len(classes)} inverse-classes, {nsets} sets, SAMPLED {CAP_SETS}")
    return inv, out


def is_nonschurian(nn, adj, basic_sets, col1):
    """Stage 2 (from `probe_2wl_sring.main`): is some basic set NOT one `Aut_e`-orbit?
    Early-exit — the common case is schurian and exits fast."""
    for cell in [c for c in basic_sets if len(c) > 1]:
        r = cell[0]
        for v in cell[1:]:
            if iso_exists(nn, adj, individualize(nn, col1, v),
                          individualize(nn, col1, r)) is not True:
                return True
    return False


# ---------------------------------------------------------------- the E1/E2 run on one input
def descend_budgeted(n, adj, auts, col, depth, stats, maxdepth, node_budget):
    """`probe_cao_induction.descend` with a NODE BUDGET.

    ⚠ The unbudgeted version does not terminate in useful time on the order-24/32 groups: it
    recurses on one rep of EVERY cell, so the tree branches multiplicatively and a single input
    reached tens of thousands of nodes (the first attempt at this sweep died on a 2 h wall at ~300
    of the sharp inputs, with no summary — EXIT 124).  Truncation is recorded per input and counted
    in the summary; it is never silent (§9).
    """
    from probe_cao_induction import twowl_pairs, orbital_partition, same_partition, stab
    if stats["nodes"] >= node_budget:
        stats["truncated"] = True
        return
    H = stab(auts, col, n)
    p2 = twowl_pairs(n, adj, col)
    diag = [p2[v * n + v] for v in range(n)]
    orb = orbits(n, H)
    fibre_ok = same_partition(diag, orb)
    full_ok = same_partition(p2, orbital_partition(n, H))
    stats["nodes"] += 1
    stats["depth"] = max(stats["depth"], depth)
    if not fibre_ok:
        stats["fibre_fail"].append((depth, len(H)))
    if not full_ok:
        stats["full_fail"].append((depth, len(H)))
    if fibre_ok and not full_ok:
        stats["fibre_ok_full_fail"] += 1
    d = defaultdict(list)
    for v, c in enumerate(diag):
        d[c].append(v)
    big = [c for c in d.values() if len(c) > 1]
    if not big or depth >= maxdepth:
        return
    for cell in big:                       # CAO here ⟹ one rep per cell suffices
        descend_budgeted(n, adj, auts, individualize(n, diag, cell[0]), depth + 1, stats,
                         maxdepth, node_budget)


def e1e2(nn, adj, autcap, maxdepth=12, node_budget=400):
    """Full descent instrumentation.  Returns None if the automorphism budget blows."""
    try:
        A = all_isos(nn, adj, wl(nn, adj, [0] * nn), wl(nn, adj, [0] * nn), limit=autcap)
    except RuntimeError:
        return None
    orb0 = orbits(nn, A)
    m = {}
    oc = [m.setdefault(orb0[v], len(m)) for v in range(nn)]      # the CAO start
    stats = {"nodes": 0, "depth": 0, "fibre_fail": [], "full_fail": [],
             "fibre_ok_full_fail": 0, "truncated": False}
    descend_budgeted(nn, adj, A, oc, 0, stats, maxdepth, node_budget)
    stats["aut"] = len(A)
    return stats


# ---------------------------------------------------------------- driver
def sweep(groups, autcap=2_000_000, verbose_every=50, deadline=None):
    tot = nondisc = sharp = done = blown = trunc = 0
    nodes = 0
    maxdepth = 0
    fibre_fail = []
    full_fail = []
    fibre_ok_full_fail = 0
    for name, mul in groups:
        if deadline and time.time() > deadline:
            SKIPPED.append(f"GROUP NOT REACHED (wall deadline): {name} (order {len(mul)})")
            continue
        n = len(mul)
        inv, sets = sets_for(name, mul)
        if SKIP_N:
            # ⚠ PROCESS TRAP (cost a whole run, 2026-07-31): `sets_for` samples with a FIXED seed
            # (random.Random(12345)), so a restarted run re-covers the SAME PREFIX and adds no
            # coverage at all.  To extend a group that was cut off after k sets, resume at k.
            sets = sets[SKIP_N:]
            SKIPPED.append(f"{name}: resumed at offset {SKIP_N} (earlier sets covered by a prior run)")
        gsharp = 0
        gt0 = time.time()
        gdone = 0
        for S in sets:
            if deadline and time.time() > deadline:
                SKIPPED.append(f"{name} (order {len(mul)}): wall deadline hit after "
                               f"{gdone}/{len(sets)} connection sets")
                break
            gdone += 1
            tot += 1
            if not connected(mul, S):
                continue
            p = sring(mul, inv, S)
            szs = defaultdict(int)
            for c in p:
                szs[c] += 1
            if max(szs.values()) == 1:
                continue                                   # discrete S-ring => 2-WL discrete
            nondisc += 1
            nn, adj = cayley_adj(mul, S)
            root = wl(nn, adj, [0] * nn)
            col1 = individualize(nn, root, 0)
            bs = defaultdict(list)
            for x, c in enumerate(p):
                bs[c].append(x)
            if not is_nonschurian(nn, adj, list(bs.values()), col1):
                continue                                   # ticket unpaid => cannot fail
            sharp += 1
            gsharp += 1
            st = e1e2(nn, adj, autcap)
            if st is None:
                blown += 1
                SKIPPED.append(f"{name} n={nn} |S|={len(S)} S={sorted(S)}: Aut budget blown")
                continue
            done += 1
            nodes += st["nodes"]
            trunc += 1 if st["truncated"] else 0
            maxdepth = max(maxdepth, st["depth"])
            fibre_ok_full_fail += st["fibre_ok_full_fail"]
            if st["fibre_fail"]:
                fibre_fail.append((name, sorted(S), st["fibre_fail"][:3]))
                print(f"  ⛔⛔ FIBRE-SCHURITY FAILS — 2-WL CAO COUNTEREXAMPLE: {name} "
                      f"n={nn} S={sorted(S)} at {st['fibre_fail'][:3]}")
            if st["full_fail"]:
                full_fail.append((name, sorted(S), st["full_fail"][:3]))
            if done % verbose_every == 0:
                print(f"  ... {done} sharp inputs instrumented, {nodes} nodes, "
                      f"{time.time() - T0:.0f}s")
        print(f"  {name:12s} (order {len(mul):2d}): {gdone}/{len(sets)} sets, "
              f"{gsharp} sharp, {time.time() - gt0:.0f}s"
              + ("   ⚠ INCOMPLETE (deadline)" if gdone < len(sets) else ""))
    return dict(tot=tot, nondisc=nondisc, sharp=sharp, done=done, blown=blown, nodes=nodes,
                maxdepth=maxdepth, fibre_fail=fibre_fail, full_fail=full_fail,
                fibre_ok_full_fail=fibre_ok_full_fail, trunc=trunc)


if __name__ == "__main__":
    print(__doc__)
    smoke = "--smoke" in sys.argv
    groups = [g for g in GROUPS if len(g[1]) == 16][:2] if smoke else GROUPS
    pick = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--groups=")), None)
    if pick:                      # e.g. --groups=Z4^2xZ2,Z8xZ4,Z16xZ2  (finish an unreached tail)
        want = set(pick.split(","))
        groups = [g for g in GROUPS if g[0] in want]
        missing = want - {g[0] for g in groups}
        if missing:
            print(f"⚠ unknown group names ignored: {sorted(missing)}")
    WALL = int(next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--wall=")), 55 * 60))
    SKIP_N = int(next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--skip=")), 0))
    print(f"{'SMOKE: ' if smoke else ''}groups = {len(groups)}, CAP_SETS = {CAP_SETS}, "
          f"node budget/input = 400, wall deadline = {WALL}s")
    r = sweep(groups, deadline=None if smoke else T0 + WALL)
    print("\n" + "=" * 92)
    print(f"connection sets tried        : {r['tot']}")
    print(f"S-ring NON-discrete          : {r['nondisc']}")
    print(f"S-ring NON-SCHURIAN (= §7.2's entry ticket, PAID) : {r['sharp']}")
    print(f"  of those, E1/E2 instrumented : {r['done']}   (Aut budget blown: {r['blown']})")
    print(f"descent nodes visited        : {r['nodes']}   max depth {r['maxdepth']}")
    print(f"  inputs whose descent hit the 400-node budget (partial coverage): {r['trunc']}")
    print(f"\n★ E1 — FIBRE-schurity failures at ANY node (= a 2-WL CAO counterexample): "
          f"{len(r['fibre_fail'])}")
    for x in r['fibre_fail'][:20]:
        print(f"    {x}")
    print(f"★ E2 — FULL-schurity failures: {len(r['full_fail'])};  "
          f"nodes where FIBRE holds but FULL fails: {r['fibre_ok_full_fail']}")
    print("    (if the second number is > 0, the target cannot be proved via the stronger"
          " 'extensions preserve schurity' — the fibre hypothesis is load-bearing)")
    if SKIPPED:
        print(f"\n⚠ SKIPPED / SAMPLED — {len(SKIPPED)} items (a silent cap reads as full coverage, §9):")
        for s in SKIPPED[:40]:
            print(f"    - {s}")
        if len(SKIPPED) > 40:
            print(f"    ... and {len(SKIPPED) - 40} more")
    else:
        print("\nno items skipped: full coverage")
    print(f"wall: {time.time() - T0:.1f}s")
