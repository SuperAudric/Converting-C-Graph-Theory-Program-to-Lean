#!/usr/bin/env python3
"""
S0 -- the 2-WL CAO instrument, separating PROPAGATION from SCHURITY at every node.

TWO DISTINCT STATEMENTS, measured independently (this separation is the whole point):

  (P) PROPAGATION -- "every CAO graph is Tinhofer under 2-WL".  At a node with colouring
      chi, let f = the 2-WL closure started from chi.  Then
            fibres(f)  ==  orbits of Aut(adj, chi)
      i.e. CellsAreOrbits survives individualize + 2-WL re-close.   <-- THE TARGET

  (S) SCHURITY -- the strictly STRONGER statement at the same node:
            pair classes of f  ==  ORBITALS of Aut(adj, chi)
      i.e. the closure is a schurian coherent configuration.

(P) is what `docs/chain-descent-cao-propagation.md` Sec 2 targets.  (S) is not.  The
recorded "falsifiers" -- Shrikhande's 2-WL rank 3 vs orbital rank 4 (Sec 14.5b), and the
477 E2 nodes (Sec 12.5b) -- are failures of (S).  If this probe finds nodes where
(S) FAILS and (P) PASSES, then Sec 0.0a's identification of the target with
"the one-point extension of a schurian CC is schurian" is an OVER-identification, and the
literature leg of the 2026-08-01 closure does not bear on (P).

METHOD
  * Clean-room oblivious 2-WL on ordered pairs, full pair colouring retained (not just the
    diagonal).  Pair-level individualization is CaoRound.ext0: mark (a,b) with
    (a==v, b==v).  That is the one-point extension X_v.
  * Automorphisms: probe_dir_flip.all_auts -- exact backtracking IR search, every leaf
    permutation edge-verified.  NEVER probe_orbit_oracle (proven wrong, errs by merging).
  * Descent, not root-only: at each node take the lowest-id non-singleton fibre and recurse
    on every vertex of it, to a node budget.  Root-only is not a pass (standing steer).
  * Posedness is recorded per node: a node is POSED iff individualizing splits some cell,
    i.e. Aut_v is intransitive on a cell.  Where nothing splits, (P) is trivially safe and
    the node is a CONTROL, not evidence.

Usage:  python3 -u probe_2wl_cao.py [--budget=N] [--only=name]
"""
import sys
import time
from collections import defaultdict

sys.path.insert(0, "/workspace/scratchpad")
from probe_dir_flip import all_auts, orbits_of, net, shrikhande, t8_chang, disjoint
from probe_holonomy_split import rook4, cfi

sys.setrecursionlimit(100000)

NODE_BUDGET = 400
AUT_CAP = 400000


# ------------------------------------------------------------------ basics
def to_matrix(n, adjl):
    A = [[0] * n for _ in range(n)]
    for v in range(n):
        for u in adjl[v]:
            A[v][u] = A[u][v] = 1
    return A


def partition_of(col):
    """Canonical partition of a colouring: sorted tuple of sorted blocks."""
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return tuple(sorted(tuple(sorted(b)) for b in d.values()))


def normalize(col):
    """Renumber a colouring to 0..k-1 by first appearance of the sorted class order."""
    rank = {c: i for i, c in enumerate(sorted(set(col)))}
    return [rank[c] for c in col]


# ------------------------------------------------------------------ clean-room 2-WL
def wl2(n, A, vcol=None, mark=None):
    """Oblivious 2-dimensional WL on ORDERED pairs.  Returns the stable pair colouring as a
    flat list of length n*n (index u*n+v).

    vcol -- optional initial vertex colouring, folded into the pair init.
    mark -- optional pair mark, mark(u, v) -> hashable.  Pair-level individualization of a
            vertex w is mark = lambda u, v: (u == w, v == w)  (= CaoRound.ext0).
    """
    if vcol is None:
        vcol = [0] * n
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        un = u * n
        for v in range(n):
            k = (0 if u == v else 1, A[u][v], vcol[u], vcol[v],
                 mark(u, v) if mark else 0)
            r = init.get(k)
            if r is None:
                r = init[k] = len(init)
            col[un + v] = r
    ncls = len(init)
    while True:
        rank = {}
        new = [0] * (n * n)
        for u in range(n):
            un = u * n
            for v in range(n):
                s = sorted((col[un + w], col[w * n + v]) for w in range(n))
                key = (col[un + v], tuple(s))
                r = rank.get(key)
                if r is None:
                    r = rank[key] = len(rank)
                new[un + v] = r
        if len(rank) == ncls:
            return col
        col, ncls = new, len(rank)


def fibres_of(n, pc):
    """The vertex (diagonal) colouring induced by a pair colouring."""
    return normalize([pc[u * n + u] for u in range(n)])


def pair_partition(n, pc):
    d = defaultdict(list)
    for u in range(n):
        for v in range(n):
            d[pc[u * n + v]].append((u, v))
    return tuple(sorted(tuple(sorted(b)) for b in d.values()))


# ------------------------------------------------------------------ the truth
def orbit_partition(n, auts):
    return partition_of(orbits_of(n, auts))


def orbital_partition(n, auts):
    """Orbits of Aut on ORDERED pairs -- the true orbitals."""
    parent = list(range(n * n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a in auts:
        for u in range(n):
            un = u * n
            au = a[u] * n
            for v in range(n):
                ru, rw = find(un + v), find(au + a[v])
                if ru != rw:
                    parent[ru] = rw
    d = defaultdict(list)
    for u in range(n):
        for v in range(n):
            d[find(u * n + v)].append((u, v))
    return tuple(sorted(tuple(sorted(b)) for b in d.values()))


# ------------------------------------------------------------------ per-node verdict
class Blown(Exception):
    pass


def is_cao(n, adjl, chi):
    """Is `chi` CAO -- is every cell a single orbit of Aut(adj, chi)?  (= SchurianAt.)
    Returns (verdict, auts, orbit_partition)."""
    auts = all_auts(n, adjl, chi, cap=AUT_CAP)
    if len(auts) >= AUT_CAP:
        raise Blown("aut cap")
    orb = orbit_partition(n, auts)
    return partition_of(chi) == orb, auts, orb


def child_verdict(n, A, adjl, chi, v):
    """Individualize `v` at the PAIR level (CaoRound.ext0) and take the 2-WL closure.
    Measure at the child:

      (P) fibres(child)     == orbits  of Aut(adj, child chi)     <- PROPAGATION
      (S) pairclasses(child) == orbitals of Aut(adj, child chi)   <- SCHURITY

    The caller guarantees the PARENT `chi` is CAO, so (P) here is exactly the conditional
    'CAO propagates through one individualization + 2-WL re-close'.
    """
    pc = wl2(n, A, vcol=chi, mark=lambda a, b: (a == v, b == v))
    fib = fibres_of(n, pc)
    ok, auts, orb = is_cao(n, adjl, fib)
    return {
        "chi": fib,
        "P": ok,
        "fibres": len(partition_of(fib)),
        "orbits": len(orb),
        "S": pair_partition(n, pc) == orbital_partition(n, auts),
        "pairclasses": len(pair_partition(n, pc)),
        "orbitals": len(orbital_partition(n, auts)),
        "split": len(partition_of(fib)) > len(partition_of(chi)) + 1,
        "discrete": len(partition_of(fib)) == n,
    }


# ------------------------------------------------------------------ the descent
def run(name, n, adjl, budget=NODE_BUDGET):
    A = to_matrix(n, adjl)
    t0 = time.time()
    stats = {
        "nodes": 0, "posed": 0, "controls": 0,
        "P_fail": 0, "S_fail": 0, "S_fail_P_pass": 0,
        "maxdepth": 0, "truncated": False, "blown": 0, "wl_root_not_cao": 0,
        "paid": 0,
    }
    sep_rows = []          # the separating nodes: (S) fails, (P) holds
    Pfail_rows = []

    # ---- the seed.  The hypothesis of propagation is 'this node is CAO', so we seed from
    # the EXACT Aut(adj)-orbit partition, which is CAO by construction (the methodology of
    # probe_cao_cleanroom / probe_cao_2wl).  Seeding from the plain WL root would instead
    # measure the STRONGER unconditional claim '2-WL reaches CAO', which is a statement
    # about base-case refiner strength, not about propagation.  Both are reported.
    try:
        _, root_auts, root_orb = is_cao(n, adjl, [0] * n)
    except Blown:
        print("    ERROR: automorphism budget blown at the root")
        return stats
    seed = [0] * n
    for i, blk in enumerate(root_orb):
        for v in blk:
            seed[v] = i
    seed = normalize(seed)

    wl_root = fibres_of(n, wl2(n, A))
    wl_root_cao = partition_of(wl_root) == root_orb
    if not wl_root_cao:
        stats["wl_root_not_cao"] = 1
    print(f"    seed: |Aut|={len(root_auts):>6}  orbits={len(root_orb):>3}   "
          f"plain 2-WL root fibres={len(partition_of(wl_root)):>3} "
          f"[{'reaches CAO' if wl_root_cao else 'does NOT reach CAO -- hypothesis unmet'}]")

    seen = set()
    stack = [(seed, 0)]
    while stack:
        chi, depth = stack.pop()
        key = partition_of(chi)
        if key in seen:
            continue
        seen.add(key)
        if stats["nodes"] >= budget:
            stats["truncated"] = True
            break
        stats["nodes"] += 1
        stats["maxdepth"] = max(stats["maxdepth"], depth)

        # ---- (S) is measured AT THE NODE: is the closure from chi a schurian CC?
        # (P) is measured ON THE EDGE below.  Every P-passing child becomes a node, so
        # nothing is double counted.
        try:
            _, nauts, _ = is_cao(n, adjl, chi)
        except Blown:
            stats["blown"] += 1
            continue
        npc = wl2(n, A, vcol=chi)
        npair, norbital = pair_partition(n, npc), orbital_partition(n, nauts)
        if npair != norbital:
            # This node is CAO (seed by construction / child by a passed P test) and its CC
            # is NON-schurian ==> propagation and schurity genuinely differ here.
            stats["S_fail"] += 1
            stats["S_fail_P_pass"] += 1
            # ⚠ §7.2's VACUITY TICKET.  A propagation test into a SCHURIAN node cannot fail
            # (schurian ==> fibres are orbits), so it is worthless.  A test is PAID exactly
            # when the node it lands on is non-schurian -- i.e. this node, at depth >= 1.
            if depth >= 1:
                stats["paid"] += 1
            sep_rows.append((depth, len(key), len(key),
                             len(npair), len(norbital), True))

        d = defaultdict(list)
        for v, c in enumerate(chi):
            d[c].append(v)
        nonsing = [c for c in sorted(d) if len(d[c]) > 1]
        if not nonsing:
            continue

        # `chi` is CAO by construction (root) or by the parent's verdict, so every cell is
        # a single orbit ==> all its vertices are conjugate ==> ONE rep per cell suffices,
        # exactly.  One rep from EACH non-singleton cell (not just the lowest-id one).
        node_posed = False
        for cid in nonsing:
            v = min(d[cid])
            try:
                r = child_verdict(n, A, adjl, chi, v)
            except Blown:
                stats["blown"] += 1
                continue
            if r["split"]:
                node_posed = True
            if not r["P"]:
                stats["P_fail"] += 1
                Pfail_rows.append((depth, len(key), r["fibres"], r["orbits"]))
            if r["P"] and not r["discrete"]:
                stack.append((r["chi"], depth + 1))
        stats["posed" if node_posed else "controls"] += 1

    dt = time.time() - t0
    print(f"    nodes={stats['nodes']:>4} maxdepth={stats['maxdepth']} "
          f"posed={stats['posed']} controls={stats['controls']} "
          f"blown={stats['blown']} {'TRUNCATED ' if stats['truncated'] else ''}"
          f"({dt:.1f}s)")
    print(f"    (P) propagation failures : {stats['P_fail']}")
    print(f"    (S) schurity    failures : {stats['S_fail']}")
    print(f"    ** (S) FAILS while (P) HOLDS : {stats['S_fail_P_pass']} **")
    print(f"    PAID propagation tests (landed on a NON-schurian node) : {stats['paid']}")
    for row in sep_rows[:4]:
        print(f"       depth={row[0]}  fibres={row[1]}=orbits={row[2]}  "
              f"pairclasses={row[3]} vs orbitals={row[4]}   split={row[5]}")
    for row in Pfail_rows[:6]:
        print(f"       !! P-FAIL depth={row[0]} parentcells={row[1]} "
              f"fibres={row[2]} orbits={row[3]}")
    return stats


# ------------------------------------------------------------------ witnesses
def k3_plus_c4():
    """K3 disjoint-union C4 -- the cograph witness where 1-WL fails at the ROOT
    (2-regular, one cell) and 2-WL is measured to fix it exactly (wind-down W1 step 0c)."""
    adj = [[] for _ in range(7)]

    def E(a, b):
        adj[a].append(b)
        adj[b].append(a)
    E(0, 1); E(1, 2); E(2, 0)
    E(3, 4); E(4, 5); E(5, 6); E(6, 3)
    return 7, [sorted(a) for a in adj]


def witnesses():
    out = []
    n, a = k3_plus_c4()
    out.append(("K3 + C4  (1-WL root failure; 2-WL fixes it)", n, a))
    n, a = shrikhande()
    out.append(("Shrikhande  (CAO root, non-schurian: 2-WL 3 vs 4 orbitals)", n, a))
    n, a = rook4()
    out.append(("rook 4x4  (the Shrikhande partner, schurian)", n, a))
    n, a = t8_chang([tuple(sorted((i, (i + 1) % 8))) for i in range(8)])
    out.append(("Chang-2  (CAO root, deficient)", n, a))
    n, a = net(4, 'Z')
    out.append(("net(Z4)  (the 1-WL falsifier; deficient at root)", n, a))
    n, a = net(4, 'K')
    out.append(("net(Z2xZ2)", n, a))
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, a = cfi(K4, 4)
    out.append(("CFI(K4) untwisted", n, a))
    n, a = cfi(K4, 4, twist={0})
    out.append(("CFI(K4) twisted", n, a))
    n1, a1 = shrikhande()
    n2, a2 = rook4()
    n, a = disjoint(n1, a1, n2, a2)
    out.append(("Shrikhande + rook4x4  (THE UNION FILTER)", n, a))
    n1, a1 = shrikhande()
    n, a = disjoint(n1, a1, n1, a1)
    out.append(("Shrikhande + Shrikhande  (G + G)", n, a))
    return out


def main():
    budget = NODE_BUDGET
    only = None
    for arg in sys.argv[1:]:
        if arg.startswith("--budget="):
            budget = int(arg.split("=", 1)[1])
        elif arg.startswith("--only="):
            only = arg.split("=", 1)[1]

    print(__doc__.split("Usage:")[0].strip())
    print("=" * 78)
    tot = defaultdict(int)
    for name, n, adjl in witnesses():
        if only and only.lower() not in name.lower():
            continue
        print(f"\n[{name}]  n={n}")
        try:
            s = run(name, n, adjl, budget=budget)
        except Exception as e:                                   # noqa: BLE001
            print(f"    ERROR: {type(e).__name__}: {e}")
            continue
        for k, v in s.items():
            if isinstance(v, int):
                tot[k] += v
    print("\n" + "=" * 78)
    print("TOTALS")
    print(f"  nodes visited              : {tot['nodes']}")
    print(f"  posed nodes                : {tot['posed']}   (controls: {tot['controls']})")
    print(f"  (P) PROPAGATION failures   : {tot['P_fail']}")
    print(f"  (S) SCHURITY    failures   : {tot['S_fail']}")
    print(f"  ** (S) fails, (P) holds    : {tot['S_fail_P_pass']} **")
    print(f"  PAID propagation tests     : {tot['paid']}   (§7.2 ticket: a test landing on a")
    print(f"                                schurian node CANNOT fail, so it is worthless)")
    print(f"  aut-budget blown           : {tot['blown']}")
    print("\nReading: S_fail_P_pass > 0 means propagation and schurity are DIFFERENT")
    print("statements, so the literature leg against schurity does not close propagation.")


if __name__ == "__main__":
    main()
