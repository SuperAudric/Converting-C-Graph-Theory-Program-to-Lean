#!/usr/bin/env python3
"""
probe_w2_linked.py — the STEP-0 probe of `docs/chain-descent-force-refinement-channel.md` §6
(2026-08-10)

============================================================================================
THE QUESTION
============================================================================================
Method 2 proposes the order-free, gauge-blind relation

      Linked u v  :=  e_u + e_v  ∈  R,      R := rowspace(H)

with H the built extraction `RigidRefine.extractOf rowAdj witChi`, i.e. **H = the F2 rows of
the adjacency matrix**.  §6 asks: does the refinement `Linked` induces SPLIT the mixed cells?

★ THE IDENTITY THAT MAKES IT CHEAP (and that predicts the answer).  For a symmetric H,
rowspace(H) = ker(H)^⊥, so

      Linked u v   ⟺   <e_u + e_v, x> = 0  for every x ∈ ker H
                   ⟺   x_u = x_v  for every x ∈ ker H.

⟹ `Linked` is EXACTLY "the kernel cannot tell u from v", its classes are the fibres of the
per-vertex kernel signature  sig(v) := (x¹_v, …, x^k_v)  over any kernel basis, and

      dim ker H = 0  ⟹  R is everything  ⟹  Linked is the TOTAL relation  ⟹  one class,
      no split, VACUOUS.

That is a prediction, not a result — this probe measures it.  `sig` is also exactly the `read`
method 1 would refine by (it is manifestly equivariant: ker transports under relabelling).

============================================================================================
WHAT IS COMPUTED
============================================================================================
* `ker_f2(adj)` — exact F2 nullspace basis by Gaussian elimination.  `dim ker` is reported.
* `sig(v)` — the kernel signature; `Linked`-classes are its fibres.  Cross-checked on the
  first witness against DIRECT membership `e_u + e_v ∈ rowspace(adj)` (independent Gaussian
  elimination) so the identity above is verified, not assumed.
* per non-singleton 1-WL cell: how many `Linked`-classes it meets  (1 = no split).
* the METHOD-1 measurement: refine χ by `sig`, run 1-WL to a fixpoint, report the resulting
  cell structure — this is what wiring the read in as a REFINER would actually do.
* SOUNDNESS (CFI witnesses): every verified gauge automorphism must PRESERVE the `Linked`
  partition.  A violation is a bug in the probe, not a discovery.  (Equivariance means an
  invariant is constant on Aut-orbits — the same built-in check that validated
  `probe_w2_keysplit`.)

    cd /workspace/scratchpad && python3 -u probe_w2_linked.py > probe_w2_linked.out 2>&1
"""
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import build_cfi_base, cubic, circ, FANO, MIXED, rand_incidence, build_mp
from probe_polyloop import adjlist, refine, target_cell
from probe_selfsep import g8
from probe_offbranch5 import cells_of
from probe_w2_linear import cfi_layout, cycle_space, gauge_perm, is_aut, orbits_of, aut_gens
from probe_w2_asymbase import FRUCHT, base_auts, wl_classes


# ---------------------------------------------------------------- F2 linear algebra

def ker_f2(n, rows):
    """Nullspace basis of the matrix whose rows are `rows` (each an int bitmask over n cols)."""
    piv = {}           # pivot column -> reduced row
    for r in rows:
        cur = r
        while cur:
            c = cur.bit_length() - 1
            if c in piv:
                cur ^= piv[c]
            else:
                piv[c] = cur
                break
    # back-reduce to RREF: each pivot row carries its own pivot bit and no other pivot bit
    for c in sorted(piv):
        for c2 in sorted(piv):
            if c2 > c and (piv[c2] >> c) & 1:
                piv[c2] ^= piv[c]
    pivots = set(piv)
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for f in free:
        # x_f = 1; each pivot row  x_c + Σ_{free j} row[j]·x_j = 0  ⟹  x_c = row[f]
        x = 1 << f
        for c in pivots:
            if (piv[c] >> f) & 1:
                x |= (1 << c)
        basis.append(x)
    # verify
    for x in basis:
        for r in rows:
            assert bin(r & x).count('1') % 2 == 0, "ker_f2: not in the nullspace"
    return basis


def rowspace_basis_f2(rows):
    piv = {}
    for r in rows:
        cur = r
        while cur:
            c = cur.bit_length() - 1
            if c in piv:
                cur ^= piv[c]
            else:
                piv[c] = cur
                break
    return piv


def in_span(piv, v):
    cur = v
    while cur:
        c = cur.bit_length() - 1
        if c not in piv:
            return False
        cur ^= piv[c]
    return True


def adj_rows(n, adj):
    return [sum((1 << j) for j in range(n) if adj[i][j]) for i in range(n)]


# ---------------------------------------------------------------- Linked

def linked_sig(n, adj):
    """Per-vertex kernel signature.  Fibres = the `Linked` classes.  Returns (sig, dimker)."""
    rows = adj_rows(n, adj)
    basis = ker_f2(n, rows)
    sig = [tuple((x >> v) & 1 for x in basis) for v in range(n)]
    return sig, len(basis)


def check_identity(n, adj, sig):
    """Verify  Linked u v  ⟺  sig u == sig v  against DIRECT rowspace membership."""
    piv = rowspace_basis_f2(adj_rows(n, adj))
    for u in range(n):
        for v in range(u + 1, n):
            direct = in_span(piv, (1 << u) | (1 << v))
            assert direct == (sig[u] == sig[v]), f"identity FAILS at ({u},{v})"
    return True


def refine_by(n, adjl, col, sig):
    """Pair χ with the read, then run 1-WL to a fixpoint — method 1's actual effect."""
    ids = {s: i for i, s in enumerate(sorted(set(sig)))}
    seeded = [0] * n
    keys = sorted({(col[v], ids[sig[v]]) for v in range(n)})
    kid = {k: i for i, k in enumerate(keys)}
    for v in range(n):
        seeded[v] = kid[(col[v], ids[sig[v]])]
    return refine(n, adjl, seeded)


# ---------------------------------------------------------------- report

def report(name, n, adj, gperms=None, verify_identity=False):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    sig, dimker = linked_sig(n, adj)
    nclasses = len(set(sig))

    print(f"  {name}   n={n}   dim ker_F2(adj) = {dimker}   Linked-classes = {nclasses}")
    if verify_identity:
        check_identity(n, adj, sig)
        print("     ✔ identity verified: Linked u v ⟺ sig u = sig v ⟺ e_u+e_v ∈ rowspace(adj)")

    sizes = defaultdict(int)
    for s in set(sig):
        sizes[sum(1 for v in range(n) if sig[v] == s)] += 1
    print(f"     Linked class-size profile: "
          f"{ {k: v for k, v in sorted(sizes.items())} }   "
          f"⟹ the only equivariant read a relation offers (class size) is "
          f"{'CONSTANT ⟹ VACUOUS' if len(sizes) == 1 else 'non-constant'}")

    if gperms is not None:
        # (a) RELATION-level equivariance — must hold (Linked is defined from adj alone).
        relbad = sum(1 for p in gperms for u in range(n) for v in range(u + 1, n)
                     if (sig[u] == sig[v]) != (sig[p[u]] == sig[p[v]]))
        # (b) READ-level equivariance — does the kernel SIGNATURE transport?  This is the
        #     illegal step: the basis is chosen by pivot order, so `sig` is not a σ-invariant.
        readbad = sum(1 for p in gperms for v in range(n) if sig[v] != sig[p[v]])
        print(f"     soundness vs {len(gperms)} edge-verified gauge automorphisms:")
        print(f"        (a) the RELATION `Linked` transports: "
              f"{'✔ 0 violations' if relbad == 0 else f'⛔ {relbad} — PROBE BUG'}")
        print(f"        (b) the kernel-SIGNATURE read transports: "
              f"{'✔ 0 violations' if readbad == 0 else f'⛔ {readbad} VIOLATIONS ⟹ `sig` is NOT `ReadEquivariant` — a basis/pivot order was chosen'}")

    cells = {c: mem for c, mem in sorted(cells_of(n, col).items()) if len(mem) >= 2}
    split = same = 0
    for c, mem in cells.items():
        k = len({sig[v] for v in mem})
        if k > 1:
            split += 1
            print(f"     cell {c} |cell|={len(mem)}  ⟹ ★ SPLIT into {k} Linked-classes")
        else:
            same += 1
    print(f"     1-WL non-singleton cells: {len(cells)}   ★ split by Linked: {split}   "
          f"untouched: {same}")

    # METHOD 1, LEGAL read #1: class size (the cheapest σ-invariant of an equivalence class).
    csize = {v: sum(1 for u in range(n) if sig[u] == sig[v]) for v in range(n)}
    col_legal = refine_by(n, adjl, col, [(csize[v],) for v in range(n)])
    cells_legal = {c: m for c, m in cells_of(n, col_legal).items() if len(m) >= 2}
    # METHOD 1, LEGAL read #2 (the STEELMAN): run 1-WL on the 2-relation (adj, Linked) — i.e.
    # use `Linked` as an extra edge colour.  Strictly stronger than class size, still order-free.
    linkl = [[u for u in range(n) if u != v and sig[u] == sig[v]] for v in range(n)]
    c2 = list(col)
    for _ in range(n + 2):
        sigs = [(c2[v], tuple(sorted(c2[u] for u in adjl[v])),
                 tuple(sorted(c2[u] for u in linkl[v]))) for v in range(n)]
        ids = {s: i for i, s in enumerate(sorted(set(sigs)))}
        nxt = [ids[sigs[v]] for v in range(n)]
        if len(set(nxt)) == len(set(c2)):
            break
        c2 = nxt
    cells_2rel = {c: m for c, m in cells_of(n, c2).items() if len(m) >= 2}
    # METHOD 1, with the ILLEGAL read: the basis-dependent signature (shown for contrast).
    col_ill = refine_by(n, adjl, col, sig)
    cells_ill = {c: m for c, m in cells_of(n, col_ill).items() if len(m) >= 2}
    before = sorted((len(m) for m in cells.values()), reverse=True)
    print(f"     METHOD 1, refine-then-1-WL-to-fixpoint.  cells before {before}")
    print(f"        ✔ LEGAL read (class size, equivariant): non-singleton cells "
          f"{len(cells)} → {len(cells_legal)}   sizes {sorted((len(m) for m in cells_legal.values()), reverse=True)}")
    print(f"        ✔ LEGAL STEELMAN (1-WL on the 2-relation adj ∪ Linked): "
          f"{len(cells)} → {len(cells_2rel)}   sizes {sorted((len(m) for m in cells_2rel.values()), reverse=True)}")
    print(f"        ⛔ ILLEGAL read (kernel signature, basis-dependent): "
          f"{len(cells)} → {len(cells_ill)}   sizes {sorted((len(m) for m in cells_ill.values()), reverse=True)}"
          f"   — this is what a pivot order buys, and it is not available")
    print()
    return split, len(cells)


def cfi(name, base_edges, m, twist=False, verify_identity=False):
    base_edges = [(min(a, b), max(a, b)) for (a, b) in base_edges]
    n, adj = build_cfi_base(base_edges, m, twist=twist)
    wire, gadget, _ = cfi_layout(base_edges, m)
    K, beta = cycle_space(base_edges, m)
    gperms = []
    for F in K:
        p = gauge_perm(F, base_edges, m, wire, gadget, n)
        assert is_aut(n, adj, p), "gauge element is not an automorphism — encoding mismatch"
        gperms.append(p)
    bwl = wl_classes(m, base_edges)
    bdisc = len(set(bwl)) == m
    tag = (f"[base m={m} |E|={len(base_edges)} |Aut(base)|={len(base_auts(m, base_edges))} "
           f"1-WL {'DISCRETE' if bdisc else 'COARSE'}]")
    return report(f"{name} {tag}", n, adj, gperms=gperms, verify_identity=verify_identity)


def main():
    print("=" * 92)
    print("probe_w2_linked.py — STEP 0 of the force-refinement-channel doc (§6)")
    print("  Linked u v := e_u + e_v ∈ rowspace_F2(adj)   [the BUILT extraction: extractOf rowAdj witChi]")
    print("=" * 92)
    print()

    print("--- §6 row 2: the SOUNDNESS control.  CFI over K4 — Aut merges the blocks, so an")
    print("    equivariant invariant MUST NOT separate them.  A split here means a bug.")
    cfi("CFI(K4)", [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 4, verify_identity=True)

    print("--- §6 row 1: CFI over Frucht (asymmetric base, 1-WL coarse).  12 Aut-blocks,")
    print("    each already a single gauge-orbit — force needs only to SPLIT them.")
    cfi("CFI(Frucht)", FRUCHT, 12)

    print("--- the item-3a witness, for continuity")
    cfi("CFI(cubic m=8 seed=8)", cubic(8, 8), 8)
    cfi("CFI(cubic m=8 seed=8) twisted", cubic(8, 8), 8, twist=True)

    print("--- §6 row 3: multipedes (the rigid family is where the headline claim lives)")
    for nm, A in [("mp7 Fano", FANO), ("MIXED", MIXED), ("circ(5)", circ(5)),
                  ("rand V=6 W=5", rand_incidence(6, 5, 3, 1))]:
        n, adj = build_mp(A)
        report(f"multipede {nm}", n, adj)

    print("--- controls: G8 (force's only measured firing witness) and small graphs")
    n, adj = g8()
    report("G8 cubic non-VT", n, adj)


if __name__ == '__main__':
    main()
