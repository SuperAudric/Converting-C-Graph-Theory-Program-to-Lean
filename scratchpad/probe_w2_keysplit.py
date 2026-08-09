#!/usr/bin/env python3
"""
probe_w2_keysplit.py — W2 STEP (ii) (2026-08-09)

============================================================================================
THE QUESTION
============================================================================================
W2 stage 0 measured that `ResolvableCellAt` fails at the CFI-over-cubic ROOT: both root cells
have the per-cell deepen guard shut, and the certified Aut-orbit partition splits each into 3
blocks.  That is the CONSUME half only.  The published object's node resolver is

    cellNarrowC key S adj χ c  =  ((keepMin key adj χ (cellList χ c)).map (rep V)).dedup

so a cell fires iff the KEY's survivors collapse to one representative under the harvested
generators `V`.  Two facts pin what that needs:

  (F1) the key is EQUIVARIANT (`Force.keyV` is constant on Aut-orbits — Force.lean §"THE CEILING"),
       so `keepMin` is a UNION OF Aut-ORBITS;
  (F2) `rep V` only merges INSIDE orbits of the harvested group `H = <verified V>`, and `H ≤ Aut`
       (every generator is checked by `IsColAut`), so `rep` never merges across Aut-orbits.

  ⟹  the cell fires  ⟹  keepMin is exactly ONE Aut-orbit block, and `H` is transitive on it.

This probe measures the FIRST conjunct, which is the key's half and needs no supply model:

  Q  At the CFI root cells, what are the Aut-orbit block sizes, and does `holKeyFast`'s argmin
     land on exactly one block, on a union of several, or on the whole cell?

Why that is decisive in one direction: `RecordKey.keepMin_pairKey_subset` proves the product key's
argmin sits INSIDE `holKeyFast`'s argmin.  So

  * argmin(holKeyFast) = exactly one Aut-block B  ⟹  argmin(recordKey) = B too (it is a nonempty
    union of Aut-orbits inside B) ⟹ the ONLY remaining question is whether the harvest is
    transitive on B.  **The key half is settled positively.**
  * argmin(holKeyFast) = the whole cell, with >= 2 blocks ⟹ `holKeyFast` ALONE cannot resolve the
    cell; whether `recordKey` can then rests entirely on the `orbKeyG guardSupply` tiebreak, which
    is NOT modelled here (it needs the fold/deck/deck2/match CertPath).  **Undetermined, and the
    doc must say so.**

============================================================================================
SOUNDNESS DISCIPLINE
============================================================================================
* The `holKeyFast` model is `HolKey.holSigFast` transcribed:
      symSame v w  = (adj v w or adj w v) and col v == col w
      symCross v w = (adj v w or adj w v) and col v != col w
      partnerTo x t = the UNIQUE w with sameComp w == sameComp x and crossComp w == crossComp t
      walkOk v t1 t2 = the three cross-components are pairwise distinct
      holMoved v t1 t2 = # of x in v's cross-component that fail to return under the 3 partner hops
      holSig v = [0 if some valid walk has moved-count c else 1 | c <- 0..n]
  ★ Everything depends on `v` only through `crossComp[v]`, so the signature is computed per
    cross-component.  That is a consequence of the definition, not an approximation.
* TWO EXTERNAL VALIDATIONS, both against shipped Lean `#guard`s (`Regression` §18):
      G8 root cell: 8 members, `holKeyFast` keeps ALL 8   (and `recordKey` keeps 2)
      mp7 / t3-style single-orbit controls: an equivariant key may not cut inside an orbit
  If the model disagrees with the first, the model is wrong and every number below is void.
* Aut-orbit blocks are union-find over the generators `Ctx`/`canon` discovers — SOUND but possibly
  incomplete, so blocks are a REFINEMENT of the true orbits (they may be finer, never coarser).
  ⚠ That direction matters: "argmin = one block" could in truth be "argmin = part of one orbit",
  which is impossible by (F1) — so a disagreement would expose incompleteness, and is reported.

    cd /workspace/scratchpad && python3 -u probe_w2_keysplit.py > probe_w2_keysplit.out 2>&1
"""
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import (circ, FANO, MIXED, build_mp, build_cfi_base, cubic, Ctx, canon)
from probe_polyloop import adjlist, refine, target_cell
from probe_selfsep import g8
from probe_offbranch5 import cells_of

LEAFCAP = 200000


# ---------------------------------------------------------------- components

def components(n, rel):
    """Connected components of a symmetric relation given as a neighbour-list."""
    comp = [-1] * n
    c = 0
    for s in range(n):
        if comp[s] != -1:
            continue
        stack, comp[s] = [s], c
        while stack:
            x = stack.pop()
            for y in rel[x]:
                if comp[y] == -1:
                    comp[y] = c
                    stack.append(y)
        c += 1
    return comp, c


# ---------------------------------------------------------------- holKeyFast

def hol_sig_by_crosscomp(n, adj, col, diag=None):
    """`HolKey.holSigFast`, computed once per cross-component.  Returns (crossComp, sig_of_cc)."""
    same_rel = [[] for _ in range(n)]
    cross_rel = [[] for _ in range(n)]
    for v in range(n):
        for w in range(n):
            if v == w:
                continue
            if adj[v][w] or adj[w][v]:
                (same_rel if col[v] == col[w] else cross_rel)[v].append(w)

    sc, _nsc = components(n, same_rel)
    cc, ncc = components(n, cross_rel)

    # partner table: (sameComp, crossComp) -> the unique vertex in both, else None
    buckets = defaultdict(list)
    for v in range(n):
        buckets[(sc[v], cc[v])].append(v)
    P = {k: (vs[0] if len(vs) == 1 else None) for k, vs in buckets.items()}

    members = defaultdict(list)
    for v in range(n):
        members[cc[v]].append(v)

    def moved(cv, c1, c2):
        k = 0
        for x in members[cv]:
            y1 = P.get((sc[x], c1))
            if y1 is None:
                k += 1
                continue
            y2 = P.get((sc[y1], c2))
            if y2 is None:
                k += 1
                continue
            y3 = P.get((sc[y2], cv))
            if y3 is None or y3 != x:
                k += 1
        return k

    sig_of_cc = {}
    for cv in range(ncc):
        hit = set()
        for c1 in range(ncc):
            if c1 == cv:
                continue
            for c2 in range(ncc):
                if c2 == cv or c2 == c1:
                    continue
                hit.add(moved(cv, c1, c2))
        sig_of_cc[cv] = tuple(0 if c in hit else 1 for c in range(n + 1))
    if diag is not None:
        diag.update(colours=len(set(col)), sameComps=max(sc) + 1, crossComps=ncc,
                    trivial=all(all(x == 1 for x in s) for s in sig_of_cc.values()))
    return cc, sig_of_cc


def keep_min(members, keyv):
    """`Force.keepMin` — the argmin under `lexLeList`, which on equal-length lists is plain lex."""
    m = min(keyv[v] for v in members)
    return [v for v in members if keyv[v] == m]


# ---------------------------------------------------------------- Aut blocks

def aut_gens(n, adj, col):
    ctx = Ctx(n, adj, prune=True, leafcap=LEAFCAP)
    canon(ctx, list(col), [], root=True)
    return [g for (g, p) in ctx.gens]


def orbit_classes(n, gens):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for g in gens:
        for v in range(n):
            a, b = f(v), f(g[v])
            if a != b:
                par[a] = b
    return [f(v) for v in range(n)]


# ---------------------------------------------------------------- report

def analyse(name, n, adj, expect_keep=None):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    tid, _ = target_cell(n, col)
    if tid is None:
        print(f"  {name:24s} n={n:<4d}  ROOT DISCRETE — skipped")
        return

    diag = {}
    cc, sig_of_cc = hol_sig_by_crosscomp(n, adj, col, diag)
    keyv = {v: sig_of_cc[cc[v]] for v in range(n)}
    cls = orbit_classes(n, aut_gens(n, adj, col))

    print(f"  {name}  (n={n})")
    why = ("  ⟹ NO VALID WALK EXISTS: `walkOk` needs THREE pairwise-distinct cross-components, "
           "so every holSig is the all-1s vector and holKeyFast is STRUCTURALLY INERT here"
           if diag['crossComps'] < 3 else
           "  ⟹ walks exist; the signature machinery is genuinely exercised")
    print(f"     root: {diag['colours']} colour(s), sameComps={diag['sameComps']}, "
          f"crossComps={diag['crossComps']}, allSigsTrivial={diag['trivial']}")
    print(why)
    for c, mem in sorted(cells_of(n, col).items()):
        blocks = defaultdict(list)
        for v in mem:
            blocks[cls[v]].append(v)
        bsz = sorted((len(b) for b in blocks.values()), reverse=True)

        # (F1) self-check: an equivariant key is constant on Aut-orbits.
        bad = [sorted(b) for b in blocks.values() if len({keyv[v] for v in b}) > 1]

        km = keep_min(mem, keyv)
        kmb = {cls[v] for v in km}
        if len(km) == len(mem):
            verdict = f"argmin = WHOLE CELL ({len(mem)}) over {len(blocks)} block(s)"
            state = "CANNOT FIRE on holKeyFast alone" if len(blocks) > 1 else "cell is ONE block"
        elif len(kmb) == 1:
            verdict = f"argmin = ONE block, size {len(km)}"
            state = "KEY HALF SETTLED — recordKey's argmin is this block too"
        else:
            verdict = f"argmin = {len(km)} vtx across {len(kmb)} blocks"
            state = "partial cut; needs the orbKeyG tiebreak"

        star = ""
        if expect_keep is not None and c == tid:
            ok = (len(km) == expect_keep)
            star = f"   [VALIDATION vs Lean #guard: keeps {len(km)}, expected {expect_keep} — " \
                   f"{'PASS' if ok else 'FAIL'}]"
        tag = " (TARGET)" if c == tid else ""
        print(f"     cell {c}{tag}: |cell|={len(mem):<3d} Aut-blocks={len(blocks)} sizes={bsz}")
        print(f"        holKeyFast: {len(set(keyv[v] for v in mem))} distinct sig(s); {verdict}")
        print(f"        ⟹ {state}{star}")
        if bad:
            print(f"        ⚠⚠ SELF-CHECK FAILED — key not constant on Aut-block(s) {bad}")
    print()


def main():
    print("W2 STEP (ii) — does the KEY isolate a single Aut-orbit block at the CFI root?")
    print("  the cell fires  ⟹  keepMin is exactly ONE Aut-block  ∧  the harvest is transitive on it")
    print("  (keepMin is a union of Aut-orbits because the key is equivariant; `rep` never merges")
    print("   across Aut-orbits because every harvested generator is a verified automorphism)")
    print("  `recordKey`'s argmin ⊆ `holKeyFast`'s argmin (`RecordKey.keepMin_pairKey_subset`).")
    print(f"  ROOT node only.  Aut gens: Ctx/canon, leafcap {LEAFCAP} (sound, maybe incomplete).")
    print()

    print("=== VALIDATION against shipped Lean `#guard`s (Regression §18) ===")
    analyse("G8 cubic non-VT", *g8(), expect_keep=8)

    print("=== THE QUESTION: CFI over a cubic base ===")
    base = cubic(8, seed=8)
    analyse("CFI cubic m=8 pl", *build_cfi_base(base, 8, twist=False))
    analyse("CFI cubic m=8 tw", *build_cfi_base(base, 8, twist=True))

    print("=== CONTROLS ===")
    analyse("mp7 Fano multipede", *build_mp(FANO))
    analyse("MIXED multipede", *build_mp(MIXED))
    analyse("circ(5) multipede", *build_mp(circ(5)))


if __name__ == '__main__':
    main()
