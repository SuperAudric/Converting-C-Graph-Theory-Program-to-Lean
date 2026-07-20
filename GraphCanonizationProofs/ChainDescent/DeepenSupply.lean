import ChainDescent.Deck2

/-!
# `C3b` — `deepenSupply` : anchor-deepening + replay (the footprint-matching constructor)

## Why the propagation supplies are not enough (remaining-work §1C C3; `PerformanceTest` §13/§16)

`deckSupply` and `deck2Supply` both work by **propagation**: seed one (or two) vertices and chase
forced consequences. On the C3 witness `mp7` (the Fano multipede) that is defeated *in principle* —
the incidence structure has girth 6, so a seed forces exactly one vertex and nothing chains, at any
number of seeds. `kernelSupply` then certifies the whole F₂ gauge, but the gauge is not all there
is: the **base** symmetry (the `Z₇` translation of the Fano plane, and in fact all of `PGL(3,2)`)
survives, and no gauge-shaped or propagation-shaped constructor reaches it.

## The mechanism (ported from the C# `ChainDescent.cs` `HarvestTwists`, which is measured to solve
`mp7` end-to-end on a SINGLE path: 4 nodes, 1 leaf, |residual| = 1344 = 8 × 168)

The trick is to stop propagating and instead **replay a deepening and compare refinement
footprints**:

1. **`deepen` (`DeepenAnchor`)** — individualize the anchor `r₁` of the branch cell and refine; then
   repeatedly individualize the lowest-id **non-singleton** sub-cell of the *footprint* (the diff
   against the node colouring, which stays fixed as the parent) until the footprint is
   all-singletons, recording the sequence of chosen cell ids. One sub-cell, one vertex per level —
   a single path, never a branch over representatives.
2. **`replay` (`ReplayDeepening`)** — for each other representative `rⱼ`, individualize `rⱼ` and
   follow the SAME recorded id sequence. If `rⱼ` cannot follow it, it is structurally unlike `r₁`
   and yields no candidate (sound: the representatives simply stay separate).
3. **`twist` (`TwistConstruction`)** — on the coupled component (the parent cells that split), match
   `r₁`'s colour-`c` vertex to `rⱼ`'s colour-`c` vertex, identity off it. 1-WL assigns identical
   canonical colours to corresponding vertices of isomorphic branches, so when the footprint is
   all-singletons this match is a forced bijection. A non-singleton sub-cell is
   refinement-indistinguishable, so no iso-invariant match exists — those are rejected outright.
4. **verify** — `permOf` gates bijectivity and `Consume.verified` re-checks `IsColAut` as always.
   The construction only *proposes*; verification disposes. Junk costs firing, never ①.

## ⚠⚠ The ①c story — A SINGLE ANCHOR IS **MEASURED FALSE**. ALL ANCHORS ARE REQUIRED.

The anchor is a **within-cell pick** and each deepening level breaks ties by vertex index, so the
supply runs a *different computation* under relabelling. `SameOrbits` (hence ①c) needs the emitted
**orbit relation** to be labelling-independent, and with ONE anchor it is not:

> **⛔ THE `G8` FALSIFIER (2026-07-20 — do not re-introduce a single-anchor variant).** Scrambling
> `G8` by five relabellings, the single-anchor supply gives branch-cell orbit profiles
> `[2,2,2,2,4,4,4,4]` under two of them and `[1,1,2,2,2,2,2,2]` under the other two — genuinely
> different partitions (one has fixed points, the other orbits of size 4). ⟹ ①c FALSE, and
> `SameOrbits` against **any** equivariant reference is therefore false too, since an equivariant
> reference has a labelling-independent orbit relation by definition. `mp7` cannot detect this: it
> fires *totally* there (whole cell = one orbit), so its profile is `[28]` whatever path is taken —
> **the falsifier must be a PARTIALLY-firing witness.**

Quantifying over **all anchors** repairs it, measured: the same five `G8` labellings then all give
`[2,2,2,2,4,4,4,4]`, and the union fires strictly more (it is the richer partition). That is why
`deepenGens` below loops over every anchor rather than the head of `Descend.branches`, at a cost of
`|cell|` extra deepenings.

**The residual ①c obligation (tranche 2, OPEN).** All-anchors removes the *anchor* choice but not
the **per-deepening-level vertex choice** (`w :: _` — the lowest-index member of the chosen
sub-cell). No falsifier is known for that layer, but none is proven absent either, so the ① route is
NOT yet settled. The two candidate routes: (a) show the emitted orbit relation is invariant under
the per-level choice, giving `SameOrbits` against the all-anchors-all-paths reference; or (b) find a
canonical tie-break. **Do not assume (a) — it is exactly the shape the `G8` falsifier just broke at
the anchor layer.**

## Performance notes (measured — these are not micro-optimisations)

A first prototype took **> 1 hour** on `mp7`; the version below takes **~3 minutes** for the whole
measurement file. Three faults, all instances of the project's standing traps:
· the per-representative refinement was recomputed once per (anchor, rⱼ) pair — `|cell|²` warm
  refinements where `|cell|` suffice;
· ★ the twist was returned as a **closure**, so each of `IsColAut`'s `~2n²` applications re-ran a
  `List.contains` + `List.find?` at `O(n)` — cured by materialising it as a `Vector` (**trap #1**:
  data, not functions);
· `coupled` is `O(n³)` and was computed twice per level and again per pair — it is now computed
  once per level and once per anchor and threaded.

## Scope, honestly

This file is **tranche 1**: the executable object and its measured firing. The ① proof stack (the
`SameOrbits` reduction above) is **tranche 2 and is NOT built**, so this supply is deliberately
**not** in `Publication.canonForm?`'s record object yet — exactly how `kernelSupply` was staged.
Measured on `mp7` (`PerformanceTest` §16): branch cell 28, and the gadget cell (28) *and* the foot
cell (14) each collapse to a **single orbit** — the standing `Z₇`/`PGL(3,2)` base symmetry that
`kernelSupply` honestly left, now certified. (The single-anchor variant gave 27 generators there;
the all-anchors design required by the `G8` falsifier gives correspondingly more.)
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (Supply gens verified IsColAut)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. Footprints -/

/-- Members of the child-colour class of `v`. -/
def classOf (χ : Colouring n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun u => χ u == χ v)

/-- **The coupled component**: the vertices whose PARENT cell split (≥ 2 child colours inside it).
`O(n³)` — compute it once per level and thread the result (see the performance notes). -/
def coupled (χp χc : Colouring n) : List (Fin n) :=
  (List.finRange n).filter (fun v =>
    (((List.finRange n).filter (fun u => χp u == χp v)).map χc).dedup.length > 1)

/-- The forced-matching gate: every sub-cell of the coupled component is a singleton. -/
def allSingletonsK (K : List (Fin n)) (χc : Colouring n) : Bool :=
  K.all (fun v => (classOf χc v).length == 1)

/-- The lowest child-colour id among the NON-singleton sub-cells of the coupled component. -/
def chooseIdK (K : List (Fin n)) (χc : Colouring n) : Option Nat :=
  (K.filter (fun v => (classOf χc v).length ≥ 2)).foldl
    (fun acc v => match acc with
      | none => some (χc v)
      | some m => some (min m (χc v))) none

/-! ## 2. Deepen and replay -/

/-- One individualize + warm-refine step, materialised (`ColData`, never a stored `Colouring`). -/
def step (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Refine.ColData n :=
  Refine.warmRefineVec adj (Descend.indivOne χ v)

/-- **`DeepenAnchor`.** Descend the lowest-id non-singleton sub-cell until the footprint is
all-singletons, recording the chosen cell ids. The parent colouring stays FIXED at the node
colouring. `none` when nothing splits or the fuel (`n` levels) runs out. -/
def deepen (adj : AdjMatrix n) (χp : Colouring n) :
    Nat → Refine.ColData n → List Nat → Option (Refine.ColData n × List Nat)
  | 0, _, _ => none
  | fuel + 1, cur, seq =>
      let χc := cur.col
      let K := coupled χp χc
      if K.isEmpty then none
      else match chooseIdK K χc with
        | none => some (cur, seq.reverse)
        | some cid =>
            match (List.finRange n).filter (fun v => χc v == cid) with
            | [] => none
            | w :: _ => deepen adj χp fuel (step adj χc w) (cid :: seq)

/-- **`ReplayDeepening`.** Follow the anchor's recorded id sequence from another representative;
`none` if the sequence cannot be followed. -/
def replay (adj : AdjMatrix n) : List Nat → Refine.ColData n → Option (Refine.ColData n)
  | [], cur => some cur
  | cid :: rest, cur =>
      let χc := cur.col
      let mem := (List.finRange n).filter (fun v => χc v == cid)
      if mem.length < 2 then none
      else match mem with
        | [] => none
        | w :: _ => replay adj rest (step adj χc w)

/-! ## 3. The supply -/

/-- **★ THE DEEPENING SUPPLY.** EVERY anchor of the branch cell (the `G8` falsifier above forbids a
single anchor); every value not depending on `rⱼ` is hoisted, and the twist is materialised as a
`Vector` (trap #1). Recognition is UNTRUSTED —
`Consume.verified` re-checks every emitted generator, so junk costs firing and never ①. Cost billed
flat at `n⁶`: `≤ n` representatives × `≤ n` deepening levels × a warm refinement (`≤ n³`), plus
`≤ n` verifications at `n²` — generous, honest. -/
def deepenGens (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  let cell := Descend.branches χ
  -- the first individualize+refine of each representative is anchor-independent: compute the
  -- `|cell|` of them ONCE rather than `|cell|²` times (trap #2 — recomputation you cannot see).
  let firsts : List (Fin n × Refine.ColData n) := cell.map (fun r => (r, step adj χ r))
  firsts.flatMap (fun p1 =>
    match deepen adj χ n p1.2 [] with
    | none => []
    | some (d1, seq) =>
        let χ1 := d1.col
        let K := coupled χ χ1
        if K.isEmpty || !allSingletonsK K χ1 then []
        else
          firsts.filterMap (fun pj =>
            if pj.1 == p1.1 then none
            else match replay adj seq pj.2 with
              | none => none
              | some dj =>
                  let χj := dj.col
                  let img : Vector (Fin n) n :=
                    Vector.ofFn (fun v =>
                      if K.contains v then (K.find? (fun w => χj w == χ1 v)).getD v else v)
                  match permOf (fun v => img.get v) with
                  | none => none
                  | some ρ => if decide (IsColAut adj χ ρ) then some ρ else none))

/-- The supply. -/
def deepenSupply : Supply n := fun adj χ =>
  (deepenGens adj χ, n * n * n * n * n * n)

end Deepen
end ChainDescent
