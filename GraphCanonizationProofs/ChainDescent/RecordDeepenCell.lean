import ChainDescent.DeepenCell
import ChainDescent.RecordDeepen
import ChainDescent.RecordKey

/-!
# ★★★ THE ENDGAME OBJECT — the record supply, cell-indexed, with deepen

This is design `B` at the object `Publication.canonForm?` is meant to become:

```
Select.selNodeC encodeFreeFast recordKey (fun c => recordSupplyFast ++ deepenCellSupply c)
```

Two obligations land here, and they are the two the plan calls `W-d′` and the `③` mirror.

## `W-d′` — `①` at the record's own left factor

`Deepen.cellOrbitTransport_append` asks only that the left factor's **orbit relation** transport
where deepen's guard is shut. `RecordCost.recordSupplyFast` is not `SupplyEquivariant` —
`Kernel.kernelSupply`'s Gaussian basis is pivot-order dependent, and provably cannot be
(`KernelRef`'s trap #7 note). But it does not have to be: its orbits match the equivariant
set-level reference `Kernel.recordRefSupply` (`Kernel.sameOrbits_recordSupply`), and the relation is
the only thing `①` reads. `Select.wordReach_transport_of_sameOrbits` is exactly that step.

⟹ **`recordDeepenCell_canonizer`**: `①a`/`①b`/`①c` at the endgame object, no hypothesis.

## The `③` mirror — why `RecordDeepen` does not simply transfer

`RecordDeepen.not_tinhoferGraph_of_flag_recordDeepen` is `③` at
`selNode` + the **node-global** `recordSupplyFast ++ deepenSupplyCert`. That object is exactly the
one `probe_offbranch2/3.py` falsifies for `①` (CFI m = 8/10, depth 1, an off-branch cell counting
`(1,1)` vs `(2,)` with the guard open on both sides), so it cannot be the published object, and the
`③` statement does not rewrite onto `selNodeC`: `Select.HandledS` / `answersS_of_handledS` /
`not_handledS_if_flagS` are all stated at `selNode`.

`SelectCell` §4 supplies the resolver-side mirror. What is left, and is here, is the **population**:
a Tinhofer graph resolves its *target* cell against generators anchored **in that cell**. The
argument is `RecordDeepen`'s, one level more local:

| step | node-global (`RecordDeepen`) | cell-indexed (here) |
|---|---|---|
| guard opens | `certifiedG_of_tinhoferGraph` (all branch anchors) | `goodCell_of_tinhofer` — `Tinhofer` **is** `∀ x ∈ branches, GoodAnchor x` (`tinhofer_iff_forall_goodAnchor`, `Iff.rfl`) and `branches χ = cellList χ c` at the target colour |
| cell is one orbit | `cellIsOrbit_deepenSupply_of_schurianAt` | `cellIsOrbit_deepenCellSupply_of_schurianAt` — same `SchurianAt` automorphism, fed to `orbitCompleteAt_of_goodCell` |
| append | `handled_append_right` | `Deepen.cellIsOrbit_append_right` |

★ The reason this goes through unchanged is the one recorded in the plan: `TinhoferGraph` is an
**all-cells** condition (`SchurianAt` at every individualization-reachable colouring), so per-cell
evidence is available wherever node-global evidence was — the strengthening costs no coverage on
the class `③` is stated about.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned.
-/

namespace ChainDescent
namespace RecordDeepenCell

open ChainDescent.Consume (Supply CellIsOrbit verified WordReach IsColAut)

variable {n : Nat}

/-! ## 1. The object -/

/-- **The endgame supply**: the record supply, plus — per cell — the guarded harvest of descents
anchored **in that cell**. `Select.ofSupply` is the `c`-independent special case, so the previous
object is the `deepenCellSupply ↦ emptySupply` degeneration of this one. -/
def recordSupplyDeepenC : Select.CellSupply n := fun c =>
  Deck.appendSupply (RecordCost.recordSupplyFast (n := n)) (Deepen.deepenCellSupply c)

/-! ## 2. `W-d′` — `①` AT THE ENDGAME OBJECT

`kernelSupply` is provably not `GensEquivariant`, so the left factor enters through `SameOrbits`
against `Kernel.recordRefSupply`. ⚠ `recordSupplyFast` uses `foldSupplyFast` where
`Kernel.recordSupply` uses `foldSupply`; `Fold.foldSupplyFast_eq` is the bridge, exactly as
`RecordKey.recordKey_canonizer` uses it. -/

/-- The record supply's orbit relation transports — the hypothesis
`Deepen.cellOrbitTransport_append` was shaped for. Stated at `Kernel.recordSupply` (the
`foldSupply` spelling) so the `SameOrbits` pair applies syntactically; `Fold.foldSupplyFast_eq`
bridges to `recordSupplyFast` one level up. -/
theorem wordReach_transport_recordSupply (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n)
    (χ : Colouring n) (a b : Fin n) :
    WordReach (verified (Kernel.recordSupply (n := n)) (relabelAdj σ adj)
        (Descend.transportColouring σ χ)) (σ a) (σ b)
      ↔ WordReach (verified (Kernel.recordSupply (n := n)) adj χ) a b :=
  Select.wordReach_transport_of_sameOrbits Kernel.sameOrbits_recordSupply
    Kernel.supplyEquivariant_recordRefSupply σ adj χ a b

/-- **★★ `W-d′`** — the endgame supply satisfies `Select.CellOrbitTransport`. Open cells get it from
the guard (the relation *is* the intrinsic orbit relation, which conjugates); shut cells inherit it
from the record supply above. -/
theorem cellOrbitTransport_recordSupplyDeepenC :
    Select.CellOrbitTransport (recordSupplyDeepenC (n := n)) := by
  have h : Select.CellOrbitTransport
      (fun c => Deck.appendSupply (Kernel.recordSupply (n := n)) (Deepen.deepenCellSupply c)) :=
    Deepen.cellOrbitTransport_append wordReach_transport_recordSupply
  show Select.CellOrbitTransport
    (fun c => Deck.appendSupply (Deck.appendSupply (Fold.foldSupplyFast (n := n))
      (Deck.appendSupply (Deck.deckSupply (n := n))
        (Deck.appendSupply (Deck2.deck2Supply (n := n)) (Kernel.kernelSupply (n := n)))))
      (Deepen.deepenCellSupply c))
  rw [Fold.foldSupplyFast_eq]
  exact h

/-- **★★★ `①` AT THE ENDGAME OBJECT** — sound, complete, flag-iso-invariant, **globally and with no
hypothesis**. This is the statement the node-global object provably cannot have, and it is what
distinguishes design `B` from wind-down option (v) (which proves `①b`/`①c` only on the class). -/
theorem recordDeepenCell_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
          (recordSupplyDeepenC (n := n)))) :=
  Select.selNodeC_canonizer RecordKey.keyEquivariant_recordKey
    cellOrbitTransport_recordSupplyDeepenC

/-! ## 3. THE `③` POPULATION — the per-cell guard opens on a Tinhofer graph -/

/-- **The per-cell guard opens at the TARGET cell**, from `Tinhofer` alone.
`Deepen.tinhofer_iff_forall_goodAnchor` is `Iff.rfl` — `Tinhofer` already *is* "every anchor of the
branch cell is good" — and `Select.branches_eq_cellList` identifies that list with the target
cell. So no new content is needed: the node-global guard and the target cell's guard are the same
statement. -/
theorem goodCell_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (htc : Descend.targetColour χ = some c) (hT : Deepen.Tinhofer adj χ) :
    Deepen.GoodCell adj χ c := by
  intro r hr
  exact hT r (by rw [Select.branches_eq_cellList htc]; exact hr)

/-- **★★ THE TARGET CELL IS ONE ORBIT OF ITS OWN GENERATORS.** `RecordDeepen`'s firing lemma with
the harvest restricted to the cell: `SchurianAt` supplies the automorphism, and
`Deepen.orbitCompleteAt_of_goodCell` — the per-cell recovery — turns it into a `WordReach` over
generators anchored **inside** the cell. -/
theorem cellIsOrbit_deepenCellSupply_of_schurianAt {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (htc : Descend.targetColour χ = some c) (hT : Deepen.Tinhofer adj χ)
    (hS : TwinFamily.SchurianAt adj χ) :
    CellIsOrbit (Deepen.deepenCellSupply (n := n) c) adj χ := by
  have hgood : Deepen.GoodCell adj χ c := goodCell_of_tinhofer htc hT
  intro u hu w hw
  rw [Deepen.verified_deepenCellSupply_of_open hgood]
  have hu' : u ∈ Select.cellList χ c := by rw [← Select.branches_eq_cellList htc]; exact hu
  have huc : χ u = c := (Descend.mem_branches_iff htc u).mp hu
  have hwc : χ w = c := (Descend.mem_branches_iff htc w).mp hw
  obtain ⟨ρ, hρ, hρu⟩ := hS c u w huc hwc
  have hreach := Deepen.orbitCompleteAt_of_goodCell hgood u hu' ρ hρ
  rwa [hρu] at hreach

/-- The same at the endgame supply — extra generators can only merge more
(`Deepen.cellIsOrbit_append_right`). -/
theorem cellIsOrbit_recordSupplyDeepenC_of_schurianAt {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (htc : Descend.targetColour χ = some c) (hT : Deepen.Tinhofer adj χ)
    (hS : TwinFamily.SchurianAt adj χ) :
    CellIsOrbit (recordSupplyDeepenC (n := n) c) adj χ :=
  Deepen.cellIsOrbit_append_right (cellIsOrbit_deepenCellSupply_of_schurianAt htc hT hS)

/-- **★★★ A TINHOFER GRAPH IS `HandledSC` — for every key.** At every reached non-discrete node the
target cell narrows to one branch **on its own evidence**. -/
theorem handledSC_of_tinhoferGraph {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj)
    (key : Force.Key n) :
    Select.HandledSC key (recordSupplyDeepenC (n := n)) adj := by
  intro χ hr hd
  obtain ⟨c₀, hc₀⟩ := Select.exists_targetColour_of_not_discrete hd
  refine ⟨c₀, Finset.mem_of_min hc₀, ?_⟩
  have hIR : TwinFamily.IndivReach adj χ :=
    TwinFamily.mem_of_reaches (TwinFamily.stepClosed_indivReach adj) TwinFamily.IndivReach.root hr
  have hcell := cellIsOrbit_recordSupplyDeepenC_of_schurianAt hc₀
    (RecordDeepen.tinhofer_of_reaches h hr) (h χ hIR)
  show (Select.cellNarrow key (recordSupplyDeepenC (n := n) c₀) adj χ c₀).length ≤ 1
  rw [Select.cellNarrow_targetColour hc₀]
  exact le_of_eq (Composite.forceThenConsume_singleton_of_cellIsOrbit hd hcell)

/-- **★★ A TINHOFER GRAPH ANSWERS** at the endgame object. -/
theorem answersSC_of_tinhoferGraph {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj)
    (key : Force.Key n) :
    Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) key (recordSupplyDeepenC (n := n))) adj
      ≠ none :=
  Select.answersSC_of_handledSC (handledSC_of_tinhoferGraph h key)

/-- **★★★ `③` AT THE ENDGAME OBJECT, FOR EVERY KEY** — if the canonizer flags, the input is provably
not a Tinhofer graph. With `recordDeepenCell_canonizer` (`①`) this is the first time `①` and `③` hold
of the **same** object with `①` unconditional; `②` is the remaining obligation. -/
theorem not_tinhoferGraph_of_flag {adj : AdjMatrix n} {key : Force.Key n}
    (hflag : Select.canonFormS? (Refine.encodeFreeFast (n := n))
      (Select.selNodeC (Refine.encodeFreeFast (n := n)) key (recordSupplyDeepenC (n := n))) adj
        = none) :
    ¬ TwinFamily.TinhoferGraph adj :=
  fun h => answersSC_of_tinhoferGraph h key hflag

/-! ## 4. `②` — THE COST, AT THE SAME OBJECT (plan `W-h`, with `W-a` folded in)

`RecordKey.descentCostS_selNode_recordKey_monomial` is stated at **`selNode`**; of its chain only
`Select.descentCostS_le_of_le_one` is resolver-generic, so `SelectCell` §5 mirrored the rest. Here it
is instantiated at the endgame supply.

**Two things changed in the numerals, and neither is free:**

* `Deepen.deepenCellCost` now bills the **guard** as well as the harvest (`W-a`,
  `Deepen.goodCellCost_bounds_guard`). Before this the declared charge was `deepenSupply`'s flat `n⁶`,
  which priced the harvest and charged nothing for the `≤ n` `CertPath` walks `GoodCell` runs.
* `Select.selProbeBoundC` bills the supply **per cell**, so the supply terms carry a factor `≤ n`.

★ **The degree does NOT move.** `RecordKey.recordKeyBound` already reaches `n^10` (the `orbKeyG` guard
inside the record key), and `(n+1) · n · n · kc` is what sets the degree — so the supply's extra `n`
and the guard's `n^8` both sit strictly below it. **`costDeg` stays 13; `costConst` goes 57 → 69.** -/

/-- The endgame supply's per-node work bound: the record's four supplies, plus the cell-anchored
harvest **and its guard**. -/
def recordDeepenSupplyBound (n : Nat) : Nat :=
  RecordCost.recordSupplyBound n + Deepen.deepenCellCost n

/-- …and its candidate-count bound: the record's, plus `≤ |cell|² ≤ n²` twists. -/
def recordDeepenGensBound (n : Nat) : Nat := RecordCost.recordGensBound n + n * n

/-- The cell-anchored harvest emits `≤ |cell|²` generators — the same `flatMap`-of-`filterMap` shape
as `TwinFamily.gens_deepenSupply_length_le`, with `cell` in place of `Descend.branches χ`. -/
theorem gens_deepenGensOn_length_le (adj : AdjMatrix n) (χ : Colouring n) {cell : List (Fin n)}
    (hc : cell.length ≤ n) : (Deepen.deepenGensOn adj χ cell).length ≤ n * n := by
  have hfirsts : (cell.map (fun r => (r, Deepen.step adj χ r))).length ≤ n := by
    rw [List.length_map]; exact hc
  refine le_trans (RecordCost.length_flatMap_le _ _ n ?_) (Nat.mul_le_mul_right n hfirsts)
  intro p1 _
  dsimp only
  split
  · simp
  · split
    · simp
    · exact le_trans (List.length_filterMap_le ..) hfirsts

theorem gens_deepenCellSupply_length_le (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    (Consume.gens (Deepen.deepenCellSupply (n := n) c) adj χ).length ≤ n * n := by
  by_cases h : Deepen.GoodCell adj χ c
  · rw [Deepen.gens_deepenCellSupply_of_open h]
    exact gens_deepenGensOn_length_le adj χ (Select.cellList_length_le χ c)
  · rw [Deepen.gens_deepenCellSupply_of_shut h]; simp

/-- ⚠ Rewrite the **outer** append only — `supplyCost_appendSupply` / `gens_appendSupply_length` are
`@[simp]`, so `simp only` would keep descending into `recordSupplyFast`'s own four-way nest and lose
the shape `RecordCost.supplyCost_record_le` is stated in. -/
theorem supplyCost_recordSupplyDeepenC_le (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    Consume.supplyCost (recordSupplyDeepenC (n := n) c) adj χ ≤ recordDeepenSupplyBound n := by
  show Consume.supplyCost (Deck.appendSupply (RecordCost.recordSupplyFast (n := n))
      (Deepen.deepenCellSupply c)) adj χ
    ≤ RecordCost.recordSupplyBound n + Deepen.deepenCellCost n
  rw [RecordCost.supplyCost_appendSupply, Deepen.supplyCost_deepenCellSupply]
  exact Nat.add_le_add (RecordCost.supplyCost_record_le adj χ) le_rfl

theorem gens_recordSupplyDeepenC_length_le (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    (Consume.gens (recordSupplyDeepenC (n := n) c) adj χ).length ≤ recordDeepenGensBound n := by
  show (Consume.gens (Deck.appendSupply (RecordCost.recordSupplyFast (n := n))
      (Deepen.deepenCellSupply c)) adj χ).length ≤ RecordCost.recordGensBound n + n * n
  rw [RecordCost.gens_appendSupply_length]
  exact Nat.add_le_add (RecordCost.gens_record_length_le adj χ)
    (gens_deepenCellSupply_length_le adj χ c)

/-- **★★ `②` AT THE ENDGAME OBJECT, PARAMETRIC.** No hypotheses: fan-out `≤ 1` holds by construction,
so this bounds answer and flag alike, on every input. -/
theorem descentCostSC_recordDeepen_le (adj : AdjMatrix n) :
    Select.descentCostS (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
          (recordSupplyDeepenC (n := n))) adj
      ≤ n * n * n + (n + 1)
          * (1 + (Select.selProbeBoundC n (recordDeepenSupplyBound n) (recordDeepenGensBound n)
              (RecordKey.recordKeyBound n) + n * n * n)) :=
  Select.descentCostS_selNodeC_le
    (fun c χ => supplyCost_recordSupplyDeepenC_le adj χ c)
    (fun c χ => gens_recordSupplyDeepenC_length_le adj χ c)
    (fun χ v => RecordKey.keyCost_recordKey_le adj χ v)

/-! ### 4a. The monomial — the shape `Publication.canon_poly_or_flag` pins

Same discipline as `RecordKey` §5: the numerals are **computed** by `ring` in the expansion below, not
fitted. ⚠ The pinned shape must stay `costConst * (n + 1) ^ costDeg` — the `n`-form is false at
`n = 0`, where every colouring is vacuously `Discrete`, the object costs 1 and *answers*. -/

/-- The coefficient sum of §4's bound polynomial. **57 → 69** against
`RecordKey.costConst`: `+ 8` from the per-cell supply billing and `+ 4` from `W-a`'s guard charge
(`Deepen.deepenCellCost = n^8 + 2n^6 + n^5`). `ring` checks the transcription. -/
def costConst : Nat := 69

/-- The degree of §4's bound polynomial — **unchanged at 13**: `RecordKey.recordKeyBound` already
reaches `n^10`, and the key term is what sets the degree. -/
def costDeg : Nat := 13

/-- §4's bound, expanded. `ring` checks it, so `costConst`/`costDeg` are computed from the object. -/
theorem recordDeepenBound_expand (n : Nat) :
    n * n * n + (n + 1)
        * (1 + (Select.selProbeBoundC n (recordDeepenSupplyBound n) (recordDeepenGensBound n)
            (RecordKey.recordKeyBound n) + n * n * n))
      = n ^ 13 + n ^ 12 + 4 * n ^ 11 + 5 * n ^ 10 + 5 * n ^ 9 + 11 * n ^ 8 + 14 * n ^ 7
          + 12 * n ^ 6 + 7 * n ^ 5 + 4 * n ^ 4 + 3 * n ^ 3 + n + 1 := by
  simp only [Select.selProbeBoundC, recordDeepenSupplyBound, recordDeepenGensBound,
    RecordCost.recordSupplyBound, RecordCost.recordGensBound, RecordKey.recordKeyBound,
    RecordKey.guardSupplyBound, SupplyCost.matchSupplyBound, Deepen.deepenCellCost,
    Deepen.goodCellCost, Deepen.stepCost]
  ring

/-- §4's sum bound is dominated by the pinned monomial — shared by the eager and the lazy object.
⟹ **the endgame object runs within `69 * (n + 1) ^ 13` on every input**, no hypotheses, no flag
disjunct. -/
theorem bound_le_monomial (n : Nat) :
    n * n * n + (n + 1)
        * (1 + (Select.selProbeBoundC n (recordDeepenSupplyBound n) (recordDeepenGensBound n)
            (RecordKey.recordKeyBound n) + n * n * n))
      ≤ costConst * (n + 1) ^ costDeg := by
  rw [recordDeepenBound_expand n]
  simp only [costConst, costDeg]
  have H : ∀ k : Nat, k ≤ 13 → n ^ k ≤ (n + 1) ^ 13 := fun k hk =>
    le_trans (Nat.pow_le_pow_left (Nat.le_succ n) k)
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) hk)
  have e13 := H 13 (by omega); have e12 := H 12 (by omega); have e11 := H 11 (by omega)
  have e10 := H 10 (by omega); have e9 := H 9 (by omega); have e8 := H 8 (by omega)
  have e7 := H 7 (by omega); have e6 := H 6 (by omega); have e5 := H 5 (by omega)
  have e4 := H 4 (by omega); have e3 := H 3 (by omega)
  have e1 : n ≤ (n + 1) ^ 13 := by simpa using H 1 (by omega)
  have e0 : 1 ≤ (n + 1) ^ 13 := by simpa using H 0 (by omega)
  omega

/-- **★★★ `②` IN THE PUBLICATION SHAPE**, at the eager object. -/
theorem descentCostSC_recordDeepen_monomial (adj : AdjMatrix n) :
    Select.descentCostS (Refine.encodeFreeFast (n := n))
        (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
          (recordSupplyDeepenC (n := n))) adj
      ≤ costConst * (n + 1) ^ costDeg :=
  le_trans (descentCostSC_recordDeepen_le adj) (bound_le_monomial n)

/-- **★★★ `①` ∧ `②` ∧ `③` AT ONE OBJECT** — every obligation `Publication.lean` states, all of them
properties of the *same* canonizer, all axiom-clean, `①` and `②` unconditional and `③` at the tight
residue `¬ TinhoferGraph`. This is what `Publication.canonForm?` is to be repointed at (plan `W-g`),
once the runnable `rfl`-twin exists (`W-i`). -/
theorem recordDeepenCell_full :
    CanonSpec.IsCanonicalFormOpt
        (Select.canonFormS? (Refine.encodeFreeFast (n := n))
          (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
            (recordSupplyDeepenC (n := n))))
    ∧ (∀ adj : AdjMatrix n,
        Select.descentCostS (Refine.encodeFreeFast (n := n))
            (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
              (recordSupplyDeepenC (n := n))) adj
          ≤ costConst * (n + 1) ^ costDeg)
    ∧ (∀ adj : AdjMatrix n,
        Select.canonFormS? (Refine.encodeFreeFast (n := n))
            (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
              (recordSupplyDeepenC (n := n))) adj = none →
          ¬ TwinFamily.TinhoferGraph adj) :=
  ⟨recordDeepenCell_canonizer, descentCostSC_recordDeepen_monomial,
   fun _ hflag => not_tinhoferGraph_of_flag hflag⟩

/-! ## 5. `W-i` + `W-e` — THE RUNNABLE, LAZILY-BILLED FORM

Two runnable forms exist and the endgame uses the second.

* **`W-i`, `Select.selNodeFastC`** — one shared `cellData` table, so each cell's supply is evaluated
  once per node, and children built through `Refine.ColData` (traps #2 and #1).
* **`W-e`, `Select.selNodeLazyC`** — strictly better: it walks the cells in **increasing colour
  order**, evaluating and billing each on demand, and **stops at the first that fires**, returning
  that cell's narrowing so the committed cell is never re-probed. On a node whose least colour fires
  it touches **one** cell instead of all of them.

⚠ Laziness had to reach the **billing**: `selProbeCostC` sums over every cell, so a lazy *selector*
alone would have saved nothing (`SelectCell` §7). The lazy resolver therefore returns a **smaller
cost** — which is why `②` goes through `probeWalk_bill_le` into the *existing* `selProbeCostC_le`
rather than needing new numerals, and why `①` goes through `descendS_val_congr` (the children are
unchanged; `NodeTransport` reads only `.1`).

## `W-j` — the two recomputations inside each probed cell (2026-08-08)

`probeWalk` evaluated the record key **three times per vertex per probed cell** (once for the bill
via `keyCost`, twice inside `Force.keepMin` — `keyCost` and `keyV` are `.2` and `.1` of the *same*
strict pair) and re-harvested the **cell-independent** left factor `recordSupplyFast`, re-running
its `IsColAut` filter, once per probed cell. `Select.probeWalkH` removes both: the key goes into a
`keyTable` read by the bill *and* the argmin, and the left factor's cost, candidate count and
**verified** list are computed once per node by `Select.selNodeLazyHC`.

★ **The bill is unchanged**, so `Select.probeWalkH_eq` is an *equation*, not an inequality: `①`, `②`
and `③` all transfer by rewriting and **`costConst`/`costDeg` do not move**. Measured 1.34× (`C₅`) /
1.48× (`K₁,₂,₃`) with identical billed costs. -/

/-- The endgame supply's split: `recordSupplyFast` is the node-level factor, the cell-anchored
harvest is the cell-level one. `Deck.appendSupply` is definitionally the `SplitSupply` shape. -/
theorem splitSupply_recordSupplyDeepenC :
    Select.SplitSupply (recordSupplyDeepenC (n := n)) (RecordCost.recordSupplyFast (n := n))
      (Deepen.deepenCellSupply (n := n)) := fun _ _ _ => rfl

/-- **The runnable endgame canonizer** — lazily billed, key shared, left factor hoisted. -/
def canonFormFast (adj : AdjMatrix n) : Option (CanonSpec.Labelled n) :=
  Select.canonFormLazyHSC? (RecordKey.recordKey (n := n)) (RecordCost.recordSupplyFast (n := n))
    (Deepen.deepenCellSupply (n := n)) adj

/-- …and its cost. -/
def costFast (adj : AdjMatrix n) : Nat :=
  Select.descentCostS (Refine.encodeFreeFast (n := n))
    (Select.selNodeLazyHC (RecordKey.recordKey (n := n)) (RecordCost.recordSupplyFast (n := n))
      (Deepen.deepenCellSupply (n := n))) adj

theorem canonFormFast_eq :
    canonFormFast (n := n)
      = Select.canonFormS? (Refine.encodeFreeFast (n := n))
          (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
            (recordSupplyDeepenC (n := n))) := by
  -- `W-j`: the hoisted walk *is* the walk (`probeWalkH_eq`); then lemma B (`W-e`).
  funext adj
  show Select.canonFormLazyHSC? _ _ _ adj = _
  rw [Select.canonFormLazyHSC?_eq splitSupply_recordSupplyDeepenC]
  exact congrFun (Select.canonFormS?_selNodeLazyC_eq _ _) adj

/-- The runnable cost is the reasoned-about cost — an **equation**, because `W-j` left the bill
alone: `probeWalkH` shares work, it does not charge differently. -/
theorem costFast_eq (adj : AdjMatrix n) :
    costFast adj
      = Select.descentCostS (Refine.encodeFreeFast (n := n))
          (Select.selNodeLazyC (RecordKey.recordKey (n := n)) (recordSupplyDeepenC (n := n))) adj :=
  Select.descentCostS_selNodeLazyHC_eq splitSupply_recordSupplyDeepenC _ adj

/-- **★★★ `①` ∧ `②` ∧ `③` AT THE RUNNABLE OBJECT.** `①` and `③` transport along `canonFormFast_eq`;
`②` rides `costFast_eq` into the lazy bill and lands on the **same** monomial. -/
theorem recordDeepenCell_full_fast :
    CanonSpec.IsCanonicalFormOpt (canonFormFast (n := n))
    ∧ (∀ adj : AdjMatrix n, costFast adj ≤ costConst * (n + 1) ^ costDeg)
    ∧ (∀ adj : AdjMatrix n, canonFormFast adj = none → ¬ TwinFamily.TinhoferGraph adj) := by
  obtain ⟨h1, _h2, h3⟩ := recordDeepenCell_full (n := n)
  refine ⟨by rw [canonFormFast_eq]; exact h1, fun adj => ?_,
    fun adj hf => h3 adj (by rw [canonFormFast_eq] at hf; exact hf)⟩
  rw [costFast_eq]
  exact le_trans (Select.descentCostS_selNodeLazyC_le
    (fun c χ => supplyCost_recordSupplyDeepenC_le adj χ c)
    (fun c χ => gens_recordSupplyDeepenC_length_le adj χ c)
    (fun χ v => RecordKey.keyCost_recordKey_le adj χ v)) (bound_le_monomial n)

/-- **★★★ `①` ∧ `③` AT ONE OBJECT**, at the record key. -/
theorem recordDeepenCell_record :
    CanonSpec.IsCanonicalFormOpt
        (Select.canonFormS? (Refine.encodeFreeFast (n := n))
          (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
            (recordSupplyDeepenC (n := n))))
    ∧ ∀ adj : AdjMatrix n,
        Select.canonFormS? (Refine.encodeFreeFast (n := n))
            (Select.selNodeC (Refine.encodeFreeFast (n := n)) (RecordKey.recordKey (n := n))
              (recordSupplyDeepenC (n := n))) adj = none →
          ¬ TwinFamily.TinhoferGraph adj :=
  ⟨recordDeepenCell_canonizer, fun _ hflag => not_tinhoferGraph_of_flag hflag⟩

end RecordDeepenCell
end ChainDescent
