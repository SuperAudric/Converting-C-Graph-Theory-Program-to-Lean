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
