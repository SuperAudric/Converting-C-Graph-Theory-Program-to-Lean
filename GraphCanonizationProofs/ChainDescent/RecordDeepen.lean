import ChainDescent.TwinFamily
import ChainDescent.DeepenGuardComplete

/-!
# ★★★ WIRING THE GUARD INTO THE RECORD OBJECT — `③` for `recordSupplyFast ++ deepenSupplyCert`

`Publication.residue_if_flag` is *"`canonForm? = none ⟹ ¬ TinhoferGraph`"*, and
[Publication.lean §1] records exactly why it is open: the bridge
`TwinFamily.cellIsOrbit_deepenSupply_of_schurianAt` *"holds today at `deepenSupply` … but **NOT** at this
file's record supply."* The record supply simply does not contain deepen.

**This file supplies the missing piece the intended way — by making deepen a PART of the record supply,
not by moving the obligation to a second object** (which the same block forbids, and which the
options table (i)–(vi) had drifted into proposing).

## Why an append works, and why the *guard* had to be complete first

Two independent monotonicity facts do the work:

* `Consume.CellIsOrbit` is **monotone in the supply** (`Deepen.cellIsOrbit_append_right`, via
  `wordReach_mono`) — more generators can only merge more.
* `Cost.CellResolved` is a disjunction whose second disjunct does not mention the supply at all, so
  `Residue.Handled` is monotone under `appendSupply` in **both** branches (§1).

So `TwinFamily.handled_of_tinhoferGraph` — already proved, and already key-generic — lifts to any
supply that *contains* deepen. That gives `③` at `recordSupplyFast ++ deepenSupply` for free.

⚠ But the raw `deepenSupply` cannot go into `Publication.canonForm?`: `①` needs the supply's
branch-orbit relation to transport, and `deepenSupply`'s greedy descent picks by vertex index. The
supply that *can* go in is the **guarded** `deepenSupplyCert`. Guarding normally costs coverage — and
here it would cost exactly `③`, since a shut guard emits nothing and `CellIsOrbit` fails.

**It does not, and that is precisely what `DeepenGuardComplete` bought.** On a Tinhofer graph every
reached node is `SchurianAt`, hence `Deepen.Tinhofer` (`TwinFamily.tinhofer_of_stepClosed`), hence —
by **completeness**, `Deepen.certifiedG_of_tinhofer` — the guard is **open** there. Soundness alone
would not do this: it gives `CertifiedG ⟹ Tinhofer`, the wrong direction. §2 is the step that needs
`tinhofer_iff_certifiedG`'s new half.

⟹ `handled_deepenSupplyCert_of_tinhoferGraph` (§4): the guarded, **computable** supply is `Handled` on
every Tinhofer graph, for every key. Guarding is free on the class it is meant to cover.

## Scope — what this file does and does not close

✅ `③` at the appended object, in both the blind (`Residue.Handled`) and fused (`Select.HandledS`)
forms, ending at `not_tinhoferGraph_of_flag_recordAppend` — the exact shape `residue_if_flag` needs.

⚠ It does **not** yet repoint `Publication.canonForm?`. Two obligations must move with it:
* **`①`** — `RecordKey.recordKey_canonizer` goes through `Select.selNode_canonizer_of_sameOrbits`, so
  the appended supply needs its `SameOrbits`/branch-orbit transport. For `deepenSupplyCert` this is
  available in principle (where the guard is open the relation **is** the full `IsColAut` orbit
  relation, which conjugates; where it is shut deepen contributes `[]`), but it is not proved here.
* **`②`** — appending changes the cost, so `costConst`/`costDeg` (53 / 13) must be recomputed, and the
  guard's own work is still unbilled (`DeepenGuardComplete` §7's recorded gap).
-/

namespace ChainDescent
namespace RecordDeepen

open ChainDescent.Consume (Supply CellIsOrbit)

variable {n : Nat}

/-! ## 1. `Handled` is monotone under `appendSupply`

`CellResolved` is `CellIsOrbit S ∨ (the key separates the cell)`. The left disjunct is monotone in the
supply by `cellIsOrbit_append_right`; the right does not mention the supply. So both branches survive,
and a resolver can only be helped by being handed more generators. -/

theorem cellResolved_append_right {key : Force.Key n} {S₁ S₂ : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : Cost.CellResolved key S₂ adj χ) :
    Cost.CellResolved key (Deck.appendSupply S₁ S₂) adj χ :=
  h.imp Deepen.cellIsOrbit_append_right id

theorem handled_append_right {key : Force.Key n} {S₁ S₂ : Supply n} {adj : AdjMatrix n}
    (h : Residue.Handled key S₂ adj) :
    Residue.Handled key (Deck.appendSupply S₁ S₂) adj :=
  fun χ hr hd => cellResolved_append_right (h χ hr hd)

/-! ## 2. ★★★ THE GUARD IS OPEN AT EVERY REACHED NODE OF A TINHOFER GRAPH

This is the step that consumes `DeepenGuardComplete`'s new half. Soundness
(`tinhofer_of_certifiedG`) runs the wrong way; what is needed is **completeness**
(`certifiedG_of_tinhofer`) — the guard opens *because* the node is Tinhofer. -/

theorem tinhofer_of_reaches {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj)
    {χ : Colouring n} (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) :
    Deepen.Tinhofer adj χ :=
  TwinFamily.tinhofer_of_stepClosed (TwinFamily.stepClosed_indivReach adj) h
    (TwinFamily.mem_of_reaches (TwinFamily.stepClosed_indivReach adj) TwinFamily.IndivReach.root hr)

/-- **★★★ THE GUARD DEFERS NOWHERE ON A TINHOFER GRAPH.** -/
theorem certifiedG_of_tinhoferGraph {adj : AdjMatrix n} (h : TwinFamily.TinhoferGraph adj)
    {χ : Colouring n} (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) :
    Deepen.CertifiedG (Deepen.deepenSupply (n := n)) adj χ :=
  Deepen.certifiedG_of_tinhofer (tinhofer_of_reaches h hr)

/-! ## 3. Where the guard is open, the guarded supply IS deepen -/

theorem verified_deepenSupplyCert_of_certifiedG {adj : AdjMatrix n} {χ : Colouring n}
    (h : Deepen.CertifiedG (Deepen.deepenSupply (n := n)) adj χ) :
    Consume.verified (Deepen.deepenSupplyCert (n := n)) adj χ
      = Consume.verified (Deepen.deepenSupply (n := n)) adj χ := by
  unfold Consume.verified Consume.gens Deepen.deepenSupplyCert
  rw [if_pos h]

/-! ## 4. ★★★ THE GUARDED SUPPLY IS `Handled` ON EVERY TINHOFER GRAPH

`TwinFamily.handled_of_tinhoferGraph` says this of the raw supply. Guarding normally costs coverage;
§2 says it costs none *here*, so the computable object keeps the whole class. -/

theorem handled_deepenSupplyCert_of_tinhoferGraph {adj : AdjMatrix n}
    (h : TwinFamily.TinhoferGraph adj) (key : Force.Key n) :
    Residue.Handled key (Deepen.deepenSupplyCert (n := n)) adj := by
  intro χ hr hd
  refine Or.inl ?_
  have hcell : CellIsOrbit (Deepen.deepenSupply (n := n)) adj χ :=
    TwinFamily.cellIsOrbit_deepenSupply_of_schurianAt (tinhofer_of_reaches h hr)
      (h χ (TwinFamily.mem_of_reaches (TwinFamily.stepClosed_indivReach adj)
        TwinFamily.IndivReach.root hr))
  intro u hu w hw
  rw [verified_deepenSupplyCert_of_certifiedG (certifiedG_of_tinhoferGraph h hr)]
  exact hcell u hu w hw

/-! ## 5. ★★★ `③` AT THE APPENDED RECORD OBJECT -/

/-- **The record supply, extended by the guarded deepening supply.** -/
def recordSupplyDeepen : Supply n :=
  Deck.appendSupply (RecordCost.recordSupplyFast (n := n)) (Deepen.deepenSupplyCert (n := n))

/-- **★★★ A TINHOFER GRAPH IS `Handled` BY THE EXTENDED RECORD SUPPLY — for every key.** -/
theorem handled_recordSupplyDeepen_of_tinhoferGraph {adj : AdjMatrix n}
    (h : TwinFamily.TinhoferGraph adj) (key : Force.Key n) :
    Residue.Handled key (recordSupplyDeepen (n := n)) adj :=
  handled_append_right (handled_deepenSupplyCert_of_tinhoferGraph h key)

/-- The fused (`Select`) form, which is what `Publication.canonForm?` is built from. -/
theorem handledS_recordSupplyDeepen_of_tinhoferGraph {adj : AdjMatrix n}
    (h : TwinFamily.TinhoferGraph adj) (key : Force.Key n) :
    Select.HandledS key (recordSupplyDeepen (n := n)) adj :=
  Select.handledS_of_handled (handled_recordSupplyDeepen_of_tinhoferGraph h key)

/-- **★★ A TINHOFER GRAPH ANSWERS** at the extended record object. -/
theorem answersS_recordSupplyDeepen_of_tinhoferGraph {adj : AdjMatrix n}
    (h : TwinFamily.TinhoferGraph adj) (key : Force.Key n) :
    Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) key (recordSupplyDeepen (n := n))) adj
      ≠ none :=
  Select.answersS_of_handledS (handledS_recordSupplyDeepen_of_tinhoferGraph h key)

/-- **★★★ `③` — THE RESIDUE, AT THE EXTENDED RECORD OBJECT, FOR EVERY KEY.** This is exactly the
shape `Publication.residue_if_flag` needs; all that remains between here and that `sorry` is
repointing `canonForm?` and carrying `①`/`②` across (see the module header). -/
theorem not_tinhoferGraph_of_flag_recordDeepen {adj : AdjMatrix n} {key : Force.Key n}
    (hflag : Select.canonFormS? (Refine.encodeFreeFast (n := n))
      (Select.selNode (Refine.encodeFreeFast (n := n)) key (recordSupplyDeepen (n := n))) adj
        = none) :
    ¬ TwinFamily.TinhoferGraph adj :=
  fun h => answersS_recordSupplyDeepen_of_tinhoferGraph h key hflag

end RecordDeepen
end ChainDescent
