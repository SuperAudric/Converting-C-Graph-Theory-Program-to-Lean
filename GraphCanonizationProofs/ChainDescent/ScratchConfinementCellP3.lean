/-
# ScratchConfinementCellP3.lean — the rethread: confinement-P3 on the FAITHFUL cell model (WIP, NOT in build.sh)

**What this does.** Swaps the residue-scheme model in the confinement-P3 chain from the `Fin n` cardinality-only
`ResidueSchemeModel` to the FAITHFUL cell-based `CellSchemeModel` (`ScratchConfinementCellModel`). The swap is ADDITIVE
and small because `confinement_selectedCellIsOrbit_spine` (`ScratchConfinement`) is **generic in the residue predicate**
(it takes `PrimRank3Classical : Nat → Prop` as an abstract argument). So we only supply a NEW predicate + producer and
plug them into the SAME assembly — the green ① showcase's core is untouched.

**The predicate.** `PrimRank3ClassicalCell k := ∃ (C) (M : CellSchemeModel … k C), IsCameronScheme (cellCard C) M.S`
— the cell `C` is existential (keeping the predicate `Nat → Prop` as the assembly requires); `IsCameronScheme` is already
polymorphic in the vertex arity, so it applies at `cellCard C`. Now G3 classifies the REAL residue cell (faithful), not
an arbitrary cardinality-matched scheme on `Fin n`.

**Carried, as before:** `hClassify` (G3), the model `M` (now faithful, carrying `CellActionFaithful` + the 2-closure
citation internally), `hprim`, `hWitt` (the cell-predicate Witt/Liebeck citation). The largeness bridge is DISCHARGED
(`largeBridge_confinementLargeScheme_cell`, from `M.hcard` — identical to the `Fin n` version).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementCellModel

namespace ChainDescent.ConfinementCellP3

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP4
open ChainDescent.Confinement
open ChainDescent.NodeCountBridge
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle
open ChainDescent.ConfinementCellModel

variable {n : Nat}

/-- **The faithful cell-based residue predicate.** `∃` a selected cell `C` with a faithful `CellSchemeModel` the seal
classifies as a Cameron section. `C` is existential so the predicate is `Nat → Prop` (what the generic assembly needs);
`IsCameronScheme (cellCard C)` uses the arity-polymorphic Cameron predicate at the cell's vertex count. -/
def PrimRank3ClassicalCell (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop) (k : Nat) : Prop :=
  ∃ (C : Finset (Fin n)) (M : CellSchemeModel adj P₀ χι₀ sel k C), IsCameronScheme (cellCard C) M.S

/-- **The largeness bridge on the cell model — DISCHARGED** (identical shape to `largeBridge_confinementLargeScheme`):
the residual order IS the cell-scheme Aut order (`M.hcard`), so the flag's super-poly bound transfers verbatim. -/
theorem largeBridge_confinementLargeScheme_cell (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) {C : Finset (Fin n)}
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (h : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k) :
    confinementLargeScheme n (cellCard C) M.S := by
  show 2 ^ baseMax n < Nat.card M.S.toAssociationScheme.SchemeAutGroup
  rw [M.hcard]; exact h

/-- **The cell-model producer** — from a faithful `CellSchemeModel` + G3 (`exhaustiveObstruction_scheme` at `cellCard C`)
produce `PrimRank3ClassicalCell`. Direct mirror of `residue_primRank3Classical`, faithful at the cell arity. -/
theorem residue_primRank3ClassicalCell (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) {C : Finset (Fin n)}
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hLargeBridge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme (cellCard C) M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hlarge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k) :
    PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme k :=
  ⟨C, M, exhaustiveObstruction_scheme hClassify M.S M.hne hprim M.hrank (hLargeBridge hlarge)⟩

/-- **★ Confinement on the FAITHFUL cell model, largeness discharged.** Plugs the cell predicate + cell producer into
the SAME generic `confinement_selectedCellIsOrbit_spine`. Carries only the genuine citations/gaps at the cell arity:
`hClassify` (G3), the faithful model `M`, `hprim`, and Witt `hWitt` (now consuming the cell predicate). Concludes the
same `SelectedCellIsOrbit` — the assume-VT prune is sound, now backed by a model that genuinely classifies the residue
cell. -/
theorem confinement_selectedCellIsOrbit_spine_cell_discharged (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine adj P₀ χι₀ sel χsel S k hn
    (PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme)
    (fun hlarge _hsym => residue_primRank3ClassicalCell adj P₀ χι₀ sel k hClassify M
      (largeBridge_confinementLargeScheme_cell adj P₀ χι₀ sel k M) hprim hlarge)
    hWitt hflag

end ChainDescent.ConfinementCellP3
