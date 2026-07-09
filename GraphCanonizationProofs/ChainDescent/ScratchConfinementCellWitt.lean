/-
# ScratchConfinementCellWitt.lean — the rethread, Witt layer on the FAITHFUL cell model (WIP, NOT in build.sh)

Mirrors `confinement_selectedCellIsOrbit_spine_witt{,_classical}` (`ScratchConfinementWitt`) on the cell predicate
`PrimRank3ClassicalCell`. The Witt reduction `frameSelectorTransitive_of_wittCellTransitive` is REUSED verbatim (it is
generic in the cell), so this is pure composition. The classicality split's `hLiebeck` becomes **arity-polymorphic**
(`∀ m (T : SchurianScheme m), Cameron → classical`) — the faithful form of Liebeck (it is not about a fixed `n`), applied
at the cell arity `cellCard C` inside the `∃`.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementCellP3
import ChainDescent.ScratchConfinementWitt

namespace ChainDescent.ConfinementCellWitt

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.NodeCountBridge
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP4
open ChainDescent.ConfinementWitt
open ChainDescent.ConfinementCellModel
open ChainDescent.ConfinementCellP3
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **Confinement on the faithful cell model, Witt layer (compound citation).** Mirrors
`confinement_selectedCellIsOrbit_spine_witt`: supplies the P3-cell `hWitt` via the reused Witt reduction. -/
theorem confinement_selectedCellIsOrbit_spine_witt_cell (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hCitation : PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact confinement_selectedCellIsOrbit_spine_cell_discharged adj P₀ χι₀ sel χsel S k hn hClassify M hprim
    (fun h => frameSelectorTransitive_of_wittCellTransitive (hCitation h)) hflag

/-- **★ Confinement on the faithful cell model, classicality-threaded.** Mirrors
`confinement_selectedCellIsOrbit_spine_witt_classical`: the compound Witt citation is split into `hLiebeck`
(Cameron ⟹ classical, arity-polymorphic — the faithful Liebeck) + `hWitt` (classical ⟹ cell-transitive), composed
inside the cell predicate's `∃`. Bundle now reads {G3, Liebeck, Witt, hImprim, D0} on the FAITHFUL model. -/
theorem confinement_selectedCellIsOrbit_spine_witt_classical_cell (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hLiebeck : ∀ (m : Nat) (T : SchurianScheme m), IsCameronScheme m T → IsClassicalScheme m T)
    (hWitt : PrimRank3ClassicalCell adj P₀ χι₀ sel IsClassicalScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine_witt_cell adj P₀ χι₀ sel χsel S k hn hClassify M hprim
    (fun hCam => hWitt (by
      obtain ⟨C', M', hcam⟩ := hCam
      exact ⟨C', M', hLiebeck (cellCard C') M'.S hcam⟩)) hflag

end ChainDescent.ConfinementCellWitt
