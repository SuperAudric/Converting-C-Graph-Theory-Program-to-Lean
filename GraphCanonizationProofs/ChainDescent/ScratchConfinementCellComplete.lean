/-
# ScratchConfinementCellComplete.lean — the rethread, top layer: the ① showcase on the FAITHFUL cell model (WIP, NOT in build.sh)

The final rethread layer. `descentCanon`, `descentCanon_complete`, `canon_sound`, `descentCanonForm?` are **model-agnostic**
(they reference the descent canonizer + `DescentConfinement`, never the residue model), so they are REUSED verbatim. Only
the citation-supply layer changes: `descentConfinement_of_citations` → `_cell` (built from the FAITHFUL `CellSchemeModel`
capstone `confinement_selectedCellIsOrbit_spine_witt_classical_cell`), the bundle → `ConfinementCitationsCell`, and the
showcase → `descentCanon_showcase_cell`.

**What changes in the bundle.** The per-node model `M` now supplies, for each `(H, done)`, a **cell `C` + a faithful
`CellSchemeModel` on it** (packaged as a `Σ`). `hLiebeck` is arity-polymorphic (the faithful Liebeck). Everything else
(`hClassify`=G3, `hprim`=hImprim, `hWitt`=classical⟹cell-transitive, `hflag`) is the same named base — now on a model
that genuinely classifies the residue cell (`Aut(S) =` the residual cell action, via 2-closure + `CellActionFaithful`).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Complete
import ChainDescent.ScratchConfinementCellWitt

namespace ChainDescent.ConfinementCellComplete

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Sel
open ChainDescent.ConfinementX3Recon
open ChainDescent.NodeCountBridge
open ChainDescent.CanonSound
open ChainDescent.ConfinementCompleteness
open ChainDescent.ConfinementWitt
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP1
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle
open ChainDescent.ConfinementCellModel
open ChainDescent.ConfinementCellP3
open ChainDescent.ConfinementCellWitt
open ChainDescent.ConfinementX3Complete

variable {n : Nat}

/-- **W4.3 adaptor on the cell capstone.** The Finset-indexed cell capstone at the constant `χsel` and `S := done.toFinset`
yields the list-indexed per-`done` `SelectedCellIsOrbit` — mirror of `selectedCellIsOrbit_done_of_capstone`. -/
theorem selectedCellIsOrbit_done_of_capstone_cell (H : AdjMatrix n) (done : List (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {C : Finset (Fin n)}
    {IsCameronScheme IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel H defaultP₀ defaultχι₀ selCell k C)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hLiebeck : ∀ (m : Nat) (T : SchurianScheme m), IsCameronScheme m T → IsClassicalScheme m T)
    (hWitt : PrimRank3ClassicalCell H defaultP₀ defaultχι₀ selCell IsClassicalScheme k →
      WittCellTransitive H defaultP₀ selCell
        (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset)
    (hflag : flagsAt
        (spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell (spineBaseAt H defaultP₀ defaultχι₀ selCell)).step
        ((spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell
          (spineBaseAt H defaultP₀ defaultχι₀ selCell)).w n) k = true) :
    SelectedCellIsOrbit H defaultP₀ selCell
      (warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset :=
  confinement_selectedCellIsOrbit_spine_witt_classical_cell H defaultP₀ defaultχι₀ selCell
    (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done))
    done.toFinset k hn hClassify M hprim hLiebeck hWitt hflag

/-- **The FAITHFUL confinement citation bundle.** As `ConfinementCitations` but the per-node model supplies a cell `C`
+ a faithful `CellSchemeModel` on it (packaged as `Σ`), and `hLiebeck` is arity-polymorphic. Reads {G3, Liebeck, Witt,
hImprim, D0} on the faithful model. -/
structure ConfinementCitationsCell (n : Nat) where
  hn : 2 ≤ n
  IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop
  IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop
  hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme
  /-- Per node: a selected cell `C` + a FAITHFUL `CellSchemeModel` on it. -/
  M : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    Σ C : Finset (Fin n), CellSchemeModel H defaultP₀ defaultχι₀ selCell done.length C
  hprim : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    (M H done).2.S.toAssociationScheme.IsPrimitive
  /-- **Liebeck** (arity-polymorphic — the faithful form): a Cameron scheme is classical. -/
  hLiebeck : ∀ (m : Nat) (T : SchurianScheme m), IsCameronScheme m T → IsClassicalScheme m T
  /-- **Witt**: a *classical* residue's selected cell is transitive. -/
  hWitt : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    PrimRank3ClassicalCell H defaultP₀ defaultχι₀ selCell IsClassicalScheme done.length →
      WittCellTransitive H defaultP₀ selCell
        (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset
  hflag : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    flagsAt
      (spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell (spineBaseAt H defaultP₀ defaultχι₀ selCell)).step
      ((spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell
        (spineBaseAt H defaultP₀ defaultχι₀ selCell)).w n) done.length = true

/-- **`DescentConfinement` from the faithful cell bundle** — per-node application of the cell adaptor. -/
theorem descentConfinement_of_bundle_cell (C : ConfinementCitationsCell n) : DescentConfinement (n := n) :=
  fun _G H _π _hadj done =>
    selectedCellIsOrbit_done_of_capstone_cell H done done.length C.hn C.hClassify
      (C.M H done).2 (C.hprim H done) C.hLiebeck (C.hWitt H done) (C.hflag H done)

/-- **①b `canon_complete` on the FAITHFUL model.** Reuses the model-agnostic `descentCanon_complete`, fed by the cell
bundle. -/
theorem canon_complete_cell (C : ConfinementCitationsCell n) {G H : AdjMatrix n} {cG cH : Fin n → Fin n → Nat}
    (hG : descentCanonForm? G = some cG) (hH : descentCanonForm? H = some cH) :
    GraphIso G H ↔ cG = cH := by
  have hcG : cG = descentCanon G := (Option.some.inj hG).symm
  have hcH : cH = descentCanon H := (Option.some.inj hH).symm
  rw [hcG, hcH]
  exact descentCanon_complete (descentConfinement_of_bundle_cell C)

/-- **★ THE ① SHOWCASE ON THE FAITHFUL CELL MODEL — sorry-free.** Identical statement to `descentCanon_showcase`, but
`canon_complete` now rests on a residue model that genuinely classifies the selected cell (faithful, via 2-closure +
`CellActionFaithful`) rather than a cardinality-matched scheme on `Fin n`. `canon_sound` is reused unchanged
(unconditional). Citation base {G3, Liebeck, Witt, hImprim, D0} on the faithful model. -/
theorem descentCanon_showcase_cell (C : ConfinementCitationsCell n) :
    (∀ (G : AdjMatrix n) (cG : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G)
    ∧ (∀ (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → descentCanonForm? H = some cH → (GraphIso G H ↔ cG = cH)) :=
  ⟨fun _ _ h => canon_sound h, fun _ _ _ _ hG hH => canon_complete_cell C hG hH⟩

end ChainDescent.ConfinementCellComplete
