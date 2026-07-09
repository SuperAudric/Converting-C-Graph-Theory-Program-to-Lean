/-
# ScratchConfinementCellImprim.lean — the ¬IsPrimitive branch, WALL-FREE + the TOTAL ① showcase (WIP, NOT in build.sh)

**What this does.** Makes the confinement **total** in the primitivity dimension: it removes the *silent* `hprim`
assumption (which the discharged spine `confinement_selectedCellIsOrbit_spine_cell_discharged` and the whole
`descentCanon_showcase_cell` chain still carry) and replaces it with Piece 1's **proved** dichotomy
`¬IsPrimitive ∨ Cameron` (`cellResidue_imprimitive_or_cameron`), routing each branch to `FrameSelectorTransitive`
and thence to `SelectedCellIsOrbit`. The payoff is `descentCanon_showcase_cell_total` — the ① showcase (sound ∧
complete) on the faithful cell model with **no silent `hprim`**.

**Why it is wall-free (the load-bearing point).** `FrameSelectorTransitive` is "the residual group `StabilizerAt S`
acts **transitively** on the selected cell" — a property of the group ACTION (`OrbitPartition` = a real descent
automorphism), **NOT** a claim that 1-WL *reaches* the orbit partition. `ConfinementP4`'s doc-comment (lines 77-84)
states this explicitly: transitivity "sidesteps the multi-base `JointProfileRecoversAt` wall — that wall is 1-WL
reaching orbits; transitivity is a property of the group action itself." So routing the ¬IsPrimitive branch through
its own `FrameSelectorTransitive` supplier (`hImprimTrans`) **never touches** `BlockRefinementVisible` /
`cell_splits_of_imprimitive` (= the WL-dimension wall = `hSmallAutThin`). The former Piece-2 routing through
`cell_splits_of_imprimitive` was a wall-reintroduction and is discarded (remaining-work.md §1, 2026-07-09).

**Faithfulness (two distinct family citations, not one compound).** The two branches are supplied by two *separate*,
honestly-scoped inputs, mirroring the classicality split (Liebeck vs Witt):
  · `hWitt` : `classical`-cell ⟹ `WittCellTransitive` — Witt flag-transitivity (forms families).
  · `hImprimTrans` : `¬IsPrimitive` ⟹ `FrameSelectorTransitive` — an imprimitive schurian residue is still
    vertex-transitive, so its residual group is cell-transitive (transitivity-PRESERVATION; `schemeBlocks_transitive`
    + `schemeBlock_fiber_transitive`, both `haveI := schemeAutGroup_isPretransitive S`). For the handled forms
    families this branch is **vacuous** (the residue is primitive rank-3); it is carried so the confinement is TOTAL
    (no silent `hprim`) without conceding anything.

The two hypotheses have the **same downstream status** as `hWitt`/`isotropic_span`: family-dischargeable, off the
critical path, never the wall.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementCellComplete

namespace ChainDescent.ConfinementCellImprim

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Sel
open ChainDescent.ConfinementX3Recon
open ChainDescent.NodeCountBridge
open ChainDescent.CanonSound
open ChainDescent.ConfinementCompleteness
open ChainDescent.ConfinementWitt
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP4
open ChainDescent.Confinement
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle
open ChainDescent.ConfinementCellModel
open ChainDescent.ConfinementCellP3
open ChainDescent.ConfinementCellWitt
open ChainDescent.ConfinementX3Complete

variable {n : Nat}

/-! ## The wall-free tail + the total spine capstone -/

/-- **The `FrameSelectorTransitive → SelectedCellIsOrbit` tail** (extracted from `confinement_selectedCellIsOrbit`,
`ScratchConfinement` lines 107-109). Given the residual group is transitive on the selected cell at base `S`, the
selected cell sits in a single `Stab(S)`-orbit, hence any two same-colour cell vertices are orbit-equivalent.
Wall-free (`ConfinementP4` lines 77-84): a group-action fact, not a 1-WL-reaches-orbits claim. -/
theorem selectedCellIsOrbit_of_frameSelectorTransitive
    {adj : AdjMatrix n} {P₀ : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    {S : Finset (Fin n)}
    (hFST : FrameSelectorTransitive adj P₀ sel χsel S) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  selectedCellIsOrbit_of_subsetOrbit
    (selectedCellSubsetOrbitAt_of_frameSelectorTransitive hFST S (Finset.Subset.refl S))

/-- **★ Confinement on the faithful cell model — TOTAL in primitivity, WALL-FREE.** The silent `hprim` of
`confinement_selectedCellIsOrbit_spine_cell_discharged` is GONE: a Phase-1 flag makes the residue cell provably
`¬IsPrimitive ∨ Cameron` (Piece 1, `cellResidue_imprimitive_or_cameron`, using flag-largeness to kill `¬IsLarge`),
and BOTH branches reach `FrameSelectorTransitive` — Cameron via `hWitt`, imprimitive via `hImprimTrans`
(transitivity-preservation). The `FST → SelectedCellIsOrbit` tail is the same wall-free group-action bridge the
Cameron path already used. NO `BlockRefinementVisible`, NO `cell_splits_of_imprimitive`, NO `hSmallAutThin`. -/
theorem confinement_selectedCellIsOrbit_spine_cell_total
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hWitt : PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hImprimTrans : ¬ M.S.toAssociationScheme.IsPrimitive →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S := by
  -- flag ⟹ super-poly residual (P1) ⟹ the residue cell is large
  have hlarge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k :=
    flag_imp_pow_baseMax_lt adj P₀ χι₀ sel k hn hflag
  -- Piece 1: the flagging residue cell is provably ¬IsPrimitive ∨ Cameron (¬IsLarge killed by hlarge)
  have hdich := cellResidue_imprimitive_or_cameron adj P₀ χι₀ sel k hClassify M hlarge
  -- route BOTH branches to FrameSelectorTransitive (never through BlockRefinementVisible)
  have hFST : FrameSelectorTransitive adj P₀ sel χsel S := by
    rcases hdich with himprim | hcam
    · exact hImprimTrans himprim
    · exact hWitt ⟨C, M, hcam⟩
  exact selectedCellIsOrbit_of_frameSelectorTransitive hFST

/-- **`hImprimTrans` from primitivity (the vacuous discharge).** When the residue cell scheme is *provably*
primitive, the ¬IsPrimitive branch never fires, so `hImprimTrans` holds vacuously. For the affine/forms families
primitivity is a theorem — `ScratchAffinePrimitive.irreducible_imp_isPrimitive_affineScheme` (forward-M1,
`G₀Irreducible → IsPrimitive(affineScheme)`) supplies it — so feeding this into `confinement_selectedCellIsOrbit_spine_cell_total`
discharges the imprimitive branch outright for that class (modulo the `M.S`↔`affineScheme` seam). -/
theorem hImprimTrans_of_primitive
    {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    {S : Finset (Fin n)} {k : Nat} {C : Finset (Fin n)}
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hprim : M.S.toAssociationScheme.IsPrimitive) :
    ¬ M.S.toAssociationScheme.IsPrimitive → FrameSelectorTransitive adj P₀ sel χsel S :=
  fun himp => absurd hprim himp

/-! ## The classicality-threaded total Witt layer -/

/-- **★ Confinement on the faithful cell model, classicality-threaded + TOTAL.** Mirrors
`confinement_selectedCellIsOrbit_spine_witt_classical_cell` but drops `hprim` for `hImprimTrans` and routes through
the total capstone. The compound Cameron⟹cell-transitive supplier is composed from `hLiebeck` (Cameron ⟹ classical,
arity-poly) + `hWitt` (classical ⟹ `WittCellTransitive`) + `frameSelectorTransitive_of_wittCellTransitive`. -/
theorem confinement_selectedCellIsOrbit_spine_witt_classical_cell_total (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hImprimTrans : ¬ M.S.toAssociationScheme.IsPrimitive →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hLiebeck : ∀ (m : Nat) (T : SchurianScheme m), IsCameronScheme m T → IsClassicalScheme m T)
    (hWitt : PrimRank3ClassicalCell adj P₀ χι₀ sel IsClassicalScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact confinement_selectedCellIsOrbit_spine_cell_total adj P₀ χι₀ sel χsel S k hn hClassify M
    (fun hCam => frameSelectorTransitive_of_wittCellTransitive (hWitt (by
      obtain ⟨C', M', hcam⟩ := hCam
      exact ⟨C', M', hLiebeck (cellCard C') M'.S hcam⟩)))
    hImprimTrans hflag

/-! ## The TOTAL bundle + ① showcase -/

/-- **W4.3 adaptor on the TOTAL cell capstone** (list-indexed, mirror of `selectedCellIsOrbit_done_of_capstone_cell`
with `hprim` replaced by `hImprimTrans`). -/
theorem selectedCellIsOrbit_done_of_capstone_cell_total (H : AdjMatrix n) (done : List (Fin n)) (k : Nat)
    (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel H defaultP₀ defaultχι₀ selCell k C)
    (hImprimTrans : ¬ M.S.toAssociationScheme.IsPrimitive →
      FrameSelectorTransitive H defaultP₀ selCell
        (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset)
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
  confinement_selectedCellIsOrbit_spine_witt_classical_cell_total H defaultP₀ defaultχι₀ selCell
    (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done))
    done.toFinset k hn hClassify M hImprimTrans hLiebeck hWitt hflag

/-- **The TOTAL faithful confinement citation bundle.** As `ConfinementCitationsCell` but the silent `hprim` is
replaced by `hImprimTrans` (the wall-free ¬IsPrimitive⟹cell-transitive supplier). Reads {G3, Liebeck, Witt,
`hImprimTrans`, D0} on the faithful model — no silent primitivity assumption. -/
structure ConfinementCitationsCellTotal (n : Nat) where
  hn : 2 ≤ n
  IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop
  IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop
  hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme
  /-- Per node: a selected cell `C` + a FAITHFUL `CellSchemeModel` on it. -/
  M : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    Σ C : Finset (Fin n), CellSchemeModel H defaultP₀ defaultχι₀ selCell done.length C
  /-- **The wall-free ¬IsPrimitive supplier** (replaces the silent `hprim`): an imprimitive residue cell is still
  transitive, so its residual group is cell-transitive. Vacuous on the primitive rank-3 forms families. -/
  hImprimTrans : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    ¬ (M H done).2.S.toAssociationScheme.IsPrimitive →
      FrameSelectorTransitive H defaultP₀ selCell
        (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset
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

/-- **`DescentConfinement` from the TOTAL faithful cell bundle** — per-node application of the total cell adaptor. -/
theorem descentConfinement_of_bundle_cell_total (C : ConfinementCitationsCellTotal n) :
    DescentConfinement (n := n) :=
  fun _G H _π _hadj done =>
    selectedCellIsOrbit_done_of_capstone_cell_total H done done.length C.hn C.hClassify
      (C.M H done).2 (C.hImprimTrans H done) C.hLiebeck (C.hWitt H done) (C.hflag H done)

/-- **①b `canon_complete` on the TOTAL faithful model.** Reuses the model-agnostic `descentCanon_complete`, fed by
the total cell bundle. -/
theorem canon_complete_cell_total (C : ConfinementCitationsCellTotal n) {G H : AdjMatrix n}
    {cG cH : Fin n → Fin n → Nat}
    (hG : descentCanonForm? G = some cG) (hH : descentCanonForm? H = some cH) :
    GraphIso G H ↔ cG = cH := by
  have hcG : cG = descentCanon G := (Option.some.inj hG).symm
  have hcH : cH = descentCanon H := (Option.some.inj hH).symm
  rw [hcG, hcH]
  exact descentCanon_complete (descentConfinement_of_bundle_cell_total C)

/-- **★ THE ① SHOWCASE ON THE FAITHFUL CELL MODEL — TOTAL, sorry-free.** Identical statement to
`descentCanon_showcase_cell`, but `canon_complete` rests on the TOTAL confinement (no silent `hprim`): the
¬IsPrimitive branch is handled wall-free by `hImprimTrans`. `canon_sound` is reused unchanged (unconditional).
Citation base {G3, Liebeck, Witt, `hImprimTrans`, D0} on the faithful model. -/
theorem descentCanon_showcase_cell_total (C : ConfinementCitationsCellTotal n) :
    (∀ (G : AdjMatrix n) (cG : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G)
    ∧ (∀ (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → descentCanonForm? H = some cH → (GraphIso G H ↔ cG = cH)) :=
  ⟨fun _ _ h => canon_sound h, fun _ _ _ _ hG hH => canon_complete_cell_total C hG hH⟩

end ChainDescent.ConfinementCellImprim
