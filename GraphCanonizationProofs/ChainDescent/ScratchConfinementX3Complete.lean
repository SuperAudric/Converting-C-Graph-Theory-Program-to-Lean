/-
# ScratchConfinementX3Complete.lean — W4 pieces 2+3: ①b on the index-free descent (WIP, NOT in build.sh)

**What this file does.** W3 produced the two exports the assembly needs — `reconcile_descent_top` (the reconciling
automorphism) and `descentPicks_leaf_univ` (leaf discreteness) — and W4.1 (`descentLeaf_canonForm_iso_invariant`, in
`ScratchConfinementX3Recon`) composed them through `ifCanon_iso_invariant_of_reconcile` into "iso ⟹ equal descent-leaf
canonical form". This file **rewires ①b (`canon_complete`) onto that index-free descent** (W4.2) and states the one
remaining input as a named obligation (W4.3).

**Why a new canonical form.** The existing `canonForm?`/`dChain` (`ConfinementCompleteness`) is built on the
*index-based* `IndivStep.default` set-individualization; its → residual `CanonFormImagesIsoInvariant` is FALSE (the
index leaks when `D ≠ ∅`). The index-free descent (`descentPicks` + `indivStep1`, ordered by descent level not `v.val`)
is exactly the fix: its leaf canonical form `descentCanon` is genuinely iso-invariant (W4.1). So ①b is re-proved for
`descentCanon`, not `canonForm?`.

**The two directions.**
  · **← (`descentCanon_iso_of_eq`)** — equal canonical forms ⟹ isomorphic, from ①a-for-free (`descentCanon` is
    literally `labelledAdj (rankPerm …) adj`, a relabelling) + `iso_of_labelledAdj_eq` (banked).
  · **→ (`descentCanon_eq_of_iso`)** — isomorphic ⟹ equal, = W4.1, modulo the confinement hypothesis `DescentConfinement`.
The default parameters make the side conditions trivial: `defaultP₀ = fun _ _ => POE.unknown` (relabel-invariant) and
`defaultχι₀ = fun _ => 0` (constant), so `hisoP`/`hχιconst` are `rfl`.

**W4.3 — the remaining input `DescentConfinement`.** The confinement capstone
(`ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt`) delivers `SelectedCellIsOrbit` per *Finset* base; the
descent's colouring is indexed by an *ordered list* `done`. `DescentConfinement` is the list-indexed form the assembly
consumes; wiring it to the Finset-indexed capstone (`done.toFinset` adaptor) is the honest remaining seam, stated here.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Recon
import ChainDescent.ScratchConfinementCompleteness

namespace ChainDescent.ConfinementX3Complete

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

variable {n : Nat}

/-! ## W4.2 — the index-free descent canonical form and its ①b -/

/-- **The index-free descent canonical form.** Run the `selCell`-descent from the constant seed to its discrete leaf
(fuel `n`), then read off the canonical labelling `labelledAdj (rankPerm leaf) adj`. This is the iso-invariant
replacement for `dCanonForm` (whose index-based descent is not iso-invariant). -/
noncomputable def descentCanon (adj : AdjMatrix n) : Fin n → Fin n → Nat :=
  labelledAdj (Colouring.rankPerm
      (warmRefine adj defaultP₀ (descentColouring adj defaultP₀ defaultχι₀ (descentPicks adj defaultP₀ n defaultχι₀)))
      (descentPicks_leaf_univ adj defaultP₀ defaultχι₀)) adj

/-- **①a for `descentCanon` (soundness, for free).** The canonical form is a relabelling of the input — it is literally
`labelledAdj π adj` for the rank permutation `π`. So a `descentCanon` output always exhibits the input up to relabel. -/
theorem descentCanon_sound (adj : AdjMatrix n) :
    ∃ π : Equiv.Perm (Fin n), labelledAdj π adj = descentCanon adj :=
  ⟨_, rfl⟩

/-- **①b ← direction.** Equal canonical forms force the inputs isomorphic — both are `labelledAdj (rankPerm …) ·`, so
`iso_of_labelledAdj_eq` (banked) applies directly. Needs no confinement. -/
theorem descentCanon_iso_of_eq {G H : AdjMatrix n} (h : descentCanon G = descentCanon H) :
    GraphIso G H :=
  iso_of_labelledAdj_eq h

/-- **W4.3 — the confinement input (list-indexed).** For every iso `π : G → H`, confinement holds at every ordered
descent base `done` of the `H`-descent: the selected cell is one `Stab`-orbit. This is the list-indexed form the
reconciliation induction consumes (the descent colouring depends on the *ordered* list `done`); it is discharged by the
Finset-indexed confinement capstone via the `done.toFinset` adaptor (the remaining seam). -/
def DescentConfinement : Prop :=
  ∀ (G H : AdjMatrix n) (π : Equiv.Perm (Fin n)),
    (∀ v w, H.adj (π v) (π w) = G.adj v w) →
    ∀ done : List (Fin n),
      SelectedCellIsOrbit H defaultP₀ selCell
        (warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset

/-- **①b → direction, modulo `DescentConfinement`.** Isomorphic inputs get equal canonical forms — exactly W4.1
(`descentLeaf_canonForm_iso_invariant`) with the default (constant) parameters, so the `hisoP`/`hχιconst` side
conditions are `rfl`. -/
theorem descentCanon_eq_of_iso (hConf : DescentConfinement (n := n))
    {G H : AdjMatrix n} (hiso : GraphIso G H) :
    descentCanon G = descentCanon H := by
  obtain ⟨π, hπ⟩ := hiso
  have hadj : ∀ v w, H.adj (π v) (π w) = G.adj v w := by
    intro v w
    have h1 := congrFun (congrFun hπ (π v)) (π w)
    simp only [labelledAdj, Equiv.symm_apply_apply] at h1
    exact h1.symm
  exact (descentLeaf_canonForm_iso_invariant hadj (fun _ _ => rfl) (fun _ _ => rfl)
    (hConf G H π hadj)
    (descentPicks_leaf_univ G defaultP₀ defaultχι₀)
    (descentPicks_leaf_univ H defaultP₀ defaultχι₀)).symm

/-- **★ ①b for the index-free descent — `canon_complete`, modulo `DescentConfinement`.** The descent canonizer is a
complete iso-invariant: `GraphIso G H ↔ descentCanon G = descentCanon H`. The ← direction is unconditional; the →
direction is the W3 reconciliation (W4.1) fed by the confinement hypothesis. This is the ①b→ that the old
`canonForm?_complete` could only pin to a *false* residual — now on the correct (index-free) object. -/
theorem descentCanon_complete (hConf : DescentConfinement (n := n)) {G H : AdjMatrix n} :
    GraphIso G H ↔ descentCanon G = descentCanon H :=
  ⟨descentCanon_eq_of_iso hConf, descentCanon_iso_of_eq⟩

/-! ## W4.3 — the list-indexed ⇐ Finset-indexed confinement adaptor

The confinement capstone `confinement_selectedCellIsOrbit_spine_witt` is parametrized by an *abstract*
`χsel : Finset → Colouring` and delivers `SelectedCellIsOrbit … (χsel S) S` at a *Finset* base `S`. The descent
colouring, by contrast, depends on the *ordered* list `done`. The mismatch dissolves: for a fixed `done`, instantiate
`χsel` at the **constant** function returning the descent colouring of `done`, and take `S := done.toFinset`. Then
`χsel S` beta-reduces (definitionally) to exactly the list-indexed colouring — so the capstone's conclusion IS the
`DescentConfinement` per-`done` statement, with no reindexing. What remains are the capstone's *carried citations*
(`hClassify` = G3, `M` = the D0 model, `hprim` = hImprim, `hCitation` = Witt+Liebeck, `hflag` = the flagging-regime
witness) — i.e. `DescentConfinement` reduces to supplying these at each descent node, exactly the named residual, not a
reindexing obstruction. -/

/-- **★ W4.3 — the adaptor.** The Finset-indexed confinement capstone, instantiated at the constant `χsel` and
`S := done.toFinset`, yields the list-indexed per-`done` `SelectedCellIsOrbit` that `DescentConfinement` /
`reconcile_descent` consume. Proof: a direct call to `confinement_selectedCellIsOrbit_spine_witt` with
`χsel := fun _ => (the descent colouring of done)`; the conclusion beta-reduces to the target. The remaining
hypotheses are precisely the confinement citations {G3, D0 model, hImprim, Witt+Liebeck} + the flag witness. -/
theorem selectedCellIsOrbit_done_of_capstone (H : AdjMatrix n) (done : List (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel H defaultP₀ defaultχι₀ selCell k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hCitation : PrimRank3Classical H defaultP₀ defaultχι₀ selCell IsCameronScheme k →
      WittCellTransitive H defaultP₀ selCell
        (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset)
    (hflag : flagsAt
        (spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell (spineBaseAt H defaultP₀ defaultχι₀ selCell)).step
        ((spineCappedCanonizerO H defaultP₀ defaultχι₀ selCell
          (spineBaseAt H defaultP₀ defaultχι₀ selCell)).w n) k = true) :
    SelectedCellIsOrbit H defaultP₀ selCell
      (warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done)) done.toFinset :=
  confinement_selectedCellIsOrbit_spine_witt H defaultP₀ defaultχι₀ selCell
    (fun _ => warmRefine H defaultP₀ (descentColouring H defaultP₀ defaultχι₀ done))
    done.toFinset k hn hClassify M hprim hCitation hflag

end ChainDescent.ConfinementX3Complete
