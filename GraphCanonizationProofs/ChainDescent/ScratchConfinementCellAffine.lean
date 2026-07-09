/-
# ScratchConfinementCellAffine.lean — the FIRST per-family instantiation: the affine forms cell (WIP, NOT in build.sh)

**What this does (the rebundle, made concrete).** The abstract total capstone
`confinement_selectedCellIsOrbit_spine_cell_total` (`ScratchConfinementCellImprim`) carries `hImprimTrans`
(`¬M.S.IsPrimitive → FrameSelectorTransitive`) as a per-node *parameter* — the honest "supplied at instantiation" slot.
This file is the first instantiation that **fills that slot**, for the affine forms family (`cellCard C = p^d`), and in
doing so **collapses the bundle**: `hImprimTrans` and the (previously silent) `hprim` are no longer carried — both are
**derived** from a single honest external citation, the leg-(c) **realization** fact
`SchemeRealizes f M.S (affineScheme G₀)` (exactly the object Route C carries as `hreal`, `RouteCNode4.lean:61`).

**The mechanism.** The classification (Cameron/Liebeck) says a small-Aut primitive rank-3 residue *is* one of the four
form families; for the affine-polar family that means the residue cell scheme `M.S` is realized by the standard affine
scheme `affineScheme G₀` with `G₀` acting irreducibly. That realization is the *citation* (a known true fact in a known
true form — proven outside the project by the CFSG-based classification). Given it, primitivity is **project-internal
and proven**: `irreducible_imp_isPrimitive_affineScheme` (forward-M1) + primitivity-transport along the realization
(`isPrimitive_of_realizes_affineScheme`). Primitivity then discharges `hImprimTrans` vacuously
(`hImprimTrans_of_primitive`). So the affine instantiation carries {G3, Liebeck, Witt, **realization-citation**, D0} —
with `hImprimTrans`/`hprim` *derived*, not assumed.

**The one plumbing wrinkle: arity.** `isPrimitive_of_realizes_affineScheme` is locked to `Fin (p^d)`, while a
`CellSchemeModel` lives at `Fin (cellCard C)`. The citation carries `hC : cellCard C = p^d` and states the realization
against `hC ▸ M.S`; the transport of `hne`/`IsPrimitive` across `hC` is handled by the two subst-based cast helpers
(`hne_cast` / `isPrimitive_uncast`) — bound-variable casts, trivially `subst`-able.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementCellImprim
import ChainDescent.ScratchSchemeRealizesPrimitive

namespace ChainDescent.ConfinementCellAffine

open ChainDescent
open ChainDescent.NodeCountBridge
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP4
open ChainDescent.Confinement
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Sel
open ChainDescent.ConfinementX3Recon
open ChainDescent.CanonSound
open ChainDescent.ConfinementCompleteness
open ChainDescent.ConfinementWitt
open ChainDescent.ConfinementX3Complete
open ChainDescent.ConfinementCellModel
open ChainDescent.ConfinementCellP3
open ChainDescent.ConfinementCellImprim

variable {n : Nat}

/-! ## Arity cast helpers (bound-variable casts, `subst`-trivial) -/

/-- **Transport `hne` across a vertex-count equality.** With `a`, `b` bound, `subst` collapses the cast. -/
theorem hne_cast {a b : Nat} (h : a = b) (X : SchurianScheme a)
    (hne : ∀ i : Fin (X.rank + 1), ∃ v w, X.rel i v w = true) :
    ∀ i : Fin ((h ▸ X).rank + 1), ∃ v w, (h ▸ X).rel i v w = true := by
  subst h; exact hne

/-- **Transport `IsPrimitive` back across a vertex-count equality.** -/
theorem isPrimitive_uncast {a b : Nat} (h : a = b) (X : SchurianScheme a)
    (hp : (h ▸ X).toAssociationScheme.IsPrimitive) :
    X.toAssociationScheme.IsPrimitive := by
  subst h; exact hp

/-! ## The leg-(c) realization citation + the derived primitivity -/

section Affine
variable {p d : Nat} [Fact p.Prime]
variable {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
variable {sel : Colouring n → Finset (Fin n)} {k : Nat} {C : Finset (Fin n)}

/-- **The leg-(c) citation, concretely (the classification realization).** The residue cell scheme `M.S` is realized —
via a relation-preserving bijection `f` — by the standard affine forms-graph `affineScheme G₀`, once the cell has the
matching vertex count `cellCard C = p^d`. This is Route C's `hreal` for the confinement's cell model: a known true fact
in a known true form, discharged **outside** the project by the (CFSG-based) rank-3 classification. -/
def AffineRealizedResidue (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : Prop :=
  ∃ (hC : cellCard C = p ^ d) (f : Equiv.Perm (Fin (p ^ d))),
    SchemeRealizes f (hC ▸ M.S) (affineScheme G₀ hneg)

/-- **★ Primitivity of the residue cell — DERIVED from the citation (not carried).** Composes forward-M1
(`irreducible_imp_isPrimitive_affineScheme`, via `isPrimitive_of_realizes_affineScheme`) with the arity transport.
This is the project-internal, *proven* content that the honest citation unlocks. -/
theorem isPrimitive_of_affineRealizedResidue
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    {hneg : LinearEquiv.neg (ZMod p) ∈ G₀} (hirr : G₀Irreducible G₀)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hr : AffineRealizedResidue M G₀ hneg) :
    M.S.toAssociationScheme.IsPrimitive := by
  obtain ⟨hC, f, hreal⟩ := hr
  have hprimCast : (hC ▸ M.S).toAssociationScheme.IsPrimitive :=
    isPrimitive_of_realizes_affineScheme G₀ hneg hirr hreal (hne_cast hC M.S M.hne)
  exact isPrimitive_uncast hC M.S hprimCast

/-- **★ `hImprimTrans` DERIVED from the citation (the collapse).** The realization citation yields `M.S.IsPrimitive`
(above), which discharges the `hImprimTrans` supplier vacuously (`hImprimTrans_of_primitive`). So the affine
instantiation supplies the `¬IsPrimitive`-branch input *without carrying it* — the field is gone, replaced by the
honest realization citation. -/
theorem hImprimTrans_of_affineRealizedResidue
    {χsel : Finset (Fin n) → Colouring n} {S : Finset (Fin n)}
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    {hneg : LinearEquiv.neg (ZMod p) ∈ G₀} (hirr : G₀Irreducible G₀)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hr : AffineRealizedResidue M G₀ hneg) :
    ¬ M.S.toAssociationScheme.IsPrimitive → FrameSelectorTransitive adj P₀ sel χsel S :=
  hImprimTrans_of_primitive M (isPrimitive_of_affineRealizedResidue hirr M hr)

/-! ## The capstone — the total confinement, `hImprimTrans` replaced by the realization citation -/

/-- **★ Confinement on the affine forms cell — the collapse made concrete.** Identical conclusion to
`confinement_selectedCellIsOrbit_spine_cell_total`, but the `hImprimTrans` *parameter* is replaced by the leg-(c)
**realization citation** `AffineRealizedResidue` (from which `hImprimTrans` is derived). So the imprimitive branch is
handled by the honest classification citation rather than a carried transitivity-preservation assumption. Still
wall-free (P1 excludes small-Aut from flagging); still routes both dichotomy branches to `FrameSelectorTransitive`. -/
theorem confinement_selectedCellIsOrbit_spine_cell_affine
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n) {C : Finset (Fin n)}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    {G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))}
    {hneg : LinearEquiv.neg (ZMod p) ∈ G₀} (hirr : G₀Irreducible G₀)
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : CellSchemeModel adj P₀ χι₀ sel k C)
    (hWitt : PrimRank3ClassicalCell adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hRealize : AffineRealizedResidue M G₀ hneg)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine_cell_total adj P₀ χι₀ sel χsel S k hn hClassify M hWitt
    (hImprimTrans_of_affineRealizedResidue hirr M hRealize) hflag

end Affine

/-! ## The affine bundle + the ① showcase — the collapse at the ① level

The affine forms instantiation of the total confinement bundle. The `hImprimTrans` *field* of
`ConfinementCitationsCellTotal` is replaced by the global irreducibility `hirr` + a per-node **realization citation**
`hRealize` (leg (c), carried like Route C's `hreal`); `hImprimTrans` is then *derived* per node
(`hImprimTrans_of_affineRealizedResidue`) and fed into the reused `_total` adaptor. So the ① showcase below rests on a
bundle that carries {G3, Liebeck, Witt, **realization-citation**, D0} — with `hImprimTrans`/`hprim` derived, not carried.
-/

section Bundle
variable {p d : Nat} [Fact p.Prime]
variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))
variable (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)

/-- **The affine forms confinement citation bundle.** As `ConfinementCitationsCellTotal`, but the wall-free
`hImprimTrans` supplier is replaced by the global `hirr` (`G₀Irreducible`) + a per-node **realization citation**
`hRealize` (the leg-(c) classification fact). `hImprimTrans` is derived, not carried. -/
structure ConfinementCitationsCellAffine (n : Nat) where
  hn : 2 ≤ n
  IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop
  IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop
  hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme
  /-- Per node: a selected cell `C` + a FAITHFUL `CellSchemeModel` on it. -/
  M : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    Σ C : Finset (Fin n), CellSchemeModel H defaultP₀ defaultχι₀ selCell done.length C
  /-- **`G₀` acts irreducibly** — checkable/known (`G0cyc_irreducible`, field-generation) for the affine family. -/
  hirr : G₀Irreducible G₀
  /-- **★ The leg-(c) realization citation** (replaces the carried `hImprimTrans`): each node's residue cell scheme is
  realized by the standard affine forms-graph `affineScheme G₀`. Primitivity — hence the imprimitive-branch input — is
  *derived* from this. -/
  hRealize : ∀ (H : AdjMatrix n) (done : List (Fin n)),
    AffineRealizedResidue (M H done).2 G₀ hneg
  /-- **Liebeck** (arity-polymorphic): a Cameron scheme is classical. -/
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

/-- **`DescentConfinement` from the affine bundle** — per node, derive `hImprimTrans` from the realization citation and
apply the reused total adaptor `selectedCellIsOrbit_done_of_capstone_cell_total`. -/
theorem descentConfinement_of_bundle_cell_affine (Cb : ConfinementCitationsCellAffine G₀ hneg n) :
    DescentConfinement (n := n) :=
  fun _G H _π _hadj done =>
    selectedCellIsOrbit_done_of_capstone_cell_total H done done.length Cb.hn Cb.hClassify
      (Cb.M H done).2
      (hImprimTrans_of_affineRealizedResidue Cb.hirr (Cb.M H done).2 (Cb.hRealize H done))
      Cb.hLiebeck (Cb.hWitt H done) (Cb.hflag H done)

/-- **①b `canon_complete` on the affine bundle.** -/
theorem canon_complete_cell_affine (Cb : ConfinementCitationsCellAffine G₀ hneg n)
    {G H : AdjMatrix n} {cG cH : Fin n → Fin n → Nat}
    (hG : descentCanonForm? G = some cG) (hH : descentCanonForm? H = some cH) :
    GraphIso G H ↔ cG = cH := by
  have hcG : cG = descentCanon G := (Option.some.inj hG).symm
  have hcH : cH = descentCanon H := (Option.some.inj hH).symm
  rw [hcG, hcH]
  exact descentCanon_complete (descentConfinement_of_bundle_cell_affine G₀ hneg Cb)

/-- **★ THE ① SHOWCASE ON THE AFFINE FORMS CELL — the collapse at the ① level, sorry-free.** Identical statement to
`descentCanon_showcase_cell_total`, but `canon_complete` rests on the affine bundle, whose imprimitive-branch input is
*derived* from the leg-(c) realization citation rather than carried. Citation base {G3, Liebeck, Witt,
realization-citation, D0}. -/
theorem descentCanon_showcase_cell_affine (Cb : ConfinementCitationsCellAffine G₀ hneg n) :
    (∀ (G : AdjMatrix n) (cG : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G)
    ∧ (∀ (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
        descentCanonForm? G = some cG → descentCanonForm? H = some cH → (GraphIso G H ↔ cG = cH)) :=
  ⟨fun _ _ h => canon_sound h, fun _ _ _ _ hG hH => canon_complete_cell_affine G₀ hneg Cb hG hH⟩

end Bundle

end ChainDescent.ConfinementCellAffine
