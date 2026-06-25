/-
# SEAM SPIKE — does the abstract residue route to a concrete forms-graph and close the seal?

The per-family capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` concludes the seal disjunction for the
**concrete** `affineScheme (similitudeGroup Q)`. The canonizer's residue is an **abstract** `S : SchurianScheme (p^d)`
that the cited classification (Skresanov/Liebeck/Cameron) places as `≅ affineScheme(Q)` for one of the named forms.
This spike asks: **does the seam close architecturally**, and if so what is the single new obligation?

Verdict (this file compiles axiom-clean): **YES — the seam closes, and it reduces to exactly ONE new obligation, the
transport `htransport`:** the seal disjunction is invariant under a realizing permutation `f : Fin (p^d) ≃ Fin (p^d)`
with `schemeAdj S v w = schemeAdj X (f v) (f w)`. Everything else is the cited classification (`hclass`, a faithful
"`S` is Cameron, or `≅` a forms-graph family") + the landed per-family `wittFree` capstone.

Why this is bounded, not a wall: all four disjuncts (`SchemeBlockRecovered`/`AbelianConsumed`/`SchemeRecoveredByDepth`/
`IsCameronScheme`) are defined purely through `schemeAdj` + `IsAut`/`IsBase`, and `f` *conjugates* those
(`isAut_schemeAdj_iff` already shows adjacency-auts = scheme-auts). So `htransport` factors through a small core —
`IsAut`/`IsBase` conjugation under `f` — replicated across the disjuncts; `IsCameronScheme` (a free predicate) only has
to be *instantiated* iso-invariantly. This is option (b) of AUDIT-S finding 3 (build the transport), and it should be
**proved**, not hidden inside the citation (option (a) would make `hclass` assert a non-trivial transport as an axiom,
breaking the faithful-citation bar). The `AlgIso.InducedBy f` object already encodes "iso realized by `f`", so the
primitive exists; only the disjunct-transport lemmas are new.

NOT in build (scratch; `lake env lean ChainDescent/ScratchSeam.lean`).
-/
import ChainDescent.CascadeAffine

namespace ChainDescent

open scoped Classical

variable {p d : ℕ} [Fact p.Prime]

/-- A permutation `f` **realizes** the scheme iso `S ≅ X` if it preserves the labelled adjacency (`schemeAdj`).
By `isAut_schemeAdj_iff` this is exactly a relation-preserving bijection — the combinatorial scheme iso the cited
classification supplies (the `AlgIso.InducedBy f` data). -/
def SchemeRealizes {n : Nat} (f : Equiv.Perm (Fin n)) (S X : SchurianScheme n) : Prop :=
  ∀ v w, (schemeAdj S.toAssociationScheme).adj v w = (schemeAdj X.toAssociationScheme).adj (f v) (f w)

/-- The seal disjunction for a scheme `X` (the conclusion shape of `…viaIsotropySeparates_wittFree`), with the free
`IsCameronScheme` predicate and depth `bound` as parameters. -/
def SealDisj (IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop) (bound : Nat)
    {n : Nat} (X : SchurianScheme n) : Prop :=
  ((SchemeBlockRecovered n X ∨ AbelianConsumed n X) ∨ SchemeRecoveredByDepth n X bound)
    ∨ IsCameronScheme n X

/-- **THE SEAM (spike).** The abstract residue `S` reaches the seal disjunction, given (C) the cited rank-3-affine
classification — `S` is Cameron, or `≅` a forms-graph family `affineScheme(Q)` (via a realizing `f`) with the per-family
separation certificate `IsotropySeparatesAtBase Q T` — and (T) the transport obligation that the disjunction is
invariant along a realizing permutation. The forms-graph case is discharged by the landed
`reachesRigidOrCameron_viaIsotropySeparates_wittFree`, then transported back to `S`. This compiles ⟹ the architecture is
sound; the only NEW content beyond citations + the landed per-family route is `htransport`. -/
theorem reachesRigidOrCameron_viaSchurianRank3Affine
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (S : SchurianScheme (p ^ d))
    (htransport : ∀ (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (f : Equiv.Perm (Fin (p ^ d))),
        SchemeRealizes f S (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) →
        SealDisj IsCameronScheme bound
            (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) →
        SealDisj IsCameronScheme bound S)
    (hclass : IsCameronScheme (p ^ d) S ∨
        ∃ (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (T : Finset (Fin (p ^ d)))
          (f : Equiv.Perm (Fin (p ^ d))),
          T.card ≤ bound ∧ IsotropySeparatesAtBase Q T ∧
          SchemeRealizes f S (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))) :
    SealDisj IsCameronScheme bound S := by
  rcases hclass with hcam | ⟨Q, T, f, hT, hIso, hreal⟩
  · exact Or.inr hcam
  · exact htransport Q f hreal (reachesRigidOrCameron_viaIsotropySeparates_wittFree Q T hT hIso)

end ChainDescent

#print axioms ChainDescent.reachesRigidOrCameron_viaSchurianRank3Affine
