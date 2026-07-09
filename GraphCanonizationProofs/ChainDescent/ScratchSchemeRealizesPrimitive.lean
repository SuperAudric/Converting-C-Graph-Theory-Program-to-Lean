/-
# ScratchSchemeRealizesPrimitive.lean — primitivity transports along `SchemeRealizes` (WIP, NOT in build.sh)

**What this proves.** `IsPrimitive` transports along a scheme realization (`SchemeRealizes f S X` = a
relation-preserving bijection `f : S ≅ X`, `RouteCTransport.lean`). This is the **primitivity leg of the item-2 seam**:
the confinement recovers the descent residue `S` as `SchemeRealizes f S (affineScheme G₀)` (carried exactly like Route
C's `hreal`), and `irreducible_imp_isPrimitive_affineScheme` (forward-M1) gives `IsPrimitive(affineScheme G₀)`; this
lemma transports that to `S.IsPrimitive`, which discharges the confinement's `hImprimTrans` vacuously
(`hImprimTrans_of_primitive`).

**Method (group route, no `Fin (rank+1)` dependent types).** `SchemeRealizes` gives
`(S.relOfPair v w).val = (X.relOfPair (f v)(f w)).val`, hence a conjugation iso `π ↦ f π f⁻¹ :
S.SchemeAutGroup ≅ X.SchemeAutGroup` intertwined by `f`. Preprimitivity transports along that equivariant bijection
(`MulAction.isPreprimitive_congr`), and `isPreprimitive_iff_isPrimitive` bridges to `IsPrimitive` on both ends.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.CascadeAffine
import ChainDescent.RouteCTransport
import ChainDescent.ScratchAffinePrimitive

namespace ChainDescent

open MulAction

variable {n : Nat}

/-- **Primitivity transports along a scheme realization.** If `f` realizes `S ≅ X` (relation-preserving) and `X` is
primitive, then `S` is primitive. Both schemes need every relation to occur (`hneS`/`hneX`) — the schurian hypothesis
of `isPreprimitive_iff_isPrimitive`. -/
theorem isPrimitive_of_schemeRealizes {f : Equiv.Perm (Fin n)} {S X : SchurianScheme n}
    (hreal : SchemeRealizes f S X)
    (hneS : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true)
    (hneX : ∀ i : Fin (X.rank + 1), ∃ v w, X.rel i v w = true)
    (hX : X.toAssociationScheme.IsPrimitive) :
    S.toAssociationScheme.IsPrimitive := by
  -- perm-inverse cancellation helpers
  have hff : ∀ x, f (f⁻¹ x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hf'f : ∀ x, f⁻¹ (f x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  -- the relation-index values agree under `f`
  have hval : ∀ v w, (S.toAssociationScheme.relOfPair v w).val
      = (X.toAssociationScheme.relOfPair (f v) (f w)).val := fun v w => hreal v w
  -- "same relation" transports across `f`
  have hrel_iff : ∀ a b x y : Fin n,
      (X.toAssociationScheme.relOfPair (f a) (f b) = X.toAssociationScheme.relOfPair (f x) (f y))
      ↔ (S.toAssociationScheme.relOfPair a b = S.toAssociationScheme.relOfPair x y) := by
    intro a b x y
    rw [Fin.ext_iff, Fin.ext_iff, ← hval a b, ← hval x y]
  -- the conjugation `π ↦ f π f⁻¹` is a bijection `S.SchemeAutGroup ≅ X.SchemeAutGroup`
  have hIff : ∀ π : Equiv.Perm (Fin n),
      IsSchemeAut S.toAssociationScheme π ↔ IsSchemeAut X.toAssociationScheme (f * π * f⁻¹) := by
    intro π
    constructor
    · intro hπ
      apply isSchemeAut_of_relOfPair_eq
      intro a b
      have e1 : (f * π * f⁻¹) a = f (π (f⁻¹ a)) := by simp [Equiv.Perm.mul_apply]
      have e2 : (f * π * f⁻¹) b = f (π (f⁻¹ b)) := by simp [Equiv.Perm.mul_apply]
      have key : X.toAssociationScheme.relOfPair (f (π (f⁻¹ a))) (f (π (f⁻¹ b)))
          = X.toAssociationScheme.relOfPair (f (f⁻¹ a)) (f (f⁻¹ b)) :=
        (hrel_iff (π (f⁻¹ a)) (π (f⁻¹ b)) (f⁻¹ a) (f⁻¹ b)).mpr (hπ.relOfPair_eq (f⁻¹ a) (f⁻¹ b))
      rw [e1, e2, key, hff a, hff b]
    · intro hσ
      apply isSchemeAut_of_relOfPair_eq
      intro a b
      have hXeq : X.toAssociationScheme.relOfPair (f (π a)) (f (π b))
          = X.toAssociationScheme.relOfPair (f a) (f b) := by
        have h := hσ.relOfPair_eq (f a) (f b)
        simpa [Equiv.Perm.mul_apply, hf'f] using h
      exact (hrel_iff (π a) (π b) a b).mp hXeq
  -- the conjugation as a map `S.SchemeAutGroup → X.SchemeAutGroup`
  let φ : S.toAssociationScheme.SchemeAutGroup → X.toAssociationScheme.SchemeAutGroup :=
    fun π => ⟨f * (π : Equiv.Perm (Fin n)) * f⁻¹, (hIff (π : Equiv.Perm (Fin n))).mp π.2⟩
  have hφsurj : Function.Surjective φ := by
    intro σ
    refine ⟨⟨f⁻¹ * (σ : Equiv.Perm (Fin n)) * f, ?_⟩, ?_⟩
    · apply (hIff (f⁻¹ * (σ : Equiv.Perm (Fin n)) * f)).mpr
      have hconj : f * (f⁻¹ * (σ : Equiv.Perm (Fin n)) * f) * f⁻¹ = (σ : Equiv.Perm (Fin n)) := by
        group
      rw [hconj]; exact σ.2
    · apply Subtype.ext
      show f * (f⁻¹ * (σ : Equiv.Perm (Fin n)) * f) * f⁻¹ = (σ : Equiv.Perm (Fin n))
      group
  -- the equivariant bijection `f : (Fin n) →ₑ[φ] (Fin n)`
  let F : (Fin n) →ₑ[φ] (Fin n) :=
    { toFun := f
      map_smul' := fun π v => by
        show f ((π : Equiv.Perm (Fin n)) v)
          = (f * (π : Equiv.Perm (Fin n)) * f⁻¹) (f v)
        simp [Equiv.Perm.mul_apply, hf'f] }
  -- transport preprimitivity, then bridge to primitivity
  have hFbij : Function.Bijective (F : Fin n → Fin n) := f.bijective
  exact (isPreprimitive_iff_isPrimitive S hneS).mp
    ((isPreprimitive_congr (f := F) hφsurj hFbij).mpr
      ((isPreprimitive_iff_isPrimitive X hneX).mpr hX))

/-! ## The affine corollary — the seam's primitivity leg, end-to-end -/

section Affine
variable {p d : ℕ} [Fact p.Prime]
variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- **Every relation of `affineScheme` occurs** — the orbital scheme's `hne` (free via `orbMk_out`). -/
theorem affineScheme_hne (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) :
    ∀ k : Fin ((affineScheme G₀ hneg).rank + 1), ∃ v w, (affineScheme G₀ hneg).rel k v w = true :=
  fun k => ⟨_, _, (affineScheme_rel_iff G₀ hneg).mpr
    (orbMk_out (affineG G₀) (orbitalIdx (affineG G₀) k)).symm⟩

/-- **★ The seam's primitivity leg, end-to-end.** The recovered descent residue `S` — realized as `affineScheme G₀`
(carried exactly like Route C's `hreal`) with `G₀` acting **irreducibly** — is **primitive**. Composes forward-M1
(`irreducible_imp_isPrimitive_affineScheme`) with primitivity-transport along the realization. This is what
discharges the confinement's `hImprimTrans` vacuously for the affine/forms residue class (`hImprimTrans_of_primitive`).
`hneS` = "every relation of `S` occurs", free from `S`'s own model (`ResidueSchemeModel.hne`). -/
theorem isPrimitive_of_realizes_affineScheme
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (hirr : G₀Irreducible G₀)
    {f : Equiv.Perm (Fin (p ^ d))} {S : SchurianScheme (p ^ d)}
    (hreal : SchemeRealizes f S (affineScheme G₀ hneg))
    (hneS : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true) :
    S.toAssociationScheme.IsPrimitive :=
  isPrimitive_of_schemeRealizes hreal hneS (affineScheme_hne G₀ hneg)
    (irreducible_imp_isPrimitive_affineScheme G₀ hneg hirr)

end Affine

end ChainDescent
