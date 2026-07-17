/-
# ImprimitiveDischarge.lean — the `hImprim` resolution layer

**What this is.** The seal capstones (`reachesRigidOrCameron_*`, `Cascade.lean`/`CascadeAffine.lean`) carry
`hImprim : ¬ IsPrimitive → SchemeBlockRecovered ∨ AbelianConsumed` — the imprimitive branch — undischarged.
This file supplies the two discharge legs that exist on known math, and the first *inhabited* instances of
both target predicates:

1. **§1 — forward M1 (`irreducible_imp_isPrimitive_affineScheme`).** `G₀` irreducible ⟹ `affineScheme G₀`
   primitive — the genuine dual of the landed `isPrimitive_affineScheme_imp_irreducible` (`CascadeAffine.lean`),
   completing the intended M1 ⟺. Ported from `ScratchAffinePrimitive.lean` (2026-07-17; the scratch file is
   retired — this is its build home).
2. **§2 — the vacuous discharge on the irreducible-affine class.** `hImprim_affine_of_irreducible` makes the
   seal's `hImprim` a *theorem* wherever `G₀` acts irreducibly (the antecedent `¬IsPrimitive` is false), with
   concrete instantiations at the two in-build irreducibility witnesses (`G0cyc_irreducible`,
   `G0pow_irreducible_of_adjoin` — the genuine cyclotomic slice), and the capstone
   `reachesRigidOrCameron_viaAffineIrreducible_prim`: the affine-irreducible seal with `hImprim` **removed**
   (carried set shrinks from `{G3, hbound, hImprim}` to `{G3, hbound}`).
3. **§3 — the leg-B witness (`translationScheme`).** The elementary-abelian translation scheme over `F₂`
   (`affineScheme ⊥`, `p = 2` — where `-1 = 1`, so `hneg` is free) is proved **`AbelianConsumed`** — the FIRST
   concrete instance of either `hImprim` target predicate — and **imprimitive** for `d ≥ 2` (a proper subspace
   gives a proper closed subset), so `hImprim_nonvacuous_witness` exhibits `hImprim`'s conclusion holding
   non-vacuously on a genuinely imprimitive scheme. This is the CFI-flavoured witness: the residual is exactly
   an elementary-abelian gauge group, and the p = 2 choice is *forced* — for an odd-order translation scheme
   the generous-symmetry closure adjoins the reflection `x ↦ −x`, the residual is dihedral, and
   `AbelianConsumed`'s determinacy clause is FALSE (see the seal-handoff hImprim note: this is why "circulants
   exit via leg B" does NOT hold in this framework, and why the generic `hImprim` is refutation-shaped against
   the Wu–Ren–Ponomarenko circulant families).

**What this does NOT do.** No discharge for imprimitive schemes with non-abelian residual and unrecoverable
constituents — per the 2026-07-16 durable note (`chain-descent-seal-handoff.md`), that content is
`deepMatchSupply` firing on the constituents and shares the one wall. The generic ∀-scheme `hImprim` should be
treated as per-family, not as a citation.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned. In `scripts/build.sh` after `ChainDescent.CascadeAffine`.
-/
import ChainDescent.CascadeAffine
import ChainDescent.RouteCTransport

namespace ChainDescent

open MulAction

/-! ## §1 — forward M1: `G₀Irreducible ⟹ IsPrimitive (affineScheme)`

The dual of `isPrimitive_affineScheme_imp_irreducible`. From a closed subset `I` build the subspace
`W := { v | relOfPair(0, v)-orbital ∈ I }`: `G₀`-invariant (a `G₀`-translate has the same orbital), closed
under `+` (the closed subset's intersection-number closure on the concrete triple `0 → v → v+v'`) and under
`ZMod p`-scaling (char `p`: scaling is repeated addition). Irreducibility forces `W = ⊥` or `⊤`; the fact
`relOfPair(0, affineRelDiff k) = k` transports these back to `I = {0}` or `I = univ`. -/

section ForwardM1

variable {p d : ℕ} [Fact p.Prime]
variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- **Forward M1 — `G₀` irreducible ⟹ `affineScheme` primitive.** The dual of
`isPrimitive_affineScheme_imp_irreducible`; completes the intended `IsPrimitive ⟺ G₀Irreducible`. -/
theorem irreducible_imp_isPrimitive_affineScheme
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (hirr : G₀Irreducible G₀) :
    (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  intro I hcl
  -- Fact A: the difference-orbital of a relation's representative difference is that relation.
  have horbdiff : ∀ k, (affineScheme G₀ hneg).relOfPair (affineE 0)
      (affineE (affineRelDiff G₀ hneg k)) = k := by
    intro k
    have htrans := affineScheme_relOfPair_translation G₀ hneg
      (orbitalIdx (affineG G₀) k).out.1 (orbitalIdx (affineG G₀) k).out.2
    have hdiffeq : affineE.symm (orbitalIdx (affineG G₀) k).out.2
        - affineE.symm (orbitalIdx (affineG G₀) k).out.1 = affineRelDiff G₀ hneg k := rfl
    rw [hdiffeq] at htrans
    have hrel : (affineScheme G₀ hneg).relOfPair (orbitalIdx (affineG G₀) k).out.1
        (orbitalIdx (affineG G₀) k).out.2 = k := by
      rw [affineScheme_relOfPair, orbMk_out, Equiv.symm_apply_apply]
    rw [← htrans, hrel]
  -- membership abbreviation
  have hzero : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (0 : Fin d → ZMod p)) ∈ I := by
    have : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (0 : Fin d → ZMod p)) = 0 :=
      ((affineScheme G₀ hneg).relOfPair_eq_zero_iff _ _).mpr rfl
    rw [this]; exact hcl.1
  -- closed under addition (the crux — mirrors `schemeEquiv_trans` in the additive direction)
  have hadd : ∀ v v' : Fin d → ZMod p,
      (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∈ I →
      (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v') ∈ I →
      (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (v + v')) ∈ I := by
    intro v v' hv hv'
    set a0 := affineE (0 : Fin d → ZMod p)
    set av := affineE v
    set avv := affineE (v + v')
    -- j := relOfPair av avv ∈ I (translation to the origin gives the orbital of v')
    have hj : (affineScheme G₀ hneg).relOfPair av avv ∈ I := by
      have ht := affineScheme_relOfPair_translation G₀ hneg av avv
      have hde : affineE.symm avv - affineE.symm av = v' := by
        simp only [av, avv, Equiv.symm_apply_apply]; abel
      rw [hde] at ht
      rw [ht]; exact hv'
    -- intersection number of (i, j) at k is positive, witnessed by the midpoint av
    have hk : (affineScheme G₀ hneg).intersectionNumber
        ((affineScheme G₀ hneg).relOfPair a0 av)
        ((affineScheme G₀ hneg).relOfPair av avv)
        ((affineScheme G₀ hneg).relOfPair a0 avv) ≠ 0 := by
      have hcard := (affineScheme G₀ hneg).intersectionNumber_well_defined
        ((affineScheme G₀ hneg).relOfPair a0 av)
        ((affineScheme G₀ hneg).relOfPair av avv)
        ((affineScheme G₀ hneg).relOfPair a0 avv) a0 avv
        ((affineScheme G₀ hneg).rel_relOfPair a0 avv)
      have hmid : av ∈ Finset.univ.filter
          (fun u : Fin (p ^ d) =>
            (affineScheme G₀ hneg).rel ((affineScheme G₀ hneg).relOfPair a0 av) a0 u = true ∧
            (affineScheme G₀ hneg).rel ((affineScheme G₀ hneg).relOfPair av avv) u avv = true) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(affineScheme G₀ hneg).rel_relOfPair a0 av,
          (affineScheme G₀ hneg).rel_relOfPair av avv⟩
      rw [← hcard]
      exact Finset.card_ne_zero.mpr ⟨av, hmid⟩
    exact hcl.2 _ hv _ hj _ hk
  -- closed under ℕ-scaling (iterated addition)
  have hnsmul : ∀ (m : ℕ) (v : Fin d → ZMod p),
      (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∈ I →
      (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (m • v)) ∈ I := by
    intro m
    induction m with
    | zero => intro v _; simpa using hzero
    | succ k ih =>
      intro v hv
      rw [succ_nsmul]
      exact hadd _ _ (ih v hv) hv
  -- build the invariant subspace `W = { v | relOfPair(0, v)-orbital ∈ I }`
  let W : Submodule (ZMod p) (Fin d → ZMod p) :=
    { carrier := {v | (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∈ I}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun c v hv => by
        show (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (c • v)) ∈ I
        have hcast : c • v = c.val • v := by
          conv_lhs => rw [show c = ((c.val : ℕ) : ZMod p) from (ZMod.natCast_rightInverse c).symm]
          rw [Nat.cast_smul_eq_nsmul]
        rw [hcast]
        exact hnsmul c.val v hv }
  have hmemW : ∀ v, v ∈ W ↔ (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE v) ∈ I :=
    fun v => Iff.rfl
  -- `W` is `G₀`-invariant: a `G₀`-translate has the same difference-orbital
  have hinv : ∀ g ∈ G₀, ∀ w ∈ W, (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) w ∈ W := by
    intro g hg w hw
    rw [hmemW] at hw ⊢
    have heq : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (g w))
        = (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE w) := by
      rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff]
      refine ⟨g, hg, ?_⟩
      simp only [Equiv.symm_apply_apply, sub_zero]
    rw [heq]; exact hw
  -- irreducibility: `W = ⊥` or `W = ⊤`
  rcases hirr W hinv with hbot | htop
  · -- `W = ⊥` ⟹ `I = {0}`
    left
    apply Finset.Subset.antisymm
    · -- `I ⊆ {0}`
      intro k hk
      rw [Finset.mem_singleton]
      have hmem : affineRelDiff G₀ hneg k ∈ W := by rw [hmemW, horbdiff]; exact hk
      rw [hbot, Submodule.mem_bot] at hmem
      have : (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (affineRelDiff G₀ hneg k))
          = (affineScheme G₀ hneg).relOfPair (affineE 0) (affineE (0 : Fin d → ZMod p)) := by
        rw [hmem]
      rw [horbdiff] at this
      rw [this]
      exact ((affineScheme G₀ hneg).relOfPair_eq_zero_iff _ _).mpr rfl
    · -- `{0} ⊆ I`
      intro k hk
      rw [Finset.mem_singleton] at hk
      rw [hk]; exact hcl.1
  · -- `W = ⊤` ⟹ `I = univ`
    right
    apply Finset.eq_univ_of_forall
    intro k
    have hmem : affineRelDiff G₀ hneg k ∈ W := by rw [htop]; exact Submodule.mem_top
    rw [hmemW, horbdiff] at hmem
    exact hmem

/-- **Every relation of `affineScheme` is realized** — `R_k` contains the pair `(0, affineRelDiff k)`.
(The orbital of the representative-pair difference is the relation itself; §1's Fact A, exported. This is
the `hne` hypothesis of the seal capstones, discharged for the whole affine family.) -/
theorem affineScheme_rel_relDiff (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (k : Fin ((affineScheme G₀ hneg).rank + 1)) :
    (affineScheme G₀ hneg).rel k (affineE 0) (affineE (affineRelDiff G₀ hneg k)) = true := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have horbdiff : (affineScheme G₀ hneg).relOfPair (affineE 0)
      (affineE (affineRelDiff G₀ hneg k)) = k := by
    have htrans := affineScheme_relOfPair_translation G₀ hneg
      (orbitalIdx (affineG G₀) k).out.1 (orbitalIdx (affineG G₀) k).out.2
    have hdiffeq : affineE.symm (orbitalIdx (affineG G₀) k).out.2
        - affineE.symm (orbitalIdx (affineG G₀) k).out.1 = affineRelDiff G₀ hneg k := rfl
    rw [hdiffeq] at htrans
    have hrel : (affineScheme G₀ hneg).relOfPair (orbitalIdx (affineG G₀) k).out.1
        (orbitalIdx (affineG G₀) k).out.2 = k := by
      rw [affineScheme_relOfPair, orbMk_out, Equiv.symm_apply_apply]
    rw [← htrans, hrel]
  have h := (affineScheme G₀ hneg).rel_relOfPair (affineE 0)
    (affineE (affineRelDiff G₀ hneg k))
  rwa [horbdiff] at h

end ForwardM1

/-! ## §2 — the `hImprim` vacuous discharge on the irreducible-affine class

Wherever `G₀` acts irreducibly the scheme is primitive (§1), so the seal's carried
`hImprim : ¬IsPrimitive → SchemeBlockRecovered ∨ AbelianConsumed` holds with a FALSE antecedent — a theorem,
not an assumption. Instantiated at both in-build irreducibility witnesses, and cashed out as the
affine-irreducible seal capstone with `hImprim` removed. -/

section HImprimDischarge

variable {p d : ℕ} [Fact p.Prime]
variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- **The `hImprim` discharge, irreducible-affine class.** For irreducible `G₀` the seal's imprimitive-branch
hypothesis is a theorem: the antecedent `¬IsPrimitive` is refuted by forward M1. Exactly the shape every
`reachesRigidOrCameron_*` capstone consumes. -/
theorem hImprim_affine_of_irreducible
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (hirr : G₀Irreducible G₀) :
    ¬ (affineScheme G₀ hneg).toAssociationScheme.IsPrimitive →
      SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
        ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg) :=
  fun hnp => absurd (irreducible_imp_isPrimitive_affineScheme G₀ hneg hirr) hnp

/-- `hImprim` discharged for the full-generator cyclic instance (`cyclicAffineScheme`, the rank-2 `K_{p^d}`
degenerate case) via `G0cyc_irreducible`. -/
theorem hImprim_cyclicAffineScheme (hd : d ≠ 0) :
    ¬ (cyclicAffineScheme (p := p) hd).toAssociationScheme.IsPrimitive →
      SchemeBlockRecovered (p ^ d) (cyclicAffineScheme hd)
        ∨ AbelianConsumed (p ^ d) (cyclicAffineScheme hd) :=
  hImprim_affine_of_irreducible (G0cyc hd) (neg_mem_G0cyc hd) (G0cyc_irreducible hd)

/-- `hImprim` discharged for the **genuine cyclotomic slice** — `G0pow β` with a field-generating `β`
(`Algebra.adjoin = ⊤`) — via `G0pow_irreducible_of_adjoin`. The imprimitive cyclotomic members are exactly
those with `β` in a proper subfield (not field-generating): they are NOT covered here and remain the honest
carried content of the cyclotomic seal. -/
theorem hImprim_G0pow_of_adjoin (hd : d ≠ 0) (β : (GaloisField p d)ˣ)
    (hβneg : (-1 : (GaloisField p d)ˣ) ∈ Subgroup.zpowers β)
    (hβ : Algebra.adjoin (ZMod p) {(β : GaloisField p d)} = ⊤) :
    ¬ (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)).toAssociationScheme.IsPrimitive →
      SchemeBlockRecovered (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg))
        ∨ AbelianConsumed (p ^ d) (affineScheme (G0pow hd β) (neg_mem_G0pow hd β hβneg)) :=
  hImprim_affine_of_irreducible (G0pow hd β) (neg_mem_G0pow hd β hβneg)
    (G0pow_irreducible_of_adjoin hd β hβ)

/-- **The affine-irreducible seal with `hImprim` REMOVED.** `reachesRigidOrCameron_viaAffineIrreducible`
carried `{G3 (hClassify), hbound, hImprim}`; with irreducibility given, §1 discharges `hImprim` and the
irreducibility half of `hbound`'s antecedent, so the carried set is `{G3, hbound}` — the first seal capstone
whose imprimitive branch is closed by a theorem rather than a hypothesis. -/
theorem reachesRigidOrCameron_viaAffineIrreducible_prim {IsLarge : Nat → Prop}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (hClassify : PrimitiveCCClassification (IsLargeSchemeViaAut IsLarge) IsCameronScheme)
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀)
    (hne : ∀ i : Fin ((affineScheme G₀ hneg).rank + 1),
        ∃ v w, (affineScheme G₀ hneg).rel i v w = true)
    (hrank : 2 ≤ (affineScheme G₀ hneg).rank)
    (hirr : G₀Irreducible G₀)
    (hbound : ¬ IsLargeSchemeViaAut IsLarge (p ^ d) (affineScheme G₀ hneg) →
        ∃ T : Finset (Fin (p ^ d)), T.card ≤ bound ∧
          Discrete (warmRefine (schemeAdj (affineScheme G₀ hneg).toAssociationScheme)
            (fun _ _ => POE.unknown) (individualizedColouring (p ^ d) T))) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme G₀ hneg)
        ∨ AbelianConsumed (p ^ d) (affineScheme G₀ hneg))
      ∨ SchemeRecoveredByDepth (p ^ d) (affineScheme G₀ hneg) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme G₀ hneg) :=
  reachesRigidOrCameron_viaAffineIrreducible (G₀ := G₀) hClassify hneg hne hrank
    (fun h => hbound h.2) (hImprim_affine_of_irreducible G₀ hneg hirr)

end HImprimDischarge

/-! ## §2b — primitivity transports along `SchemeRealizes` (the seam's primitivity leg)

The descent recovers a residue `S` only *up to realization* (`SchemeRealizes f S X`, carried like Route C's
`hreal`). This section transports §1's primitivity across the realization, so the `hImprim` discharge covers
every **realized** residue of an irreducible-affine model — not just the literal `affineScheme`. Ported from
`ScratchSchemeRealizesPrimitive.lean` (2026-07-17; the scratch file is retired). Method: the conjugation
`π ↦ f π f⁻¹` is a bijection `S.SchemeAutGroup ≅ X.SchemeAutGroup` intertwined by `f`; preprimitivity
transports along the equivariant bijection (`MulAction.isPreprimitive_congr`), and
`isPreprimitive_iff_isPrimitive` bridges to `IsPrimitive` on both ends. -/

section RealizesTransport

variable {n : Nat}

/-- **Primitivity transports along a scheme realization.** If `f` realizes `S ≅ X` (relation-preserving) and
`X` is primitive, then `S` is primitive. Both schemes need every relation to occur (`hneS`/`hneX`) — the
schurian hypothesis of `isPreprimitive_iff_isPrimitive`. -/
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

end RealizesTransport

section RealizesAffine

variable {p d : ℕ} [Fact p.Prime]
variable (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)))

/-- **Every relation of `affineScheme` occurs** — the orbital scheme's `hne` (free via `orbMk_out`). -/
theorem affineScheme_hne (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) :
    ∀ k : Fin ((affineScheme G₀ hneg).rank + 1), ∃ v w, (affineScheme G₀ hneg).rel k v w = true :=
  fun k => ⟨_, _, (affineScheme_rel_iff G₀ hneg).mpr
    (orbMk_out (affineG G₀) (orbitalIdx (affineG G₀) k)).symm⟩

/-- **★ The seam's primitivity leg, end-to-end.** A descent residue `S` realized as an irreducible-affine
model (`SchemeRealizes f S (affineScheme G₀)`, carried like Route C's `hreal`) is **primitive**. Composes
forward-M1 with primitivity transport along the realization. -/
theorem isPrimitive_of_realizes_affineScheme
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (hirr : G₀Irreducible G₀)
    {f : Equiv.Perm (Fin (p ^ d))} {S : SchurianScheme (p ^ d)}
    (hreal : SchemeRealizes f S (affineScheme G₀ hneg))
    (hneS : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true) :
    S.toAssociationScheme.IsPrimitive :=
  isPrimitive_of_schemeRealizes hreal hneS (affineScheme_hne G₀ hneg)
    (irreducible_imp_isPrimitive_affineScheme G₀ hneg hirr)

/-- **The `hImprim` discharge at an arbitrary REALIZED residue.** The exact hypothesis shape the seal
capstones carry, discharged for any `S` realized as an irreducible-affine model — the route-2 endpoint
("prevent `hImprim` from arising where it occurs"): wherever the descent's recovered residue realizes an
irreducible-affine scheme, the imprimitive branch is closed by a theorem. -/
theorem hImprim_of_realizes_affineScheme
    (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) (hirr : G₀Irreducible G₀)
    {f : Equiv.Perm (Fin (p ^ d))} {S : SchurianScheme (p ^ d)}
    (hreal : SchemeRealizes f S (affineScheme G₀ hneg))
    (hneS : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true) :
    ¬ S.toAssociationScheme.IsPrimitive →
      SchemeBlockRecovered (p ^ d) S ∨ AbelianConsumed (p ^ d) S :=
  fun hnp => absurd (isPrimitive_of_realizes_affineScheme G₀ hneg hirr hreal hneS) hnp

end RealizesAffine

/-! ## §3 — the leg-B witness: the elementary-abelian translation scheme

`translationScheme d = affineScheme ⊥` over `F₂` — relations are exactly the difference vectors (the
`G₀ = ⊥` orbitals are singletons), automorphisms are exactly the `2^d` translations (abelian!), and every
subspace of differences is a closed subset (imprimitivity for `d ≥ 2`). The `p = 2` choice is forced:
the scheme's relations are symmetric, so for odd `p` the reflection `x ↦ −x` is always a scheme automorphism
and the residual is dihedral — non-abelian, and `AbelianConsumed`'s determinacy clause fails. Only in
characteristic 2 (`−1 = 1`) is the translation residual honestly abelian. -/

section LegBWitness

variable {d : ℕ}

/-- Over `ZMod 2` the negation map IS the identity (`−x = x`), so `hneg` holds for the trivial group. -/
theorem neg_mem_bot_two :
    LinearEquiv.neg (ZMod 2)
      ∈ (⊥ : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2))) := by
  rw [Subgroup.mem_bot]
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  show -v = v
  funext i
  exact CharTwo.neg_eq (v i)

/-- **The elementary-abelian translation scheme** — `affineScheme` with the trivial linear group over `F₂`.
Relations = difference vectors; `Aut` = the translations `Z₂^d`. -/
noncomputable def translationScheme (d : ℕ) : SchurianScheme (2 ^ d) :=
  affineScheme (p := 2) (⊥ : Subgroup ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)))
    neg_mem_bot_two

/-- With `G₀ = ⊥` the orbital of a pair is exactly its difference: two pairs share a relation iff their
differences are equal. -/
theorem translationScheme_relOfPair_eq_iff {x y x' y' : Fin (2 ^ d)} :
    (translationScheme d).relOfPair x y = (translationScheme d).relOfPair x' y' ↔
      affineE.symm y - affineE.symm x = affineE.symm y' - affineE.symm x' := by
  rw [translationScheme, affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff]
  constructor
  · rintro ⟨g₀, hg₀, heq⟩
    rw [Subgroup.mem_bot] at hg₀
    subst hg₀
    simpa using heq.symm
  · intro h
    exact ⟨1, Subgroup.one_mem _, by simpa using h.symm⟩

/-- The relation class of a difference vector — the scheme's relations, enumerated by `Z₂^d`. -/
noncomputable def diffClass (v : Fin d → ZMod 2) : Fin ((translationScheme d).rank + 1) :=
  (translationScheme d).relOfPair (affineE 0) (affineE v)

theorem diffClass_inj {v w : Fin d → ZMod 2} (h : diffClass v = diffClass w) : v = w := by
  have hd := (translationScheme_relOfPair_eq_iff).mp h
  simpa using hd

theorem diffClass_zero : diffClass (d := d) 0 = 0 :=
  ((translationScheme d).relOfPair_eq_zero_iff _ _).mpr rfl

/-- Any related pair's relation is the class of its difference. -/
theorem rel_eq_diffClass {i : Fin ((translationScheme d).rank + 1)} {a u : Fin (2 ^ d)}
    (h : (translationScheme d).rel i a u = true) :
    i = diffClass (affineE.symm u - affineE.symm a) := by
  have h1 : i = (translationScheme d).relOfPair a u :=
    ((translationScheme d).rel_iff_relOfPair).mp h
  rw [h1, diffClass]
  exact affineScheme_relOfPair_translation _ neg_mem_bot_two a u

/-- The translation permutation `x ↦ x + t` on `Fin (2^d)`, through the coordinate equivalence. -/
noncomputable def transPerm (t : Fin d → ZMod 2) : Equiv.Perm (Fin (2 ^ d)) :=
  affineE.permCongr (Equiv.addRight t)

theorem transPerm_apply (t : Fin d → ZMod 2) (x : Fin (2 ^ d)) :
    transPerm t x = affineE (affineE.symm x + t) := by
  simp [transPerm, Equiv.permCongr_apply]

/-- Translations are automorphisms of the labelled scheme graph (differences are translation-invariant). -/
theorem isAut_transPerm (t : Fin d → ZMod 2) :
    IsAut (transPerm t) (schemeAdj (translationScheme d).toAssociationScheme) := by
  intro v w
  have h : (translationScheme d).relOfPair (transPerm t v) (transPerm t w)
      = (translationScheme d).relOfPair v w := by
    rw [translationScheme_relOfPair_eq_iff, transPerm_apply, transPerm_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    abel
  exact congrArg Fin.val h

/-- **Every residual automorphism of the translation scheme IS a translation** — the color-preserving
automorphisms of the complete Cayley colour graph of an abelian group are exactly the translations. -/
theorem residualAut_translationScheme_eq {π : Equiv.Perm (Fin (2 ^ d))}
    (hπ : ResidualAut (schemeAdj (translationScheme d).toAssociationScheme)
      (fun _ _ => POE.unknown) ∅ π) (x : Fin (2 ^ d)) :
    affineE.symm (π x) = affineE.symm x + affineE.symm (π (affineE 0)) := by
  have hsa : IsSchemeAut (translationScheme d).toAssociationScheme π :=
    (isAut_schemeAdj_iff (translationScheme d).toAssociationScheme π).mp hπ.1
  have h := IsSchemeAut.relOfPair_eq hsa (affineE 0) x
  have hdiff := (translationScheme_relOfPair_eq_iff).mp h
  rw [Equiv.symm_apply_apply, sub_zero] at hdiff
  exact eq_add_of_sub_eq hdiff

/-- **The translation residual is ABELIAN** — the honest `ResidualAbelian` instance leg B was designed for
(elementary-abelian gauge; no reflection in characteristic 2). -/
theorem residualAbelian_translationScheme :
    ResidualAbelian (schemeAdj (translationScheme d).toAssociationScheme)
      (fun _ _ => POE.unknown) ∅ := by
  intro π₁ π₂ h₁ h₂
  apply Equiv.ext
  intro x
  apply affineE.symm.injective
  have k₁ := residualAut_translationScheme_eq h₁
  have k₂ := residualAut_translationScheme_eq h₂
  have l1 : affineE.symm (π₁ (π₂ x))
      = affineE.symm x + affineE.symm (π₂ (affineE 0)) + affineE.symm (π₁ (affineE 0)) := by
    rw [k₁ (π₂ x), k₂ x]
  have l2 : affineE.symm (π₂ (π₁ x))
      = affineE.symm x + affineE.symm (π₁ (affineE 0)) + affineE.symm (π₂ (affineE 0)) := by
    rw [k₂ (π₁ x), k₁ x]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, l1, l2]
  abel

/-- The translation residual is non-trivial (`d ≠ 0`): a non-zero translation moves the origin. -/
theorem not_isBase_translationScheme (hd : d ≠ 0) :
    ¬ IsBase (schemeAdj (translationScheme d).toAssociationScheme)
      (fun _ _ => POE.unknown) ∅ := by
  intro hbase
  set t : Fin d → ZMod 2 := Pi.single ⟨0, Nat.pos_of_ne_zero hd⟩ 1 with ht
  have horb : OrbitPartition (schemeAdj (translationScheme d).toAssociationScheme)
      (fun _ _ => POE.unknown) ∅ (affineE 0) (affineE t) := by
    rw [orbitPartition_iff_residualAut]
    refine ⟨transPerm t,
      ⟨isAut_transPerm t, fun _ _ => rfl, fun v hv => absurd hv (Finset.notMem_empty v)⟩, ?_⟩
    rw [transPerm_apply, Equiv.symm_apply_apply, zero_add]
  have h0t : (0 : Fin d → ZMod 2) = t := affineE.injective (hbase _ _ horb)
  have h01 := congrFun h0t ⟨0, Nat.pos_of_ne_zero hd⟩
  rw [ht, Pi.single_eq_same] at h01
  exact zero_ne_one h01

/-- **★ The FIRST concrete `AbelianConsumed` instance** — leg B fires on the elementary-abelian translation
scheme. Both target predicates of `hImprim` were previously zero-instantiated (the recurring vacuity
failure mode); this closes the leg-B half. -/
theorem abelianConsumed_translationScheme (hd : d ≠ 0) :
    AbelianConsumed (2 ^ d) (translationScheme d) :=
  abelianConsumed_of_residualAbelian residualAbelian_translationScheme
    (not_isBase_translationScheme hd)

/-- **The translation scheme is IMPRIMITIVE for `d ≥ 2`** — the difference classes of a proper non-zero
subspace (here `{0, e₀}`) form a proper non-trivial closed subset. The block ⟺ subspace correspondence of
§1, exercised in the constructive direction. -/
theorem not_isPrimitive_translationScheme (hd2 : 2 ≤ d) :
    ¬ (translationScheme d).toAssociationScheme.IsPrimitive := by
  intro hprim
  have hv2 : ∀ v : Fin d → ZMod 2, v + v = 0 := by
    intro v; funext i
    show v i + v i = 0
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  set e0v : Fin d → ZMod 2 := Pi.single ⟨0, by omega⟩ 1 with he0v
  set e1v : Fin d → ZMod 2 := Pi.single ⟨1, by omega⟩ 1 with he1v
  have he0_ne : e0v ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    rw [he0v, Pi.single_eq_same] at this
    exact one_ne_zero this
  have he1_ne : e1v ≠ 0 := by
    intro h
    have := congrFun h ⟨1, by omega⟩
    rw [he1v, Pi.single_eq_same] at this
    exact one_ne_zero this
  have he10 : e1v ≠ e0v := by
    intro h
    have := congrFun h ⟨1, by omega⟩
    rw [he1v, he0v, Pi.single_eq_same,
      Pi.single_eq_of_ne (by simp [Fin.ext_iff]) 1] at this
    exact one_ne_zero this
  set I : Finset (Fin ((translationScheme d).rank + 1)) := {diffClass 0, diffClass e0v} with hI
  have hcl : (translationScheme d).toAssociationScheme.ClosedSubset I := by
    constructor
    · rw [hI, ← diffClass_zero]
      exact Finset.mem_insert_self _ _
    · intro i hi j hj k hk
      -- realize `k` by a representative pair (§1's Fact A, at `p = 2`, `G₀ = ⊥`)
      obtain ⟨a, b, hab⟩ : ∃ a b, (translationScheme d).rel k a b = true :=
        ⟨_, _, affineScheme_rel_relDiff _ neg_mem_bot_two k⟩
      -- the intersection witness `u`
      have hw := (translationScheme d).intersectionNumber_well_defined i j k a b hab
      have hcard : (Finset.univ.filter (fun u : Fin (2 ^ d) =>
          (translationScheme d).rel i a u = true ∧
          (translationScheme d).rel j u b = true)).card ≠ 0 := by
        rw [hw]; exact hk
      obtain ⟨u, hu⟩ := Finset.card_ne_zero.mp hcard
      rw [Finset.mem_filter] at hu
      obtain ⟨-, hiau, hjub⟩ := hu
      -- translate everything to differences
      have hia := rel_eq_diffClass hiau
      have hjb := rel_eq_diffClass hjub
      have hkab := rel_eq_diffClass hab
      -- membership in `I` pins each difference to `{0, e0v}`
      have hmemd : ∀ {c : Fin ((translationScheme d).rank + 1)} {v : Fin d → ZMod 2},
          c ∈ I → c = diffClass v → v = 0 ∨ v = e0v := by
        intro c v hc hcv
        rw [hI, Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with h | h
        · exact Or.inl (diffClass_inj (hcv.symm.trans h).symm).symm
        · exact Or.inr (diffClass_inj (hcv.symm.trans h).symm).symm
      have hdi := hmemd hi hia
      have hdj := hmemd hj hjb
      -- the difference of `k` is the sum
      have hsum : affineE.symm b - affineE.symm a
          = (affineE.symm u - affineE.symm a) + (affineE.symm b - affineE.symm u) := by
        abel
      have hkI : k = diffClass ((affineE.symm u - affineE.symm a)
          + (affineE.symm b - affineE.symm u)) := by
        rw [hkab, hsum]
      -- case bash in `Z₂`
      rw [hI, Finset.mem_insert, Finset.mem_singleton]
      rcases hdi with h1 | h1 <;> rcases hdj with h2 | h2 <;> rw [h1, h2] at hkI
      · left; rw [hkI, add_zero]
      · right; rw [hkI, zero_add]
      · right; rw [hkI, add_zero]
      · left; rw [hkI, hv2 e0v]
  rcases hprim I hcl with h | h
  · -- `I = {0}` is refuted by `diffClass e0v ∈ I`, `e0v ≠ 0`
    have hmem : diffClass e0v ∈ I := by
      rw [hI]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [h, Finset.mem_singleton, ← diffClass_zero] at hmem
    exact he0_ne (diffClass_inj hmem)
  · -- `I = univ` is refuted by `diffClass e1v ∉ {diffClass 0, diffClass e0v}`
    have hmem : diffClass e1v ∈ I := h ▸ Finset.mem_univ _
    rw [hI, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact he1_ne (diffClass_inj h1)
    · exact he10 (diffClass_inj h1)

/-- **★ `hImprim`'s conclusion, non-vacuously, on a genuinely IMPRIMITIVE scheme.** The elementary-abelian
translation scheme (`d ≥ 2`) is imprimitive AND `AbelianConsumed` — the first machine-checked witness that
the seal's imprimitive branch can actually fire (previously both `SchemeBlockRecovered` and `AbelianConsumed`
had zero instances, so `hImprim` was carried against uninhabited targets). -/
theorem hImprim_nonvacuous_witness (hd2 : 2 ≤ d) :
    ¬ (translationScheme d).toAssociationScheme.IsPrimitive ∧
      (SchemeBlockRecovered (2 ^ d) (translationScheme d)
        ∨ AbelianConsumed (2 ^ d) (translationScheme d)) :=
  ⟨not_isPrimitive_translationScheme hd2,
   Or.inr (abelianConsumed_translationScheme (by omega))⟩

end LegBWitness

end ChainDescent
