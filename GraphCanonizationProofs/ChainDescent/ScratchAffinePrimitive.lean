/-
# ScratchAffinePrimitive.lean — forward-M1: `G₀Irreducible ⟹ IsPrimitive (affineScheme)` (WIP, NOT in build.sh)

**What this proves.** The genuine **dual** of `isPrimitive_affineScheme_imp_irreducible` (`CascadeAffine.lean:2351`,
which proves the *converse* `IsPrimitive → G₀Irreducible`). The intended M1 was an ⟺ (`CascadeAffine.lean:2203`); only
one direction was built (the converse), because the recovery bridge M3 consumes only `¬irreducible → ¬IsPrimitive`
(docstring `:2256`). This file supplies the **forward** direction:

  `G₀` acts irreducibly on `V = F_p^d`  ⟹  `affineScheme G₀` is **primitive** (no non-trivial block system).

**Why it matters (the generic hImprim discharge).** The confinement's `hImprimTrans` (`ScratchConfinementCellImprim`,
the wall-free ¬IsPrimitive supplier) is **vacuous** on the affine/forms families because they are primitive rank-3.
Making that vacuity a *theorem* (not a carried assumption) needs exactly `G₀Irreducible → IsPrimitive` — which the doc
and memory previously mis-cited as already-built (it was the converse). This closes that orientation gap and discharges
`hImprimTrans` for the entire affine residue class at once (given the `M.S`↔`affineScheme` seam, item 2).

**The proof (dual of the converse).** From a closed subset `I` (a block system), build the subspace
`W := { v | relOfPair(0, v)-orbital ∈ I }` = the vectors whose difference-orbital lies in `I`. It is `G₀`-invariant
(a `G₀`-translate has the same orbital) and a subspace: `0 ∈ W` (diagonal), closed under `+` (the closed subset's
intersection-number closure applied to the concrete triple `0 → v → v+v'`, mirroring `schemeEquiv_trans`), and closed
under `ZMod p`-scaling (char `p`: scaling is repeated addition). Irreducibility forces `W = ⊥` or `W = ⊤`; the key fact
`relOfPair(0, affineRelDiff k)-orbital = k` transports these back to `I = {0}` or `I = univ`.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.CascadeAffine

namespace ChainDescent

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

end ChainDescent
