/-
# Gauss-sum point-count infrastructure for Stage B.1c-ii (the "Gauss build")

WORK IN PROGRESS — develop here, port into `CascadeAffine.lean` (near §OrthogonalForm) once Bricks
C and D land. Everything below is PROVEN and axiom-clean `[propext, Classical.choice, Quot.sound]`
(verified via `lake env lean ChainDescent/ScratchGauss.lean`). This file imports ONLY Mathlib, so it
builds in isolation (cheap) — it does NOT pull in the heavy project modules.

Target: discharge `IsotropyCountsRecoverFrameQ Q` (CascadeAffine §OrthogonalForm, B.1c-ii) for the
forms-graph residue, starting at `VO^ε_4(3)`. Mathlib has the machinery (`gaussSum_sq`,
`quadraticChar_card_sqrts`, `equivalent_weightedSumSquares`, char orthogonality) but NOT the assembled
affine-quadric point-count formula — that is what these bricks build.

DONE (this file):
* Brick A  `count_eq_charsum`        — solution count `#{x | f x = c}` as a double character sum.
* Brick B1 `sum_addChar_sq`          — `∑_x ψ(x²) = gaussSum χ ψ`.
* Brick B2 `sum_addChar_smul_sq`     — `∑_x ψ(a·x²) = χ(a)·gaussSum χ ψ` (a a unit).
* helper   `addChar_sum`             — `ψ(∑ aᵢ) = ∏ ψ(aᵢ)`.
* Brick B3 `sum_addChar_quadForm`    — `∑_x ψ(Q x) = (∏ᵢ χ(wᵢ))·gaussSum^d` for nondegenerate `Q`
                                       (diagonalize + reindex + factor). THE multivariable core.

NEXT (next session):
* Brick C  — the affine-quadric point count `#{x : Q x = c}`: combine Brick A (`f = Q`) with Brick B3
             applied to `t·Q` for `t ≠ 0` (split off the `t = 0` term `= q^d`; the `t ≠ 0` terms give
             `χ(t)^d · χ(disc) · Gᵈ`, summed against `ψ(−tc)`). Yields the standard
             `q^{d-1} ± (…)q^{d/2-1}` formula. `gaussSum_sq : G² = χ(-1)·q` collapses `Gᵈ` for even `d`.
* Brick D  — reduce `IsotropyFrameCountsAgree` to these point counts: the common-isotropic-neighbour
             count of a frame point `t` and `u` is a hyperplane-section count determined by `Q(ū−t̄)`,
             so equal isotropy counts ⟹ equal `Q`-profile ⟹ `IsotropyCountsRecoverFrameQ`. At `q = 3`
             this is the binary square/non-square shell distinction (§3 non-isotropic shell).
* Bridge   — `(Q.polarBilin).Nondegenerate` (the project's hyp) ⟹ `(associated Q).SeparatingLeft`
             (B3's hyp), via `two_nsmul_associated` + `Invertible (2 : ZMod p)` (p odd). Small.

CAVEAT: B3 requires `[Invertible (2:K)]` / `ringChar ≠ 2` — char-2 (`q = 2,4`) is a separate argument
(§5 R2′); do `q = 3` first.
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

open Finset

/-- **Brick A — solution count as a character sum.** -/
theorem count_eq_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] (f : V → F) (c : F) :
    (∑ x : V, ∑ t : F, ψ (t * (f x - c)))
      = ((univ.filter (fun x : V => f x = c)).card : R') * (Fintype.card F : R') := by
  have hinner : ∀ x : V, (∑ t : F, ψ (t * (f x - c)))
      = if f x = c then (Fintype.card F : R') else 0 := by
    intro x
    rw [AddChar.sum_mulShift (f x - c) hψ]
    simp [sub_eq_zero]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

/-- **Brick B1 — the 1-dimensional quadratic Gauss sum.** For a finite field `F` of odd
characteristic and a nontrivial additive character `ψ`, the quadratic exponential sum
`∑_x ψ(x²)` equals the Gauss sum of the quadratic character. (Each value `y` is hit by
`χ(y)+1` square roots; the `+1` part sums to `0`.) -/
theorem sum_addChar_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2))
      = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom R')) ψ := by
  have hfib : (∑ x : F, ψ (x ^ 2))
      = ∑ y : F, ∑ x ∈ univ.filter (fun x : F => x ^ 2 = y), ψ y := by
    rw [← Finset.sum_fiberwise (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x hx => ?_))
    rw [(Finset.mem_filter.1 hx).2]
  rw [hfib]
  have hcard : ∀ y : F, ((univ.filter (fun x : F => x ^ 2 = y)).card : R')
      = ((quadraticChar F).ringHomComp (Int.castRingHom R')) y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts hF y
    rw [Set.toFinset_setOf] at h
    have : ((univ.filter (fun x : F => x ^ 2 = y)).card : ℤ) = quadraticChar F y + 1 := h
    have hcast := congrArg (Int.cast (R := R')) this
    push_cast at hcast
    rw [hcast]
    simp [MulChar.ringHomComp]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => by rw [hcard y])]
  rw [gaussSum]
  rw [Finset.sum_congr rfl (fun y _ => by rw [add_mul, one_mul])]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]

/-- **Brick B2 — the scaled quadratic Gauss sum.** For a unit `a`, the scaled sum `∑_x ψ(a·x²)`
equals `χ(a) · gaussSum χ ψ`. (Via `gaussSum_mulShift` and `χ(a)² = 1`.) -/
theorem sum_addChar_smul_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive) (a : Fˣ) :
    (∑ x : F, ψ ((a : F) * x ^ 2))
      = ((quadraticChar F).ringHomComp (Int.castRingHom R')) (a : F)
        * gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom R')) ψ := by
  set χ := (quadraticChar F).ringHomComp (Int.castRingHom R') with hχ
  have hne : (AddChar.mulShift ψ (a : F)) ≠ 1 := hψ a.ne_zero
  have hB1 : (∑ x : F, ψ ((a : F) * x ^ 2)) = gaussSum χ (AddChar.mulShift ψ (a : F)) := by
    rw [← sum_addChar_sq hF hne]
    exact Finset.sum_congr rfl (fun x _ => by rw [AddChar.mulShift_apply])
  have hms := gaussSum_mulShift χ ψ a
  have hsq : χ (a : F) * χ (a : F) = 1 := by
    have h := quadraticChar_sq_one (F := F) a.ne_zero
    have : χ (a : F) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    rw [pow_two] at this; simpa using this
  rw [hB1]
  have := congrArg (fun z => χ (a : F) * z) hms
  simp only at this
  rw [← mul_assoc, hsq, one_mul] at this
  rw [this]

/-- An additive character turns a finite sum into a finite product. -/
theorem addChar_sum {F : Type*} [AddCommGroup F] {R' : Type*} [CommMonoid R'] (ψ : AddChar F R')
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → F) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  induction s using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

/-- **Brick B3 — the multivariable quadratic Gauss sum.** For a nondegenerate quadratic form `Q` on a
finite-dimensional space over a finite field of odd characteristic, the exponential sum `∑_x ψ(Q x)`
diagonalizes to `(∏ᵢ χ(wᵢ)) · gaussSum^d`, where the `wᵢ` are the (nonzero) diagonal weights and
`d = finrank`. (Diagonalize via `equivalent_weightedSumSquares`; reindex; the additive character
factors the diagonal sum into a product of 1-D Gauss sums, each evaluated by Brick B2.) -/
theorem sum_addChar_quadForm {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] (Q : QuadraticForm K V) (hQ : (QuadraticMap.associated (R := K) Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank K V) → Kˣ,
      (∑ x : V, ψ (Q x))
        = (∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (w i : K))
          * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
              ^ Module.finrank K V := by
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ
  refine ⟨w, ?_⟩
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  have hreindex : (∑ x : V, ψ (Q x))
      = ∑ y : (Fin (Module.finrank K V) → K), ψ (QuadraticMap.weightedSumSquares K w y) := by
    rw [← Equiv.sum_comp e.toLinearEquiv.toEquiv (fun y => ψ (QuadraticMap.weightedSumSquares K w y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    exact (e.map_app' x).symm
  rw [hreindex]
  have hexp : ∀ y : (Fin (Module.finrank K V) → K),
      ψ (QuadraticMap.weightedSumSquares K w y) = ∏ i, ψ ((w i : K) * (y i) ^ 2) := by
    intro y
    rw [QuadraticMap.weightedSumSquares_apply, addChar_sum]
    exact Finset.prod_congr rfl (fun i _ => by simp only [Units.smul_def, smul_eq_mul, pow_two])
  rw [Finset.sum_congr rfl (fun y _ => hexp y),
    ← Fintype.prod_sum (fun (i : Fin (Module.finrank K V)) (t : K) => ψ ((w i : K) * t ^ 2)),
    Finset.prod_congr rfl (fun i _ => sum_addChar_smul_sq hF hψ (w i)),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

#print axioms count_eq_charsum
#print axioms sum_addChar_sq
#print axioms sum_addChar_smul_sq
#print axioms addChar_sum
#print axioms sum_addChar_quadForm
