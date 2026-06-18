/-
# Gauss-sum point-count toolkit (`GaussCount`) — Stage B.1c-ii infrastructure

The finite-field quadratic exponential-sum toolkit for the seal's node-4 forms-graph residue (B.1c-ii): the
Mathlib-absent affine-quadric point-count formula and its multi-point / k-fold generalizations, used to discharge
`IsotropySeparatesAtBase Q T` (CascadeAffine §OrthogonalForm) at a symmetry-broken base for `VO^ε_4(q)`.

Imports ONLY Mathlib (no project modules), so it is a cheap leaf. Ported from the former `ScratchGauss.lean`
development file; all lemmas axiom-clean `[propext, Classical.choice, Quot.sound]`.

Contents (all in `namespace ChainDescent`):
* count layer — `count_eq_charsum` (A), `count2_eq_charsum` (A2), `countk_eq_charsum`/`countk_eq_sum_charsum` (Aₖ),
  `count_pi_setValued` (value-set → value-point inclusion–exclusion).
* 1-D Gauss — `sum_addChar_sq` (B1), `sum_addChar_smul_sq` (B2); helper `addChar_sum`.
* multivariable Gauss — `sum_addChar_quadForm` (B3), `sum_quadForm_eval` (B3′), `sum_addChar_quadForm_smul`
  (scaling), `card_quadForm_eq` (C, THE affine-quadric point count).
* multi-point — `sum_addChar_quadForm_linear` (D1), `sum_addChar_multiQuad` (R≠0), `sum_addChar_multiQuad_zero`
  (R=0), `sum_addChar_linearMap` (the linear boundary); helpers `quad_sub`, `polar_sum_right`.

So the multi-point Q-count `#{z : Q(z−tⱼ)=cⱼ ∀j}` is in CLOSED FORM (`countk_eq_sum_charsum` + the inner-sum
evaluations `multiQuad`/`multiQuad_zero`/`linearMap`), and isotropy-class counts reduce to it (`count_pi_setValued`
+ the CascadeAffine isotropy dictionary `isoClass_eq_*`).

CAVEAT: requires `[Invertible (2:K)]` / `ringChar ≠ 2`; char-2 (`q=2,4`) is a separate argument.
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank


open Finset Module

namespace ChainDescent

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

/-- **Brick B3′ — basis-explicit multivariable Gauss sum.** As `sum_addChar_quadForm` but with an
explicit orthogonal basis `v` (weights `Q (v i)`), so the value is pinned (no existential). This is
the form that powers the scaling relation (Brick C). -/
theorem sum_quadForm_eval {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] (Q : QuadraticForm K V) (v : Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    (∑ x : V, ψ (Q x))
      = (∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q (v i)))
        * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ Module.finrank K V := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  let e := QuadraticForm.isometryEquivWeightedSumSquares Q v hv
  have hreindex : (∑ x : V, ψ (Q x))
      = ∑ y : (Fin (Module.finrank K V) → K),
          ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y) := by
    rw [← Equiv.sum_comp e.toLinearEquiv.toEquiv
      (fun y => ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    exact (e.map_app' x).symm
  rw [hreindex]
  have hexp : ∀ y : (Fin (Module.finrank K V) → K),
      ψ (QuadraticMap.weightedSumSquares K (fun i => Q (v i)) y) = ∏ i, ψ (Q (v i) * (y i) ^ 2) := by
    intro y
    rw [QuadraticMap.weightedSumSquares_apply, addChar_sum]
    exact Finset.prod_congr rfl (fun i _ => by rw [pow_two, smul_eq_mul])
  have hfac : ∀ i, (∑ t : K, ψ (Q (v i) * t ^ 2)) = χ (Q (v i)) * gaussSum χ ψ := by
    intro i
    have h := sum_addChar_smul_sq hF hψ (Units.mk0 (Q (v i)) (hw i))
    rw [Units.val_mk0] at h
    rw [← hχ] at h
    exact h
  rw [Finset.sum_congr rfl (fun y _ => hexp y),
    ← Fintype.prod_sum (fun (i : Fin (Module.finrank K V)) (t : K) => ψ (Q (v i) * t ^ 2)),
    Finset.prod_congr rfl (fun i _ => hfac i),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Brick C-scale — the scaling relation.** Scaling the form by a unit `s` scales the Gauss sum by
`χ(s)^d`: `∑_x ψ(s·Q x) = χ(s)^d · ∑_x ψ(Q x)`. Proved by changing the additive character
(`ψ(s·Q x) = (mulShift ψ s)(Q x)`) and `gaussSum_mulShift`. (For `d` even, `χ(s)^d = 1`, so the
quadratic exponential sum is scale-invariant — the fact behind the affine-quadric point count.) -/
theorem sum_addChar_quadForm_smul {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Invertible (2 : K)] (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype V] (Q : QuadraticForm K V)
    (v : Module.Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) (s : Kˣ) :
    (∑ x : V, ψ ((s : K) * Q x))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) ^ Module.finrank K V
        * ∑ x : V, ψ (Q x) := by
  have hφ : (AddChar.mulShift ψ (s : K)).IsPrimitive := by
    intro a ha
    have hmm : AddChar.mulShift (AddChar.mulShift ψ (s : K)) a = AddChar.mulShift ψ ((s : K) * a) := by
      ext x; simp only [AddChar.mulShift_apply, mul_assoc]
    rw [hmm]; exact hψ (mul_ne_zero s.ne_zero ha)
  have e1 : (∑ x : V, ψ ((s : K) * Q x)) = ∑ x : V, (AddChar.mulShift ψ (s : K)) (Q x) :=
    Finset.sum_congr rfl (fun x _ => by rw [AddChar.mulShift_apply])
  have hsq : ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
      * ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) = 1 := by
    have h := quadraticChar_sq_one (F := K) s.ne_zero
    have h2 : (((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)) ^ 2 = ((1 : ℤ) : R') := by
      rw [MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    rw [pow_two] at h2; simpa using h2
  have hgss : gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R'))
        (AddChar.mulShift ψ (s : K))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
        * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ := by
    have hms := gaussSum_mulShift ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ s
    have h3 := congrArg
      (fun z => ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K) * z) hms
    simp only at h3
    rw [← mul_assoc, hsq, one_mul] at h3
    exact h3
  rw [e1, sum_quadForm_eval hF hφ Q v hv hw, sum_quadForm_eval hF hψ Q v hv hw, hgss, mul_pow]
  ring

/-- **Brick C — the affine-quadric point count (character-sum form).** The number of solutions of
`Q x = c`, scaled by `#K`, equals `#V` plus `(∑_{t≠0} ψ(−tc)·χ(t)^d)·∑_x ψ(Q x)`. This is the
assembled affine-quadric point-count formula (Mathlib-absent), from Brick A + the scaling relation.
For `d` even, `χ(t)^d = 1`, so the bracket collapses to `q−1` (if `c=0`) or `−1` (if `c≠0`) by
additive orthogonality, giving the classical `q^{d-1} ± (q-1)q^{d/2-1}` count once `∑_x ψ(Q x)` is
evaluated via `gaussSum_sq`. -/
theorem card_quadForm_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'}
    (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (Q : QuadraticForm K V)
    (v : Module.Basis (Fin (Module.finrank K V)) K V)
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) (c : K) :
    ((univ.filter (fun x : V => Q x = c)).card : R') * (Fintype.card K : R')
      = (Fintype.card V : R')
        + (∑ t ∈ univ.erase (0 : K),
            ψ (-(t * c)) * ((quadraticChar K).ringHomComp (Int.castRingHom R')) t
              ^ Module.finrank K V) * (∑ x : V, ψ (Q x)) := by
  have hcount := count_eq_charsum hψ (fun x : V => Q x) c
  have hsplit_x : ∀ t : K,
      (∑ x : V, ψ (t * (Q x - c))) = ψ (-(t * c)) * ∑ x : V, ψ (t * Q x) := by
    intro t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hzero : ψ (-((0 : K) * c)) * (∑ x : V, ψ ((0 : K) * Q x)) = (Fintype.card V : R') := by
    simp [AddChar.map_zero_eq_one, Finset.card_univ]
  have hLHS : (∑ x : V, ∑ t : K, ψ (t * (Q x - c)))
      = (Fintype.card V : R')
        + (∑ t ∈ univ.erase (0 : K),
            ψ (-(t * c)) * ((quadraticChar K).ringHomComp (Int.castRingHom R')) t
              ^ Module.finrank K V) * (∑ x : V, ψ (Q x)) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun t _ => hsplit_x t),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), hzero, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have htne : t ≠ 0 := Finset.ne_of_mem_erase ht
    have hsc := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 t htne)
    rw [Units.val_mk0] at hsc
    rw [hsc]; ring
  rw [← hcount, hLHS]

/-- **Brick D1 — the quadratic-plus-linear sum (complete the square).** For a unit `r` and any `a'`,
`∑_w ψ(r·Q w + polar Q w a') = ψ(−r⁻¹·Q a')·∑_w ψ(r·Q w)`. The linear term is absorbed by the shift
`w ↦ w + r⁻¹·a'`; the residual constant `−r⁻¹·Q a'` factors out. This is the engine of the
hyperplane-section counts that Brick D needs (the isotropy joint-count reduces to such sums). Needs no
diagonalization or primitivity — pure reindexing + additivity of `ψ`. -/
theorem sum_addChar_quadForm_linear {K : Type*} [Field K] {R' : Type*} [CommRing R']
    (ψ : AddChar K R') {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (Q : QuadraticForm K V) (r : Kˣ) (a' : V) :
    (∑ w : V, ψ ((r : K) * Q w + QuadraticMap.polar Q w a'))
      = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q w) := by
  have hr : (r : K) ≠ 0 := r.ne_zero
  have key : ∀ w : V, (r : K) * Q w + QuadraticMap.polar Q w a'
      = (r : K) * Q (w + (r : K)⁻¹ • a') + (-((r : K)⁻¹ * Q a')) := by
    intro w
    have h1 : Q (w + (r : K)⁻¹ • a')
        = QuadraticMap.polar Q w ((r : K)⁻¹ • a') + Q w + Q ((r : K)⁻¹ • a') := by
      simp only [QuadraticMap.polar]; ring
    rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]; field_simp; ring
  calc (∑ w : V, ψ ((r : K) * Q w + QuadraticMap.polar Q w a'))
      = ∑ w : V, ψ ((r : K) * Q (w + (r : K)⁻¹ • a') + (-((r : K)⁻¹ * Q a'))) :=
        Finset.sum_congr rfl (fun w _ => by rw [key w])
    _ = ∑ w : V, ψ (-((r : K)⁻¹ * Q a')) * ψ ((r : K) * Q (w + (r : K)⁻¹ • a')) :=
        Finset.sum_congr rfl (fun w _ => by rw [AddChar.map_add_eq_mul, mul_comm])
    _ = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q (w + (r : K)⁻¹ • a')) := by
        rw [Finset.mul_sum]
    _ = ψ (-((r : K)⁻¹ * Q a')) * ∑ w : V, ψ ((r : K) * Q w) := by
        congr 1
        exact Equiv.sum_comp (Equiv.addRight ((r : K)⁻¹ • a')) (fun w => ψ ((r : K) * Q w))

/-- **Brick A2 — two-condition solution count as a character sum.** Generalizes Brick A: the number of
common solutions of `f x = c` and `g x = d`, scaled by `q²`, equals `∑_x (∑_r ψ(r(f x−c)))·(∑_s ψ(s(g x−d)))`.
This is the entry point for the hyperplane-section count `#{w : Q w = 0 ∧ polar Q w a = c}` (Brick D),
whose inner sum then evaluates via Brick D1. -/
theorem count2_eq_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] (f g : V → F) (c d : F) :
    (∑ x : V, (∑ r : F, ψ (r * (f x - c))) * (∑ s : F, ψ (s * (g x - d))))
      = ((univ.filter (fun x : V => f x = c ∧ g x = d)).card : R')
        * ((Fintype.card F : R') * (Fintype.card F : R')) := by
  have hinner : ∀ x : V, (∑ r : F, ψ (r * (f x - c))) * (∑ s : F, ψ (s * (g x - d)))
      = if (f x = c ∧ g x = d) then (Fintype.card F : R') * (Fintype.card F : R') else 0 := by
    intro x
    rw [AddChar.sum_mulShift (f x - c) hψ, AddChar.sum_mulShift (g x - d) hψ]
    simp only [sub_eq_zero]
    split_ifs with h1 h2 h2 <;> simp_all
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]


-- ============== multi-point quadratic sum (toward the symmetry-broken-base count) ==============

/-- The quadratic "difference" identity (parallelogram form): `Q(a−b) = Q a + Q b − polar Q a b`. -/
theorem quad_sub {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a b : V) :
    Q (a - b) = Q a + Q b - QuadraticMap.polar Q a b := by
  have h1 : QuadraticMap.polar Q a (-b) = Q (a - b) - Q a - Q b := by
    simp only [QuadraticMap.polar, ← sub_eq_add_neg, QuadraticMap.map_neg]
  have h2 : QuadraticMap.polar Q a (-b) = - QuadraticMap.polar Q a b := by
    rw [← neg_one_smul K b, QuadraticMap.polar_smul_right, neg_one_smul]
  rw [h2] at h1; linear_combination -h1

/-- `polar Q z ·` is additive over a finite sum in its second argument (via `polarBilin`). -/
theorem polar_sum_right {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (z : V) {ι : Type*} (s : Finset ι) (r : ι → K) (t : ι → V) :
    (∑ j ∈ s, r j * QuadraticMap.polar Q z (t j))
      = QuadraticMap.polar Q z (∑ j ∈ s, r j • t j) := by
  have hb : ∀ y, QuadraticMap.polar Q z y = Q.polarBilin z y :=
    fun y => (QuadraticMap.polarBilin_apply_apply Q z y).symm
  rw [hb, map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [hb, map_smul, smul_eq_mul])

/-- **Multi-point quadratic Gauss sum (generalizes D1).** For weights `r` summing to `R ≠ 0`,
`∑_z ψ(∑ⱼ rⱼ·Q(z−tⱼ)) = ψ(∑ⱼ rⱼ·Q(tⱼ) − R⁻¹·Q(∑ⱼ rⱼ•tⱼ))·∑_z ψ(R·Q z)`. The summand expands to
`R·Q z − polar Q z (∑rⱼ•tⱼ) + const`, collapsing to D1. THE engine for the multi-point count at a
symmetry-broken base. -/
theorem sum_addChar_multiQuad {K : Type*} [Field K] {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V)
    {ι : Type*} (s : Finset ι) (r : ι → K) (t : ι → V) (hR : (∑ j ∈ s, r j) ≠ 0) :
    (∑ z : V, ψ (∑ j ∈ s, r j * Q (z - t j)))
      = ψ ((∑ j ∈ s, r j * Q (t j)) - (∑ j ∈ s, r j)⁻¹ * Q (∑ j ∈ s, r j • t j))
        * ∑ z : V, ψ ((∑ j ∈ s, r j) * Q z) := by
  have key : ∀ z : V, (∑ j ∈ s, r j * Q (z - t j))
      = (∑ j ∈ s, r j) * Q z + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))
        + (∑ j ∈ s, r j * Q (t j)) := by
    intro z
    have e : ∀ j ∈ s, r j * Q (z - t j)
        = r j * Q z + r j * Q (t j) - r j * QuadraticMap.polar Q z (t j) := by
      intro j _; rw [quad_sub]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        polar_sum_right,
        show QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))
            = - QuadraticMap.polar Q z (∑ j ∈ s, r j • t j) by
          rw [← neg_one_smul K (∑ j ∈ s, r j • t j), QuadraticMap.polar_smul_right, neg_one_smul]]
    ring
  rw [Finset.sum_congr rfl (fun z _ => by rw [key z])]
  have hD1 := sum_addChar_quadForm_linear ψ Q (Units.mk0 (∑ j ∈ s, r j) hR)
    (-(∑ j ∈ s, r j • t j))
  rw [Units.val_mk0] at hD1
  have hfactor : (∑ z : V, ψ ((∑ j ∈ s, r j) * Q z
        + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j)) + (∑ j ∈ s, r j * Q (t j))))
      = ψ (∑ j ∈ s, r j * Q (t j))
        * ∑ z : V, ψ ((∑ j ∈ s, r j) * Q z
            + QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by rw [AddChar.map_add_eq_mul]; ring)
  rw [hfactor, hD1, QuadraticMap.map_neg, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2; ring


-- ============== the k-fold count (generalizes Brick A2 to a Finset of conditions) ==============

/-- **Brick A_k — k-fold solution count as a product-of-sums character sum.** Generalizes `count_eq_charsum`
(`A`) and `count2_eq_charsum` (`A2`) to a whole `Fintype`-indexed family of conditions: the number of common
solutions of `f j x = c j` (over all `j : ι`), scaled by `qᵏ` (`k = #ι`), equals `∑_x ∏_j (∑_{r_j} ψ(r_j(f_j x −
c_j)))`. Each inner `∑_{r_j}` is `q·[f_j x = c_j]` (additive orthogonality), and the product of these indicators
is `qᵏ·[∀ j, f_j x = c_j]`. -/
theorem countk_eq_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → V → F) (c : ι → F) :
    (∑ x : V, ∏ j : ι, (∑ r : F, ψ (r * (f j x - c j))))
      = ((univ.filter (fun x : V => ∀ j, f j x = c j)).card : R')
        * (Fintype.card F : R') ^ (Fintype.card ι) := by
  classical
  have hinner : ∀ x : V, (∏ j : ι, (∑ r : F, ψ (r * (f j x - c j))))
      = if (∀ j, f j x = c j) then ((Fintype.card F : R') ^ (Fintype.card ι)) else 0 := by
    intro x
    have h1 : (∏ j : ι, (∑ r : F, ψ (r * (f j x - c j))))
        = ∏ j : ι, (if f j x = c j then (Fintype.card F : R') else 0) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [AddChar.sum_mulShift (f j x - c j) hψ]
      simp [sub_eq_zero]
    rw [h1]
    by_cases h : ∀ j, f j x = c j
    · rw [if_pos h, Finset.prod_congr rfl (fun j _ => if_pos (h j)), Finset.prod_const,
        Finset.card_univ]
    · rw [if_neg h]
      rw [not_forall] at h
      obtain ⟨j₀, hj₀⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) (if_neg hj₀)
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

/-- **Brick A_k factored — the k-fold count as a sum over dual variables.** Expanding the product of sums in
`countk_eq_charsum` (distributivity `Fintype.prod_sum`, then `addChar_sum` collapses each `∏_j ψ` to `ψ(∑_j)`)
splits the `x`-dependent part off: `#{x : ∀ j, f_j x = c_j}·qᵏ = ∑_{r:ι→F} ψ(−∑_j r_j c_j)·∑_x ψ(∑_j r_j·f_j x)`.
With `f_j x := Q(x − t_j)` the inner `∑_x ψ(∑_j r_j·Q(x − t_j))` is exactly `sum_addChar_multiQuad` (when
`∑_j r_j ≠ 0`) or a linear boundary (`∑_j r_j = 0`) — the closed-form multi-point `Q`-count. -/
theorem countk_eq_sum_charsum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → V → F) (c : ι → F) :
    ((univ.filter (fun x : V => ∀ j, f j x = c j)).card : R')
        * (Fintype.card F : R') ^ (Fintype.card ι)
      = ∑ r : ι → F, ψ (-(∑ j : ι, r j * c j)) * ∑ x : V, ψ (∑ j : ι, r j * f j x) := by
  classical
  rw [← countk_eq_charsum hψ f c,
    Finset.sum_congr rfl (fun x _ =>
      Fintype.prod_sum (fun (j : ι) (rj : F) => ψ (rj * (f j x - c j)))),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← addChar_sum ψ Finset.univ (fun j => r j * (f j x - c j)),
    ← AddChar.map_add_eq_mul]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => show r j * (f j x - c j) = r j * f j x - r j * c j from by ring),
    Finset.sum_sub_distrib]
  ring


-- ============== the quadratic specialization (the R = ∑r_j = 0 boundary) ==============

open scoped Classical in
/-- **The linear-functional character sum (the boundary engine).** For a primitive additive character `ψ` and a
`K`-linear functional `φ : V →ₗ[K] K`, `∑_x ψ(φ x) = |V|` if `φ = 0`, else `0`. (When `φ ≠ 0`, translating by an
`x₀` with `ψ(φ x₀) ≠ 1` — supplied by primitivity, since `mulShift ψ (φ a) ≠ 1` for `φ a ≠ 0` — gives
`S = ψ(φ x₀)·S`, forcing `S = 0` in the domain `R'`.) This evaluates the `R = ∑r_j = 0` boundary of the
multi-point count, where the quadratic part drops and only the linear `polar Q · w` survives. -/
theorem sum_addChar_linearMap {K : Type*} [Field K] {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (φ : V →ₗ[K] K) :
    (∑ x : V, ψ (φ x)) = if φ = 0 then (Fintype.card V : R') else 0 := by
  by_cases hφ : φ = 0
  · rw [if_pos hφ]; subst hφ
    simp [AddChar.map_zero_eq_one, Finset.card_univ]
  · rw [if_neg hφ]
    obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by
      by_contra h
      exact hφ (LinearMap.ext fun a => by
        rw [LinearMap.zero_apply]; exact not_not.1 (fun haa => h ⟨a, haa⟩))
    have hms : AddChar.mulShift ψ (φ a) ≠ 1 := hψ ha
    obtain ⟨c, hc⟩ : ∃ c : K, ψ (φ a * c) ≠ 1 := by
      by_contra h
      refine hms ?_
      ext c
      rw [AddChar.mulShift_apply, AddChar.one_apply]
      exact not_not.1 (fun hcc => h ⟨c, hcc⟩)
    have hφx₀ : ψ (φ (c • a)) ≠ 1 := by rw [map_smul, smul_eq_mul, mul_comm]; exact hc
    have hstep : (∑ x : V, ψ (φ (x + c • a))) = ∑ x : V, ψ (φ x) :=
      Equiv.sum_comp (Equiv.addRight (c • a)) (fun x => ψ (φ x))
    have hexp : (∑ x : V, ψ (φ (x + c • a))) = ψ (φ (c • a)) * ∑ x : V, ψ (φ x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [map_add, AddChar.map_add_eq_mul, mul_comm]
    have hSS : (∑ x : V, ψ (φ x)) = ψ (φ (c • a)) * ∑ x : V, ψ (φ x) := hstep.symm.trans hexp
    have hfac : (1 - ψ (φ (c • a))) * (∑ x : V, ψ (φ x)) = 0 := by
      rw [sub_mul, one_mul, ← hSS, sub_self]
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h).symm hφx₀
    · exact h

/-- **Multi-point quadratic Gauss sum, the `R = 0` boundary (companion to `sum_addChar_multiQuad`).** When the
weights sum to `R = ∑_j r_j = 0`, the `R·Q z` term vanishes and the summand is purely *linear* in `z`:
`∑_z ψ(∑_j r_j·Q(z−t_j)) = ψ(∑_j r_j·Q(t_j))·∑_z ψ(polar Q z (−∑_j r_j•t_j))`. The surviving factor is a linear
character sum (`sum_addChar_linearMap` with `φ = (polar Q · (−∑r_j•t_j))`), so it is `|V|` if `∑_j r_j•t_j` is in
the radical of the polar form (e.g. `= 0` when nondegenerate) and `0` otherwise. -/
theorem sum_addChar_multiQuad_zero {K : Type*} [Field K] {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V)
    {ι : Type*} (s : Finset ι) (r : ι → K) (t : ι → V) (hR : (∑ j ∈ s, r j) = 0) :
    (∑ z : V, ψ (∑ j ∈ s, r j * Q (z - t j)))
      = ψ (∑ j ∈ s, r j * Q (t j))
        * ∑ z : V, ψ (QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))) := by
  have key : ∀ z : V, (∑ j ∈ s, r j * Q (z - t j))
      = QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j)) + (∑ j ∈ s, r j * Q (t j)) := by
    intro z
    have e : ∀ j ∈ s, r j * Q (z - t j)
        = r j * Q z + r j * Q (t j) - r j * QuadraticMap.polar Q z (t j) := by
      intro j _; rw [quad_sub]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        hR, zero_mul, zero_add, polar_sum_right,
        show QuadraticMap.polar Q z (-(∑ j ∈ s, r j • t j))
            = - QuadraticMap.polar Q z (∑ j ∈ s, r j • t j) by
          rw [← neg_one_smul K (∑ j ∈ s, r j • t j), QuadraticMap.polar_smul_right, neg_one_smul]]
    ring
  rw [Finset.sum_congr rfl (fun z _ => by rw [key z]), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => by rw [AddChar.map_add_eq_mul, mul_comm])


-- ============== inclusion–exclusion: value-SET counts = sum of value-POINT counts ==============

/-- **The value-set / value-point bridge (the inclusion–exclusion engine).** The number of `z` with each
"coordinate value" `h j z` lying in a prescribed `Finset` `A j` equals the sum, over all selections
`c ∈ ∏_j A j`, of the pointwise counts `#{z : ∀ j, h j z = c j}`. Pure partition additivity (fiberwise over the
value tuple). For the forms-graph this turns isotropy-class counts — each class is a value-set of the form
`Q(z − t_j) ∈ A_j` (anisotropic ↔ `K∖{0}`, isotropic-or-zero ↔ `{0}`) — into the pointwise `Q`-value counts the
Gauss toolkit (`countk_eq_sum_charsum` + `multiQuad`/`multiQuad_zero`/`linearMap`) puts in closed form. -/
theorem count_pi_setValued {K : Type*} [DecidableEq K] {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → V → K) (A : ι → Finset K) :
    (univ.filter (fun z : V => ∀ j, h j z ∈ A j)).card
      = ∑ c ∈ Fintype.piFinset A, (univ.filter (fun z : V => ∀ j, h j z = c j)).card := by
  classical
  have H : ∀ z ∈ (univ.filter (fun z : V => ∀ j, h j z ∈ A j)),
      (fun j => h j z) ∈ Fintype.piFinset A :=
    fun z hz => Fintype.mem_piFinset.2 (fun j => (Finset.mem_filter.1 hz).2 j)
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hφ⟩ j; exact congrFun hφ j
  · intro hz
    exact ⟨fun j => by rw [hz j]; exact Fintype.mem_piFinset.1 hc j, funext hz⟩

end ChainDescent
