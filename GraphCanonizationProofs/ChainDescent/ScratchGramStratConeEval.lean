/-
# Route A, Step C — Piece 1c: the closed form of `isoConeSum` (even dimension) — the analytic core

**What this module builds (recovery doc §9.7).** The discharge of `IsoConeSumSeparatesGram` needs the closed form of the
isotropic-cone character sum `isoConeSum Q ψ y = ∑_{w:Qw=0} ψ(polar w y)`. For **even** ambient dimension (the forms-graph
case `VO^ε_{2m}`), the quadratic Gauss sum is scale-invariant (`∑_x ψ(s·Qx) = χ(s)^n·G₁ = G₁` for `n` even, `s≠0`), which
collapses the `s`-sum to additive orthogonality. Result:

  **`isoConeSum_eval_even`:** `|K| · isoConeSum Q ψ y = |V|·𝟙[y=0] + G₁·(|K|·𝟙[Qy=0] − 1)`, `G₁ = ∑_x ψ(Q x)`.

(Stated with the `|K|·` factor to avoid `|K|⁻¹`.) Proof: expand `𝟙[Qw=0] = |K|⁻¹∑_s ψ(s·Qw)` (as `|K|·`), swap sums,
split `s=0` (linear term `∑_w ψ(polar w y) = |V|·𝟙[y=0]`, `sum_addChar_linearMap` + nondeg) from `s≠0` (Brick D1
`sum_addChar_quadForm_linear` gives `ψ(−s⁻¹Qy)·G(s)`; Brick C-scale `sum_addChar_quadForm_smul` + `χ(s)^n = 1` for even
`n` gives `G(s) = G₁`), then reindex `s ↦ −s⁻¹` (an involution) to additive orthogonality `∑_{t≠0} ψ(t·Qy) = |K|·𝟙[Qy=0]−1`.

Corollary **`isoConeSum_ne_zero`**: at even dim `isoConeSum Q ψ y ≠ 0` for every `y` (the non-degeneracy that powers the
off-diagonal extraction) — `G₁ ≠ 0` (`sum_addChar_quadForm_ne_zero`, CharZero) and the scalar `|K|𝟙[Qy=0]−1 ∈ {|K|−1, −1}`
is a nonzero integer, plus `isoConeSum 0 = #{Qw=0} ≠ 0` directly.

Reuses `GaussCount` (Bricks D1, C-scale, linear-map sum, Gauss-sum ≠ 0), `Coordinatization`
(`exists_orthoAnisotropic_basis`), `ScratchGramStratGauss` (`isoConeSum`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratGauss
import ChainDescent.GaussCount
import ChainDescent.Coordinatization

namespace ChainDescent.GramStrat

open QuadraticMap Finset ChainDescent

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **`(associated Q).SeparatingLeft` from `polarBilin` nondegeneracy** (char ≠ 2). `polarBilin = 2 • associated`, so a
zero `associated`-row forces a zero `polarBilin`-row, hence the vector is `0`. -/
theorem associated_separatingLeft_of_polarBilin_nondeg [Invertible (2 : K)]
    (hnd : (Q.polarBilin).Nondegenerate) : (QuadraticMap.associated Q).SeparatingLeft := by
  intro x hx
  refine hnd.1 x (fun n => ?_)
  have e2 : (Q.polarBilin) x n = (2 : ℕ) • (QuadraticMap.associated Q) x n := by
    conv_lhs => rw [← QuadraticMap.two_nsmul_associated (S := K)]
    simp only [two_nsmul, LinearMap.add_apply]
  rw [e2, hx n, smul_zero]

/-- **The even-dimension closed form of `isoConeSum`.** `|K| · isoConeSum Q ψ y = |V|·𝟙[y=0] + G₁·(|K|·𝟙[Qy=0] − 1)`,
`G₁ = ∑_x ψ(Q x)`. Char ≠ 2, `Q` nondegenerate, `finrank` even. -/
theorem isoConeSum_eval_even [Invertible (2 : K)] (hF : ringChar K ≠ 2) [FiniteDimensional K V]
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (hnd : (Q.polarBilin).Nondegenerate) (heven : Even (Module.finrank K V)) (y : V) :
    (Fintype.card K : R') * isoConeSum Q ψ y
      = (Fintype.card V : R') * (if y = 0 then (1 : R') else 0)
        + (∑ x : V, ψ (Q x)) * ((Fintype.card K : R') * (if Q y = 0 then (1 : R') else 0) - 1) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  have hsep := associated_separatingLeft_of_polarBilin_nondeg hnd
  obtain ⟨v, hv, hw⟩ := exists_orthoAnisotropic_basis Q hsep
  -- Step 1: |K| · isoConeSum = ∑_s ∑_w ψ(s·Qw + polar w y)
  have hcard : ∀ w : V, (∑ s : K, ψ (s * Q w)) = if Q w = 0 then (Fintype.card K : R') else 0 := by
    intro w
    have h := AddChar.sum_mulShift (Q w) hψ
    simp_rw [mul_comm _ (Q w)] at h ⊢
    rw [h]; split_ifs <;> simp
  have step1 : (Fintype.card K : R') * isoConeSum Q ψ y
      = ∑ s : K, ∑ w : V, ψ (s * Q w + QuadraticMap.polar Q w y) := by
    rw [isoConeSum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ univ) => AddChar.map_add_eq_mul ψ (s * Q w)
        (QuadraticMap.polar Q w y)), ← Finset.sum_mul, hcard w]
    split_ifs <;> ring
  rw [step1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
  -- s = 0 term:  ∑_w ψ(polar w y) = |V|·𝟙[y=0]
  have hzero : (∑ w : V, ψ ((0 : K) * Q w + QuadraticMap.polar Q w y))
      = (Fintype.card V : R') * (if y = 0 then (1 : R') else 0) := by
    have hlin : (∑ w : V, ψ ((0 : K) * Q w + QuadraticMap.polar Q w y))
        = ∑ w : V, ψ ((QuadraticMap.polarBilin Q).flip y w) := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [zero_mul, zero_add, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
    rw [hlin, sum_addChar_linearMap hψ]
    have hflip : ((QuadraticMap.polarBilin Q).flip y = 0) ↔ (y = 0) := by
      constructor
      · intro h
        refine hnd.2 y (fun n => ?_)
        have hn := LinearMap.congr_fun h n
        rwa [LinearMap.flip_apply, LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply] at hn
      · intro h; subst h; simp
    by_cases hy : y = 0
    · rw [if_pos (hflip.mpr hy), if_pos hy, mul_one]
    · rw [if_neg (fun h => hy (hflip.mp h)), if_neg hy, mul_zero]
  rw [hzero]
  -- s ≠ 0 terms:  ∑_{s≠0} ψ(−s⁻¹Qy)·G₁ = G₁·(∑_{s≠0} ψ(−s⁻¹Qy))
  have hne : ∀ s ∈ univ.erase (0 : K),
      (∑ w : V, ψ (s * Q w + QuadraticMap.polar Q w y))
        = ψ (-(s⁻¹ * Q y)) * (∑ x : V, ψ (Q x)) := by
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    have hD1 := sum_addChar_quadForm_linear ψ Q (Units.mk0 s hs0) y
    rw [Units.val_mk0] at hD1
    rw [hD1]
    congr 1
    have hscale := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 s hs0)
    rw [Units.val_mk0] at hscale
    rw [hscale]
    -- χ(s)^n = 1 for even n
    have hchisq : χ s * χ s = 1 := by
      have h := quadraticChar_sq_one (F := K) hs0
      have h2 : (χ s) ^ 2 = (1 : R') := by
        rw [hχ, MulChar.ringHomComp_apply, ← map_pow]
        have hc := congrArg (Int.castRingHom R') h
        rwa [map_one] at hc
      rw [pow_two] at h2; exact h2
    obtain ⟨k, hk⟩ := heven
    rw [hk, show k + k = 2 * k from (two_mul k).symm, pow_mul, pow_two, hchisq, one_pow, one_mul]
  rw [Finset.sum_congr rfl hne, ← Finset.sum_mul]
  congr 1
  rw [mul_comm]
  congr 1
  -- reindex s ↦ −s⁻¹ (involution) and additive orthogonality
  have hinv : Function.Involutive (fun s : K => -s⁻¹) := by
    intro s; simp only [inv_neg, inv_inv, neg_neg]
  have hreidx : (∑ s ∈ univ.erase (0 : K), ψ (-(s⁻¹ * Q y)))
      = (∑ s ∈ univ.erase (0 : K), ψ (s * Q y)) := by
    refine Finset.sum_nbij' (fun s => -s⁻¹) (fun s => -s⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      exact Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (inv_ne_zero (Finset.ne_of_mem_erase hs)),
        Finset.mem_univ _⟩
    · intro s hs
      exact Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (inv_ne_zero (Finset.ne_of_mem_erase hs)),
        Finset.mem_univ _⟩
    · intro s _; exact hinv s
    · intro s _; exact hinv s
    · intro s _; rw [neg_mul]
  rw [hreidx]
  -- ∑_{s≠0} ψ(s·Qy) = |K|·𝟙[Qy=0] − 1
  have hfull : (∑ s : K, ψ (s * Q y)) = if Q y = 0 then (Fintype.card K : R') else 0 := hcard y
  rw [← Finset.add_sum_erase _ (fun s : K => ψ (s * Q y)) (Finset.mem_univ (0 : K))] at hfull
  rw [zero_mul, AddChar.map_zero_eq_one] at hfull
  -- hfull : 1 + ∑_{s≠0} ψ(s·Qy) = if Qy=0 then |K| else 0
  by_cases hQy : Q y = 0
  · rw [if_pos hQy] at hfull; rw [if_pos hQy, mul_one]; linear_combination hfull
  · rw [if_neg hQy] at hfull; rw [if_neg hQy, mul_zero]; linear_combination hfull

/-- **Even-dim non-degeneracy of the cone sum.** At even ambient dimension `isoConeSum Q ψ y ≠ 0` for every `y`
(char zero). For `y = 0` it is `#{w:Qw=0} ≠ 0`; for `y ≠ 0` the closed form gives `G₁·(|K|·𝟙[Qy=0]−1)` with `G₁ ≠ 0`
and the integer factor `|K|·𝟙[Qy=0]−1 ∈ {|K|−1, −1}` nonzero. -/
theorem isoConeSum_ne_zero [Invertible (2 : K)] (hF : ringChar K ≠ 2) [FiniteDimensional K V]
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (hnd : (Q.polarBilin).Nondegenerate) (heven : Even (Module.finrank K V)) (y : V) :
    isoConeSum Q ψ y ≠ 0 := by
  have hK : (Fintype.card K : R') ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  intro hzero
  have heval := isoConeSum_eval_even hF hψ hnd heven y
  rw [hzero, mul_zero] at heval
  -- 0 = |V|·𝟙[y=0] + G₁·(|K|·𝟙[Qy=0]−1)
  obtain ⟨vb, hvb, hwb⟩ := exists_orthoAnisotropic_basis Q
    (associated_separatingLeft_of_polarBilin_nondeg hnd)
  have hG1 : (∑ x : V, ψ (Q x)) ≠ 0 := sum_addChar_quadForm_ne_zero hF hψ Q vb hvb hwb
  by_cases hy : y = 0
  · -- then Qy = 0 too, and |V| + G₁·(|K|−1) = 0; but isoConeSum 0 = #{Qw=0} directly
    subst hy
    have hQ0 : Q (0 : V) = 0 := by simp
    rw [if_pos rfl, if_pos hQ0, mul_one, mul_one] at heval
    -- heval : 0 = |V| + G₁·(|K| − 1)
    -- Contra via the direct value isoConeSum 0 = #{w:Qw=0}, a positive nat, but we use hzero on the direct sum
    have hdirect : isoConeSum Q ψ (0 : V) = ((univ.filter (fun w : V => Q w = 0)).card : R') := by
      rw [isoConeSum,
        Finset.sum_congr rfl (fun w _ => by rw [QuadraticMap.polar_zero_right,
          AddChar.map_zero_eq_one]),
        Finset.sum_boole]
    rw [hdirect] at hzero
    have : ((univ.filter (fun w : V => Q w = 0)).card : R') ≠ 0 := by
      have hmem : (0 : V) ∈ univ.filter (fun w : V => Q w = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ0⟩
      have hpos : 0 < (univ.filter (fun w : V => Q w = 0)).card :=
        Finset.card_pos.mpr ⟨0, hmem⟩
      exact_mod_cast hpos.ne'
    exact this hzero
  · -- y ≠ 0: |V|·0 + G₁·(|K|·𝟙[Qy=0]−1) = 0, factor nonzero
    rw [if_neg hy, mul_zero, zero_add] at heval
    rcases mul_eq_zero.mp heval.symm with h | h
    · exact hG1 h
    · -- |K|·𝟙[Qy=0] − 1 = 0
      by_cases hQy : Q y = 0
      · rw [if_pos hQy, mul_one] at h
        -- |K| − 1 = 0 ⟹ |K| = 1, impossible (|K| ≥ 2)
        have hc1 : (Fintype.card K : R') = 1 := by linear_combination h
        have hc2 : Fintype.card K = 1 := by exact_mod_cast hc1
        have h1 : (1 : ℕ) < Fintype.card K := Fintype.one_lt_card
        omega
      · rw [if_neg hQy, mul_zero, zero_sub] at h
        exact one_ne_zero (neg_eq_zero.mp h)

end ChainDescent.GramStrat
