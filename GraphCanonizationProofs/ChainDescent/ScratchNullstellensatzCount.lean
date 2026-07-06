/-
# Nullstellensatz discharge — the cone-covering count (WIP, route B)

The connectivity fact `hconn` (⟹ `nullstellensatz_of_connectivity`) reduces, via the route-A scaffold, to ONE
classical counting lemma:
  `cone_not_covered` — nondeg `Q` on `𝔽_q^d`, vectors `u₁,…,u_k` (`k ≤ 2` suffices via the `A_e`-hub walk) ⟹ ∃
  isotropic `a` with `polar Q uᵢ a ≠ 0` ∀`i` (the isotropic cone is not covered by `k` hyperplanes `uᵢ^⊥`).

This file builds it from the project's OWN Gauss-sum count machinery (`ChainDescent.zeroCount_sq_le` in `PairForm`,
which for a quadratic `P` bounds `(|{P=0}|·q − qᵈ)² ≤ (q−1)²·(qᵈ·|radical P|)`), avoiding any from-scratch magnitude
work. For nondegenerate `Q` the radical is `{0}`, giving the cone size `|cone| ≥ (qᵈ − (q−1)·√(qᵈ))/q`.

**STATUS (2026-07-06 — BEGUN).** `radical_card_one` + `cone_card_lower` landed. Next: the hyperplane-section upper
bound (via `norm_sq_sum_addChar_quadForm_linear_le`), then the union bound `cone_not_covered`, then the walk/hub.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`, `native_decide` banned. WIP.
-/
import ChainDescent.PairForm
import ChainDescent.ScratchNullstellensatz

namespace ChainDescent.Nullstellensatz

open QuadraticMap

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false in
/-- **The radical of a nondegenerate `Q` is trivial** (the `zeroCount_sq_le` "radical filter" has card 1). -/
theorem radical_card_one (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hh
    refine hQnd.1 h (fun x => ?_)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hh x
  · rintro rfl x
    simp [QuadraticMap.polar]

/-- **The isotropic cone is large.** For a nondegenerate `Q` over `ℂ`-valued primitive `ψ`,
`qᵈ − (q−1)·√(qᵈ) ≤ |cone|·q`, i.e. `|cone| ≥ q^{d−1} − (q−1)q^{d/2−1}` (the classical count with the Gauss
error term). Direct from `zeroCount_sq_le` (radical trivial) + `√` monotonicity. `N := |V| = qᵈ`. -/
theorem cone_card_lower {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (Fintype.card V : ℝ) - ((Fintype.card K : ℝ) - 1) * Real.sqrt (Fintype.card V)
      ≤ ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) * (Fintype.card K) := by
  have hsq := zeroCount_sq_le hψ Q
  rw [radical_card_one Q hQnd, Nat.cast_one, mul_one] at hsq
  set z : ℝ := ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) with hz
  set q : ℝ := (Fintype.card K : ℝ) with hq
  set N : ℝ := (Fintype.card V : ℝ) with hN
  -- hsq : (z*q - N)^2 ≤ (q-1)^2 * N
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast Fintype.card_pos
    linarith
  -- |z*q - N| ≤ (q-1)*√N
  have habs : |z * q - N| ≤ (q - 1) * Real.sqrt N := by
    have hrhs : ((q - 1) * Real.sqrt N) ^ 2 = (q - 1) ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt hNnonneg]
    have hle2 : (z * q - N) ^ 2 ≤ ((q - 1) * Real.sqrt N) ^ 2 := by rw [hrhs]; exact hsq
    have hle := Real.sqrt_le_sqrt hle2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hle
  have := (abs_le.mp habs).1
  linarith