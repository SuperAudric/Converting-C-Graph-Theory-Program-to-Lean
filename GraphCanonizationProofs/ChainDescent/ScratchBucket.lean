/-
# Abstract two-bucket sum bound (increment 3, step 3e-ii — the nondeg/deg split arithmetic).

`normT_le`'s RHS is a sum over `(y,z)` of `√(|V|·|radical F_{y,z}|)`. Splitting the index set by the degeneracy
predicate `p`, the terms in each bucket obey a uniform magnitude bound (`Ma` on the nondeg bucket `¬p`, `Mb` on the deg
bucket `p`), and each bucket has a cardinality bound (`Ca`, `Cb`). This file proves the resulting arithmetic:
`∑ g ≤ Ca·Ma + Cb·Mb`. Pure `Finset`/`ℝ`, reusable. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ChainDescent

open Finset

/-- **Two-bucket sum bound.** Split `s` by predicate `p`; if `g ≤ Ma` on the `¬p` bucket and `g ≤ Mb` on the `p`
bucket, with cardinalities `≤ Ca`, `≤ Cb` respectively (and `Ma, Mb ≥ 0`), then `∑_{i∈s} g i ≤ Ca·Ma + Cb·Mb`. -/
theorem sum_two_bucket_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) (p : ι → Prop) [DecidablePred p]
    (Ma Mb Ca Cb : ℝ) (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (ha : ∀ i ∈ s, ¬ p i → g i ≤ Ma) (hb : ∀ i ∈ s, p i → g i ≤ Mb)
    (hca : ((s.filter (fun i => ¬ p i)).card : ℝ) ≤ Ca)
    (hcb : ((s.filter p).card : ℝ) ≤ Cb) :
    ∑ i ∈ s, g i ≤ Ca * Ma + Cb * Mb := by
  rw [← Finset.sum_filter_add_sum_filter_not s p g, add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ s.filter (fun i => ¬ p i), g i
        ≤ ∑ _i ∈ s.filter (fun i => ¬ p i), Ma :=
          Finset.sum_le_sum (fun i hi => ha i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2)
      _ = ((s.filter (fun i => ¬ p i)).card : ℝ) * Ma := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Ca * Ma := mul_le_mul_of_nonneg_right hca hMa
  · calc ∑ i ∈ s.filter p, g i
        ≤ ∑ _i ∈ s.filter p, Mb :=
          Finset.sum_le_sum (fun i hi => hb i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2)
      _ = ((s.filter p).card : ℝ) * Mb := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cb * Mb := mul_le_mul_of_nonneg_right hcb hMb

/-- **Deg-bucket magnitude.** If `r·k ≤ V` (the proper-subspace radical bound), then `√(V·r) ≤ V/√k`. Used with
`r = |radical F_{y,z}|`, `k = |K|`, `V = card V`: a degenerate member contributes at most `card V / √|K|`. -/
theorem sqrt_mul_le_div {V k r : ℝ} (hV : 0 ≤ V) (hk : 0 < k) (h : r * k ≤ V) :
    Real.sqrt (V * r) ≤ V / Real.sqrt k := by
  have hr2 : r ≤ V / k := (le_div_iff₀ hk).2 h
  have h1 : V * r ≤ V ^ 2 / k := by
    rw [sq, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hr2 hV
  calc Real.sqrt (V * r) ≤ Real.sqrt (V ^ 2 / k) := Real.sqrt_le_sqrt h1
    _ = V / Real.sqrt k := by rw [Real.sqrt_div (by positivity), Real.sqrt_sq hV]

end ChainDescent

#print axioms ChainDescent.sum_two_bucket_le
#print axioms ChainDescent.sqrt_mul_le_div
