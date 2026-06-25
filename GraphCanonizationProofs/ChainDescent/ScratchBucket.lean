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

/-- **The final c₀ bound (3e-iii finish).** From the counting bound `2·NS ≤ 2·z_u + n + T` (`card_agree_le`), the `|T|`
bound `T ≤ q·√n + d·n/√q` (`normT_bucket_bound`, ÷q), and the zero-count `z_u·q ≤ n + (q−1)·n/√q` (`zeroCount_sq_le` with
the proper-subspace radical bound), under the threshold `64q² ≤ n` (i.e. `d ≥ 3`), `64d² ≤ q`, `256 ≤ q`: `NS ≤ ¾·n`, i.e.
`c₀ = NS/n ≤ ¾`. -/
theorem c0_le {n q dR T zu NS : ℝ} (hn : 0 < n) (hq : 0 < q) (hd : 0 ≤ dR)
    (hcount : 2 * NS ≤ 2 * zu + n + T)
    (hT : T ≤ q * Real.sqrt n + dR * n / Real.sqrt q)
    (hzu : zu * q ≤ n + (q - 1) * n / Real.sqrt q)
    (hq1 : 64 * q ^ 2 ≤ n) (hq2 : 64 * dR ^ 2 ≤ q) (hq3 : 256 ≤ q) :
    NS ≤ 3 / 4 * n := by
  set r := Real.sqrt q with hrdef
  set m := Real.sqrt n with hmdef
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hnn : m * m = n := Real.mul_self_sqrt hn.le
  have h8q : 8 * q ≤ m := by
    rw [hmdef, show (8 : ℝ) * q = Real.sqrt ((8 * q) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq1])
  have h8d : 8 * dR ≤ r := by
    rw [hrdef, show (8 : ℝ) * dR = Real.sqrt ((8 * dR) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq2])
  have h16 : (16 : ℝ) ≤ r := by
    rw [hrdef, show (16 : ℝ) = Real.sqrt (16 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq3])
  -- T ≤ n/4
  have hA : q * m ≤ n / 8 := by nlinarith [mul_le_mul_of_nonneg_right h8q hm, hnn]
  have hB : dR * n / r ≤ n / 8 := by
    rw [div_le_iff₀ hr]; nlinarith [mul_le_mul_of_nonneg_right h8d hn.le]
  have hTb : T ≤ n / 4 := by linarith [hT, hA, hB]
  -- z_u ≤ n/8
  have hC : n ≤ q * n / 16 := by nlinarith [hq3, hn]
  have hD : (q - 1) * n / r ≤ q * n / 16 := by
    rw [div_le_iff₀ hr]; nlinarith [mul_le_mul_of_nonneg_left h16 hq.le, hn.le, mul_nonneg hq.le hn.le]
  have hzub : zu ≤ n / 8 := by
    have hzq : zu * q ≤ n / 8 * q := by nlinarith [hzu, hC, hD]
    exact le_of_mul_le_mul_right hzq hq
  linarith [hcount, hTb, hzub]

end ChainDescent

#print axioms ChainDescent.sum_two_bucket_le
#print axioms ChainDescent.sqrt_mul_le_div
#print axioms ChainDescent.c0_le
