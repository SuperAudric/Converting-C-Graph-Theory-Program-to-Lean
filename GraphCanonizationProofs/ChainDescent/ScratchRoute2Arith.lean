import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ChainDescent

/-- **Route 2 tail arithmetic.** From the tight count `2·NS ≤ zu + n + T`, the loose zero-count
`zu·q ≤ n + (q−1)·√n·√q` (corank-1), the triangle `T·q² ≤ (q−1)²·n`, and the family range `q⁴ ≤ n` (`d ≥ 4`),
`q ≥ 3`: `NS ≤ (1 − 1/(4q²))·n`, i.e. `4q²·NS ≤ (4q²−1)·n`. The `√` only appears internally; the final gap
`δ = 1/(4q²)` is clean. -/
theorem c0_route2_arith {n q NS zu T : ℝ} (hn : 0 < n) (hq : 0 < q)
    (hcount : 2 * NS ≤ zu + n + T)
    (hzu : zu * q ≤ n + (q - 1) * Real.sqrt n * Real.sqrt q)
    (hT : T * q ^ 2 ≤ (q - 1) ^ 2 * n)
    (hq1 : q ^ 4 ≤ n) (hq3 : 3 ≤ q) :
    4 * q ^ 2 * NS ≤ (4 * q ^ 2 - 1) * n := by
  set r := Real.sqrt q with hrdef
  set m := Real.sqrt n with hmdef
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = q := Real.sq_sqrt hq.le
  have hm2 : m ^ 2 = n := Real.sq_sqrt hn.le
  -- m ≥ r⁴  (from n ≥ q⁴)
  have hrm4 : r ^ 4 ≤ m := by
    have hq2 : r ^ 4 = q ^ 2 := by rw [← hr2]; ring
    rw [hq2, hmdef]
    calc (q : ℝ) ^ 2 = Real.sqrt ((q ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (q ^ 4) := by rw [show ((q : ℝ) ^ 2) ^ 2 = q ^ 4 from by ring]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hq1
  -- r ≥ √3 > 1
  have hr3 : 3 ≤ r ^ 2 := by rw [hr2]; exact hq3
  have hr1 : 1 ≤ r := by nlinarith [hr.le]
  -- T·q² ≤ (q−1)²·n  ⟹  feed as r-poly; zu·q ≤ n + (q−1)·m·r
  have hzu' : zu * r ^ 2 ≤ m ^ 2 + (r ^ 2 - 1) * m * r := by
    rw [hr2, hm2]; exact hzu
  have hT' : T * r ^ 4 ≤ (r ^ 2 - 1) ^ 2 * m ^ 2 := by
    have : T * (r ^ 2) ^ 2 ≤ (r ^ 2 - 1) ^ 2 * n := by rw [hr2]; exact hT
    rw [hm2]; rw [show (r ^ 2) ^ 2 = r ^ 4 from by ring] at this; exact this
  -- the key polynomial inequality `2r³ − 2r² − 3r + 2 ≥ 0` (for r² ≥ 3)
  have key : 2 * r ^ 3 - 2 * r ^ 2 - 3 * r + 2 ≥ 0 := by nlinarith [hr3, hr1, sq_nonneg (r - 1), sq_nonneg r]
  -- assemble: 2r⁴·hcount, 2r²·hzu', 2·hT', then the two closing nonnegativity products.
  have hA := mul_le_mul_of_nonneg_left hcount (show (0 : ℝ) ≤ 2 * r ^ 4 from by positivity)
  have hB := mul_le_mul_of_nonneg_left hzu' (show (0 : ℝ) ≤ 2 * r ^ 2 from by positivity)
  have hC := mul_le_mul_of_nonneg_left hT' (show (0 : ℝ) ≤ (2 : ℝ) from by norm_num)
  have h23 : (0 : ℝ) ≤ 2 * r ^ 2 - 3 := by linarith [hr3]
  have hD : (0 : ℝ) ≤ m * ((m - r ^ 4) * (2 * r ^ 2 - 3)) :=
    mul_nonneg hm (mul_nonneg (sub_nonneg.2 hrm4) h23)
  have hE : (0 : ℝ) ≤ m * (r ^ 3 * (2 * r ^ 3 - 2 * r ^ 2 - 3 * r + 2)) :=
    mul_nonneg hm (mul_nonneg (by positivity) key)
  have hgoal : 4 * (r ^ 2) ^ 2 * NS ≤ (4 * (r ^ 2) ^ 2 - 1) * m ^ 2 := by
    nlinarith [hA, hB, hC, hD, hE, hm2, hm, hr.le]
  rw [hr2, hm2] at hgoal
  convert hgoal using 2

end ChainDescent

#print axioms ChainDescent.c0_route2_arith
