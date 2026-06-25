/-
# Good-anchor count (increment 3, step 3e-ii(a) — the Schwartz–Zippel input, SHARED with increment 4).

To bound `normT_le`'s RHS radical-sum we need: the number of degenerate pencil ratios `(y,z)` is `O(d·q)`.
A pencil member `F_{y,z} = y•pairForm_u + z•pairForm_v` is degenerate ⟺ the pencil discriminant
`disc(y,z) = det(y·G_u + z·G_v)` (a homogeneous polynomial of degree `d` in `(y,z)`) vanishes. Provided the anchor is
*good* (`disc ≢ 0`), Schwartz–Zippel bounds the number of zeros, hence the number of degenerate ratios, by `d·q`.

This file proves the two reusable CORES of the good-anchor count:
* `mvPoly_zeros_count_le` — the Schwartz–Zippel count: `p ≠ 0 ⟹ #{f : Fin 2 → K | eval f p = 0} ≤ p.totalDegree · |K|`.
* `det_totalDegree_le` — the degree cap: `det` of a `d × d` matrix with `totalDegree ≤ 1` entries has `totalDegree ≤ d`.
Together: for the pencil discriminant `disc(y,z) = det(y·G_u + z·G_v)` (linear-entry, `≢ 0` at a good anchor), the two give
`#{(y,z) : disc(y,z) = 0} ≤ d·|K|`.

The remaining bridge to the concrete pencil (still to build) connects `disc` to degeneracy:
* (C) DEFINE `disc : MvPolynomial (Fin 2) K` as `det (fun i j => X 0 * C (A i j) + X 1 * C (B i j))`, `A, B` the Gram
  matrices of `polar pairForm_u`, `polar pairForm_v`; entry `totalDegree ≤ 1` (feeds `det_totalDegree_le`), and
  `eval (![y, z]) disc = det (y • A + z • B)`.
* (D) the LINCHPIN: `F_{y,z}` degenerate ⟺ `polarRad F_{y,z} ≠ ⊥` ⟺ `¬ (polarBilin F_{y,z}).Nondegenerate` ⟺
  `det (y • A + z • B) = 0`, via `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` (+ `toMatrix₂` of the polar bilinear form).
* (E) good anchor (∃ nondeg member) ⟹ `disc ≢ 0`, then `mvPoly_zeros_count_le` + `det_totalDegree_le` close `#degenerate ≤ d·q`.

NOT in build (scratch; `lake env lean ChainDescent/ScratchGoodAnchor.lean`).
-/
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ChainDescent

open Finset

/-- **The Schwartz–Zippel count (n = 2).** For a nonzero polynomial `p` in two variables over a finite field `K`,
the number of common zeros over `K²` is at most `p.totalDegree · |K|`. This is the analytic core of the good-anchor
count: applied to the pencil discriminant `disc(y,z)` (degree `d`, `≢ 0` at a good anchor) it gives `#degenerate ≤ d·q`. -/
theorem mvPoly_zeros_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0) :
    (Finset.univ.filter (fun f : Fin 2 → K => MvPolynomial.eval f p = 0)).card
      ≤ p.totalDegree * Fintype.card K := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  -- rewrite `piFinset (fun _ => univ) = univ` and `#univ = card K`
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  set Sz : ℕ := (Finset.univ.filter (fun f : Fin 2 → K => MvPolynomial.eval f p = 0)).card with hSz
  -- hsz : (Sz : ℚ≥0) / (card K)^2 ≤ totalDegree / card K
  set q : ℕ := Fintype.card K with hqdef
  have hqQ : (0 : ℚ≥0) < (q : ℚ≥0) := by exact_mod_cast hq
  -- clear the LHS denominator, then cancel one factor of q from the RHS
  rw [div_le_iff₀ (by positivity : (0 : ℚ≥0) < (q : ℚ≥0) ^ 2), sq, ← mul_assoc,
    div_mul_cancel₀ _ hqQ.ne'] at hsz
  -- hsz : (Sz : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) * q
  exact_mod_cast hsz

/-- **The pencil-discriminant degree bound.** The determinant of a `d × d` matrix whose every entry is a
2-variable polynomial of `totalDegree ≤ 1` (a *linear pencil* `y·A + z·B`) has `totalDegree ≤ d`. This caps the
discriminant `disc(y,z) = det(y·G_u + z·G_v)` at degree `d`, the `p.totalDegree` fed into `mvPoly_zeros_count_le`. -/
theorem det_totalDegree_le {K : Type*} [CommRing K] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin 2) K))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ d := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun σ _ => ?_))
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i : Fin d, (M (σ i) i).totalDegree
      ≤ ∑ _i : Fin d, 1 := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

end ChainDescent

#print axioms ChainDescent.mvPoly_zeros_count_le
#print axioms ChainDescent.det_totalDegree_le
