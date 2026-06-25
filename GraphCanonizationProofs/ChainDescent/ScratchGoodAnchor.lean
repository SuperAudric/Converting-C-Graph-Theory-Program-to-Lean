/-
# Good-anchor count (increment 3, step 3e-ii(a) — the Schwartz–Zippel input, SHARED with increment 4).

To bound `normT_le`'s RHS radical-sum we need: the number of degenerate pencil ratios `(y,z)` is `O(d·q)`.
A pencil member `F_{y,z} = y•pairForm_u + z•pairForm_v` is degenerate ⟺ the pencil discriminant
`disc(y,z) = det(y·G_u + z·G_v)` (a homogeneous polynomial of degree `d` in `(y,z)`) vanishes. Provided the anchor is
*good* (`disc ≢ 0`), Schwartz–Zippel bounds the number of zeros, hence the number of degenerate ratios, by `d·q`.

**FULLY PROVEN (2026-06-25, all axiom-clean `[propext, Classical.choice, Quot.sound]`).** Capstone:
* `degenerate_count_le` — **THE good-anchor count**: given a good anchor (`∃ y z, polarRad (y•P + z•R) = ⊥`),
  `#{(y,z) : polarRad (y•P + z•R) ≠ ⊥} ≤ d·|K|`. (`P, R` = `pairForm_u, pairForm_v`; `d` = basis dimension.)

Analytic cores:
* `mvPoly_zeros_count_le` — the Schwartz–Zippel count: `p ≠ 0 ⟹ #{f : Fin 2 → K | eval f p = 0} ≤ p.totalDegree · |K|`
  (`pencilZeros_count_le` = its `K × K` form via the `(y,z) ↦ ![y,z]` bijection).
* `det_totalDegree_le` — the degree cap: `det` of a `d × d` matrix with `totalDegree ≤ 1` entries has `totalDegree ≤ d`.

The concrete-pencil bridge (all landed):
* (C) `pencilDisc A B := det (fun i j => X 0 * C (A i j) + X 1 * C (B i j))`; `pencilDisc_totalDegree_le` (deg ≤ d via
  `det_totalDegree_le`) + `pencilDisc_eval` (`eval ![y,z] (pencilDisc A B) = det (y•A + z•B)`, via `RingHom.map_det`).
* (D) the LINCHPIN: `polarRad_ne_bot_iff_det_eq_zero` — `polarRad G ≠ ⊥ ⟺ det (toMatrix₂ b b (polarBilin G)) = 0`, via
  `polarRad_eq_bot_iff_separatingRight` (`polarRad G = ⊥ ⟺ (polarBilin G).SeparatingRight`) + Mathlib
  `LinearMap.separatingRight_iff_det_ne_zero`. `toMatrix₂_polarBilin_pencil` + `polar_pencil` give `toMatrix₂ b b
  (polarBilin (y•P+z•R)) = y•A + z•B`.
* (E) good anchor ⟹ `pencilDisc A B ≠ 0` (evaluate at the nondeg witness), then the cores close `#degenerate ≤ d·q`.

REMAINING for 3e-ii: this count feeds the nondeg/deg split of `normT_le`'s RHS (with `ScratchCorank.radical_card_mul_card_le`
for the deg magnitude) + χ-norm `‖χy‖∈{0,1}` + the `c₀` counting identity + arithmetic. See the forms-graph plan §13.

NOT in build (scratch; `lake env lean ChainDescent/ScratchGoodAnchor.lean`; needs `lake build ChainDescent.ScratchCorank` first
for the `polarRad` import).
-/
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import ChainDescent.ScratchCorank

namespace ChainDescent

open Finset Module

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

open MvPolynomial in
/-- The **pencil discriminant** of two matrices `A, B` over `K`: the determinant of the linear-pencil matrix
`y·A + z·B` packaged as a 2-variable polynomial `det(X₀·A + X₁·B) : MvPolynomial (Fin 2) K`. -/
noncomputable def pencilDisc {K : Type*} [CommRing K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) : MvPolynomial (Fin 2) K :=
  (Matrix.of fun i j => X (0 : Fin 2) * C (A i j) + X 1 * C (B i j)).det

open MvPolynomial in
/-- `pencilDisc A B` has `totalDegree ≤ d` (each entry is linear in `(X₀, X₁)`). -/
theorem pencilDisc_totalDegree_le {K : Type*} [CommRing K] [Nontrivial K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) : (pencilDisc A B).totalDegree ≤ d := by
  refine det_totalDegree_le _ (fun i j => ?_)
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩ <;>
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero, MvPolynomial.totalDegree_X]

open MvPolynomial in
/-- Evaluating `pencilDisc A B` at `(y, z)` recovers `det(y·A + z·B)`. -/
theorem pencilDisc_eval {K : Type*} [CommRing K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) (y z : K) :
    MvPolynomial.eval ![y, z] (pencilDisc A B) = (y • A + z • B).det := by
  rw [pencilDisc, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply]

section Bridge
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Polar of the pencil form `y•P + z•R` is the linear combination of the polars. -/
theorem polar_pencil (P R : QuadraticForm K V) (y z : K) (x h : V) :
    QuadraticMap.polar (y • P + z • R) x h
      = y * QuadraticMap.polar P x h + z * QuadraticMap.polar R x h := by
  simp only [QuadraticMap.polar, QuadraticMap.add_apply, QuadraticMap.smul_apply, smul_eq_mul]
  ring

/-- The polar-radical is trivial ⟺ the polar bilinear form separates on the right. -/
theorem polarRad_eq_bot_iff_separatingRight (G : QuadraticForm K V) :
    polarRad G = ⊥ ↔ (QuadraticMap.polarBilin G).SeparatingRight := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro hh y hy
    refine hh y (mem_polarRad.2 (fun x => ?_))
    rw [← QuadraticMap.polarBilin_apply_apply]; exact hy x
  · intro hh y hy
    refine hh y (fun x => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]; exact (mem_polarRad.1 hy) x

/-- **Degeneracy ⟺ vanishing determinant** (the bridge linchpin). For a basis `b`, the pencil member `G` is degenerate
(`polarRad G ≠ ⊥`) iff the determinant of the Gram matrix of its polar form vanishes. -/
theorem polarRad_ne_bot_iff_det_eq_zero {d : ℕ} (b : Basis (Fin d) K V) (G : QuadraticForm K V) :
    polarRad G ≠ ⊥ ↔ (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin G)).det = 0 := by
  rw [ne_eq, polarRad_eq_bot_iff_separatingRight, LinearMap.separatingRight_iff_det_ne_zero b,
    not_ne_iff]

/-- The Gram matrix of the pencil's polar form is the linear pencil `y•A + z•B` of the Gram matrices. -/
theorem toMatrix₂_polarBilin_pencil {d : ℕ} (b : Basis (Fin d) K V)
    (P R : QuadraticForm K V) (y z : K) :
    LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (y • P + z • R))
      = y • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P)
        + z • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, LinearMap.toMatrix₂_apply,
    LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, polar_pencil,
    smul_eq_mul, smul_eq_mul]

end Bridge

/-- The Schwartz–Zippel count over `K × K` (via the `(y,z) ↦ ![y,z]` bijection). -/
theorem pencilZeros_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0) :
    (Finset.univ.filter (fun yz : K × K => MvPolynomial.eval ![yz.1, yz.2] p = 0)).card
      ≤ p.totalDegree * Fintype.card K := by
  refine le_trans (le_of_eq ?_) (mvPoly_zeros_count_le hp)
  refine Finset.card_nbij' (fun yz => ![yz.1, yz.2]) (fun f => (f 0, f 1)) ?_ ?_ ?_ ?_
  · intro yz hyz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
    exact hyz
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rwa [show (![(f 0), (f 1)] : Fin 2 → K) = f from by ext i; fin_cases i <;> rfl]
  · intro yz _; rfl
  · intro f _; ext i; fin_cases i <;> rfl

/-- **THE GOOD-ANCHOR COUNT.** For a good anchor (∃ nondegenerate pencil member `polarRad (y•P+z•R) = ⊥`), the number of
*degenerate* ratios `(y,z)` is at most `d·|K|`. Assembles the analytic cores (`pencilZeros_count_le`,
`pencilDisc_totalDegree_le`) with the bridge (`polarRad_ne_bot_iff_det_eq_zero`, `toMatrix₂_polarBilin_pencil`,
`pencilDisc_eval`) on the pencil discriminant `disc = det(X₀·A + X₁·B)`, `A,B` the Gram matrices of `polar P, polar R`. -/
theorem degenerate_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module K V] {d : ℕ} (b : Basis (Fin d) K V)
    (P R : QuadraticForm K V) (hgood : ∃ y z : K, polarRad (y • P + z • R) = ⊥) :
    (Finset.univ.filter (fun yz : K × K => polarRad (yz.1 • P + yz.2 • R) ≠ ⊥)).card
      ≤ d * Fintype.card K := by
  set A := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P) with hA
  set B' := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) with hB
  have hiff : ∀ y z : K, polarRad (y • P + z • R) ≠ ⊥
      ↔ MvPolynomial.eval ![y, z] (pencilDisc A B') = 0 := by
    intro y z
    rw [polarRad_ne_bot_iff_det_eq_zero b, toMatrix₂_polarBilin_pencil b, ← hA, ← hB,
      ← pencilDisc_eval A B' y z]
  obtain ⟨y₀, z₀, h0⟩ := hgood
  have hne0 : MvPolynomial.eval ![y₀, z₀] (pencilDisc A B') ≠ 0 :=
    fun heq => (hiff y₀ z₀).mpr heq h0
  have hdisc : pencilDisc A B' ≠ 0 := fun hc => hne0 (by rw [hc, map_zero])
  calc (Finset.univ.filter (fun yz : K × K => polarRad (yz.1 • P + yz.2 • R) ≠ ⊥)).card
      = (Finset.univ.filter
          (fun yz : K × K => MvPolynomial.eval ![yz.1, yz.2] (pencilDisc A B') = 0)).card := by
        refine Finset.card_bij (fun yz _ => yz) ?_ (fun _ _ _ _ h => h) ?_
        · intro yz hyz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
          exact (hiff yz.1 yz.2).1 hyz
        · intro yz hyz
          refine ⟨yz, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
          exact (hiff yz.1 yz.2).2 hyz
    _ ≤ (pencilDisc A B').totalDegree * Fintype.card K := pencilZeros_count_le hdisc
    _ ≤ d * Fintype.card K := by gcongr; exact pencilDisc_totalDegree_le A B'

end ChainDescent

#print axioms ChainDescent.mvPoly_zeros_count_le
#print axioms ChainDescent.det_totalDegree_le
#print axioms ChainDescent.pencilDisc_totalDegree_le
#print axioms ChainDescent.pencilDisc_eval
#print axioms ChainDescent.polarRad_ne_bot_iff_det_eq_zero
#print axioms ChainDescent.degenerate_count_le
