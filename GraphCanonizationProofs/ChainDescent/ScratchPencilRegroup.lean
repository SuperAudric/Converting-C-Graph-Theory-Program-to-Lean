/-
# Projective-ratio regroup (corank tightening, step A-regroup + C-input).

`ScratchTBound`'s degenerate bucket sums `√(|V|·|radical(y•P+z•R)|)` over pairs `(y,z)` with `y,z ≠ 0`. The
corank-budget `∑_t corank ≤ d` (`ScratchPencilCorank.sum_finrankKer_le`) lives over *ratios* `t = z/y`, so this module
regroups the pair-sum into a ratio-sum: each ratio has `q−1` representative pairs, all sharing one corank (the Gram
`y•A+z•B = y·(A + (z/y)•B)` has the same kernel as `A + (z/y)•B`). Combined with `concentration_bound`, the degenerate
bucket is `≤ 2·|K|·(|V|/√|K|)` — the `d`-free bound that drops `ScratchBucket.c0_le`'s `hq2`.

This file builds the regroup infrastructure:
* `ker_smul_mulVecLin` / `finrankKer_ratio` — scale-invariance of the corank.

NOT in build (scratch).
-/
import ChainDescent.ScratchPencilBridge
import ChainDescent.ScratchGoodAnchor

namespace ChainDescent

open Polynomial Matrix Finset Module QuadraticMap

variable {K : Type*} [Field K] {d : ℕ}

/-- Scaling a matrix by a nonzero constant preserves the kernel of its `mulVecLin`. -/
theorem ker_smul_mulVecLin {c : K} (hc : c ≠ 0) (M : Matrix (Fin d) (Fin d) K) :
    LinearMap.ker ((c • M).mulVecLin) = LinearMap.ker M.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec, smul_eq_zero, hc,
    false_or]

/-- **Scale-invariance of the corank along a ratio.** For `y ≠ 0`, the kernel-dimension of the pencil member
`y•A + z•B` equals that of the normalized member `A + (z/y)•B`. -/
theorem finrankKer_ratio {y z : K} (hy : y ≠ 0) (A B : Matrix (Fin d) (Fin d) K) :
    finrank K (LinearMap.ker ((y • A + z • B).mulVecLin))
      = finrank K (LinearMap.ker ((A + (z * y⁻¹) • B).mulVecLin)) := by
  have hyz : y * (z * y⁻¹) = z := by field_simp
  rw [show y • A + z • B = y • (A + (z * y⁻¹) • B) by rw [smul_add, smul_smul, hyz],
    ker_smul_mulVecLin hy]

/-- **The radical cardinality as a corank power.** The radical-count of the pencil member `y•P + z•R` (the
`ScratchTBound` magnitude input) equals `|K|^{corank}`, where the corank is that of the *normalized* Gram matrix
`A + (z/y)•B` (`A,B` the Gram matrices of `polarBilin P, polarBilin R`). Composes `polarRad_card_filter`,
`natCard_eq_pow_finrank`, the bridge `finrank_polarRad_eq_finrankKer`, `toMatrix₂_polarBilin_pencil`, and the
ratio scale-invariance `finrankKer_ratio`. -/
theorem radicalCard_eq_pow {V : Type*} [AddCommGroup V] [Module K V] [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] [Invertible (2 : K)]
    (b : Basis (Fin d) K V) (P R : QuadraticForm K V) {y z : K} (hy : y ≠ 0) :
    (Finset.univ.filter (fun h : V => ∀ w, QuadraticMap.polar (y • P + z • R) w h = 0)).card
      = Fintype.card K ^ finrank K (LinearMap.ker
          ((LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P)
            + (z * y⁻¹) • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R)).mulVecLin)) := by
  rw [polarRad_card_filter,
    Module.natCard_eq_pow_finrank (K := K) (V := polarRad (y • P + z • R)),
    finrank_polarRad_eq_finrankKer b, Nat.card_eq_fintype_card]
  congr 1
  rw [toMatrix₂_polarBilin_pencil b, finrankKer_ratio hy]

/-- The normalized-Gram corank at a ratio equals the polar-radical dimension of the pencil member (finrank version
of `radicalCard_eq_pow`; used to transport the degeneracy/non-vanishing bounds to the ratio corank). -/
theorem corank_ratio_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (b : Basis (Fin d) K V) (P R : QuadraticForm K V) {y z : K} (hy : y ≠ 0) :
    finrank K (LinearMap.ker ((LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P)
        + (z * y⁻¹) • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R)).mulVecLin))
      = finrank K (polarRad (y • P + z • R)) := by
  rw [← finrankKer_ratio hy, ← toMatrix₂_polarBilin_pencil b, ← finrank_polarRad_eq_finrankKer b]

/-- **Fiber-collapse bound.** For a nonneg `h` factoring through `ρ`, the `S`-sum of `h ∘ ρ` is at most `N` times the
ratio-sum, where `N` bounds every fiber's cardinality. -/
theorem sum_comp_ratio_le {α β : Type*} [DecidableEq β] (S : Finset α) (ρ : α → β) (h : β → ℝ)
    (hh : ∀ t, 0 ≤ h t) (N : ℝ) (hN : ∀ t, ((S.filter (fun x => ρ x = t)).card : ℝ) ≤ N) :
    ∑ x ∈ S, h (ρ x) ≤ N * ∑ t ∈ S.image ρ, h t := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := S.image ρ) (g := ρ)
      (fun x hx => Finset.mem_image_of_mem ρ hx) (fun x => h (ρ x)), Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hconst : ∑ x ∈ S.filter (fun x => ρ x = t), h (ρ x)
      = ((S.filter (fun x => ρ x = t)).card : ℝ) * h t := by
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
      nsmul_eq_mul]
  rw [hconst]
  exact mul_le_mul_of_nonneg_right (hN t) (hh t)

/-- Every ratio-fiber `{x ∈ S : x.2/x.1 = t}` of a set `S` with nonzero first coordinates has at most `|K|` elements
(it injects into `K` via the first coordinate). -/
theorem fiber_fst_card_le [Fintype K] [DecidableEq K] (S : Finset (K × K))
    (hS : ∀ x ∈ S, x.1 ≠ 0) (t : K) :
    ((S.filter (fun x => x.2 * x.1⁻¹ = t)).card : ℕ) ≤ Fintype.card K := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun x => x.1) (fun _ _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at ha hb
  obtain ⟨haS, hat⟩ := ha
  obtain ⟨hbS, hbt⟩ := hb
  have hb1 : b.1 ≠ 0 := hS b hbS
  have hab' : a.1 = b.1 := hab
  have key : a.2 * a.1⁻¹ = b.2 * b.1⁻¹ := hat.trans hbt.symm
  rw [hab'] at key
  exact Prod.ext hab' (mul_right_cancel₀ (inv_ne_zero hb1) key)

end ChainDescent

#print axioms ChainDescent.ker_smul_mulVecLin
#print axioms ChainDescent.finrankKer_ratio
#print axioms ChainDescent.radicalCard_eq_pow
#print axioms ChainDescent.corank_ratio_eq
#print axioms ChainDescent.sum_comp_ratio_le
#print axioms ChainDescent.fiber_fst_card_le
