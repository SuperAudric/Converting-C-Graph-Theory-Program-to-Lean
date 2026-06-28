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
import ChainDescent.PencilTBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

/-- `√(a^c) = (√a)^c` for `a ≥ 0`. -/
theorem sqrt_natpow (a : ℝ) (ha : 0 ≤ a) (c : ℕ) : Real.sqrt (a ^ c) = Real.sqrt a ^ c := by
  induction c with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]

/-- **Good anchor ⟹ pencil determinant nonzero (the `hgood → hp` bridge).** A good anchor (a nondegenerate pencil
member `polarRad (y•P + z•R) = ⊥`) gives the `normT_bucket_bound_corank` hypothesis: the univariate pencil determinant
of the Gram matrices is nonzero. -/
theorem pencilDet_ne_zero_of_good {V : Type*} [AddCommGroup V] [Module K V]
    (b : Basis (Fin d) K V) (P R : QuadraticForm K V)
    (hgood : ∃ y z : K, polarRad (y • P + z • R) = ⊥) :
    (pencilPoly (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P))
        (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R))).det ≠ 0 := by
  apply pencilPoly_det_ne_zero
  obtain ⟨y, z, hyz⟩ := hgood
  refine ⟨y, z, ?_⟩
  rw [← toMatrix₂_polarBilin_pencil b, ne_eq, ← polarRad_ne_bot_iff_det_eq_zero b (y • P + z • R),
    not_not]
  exact hyz

/-- **The corank-stratified degenerate bucket bound (A-assembly).** The `ScratchTBound` degenerate-bucket sum
`∑_{x∈s deg} √(|V|·|radical|)` is at most `2·|K|·(|V|/√|K|)` — the `d`-free bound (vs the uniform `d·|K|·(|V|/√|K|)`).
Chains `radicalCard_eq_pow` (factor `g = √|V|·(√q)^{corank}`), `sum_comp_ratio_le`/`fiber_fst_card_le` (regroup pairs
to ratios, `≤ |K|` each), and `concentration_bound` (the `∑ corank ≤ d`, `corank ≤ d−1` budget). -/
theorem deg_bucket_le {V : Type*} [AddCommGroup V] [Module K V] [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] [Invertible (2 : K)]
    (b : Basis (Fin d) K V) (P R : QuadraticForm K V) (hd : 1 ≤ d) (hq4 : 4 ≤ Fintype.card K)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 → y • P + z • R ≠ 0)
    (hp : (pencilPoly (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P))
            (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R))).det ≠ 0) :
    ∑ x ∈ ((Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0)).filter
        (fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥)),
      Real.sqrt ((Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V =>
            ∀ w, QuadraticMap.polar (x.1 • P + x.2 • R) w h = 0)).card)
      ≤ 2 * Fintype.card K * (Fintype.card V / Real.sqrt (Fintype.card K)) := by
  classical
  set A := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P) with hA
  set B := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) with hB
  set q : ℕ := Fintype.card K with hq
  set n : ℕ := Fintype.card V with hn
  set ρ : K × K → K := fun x => x.2 * x.1⁻¹ with hρ
  set cork : K → ℕ := fun t => finrank K (LinearMap.ker ((A + t • B).mulVecLin)) with hcork
  set S := (Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0)).filter
      (fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥) with hS
  -- membership facts
  have hxne : ∀ x ∈ S, x.1 ≠ 0 ∧ x.2 ≠ 0 := by
    intro x hx; exact (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
  have hxrad : ∀ x ∈ S, polarRad (x.1 • P + x.2 • R) ≠ ⊥ := by
    intro x hx; exact (Finset.mem_filter.1 hx).2
  -- field facts
  have hsqrtq2 : (2 : ℝ) ≤ Real.sqrt q := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq4)
  have hqpos : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  have hnq : (n : ℝ) = (q : ℝ) ^ d := by
    rw [hn, hq, Module.card_eq_pow_finrank (K := K) (V := V), Module.finrank_eq_card_basis b,
      Fintype.card_fin]; push_cast; ring
  have hfin : finrank K V = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  -- Step 1: g x = √n · (√q)^{cork (ρ x)}
  have hgx : ∀ x ∈ S, Real.sqrt ((n : ℝ)
      * (Finset.univ.filter (fun h : V =>
          ∀ w, QuadraticMap.polar (x.1 • P + x.2 • R) w h = 0)).card)
        = Real.sqrt n * Real.sqrt q ^ (cork (ρ x)) := by
    intro x hx
    have h1 : ((Finset.univ.filter (fun h : V =>
        ∀ w, QuadraticMap.polar (x.1 • P + x.2 • R) w h = 0)).card : ℝ)
        = (q : ℝ) ^ (cork (ρ x)) := by
      rw [radicalCard_eq_pow b P R (hxne x hx).1, ← hA, ← hB]
      push_cast
      rfl
    rw [h1, Real.sqrt_mul (by positivity), sqrt_natpow _ (le_of_lt hqpos)]
  rw [Finset.sum_congr rfl hgx, ← Finset.mul_sum]
  -- Step 2: regroup pairs → ratios
  have hN : ∀ t : K, ((S.filter (fun x => ρ x = t)).card : ℝ) ≤ (q : ℝ) := by
    intro t
    rw [hρ]
    exact_mod_cast fiber_fst_card_le S (fun x hx => (hxne x hx).1) t
  have hstep2 : ∑ x ∈ S, Real.sqrt q ^ (cork (ρ x))
      ≤ (q : ℝ) * ∑ t ∈ S.image ρ, Real.sqrt q ^ (cork t) :=
    sum_comp_ratio_le S ρ (fun t => Real.sqrt q ^ (cork t)) (fun t => by positivity) q hN
  -- Step 3: concentration over the ratio set
  set T := S.image ρ with hT
  have hce : ∀ x ∈ S, cork (ρ x) = finrank K (polarRad (x.1 • P + x.2 • R)) := fun x hxS =>
    corank_ratio_eq b P R (hxne x hxS).1
  have hlo : ∀ t ∈ T, 1 ≤ cork t := by
    intro t ht
    rw [hT, Finset.mem_image] at ht
    obtain ⟨x, hxS, hxt⟩ := ht
    rw [← hxt, hce x hxS, Nat.one_le_iff_ne_zero]
    intro hzero
    exact hxrad x hxS (Submodule.finrank_eq_zero.1 hzero)
  have hhi : ∀ t ∈ T, cork t ≤ d - 1 := by
    intro t ht
    rw [hT, Finset.mem_image] at ht
    obtain ⟨x, hxS, hxt⟩ := ht
    rw [← hxt, hce x hxS]
    have hmem0 : x.1 • P + x.2 • R ≠ 0 := hnz x.1 x.2 (hxne x hxS).1 (hxne x hxS).2
    have hlt : finrank K (polarRad (x.1 • P + x.2 • R)) < d := by
      rw [← hfin]; exact Submodule.finrank_lt (polarRad_ne_top_of_ne_zero _ hmem0)
    omega
  have hsumcork : ∑ t ∈ T, cork t ≤ d := by
    rw [hT]; exact sum_finrankKer_le A B (S.image ρ) hp
  have hstep3 : ∑ t ∈ T, Real.sqrt q ^ (cork t) ≤ 2 * Real.sqrt q ^ (d - 1) :=
    concentration_bound hsqrtq2 hsumcork hlo hhi
  -- Step 4: assemble the arithmetic
  have hkey : Real.sqrt n * ((q : ℝ) * (2 * Real.sqrt q ^ (d - 1)))
      ≤ 2 * (q : ℝ) * ((n : ℝ) / Real.sqrt q) := by
    apply le_of_eq
    obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    subst hm
    have hsqpos : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.2 hqpos
    have hu2 : Real.sqrt q ^ 2 = (q : ℝ) := Real.sq_sqrt (le_of_lt hqpos)
    have hsqn : Real.sqrt (n : ℝ) = Real.sqrt q ^ (m + 1) := by
      rw [hnq, sqrt_natpow _ (le_of_lt hqpos)]
    have hpow : Real.sqrt q ^ (2 * m + 1) * Real.sqrt q = (q : ℝ) ^ (m + 1) := by
      rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, hu2]
    have hndiv : (n : ℝ) / Real.sqrt q = Real.sqrt q ^ (2 * m + 1) := by
      rw [hnq, ← hpow, mul_div_assoc, div_self (ne_of_gt hsqpos), mul_one]
    rw [hsqn, hndiv, Nat.add_sub_cancel]
    generalize Real.sqrt q = u at hu2 ⊢
    rw [← hu2]
    ring
  calc Real.sqrt n * ∑ x ∈ S, Real.sqrt q ^ (cork (ρ x))
      ≤ Real.sqrt n * ((q : ℝ) * ∑ t ∈ T, Real.sqrt q ^ (cork t)) :=
        mul_le_mul_of_nonneg_left hstep2 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * ((q : ℝ) * (2 * Real.sqrt q ^ (d - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hstep3 (le_of_lt hqpos)
    _ ≤ 2 * (q : ℝ) * ((n : ℝ) / Real.sqrt q) := hkey

end ChainDescent

#print axioms ChainDescent.ker_smul_mulVecLin
#print axioms ChainDescent.finrankKer_ratio
#print axioms ChainDescent.radicalCard_eq_pow
#print axioms ChainDescent.corank_ratio_eq
#print axioms ChainDescent.sum_comp_ratio_le
#print axioms ChainDescent.fiber_fst_card_le
#print axioms ChainDescent.deg_bucket_le
