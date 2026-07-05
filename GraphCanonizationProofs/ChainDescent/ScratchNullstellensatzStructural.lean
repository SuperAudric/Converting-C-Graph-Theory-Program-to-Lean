/-
# Nullstellensatz discharge — the finite-field structural facts (WIP)

The assembly `nullstellensatz_of_structural` (`ScratchNullstellensatz.lean`) reduced the quadric Nullstellensatz to two
structural facts about a nondegenerate `Q` over a finite field (odd char, `dim ≥ 4`):
- `hspan` — the punctured isotropic cone `{x | Q x = 0 ∧ polar Q x y ≠ 0}` spans, for each anisotropic `y`;
- `hlink` — the anisotropic vectors have `polar`-diameter ≤ 2.
Both rest on the bedrock **isotropic-vector existence** (a nondeg form in `dim ≥ 3` over a finite field is isotropic),
which this file builds — via **diagonalization** (`equivalent_weightedSumSquares_units_of_nondegenerate'`) + **binary
solvability** (`FiniteField.exists_root_sum_quadratic`), NOT Chevalley–Warning.

**STATUS (2026-07-05 — bedrock DONE).**
- ✅ `binary_represents` — `A x² + B y² = c` solvable over a finite field of odd order (units `A,B`).
- ✅ `weightedSumSquares_isotropic` — a unit-weighted sum of squares in `dim ≥ 3` is isotropic.
- ✅ `separatingLeft_associated_of_polarBilin_nondeg` — the `polarBilin.Nondegenerate ⟹ (associated Q).SeparatingLeft`
  bridge (char `≠ 2`).
- ✅ **`exists_isotropic_of_nondegenerate`** — the BEDROCK: a nondegenerate `Q` in `dim ≥ 3` over a finite field of odd
  order has a nonzero isotropic vector (diagonalize + `weightedSumSquares_isotropic` + isometry transport).
- ✅ `exists_hyperbolic_partner` — an isotropic `v ≠ 0` has an isotropic `f` with `polar Q v f = 1` (hyperbolic pair).
- ✅ **`isotropic_span`** — the isotropic vectors span `V` (dim ≥ 3). Clean proof from ONE hyperbolic pair
  (`u = w − t·v − s·f`, `w := t·v + s·f + u` made isotropic); holds even at the `d = 4` elliptic boundary. All axiom-clean.
- ◻ next: `hspan` (punctured isotropic cone spans) and `hlink` (anisotropic `polar`-diameter ≤ 2), then plug into
  `nullstellensatz_of_structural`. **Both hinge on the Witt-index-1 / `q = 3` boundary** (at `d = 4` elliptic there are
  no two orthogonal independent isotropic vectors, so the "add an orthogonal punctured isotropic" trick and the small-`q`
  in-plane constructions both fail) — they need genuine case-analysis finite geometry using the ambient `d ≥ 4`. This is
  the remaining delicate frontier.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`, `native_decide` banned. WIP scratch.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import ChainDescent.ScratchNullstellensatz

namespace ChainDescent.Nullstellensatz

open Polynomial QuadraticMap

/-- **Binary solvability over a finite field of odd order.** For units `A, B` and any target `c`, the nondegenerate
binary form `A x² + B y²` represents `c`. Pigeonhole on the square-value sets, packaged by
`FiniteField.exists_root_sum_quadratic` (`f := A·X²`, `g := B·X² − c`, both of degree 2). -/
theorem binary_represents {K : Type*} [Field K] [Fintype K] (hodd : Fintype.card K % 2 = 1)
    (A B : Kˣ) (c : K) : ∃ x y : K, (A : K) * x ^ 2 + (B : K) * y ^ 2 = c := by
  have hA : (A : K) ≠ 0 := A.ne_zero
  have hB : (B : K) ≠ 0 := B.ne_zero
  have hfdeg : (C (A : K) * X ^ 2 : K[X]).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hA]; rfl
  have h2B : (C (B : K) * X ^ 2 : K[X]).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB]; rfl
  have hgdeg : (C (B : K) * X ^ 2 - C c : K[X]).degree = 2 := by
    have hlt : (C c : K[X]).degree < (C (B : K) * X ^ 2 : K[X]).degree := by
      rw [h2B]; exact lt_of_le_of_lt degree_C_le (by norm_num)
    rw [degree_sub_eq_left_of_degree_lt hlt, h2B]
  obtain ⟨a, b, hab⟩ :=
    FiniteField.exists_root_sum_quadratic (R := K)
      (f := C (A : K) * X ^ 2) (g := C (B : K) * X ^ 2 - C c) hfdeg hgdeg hodd
  refine ⟨a, b, ?_⟩
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hab
  linear_combination hab

open QuadraticMap in
/-- **A weighted sum of squares in `dim ≥ 3` (unit weights) is isotropic over a finite field of odd order.** The
vector supported as `(α, β, 1, 0, …)` on the first three coordinates is a nonzero zero of `∑ᵢ wᵢ xᵢ²`, with `α, β`
from `binary_represents` (`w₀ α² + w₁ β² = −w₂`). The bedrock isotropic-existence fact (diagonalized form). -/
theorem weightedSumSquares_isotropic {K : Type*} [Field K] [Fintype K]
    (hodd : Fintype.card K % 2 = 1) {n : ℕ} (hn : 3 ≤ n) (w : Fin n → Kˣ) :
    ∃ x : Fin n → K, x ≠ 0 ∧ weightedSumSquares K w x = 0 := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have h2 : (2 : ℕ) < n := by omega
  set i0 : Fin n := ⟨0, h0⟩
  set i1 : Fin n := ⟨1, h1⟩
  set i2 : Fin n := ⟨2, h2⟩
  have d01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have d02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have d12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  obtain ⟨a, b, hab⟩ := binary_represents hodd (w i0) (w i1) (-(w i2 : K))
  set x : Fin n → K := fun i => if i = i0 then a else if i = i1 then b else if i = i2 then 1 else 0
    with hx
  have hxi0 : x i0 = a := by simp [hx]
  have hxi1 : x i1 = b := by simp [hx, (Ne.symm d01)]
  have hxi2 : x i2 = 1 := by simp [hx, (Ne.symm d02), (Ne.symm d12)]
  refine ⟨x, ?_, ?_⟩
  · intro h
    have := congrFun h i2
    rw [hxi2] at this
    exact one_ne_zero this
  · rw [weightedSumSquares_apply]
    have hsupp : ∀ i ∈ Finset.univ, i ∉ ({i0, i1, i2} : Finset (Fin n)) →
        w i • (x i * x i) = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      obtain ⟨hia, hib, hic⟩ := hi
      have : x i = 0 := by simp [hx, hia, hib, hic]
      rw [this]; simp
    rw [← Finset.sum_subset (Finset.subset_univ _) hsupp,
      Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, d01, d02]),
      Finset.sum_insert (by simp [Finset.mem_singleton, d12]), Finset.sum_singleton,
      hxi0, hxi1, hxi2, Units.smul_def, Units.smul_def, Units.smul_def]
    linear_combination hab

/-- **Bridge: `polarBilin` nondegenerate ⟹ `associated Q` separating-left** (char `≠ 2`). Since
`2 • associated Q = polarBilin Q`, a vector killed by `associated Q` is killed by `polarBilin Q`, hence zero. The form
`equivalent_weightedSumSquares_units_of_nondegenerate'` wants the `associated`-side hypothesis. -/
theorem separatingLeft_associated_of_polarBilin_nondeg {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (QuadraticMap.associated (R := K) Q).SeparatingLeft := by
  intro x hx
  refine hQ.1 x (fun y => ?_)
  have h2 : Q.polarBilin x y = 2 • (QuadraticMap.associated (R := K) Q) x y := by
    rw [← QuadraticMap.two_nsmul_associated K Q]
    rfl
  rw [h2, hx y, smul_zero]

open Module in
/-- **Isotropic existence for a nondegenerate `Q` in `dim ≥ 3` over a finite field of odd order.** Diagonalize
(`equivalent_weightedSumSquares_units_of_nondegenerate'`) to unit-weighted squares, find an isotropic vector there
(`weightedSumSquares_isotropic`), and pull it back along the isometry. The bedrock both structural facts rest on. -/
theorem exists_isotropic_of_nondegenerate {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (hodd : Fintype.card K % 2 = 1)
    (hdim : 3 ≤ finrank K V) (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨w, ⟨φ⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q
    (separatingLeft_associated_of_polarBilin_nondeg Q hQ)
  obtain ⟨u, hu0, huiso⟩ := weightedSumSquares_isotropic hodd hdim w
  refine ⟨φ.symm u, ?_, ?_⟩
  · intro h
    apply hu0
    have : φ.symm u = φ.symm 0 := by rw [h, map_zero]
    exact φ.symm.injective this
  · have hmap := φ.map_app (φ.symm u)
    rw [φ.apply_symm_apply] at hmap
    rw [← hmap]; exact huiso

/-- **A hyperbolic partner for an isotropic vector.** For nondegenerate `Q` and a nonzero isotropic `v`, there is an
isotropic `f` with `polar Q v f = 1` (so `{v, f}` is a hyperbolic pair). Nondegeneracy gives some `u` with
`polar Q v u ≠ 0`; rescale and correct by `Q u' • v` to make it isotropic. Char-free, dimension-free. -/
theorem exists_hyperbolic_partner {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {v : V}
    (hv : Q v = 0) (hv0 : v ≠ 0) :
    ∃ f : V, Q f = 0 ∧ QuadraticMap.polar Q v f = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, QuadraticMap.polar Q v u ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv0 (hQ.1 v (fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h y))
  have hc0 : QuadraticMap.polar Q v u ≠ 0 := hu
  set u' := (QuadraticMap.polar Q v u)⁻¹ • u with hu'
  have hvu' : QuadraticMap.polar Q v u' = 1 := by
    rw [hu', QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hc0]
  refine ⟨u' - Q u' • v, ?_, ?_⟩
  · rw [show u' - Q u' • v = (1 : K) • u' + (-(Q u')) • v by rw [one_smul, neg_smul, sub_eq_add_neg],
      quad_lin_combo, hv]
    have : QuadraticMap.polar Q u' v = 1 := by rw [QuadraticMap.polar_comm]; exact hvu'
    rw [this]; ring
  · rw [QuadraticMap.polar_sub_right, hvu', QuadraticMap.polar_smul_right,
      show QuadraticMap.polar Q v v = 2 • Q v from Q.polar_self v, hv]
    simp

/-- **Isotropic vectors span (dim ≥ 3, nondegenerate, finite field of odd order).** With a hyperbolic pair `{v, f}`
(from isotropic existence), every `u` is a difference of isotropic vectors: choose `s := 1 − polar Q v u` and
`t := −(Q u + s · polar Q u f)`, so `w := t·v + s·f + u` is isotropic and `u = w − t·v − s·f`. Uses only ONE hyperbolic
pair, so it holds even at the `d = 4` elliptic boundary. The bridge from `exists_isotropic_of_nondegenerate` to the
structural facts. -/
theorem isotropic_span {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)] (hodd : Fintype.card K % 2 = 1)
    (hdim : 3 ≤ Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Submodule.span K {x : V | Q x = 0} = ⊤ := by
  obtain ⟨v, hv0, hviso⟩ := exists_isotropic_of_nondegenerate hodd hdim Q hQ
  obtain ⟨f, hfiso, hvf⟩ := exists_hyperbolic_partner Q hQ hviso hv0
  rw [eq_top_iff]
  intro u _
  set s : K := 1 - QuadraticMap.polar Q v u with hs
  set t : K := -(Q u + s * QuadraticMap.polar Q u f) with ht
  set w : V := t • v + s • f + u with hw
  have hsp : s + QuadraticMap.polar Q v u = 1 := by rw [hs]; ring
  -- Q w = 0 : expand over the hyperbolic pair
  have hQa : Q (t • v + s • f)
      = t * t * Q v + s * s * Q f + t * s * QuadraticMap.polar Q v f := quad_lin_combo Q t s v f
  have hpau : QuadraticMap.polar Q (t • v + s • f) u
      = t * QuadraticMap.polar Q v u + s * QuadraticMap.polar Q f u := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      smul_eq_mul, smul_eq_mul]
  have hwiso : Q w = 0 := by
    rw [hw, show t • v + s • f + u = (t • v + s • f) + u from by abel,
      QuadraticMap.map_add (⇑Q) _ _, hQa, hpau, hviso, hfiso, hvf, QuadraticMap.polar_comm Q f u]
    rw [ht, hs]; ring
  have hueq : u = w - t • v - s • f := by rw [hw]; abel
  rw [hueq]
  refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  · exact Submodule.subset_span (show w ∈ {x : V | Q x = 0} from hwiso)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (show v ∈ {x : V | Q x = 0} from hviso))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (show f ∈ {x : V | Q x = 0} from hfiso))

end ChainDescent.Nullstellensatz
