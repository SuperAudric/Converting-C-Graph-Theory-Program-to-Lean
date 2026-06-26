/-
# The `|radical| ↔ ker` bridge (corank tightening, step A).

`ScratchTBound`'s degenerate-bucket magnitude is `√(|V|·|radical F|)`, where `|radical F| = q^{finrank (polarRad F)}`
(`polarRad_card_filter` + `natCard_eq_pow_finrank`). The corank-stratified `ScratchPencilCorank.sum_finrankKer_le`
bounds `∑ finrank ker(Gram.mulVecLin)`. This module bridges the two notions of corank:

  **`finrank (polarRad G) = finrank ker((toMatrix₂ b b (polarBilin G)).mulVecLin)`.**

Mechanism: `b.equivFun : V ≃ₗ (Fin d → K)` carries `polarRad G` *onto* the matrix kernel, because
`(Gram *ᵥ (b.equivFun h)) i = polarBilin G (b i) h` and a linear functional vanishing on the basis `{b i}` is zero.
Then `LinearEquiv.finrank_map_eq` transports the dimension.

NOT in build (scratch; `lake env lean ChainDescent/ScratchPencilBridge.lean`, after building the imported scratch oleans).
-/
import ChainDescent.ScratchPencilCorank
import ChainDescent.ScratchCorank
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

namespace ChainDescent

open Polynomial Matrix Finset Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {d : ℕ}

/-- **The corank bridge.** The `finrank` of the polar-radical of `G` equals the `finrank` of the kernel of its Gram
matrix's `mulVecLin`. -/
theorem finrank_polarRad_eq_finrankKer (b : Basis (Fin d) K V) (G : QuadraticForm K V) :
    finrank K (polarRad G)
      = finrank K (LinearMap.ker (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin G)).mulVecLin) := by
  classical
  set M := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin G) with hM
  -- key entrywise identity: `(M *ᵥ b.equivFun h) i = polarBilin G (b i) h`
  have hkey : ∀ (h : V) (i : Fin d),
      (M *ᵥ (b.equivFun h)) i = QuadraticMap.polarBilin G (b i) h := by
    intro h i
    have hrhs : QuadraticMap.polarBilin G (b i) h
        = ∑ j, b.repr h j * QuadraticMap.polarBilin G (b i) (b j) := by
      conv_lhs => rw [← b.sum_repr h]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [hrhs]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hM, LinearMap.toMatrix₂_apply, Basis.equivFun_apply, mul_comm]
  -- `b.equivFun` carries `polarRad G` onto `ker M.mulVecLin`
  have hmap : Submodule.map (b.equivFun : V →ₗ[K] (Fin d → K)) (polarRad G)
      = LinearMap.ker M.mulVecLin := by
    ext v
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, Matrix.mulVecLin_apply, mem_polarRad]
    set h := b.equivFun.symm v with hh
    have hv : b.equivFun h = v := by rw [hh, LinearEquiv.apply_symm_apply]
    constructor
    · intro hx
      funext i
      simp only [Pi.zero_apply]
      have hki := hkey h i
      rw [hv] at hki
      rw [hki, polarBilin_apply_apply]
      exact hx (b i)
    · intro hMv x
      have hb0 : ∀ i, QuadraticMap.polarBilin G (b i) h = 0 := by
        intro i
        have hki := hkey h i
        rw [hv] at hki
        rw [← hki]
        simpa using congrFun hMv i
      have hflip : LinearMap.flip (QuadraticMap.polarBilin G) h = 0 :=
        b.ext fun i => by simpa [LinearMap.flip_apply] using hb0 i
      have hxx := LinearMap.congr_fun hflip x
      rw [← polarBilin_apply_apply, ← LinearMap.flip_apply]
      simpa using hxx
  rw [← LinearEquiv.finrank_map_eq b.equivFun (polarRad G), hmap]

end ChainDescent

#print axioms ChainDescent.finrank_polarRad_eq_finrankKer
