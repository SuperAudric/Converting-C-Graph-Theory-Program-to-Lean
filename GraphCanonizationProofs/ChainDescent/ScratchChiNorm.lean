import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.Complex.Basic

namespace ChainDescent

open scoped Classical

/-- The quadratic character composed into `ℂ` has norm `0` at `0` and `1` elsewhere. -/
theorem norm_quadraticChar {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (y : K) :
    ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖ = if y = 0 then 0 else 1 := by
  rw [MulChar.ringHomComp_apply]
  split_ifs with hy
  · subst hy
    rw [quadraticChar_zero]
    simp
  · have h2 : (quadraticChar K y) ^ 2 = 1 := quadraticChar_sq_one hy
    have hc : ((Int.castRingHom ℂ) (quadraticChar K y)) ^ 2 = 1 := by
      rw [← map_pow, h2, map_one]
    have hsq : ‖(Int.castRingHom ℂ) (quadraticChar K y)‖ ^ 2 = 1 := by
      rw [← norm_pow, hc, norm_one]
    nlinarith [norm_nonneg ((Int.castRingHom ℂ) (quadraticChar K y)), hsq]

end ChainDescent

#print axioms ChainDescent.norm_quadraticChar
