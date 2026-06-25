/-
# Connecting the count to the analytic magnitude (increment 3, step 3e-iii).

`counting_identity` bounds `2·NS` by `2·z_u + n + T_ℤ` (integer character sum). The analytic side (`normT_bucket_bound`)
bounds the COMPLEX character sum `‖T_ℂ‖`. These connect via `T_ℂ = (T_ℤ : ℂ)`, so `T_ℤ ≤ |T_ℤ| = ‖T_ℂ‖`. Result:
`2·NS ≤ 2·z_u + n + ‖T_ℂ‖` over ℝ — the count is controlled by the landed magnitude bound. -/
import ChainDescent.ScratchCount
import Mathlib.Analysis.Complex.Basic

namespace ChainDescent

open Finset

/-- The integer character sum is `≤` the norm of the complex character sum (`T_ℤ ≤ |T_ℤ| = ‖T_ℂ‖`). -/
theorem charSum_int_le_norm {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] (a b : V → K) :
    ((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ)
      ≤ ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
          * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t)‖ := by
  have hcast : (∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t))
      = (((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ) : ℂ) := by
    push_cast [MulChar.ringHomComp_apply]
    simp only [eq_intCast]
  rw [hcast, Complex.norm_real]
  exact le_abs_self _

/-- **The count controlled by the magnitude.** `2·#{χ(a)=χ(b)} ≤ 2·#{a=0} + |V| + ‖T_ℂ‖` over ℝ, combining
`counting_identity` with `charSum_int_le_norm`. -/
theorem card_agree_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℝ)
        + (Fintype.card V : ℝ)
        + ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t)‖ := by
  have hc := counting_identity a b
  have hT := charSum_int_le_norm a b
  have hcR : 2 * ((Finset.univ.filter
        (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℝ) + (Fintype.card V : ℝ)
        + ((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ) := by
    exact_mod_cast hc
  linarith [hcR, hT]

end ChainDescent

#print axioms ChainDescent.charSum_int_le_norm
#print axioms ChainDescent.card_agree_le
