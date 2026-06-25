/-
# The c₀ counting identity (increment 3, step 3e-iii).

`NS = #{t : χ(I_u t) = χ(I_v t)}` (the count of probes where the pair invariants agree) is controlled by the character
sum `T = ∑_t χ(I_u t)·χ(I_v t)` via the elementary identity `2·NS ≤ 2·z_u + n + T` (`z_u = #{I_u = 0}`, `n = card V`).
This is proved from a per-element χ-value inequality (`χ ∈ {-1,0,1}`); summing gives the bound. Pure ℤ-counting. -/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace ChainDescent

open Finset

/-- Per-element χ-value inequality (the heart of the counting identity). For `ca, cb ∈ {-1,0,1}`:
`2·[ca=cb] ≤ 2·[ca=0] + 1 + ca·cb`. -/
theorem int_char_pointwise (ca cb : ℤ)
    (hca : ca = -1 ∨ ca = 0 ∨ ca = 1) (hcb : cb = -1 ∨ cb = 0 ∨ cb = 1) :
    2 * (if ca = cb then (1 : ℤ) else 0) ≤ 2 * (if ca = 0 then (1 : ℤ) else 0) + 1 + ca * cb := by
  rcases hca with h | h | h <;> rcases hcb with h' | h' | h' <;> subst h <;> subst h' <;> decide

/-- **The c₀ counting identity.** `2·#{t : χ(a t) = χ(b t)} ≤ 2·#{t : a t = 0} + |V| + ∑_t χ(a t)·χ(b t)`,
for the quadratic character `χ = quadraticChar K`. (`a, b = I_u, I_v`.) -/
theorem counting_identity {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℤ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℤ)
        + (Fintype.card V : ℤ)
        + ∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) := by
  have hval : ∀ k : K, quadraticChar K k = -1 ∨ quadraticChar K k = 0 ∨ quadraticChar K k = 1 := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [quadraticChar_zero]; tauto
    · rcases quadraticChar_dichotomy hk with h | h <;> tauto
  -- replace the `a t = 0` filter by the `χ(a t) = 0` filter
  have hz : (Finset.univ.filter (fun t => a t = 0))
          = (Finset.univ.filter (fun t => quadraticChar K (a t) = 0)) := by
    apply Finset.filter_congr
    intro t _
    rw [quadraticChar_eq_zero_iff]
  rw [hz, Finset.card_filter, Finset.card_filter,
    show (Fintype.card V : ℤ) = ∑ _t : V, (1 : ℤ) from by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => int_char_pointwise _ _ (hval _) (hval _))

end ChainDescent

#print axioms ChainDescent.int_char_pointwise
#print axioms ChainDescent.counting_identity
