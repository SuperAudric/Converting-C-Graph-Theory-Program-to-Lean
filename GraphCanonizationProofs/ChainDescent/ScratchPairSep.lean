/-
# Per-pair separation — the Lean sibling of `Probe_D3dExactVsWeil` (plan §13, D3d, Weil-free route)

The existential-counting route reduces D3d to a per-pair bound on
`S(c) = ∑_w χ(Q w · Q (w − c))` (the singleton-separation driver, `c = u' − u`). The C# probe established it is
EXACT (no Weil): `S` factors through the scalar values `(Q w, Q (w−c))`, so it is a finite combination of the
ADDITIVE Gauss sums the toolkit already builds — no `χ` of an irreducible high-degree polynomial.

This module formalizes that. Increment 1 (this file):
* `quadChar_addChar_sum` — the multiplicative↔additive **Gauss bridge** `∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)`
  (for ALL `a`, the quadratic character of `K` composed into a domain `R'`). The reusable atom.
* `pairCharSum_factor` — applying the bridge twice + Fubini: `gaussSum χ ψ ^ 2 · S = ∑_y ∑_z χ(y)χ(z)·M(y,z)`
  where `M(y,z) = ∑_w ψ(y·Q w + z·Q(w−c))` is the landed multi-point additive Gauss sum
  (`sum_addChar_multiQuad`/`_zero`). This is the rigorous "no Weil" core: `S` is built from additive Gauss sums.

Axiom-clean target `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.GaussCount

namespace ChainDescent

open Finset Module
open scoped BigOperators

section Bridge
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

/-- **The multiplicative↔additive Gauss bridge.** For the quadratic character `χ` of `K` composed into a
char-zero domain `R'`, and any additive character `ψ : AddChar K R'`,
`∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)` for every `a : K` (including `a = 0`, both sides `0`). -/
theorem quadChar_addChar_sum (hF : ringChar K ≠ 2) (ψ : AddChar K R') (a : K) :
    (∑ y : K, ((quadraticChar K).ringHomComp (Int.castRingHom R')) y * ψ (a * y))
      = gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
        * ((quadraticChar K).ringHomComp (Int.castRingHom R')) a := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  have hχ1 : χ ≠ 1 := by
    rw [hχ, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
    exact quadraticChar_ne_one hF
  have hbase : gaussSum χ (AddChar.mulShift ψ a) = ∑ y : K, χ y * ψ (a * y) := by
    simp only [gaussSum, AddChar.mulShift_apply]
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero]
    rw [MulChar.sum_eq_zero_of_ne_one hχ1, mul_zero]
  · have hane : χ a ≠ 0 := by
      intro h
      have hmm : χ (a * a⁻¹) = χ a * χ a⁻¹ := map_mul χ a a⁻¹
      rw [mul_inv_cancel₀ ha, map_one, h, zero_mul] at hmm
      exact one_ne_zero hmm
    have hcast : χ a = ((quadraticChar K a : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply]; rfl
    have hsq : χ a * χ a = 1 := by
      rcases quadraticChar_isQuadratic K a with h | h | h
      · rw [hcast, h] at hane; simp at hane
      · rw [hcast, h]; norm_num
      · rw [hcast, h]; norm_num
    have hmul := gaussSum_mulShift χ ψ (Units.mk0 a ha)
    rw [Units.val_mk0, hbase] at hmul
    calc (∑ y : K, χ y * ψ (a * y))
        = (χ a * χ a) * (∑ y : K, χ y * ψ (a * y)) := by rw [hsq, one_mul]
      _ = χ a * (χ a * (∑ y : K, χ y * ψ (a * y))) := by ring
      _ = χ a * gaussSum χ ψ := by rw [hmul]
      _ = gaussSum χ ψ * χ a := by ring

end Bridge

section Factor
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

/-- **The "no Weil" core — `S` factors into additive Gauss sums.** Applying the bridge twice and reordering,
`gaussSum χ ψ ^ 2 · (∑_w χ(Q w)·χ(Q(w−c))) = ∑_y ∑_z χ(y)χ(z)·(∑_w ψ(y·Q w + z·Q(w−c)))`. The inner
`∑_w ψ(y·Q w + z·Q(w−c))` is the landed multi-point additive Gauss sum (`sum_addChar_multiQuad`/`_zero`), so the
per-pair singleton sum `S` is a finite combination of additive Gauss sums — **no `χ` of an irreducible
high-degree polynomial, no Weil/Deligne**. -/
theorem pairCharSum_factor (hF : ringChar K ≠ 2) (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V) (c : V) :
    gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ 2
        * (∑ w : V, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q w)
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q (w - c)))
      = ∑ y : K, ∑ z : K,
          ((quadraticChar K).ringHomComp (Int.castRingHom R')) y
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) z
            * (∑ w : V, ψ (y * Q w + z * Q (w - c))) := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  set g := gaussSum χ ψ with hg
  have perw : ∀ w : V, g ^ 2 * (χ (Q w) * χ (Q (w - c)))
      = ∑ y : K, ∑ z : K, χ y * χ z * ψ (y * Q w + z * Q (w - c)) := by
    intro w
    have h1 : g * χ (Q w) = ∑ y : K, χ y * ψ (y * Q w) := by
      rw [hg, ← quadChar_addChar_sum hF ψ (Q w)]
      exact Finset.sum_congr rfl (fun y _ => by rw [mul_comm (Q w) y])
    have h2 : g * χ (Q (w - c)) = ∑ z : K, χ z * ψ (z * Q (w - c)) := by
      rw [hg, ← quadChar_addChar_sum hF ψ (Q (w - c))]
      exact Finset.sum_congr rfl (fun z _ => by rw [mul_comm (Q (w - c)) z])
    have hsq : g ^ 2 * (χ (Q w) * χ (Q (w - c))) = (g * χ (Q w)) * (g * χ (Q (w - c))) := by ring
    rw [hsq, h1, h2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
    rw [AddChar.map_add_eq_mul]; ring
  calc g ^ 2 * (∑ w : V, χ (Q w) * χ (Q (w - c)))
      = ∑ w : V, g ^ 2 * (χ (Q w) * χ (Q (w - c))) := by rw [Finset.mul_sum]
    _ = ∑ w : V, ∑ y : K, ∑ z : K, χ y * χ z * ψ (y * Q w + z * Q (w - c)) :=
        Finset.sum_congr rfl (fun w _ => perw w)
    _ = ∑ y : K, ∑ z : K, χ y * χ z * (∑ w : V, ψ (y * Q w + z * Q (w - c))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.mul_sum]

end Factor

end ChainDescent

#print axioms ChainDescent.quadChar_addChar_sum
#print axioms ChainDescent.pairCharSum_factor
