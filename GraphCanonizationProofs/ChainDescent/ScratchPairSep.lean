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

/-- **The "no Weil" core, GENERAL form — a product of two `χ`-of-functions factors into additive Gauss sums.** For ANY
two functions `f g : V → K`, applying the bridge twice and reordering,
`gaussSum χ ψ ^ 2 · (∑_t χ(f t)·χ(g t)) = ∑_y ∑_z χ(y)χ(z)·(∑_t ψ(y·f t + z·g t))`. The factoring never uses any
structure on `f, g` (the inner `∑_t ψ(y·f t + z·g t)` is then evaluated by the additive toolkit when `f, g` are
*quadratic* — `sum_addChar_multiQuad`/`_zero` / completing the square). This is what makes the pair invariant
`χ(det G₂(u;·,t₀))·χ(det G₂(u';·,t₀))` (a product of two `χ`-of-quadratics in the probe) **Weil-free**: the degree-4
multiplicative sum factors through the SCALAR values, never needing `χ` of an irreducible high-degree polynomial. -/
theorem pairCharSum_factor_gen (hF : ringChar K ≠ 2) (ψ : AddChar K R')
    {V : Type*} [Fintype V] (f g : V → K) :
    gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ 2
        * (∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (f t)
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) (g t))
      = ∑ y : K, ∑ z : K,
          ((quadraticChar K).ringHomComp (Int.castRingHom R')) y
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) z
            * (∑ t : V, ψ (y * f t + z * g t)) := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  set G := gaussSum χ ψ with hG
  have perw : ∀ t : V, G ^ 2 * (χ (f t) * χ (g t))
      = ∑ y : K, ∑ z : K, χ y * χ z * ψ (y * f t + z * g t) := by
    intro t
    have h1 : G * χ (f t) = ∑ y : K, χ y * ψ (y * f t) := by
      rw [hG, ← quadChar_addChar_sum hF ψ (f t)]
      exact Finset.sum_congr rfl (fun y _ => by rw [mul_comm (f t) y])
    have h2 : G * χ (g t) = ∑ z : K, χ z * ψ (z * g t) := by
      rw [hG, ← quadChar_addChar_sum hF ψ (g t)]
      exact Finset.sum_congr rfl (fun z _ => by rw [mul_comm (g t) z])
    have hsq : G ^ 2 * (χ (f t) * χ (g t)) = (G * χ (f t)) * (G * χ (g t)) := by ring
    rw [hsq, h1, h2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
    rw [AddChar.map_add_eq_mul]; ring
  calc G ^ 2 * (∑ t : V, χ (f t) * χ (g t))
      = ∑ t : V, G ^ 2 * (χ (f t) * χ (g t)) := by rw [Finset.mul_sum]
    _ = ∑ t : V, ∑ y : K, ∑ z : K, χ y * χ z * ψ (y * f t + z * g t) :=
        Finset.sum_congr rfl (fun t _ => perw t)
    _ = ∑ y : K, ∑ z : K, χ y * χ z * (∑ t : V, ψ (y * f t + z * g t)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.mul_sum]

/-- The original form-specific factoring (the singleton model `S`), now a one-line corollary of the general lemma
(`f = Q`, `g = Q(· − c)`). Kept for the singleton/translate instance; the live route uses `…_gen` with the pair
invariant `f = det G₂(u; ·, t₀)`, `g = det G₂(u'; ·, t₀)`. -/
theorem pairCharSum_factor (hF : ringChar K ≠ 2) (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V) (c : V) :
    gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ 2
        * (∑ w : V, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q w)
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) (Q (w - c)))
      = ∑ y : K, ∑ z : K,
          ((quadraticChar K).ringHomComp (Int.castRingHom R')) y
            * ((quadraticChar K).ringHomComp (Int.castRingHom R')) z
            * (∑ w : V, ψ (y * Q w + z * Q (w - c))) :=
  pairCharSum_factor_gen hF ψ (fun w => Q w) (fun w => Q (w - c))

end Factor

/-! ## Increment 2 (foundation) — the pair invariant is a quadratic form at a shift

The observable per-probe invariant is `det G₂(u; t, t₀) = 4 Q(t−u) Q(t₀−u) − B(t−u, t₀−u)²` (`B = polar Q`). In the
shift `s = t − u` this is a **homogeneous quadratic form** `pairForm Q a s = 4 Q(a) Q(s) − (polar Q s a)²` (with the
anchor offset `a = t₀ − u`). So the inner sum `∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(u';t,t₀))` is a genuine quadratic
Gauss sum: `pairForm` + the shift `t ↦ t − u` reduce it to the quadratic-form machinery (`sum_addChar_quadForm_linear`
at `r = 1` to complete the square, then `sum_addChar_quadForm`). This section lands those two foundations. -/
section InnerSum
variable {K : Type*} [Field K]

/-- **The pair invariant as a quadratic form.** `pairForm Q a` is the form `s ↦ 4·Q(a)·Q(s) − (polar Q s a)²`; its
value at the shift `s = t − u` (anchor offset `a = t₀ − u`) is exactly the Gram determinant `det G₂(u; t, t₀)`. -/
noncomputable def pairForm {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (a : V) :
    QuadraticForm K V :=
  (4 * Q a) • Q - QuadraticMap.sq.comp ((LinearMap.flip Q.polarBilin) a)

theorem pairForm_apply {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (a s : V) :
    pairForm Q a s = 4 * Q a * Q s - QuadraticMap.polar Q s a * QuadraticMap.polar Q s a := by
  simp only [pairForm, QuadraticMap.sub_apply, QuadraticMap.smul_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]

/-- The Gram determinant `det G₂(u; t, t₀) = 4 Q(t−u) Q(t₀−u) − B(t−u,t₀−u)²` equals `pairForm Q (t₀−u)` evaluated at
the shift `t − u` — the structural identity that turns the opaque pair invariant into a quadratic-form-at-a-shift. -/
theorem detG2_eq_pairForm {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (u t₀ t : V) :
    4 * Q (t - u) * Q (t₀ - u) - QuadraticMap.polar Q (t - u) (t₀ - u) * QuadraticMap.polar Q (t - u) (t₀ - u)
      = pairForm Q (t₀ - u) (t - u) := by
  rw [pairForm_apply]; ring

/-- **The two-pivot combine.** The inner-sum integrand `y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀)` — two pair invariants at
DIFFERENT pivots `u, v` — expressed in the single shift `p = t − u`: a quadratic FORM `y•pairForm_u + z•pairForm_v`
applied to `p`, plus a LINEAR term `z·polar pairForm_v (p, u−v)` and a CONSTANT `z·pairForm_v(u−v)`. (Expand pivot
`v`'s form around `u` via the polar identity `P(p+e) = P p + polar P p e + P e`, `e = u−v`.) This is the algebraic core
of the inner-sum evaluation: it puts `M(y,z) = ∑_t ψ(…)` into "quadratic form + linear + const" shape, ready for
`sum_addChar_quadForm_linear` (complete the square, `r = 1`) then `sum_addChar_quadForm`. -/
theorem pairCombine {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (u v t₀ t : V) (y z : K) :
    y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)
      = (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) (t - u)
        + z * QuadraticMap.polar (pairForm Q (t₀ - v)) (t - u) (u - v)
        + z * pairForm Q (t₀ - v) (u - v) := by
  set Pv := pairForm Q (t₀ - v) with hPv
  have hexp : Pv (t - v) = Pv (t - u) + QuadraticMap.polar Pv (t - u) (u - v) + Pv (u - v) := by
    rw [QuadraticMap.polar]
    have hsum : (t - u) + (u - v) = t - v := by abel
    rw [hsum]; ring
  rw [QuadraticMap.add_apply, QuadraticMap.smul_apply, QuadraticMap.smul_apply, smul_eq_mul,
    smul_eq_mul, hexp]
  ring

/-- **Gauss-sum translation invariance.** `∑_t ψ(P (t − a)) = ∑_t ψ(P t)` for any quadratic form `P` (reindex
`t ↦ t + a`). The final step of the inner-sum evaluation, recentring each pivot's shift. -/
theorem sum_addChar_quadForm_translate {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (P : QuadraticForm K V) (a : V) :
    (∑ t : V, ψ (P (t - a))) = ∑ t : V, ψ (P t) := by
  have h := Equiv.sum_comp (Equiv.addRight (-a)) (fun t : V => ψ (P t))
  simpa [sub_eq_add_neg] using h

end InnerSum

end ChainDescent

#print axioms ChainDescent.quadChar_addChar_sum
#print axioms ChainDescent.pairCharSum_factor_gen
#print axioms ChainDescent.pairCharSum_factor
#print axioms ChainDescent.pairForm_apply
#print axioms ChainDescent.detG2_eq_pairForm
#print axioms ChainDescent.pairCombine
#print axioms ChainDescent.sum_addChar_quadForm_translate
