/-
# Per-pair separation — the Weil-free D3d route (plan §13). HANDOFF / pick-up point.

**Goal of this module.** Discharge the one open predicate `ZProfileSeparates Q T` (the joint `Z(S)`-profile separates
pivots at a bounded base = D3d = forms-graph bounded WL-dimension). The route: the seal's observable is the **pair**
joint-isotropic count `Z_u({t,t'})` (NB the SINGLETON `Z_u({t})` is binary — `Probe_D3cObservable`; do not use it). Its
separating invariant is `χ(det G₂(u;t,t₀))` against an anchor `t₀`, which is `χ` of a **quadratic in the probe `t`**. For a
pair of pivots `u,u'`, `u` is separated from `u'` iff some probe `t` gives a different invariant; the per-pair fail count
is controlled by the character sum `∑_t χ(det G₂(u;t,t₀))·χ(det G₂(u';t,t₀))`, which **factors into additive Gauss sums
(no Weil)**. Probe `Probe_D3dPairCount`: `c₀ ≤ 0.49 < 1`, anchor existence robust. Then a finite-averaging argument gives
a separating base of size `O(d log q)`, discharging `ZProfileSeparates`.

**LANDED in this file (all axiom-clean `[propext, Classical.choice, Quot.sound]`):**
* `quadChar_addChar_sum` — the multiplicative↔additive **Gauss bridge** `∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)` (∀`a`;
  `χ = (quadraticChar K).ringHomComp (Int.castRingHom R')`, `R'` a char-zero domain). The reusable atom.
* `pairCharSum_factor_gen` — the **"no Weil" core**, GENERAL: for any `f,g : V → K`,
  `gaussSum² · ∑_t χ(f t)χ(g t) = ∑_y ∑_z χ(y)χ(z)·(∑_t ψ(y·f t + z·g t))`. (`pairCharSum_factor` = the `f=Q,g=Q(·−c)`
  singleton corollary.) Apply with `f = det G₂(u;·,t₀)`, `g = det G₂(u';·,t₀)`.
* `pairForm` / `pairForm_apply` / `detG2_eq_pairForm` — the pair invariant IS the quadratic form
  `pairForm Q a = 4 Q(a)·Q − (polar Q · a)²` evaluated at the shift `t−u` (anchor offset `a = t₀−u`).
* `pairCombine` — the two-pivot integrand `y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀)` in "quadratic FORM `(y•pairForm_u +
  z•pairForm_v)` at shift `t−u` + LINEAR `z·polar pairForm_v(·,u−v)` + CONST `z·pairForm_v(u−v)`" shape.
* `sum_addChar_quadForm_translate` — `∑_t ψ(P(t−a)) = ∑_t ψ(P t)`.

**★ PICK UP HERE — the exact next step (finish increment 2: the `M(y,z)` closed form).** Combine the above:
  1. `M(y,z) := ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))`. By `pairCombine` + `detG2_eq_pairForm`, the integrand is
     `(F)(t−u) + z·polar pairForm_v(t−u, u−v) + z·pairForm_v(u−v)`, `F := y•pairForm Q (t₀−u) + z•pairForm Q (t₀−v)`.
  2. Pull out the constant `ψ(z·pairForm_v(u−v))`; shift `t = u+s` (use `sum_addChar_quadForm_translate`):
     `M = ψ(z·pairForm_v(u−v)) · ∑_s ψ(F(s) + polar F s b)` once the linear part `z·polar pairForm_v(·,u−v)` is rewritten
     as `polar F (·, b)` for `b` solving `polar F (·,b) = z·polar pairForm_v(·,u−v)` (exists when `F` is NONDEGENERATE).
  3. Complete the square: `sum_addChar_quadForm_linear` (GaussCount) at `r = 1` (Q := F) ⟹
     `∑_s ψ(F s + polar F s b) = ψ(−F b)·∑_s ψ(F s)`.
  4. Evaluate `∑_s ψ(F s) = (∏χ(wᵢ))·gaussSum^d = χ(disc F)·gaussSum^d` via `sum_addChar_quadForm` (needs `F` nondeg /
     `SeparatingLeft`, `[Invertible (2:K)]`).
  5. Handle the DEGENERATE `(y,z)` locus (where `F` drops rank — the "diagonal" analog; e.g. for the singleton
     `pairCharSum_factor` the `y+z=0` diagonal vanished via `sum_addChar_multiQuad_zero` + `sum_addChar_linearMap`).
Then: **increment 3** — feed the closed form into `pairCharSum_factor_gen`'s outer `∑_{y,z}` and bound the per-pair
`c₀ < 1` (the one ℂ-magnitude step: `|gaussSum| = √q` via `gaussSum_sq`; `c₀·n = z₂' + ½(nn' + T)`, zero-counts via
`card_quadForm_eq`). **increments 4+5 (anchor existence FOLDS into averaging — the matching trick):** build base `T` (k iid
points), match into DISJOINT pairs ⟹ independent ⟹ `P[(u,u') unsep] ≤ c̄₀^{k/2}`, `c̄₀ = V×V density of non-separating pairs`;
first moment ⟹ base `O(d log q)` separates all pairs, NO separate/universal anchor. Single input `c̄₀ < 1` (bound it from the
per-anchor `c₀` + "bad-anchor locus is a proper subvariety, density O(1/q)" — NOT a joint `(a,t)` Deligne sum). Probe-confirmed:
`c̄₀ ≈ 0.45` flat in q; worst single anchor `maxC0` hits 1 at small q ⟹ use the average, not a universal anchor. Fed to
`reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`PublicTheoremIndex.md:1248`). Full narrative: plan §13.

NOT in build (scratch; `lake env lean ChainDescent/ScratchPairSep.lean`). Reduction skeleton: `ScratchCrux.lean`.
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

/-- **The single-shift reduction of `M(y,z)` (increment 2, forward step — UNCONDITIONAL).** The inner sum
`M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))` (written via `pairForm`) reduces, by `pairCombine` then
recentring `t ↦ t−u`, to a CONSTANT phase times a sum of `ψ` of `F(s) + (linear in s)`, where
`F = y•pairForm_u + z•pairForm_v`. No nondegeneracy is used here; this is the clean reorganisation that sets up
the complete-the-square step (which then needs `F` nondeg to absorb the linear term into `polar F · b`). -/
theorem pairSum_to_shifted {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V)
    (u v t₀ : V) (y z : K) :
    (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))
      = ψ (z * pairForm Q (t₀ - v) (u - v))
        * ∑ s : V, ψ ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s
            + z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v)) := by
  set Pu := pairForm Q (t₀ - u) with hPu
  set Pv := pairForm Q (t₀ - v) with hPv
  set F := y • Pu + z • Pv with hF
  have hstep : ∀ t : V, y * Pu (t - u) + z * Pv (t - v)
      = (F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v)) + z * Pv (u - v) := by
    intro t
    have h := pairCombine Q u v t₀ t y z
    rw [← hPu, ← hPv, ← hF] at h
    rw [h]
  calc (∑ t : V, ψ (y * Pu (t - u) + z * Pv (t - v)))
      = ∑ t : V, ψ ((F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v)) + z * Pv (u - v)) :=
        Finset.sum_congr rfl (fun t _ => by rw [hstep t])
    _ = ∑ t : V, ψ (F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v)) * ψ (z * Pv (u - v)) :=
        Finset.sum_congr rfl (fun t _ => by rw [AddChar.map_add_eq_mul])
    _ = (∑ t : V, ψ (F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v))) * ψ (z * Pv (u - v)) := by
        rw [← Finset.sum_mul]
    _ = ψ (z * Pv (u - v)) * ∑ t : V, ψ (F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v)) := by
        rw [mul_comm]
    _ = ψ (z * Pv (u - v)) * ∑ s : V, ψ (F s + z * QuadraticMap.polar Pv s (u - v)) := by
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight u)
          (fun t => ψ (F (t - u) + z * QuadraticMap.polar Pv (t - u) (u - v)))
          (fun s => ψ (F s + z * QuadraticMap.polar Pv s (u - v)))
          (fun t => by rw [Equiv.subRight_apply])

/-- **Complete the square (increment 2, forward step).** Once the linear term `L s` of the shifted sum is
represented as `polar F s b` (possible exactly when `F` is nondegenerate — that representability is the separate
next piece), the linear part is absorbed by a translate and `∑_s ψ(F s + L s) = ψ(−F b)·∑_s ψ(F s)`. This is
`sum_addChar_quadForm_linear` at `r = 1`. Unconditional given the representation `hb`. -/
theorem sum_addChar_shifted_eval {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (F : QuadraticForm K V) (L : V → K) (b : V)
    (hb : ∀ s, L s = QuadraticMap.polar F s b) :
    (∑ s : V, ψ (F s + L s)) = ψ (-(F b)) * ∑ s : V, ψ (F s) := by
  have h := sum_addChar_quadForm_linear ψ F 1 b
  simp only [Units.val_one, one_mul, inv_one] at h
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hb s] :
        ∀ s ∈ Finset.univ, ψ (F s + L s) = ψ (F s + QuadraticMap.polar F s b))]
  exact h

/-- **The `M(y,z)` closed form, modulo the representation `b` (increment 2 — ASSEMBLED).** Chains
`pairSum_to_shifted` (reorganise) with `sum_addChar_shifted_eval` (complete the square): given a vector `b`
representing the residual linear term against `F = y•pairForm_u + z•pairForm_v` (i.e. `hb`, which exists exactly
when `F` is nondegenerate), the inner sum `M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))` collapses to
`ψ(z·pairForm_v(u−v)) · ψ(−F b) · ∑_s ψ(F s)`. The two remaining inputs — the existence of `b` (nondeg of `F`)
and the evaluation `∑_s ψ(F s) = (∏χ wᵢ)·gaussSum^d` (`sum_addChar_quadForm`) — are now the only open pieces of
the closed form (plus the degenerate-`(y,z)` locus where `F` drops rank: the axes `{y=0}∪{z=0}` + the pencil's
discriminant conic, since every `pairForm` is itself degenerate). -/
theorem pairSum_closed_of_repr {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V)
    (u v t₀ : V) (y z : K) (b : V)
    (hb : ∀ s, z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v)
            = QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s b) :
    (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))
      = ψ (z * pairForm Q (t₀ - v) (u - v))
        * (ψ (-((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) b))
            * ∑ s : V, ψ ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s)) := by
  rw [pairSum_to_shifted ψ Q u v t₀ y z]
  congr 1
  exact sum_addChar_shifted_eval ψ (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v))
    (fun s => z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v)) b hb

end InnerSum

end ChainDescent

#print axioms ChainDescent.quadChar_addChar_sum
#print axioms ChainDescent.pairCharSum_factor_gen
#print axioms ChainDescent.pairCharSum_factor
#print axioms ChainDescent.pairForm_apply
#print axioms ChainDescent.detG2_eq_pairForm
#print axioms ChainDescent.pairCombine
#print axioms ChainDescent.sum_addChar_quadForm_translate
#print axioms ChainDescent.pairSum_to_shifted
#print axioms ChainDescent.sum_addChar_shifted_eval
#print axioms ChainDescent.pairSum_closed_of_repr
