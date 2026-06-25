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

**LANDED in this file — 24 lemmas, all axiom-clean `[propext, Classical.choice, Quot.sound]`; full file `lake env lean`
green (NOT in build.sh).** Grouped by increment:

*Increment 1 — Gauss bridge + factoring (general `R'`, char-zero domain):* `quadChar_addChar_sum` (the **Gauss bridge**
`∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)`, reusable atom) + `pairCharSum_factor_gen` (the **"no Weil" core**:
`gaussSum² · ∑_t χ(f t)χ(g t) = ∑_y ∑_z χ(y)χ(z)·(∑_t ψ(y·f t + z·g t))`, any `f,g`; `pairCharSum_factor` = singleton corollary).

*Increment 2 — `M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀)+z·det G₂(v;t,t₀))` closed form on the NONDEGENERATE locus:*
`pairForm`/`pairForm_apply`/`detG2_eq_pairForm` (pair invariant IS `pairForm Q a = 4 Q(a)·Q − (polar Q · a)²` at shift `t−u`),
`pairCombine` (two-pivot integrand = form `(y•pairForm_u + z•pairForm_v)` + linear `z·polar pairForm_v(·,u−v)` + const),
`sum_addChar_quadForm_translate`, `pairSum_to_shifted`, `sum_addChar_shifted_eval` (complete-the-square given `b`),
`pairSum_closed_of_repr`, `exists_repr_of_nondeg` (`b` from `F.polarBilin` nondeg via `BilinForm.toDual`),
`pairSum_closed_of_nondeg`, `pairSum_fully_closed` (`M = ψ(const)·ψ(−F b)·(∏χ wᵢ)·gaussSum^d`); degenerate-locus (exact):
`pairForm_polar_anchor`/`pairForm_self_anchor` (every `pairForm Q a` degenerate, `a∈radical`), `sum_addChar_radical_vanish`.

*Increment 3 — per-pair `c₀<1` machinery (over `ℂ`; needs `import Mathlib.Analysis.Complex.Basic`):*
`norm_addChar_eq_one`, `norm_gaussSum_sq` (**`‖gaussSum‖²=q`** = `|gaussSum|=√q`), `norm_pairSum_le`,
**`norm_sq_sum_addChar_quadForm`** (`‖∑ψ(Q)‖²=qᵈ·|radical Q|`, ANY `Q`), **`norm_sq_sum_addChar_quadForm_linear_le`**
(`‖∑ψ(Q+L)‖²≤qᵈ·|radical Q|`), **`norm_sq_pairSum_le`** (3c: `‖M(y,z)‖²≤qᵈ·|radical F|`, nondeg AND conic uniformly),
**`zeroCount_sq_le`** (3d: `(z·q−qᵈ)²≤(q−1)²·qᵈ·|radical P|`), **`normT_le`** (3e-i:
`q·‖T‖ ≤ ∑_{y,z} ‖χy‖‖χz‖·√(qᵈ·|radical F_{y,z}|)`, `T = ∑_t χ(det G₂(u;·,t₀))χ(det G₂(v;·,t₀))`).

**★ PICK UP HERE — finish increment 3 (`c₀<1`), then the matching-trick assembly. NO MORE MAGNITUDE ANALYSIS NEEDED**
(all Gauss-sum/magnitude tools above are landed). The remaining steps are counting + Schwartz-Zippel + arithmetic:
  1. **Good-anchor count (the one remaining analytic input; SHARED with increment 4).** Bound `normT_le`'s RHS radical-sum:
     `#{(y,z) : F_{y,z} = y•pairForm_u + z•pairForm_v degenerate} ≤ d(q−1)`, by **`MvPolynomial.schwartz_zippel_totalDegree`**
     (Mathlib, confirmed present) on the pencil discriminant `det(y·G_u + z·G_v)` (degree `d` in `(y,z)`; `≢0` ⟺ good anchor).
     ⟹ `‖T‖ ≤ [(q−1)²·q^{d/2} + d(q−1)·q^{(d+1)/2}]/q` (nondeg `(y,z)`: `|radical|=1`; conic: `|radical|≤q`).
  2. **`c₀` counting identity (pure ℤ counting).** `2·NS ≤ 2·z_u + n + T_ℤ` (`NS = #{t : χ(I_u t)=χ(I_v t)}`; `χ`-value cases:
     `#both0 ≤ z_u`, `#{both≠0,same} = ½(N₂+T_ℤ)`); cast `T_ℤ ↔ T_ℂ` (`‖T_ℂ‖ = |T_ℤ|`). (Simplification: only `z_u` needed,
     drop `z₂`,`z_v`.)
  3. **Arithmetic.** Plug `zeroCount_sq_le` (`z_u`) + step-1 `‖T‖` bound ⟹ `c₀ = NS/n ≤ ¾` for `q ≥ q₀` (sqrt comparisons, done
     squared); small `q` by `decide` or via the matching trick's small-`q` handling.
  4. **Matching-trick assembly (increments 4+5).** `ScratchMatching.exists_separating_base` (LANDED, axiom-clean) is the engine:
     match the base into DISJOINT independent probe/anchor pairs (`det G₂` symmetric in `(t,a)`, so anchor existence dissolves) ⟹
     `c̄₀ < 1` (V×V non-separating density, from step-1 good-anchor count + step-2/3 per-anchor `c₀`) ⟹ separating base `O(d log q)`.
     Then bridge `χ(det G₂)` recoverable from `Z_u({t,t₀})` ⟹ `ZProfileSeparates` ⟹
     `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`PublicTheoremIndex.md:1248`). Probe `Probe_D3dPairCount`: `cbarMax≈0.5`
     flat, `q·badFrMx→0` (good-anchor O(1/q)). Full narrative + status: plan §13.

NOT in build (scratch; `lake env lean ChainDescent/ScratchPairSep.lean`). Reduction skeleton: `ScratchCrux.lean`;
matching trick: `ScratchMatching.lean`.
-/
import ChainDescent.GaussCount
import Mathlib.Analysis.Complex.Basic

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

/-- **Representability from nondegeneracy (increment 2, piece (i)).** On a finite-dimensional space, if the polar
bilinear form of `F` is nondegenerate then every linear functional `ℓ` is `polar F (·, b)` for some `b` — exactly
the input `pairSum_closed_of_repr` needs. Via Mathlib's `LinearMap.BilinForm.toDual` (the nondeg-form ≃ dual) and
the symmetry of `polar`. -/
theorem exists_repr_of_nondeg {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : QuadraticForm K V) (hF : (F.polarBilin).Nondegenerate) (ℓ : Module.Dual K V) :
    ∃ b : V, ∀ s : V, ℓ s = QuadraticMap.polar F s b := by
  refine ⟨(LinearMap.BilinForm.toDual F.polarBilin hF).symm ℓ, fun s => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := F.polarBilin) (hB := hF) ℓ s
  rw [QuadraticMap.polarBilin_apply_apply] at h
  rw [← h]
  exact QuadraticMap.polar_comm F _ _

/-- **The `M(y,z)` closed form from nondegeneracy alone (increment 2, (i) discharged).** Combining
`exists_repr_of_nondeg` with `pairSum_closed_of_repr`: when `F = y•pairForm_u + z•pairForm_v` has nondegenerate
polar form, there is a `b` (the canonical representative of the residual linear term) with
`M(y,z) = ψ(z·pairForm_v(u−v)) · ψ(−F b) · ∑_s ψ(F s)`. The only remaining step to a fully explicit value is the
quadratic Gauss-sum evaluation of `∑_s ψ(F s)` (`sum_addChar_quadForm`), and the degenerate-`(y,z)` locus. -/
theorem pairSum_closed_of_nondeg {R' : Type*} [CommRing R'] (ψ : AddChar K R')
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (Q : QuadraticForm K V) (u v t₀ : V) (y z : K)
    (hF : ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)).polarBilin).Nondegenerate) :
    ∃ b : V,
      (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))
        = ψ (z * pairForm Q (t₀ - v) (u - v))
          * (ψ (-((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) b))
              * ∑ s : V, ψ ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s)) := by
  obtain ⟨b, hb⟩ := exists_repr_of_nondeg (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) hF
    (z • (LinearMap.flip (pairForm Q (t₀ - v)).polarBilin (u - v)))
  refine ⟨b, pairSum_closed_of_repr ψ Q u v t₀ y z b (fun s => ?_)⟩
  have hℓ : (z • (LinearMap.flip (pairForm Q (t₀ - v)).polarBilin (u - v))) s
      = z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v) := by
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
      smul_eq_mul]
  rw [← hℓ]; exact hb s

/-- **The fully explicit `M(y,z)` closed form (increment 2 — COMPLETE on the nondegenerate locus).** Chaining
`pairSum_closed_of_nondeg` (absorb the linear term) with `sum_addChar_quadForm` (evaluate the quadratic Gauss sum)
gives, for `F = y•pairForm_u + z•pairForm_v` nondegenerate,
`M(y,z) = ψ(z·pairForm_v(u−v)) · ψ(−F b) · (∏ᵢ χ(wᵢ)) · gaussSum^d`. Every factor is a unit-modulus phase except
`gaussSum^d`, so `|M| = |gaussSum|^d = q^{d/2}` — the magnitude that drives the increment-3 `c₀` bound. The two
nondegeneracy hypotheses (`polarBilin.Nondegenerate` for the representation, `(associated F).SeparatingLeft` for the
Gauss evaluation) are the SAME nondegeneracy of `F` up to the unit `2` (`two_nsmul_associated`); both are discharged
concretely at instantiation. Open beyond this: the degenerate-`(y,z)` locus (axes ∪ conic — the main term). -/
theorem pairSum_fully_closed [Fintype K] [DecidableEq K] [Invertible (2 : K)] (hch : ringChar K ≠ 2)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (Q : QuadraticForm K V) (u v t₀ : V) (y z : K)
    (hFpolar : ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)).polarBilin).Nondegenerate)
    (hFassoc : (QuadraticMap.associated (R := K)
        (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v))).SeparatingLeft) :
    ∃ (b : V) (w : Fin (Module.finrank K V) → Kˣ),
      (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))
        = ψ (z * pairForm Q (t₀ - v) (u - v))
          * (ψ (-((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) b))
              * ((∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (w i : K))
                  * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
                      ^ Module.finrank K V)) := by
  obtain ⟨b, hb⟩ := pairSum_closed_of_nondeg ψ Q u v t₀ y z hFpolar
  obtain ⟨w, hw⟩ := sum_addChar_quadForm hch hψ
    (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) hFassoc
  exact ⟨b, w, by rw [hb, hw]⟩

/-! ### The degenerate locus (increment 2 — exact part)

When `F` drops rank — `F.polarBilin` has a nonzero radical — the closed form `pairSum_fully_closed` does not apply.
The exact handling: if a radical direction `r` (`∀ s, polar F s r = 0`, `F r = 0`) is NOT annihilated by the residual
linear term `L`, the whole sum *vanishes* (the pair analog of the singleton's `y+z=0` diagonal vanishing). Combined
with the fact that the outer `∑_{y,z}` carries the weight `χ(y)χ(z)` (which is `0` on the axes `{y=0}∪{z=0}`, where the
degeneracy is forced because every `pairForm Q a` has `a` in its radical), this leaves only the thin `L(r)=0`
sub-locus of the discriminant conic as a (bounded, lower-order) main term — handled by the increment-3 magnitude
bound. -/

/-- **Every `pairForm Q a` is degenerate: `a` lies in its polar-radical, and `pairForm Q a (a) = 0`.** This is the
structural source of the degenerate locus (it forces degeneracy on the axes `{y=0}∪{z=0}`). Verified by expanding
`pairForm_apply` + the polar identities. -/
theorem pairForm_polar_anchor {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (a s : V) :
    QuadraticMap.polar (pairForm Q a) s a = 0 := by
  have hsa : Q (s + a) = Q s + Q a + QuadraticMap.polar Q s a := by rw [QuadraticMap.polar]; ring
  have hpsa : QuadraticMap.polar Q (s + a) a
      = QuadraticMap.polar Q s a + QuadraticMap.polar Q a a := QuadraticMap.polar_add_left Q s a a
  rw [QuadraticMap.polar, pairForm_apply, pairForm_apply, pairForm_apply, hsa, hpsa,
    QuadraticMap.polar_self, nsmul_eq_mul]
  push_cast; ring

theorem pairForm_self_anchor {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (a : V) :
    pairForm Q a a = 0 := by
  rw [pairForm_apply, QuadraticMap.polar_self, nsmul_eq_mul]
  push_cast; ring

/-- **Radical-vanishing (the degenerate-locus diagonal collapse).** If `r` lies in the polar-radical of `F`
(`∀ s, polar F s r = 0`) with `F r = 0`, and the residual linear functional does not annihilate `r` (`L r ≠ 0`),
then `∑_s ψ(F s + L s) = 0`. Proof: translating by `c•r` fixes `F` (constant on `⟨r⟩`-cosets) and shifts `L` by
`c·(L r)`, so the sum is multiplied by `ψ(c·L r)`; choosing `c` with `ψ(c·L r) ≠ 1` (primitivity) forces it to `0`. -/
theorem sum_addChar_radical_vanish {R' : Type*} [CommRing R'] [IsDomain R'] [Fintype K]
    {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (F : QuadraticForm K V) (L : Module.Dual K V)
    (r : V) (hrad : ∀ s, QuadraticMap.polar F s r = 0) (hFr : F r = 0) (hLr : L r ≠ 0) :
    (∑ s : V, ψ (F s + L s)) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : K, ψ (L r * c) ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact (hψ hLr) (by ext c; simpa only [AddChar.mulShift_apply, AddChar.one_apply] using hcon c)
  have hF_inv : ∀ s : V, F (s + c • r) = F s := by
    intro s
    have h1 : QuadraticMap.polar F s (c • r) = 0 := by
      rw [QuadraticMap.polar_smul_right, hrad s, smul_zero]
    have h2 : F (c • r) = 0 := by rw [QuadraticMap.map_smul, hFr, smul_zero]
    have h3 : F (s + c • r) = QuadraticMap.polar F s (c • r) + F s + F (c • r) := by
      rw [QuadraticMap.polar]; ring
    rw [h3, h1, h2]; ring
  have hL_shift : ∀ s : V, L (s + c • r) = L s + c * (L r) := by
    intro s; rw [map_add, map_smul, smul_eq_mul]
  have hreind : (∑ s : V, ψ (F s + L s)) = ∑ s : V, ψ (F (s + c • r) + L (s + c • r)) :=
    (Equiv.sum_comp (Equiv.addRight (c • r)) (fun s => ψ (F s + L s))).symm
  have heq : (∑ s : V, ψ (F (s + c • r) + L (s + c • r)))
      = ψ (c * L r) * ∑ s : V, ψ (F s + L s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hF_inv s, hL_shift s,
      show F s + (L s + c * L r) = (c * L r) + (F s + L s) from by ring, AddChar.map_add_eq_mul]
  have key : (∑ s : V, ψ (F s + L s)) = ψ (c * L r) * ∑ s : V, ψ (F s + L s) := hreind.trans heq
  have hsub : (1 - ψ (c * L r)) * (∑ s : V, ψ (F s + L s)) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.1 hsub with h | h
  · exact absurd (by rw [mul_comm]; exact (sub_eq_zero.1 h).symm : ψ (L r * c) = 1) hc
  · exact h

end InnerSum

/-! ## Increment 3, step 3b — the ℂ magnitude of `M` (`|M| = q^{d/2}` on the nondeg locus)

The one place the development leaves the equality regime: over `ℂ`, the quadratic Gauss sum has `|gaussSum| = √q`
(`norm_gaussSum_sq`), `AddChar` values are unit-modulus (`norm_addChar_eq_one`, roots of unity), and the
`quadraticChar` factors have norm `≤ 1`; so the fully-explicit `M = phase · (∏χ) · gaussSum^d` has
`‖M‖ ≤ ‖gaussSum‖^d`, i.e. `‖M‖² ≤ (card K)^d` — the magnitude the increment-3 `c₀` bound consumes. -/
section CMagnitude

/-- **`AddChar` values into `ℂ` are unit-modulus** (each `ψ c` is a `(card K)`-th root of unity). The phase factors
of `M` therefore drop out of its magnitude. -/
theorem norm_addChar_eq_one {K : Type*} [AddGroup K] [Fintype K] (ψ : AddChar K ℂ) (c : K) :
    ‖ψ c‖ = 1 := by
  have hpow : ψ c ^ Fintype.card K = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hn : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  have h2 : ‖ψ c‖ ^ Fintype.card K = 1 := by rw [← norm_pow, hpow, norm_one]
  rcases lt_trichotomy (‖ψ c‖) 1 with hlt | heq | hgt
  · exfalso; have := pow_lt_one₀ (norm_nonneg _) hlt hn; rw [h2] at this; exact lt_irrefl 1 this
  · exact heq
  · exfalso; have := one_lt_pow₀ hgt hn; rw [h2] at this; exact lt_irrefl 1 this

/-- **The quadratic Gauss sum has `|gaussSum| = √q`** (over `ℂ`): `‖gaussSum χ ψ‖² = card K`. Via Mathlib's
`gaussSum_mul_gaussSum_pow_orderOf_sub_one` (`gaussSum² = χ(-1)·card` for the order-2 character `χ`) and `|χ(-1)| = 1`.
The genuinely-new analytic content of increment 3. -/
theorem norm_gaussSum_sq {K : Type*} [Field K] [Fintype K] [DecidableEq K] (hch : ringChar K ≠ 2)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) ψ‖ ^ 2 = Fintype.card K := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  have hQuad : χ.IsQuadratic := (quadraticChar_isQuadratic K).comp _
  have hχ1 : χ ≠ 1 := by
    rw [hχ, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
    exact quadraticChar_ne_one hch
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf χ = 2 := orderOf_eq_prime hQuad.sq_eq_one hχ1
  have hsq : gaussSum χ ψ ^ 2 = χ (-1) * (Fintype.card K : ℂ) := by
    have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
    have hpow : χ ^ (orderOf χ - 1) = χ := by rw [hord]; exact pow_one χ
    rw [hpow, ← pow_two] at h
    exact h
  have hchm1 : ‖χ (-1)‖ = 1 := by
    rcases hQuad (-1) with h | h | h
    · exfalso
      have h0 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
      rw [h] at h0; simp at h0
    · rw [h]; simp
    · rw [h]; simp
  rw [show ‖gaussSum χ ψ‖ ^ 2 = ‖gaussSum χ ψ ^ 2‖ from (norm_pow _ _).symm, hsq, norm_mul, hchm1,
    one_mul, norm_natCast]

/-- **`‖M(y,z)‖ ≤ ‖gaussSum‖^d` on the nondegenerate locus** (so `‖M‖² ≤ (card K)^d = q^d`). From the explicit
`pairSum_fully_closed` value: the two `ψ`-phases have norm `1` (`norm_addChar_eq_one`), the `∏ χ(wᵢ)` factor has
norm `≤ 1` (each `χ` value is `0, 1`, or `−1`), leaving `‖gaussSum‖^d`. The increment-3 magnitude input. -/
theorem norm_pairSum_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hch : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (Q : QuadraticForm K V) (u v t₀ : V) (y z : K)
    (hFpolar : ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)).polarBilin).Nondegenerate)
    (hFassoc : (QuadraticMap.associated (R := K)
        (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v))).SeparatingLeft) :
    ‖∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v))‖
      ≤ ‖gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) ψ‖ ^ Module.finrank K V := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  have hQuad : χ.IsQuadratic := (quadraticChar_isQuadratic K).comp _
  obtain ⟨b, w, hM⟩ := pairSum_fully_closed hch hψ Q u v t₀ y z hFpolar hFassoc
  rw [hM, norm_mul, norm_mul, norm_mul, norm_pow, norm_addChar_eq_one, norm_addChar_eq_one,
    one_mul, one_mul]
  have hprod : ‖∏ i, χ (w i : K)‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rcases hQuad (w i : K) with h | h | h <;> rw [h] <;> simp
  exact mul_le_of_le_one_left (by positivity) hprod

/-! ### Increment 3, step 3c-tool — the degenerate quadratic Gauss-sum magnitude

The unified tool for the degenerate locus: `‖∑_x ψ(Q x)‖² = qᵈ · |radical Q|` for ANY quadratic form `Q` (no
nondegeneracy). Quotient-free proof: `‖·‖² = (∑ψ)·conj(∑ψ) = ∑_{x,h} ψ(Q x − Q(x+h))`, expand
`Q x − Q(x+h) = −polar Q x h − Q h`, and `∑_x ψ(−polar Q x h) = qᵈ·[h ∈ radical]` by `sum_addChar_linearMap`; on the
radical `Q h = 0` so the phase is 1. Generalizes `norm_gaussSum_sq` (nondeg ⟹ radical = {0}). Powers both 3c (conic
magnitude, `|radical| ≤ q`) and 3d (zero-counts via `card_quadForm_eq`). -/
theorem norm_sq_sum_addChar_quadForm {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V) :
    ‖∑ x : V, ψ (Q x)‖ ^ 2
      = (Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card := by
  classical
  set S := ∑ x : V, ψ (Q x) with hS
  -- conjugate of a ψ-value is ψ of the negation (values are unit-modulus)
  have hconj : ∀ z : K, (starRingEnd ℂ) (ψ z) = ψ (-z) := by
    intro z
    have hns : Complex.normSq (ψ z) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_addChar_eq_one]; norm_num
    have hmul : ψ z * (starRingEnd ℂ) (ψ z) = 1 := by rw [Complex.mul_conj, hns, Complex.ofReal_one]
    have hne : ψ z ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hconjz : (starRingEnd ℂ) (ψ z) = (ψ z)⁻¹ := by
      rw [← one_mul ((starRingEnd ℂ) (ψ z)), ← inv_mul_cancel₀ hne, mul_assoc, hmul, mul_one]
    rw [hconjz, ← AddChar.map_neg_eq_inv]
  -- the core complex identity: S · conj S = card V · |radical|
  have hmain : S * (starRingEnd ℂ) S
      = (Fintype.card V : ℂ)
        * ((Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card : ℂ) := by
    have hconjS : (starRingEnd ℂ) S = ∑ y : V, ψ (-(Q y)) := by
      rw [hS, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (Q y))
    rw [hS, hconjS, Finset.sum_mul_sum]
    -- ∑_x ∑_y ψ(Q x) * ψ(-(Q y)) = ∑_x ∑_y ψ(Q x - Q y)
    have e1 : ∀ x y : V, ψ (Q x) * ψ (-(Q y)) = ψ (Q x - Q y) := by
      intro x y; rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => e1 x y))]
    -- reindex inner y ↦ x + h
    have e2 : ∀ x : V, (∑ y : V, ψ (Q x - Q y)) = ∑ h : V, ψ (Q x - Q (x + h)) :=
      fun x => (Equiv.sum_comp (Equiv.addLeft x) (fun y => ψ (Q x - Q y))).symm
    rw [Finset.sum_congr rfl (fun x _ => e2 x)]
    -- Q x - Q(x+h) = -(polar Q x h) - Q h
    have e3 : ∀ x h : V, ψ (Q x - Q (x + h)) = ψ (-(QuadraticMap.polar Q x h) - Q h) := by
      intro x h; congr 1; rw [QuadraticMap.polar]; ring
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun h _ => e3 x h)), Finset.sum_comm]
    -- ∑_h ∑_x ψ(-(polar Q x h) - Q h) = ∑_h ψ(-Q h)·(∑_x ψ(-(polar Q x h)))
    have e4 : ∀ h : V, (∑ x : V, ψ (-(QuadraticMap.polar Q x h) - Q h))
        = ψ (-(Q h)) * ∑ x : V, ψ (-(QuadraticMap.polar Q x h)) := by
      intro h
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by rw [← AddChar.map_add_eq_mul]; congr 1; ring)
    rw [Finset.sum_congr rfl (fun h _ => e4 h)]
    -- inner linear sum via sum_addChar_linearMap
    have e5 : ∀ h : V, (∑ x : V, ψ (-(QuadraticMap.polar Q x h)))
        = if (∀ x, QuadraticMap.polar Q x h = 0) then (Fintype.card V : ℂ) else 0 := by
      intro h
      have hφx : ∀ x, (-(Q.polarBilin.flip h)) x = -(QuadraticMap.polar Q x h) := by
        intro x; rw [LinearMap.neg_apply, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
      rw [show (∑ x : V, ψ (-(QuadraticMap.polar Q x h)))
            = ∑ x : V, ψ ((-(Q.polarBilin.flip h)) x) from
          Finset.sum_congr rfl (fun x _ => by rw [hφx x]),
        sum_addChar_linearMap hψ]
      refine if_congr ?_ rfl rfl
      rw [LinearMap.ext_iff]
      constructor
      · intro hh x; have := hh x; rw [hφx x, LinearMap.zero_apply, neg_eq_zero] at this; exact this
      · intro hh x; rw [hφx x, LinearMap.zero_apply, neg_eq_zero]; exact hh x
    rw [Finset.sum_congr rfl (fun h _ => by rw [e5 h])]
    -- ∑_h ψ(-Q h)·(if radical then card else 0) = card·|radical|
    have e6 : ∀ h : V, ψ (-(Q h))
          * (if (∀ x, QuadraticMap.polar Q x h = 0) then (Fintype.card V : ℂ) else 0)
        = (if (∀ x, QuadraticMap.polar Q x h = 0) then (Fintype.card V : ℂ) else 0) := by
      intro h
      split_ifs with hP
      · have hQh : Q h = 0 := by
          have hps := QuadraticMap.polar_self Q h
          rw [hP h, nsmul_eq_mul] at hps
          have h2 : ((2 : ℕ) : K) * Q h = 0 := hps.symm
          have h2K : ((2 : ℕ) : K) ≠ 0 := by
            simpa using (Invertible.ne_zero (2 : K))
          exact (mul_eq_zero.1 h2).resolve_left h2K
        rw [hQh, neg_zero, AddChar.map_zero_eq_one, one_mul]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun h _ => e6 h), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  -- bridge to ‖S‖²
  have key : ((‖S‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card V : ℂ)
        * ((Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card : ℂ) := by
    rw [← hmain, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq]
  exact_mod_cast key

/-- **The with-linear degenerate magnitude bound (3c — uniform over nondeg AND conic).** For ANY quadratic form `Q`
and linear functional `L`, `‖∑_x ψ(Q x + L x)‖² ≤ qᵈ · |radical Q|`. (Exact: `S·conj S = qᵈ·∑_{h∈radical} ψ(−L h)`,
bounded by the triangle inequality + `‖ψ‖ = 1`.) This is the magnitude `M` actually needs (its integrand carries a
linear term), and it covers the degenerate conic (`|radical| ≤ q ⟹ ‖∑‖ ≤ q^{(d+1)/2}`) and nondeg
(`|radical| = 1 ⟹ ‖∑‖ ≤ q^{d/2}`) uniformly. -/
theorem norm_sq_sum_addChar_quadForm_linear_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Invertible (2 : K)] {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V) (L : Module.Dual K V) :
    ‖∑ x : V, ψ (Q x + L x)‖ ^ 2
      ≤ (Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card := by
  classical
  set S := ∑ x : V, ψ (Q x + L x) with hS
  set rad := Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0) with hrad
  have hconj : ∀ z : K, (starRingEnd ℂ) (ψ z) = ψ (-z) := by
    intro z
    have hns : Complex.normSq (ψ z) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_addChar_eq_one]; norm_num
    have hmul : ψ z * (starRingEnd ℂ) (ψ z) = 1 := by rw [Complex.mul_conj, hns, Complex.ofReal_one]
    have hne : ψ z ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hconjz : (starRingEnd ℂ) (ψ z) = (ψ z)⁻¹ := by
      rw [← one_mul ((starRingEnd ℂ) (ψ z)), ← inv_mul_cancel₀ hne, mul_assoc, hmul, mul_one]
    rw [hconjz, ← AddChar.map_neg_eq_inv]
  have hmain : S * (starRingEnd ℂ) S = (Fintype.card V : ℂ) * ∑ h ∈ rad, ψ (-(L h)) := by
    have hconjS : (starRingEnd ℂ) S = ∑ y : V, ψ (-(Q y + L y)) := by
      rw [hS, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (Q y + L y))
    rw [hS, hconjS, Finset.sum_mul_sum]
    have e1 : ∀ x y : V, ψ (Q x + L x) * ψ (-(Q y + L y)) = ψ ((Q x + L x) - (Q y + L y)) := by
      intro x y; rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => e1 x y))]
    have e2 : ∀ x : V, (∑ y : V, ψ ((Q x + L x) - (Q y + L y)))
        = ∑ h : V, ψ ((Q x + L x) - (Q (x + h) + L (x + h))) :=
      fun x => (Equiv.sum_comp (Equiv.addLeft x) (fun y => ψ ((Q x + L x) - (Q y + L y)))).symm
    rw [Finset.sum_congr rfl (fun x _ => e2 x)]
    have e3 : ∀ x h : V, ψ ((Q x + L x) - (Q (x + h) + L (x + h)))
        = ψ (-(QuadraticMap.polar Q x h) - (Q h + L h)) := by
      intro x h; congr 1
      have hLadd : L (x + h) = L x + L h := L.map_add x h
      rw [QuadraticMap.polar, hLadd]; ring
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun h _ => e3 x h)), Finset.sum_comm]
    have e4 : ∀ h : V, (∑ x : V, ψ (-(QuadraticMap.polar Q x h) - (Q h + L h)))
        = ψ (-(Q h + L h)) * ∑ x : V, ψ (-(QuadraticMap.polar Q x h)) := by
      intro h
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by rw [← AddChar.map_add_eq_mul]; congr 1; ring)
    rw [Finset.sum_congr rfl (fun h _ => e4 h)]
    have e5 : ∀ h : V, (∑ x : V, ψ (-(QuadraticMap.polar Q x h)))
        = if (∀ x, QuadraticMap.polar Q x h = 0) then (Fintype.card V : ℂ) else 0 := by
      intro h
      have hφx : ∀ x, (-(Q.polarBilin.flip h)) x = -(QuadraticMap.polar Q x h) := by
        intro x; rw [LinearMap.neg_apply, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
      rw [show (∑ x : V, ψ (-(QuadraticMap.polar Q x h)))
            = ∑ x : V, ψ ((-(Q.polarBilin.flip h)) x) from
          Finset.sum_congr rfl (fun x _ => by rw [hφx x]), sum_addChar_linearMap hψ]
      refine if_congr ?_ rfl rfl
      rw [LinearMap.ext_iff]
      constructor
      · intro hh x; have := hh x; rw [hφx x, LinearMap.zero_apply, neg_eq_zero] at this; exact this
      · intro hh x; rw [hφx x, LinearMap.zero_apply, neg_eq_zero]; exact hh x
    rw [Finset.sum_congr rfl (fun h _ => by rw [e5 h])]
    have e6 : ∀ h : V, ψ (-(Q h + L h))
          * (if (∀ x, QuadraticMap.polar Q x h = 0) then (Fintype.card V : ℂ) else 0)
        = (if (∀ x, QuadraticMap.polar Q x h = 0) then ψ (-(L h)) * (Fintype.card V : ℂ) else 0) := by
      intro h
      split_ifs with hP
      · have hQh : Q h = 0 := by
          have hps := QuadraticMap.polar_self Q h
          rw [hP h, nsmul_eq_mul] at hps
          have h2 : ((2 : ℕ) : K) * Q h = 0 := hps.symm
          have h2K : ((2 : ℕ) : K) ≠ 0 := by simpa using (Invertible.ne_zero (2 : K))
          exact (mul_eq_zero.1 h2).resolve_left h2K
        rw [hQh, zero_add]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun h _ => e6 h), ← Finset.sum_filter, ← hrad, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => by rw [mul_comm])
  have hnormeq : ‖S‖ ^ 2 = ‖S * (starRingEnd ℂ) S‖ := by
    rw [norm_mul, Complex.norm_conj]; ring
  rw [hnormeq, hmain, norm_mul, norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ h ∈ rad, ψ (-(L h))‖
      ≤ ∑ h ∈ rad, ‖ψ (-(L h))‖ := norm_sum_le _ _
    _ = ∑ _h ∈ rad, (1 : ℝ) := Finset.sum_congr rfl (fun h _ => norm_addChar_eq_one ψ _)
    _ = (rad.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The uniform `|M(y,z)|²` bound (3c — the magnitude consumed by the increment-3 `c₀` bound).** For the inner sum
`M(y,z) = ∑_t ψ(y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀))`, `‖M‖² ≤ qᵈ · |radical F|`, `F = y•pairForm_u + z•pairForm_v`.
On the NONDEG locus `|radical F| = 1 ⟹ ‖M‖² ≤ qᵈ` (matches `norm_pairSum_le`); on the degenerate conic
`|radical F| ≤ q ⟹ ‖M‖² ≤ q^{d+1}` (so `‖M‖ ≤ q^{(d+1)/2}`). Via `pairSum_to_shifted` (`M = ψ(const)·∑_s ψ(F s + L s)`)
+ `norm_sq_sum_addChar_quadForm_linear_le`. -/
theorem norm_sq_pairSum_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] (Q : QuadraticForm K V) (u v t₀ : V) (y z : K) :
    ‖∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v))‖ ^ 2
      ≤ (Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V =>
            ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card := by
  rw [pairSum_to_shifted ψ Q u v t₀ y z, norm_mul, norm_addChar_eq_one, one_mul]
  have hL : ∀ s, z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v)
      = (z • (pairForm Q (t₀ - v)).polarBilin.flip (u - v)) s := by
    intro s
    rw [LinearMap.smul_apply, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  rw [show (∑ s : V, ψ ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s
            + z * QuadraticMap.polar (pairForm Q (t₀ - v)) s (u - v)))
        = ∑ s : V, ψ ((y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) s
            + (z • (pairForm Q (t₀ - v)).polarBilin.flip (u - v)) s) from
      Finset.sum_congr rfl (fun s _ => by rw [hL s])]
  exact norm_sq_sum_addChar_quadForm_linear_le hψ (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v))
    (z • (pairForm Q (t₀ - v)).polarBilin.flip (u - v))

/-- **Zero-count bound (3d).** For a quadratic form `P` (possibly degenerate), the number of zeros `z = #{x : P x = 0}`
satisfies `(z·q − qᵈ)² ≤ (q−1)²·qᵈ·|radical P|` (`qᵈ = card V`). From `count_eq_charsum` (`z·q = ∑_x ∑_t ψ(t·P x)`),
peeling the `t = 0` term (`= qᵈ`), and bounding the rest by the magnitude tool: each `‖∑_x ψ(t·P x)‖² = qᵈ·|radical P|`
(scaling `t ≠ 0` preserves the radical). On the conic-relevant case `|radical P| ≤ q ⟹ z ≤ q^{d-1} + q^{(d+1)/2}`. -/
theorem zeroCount_sq_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] (P : QuadraticForm K V) :
    (((Finset.univ.filter (fun x : V => P x = 0)).card : ℝ) * (Fintype.card K) - (Fintype.card V)) ^ 2
      ≤ ((Fintype.card K : ℝ) - 1) ^ 2
        * ((Fintype.card V : ℝ)
            * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) := by
  classical
  -- D := ∑_{t≠0} ∑_x ψ(t·P x) = (z:ℂ)·q − qᵈ
  have hcount := count_eq_charsum hψ (fun x : V => P x) 0
  simp only [sub_zero] at hcount
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))] at hcount
  simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcount
  set z : ℕ := (Finset.univ.filter (fun x : V => P x = 0)).card with hz
  set D : ℂ := ∑ t ∈ Finset.univ.erase (0 : K), ∑ x : V, ψ (t * P x) with hD
  have hDeq : D = (z : ℂ) * (Fintype.card K) - (Fintype.card V) := by
    rw [hD]; linear_combination hcount
  -- each inner sum's norm² = qᵈ · |radical P|
  have hmag : ∀ t ∈ Finset.univ.erase (0 : K),
      ‖∑ x : V, ψ (t * P x)‖ ≤ Real.sqrt ((Fintype.card V : ℝ)
        * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) := by
    intro t ht
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    have hsm : (∑ x : V, ψ (t * P x)) = ∑ x : V, ψ ((t • P) x) :=
      Finset.sum_congr rfl (fun x _ => by rw [QuadraticMap.smul_apply, smul_eq_mul])
    have hpsm : ∀ x h : V, QuadraticMap.polar (t • P) x h = t * QuadraticMap.polar P x h := by
      intro x h; simp only [QuadraticMap.polar, QuadraticMap.smul_apply, smul_eq_mul]; ring
    have hradeq : (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar (t • P) x h = 0))
        = (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hh x
        have := hh x; rw [hpsm] at this
        exact (mul_eq_zero.1 this).resolve_left ht0
      · intro hh x; rw [hpsm, hh x, mul_zero]
    rw [hsm, show ‖∑ x : V, ψ ((t • P) x)‖
          = Real.sqrt (‖∑ x : V, ψ ((t • P) x)‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm,
      norm_sq_sum_addChar_quadForm hψ (t • P), hradeq]
  -- ‖D‖ ≤ (q−1)·√(qᵈ·|rad|)
  have hDnorm : ‖D‖ ≤ ((Fintype.card K : ℝ) - 1)
      * Real.sqrt ((Fintype.card V : ℝ)
          * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) := by
    calc ‖D‖ ≤ ∑ t ∈ Finset.univ.erase (0 : K), ‖∑ x : V, ψ (t * P x)‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Finset.univ.erase (0 : K), Real.sqrt ((Fintype.card V : ℝ)
            * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) :=
          Finset.sum_le_sum hmag
      _ = ((Fintype.card K : ℝ) - 1)
            * Real.sqrt ((Fintype.card V : ℝ)
              * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
            nsmul_eq_mul]
          congr 2
          rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  -- square, and ‖D‖² = (z·q − qᵈ)²
  have hreal : ‖D‖ ^ 2 = ((z : ℝ) * (Fintype.card K) - (Fintype.card V)) ^ 2 := by
    have hcast : D = (((z : ℝ) * (Fintype.card K) - (Fintype.card V) : ℝ) : ℂ) := by
      rw [hDeq]; push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc (((z : ℝ) * (Fintype.card K) - (Fintype.card V)) ^ 2)
      = ‖D‖ ^ 2 := hreal.symm
    _ ≤ (((Fintype.card K : ℝ) - 1)
          * Real.sqrt ((Fintype.card V : ℝ)
            * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card)) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hDnorm 2
    _ = ((Fintype.card K : ℝ) - 1) ^ 2
          * ((Fintype.card V : ℝ)
            * (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- **The `|T|` bound (3e, step i — the load-bearing analytic step).** The per-pair character sum
`T = ∑_t χ(det G₂(u;t,t₀))·χ(det G₂(v;t,t₀))` (over ℂ) satisfies `q·‖T‖ ≤ ∑_{y,z} ‖χ y‖·‖χ z‖·√(qᵈ·|radical F_{y,z}|)`,
`F_{y,z} = y•pairForm_u + z•pairForm_v`. From the factoring `gaussSum²·T = ∑_{y,z} χ(y)χ(z)·M(y,z)`
(`pairCharSum_factor_gen`), `‖gaussSum‖² = q` (`norm_gaussSum_sq`), the triangle inequality, and the uniform
`‖M(y,z)‖ ≤ √(qᵈ·|radical F|)` (`norm_sq_pairSum_le`). The axes drop (`‖χ 0‖ = 0`); bounding the RHS radical-sum is the
good-anchor count (Schwartz–Zippel, shared with increment 4). -/
theorem normT_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (Q : QuadraticForm K V) (u v t₀ : V) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ ∑ y : K, ∑ z : K,
          ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖
            * ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) z‖
            * Real.sqrt ((Fintype.card V : ℝ)
              * (Finset.univ.filter (fun h : V =>
                  ∀ x, QuadraticMap.polar (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) x h = 0)).card) := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  have hq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card K : ℝ) := norm_gaussSum_sq hF hψ
  have hfac := pairCharSum_factor_gen hF ψ (fun t : V => pairForm Q (t₀ - u) (t - u))
    (fun t : V => pairForm Q (t₀ - v) (t - v))
  have h1 := congrArg norm hfac
  rw [norm_mul, norm_pow, hq] at h1
  rw [h1]
  calc ‖∑ y : K, ∑ z : K, χ y * χ z
          * (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))‖
      ≤ ∑ y : K, ‖∑ z : K, χ y * χ z
          * (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ y : K, ∑ z : K, ‖χ y * χ z
          * (∑ t : V, ψ (y * pairForm Q (t₀ - u) (t - u) + z * pairForm Q (t₀ - v) (t - v)))‖ :=
        Finset.sum_le_sum (fun y _ => norm_sum_le _ _)
    _ ≤ _ := Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun z _ => ?_))
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (norm_sq_pairSum_le hψ Q u v t₀ y z))
    (by positivity)

end CMagnitude

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
#print axioms ChainDescent.exists_repr_of_nondeg
#print axioms ChainDescent.pairSum_closed_of_nondeg
#print axioms ChainDescent.pairSum_fully_closed
#print axioms ChainDescent.pairForm_polar_anchor
#print axioms ChainDescent.pairForm_self_anchor
#print axioms ChainDescent.sum_addChar_radical_vanish
#print axioms ChainDescent.norm_addChar_eq_one
#print axioms ChainDescent.norm_gaussSum_sq
#print axioms ChainDescent.norm_pairSum_le
#print axioms ChainDescent.norm_sq_sum_addChar_quadForm
#print axioms ChainDescent.norm_sq_sum_addChar_quadForm_linear_le
#print axioms ChainDescent.norm_sq_pairSum_le
#print axioms ChainDescent.zeroCount_sq_le
#print axioms ChainDescent.normT_le
