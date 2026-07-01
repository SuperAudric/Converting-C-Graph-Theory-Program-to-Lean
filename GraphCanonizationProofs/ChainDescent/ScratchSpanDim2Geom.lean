/-
# Route A, Phase 1 — the geometric recovery core (the information is present at span-dim-2, `d`-independently)

**What this module builds.** The mathematical heart of route A (recovery doc §8 ITEM B, the re-scoped "(I)"): at a
span-dim-2 base with plane `W = span{a,b}`, the **isoClass profile of a vertex `u` over the whole plane `W`** determines
its exact Gram `(Q u, polar u a, polar u b)`. This is `d`-**independent** (the `(d−2)`-dim complement never enters — the
profile is over `W` only) and needs **no Gauss sums, no Witt, no WL iteration** — pure affine geometry.

**The mechanism.** For `w ∈ W`, the difference `D(w) := Q(u − w) − Q(u' − w)` is **affine** in `w`:
`D(w) = polar Q (u' − u) w + (Q u − Q u')` (the quadratic parts `Q w` cancel). Two vertices with the same profile over
`W` (same isotropic set `Z = {w ∈ W : Q(u − w) = 0}`) have `D = 0` on `Z`. If `Z` **affinely spans** `W` (anchored: some
`w₀ ∈ Z` with `Z − w₀` linearly spanning `W`), the affine `D` vanishes on all of `W`, giving `polar Q (u'−u) = 0` on `W`
— hence `polar u a = polar u' a`, `polar u b = polar u' b` (as `a, b ∈ W`) and `Q u = Q u'`. That is `SameExactGram` to
`{a, b}` — `bᵢ = 1` once the profile is known.

**Honest scope.** This is the recovery *core*: it proves the information is geometrically present at span-dim-2. It
carries the **spanning hypothesis** `hspan` (the level set / conic affinely spans `W`) — the geometric non-degeneracy,
true except for degenerate levels and tiny `q` (a finite tail, discharged separately). The **remaining route-A seam** is
(II): connecting the WL-stable / iterated observable to "isoClass profile over `W`" (the fixpoint propagation the probe's
`r*∈{3,4}` measures) — NOT in this module.

Pure geometry (no `Fintype`, no Witt, no Gauss). Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`,
NOT in `build.sh`.
-/
import ChainDescent.ScratchComplementFactor

namespace ChainDescent.SpanDim2Geom

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- **The difference norm is affine.** `Q (u − w) = Q u + Q w − polar Q u w`. -/
theorem map_sub_eq {u w : V} : Q (u - w) = Q u + Q w - QuadraticMap.polar Q u w := by
  have hmap : Q (u + (-w)) = Q u + Q (-w) + QuadraticMap.polar Q u (-w) :=
    QuadraticMap.map_add _ u (-w)
  rw [QuadraticMap.map_neg, QuadraticMap.polar_neg_right, ← sub_eq_add_neg] at hmap
  linear_combination hmap

/-- **The affine difference identity.** `Q (u − w) − Q (u' − w) = polar Q (u' − u) w + (Q u − Q u')`; the quadratic
part `Q w` cancels, leaving an affine function of `w`. This is what makes "same zero set ⟹ same coefficients" work. -/
theorem norm_diff_affine {u u' w : V} :
    Q (u - w) - Q (u' - w) = QuadraticMap.polar Q (u' - u) w + (Q u - Q u') := by
  rw [map_sub_eq, map_sub_eq, QuadraticMap.polar_sub_left]
  ring

/-- **★ The span-dim-2 geometric recovery core.** Let `W` be the plane, `a, b ∈ W`. If two vertices `u, u'` have the
**same isotropy profile over `W`** (`hprof`) and the common isotropic set `{w ∈ W : Q(u − w) = 0}` **affinely spans** `W`
(anchored at `w₀`: `Z − w₀` linearly spans `W`, `hspan`), then they have the **same exact Gram** to `{a, b}`:
`Q u = Q u'`, `polar u a = polar u' a`, `polar u b = polar u' b`. `d`-independent; no Gauss, no Witt. -/
theorem exactGram_of_sameWProfile {W : Submodule K V} {a b : V} (haW : a ∈ W) (hbW : b ∈ W)
    {u u' : V} (hprof : ∀ w ∈ W, (Q (u - w) = 0 ↔ Q (u' - w) = 0))
    {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀0 : Q (u - w₀) = 0)
    (hspan : Submodule.span K
        ((fun w => w - w₀) '' {w : V | w ∈ W ∧ Q (u - w) = 0}) = W) :
    Q u = Q u' ∧ QuadraticMap.polar Q u a = QuadraticMap.polar Q u' a
      ∧ QuadraticMap.polar Q u b = QuadraticMap.polar Q u' b := by
  -- The linear functional `f = polar Q (u' − u)`; goal is `f = 0` on `W`, plus `Q u = Q u'`.
  set f : V →ₗ[K] K := Q.polarBilin (u' - u) with hf
  have hfapp : ∀ x : V, f x = QuadraticMap.polar Q (u' - u) x := fun x => by
    rw [hf, polarBilin_apply_apply]
  -- `f` vanishes on the generators `w − w₀` for `w` in the common isotropic set.
  have hgen : ∀ x ∈ (fun w => w - w₀) '' {w : V | w ∈ W ∧ Q (u - w) = 0}, f x = 0 := by
    rintro _ ⟨w, ⟨hwW, hw0⟩, rfl⟩
    have hw0' : Q (u' - w) = 0 := (hprof w hwW).mp hw0
    have hw₀0' : Q (u' - w₀) = 0 := (hprof w₀ hw₀).mp hw₀0
    have dW : Q (u - w) - Q (u' - w) = f w + (Q u - Q u') := by
      rw [hfapp]; exact norm_diff_affine
    have dW₀ : Q (u - w₀) - Q (u' - w₀) = f w₀ + (Q u - Q u') := by
      rw [hfapp]; exact norm_diff_affine
    rw [hw0, hw0'] at dW
    rw [hw₀0, hw₀0'] at dW₀
    -- `f w + (Qu − Qu') = 0` and `f w₀ + (Qu − Qu') = 0` ⟹ `f (w − w₀) = f w − f w₀ = 0`.
    rw [map_sub]
    linear_combination dW₀ - dW
  -- `f` vanishes on all of `W` (spanning).
  have hfW : ∀ x ∈ W, f x = 0 := by
    intro x hx
    have hxspan : x ∈ Submodule.span K
        ((fun w => w - w₀) '' {w : V | w ∈ W ∧ Q (u - w) = 0}) := by rw [hspan]; exact hx
    refine Submodule.span_induction hgen ?_ ?_ ?_ hxspan
    · exact map_zero f
    · intro y z _ _ hy hz; rw [map_add, hy, hz, add_zero]
    · intro c y _ hy; rw [map_smul, hy, smul_zero]
  -- `Q u = Q u'` from the anchor (`w₀ ∈ W`, both isotropic).
  have hQ : Q u = Q u' := by
    have hw₀0' : Q (u' - w₀) = 0 := (hprof w₀ hw₀).mp hw₀0
    have d₀ : Q (u - w₀) - Q (u' - w₀) = f w₀ + (Q u - Q u') := by
      rw [hfapp]; exact norm_diff_affine
    rw [hw₀0, hw₀0', hfW w₀ hw₀] at d₀
    linear_combination -d₀
  -- The polar equalities from `f a = f b = 0` (`polar Q (u' − u) · = polar u' · − polar u ·`).
  refine ⟨hQ, ?_, ?_⟩
  · have hfa := hfW a haW
    rw [hfapp, QuadraticMap.polar_sub_left] at hfa
    linear_combination -hfa
  · have hfb := hfW b hbW
    rw [hfapp, QuadraticMap.polar_sub_left] at hfb
    linear_combination -hfb

end ChainDescent.SpanDim2Geom
