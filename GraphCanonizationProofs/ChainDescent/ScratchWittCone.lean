/-
# Witt build, stages W0–W1 — reflections are isometries + cone transitivity (CellsAreOrbits route §7)

Discharges the carried `WittConeTransitive` input of `ScratchOrbitBaseCase` by building the orthogonal-reflection
engine and proving isometries are transitive on the nonzero isotropic vectors. This makes the depth-1 base case
(`depth1_isotropic_sphere_one_orbit`) **unconditional**.

* **W0 (foundation)** — the orthogonal reflection `τ_v` (built on Mathlib's `Module.reflection`) is an isometry
  (`refl_isometry`), packaged as a `Similitude` with multiplier `1` (`reflSim`); and `Q u = Q v ∧ Q(u−v) ≠ 0 ⟹
  τ_{u−v}(u) = v` (`refl_swap`). For isotropic `u, v` this is exactly the `polar Q u v ≠ 0` case of cone transitivity.
* **W1 (cone transitivity)** — `WittConeTransitive Q` for nondegenerate `Q`: the `polar ≠ 0` case via one reflection;
  the `polar = 0` case via two reflections through an intermediate isotropic vector (hyperbolic-partner construction).

Char ≠ 2 (`Invertible 2`) for W1 (reflections must be non-trivial); W0's isometry proof needs only `Q v ≠ 0`.
Axiom-clean target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchOrbitBaseCase
import Mathlib.LinearAlgebra.Reflection

namespace ChainDescent.WittCone

open ChainDescent.OrbitBaseCase QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The reflection functional `y ↦ polar Q y v / Q v`. Used as the `f` of `Module.reflection`. -/
noncomputable def reflFunc (Q : QuadraticForm K V) (v : V) : V →ₗ[K] K :=
  (Q v)⁻¹ • (Q.polarBilin.flip v)

theorem reflFunc_apply (Q : QuadraticForm K V) (v y : V) :
    reflFunc Q v y = (Q v)⁻¹ * QuadraticMap.polar Q y v := by
  simp only [reflFunc, LinearMap.smul_apply, LinearMap.flip_apply,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]

/-- `reflFunc Q v v = 2` — the hypothesis `Module.reflection` needs. -/
theorem reflFunc_self (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) :
    reflFunc Q v v = 2 := by
  rw [reflFunc_apply, QuadraticMap.polar_self, two_nsmul]
  rw [show (Q v)⁻¹ * (Q v + Q v) = 2 * ((Q v)⁻¹ * Q v) from by ring, inv_mul_cancel₀ hv, mul_one]

/-- The orthogonal reflection `τ_v : y ↦ y − (polar Q y v / Q v) • v`, as a linear equivalence. -/
noncomputable def refl (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) : V ≃ₗ[K] V :=
  Module.reflection (reflFunc_self Q v hv)

/-- General quadratic-difference expansion `Q (a − b) = Q a − polar Q a b + Q b`. -/
theorem map_sub' (Q : QuadraticForm K V) (a b : V) :
    Q (a - b) = Q a - QuadraticMap.polar Q a b + Q b := by
  rw [sub_eq_add_neg,
    show Q (a + -b) = Q a + Q (-b) + QuadraticMap.polar Q a (-b) from by rw [QuadraticMap.polar]; ring,
    QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
  ring

/-- **W0 — the reflection is an isometry.** `Q (τ_v y) = Q y`. Needs only `Q v ≠ 0`. -/
theorem refl_isometry (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) (y : V) :
    Q (refl Q v hv y) = Q y := by
  have qsub : Q (y - reflFunc Q v y • v)
      = Q y - reflFunc Q v y * QuadraticMap.polar Q y v
        + (reflFunc Q v y * reflFunc Q v y) * Q v := by
    rw [map_sub', QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
  rw [refl, Module.reflection_apply, qsub, reflFunc_apply]
  field_simp
  ring

/-- **W0 — the reflection as a `Similitude` (multiplier 1, i.e. an isometry).** -/
noncomputable def reflSim (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) : Similitude Q where
  toLinearEquiv := refl Q v hv
  mult := 1
  mult_ne := one_ne_zero
  map := fun x => by rw [refl_isometry, one_mul]

/-- **W0 — the swap lemma.** When `Q u = Q v` and `u − v` is anisotropic, the reflection in `u − v` sends `u ↦ v`.
For isotropic `u, v` this is precisely the `polar Q u v ≠ 0` case (`Q(u−v) = −polar Q u v`). -/
theorem refl_swap (Q : QuadraticForm K V) {u v : V} (hQ : Q u = Q v) (hne : Q (u - v) ≠ 0) :
    refl Q (u - v) hne u = v := by
  have hpolar : QuadraticMap.polar Q u (u - v) = Q (u - v) := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_self, map_sub', two_nsmul, hQ]; ring
  have hcoef : (Q (u - v))⁻¹ * QuadraticMap.polar Q u (u - v) = 1 := by
    rw [hpolar]; exact inv_mul_cancel₀ hne
  rw [refl, Module.reflection_apply, reflFunc_apply, hcoef, one_smul]
  abel

/-- Composition of similitudes (multipliers multiply); used to chain two reflections. -/
noncomputable def simComp {Q : QuadraticForm K V} (g h : Similitude Q) : Similitude Q where
  toLinearEquiv := h.toLinearEquiv.trans g.toLinearEquiv
  mult := g.mult * h.mult
  mult_ne := mul_ne_zero g.mult_ne h.mult_ne
  map := fun x => by
    rw [LinearEquiv.trans_apply, g.map, h.map]; ring

/-- **W1, case `polar ≠ 0`.** Two nonzero isotropic vectors with `polar Q u u' ≠ 0` are related by a single
reflection (`u − u'` is anisotropic). -/
theorem cone_case_polar_ne {Q : QuadraticForm K V} {u u' : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (hpolar : QuadraticMap.polar Q u u' ≠ 0) :
    ∃ g : Similitude Q, g.mult = 1 ∧ g.toLinearEquiv u = u' := by
  have hQ : Q u = Q u' := by rw [hu, hu']
  have hne : Q (u - u') ≠ 0 := by
    rw [map_sub', hu, hu']; simp only [zero_sub, add_zero]; exact neg_ne_zero.mpr hpolar
  exact ⟨reflSim Q (u - u') hne, rfl, refl_swap Q hQ hne⟩

/-- **The hyperbolic-partner lemma.** A nonzero isotropic vector has an isotropic partner `f` with `polar Q u f = 1`
(nondegeneracy supplies a non-orthogonal `z`; rescale and isotropize). The key tool for the residual `IsotropicPairing`. -/
theorem exists_hyperbolic_partner {Q : QuadraticForm K V}
    (hnd : ∀ x : V, x ≠ 0 → ∃ y, QuadraticMap.polar Q x y ≠ 0)
    {u : V} (hu0 : u ≠ 0) (hu : Q u = 0) :
    ∃ f : V, Q f = 0 ∧ QuadraticMap.polar Q u f = 1 := by
  obtain ⟨z, hz⟩ := hnd u hu0
  set z1 := (QuadraticMap.polar Q u z)⁻¹ • z with hz1
  have hpz1 : QuadraticMap.polar Q u z1 = 1 := by
    rw [hz1, QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hz]
  clear_value z1
  refine ⟨z1 - (Q z1) • u, ?_, ?_⟩
  · rw [map_sub', QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul,
      QuadraticMap.polar_comm Q z1 u, hpz1, hu]
    ring
  · rw [QuadraticMap.polar_sub_right, hpz1, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hu]
    simp

/-- **The residual existence predicate.** For any two nonzero isotropic `u, u'`, an isotropic `w` non-orthogonal to
both. This is the *only* remaining content of `WittConeTransitive` after the reflection engine — a concrete vector
existence statement (no isometries), strictly smaller than cone-transitivity itself. -/
def IsotropicPairing (Q : QuadraticForm K V) : Prop :=
  ∀ u u' : V, u ≠ 0 → u' ≠ 0 → Q u = 0 → Q u' = 0 →
    ∃ w : V, Q w = 0 ∧ QuadraticMap.polar Q u w ≠ 0 ∧ QuadraticMap.polar Q u' w ≠ 0

/-- **W1 — the reduction.** Cone transitivity follows from `IsotropicPairing`: the `polar ≠ 0` case is one reflection
(`cone_case_polar_ne`); the `polar = 0` case routes `u → w → u'` through the pairing vector `w` by two reflections
(`refl_swap` twice, composed by `simComp`). So `WittConeTransitive Q` is reduced to the concrete `IsotropicPairing Q`. -/
theorem wittConeTransitive_of_pairing {Q : QuadraticForm K V}
    (hP : IsotropicPairing Q) : WittConeTransitive Q := by
  intro u u' hu0 hu'0 hu hu'
  by_cases hpolar : QuadraticMap.polar Q u u' = 0
  · obtain ⟨w, hw, hpuw, hpu'w⟩ := hP u u' hu0 hu'0 hu hu'
    have hQuw : Q u = Q w := by rw [hu, hw]
    have hne1 : Q (u - w) ≠ 0 := by
      rw [map_sub', hu, hw]; simp only [zero_sub, add_zero]; exact neg_ne_zero.mpr hpuw
    have hQwu' : Q w = Q u' := by rw [hw, hu']
    have hpwu' : QuadraticMap.polar Q w u' ≠ 0 := by
      rw [QuadraticMap.polar_comm Q w u']; exact hpu'w
    have hne2 : Q (w - u') ≠ 0 := by
      rw [map_sub', hw, hu']; simp only [zero_sub, add_zero]; exact neg_ne_zero.mpr hpwu'
    refine ⟨simComp (reflSim Q (w - u') hne2) (reflSim Q (u - w) hne1), ?_, ?_⟩
    · show (1 : K) * 1 = 1; ring
    · rw [simComp, LinearEquiv.trans_apply,
        show (reflSim Q (u - w) hne1).toLinearEquiv u = w from refl_swap Q hQuw hne1]
      exact refl_swap Q hQwu' hne2
  · exact cone_case_polar_ne hu hu' hpolar

end ChainDescent.WittCone
