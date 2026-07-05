/-
# Discharging `NondegQuadricDeterminesForm` — the quadric Nullstellensatz (WIP)

**Target.** Replace the carried citation
`NondegQuadricDeterminesForm (p d) : p ≠ 2 → 4 ≤ d → ∀ Q R, Q.polarBilin.Nondegenerate →
  (∀ v, Q v = 0 ↔ R v = 0) → ∃ μ : (ZMod p)ˣ, ∀ v, R v = μ * Q v`
(RouteCFormAdapters.lean) with a full Lean proof. "A nondegenerate quadric determines its quadratic form up to a
nonzero scalar" — the projective Nullstellensatz for a nondegenerate quadric, scoped `p ≠ 2`, `d ≥ 4` (the exact TRUE
range: at `d = 3, q = 3` a conic's 4 points lie on a pencil, `vanishDim = 2`).

**The elementary proof path (probe-validated 2026-07-05, `nullstellensatz_path_probe.py` / `nsp.py`).** Avoids Witt
decomposition. Char `≠ 2` ⟹ identify a quadratic form with its polar bilinear form. For an anisotropic `y` and an
isotropic `x`, restrict `Q` to the line `x + t·y`: it is a quadratic in `t` with a root at `t = 0` (giving `x`) and a
second root giving another isotropic point `w`. Since `Z(Q) ⊆ Z(R)`, `R(w) = 0` too — and expanding that identity
yields the **line-restriction identity** `polar Q x y · R y = Q y · polar R x y` (for `polar Q x y ≠ 0`). Reading it as
a linear functional in `x`, it says `polar R (·) y = (R y / Q y) · polar Q (·) y` on the isotropic cone; since the
isotropic cone **spans** `V` (structural fact 1) the identity extends to all `x`, and comparing across anisotropic `y`
via **anisotropic B-connectivity** (structural fact 2) makes the ratio `R y / Q y` a global constant `μ`. Then
`polar R = μ · polar Q` ⟹ `R = μ · Q` (char `≠ 2`), with `μ ≠ 0` from the *reverse* cone inclusion (`Q y ≠ 0 ⟹ R y ≠ 0`).

**STATUS (2026-07-05 — BEGUN).**
- ✅ **The mathematical heart is LANDED, axiom-clean, ring-general:** `quad_lin_combo` (the `Q(c•x+d•y)` expansion) and
  **`nullstellensatz_core`** (the `w`-construction: `polar Q x y · (polar Q x y · R y − Q y · polar R x y) = 0` for
  isotropic `x`, any `y`, over ANY `CommRing`), plus the field-level cancellation `nullstellensatz_pointwise`
  (`polar Q x y ≠ 0 ⟹ polar Q x y · R y = Q y · polar R x y`). This is the genuinely non-obvious, reusable content.
- ◻ **REMAINING = two purely-structural finite-geometry facts** (Mathlib has neither; they are the honest hard core the
  opaque "Nullstellensatz" citation is now reduced to — each is elementary to STATE and standard, no longer a black box):
  1. **`IsotropicConeSpans`** — the isotropic vectors of a nondegenerate `Q` on `𝔽_q^d` (`q` odd, `d ≥ 4`, all four
     `VO^ε` types incl. the elliptic `d = 4` boundary) span `V`. Probe-confirmed rank `= d` for `VO^±_{4,6}(3,5,7)`.
  2. **`AnisotropicConnected`** — the anisotropic vectors are connected under the relation `polar Q z z' ≠ 0`
     (so the ratio `R z / Q z` is forced constant). Probe-confirmed connected for the same families.
  The assembly `IsotropicConeSpans → AnisotropicConnected → (the μ-scalar conclusion)` is elementary linear algebra
  (linear functional vanishing on a spanning set + a connectivity induction + `polar_self` to pass `polar R = μ polar Q`
  back to `R = μ Q`); it is the next build step. Until both structural facts are discharged, the citation stays carried.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned.
NOT in `build.sh` yet (WIP scratch).
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination

namespace ChainDescent.Nullstellensatz

open QuadraticMap

section Ring
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The two-vector expansion of a quadratic form.** `Q(c•x + d•y) = c²·Qx + d²·Qy + c·d·polar Q x y`. Pure
`QuadraticMap` API (`map_add`, `map_smul`, `polar_smul_{left,right}`). The workhorse for the `w`-construction. -/
theorem quad_lin_combo (Q : QuadraticForm K V) (c d : K) (x y : V) :
    Q (c • x + d • y) = c * c * Q x + d * d * Q y + c * d * QuadraticMap.polar Q x y := by
  rw [QuadraticMap.map_add (⇑Q) (c • x) (d • y), QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]; ring

/-- **The line-restriction core (ring-general).** For quadratic forms `Q, R` with `R` vanishing on the `Q`-cone
(`∀ v, Q v = 0 → R v = 0`) and any isotropic `x` (`Q x = 0`): the "second intersection" vector
`w = Q y • x − polar Q x y • y` is `Q`-isotropic, hence `R`-isotropic, and expanding `R(w) = 0` gives
`polar Q x y · (polar Q x y · R y − Q y · polar R x y) = 0` for every `y`. This is the elementary heart of the
quadric Nullstellensatz — no field, no finiteness, no dimension hypothesis. -/
theorem nullstellensatz_core (Q R : QuadraticForm K V)
    (hcone : ∀ v, Q v = 0 → R v = 0) {x y : V} (hx : Q x = 0) :
    QuadraticMap.polar Q x y *
      (QuadraticMap.polar Q x y * R y - Q y * QuadraticMap.polar R x y) = 0 := by
  -- `w := Q y • x + (−polar Q x y) • y` is Q-isotropic
  have hw : Q ((Q y) • x + (-(QuadraticMap.polar Q x y)) • y) = 0 := by
    rw [quad_lin_combo, hx]; ring
  -- hence R-isotropic; expand and use R x = 0
  have hRw := hcone _ hw
  rw [quad_lin_combo, hcone x hx] at hRw
  linear_combination hRw

end Ring

section Field
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The line-restriction identity (field version).** Cancelling the nonzero factor `polar Q x y` in
`nullstellensatz_core`: for isotropic `x` and `y` with `polar Q x y ≠ 0`,
`polar Q x y · R y = Q y · polar R x y`. Equivalently `polar R x y = (R y / Q y) · polar Q x y` — the linear
functional `polar R (·) y` equals `(R y / Q y) · polar Q (·) y` at isotropic `x`. -/
theorem nullstellensatz_pointwise (Q R : QuadraticForm K V)
    (hcone : ∀ v, Q v = 0 → R v = 0) {x y : V} (hx : Q x = 0)
    (hxy : QuadraticMap.polar Q x y ≠ 0) :
    QuadraticMap.polar Q x y * R y = Q y * QuadraticMap.polar R x y := by
  rcases mul_eq_zero.mp (nullstellensatz_core Q R hcone hx) with h0 | h0
  · exact absurd h0 hxy
  · exact sub_eq_zero.mp h0

/-- **The finish (char `≠ 2`): `polar R = μ · polar Q` ⟹ `R = μ · Q`.** Over a field of characteristic `≠ 2`, a
quadratic form is recovered from its polar bilinear form via `polar Q x x = 2 • Q x`; so if the polar forms are
proportional by `μ`, the quadratic forms are too. The last step of the assembly, once the structural facts have made
the ratio `μ` global. Elementary. -/
theorem form_eq_of_polar_eq_smul (Q R : QuadraticForm K V) (μ : K) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, QuadraticMap.polar R x y = μ * QuadraticMap.polar Q x y) (x : V) :
    R x = μ * Q x := by
  have hxx := h x x
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at hxx
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hxx
  exact mul_left_cancel₀ h2 (by linear_combination hxx)

/-! ### The assembly — the two structural facts imply the μ-scalar conclusion

`nullstellensatz_of_structural` reduces the full quadric Nullstellensatz to two **purely geometric** facts about the
nondegenerate `Q` (probe-validated for the `VO^ε` families, `nsp2.py`):
- `hspan` — for each anisotropic `y`, the **punctured isotropic cone** `{x | Q x = 0 ∧ polar Q x y ≠ 0}` spans `V`.
- `hlink` — the anisotropic vectors have **`polar`-diameter ≤ 2**: any two are joined through one anisotropic `z` with
  `polar Q y z ≠ 0` and `polar Q z y' ≠ 0` (replaces a general connectivity induction).
Everything else is elementary and proved here. This is the "isolate" capstone: the opaque Nullstellensatz is now
exactly these two finite-geometry facts + `nullstellensatz_core`. -/
theorem nullstellensatz_of_structural [Nontrivial V] (Q R : QuadraticForm K V)
    (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcone : ∀ v, Q v = 0 ↔ R v = 0)
    (hspan : ∀ y, Q y ≠ 0 →
      Submodule.span K {x | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} = ⊤)
    (hlink : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 →
      ∃ z, Q z ≠ 0 ∧ QuadraticMap.polar Q y z ≠ 0 ∧ QuadraticMap.polar Q z y' ≠ 0) :
    ∃ μ : Kˣ, ∀ v, R v = (μ : K) * Q v := by
  classical
  -- (0) an anisotropic vector exists (else `polarBilin Q = 0`, impossible for a nondegenerate form).
  have hEx : ∃ y, Q y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hz : QuadraticMap.polarBilin Q = 0 := by
      ext x y
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h]
    exact LinearMap.BilinForm.not_nondegenerate_zero K V (hz ▸ hQnd)
  -- (†) the per-anisotropic-`y` identity `Q y · polar R x y = R y · polar Q x y`, for ALL x
  -- (proved on the punctured cone via `nullstellensatz_core`, then extended by linearity over its span).
  have key : ∀ y, Q y ≠ 0 → ∀ x,
      Q y * QuadraticMap.polar R x y = R y * QuadraticMap.polar Q x y := by
    intro y hy x
    have hx : x ∈ Submodule.span K {x | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} := by
      rw [hspan y hy]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨hziso, hzp⟩ := hz
        have hc := nullstellensatz_core Q R (fun v hv => (hcone v).mp hv) hziso (y := y)
        have h0 := (mul_eq_zero.mp hc).resolve_left hzp
        linear_combination -h0
    | zero => simp
    | add a b _ _ pa pb =>
        simp only [QuadraticMap.polar_add_left]
        linear_combination pa + pb
    | smul c a _ pa =>
        simp only [QuadraticMap.polar_smul_left, smul_eq_mul]
        linear_combination c * pa
  -- (step) two `polar`-linked anisotropic vectors have the same ratio `R/Q`.
  have step : ∀ y z, Q y ≠ 0 → Q z ≠ 0 → QuadraticMap.polar Q y z ≠ 0 →
      R y * Q z = R z * Q y := by
    intro y z hy hz hpyz
    have e1 : Q z * QuadraticMap.polar R y z = R z * QuadraticMap.polar Q y z := key z hz y
    have e2 : Q y * QuadraticMap.polar R y z = R y * QuadraticMap.polar Q y z := by
      have h := key y hy z
      rwa [QuadraticMap.polar_comm R z y, QuadraticMap.polar_comm Q z y] at h
    have h3 : (R y * Q z) * QuadraticMap.polar Q y z = (R z * Q y) * QuadraticMap.polar Q y z := by
      linear_combination Q y * e1 - Q z * e2
    exact mul_right_cancel₀ hpyz h3
  -- (const) hence the ratio is constant across ALL anisotropic vectors (via the diameter-≤2 link).
  have const : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 → R y * Q y' = R y' * Q y := by
    intro y y' hy hy'
    obtain ⟨z, hz, hyz, hzy'⟩ := hlink y y' hy hy'
    have s1 : R y * Q z = R z * Q y := step y z hy hz hyz
    have s2 : R z * Q y' = R y' * Q z := step z y' hz hy' hzy'
    have h3 : (R y * Q y') * Q z = (R y' * Q y) * Q z := by
      linear_combination Q y' * s1 + Q y * s2
    exact mul_right_cancel₀ hz h3
  -- (finish) `μ := R y₀ / Q y₀`; `R v = μ Q v` by cases on `Q v = 0` (cone) vs `≠ 0` (constancy).
  obtain ⟨y0, hy0⟩ := hEx
  have hRy0 : R y0 ≠ 0 := fun h => hy0 ((hcone y0).mpr h)
  refine ⟨Units.mk0 (R y0 * (Q y0)⁻¹) (mul_ne_zero hRy0 (inv_ne_zero hy0)), fun v => ?_⟩
  simp only [Units.val_mk0]
  by_cases hv : Q v = 0
  · rw [(hcone v).mp hv, hv, mul_zero]
  · have hc := const v y0 hv hy0
    rw [show R y0 * (Q y0)⁻¹ * Q v = R y0 * Q v * (Q y0)⁻¹ by ring, ← hc,
      mul_assoc, mul_inv_cancel₀ hy0, mul_one]

end Field

end ChainDescent.Nullstellensatz
