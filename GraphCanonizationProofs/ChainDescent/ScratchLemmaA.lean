import ChainDescent.CascadeAffine
import ChainDescent.GaussCount

/-!
# Lemma A (step-4 analytic crux) — the isotropic-incidence count in closed form.

Target: for a configuration whose difference `B`-Gram is **nondegenerate**, the count
`N = #{w : Q w = 0 ∧ ∀ j, Q (w − a j) = 0}` is an explicit function of the Gram, via:
  A1  linear conditions:  `Q w = 0 ⟹ (Q (w − a j)=0 ↔ polar Q w (a j) = Q (a j))`.
  A2  `V = U ⊕ Uᗮ` for `U = span{a j}` nondegenerate (Mathlib orthogonal complement).
  A3  unique `w₀ ∈ U` solving the system; solution set `= w₀ + Uᗮ`.
  A4  for `x ∈ Uᗮ`, `polar Q x w₀ = 0` ⟹ `Q (w₀ + x) = Q x + Q w₀` (LINEAR TERM VANISHES)
      ⟹ `N = #{x ∈ Uᗮ : Q|_{Uᗮ} x = −Q w₀}`.
  A5  `card_quadForm_eq` on `Q|_{Uᗮ}` (needs an orthogonal anisotropic basis).
  A6  `disc(Q|_{Uᗮ})`, `Q w₀` are Gram-functions ⟹ `N = f(Gram)`.

Witt-free throughout (the orthogonal split for nondegenerate `U` is elementary; the explicit count
avoids Witt cancellation). Develop here, port into a real module when stable.
-/

namespace ChainDescent
open QuadraticMap Finset

variable {p d : ℕ} [Fact p.Prime]

/-- **Lemma A, step A1 — the isotropic-incidence count rewrites with LINEAR conditions.** On the cone
`Q w = 0`, the condition `Q (w − a j) = 0` is equivalent to the affine-linear `polar Q w (a j) = Q (a j)`
(by the polar identity `polar Q w a = Q w + Q a − Q (w − a)`). So the count is over linear conditions. -/
theorem isoIncidence_eq_linearConds (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) :
    (Finset.univ.filter (fun w : Fin d → ZMod p =>
        Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
      = (Finset.univ.filter (fun w : Fin d → ZMod p =>
        Q w = 0 ∧ ∀ j, QuadraticMap.polar Q w (a j) = Q (a j))).card := by
  congr 1
  apply Finset.filter_congr
  intro w _
  apply and_congr_right
  intro hw
  apply forall_congr'
  intro j
  rw [polar_eq_of_sub, hw]
  constructor <;> intro h <;> linear_combination -h

/-- **Lemma A, step A4-core — `Q` is additive across a polar-orthogonal pair.** If `polar Q w x = 0` then
`Q (w + x) = Q w + Q x`. (This is what makes the affine level-set HOMOGENEOUS once `w₀ ⊥ Uᗮ`.) -/
theorem map_add_of_polar_zero (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {w x : Fin d → ZMod p} (h : QuadraticMap.polar Q w x = 0) :
    Q (w + x) = Q w + Q x := by
  have hp : Q (w + x) = Q w + Q x + QuadraticMap.polar Q w x := by
    simp only [QuadraticMap.polar]; ring
  rw [hp, h, add_zero]

/-- **Lemma A, step A3 — the linear-condition count is a count over the kernel coset.** Given any `w₀`
realizing the affine system (`polar Q w₀ (a j) = Q (a j)`), the solution set of the system is `w₀ + Uᗮ`
(`Uᗮ = {x | ∀ j, polar Q x (a j) = 0}`), so the cone-count over the system equals the count, over `Uᗮ`,
of `x` with `Q (w₀ + x) = 0`. Bijection `w ↦ w − w₀` (polar bilinearity). -/
theorem count_coset (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (w₀ : Fin d → ZMod p)
    (hw₀ : ∀ j, QuadraticMap.polar Q w₀ (a j) = Q (a j)) :
    (Finset.univ.filter (fun w : Fin d → ZMod p =>
        Q w = 0 ∧ ∀ j, QuadraticMap.polar Q w (a j) = Q (a j))).card
      = (Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q (w₀ + x) = 0)).card := by
  apply Finset.card_bij' (fun w _ => w - w₀) (fun x _ => w₀ + x)
  · rintro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine ⟨fun j => ?_, ?_⟩
    · rw [QuadraticMap.polar_sub_left, hw.2 j, hw₀ j, sub_self]
    · rw [add_sub_cancel]; exact hw.1
  · rintro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨hx.2, fun j => ?_⟩
    rw [QuadraticMap.polar_add_left, hw₀ j, hx.1 j, add_zero]
  · rintro w _; abel
  · rintro x _; abel

/-- **Lemma A, step A4-link — `w₀ ∈ span{a j}` is polar-orthogonal to `Uᗮ`.** If `w₀ = ∑ k, c k • a k` and
`x` is in `Uᗮ` (`∀ j, polar Q x (a j) = 0`), then `polar Q w₀ x = 0`. (Polar bilinearity, `polar_sum_right`.) -/
theorem polar_w0_perp (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : Fin m → ZMod p) {x : Fin d → ZMod p}
    (hx : ∀ j, QuadraticMap.polar Q x (a j) = 0) :
    QuadraticMap.polar Q (∑ k, c k • a k) x = 0 := by
  rw [QuadraticMap.polar_comm, ← polar_sum_right Q x Finset.univ c a]
  apply Finset.sum_eq_zero
  intro k _
  rw [hx k, mul_zero]

/-- **Lemma A, steps A1+A3+A4 combined — the count is a HOMOGENEOUS level-set count over `Uᗮ`.** Given a
spanning solution `w₀ = ∑ k, c k • a k` of the affine system (`polar Q w₀ (a j) = Q (a j)`), the
isotropic-incidence count equals the count, over `Uᗮ = {x | ∀ j, polar Q x (a j) = 0}`, of `x` with
`Q x = − Q w₀`. The linear term vanished (A4-link + A4-core), leaving a pure level-set of `Q|_{Uᗮ}` — exactly
`card_quadForm_eq`'s domain (step A5). The remaining open steps: A2/A3-existence (a spanning `w₀` exists when
the config Gram is nondegenerate) and A5/A6 (`card_quadForm_eq` + `disc` as a Gram-function). -/
theorem reduction_to_levelset (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : Fin m → ZMod p)
    (hw₀ : ∀ j, QuadraticMap.polar Q (∑ k, c k • a k) (a j) = Q (a j)) :
    (Finset.univ.filter (fun w : Fin d → ZMod p =>
        Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
      = (Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = - Q (∑ k, c k • a k))).card := by
  rw [isoIncidence_eq_linearConds, count_coset Q a (∑ k, c k • a k) hw₀]
  congr 1
  apply Finset.filter_congr
  intro x _
  apply and_congr_right
  intro hx
  rw [map_add_of_polar_zero Q (polar_w0_perp Q a c hx)]
  constructor <;> intro h <;> linear_combination h

end ChainDescent

#print axioms ChainDescent.isoIncidence_eq_linearConds
#print axioms ChainDescent.count_coset
#print axioms ChainDescent.reduction_to_levelset
