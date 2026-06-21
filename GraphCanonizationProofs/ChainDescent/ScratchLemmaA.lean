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
open scoped Matrix

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

/-- **Lemma A, step A-M2 — a spanning `w₀` exists when the config Gram is nondegenerate.** If the Gram matrix
`G i j = polar Q (a i) (a j)` is invertible (`IsUnit G.det`), then `c := (Q ∘ a) ᵥ* G⁻¹` realizes the affine
system: `w₀ = ∑ k, c k • a k` satisfies `polar Q w₀ (a j) = Q (a j)` for all `j`. Discharges the hypothesis of
`reduction_to_levelset`, so the count is unconditionally the homogeneous level-set on nondegenerate configs. -/
theorem spanning_w0_exists (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) (ZMod p)).det) :
    ∃ c : Fin m → ZMod p, ∀ j, QuadraticMap.polar Q (∑ k, c k • a k) (a j) = Q (a j) := by
  set G : Matrix (Fin m) (Fin m) (ZMod p) :=
    Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) with hGdef
  refine ⟨(fun j => Q (a j)) ᵥ* G⁻¹, fun j => ?_⟩
  set c : Fin m → ZMod p := (fun j => Q (a j)) ᵥ* G⁻¹ with hcdef
  have hcG : c ᵥ* G = (fun j => Q (a j)) := by
    rw [hcdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hG, Matrix.vecMul_one]
  have hexp : QuadraticMap.polar Q (∑ k, c k • a k) (a j) = (c ᵥ* G) j := by
    rw [QuadraticMap.polar_comm, ← polar_sum_right Q (a j) Finset.univ c a]
    simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [QuadraticMap.polar_comm Q (a j) (a k)])
  rw [hexp, hcG]

/-- **Lemma A, A-M1 ∘ A-M2 — the reduction, unconditional on nondegenerate configs.** If the config Gram matrix
is invertible, the isotropic-incidence count is the HOMOGENEOUS level-set count `#{x ∈ Uᗮ : Q x = − Q w₀}` for the
explicit `w₀ = ∑ k, c k • a k` (`c` from `spanning_w0_exists`). The remaining steps A-M3/A-M4 evaluate this
level-set via `card_quadForm_eq` on `Q|_{Uᗮ}` and express it as a function of the Gram. -/
theorem reduction_to_levelset_nondeg (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) (ZMod p)).det) :
    ∃ c : Fin m → ZMod p,
      (Finset.univ.filter (fun w : Fin d → ZMod p =>
          Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
        = (Finset.univ.filter (fun x : Fin d → ZMod p =>
          (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = - Q (∑ k, c k • a k))).card := by
  obtain ⟨c, hc⟩ := spanning_w0_exists Q a hG
  exact ⟨c, reduction_to_levelset Q a c hc⟩

open scoped Classical in
/-- **Lemma A, step A-M3 increment 1 — the Fourier expansion of the level-set count over the FULL space `V`**
(Route B, §10.10). The level-set count `#{x : (∀ j, polar Q x (a j)=0) ∧ Q x = c}`, scaled by `q^{m+1}`, is a
double character sum indexed by `Option (Fin m)`: the `none` slot carries the quadratic condition `Q x = c`
(dual weight `r none`), the `some j` slots carry the `m` linear conditions `polar Q x (a j)=0` (dual weights
`r (some j)`). The `m` linear duals collapse, by bilinearity (`polar_sum_right`), into a single linear term
`polar Q x (∑ j, r (some j) • a j)`. This never forms the subspace `Uᗮ` — the inner sum is over all of `V`,
ready for the D1 / `linearMap` split (increment 2). -/
theorem levelset_fourier (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : ZMod p)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (p : R') ^ (m + 1)
    = ∑ r : Option (Fin m) → ZMod p,
        ψ (-(r none * c)) * ∑ x : Fin d → ZMod p,
          ψ (r none * Q x + QuadraticMap.polar Q x (∑ j, r (some j) • a j)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  let f : Option (Fin m) → (Fin d → ZMod p) → ZMod p :=
    fun k x => k.elim (Q x) (fun j => QuadraticMap.polar Q x (a j))
  let cc : Option (Fin m) → ZMod p := fun k => k.elim c (fun _ => 0)
  have hcard := countk_eq_sum_charsum (F := ZMod p) (R' := R') hψ f cc
  rw [ZMod.card, Fintype.card_option, Fintype.card_fin] at hcard
  have hfilter : (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ k, f k x = cc k))
      = Finset.univ.filter (fun x : Fin d → ZMod p =>
          (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro h; exact ⟨fun j => h (some j), h none⟩
    · rintro ⟨h1, h2⟩ k; cases k with
      | none => exact h2
      | some j => exact h1 j
  rw [hfilter] at hcard
  rw [hcard]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  · congr 2
    rw [Fintype.sum_option]
    simp only [cc, Option.elim_none, Option.elim_some, mul_zero, Finset.sum_const_zero, add_zero]
  · apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fintype.sum_option]
    simp only [f, Option.elim_none, Option.elim_some]
    rw [polar_sum_right Q x Finset.univ (fun j => r (some j)) a]

open scoped Classical in
/-- **Lemma A, step A-M3 increment 2a — reindex the dual sum into `(s, ρ)` product form.** Splits the
`Option (Fin m) → F` dual variable into the quadratic dual `s = r none` and the linear duals `ρ = r ∘ some`
(via `Equiv.piOptionEquivProd`), so the inner sum is `∑_x ψ(s·Q x + polar Q x (∑ⱼ ρⱼ•aⱼ))` — ready for the
`s = 0` (`linearMap` boundary) vs `s ≠ 0` (D1 `sum_addChar_quadForm_linear`) split of increment 2b. -/
theorem levelset_fourier_prod (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : ZMod p)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (p : R') ^ (m + 1)
    = ∑ s : ZMod p, ∑ ρ : Fin m → ZMod p,
        ψ (-(s * c)) * ∑ x : Fin d → ZMod p,
          ψ (s * Q x + QuadraticMap.polar Q x (∑ j, ρ j • a j)) := by
  rw [levelset_fourier Q a c hψ,
    ← Equiv.sum_comp (Equiv.piOptionEquivProd (α := Fin m) (β := fun _ => ZMod p)).symm
      (fun r : Option (Fin m) → ZMod p => ψ (-(r none * c)) * ∑ x : Fin d → ZMod p,
        ψ (r none * Q x + QuadraticMap.polar Q x (∑ j, r (some j) • a j))),
    Fintype.sum_prod_type]
  rfl

open scoped Classical in
/-- **Lemma A, step A-M3 increment 2b — the `s`-split (D1 on the bulk).** Split the quadratic dual `∑_s` at `s = 0`.
The `s = 0` boundary leaves the linear sum `∑_ρ ∑_x ψ(polar Q x (∑ⱼ ρⱼ•aⱼ))` (collapsed in 2c via
`sum_addChar_linearMap` + config-vector independence, where nondegeneracy enters). The `s ≠ 0` bulk evaluates via
**D1 `sum_addChar_quadForm_linear`** (each `s` as a unit `Units.mk0`): the inner `x`-sum becomes
`ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))·∑_x ψ(s·Q x)`, factoring the config-Gram piece (the `ρ`-sum, → 2c) from the scaled global Gauss
sum `∑_x ψ(s·Q x)`. -/
theorem levelset_fourier_split (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : ZMod p)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (p : R') ^ (m + 1)
    = (∑ ρ : Fin m → ZMod p, ∑ x : Fin d → ZMod p,
          ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
      + ∑ s ∈ Finset.univ.erase (0 : ZMod p), ∑ ρ : Fin m → ZMod p,
          ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x)) := by
  rw [levelset_fourier_prod Q a c hψ,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
  congr 1
  · apply Finset.sum_congr rfl
    intro ρ _
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, zero_add]
  · apply Finset.sum_congr rfl
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    apply Finset.sum_congr rfl
    intro ρ _
    have hD1 := sum_addChar_quadForm_linear ψ Q (Units.mk0 s hs0) (∑ j, ρ j • a j)
    rw [Units.val_mk0] at hD1
    rw [hD1]

open scoped Classical in
/-- **Lemma A, step A-M3 increment 2c — the `s = 0` boundary collapses to `q^d`.** The boundary sum
`∑_ρ ∑_x ψ(polar Q x (∑ⱼ ρⱼ•aⱼ))` equals `|V| = q^d`. Pointwise (`sum_addChar_linearMap`, with the linear functional
`φ_ρ = (polarBilin Q).flip (∑ⱼ ρⱼ•aⱼ)`), the inner `x`-sum is `|V|·[φ_ρ = 0]`; and `φ_ρ = 0 ⟺ ρ = 0` using **only the
config-Gram nondegeneracy** (`IsUnit G.det`): evaluating `φ_ρ` at `aᵢ` gives `(G *ᵥ ρ)ᵢ = 0`, and `G` invertible forces
`ρ = 0`. So exactly `ρ = 0` survives, contributing `|V|`. (No full `Q`-nondegeneracy needed — the config Gram suffices.) -/
theorem s0_boundary_collapse (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    (∑ ρ : Fin m → ZMod p, ∑ x : Fin d → ZMod p,
        ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
      = (Fintype.card (Fin d → ZMod p) : R') := by
  classical
  set G : Matrix (Fin m) (Fin m) (ZMod p) :=
    Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) with hGdef
  have hpt : ∀ ρ : Fin m → ZMod p,
      (∑ x : Fin d → ZMod p, ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
        = if (QuadraticMap.polarBilin Q).flip (∑ j, ρ j • a j) = 0
            then (Fintype.card (Fin d → ZMod p) : R') else 0 := by
    intro ρ
    rw [Finset.sum_congr rfl (fun x _ => by
      rw [show QuadraticMap.polar Q x (∑ j, ρ j • a j)
          = (QuadraticMap.polarBilin Q).flip (∑ j, ρ j • a j) x from by
        rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]])]
    exact sum_addChar_linearMap hψ _
  have hcond : ∀ ρ : Fin m → ZMod p,
      ((QuadraticMap.polarBilin Q).flip (∑ j, ρ j • a j) = 0) ↔ ρ = 0 := by
    intro ρ
    constructor
    · intro h
      have hGρ : G *ᵥ ρ = 0 := by
        funext i
        have hi0 := LinearMap.congr_fun h (a i)
        rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at hi0
        rw [← polar_sum_right Q (a i) Finset.univ ρ a] at hi0
        rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
        rw [show (∑ j, G i j * ρ j) = ∑ j, ρ j * QuadraticMap.polar Q (a i) (a j) from
          Finset.sum_congr rfl (fun j _ => by rw [hGdef, Matrix.of_apply]; ring)]
        exact hi0
      have hρ : ρ = G⁻¹ *ᵥ (G *ᵥ ρ) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]
      rw [hρ, hGρ, Matrix.mulVec_zero]
    · intro h
      subst h
      rw [show (∑ j, (0 : Fin m → ZMod p) j • a j) = 0 from by simp, map_zero]
  rw [Finset.sum_congr rfl (fun ρ _ => hpt ρ),
    Finset.sum_congr rfl (fun ρ _ => if_congr (hcond ρ) rfl rfl),
    Finset.sum_ite_eq' Finset.univ (0 : Fin m → ZMod p)
      (fun _ => (Fintype.card (Fin d → ZMod p) : R'))]
  simp

open scoped Classical in
/-- **Lemma A, step A-M3 ASSEMBLED — the level-set count in closed form up to the two Gauss sums (Route B).** For a
nondegenerate config Gram (`IsUnit G.det`), the level-set count satisfies
`count·q^{m+1} = |V| + ∑_{s≠0} ψ(−s·c)·(ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))·∑_x ψ(s·Q x)) summed over ρ`. The `|V|` is the `s=0`
boundary (increment 2c); the bulk is the D1-evaluated `s≠0` part (increment 2b). **All that remains for Lemma A
(A-M4)** is to evaluate the two Gauss sums: the global `∑_x ψ(s·Q x) = χ(s)^d·W` (scaling, fixed basis of `Q`) and
the config-Gram sum `∑_ρ ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))` (Gauss sum of the config form `QR = Q.comp (∑ⱼ ρⱼ•aⱼ)` on `Fin m → F`),
then collapse to the §10.10 `N(m, det G, c_lev)` table. -/
theorem levelset_count_eq (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {m : ℕ} (a : Fin m → (Fin d → ZMod p)) (c : ZMod p)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (p : R') ^ (m + 1)
    = (Fintype.card (Fin d → ZMod p) : R')
      + ∑ s ∈ Finset.univ.erase (0 : ZMod p), ∑ ρ : Fin m → ZMod p,
          ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x)) := by
  rw [levelset_fourier_split Q a c hψ, s0_boundary_collapse Q a hG hψ]

end ChainDescent

#print axioms ChainDescent.isoIncidence_eq_linearConds
#print axioms ChainDescent.count_coset
#print axioms ChainDescent.reduction_to_levelset
#print axioms ChainDescent.spanning_w0_exists
#print axioms ChainDescent.reduction_to_levelset_nondeg
#print axioms ChainDescent.levelset_fourier
#print axioms ChainDescent.levelset_fourier_prod
#print axioms ChainDescent.levelset_fourier_split
#print axioms ChainDescent.s0_boundary_collapse
#print axioms ChainDescent.levelset_count_eq
