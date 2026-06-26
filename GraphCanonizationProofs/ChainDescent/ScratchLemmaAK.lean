/-
# Lemma A, abstract-`K` lift (concern #4 — bridge lift, the analytic core).

The field-generalized version of `ScratchLemmaA`: the isotropic-incidence count in closed form, over an abstract
finite field `K` (replacing `ZMod p`) with `V = Fin d → K`. The original proof used no `ZMod p`-specific fact beyond
`polar_eq_of_sub` (now `ScratchFieldGen.polar_eq_of_subK`) and `ZMod.card`/`NeZero p` (now `Fintype.card K`); the Gauss
toolkit (`GaussCount`) is already abstract over a finite field, so the lift is a mechanical typeclass swap
`ZMod p ↦ K`, `(p : R') ↦ (Fintype.card K : R')`.

Mirrors `ScratchLemmaA` decl-for-decl. Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build.
-/
import ChainDescent.ScratchFieldGen

namespace ChainDescent
open QuadraticMap Finset
open scoped Matrix

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-- **A1 (K)** — isotropic-incidence count rewrites with LINEAR conditions. -/
theorem isoIncidence_eq_linearCondsK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) :
    (Finset.univ.filter (fun w : Fin d → K =>
        Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
      = (Finset.univ.filter (fun w : Fin d → K =>
        Q w = 0 ∧ ∀ j, QuadraticMap.polar Q w (a j) = Q (a j))).card := by
  congr 1
  apply Finset.filter_congr
  intro w _
  apply and_congr_right
  intro hw
  apply forall_congr'
  intro j
  rw [polar_eq_of_subK, hw]
  constructor <;> intro h <;> linear_combination -h

omit [Fintype K] [DecidableEq K] in
/-- **A4-core (K)** — `Q` is additive across a polar-orthogonal pair. -/
theorem map_add_of_polar_zeroK (Q : QuadraticForm K (Fin d → K))
    {w x : Fin d → K} (h : QuadraticMap.polar Q w x = 0) :
    Q (w + x) = Q w + Q x := by
  have hp : Q (w + x) = Q w + Q x + QuadraticMap.polar Q w x := by
    simp only [QuadraticMap.polar]; ring
  rw [hp, h, add_zero]

/-- **A3 (K)** — the linear-condition count is a count over the kernel coset. -/
theorem count_cosetK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (w₀ : Fin d → K)
    (hw₀ : ∀ j, QuadraticMap.polar Q w₀ (a j) = Q (a j)) :
    (Finset.univ.filter (fun w : Fin d → K =>
        Q w = 0 ∧ ∀ j, QuadraticMap.polar Q w (a j) = Q (a j))).card
      = (Finset.univ.filter (fun x : Fin d → K =>
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

omit [Fintype K] [DecidableEq K] in
/-- **A4-link (K)** — `w₀ ∈ span{a j}` is polar-orthogonal to `Uᗮ`. -/
theorem polar_w0_perpK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : Fin m → K) {x : Fin d → K}
    (hx : ∀ j, QuadraticMap.polar Q x (a j) = 0) :
    QuadraticMap.polar Q (∑ k, c k • a k) x = 0 := by
  rw [QuadraticMap.polar_comm, ← polar_sum_right Q x Finset.univ c a]
  apply Finset.sum_eq_zero
  intro k _
  rw [hx k, mul_zero]

/-- **A1+A3+A4 (K)** — the count is a HOMOGENEOUS level-set count over `Uᗮ`. -/
theorem reduction_to_levelsetK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : Fin m → K)
    (hw₀ : ∀ j, QuadraticMap.polar Q (∑ k, c k • a k) (a j) = Q (a j)) :
    (Finset.univ.filter (fun w : Fin d → K =>
        Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
      = (Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = - Q (∑ k, c k • a k))).card := by
  rw [isoIncidence_eq_linearCondsK, count_cosetK Q a (∑ k, c k • a k) hw₀]
  congr 1
  apply Finset.filter_congr
  intro x _
  apply and_congr_right
  intro hx
  rw [map_add_of_polar_zeroK Q (polar_w0_perpK Q a c hx)]
  constructor <;> intro h <;> linear_combination h

omit [Fintype K] [DecidableEq K] in
/-- **A-M2 (K)** — a spanning `w₀` exists when the config Gram is nondegenerate. -/
theorem spanning_w0_existsK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det) :
    ∃ c : Fin m → K, ∀ j, QuadraticMap.polar Q (∑ k, c k • a k) (a j) = Q (a j) := by
  set G : Matrix (Fin m) (Fin m) K :=
    Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) with hGdef
  refine ⟨(fun j => Q (a j)) ᵥ* G⁻¹, fun j => ?_⟩
  set c : Fin m → K := (fun j => Q (a j)) ᵥ* G⁻¹ with hcdef
  have hcG : c ᵥ* G = (fun j => Q (a j)) := by
    rw [hcdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hG, Matrix.vecMul_one]
  have hexp : QuadraticMap.polar Q (∑ k, c k • a k) (a j) = (c ᵥ* G) j := by
    rw [QuadraticMap.polar_comm, ← polar_sum_right Q (a j) Finset.univ c a]
    simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [QuadraticMap.polar_comm Q (a j) (a k)])
  rw [hexp, hcG]

/-- **A-M1 ∘ A-M2 (K)** — the reduction, unconditional on nondegenerate configs. -/
theorem reduction_to_levelset_nondegK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det) :
    ∃ c : Fin m → K,
      (Finset.univ.filter (fun w : Fin d → K =>
          Q w = 0 ∧ ∀ j, Q (w - a j) = 0)).card
        = (Finset.univ.filter (fun x : Fin d → K =>
          (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = - Q (∑ k, c k • a k))).card := by
  obtain ⟨c, hc⟩ := spanning_w0_existsK Q a hG
  exact ⟨c, reduction_to_levelsetK Q a c hc⟩

open scoped Classical in
/-- **A-M3 inc 1 (K)** — the Fourier expansion of the level-set count over the FULL space `V`. -/
theorem levelset_fourierK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1)
    = ∑ r : Option (Fin m) → K,
        ψ (-(r none * c)) * ∑ x : Fin d → K,
          ψ (r none * Q x + QuadraticMap.polar Q x (∑ j, r (some j) • a j)) := by
  classical
  let f : Option (Fin m) → (Fin d → K) → K :=
    fun k x => k.elim (Q x) (fun j => QuadraticMap.polar Q x (a j))
  let cc : Option (Fin m) → K := fun k => k.elim c (fun _ => 0)
  have hcard := countk_eq_sum_charsum (F := K) (R' := R') hψ f cc
  rw [Fintype.card_option, Fintype.card_fin] at hcard
  have hfilter : (Finset.univ.filter (fun x : Fin d → K => ∀ k, f k x = cc k))
      = Finset.univ.filter (fun x : Fin d → K =>
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
/-- **A-M3 inc 2a (K)** — reindex the dual sum into `(s, ρ)` product form. -/
theorem levelset_fourier_prodK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1)
    = ∑ s : K, ∑ ρ : Fin m → K,
        ψ (-(s * c)) * ∑ x : Fin d → K,
          ψ (s * Q x + QuadraticMap.polar Q x (∑ j, ρ j • a j)) := by
  rw [levelset_fourierK Q a c hψ,
    ← Equiv.sum_comp (Equiv.piOptionEquivProd (α := Fin m) (β := fun _ => K)).symm
      (fun r : Option (Fin m) → K => ψ (-(r none * c)) * ∑ x : Fin d → K,
        ψ (r none * Q x + QuadraticMap.polar Q x (∑ j, r (some j) • a j))),
    Fintype.sum_prod_type]
  rfl

open scoped Classical in
/-- **A-M3 inc 2b (K)** — the `s`-split (D1 on the bulk). -/
theorem levelset_fourier_splitK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : K)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1)
    = (∑ ρ : Fin m → K, ∑ x : Fin d → K,
          ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
      + ∑ s ∈ Finset.univ.erase (0 : K), ∑ ρ : Fin m → K,
          ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → K, ψ (s * Q x)) := by
  rw [levelset_fourier_prodK Q a c hψ,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : K))]
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
/-- **A-M3 inc 2c (K)** — the `s = 0` boundary collapses to `q^d`. -/
theorem s0_boundary_collapseK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    (∑ ρ : Fin m → K, ∑ x : Fin d → K,
        ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
      = (Fintype.card (Fin d → K) : R') := by
  classical
  set G : Matrix (Fin m) (Fin m) K :=
    Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) with hGdef
  have hpt : ∀ ρ : Fin m → K,
      (∑ x : Fin d → K, ψ (QuadraticMap.polar Q x (∑ j, ρ j • a j)))
        = if (QuadraticMap.polarBilin Q).flip (∑ j, ρ j • a j) = 0
            then (Fintype.card (Fin d → K) : R') else 0 := by
    intro ρ
    rw [Finset.sum_congr rfl (fun x _ => by
      rw [show QuadraticMap.polar Q x (∑ j, ρ j • a j)
          = (QuadraticMap.polarBilin Q).flip (∑ j, ρ j • a j) x from by
        rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]])]
    exact sum_addChar_linearMap hψ _
  have hcond : ∀ ρ : Fin m → K,
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
      rw [show (∑ j, (0 : Fin m → K) j • a j) = 0 from by simp, map_zero]
  rw [Finset.sum_congr rfl (fun ρ _ => hpt ρ),
    Finset.sum_congr rfl (fun ρ _ => if_congr (hcond ρ) rfl rfl),
    Finset.sum_ite_eq' Finset.univ (0 : Fin m → K)
      (fun _ => (Fintype.card (Fin d → K) : R'))]
  simp

open scoped Classical in
/-- **A-M3 ASSEMBLED (K)** — the level-set count in closed form up to the two Gauss sums. -/
theorem levelset_count_eqK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (c : K)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R')
      * (Fintype.card K : R') ^ (m + 1)
    = (Fintype.card (Fin d → K) : R')
      + ∑ s ∈ Finset.univ.erase (0 : K), ∑ ρ : Fin m → K,
          ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → K, ψ (s * Q x)) := by
  rw [levelset_fourier_splitK Q a c hψ, s0_boundary_collapseK Q a hG hψ]

/-! ### A-M4a (K) — the config quadratic form `QR` and its Gram. -/

/-- **The config quadratic form (K)** `QR(ρ) = Q(∑ⱼ ρⱼ•aⱼ)` on `Fin m → K`. -/
noncomputable def configFormK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) : QuadraticForm K (Fin m → K) :=
  Q.comp (Fintype.linearCombination K a)

omit [Fintype K] [DecidableEq K] in
@[simp] theorem configFormK_apply (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (ρ : Fin m → K) :
    configFormK Q a ρ = Q (∑ j, ρ j • a j) := by
  rw [configFormK, QuadraticMap.comp_apply, Fintype.linearCombination_apply]

omit [Fintype K] [DecidableEq K] in
theorem linComb_singleK {m : ℕ} (a : Fin m → (Fin d → K)) (i : Fin m) :
    Fintype.linearCombination K a (Pi.single i 1) = a i := by
  rw [Fintype.linearCombination_apply_single, one_smul]

omit [Fintype K] [DecidableEq K] in
/-- The polar of the config form transports along `L`. -/
theorem polar_configFormK (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (ρ σ : Fin m → K) :
    QuadraticMap.polar (configFormK Q a) ρ σ
      = QuadraticMap.polar Q (Fintype.linearCombination K a ρ)
          (Fintype.linearCombination K a σ) := by
  simp only [QuadraticMap.polar, configFormK, QuadraticMap.comp_apply, map_add]

omit [Fintype K] [DecidableEq K] in
/-- **The config form's Gram = the config Gram `G`** (K). -/
theorem polar_configFormK_single (Q : QuadraticForm K (Fin d → K))
    {m : ℕ} (a : Fin m → (Fin d → K)) (i j : Fin m) :
    QuadraticMap.polar (configFormK Q a) (Pi.single i 1) (Pi.single j 1)
      = QuadraticMap.polar Q (a i) (a j) := by
  rw [polar_configFormK, linComb_singleK, linComb_singleK]

open scoped Classical in
omit [Fintype K] [DecidableEq K] in
/-- **A-M4a gap-2 (K)** — the config form's associated bilinear is nondegenerate. -/
theorem configFormK_nondegenerate (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)]
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det) :
    (QuadraticMap.associated (R := K) (configFormK Q a)).Nondegenerate := by
  set G : Matrix (Fin m) (Fin m) K :=
    Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) with hGdef
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticForm.associated_isSymm K (configFormK Q a)).isRefl]
  intro x hx
  have hGx : G *ᵥ x = 0 := by
    funext i
    have hp : QuadraticMap.polar (configFormK Q a) x (Pi.single i 1) = 0 := by
      have hpb : QuadraticMap.polar (configFormK Q a) x (Pi.single i 1)
          = 2 • (QuadraticMap.associated (R := K) (configFormK Q a) x (Pi.single i 1)) := by
        rw [← QuadraticMap.polarBilin_apply_apply, ← two_nsmul_associated (S := K)]
        simp only [LinearMap.smul_apply]
      rw [hpb, hx (Pi.single i 1), smul_zero]
    rw [polar_configFormK, linComb_singleK] at hp
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
    rw [show (∑ j, G i j * x j)
        = QuadraticMap.polar Q (Fintype.linearCombination K a x) (a i) from ?_]
    · exact hp
    · rw [Fintype.linearCombination_apply, QuadraticMap.polar_comm,
        ← polar_sum_right Q (a i) Finset.univ x a]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [hGdef, Matrix.of_apply, mul_comm, QuadraticMap.polar_comm Q (a i) (a j)])
  have hxeq : x = G⁻¹ *ᵥ (G *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]
  rw [hxeq, hGx, Matrix.mulVec_zero]

open scoped Classical in
omit [Fintype K] [DecidableEq K] in
/-- **A-M4a gap-3 (K)** — an orthogonal *anisotropic* basis of the config form `QR`. -/
theorem configFormK_exists_orthoBasis (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)]
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det) :
    ∃ v : Module.Basis (Fin (Module.finrank K (Fin m → K))) K (Fin m → K),
      (QuadraticMap.associated (configFormK Q a)).IsOrthoᵢ v ∧
      ∀ i, configFormK Q a (v i) ≠ 0 := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm K (configFormK Q a))
  refine ⟨v, hv, ?_⟩
  have hv₂ := hv.not_isOrtho_basis_self_of_separatingLeft (configFormK_nondegenerate Q a hG).1
  simp_rw [LinearMap.IsOrtho, QuadraticMap.associated_eq_self_apply] at hv₂
  exact hv₂

open scoped Classical in
/-- **A-M4a gap-4 (K)** — the config-form Gauss sum. -/
theorem configGaussSum_evalK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    {m : ℕ} (a : Fin m → (Fin d → K))
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank K (Fin m → K))) K (Fin m → K))
    (hv : (QuadraticMap.associated (configFormK Q a)).IsOrthoᵢ v)
    (hw : ∀ i, configFormK Q a (v i) ≠ 0) (s : Kˣ) :
    (∑ ρ : Fin m → K, ψ ((s : K) * configFormK Q a ρ))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
            ^ Module.finrank K (Fin m → K)
        * ((∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R'))
              (configFormK Q a (v i)))
          * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
              ^ Module.finrank K (Fin m → K)) := by
  rw [sum_addChar_quadForm_smul hF hψ (configFormK Q a) v hv hw s,
    sum_quadForm_eval hF hψ (configFormK Q a) v hv hw]

open scoped Classical in
/-- **A-M4a gap-5 (K, THE CRUX)** — the discriminant collapse. -/
theorem prod_quadChar_eq_detK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)]
    {m : ℕ} (a : Fin m → (Fin d → K))
    {R' : Type*} [CommRing R'] [IsDomain R']
    (v : Module.Basis (Fin (Module.finrank K (Fin m → K))) K (Fin m → K))
    (hv : (QuadraticMap.associated (configFormK Q a)).IsOrthoᵢ v) :
    (∏ i, ((quadraticChar K).ringHomComp (Int.castRingHom R')) (configFormK Q a (v i)))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R'))
          ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin m → K))
            (QuadraticMap.associated (configFormK Q a))).det) := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  set b₀ := Module.finBasis K (Fin m → K) with hb₀
  set P := b₀.toMatrix v with hPdef
  have hdiag : LinearMap.BilinForm.toMatrix v (QuadraticMap.associated (configFormK Q a))
      = Matrix.diagonal (fun i => configFormK Q a (v i)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, QuadraticMap.associated_eq_self_apply]
    · rw [if_neg hij]; exact LinearMap.isOrthoᵢ_def.mp hv i j hij
  have hdetv : (LinearMap.BilinForm.toMatrix v (QuadraticMap.associated (configFormK Q a))).det
      = ∏ i, configFormK Q a (v i) := by rw [hdiag, Matrix.det_diagonal]
  have hchange : Pᵀ * LinearMap.BilinForm.toMatrix b₀ (QuadraticMap.associated (configFormK Q a)) * P
      = LinearMap.BilinForm.toMatrix v (QuadraticMap.associated (configFormK Q a)) :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b₀) v _
  have hPne : P.det ≠ 0 := by
    have hflip : (v.toMatrix b₀).det * P.det = 1 := by
      rw [← Matrix.det_mul, hPdef, v.toMatrix_mul_toMatrix_flip b₀, Matrix.det_one]
    intro h0; rw [h0, mul_zero] at hflip; exact one_ne_zero hflip.symm
  have hdetrel : P.det
      * (LinearMap.BilinForm.toMatrix b₀ (QuadraticMap.associated (configFormK Q a))).det * P.det
      = ∏ i, configFormK Q a (v i) := by
    rw [← hdetv, ← hchange, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hsq : χ P.det * χ P.det = 1 := by
    simp only [hχ, MulChar.ringHomComp_apply]
    rw [← map_mul, ← pow_two, quadraticChar_sq_one hPne, map_one]
  rw [← map_prod χ (fun i => configFormK Q a (v i)), ← hdetrel, map_mul, map_mul,
    mul_right_comm, hsq, one_mul]

open scoped Classical in
/-- **A-M4a config-side ASSEMBLED (K)** — the config Gauss sum, basis-free. -/
theorem configGaussSum_eq_detK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    {m : ℕ} (a : Fin m → (Fin d → K))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin m) (Fin m) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (s : Kˣ) :
    (∑ ρ : Fin m → K, ψ ((s : K) * configFormK Q a ρ))
      = ((quadraticChar K).ringHomComp (Int.castRingHom R')) (s : K)
            ^ Module.finrank K (Fin m → K)
        * (((quadraticChar K).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin m → K))
              (QuadraticMap.associated (configFormK Q a))).det)
          * gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ
              ^ Module.finrank K (Fin m → K)) := by
  obtain ⟨v, hv, hw⟩ := configFormK_exists_orthoBasis Q a hG
  rw [configGaussSum_evalK Q hF a hψ v hv hw s, prod_quadChar_eq_detK Q a v hv]

end ChainDescent

#print axioms ChainDescent.isoIncidence_eq_linearCondsK
#print axioms ChainDescent.reduction_to_levelset_nondegK
#print axioms ChainDescent.levelset_count_eqK
#print axioms ChainDescent.configFormK_nondegenerate
#print axioms ChainDescent.configGaussSum_eq_detK
