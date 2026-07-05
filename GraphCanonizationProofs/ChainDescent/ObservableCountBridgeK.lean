/-
# Bridge lift (concern #4) — `ScratchBridge{A,B,C,D}` + `ScratchLemmaB.cone_count_zero_split` over abstract `K`.

The analytic half of the observable↔count bridge, V-indexed over an abstract finite field `K` (`V = Fin d → K`,
no `affineE`). Mirrors the `ZMod p` bridge decl-for-decl; the analytic core `ScratchLemmaAK` is already lifted, the
Gauss toolkit (`GaussCount`) is abstract, and the field-arithmetic distinctness lemmas
(`chiSep_imp_zSep_field`/`pairCount_ne_of_chiSep_field`, already abstract `[Field F][CharZero F]`) are reused from
`ScratchBridgeD`.

End-to-end K-capstone: **`jointIsoCount_ne_of_chiSep_pairK`** — for `u ≠ v`, config-nondeg + `corr = 0` sub-frame
`{t,t₀}`, χ(pairForm) separating ⟹ `jointIsoCountK Q u {t,t₀} ≠ jointIsoCountK Q v {t,t₀}`. Feeds
`ScratchBridgeK.zProfileSeparatesK_of_zSep`. The one field-specific spot: carries `2 < Fintype.card K` (the K-analogue
of `2 < p`).

Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build.
-/
import ChainDescent.IsotropicIncidenceCountK
import ChainDescent.PairForm
import ChainDescent.ObservableCountBridge

namespace ChainDescent

open QuadraticMap Finset Module Matrix

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-! ### `ScratchLemmaB.cone_count_zero_split` over `K` (V-indexed). -/

open scoped Classical in
/-- **The `y=0` split (K)** — `fullcount = restricted (y≠0) + [∀ t∈S', Q(t−w)=0]`. -/
theorem cone_count_zero_splitK (Q : QuadraticForm K (Fin d → K))
    (S' : Finset (Fin d → K)) (w : Fin d → K) :
    (Finset.univ.filter (fun y : Fin d → K =>
        Q y = 0 ∧ ∀ t ∈ S', Q (y - (t - w)) = 0)).card
      = (Finset.univ.filter (fun y : Fin d → K =>
        y ≠ 0 ∧ Q y = 0 ∧ ∀ t ∈ S', Q (y - (t - w)) = 0)).card
        + (if ∀ t ∈ S', Q (t - w) = 0 then 1 else 0) := by
  classical
  have hP0 : (Q (0 : Fin d → K) = 0
        ∧ ∀ t ∈ S', Q ((0 : Fin d → K) - (t - w)) = 0)
      ↔ ∀ t ∈ S', Q (t - w) = 0 := by
    constructor
    · intro h t ht; have := h.2 t ht; rwa [zero_sub, QuadraticMap.map_neg] at this
    · exact fun h => ⟨by simp, fun t ht => by rw [zero_sub, QuadraticMap.map_neg]; exact h t ht⟩
  by_cases h0 : ∀ t ∈ S', Q (t - w) = 0
  · rw [if_pos h0]
    have hmem : (0 : Fin d → K) ∈ Finset.univ.filter (fun y : Fin d → K =>
        Q y = 0 ∧ ∀ t ∈ S', Q (y - (t - w)) = 0) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hP0.mpr h0⟩
    have heq : (Finset.univ.filter (fun y : Fin d → K =>
          Q y = 0 ∧ ∀ t ∈ S', Q (y - (t - w)) = 0)).erase 0
        = Finset.univ.filter (fun y : Fin d → K =>
          y ≠ 0 ∧ Q y = 0 ∧ ∀ t ∈ S', Q (y - (t - w)) = 0) := by
      ext y; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← heq, Finset.card_erase_add_one hmem]
  · rw [if_neg h0, add_zero]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hy => ⟨?_, hy⟩, fun hy => hy.2⟩
    rintro rfl
    exact h0 (hP0.mp hy)

/-! ### `ScratchBridgeB` over `K`. -/

open scoped Classical in
/-- **B1a wrap (i) (K)** — `fullcount = jointIsoCountK + (y=0 correction)`. -/
theorem fullcount_eq_jointIsoCountK_add_corr (Q : QuadraticForm K (Fin d → K))
    (S : Finset (Fin d → K)) (u : Fin d → K) :
    (Finset.univ.filter (fun y : Fin d → K =>
        Q y = 0 ∧ ∀ t ∈ S, Q (y - (t - u)) = 0)).card
      = jointIsoCountK Q u S
        + (if ∀ t ∈ S, Q (t - u) = 0 then 1 else 0) := by
  rw [cone_count_zero_splitK Q S u, ← jointIsoCountK_eq_restricted]

/-! ### `ScratchBridgeA` over `K`. -/

open scoped Classical in
/-- **B1a analytic core (K)** — the `|S|=2`, even-`d` `s`-sum collapse. -/
theorem levelset_count_collapseK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    (a : Fin 2 → (Fin d → K)) (c : K) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin 2) (Fin 2) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ((Finset.univ.filter (fun x : Fin d → K =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R') * (Fintype.card K : R') ^ 3
      = (Fintype.card (Fin d → K) : R')
        + ((quadraticChar K).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin 2 → K))
              (QuadraticMap.associated (configFormK Q a))).det)
          * (gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ 2
              * ∑ x : Fin d → K, ψ (Q x))
          * ((Fintype.card K : R') * (if c = 0 then 1 else 0) - 1) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  set g := gaussSum χ ψ with hg
  set W := ∑ x : Fin d → K, ψ (Q x) with hW
  set D := (LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin 2 → K))
      (QuadraticMap.associated (configFormK Q a))).det with hD
  rw [show ((Fintype.card K : R') ^ 3) = (Fintype.card K : R') ^ (2 + 1) from by norm_num,
    levelset_count_eqK Q a c hG hψ]
  congr 1
  have hsq : ∀ t : K, t ≠ 0 → χ t ^ 2 = 1 := by
    intro t ht
    have h := quadraticChar_sq_one (F := K) ht
    have : (χ t) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hterm : ∀ s ∈ Finset.univ.erase (0 : K),
      (∑ ρ : Fin 2 → K, ψ (-(s * c)) *
          (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → K, ψ (s * Q x)))
        = ψ (-(s * c)) * (χ D * (g ^ 2 * W)) := by
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    have hfac : ∀ ρ : Fin 2 → K,
        ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → K, ψ (s * Q x))
          = (ψ (-(s * c)) * ∑ x : Fin d → K, ψ (s * Q x))
            * ψ ((-(s⁻¹)) * configFormK Q a ρ) := by
      intro ρ
      rw [configFormK_apply, show (-(s⁻¹)) * Q (∑ j, ρ j • a j) = -(s⁻¹ * Q (∑ j, ρ j • a j)) from by
        ring]
      ring
    rw [Finset.sum_congr rfl (fun ρ _ => hfac ρ), ← Finset.mul_sum]
    have hsinv : (-(s⁻¹)) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
    have hcfg := configGaussSum_eq_detK Q hF a hG hψ (Units.mk0 (-(s⁻¹)) hsinv)
    rw [Units.val_mk0] at hcfg
    rw [hcfg]
    have hglob := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 s hs0)
    rw [Units.val_mk0] at hglob
    rw [hglob, ← hW]
    have hp1 : χ (-(s⁻¹)) ^ (Module.finrank K (Fin 2 → K)) = 1 := by
      rw [Module.finrank_fin_fun (R := K)]; exact hsq _ hsinv
    have hp2 : χ s ^ (Module.finrank K (Fin d → K)) = 1 := by
      rw [Module.finrank_fin_fun (R := K)]
      obtain ⟨r, hr⟩ := hd
      rw [hr, ← two_mul, pow_mul, hsq s hs0, one_pow]
    have hp3 : g ^ (Module.finrank K (Fin 2 → K)) = g ^ 2 := by
      rw [Module.finrank_fin_fun (R := K)]
    rw [hp1, hp2, hp3]
    simp only [hχ, hg, hW, hD]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have horth : (∑ s ∈ Finset.univ.erase (0 : K), ψ (-(s * c)))
      = (Fintype.card K : R') * (if c = 0 then 1 else 0) - 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : K)),
      Finset.sum_congr rfl (fun s _ => by rw [show -(s * c) = s * (-c) from by ring]),
      AddChar.sum_mulShift (-c) hψ]
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, neg_eq_zero]
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · simp [hc]
  rw [horth]
  ring

/-! ### `ScratchBridgeC` over `K`. -/

open scoped Classical in
/-- **B1a wrap (ii-a) (K)** — fullcount over `{t,t₀}` = the homogeneous level-set count. -/
theorem fullcount_pair_eq_levelsetK (Q : QuadraticForm K (Fin d → K))
    (u t t₀ : Fin d → K)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![t - u, t₀ - u] i) (![t - u, t₀ - u] j)) :
      Matrix (Fin 2) (Fin 2) K).det) :
    ∃ c : Fin 2 → K,
      (Finset.univ.filter (fun y : Fin d → K =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin d → K)), Q (y - (s - u)) = 0)).card
        = (Finset.univ.filter (fun x : Fin d → K =>
          (∀ j, QuadraticMap.polar Q x (![t - u, t₀ - u] j) = 0)
          ∧ Q x = - Q (∑ k, c k • (![t - u, t₀ - u] k)))).card := by
  set a : Fin 2 → (Fin d → K) := ![t - u, t₀ - u] with ha
  have hpred : (Finset.univ.filter (fun y : Fin d → K =>
        Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin d → K)), Q (y - (s - u)) = 0))
      = (Finset.univ.filter (fun y : Fin d → K =>
        Q y = 0 ∧ ∀ j, Q (y - a j) = 0)) := by
    apply Finset.filter_congr
    intro y _
    refine and_congr_right (fun _ => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.forall_fin_two, ha, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpred]
  exact reduction_to_levelset_nondegK Q a hG

open scoped Classical in
/-- **B1a wrap (ii-b) (K)** — the fullcount closed form over `{t,t₀}`. -/
theorem fullcount_pair_closedK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    (u t t₀ : Fin d → K) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![t - u, t₀ - u] i) (![t - u, t₀ - u] j)) :
      Matrix (Fin 2) (Fin 2) K).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ∃ w₀ : Fin d → K,
      ((Finset.univ.filter (fun y : Fin d → K =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin d → K)), Q (y - (s - u)) = 0)).card : R')
            * (Fintype.card K : R') ^ 3
        = (Fintype.card (Fin d → K) : R')
          + ((quadraticChar K).ringHomComp (Int.castRingHom R'))
              ((LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin 2 → K))
                (QuadraticMap.associated (configFormK Q ![t - u, t₀ - u]))).det)
            * (gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom R')) ψ ^ 2
                * ∑ x : Fin d → K, ψ (Q x))
            * ((Fintype.card K : R') * (if Q w₀ = 0 then 1 else 0) - 1) := by
  obtain ⟨c, hc⟩ := fullcount_pair_eq_levelsetK Q u t t₀ hG
  refine ⟨∑ k, c k • (![t - u, t₀ - u] k), ?_⟩
  rw [hc, levelset_count_collapseK Q hF ![t - u, t₀ - u]
      (- Q (∑ k, c k • (![t - u, t₀ - u] k))) hd hG hψ v hv hw]
  simp only [neg_eq_zero]

/-! ### `ScratchBridgeD` over `K`. -/

omit [Fintype K] [DecidableEq K] in
/-- **The config polar-Gram det is the pair invariant `pairForm` (K).** -/
theorem configPolarDet_eq_pairFormK (Q : QuadraticForm K (Fin d → K)) (u t t₀ : Fin d → K) :
    (Matrix.of (fun i j => QuadraticMap.polar Q (![t - u, t₀ - u] i) (![t - u, t₀ - u] j)) :
      Matrix (Fin 2) (Fin 2) K).det
      = pairForm Q (t₀ - u) (t - u) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    QuadraticMap.polar_self, QuadraticMap.polar_comm Q (t₀ - u) (t - u), nsmul_eq_mul]
  rw [← detG2_eq_pairForm Q u t₀ t]
  push_cast
  ring

/-- **wrap (iii) (K) — `χ(D) = χ(I_w(t))`.** -/
theorem chi_configDet_eq_chi_pairFormK (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (u t t₀ : Fin d → K)
    {R' : Type*} [CommRing R'] [IsDomain R'] :
    ((quadraticChar K).ringHomComp (Int.castRingHom R'))
        (LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin 2 → K))
          (QuadraticMap.associated (configFormK Q ![t - u, t₀ - u]))).det
      = ((quadraticChar K).ringHomComp (Int.castRingHom R'))
          (pairForm Q (t₀ - u) (t - u)) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  set a : Fin 2 → (Fin d → K) := ![t - u, t₀ - u] with ha
  set Bil := QuadraticMap.associated (R := K) (configFormK Q a) with hBil
  set Mfin := LinearMap.BilinForm.toMatrix (Module.finBasis K (Fin 2 → K)) Bil with hMfin
  set Mbf := LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin 2)) Bil with hMbf
  have hsq : ∀ s : K, s ≠ 0 → (χ s) ^ 2 = 1 := by
    intro s hs
    have h := quadraticChar_sq_one (F := K) hs
    have : (χ s) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hkill : ∀ s x : K, s ≠ 0 → χ (s ^ 2 * x) = χ x := by
    intro s x hs
    rw [map_mul, map_pow, hsq s hs, one_mul]
  set e : Fin (Module.finrank K (Fin 2 → K)) ≃ Fin 2 :=
    finCongr (Module.finrank_fin_fun (R := K)) with he
  set b₂ := (Module.finBasis K (Fin 2 → K)).reindex e with hb₂
  set Mr := LinearMap.BilinForm.toMatrix b₂ Bil with hMr
  have hMrsub : Mr = Mfin.submatrix e.symm e.symm := by
    ext i j
    rw [hMr, LinearMap.BilinForm.toMatrix_apply, Matrix.submatrix_apply, hMfin,
      LinearMap.BilinForm.toMatrix_apply, hb₂, Basis.reindex_apply, Basis.reindex_apply]
  have hMrdet : Mr.det = Mfin.det := by rw [hMrsub, Matrix.det_submatrix_equiv_self]
  set P := b₂.toMatrix (Pi.basisFun K (Fin 2)) with hP
  have hPne : P.det ≠ 0 := by
    intro h0
    have hmul : P.det * ((Pi.basisFun K (Fin 2)).toMatrix b₂).det = 1 := by
      rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    rw [h0, zero_mul] at hmul
    exact one_ne_zero hmul.symm
  have hcong : Pᵀ * Mr * P = Mbf :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b₂) (Pi.basisFun K (Fin 2)) Bil
  have hdet : Mbf.det = P.det ^ 2 * Mr.det := by
    rw [← hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hstep1 : χ Mfin.det = χ Mbf.det := by
    rw [hdet, ← hMrdet]; exact (hkill P.det Mr.det hPne).symm
  have hentry : ∀ i j, Mbf i j = ⅟(2 : K) * QuadraticMap.polar Q (a i) (a j) := by
    intro i j
    rw [hMbf, LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    have hpolar : QuadraticMap.polar (configFormK Q a) (Pi.single i 1) (Pi.single j 1)
        = 2 • Bil (Pi.single i 1) (Pi.single j 1) := by
      rw [hBil, ← QuadraticMap.polarBilin_apply_apply, ← two_nsmul_associated (S := K)]
      simp only [LinearMap.smul_apply]
    rw [polar_configFormK_single] at hpolar
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hpolar
    rw [hpolar, ← mul_assoc, invOf_mul_self, one_mul]
  have hMbfdet : Mbf.det = (⅟(2 : K)) ^ 2 * pairForm Q (t₀ - u) (t - u) := by
    rw [← configPolarDet_eq_pairFormK Q u t t₀]
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [hentry, Matrix.of_apply, ha]
    ring
  have h2ne : (⅟(2 : K)) ≠ 0 := by
    intro h0
    have hms := invOf_mul_self (2 : K)
    rw [h0, zero_mul] at hms
    exact one_ne_zero hms.symm
  have hstep2 : χ Mbf.det = χ (pairForm Q (t₀ - u) (t - u)) := by
    rw [hMbfdet]; exact hkill _ _ h2ne
  exact hstep1.trans hstep2

/-- The quadratic character of a nonzero element is `±1` (K). -/
theorem chi_eq_one_or_neg_oneK {R' : Type*} [CommRing R'] [IsDomain R'] {x : K} (hx : x ≠ 0) :
    ((quadraticChar K).ringHomComp (Int.castRingHom R')) x = 1
      ∨ ((quadraticChar K).ringHomComp (Int.castRingHom R')) x = -1 := by
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom R') with hχ
  have hsq : (χ x) ^ 2 = 1 := by
    have h := quadraticChar_sq_one (F := K) hx
    have : (χ x) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hmm : χ x * χ x = 1 := by rw [← pow_two]; exact hsq
  exact mul_self_eq_one_iff.mp hmm

open scoped Classical in
/-- **B1a final assembly (K) — the observable per-pair closed form (corr = 0).** -/
theorem jointIsoCountK_pair_closed_corr0 (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    (u t t₀ : Fin d → K) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![t - u, t₀ - u] i) (![t - u, t₀ - u] j)) :
      Matrix (Fin 2) (Fin 2) K).det)
    {F : Type*} [Field F] [CharZero F] {ψ : AddChar K F} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (hcorr : ¬ (Q (t - u) = 0 ∧ Q (t₀ - u) = 0)) :
    ∃ w₀ : Fin d → K,
      (jointIsoCountK Q u {t, t₀} : F) * (Fintype.card K : F) ^ 3
        = (Fintype.card (Fin d → K) : F)
          + ((quadraticChar K).ringHomComp (Int.castRingHom F))
              (pairForm Q (t₀ - u) (t - u))
            * (gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom F)) ψ ^ 2
                * ∑ x : Fin d → K, ψ (Q x))
            * ((Fintype.card K : F) * (if Q w₀ = 0 then 1 else 0) - 1) := by
  obtain ⟨w₀, hfc⟩ := fullcount_pair_closedK Q hF u t t₀ hd hG hψ vb hv hw
  refine ⟨w₀, ?_⟩
  have hcorr0 : (if ∀ s ∈ ({t, t₀} : Finset (Fin d → K)), Q (s - u) = 0 then 1 else 0) = (0 : ℕ) := by
    rw [if_neg]
    intro hall
    exact hcorr ⟨hall t (by simp), hall t₀ (by simp)⟩
  have hcard : (Finset.univ.filter (fun y : Fin d → K =>
      Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin d → K)), Q (y - (s - u)) = 0)).card
      = jointIsoCountK Q u {t, t₀} := by
    rw [fullcount_eq_jointIsoCountK_add_corr Q {t, t₀} u, hcorr0, add_zero]
  rw [hcard, chi_configDet_eq_chi_pairFormK Q u t t₀] at hfc
  exact hfc

open scoped Classical in
/-- **THE BRIDGE, per-pair end-to-end (K) — `χ(I)`-separation ⟹ `Z`-separation.** Carries `2 < Fintype.card K`
(the K-analogue of `2 < p`); the Gauss-factor nonvanishing is discharged internally (`gaussSum_sq_ne_zero` +
`sum_addChar_quadForm_ne_zero`). Feeds `ScratchBridgeK.zProfileSeparatesK_of_zSep`. -/
theorem jointIsoCountK_ne_of_chiSep_pair (Q : QuadraticForm K (Fin d → K))
    [Invertible (2 : K)] (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K)
    (u v t t₀ : Fin d → K) (hd : Even d)
    (hGu : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![t - u, t₀ - u] i) (![t - u, t₀ - u] j)) : Matrix (Fin 2) (Fin 2) K).det)
    (hGv : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![t - v, t₀ - v] i) (![t - v, t₀ - v] j)) : Matrix (Fin 2) (Fin 2) K).det)
    {F : Type*} [Field F] [CharZero F] {ψ : AddChar K F} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (hcorru : ¬ (Q (t - u) = 0 ∧ Q (t₀ - u) = 0))
    (hcorrv : ¬ (Q (t - v) = 0 ∧ Q (t₀ - v) = 0))
    (hne : ((quadraticChar K).ringHomComp (Int.castRingHom F)) (pairForm Q (t₀ - u) (t - u))
          ≠ ((quadraticChar K).ringHomComp (Int.castRingHom F)) (pairForm Q (t₀ - v) (t - v))) :
    jointIsoCountK Q u {t, t₀} ≠ jointIsoCountK Q v {t, t₀} := by
  -- the carried Gauss-factor nonvanishing `hK` is discharged from `hF`/`hψ` + the anisotropic basis `vb`
  have hK : gaussSum ((quadraticChar K).ringHomComp (Int.castRingHom F)) ψ ^ 2
      * ∑ x : Fin d → K, ψ (Q x) ≠ 0 :=
    mul_ne_zero (gaussSum_sq_ne_zero hF hψ) (sum_addChar_quadForm_ne_zero hF hψ Q vb hv hw)
  have hpu : pairForm Q (t₀ - u) (t - u) ≠ 0 := by
    have h := hGu; rw [configPolarDet_eq_pairFormK Q u t t₀] at h; exact h.ne_zero
  have hpv : pairForm Q (t₀ - v) (t - v) ≠ 0 := by
    have h := hGv; rw [configPolarDet_eq_pairFormK Q v t t₀] at h; exact h.ne_zero
  have hcu := chi_eq_one_or_neg_oneK (R' := F) hpu
  have hcv := chi_eq_one_or_neg_oneK (R' := F) hpv
  obtain ⟨wu, hu⟩ := jointIsoCountK_pair_closed_corr0 Q hF u t t₀ hd hGu hψ vb hv hw hcorru
  obtain ⟨wv, hvv⟩ := jointIsoCountK_pair_closed_corr0 Q hF v t t₀ hd hGv hψ vb hv hw hcorrv
  have hbu : (if Q wu = 0 then (1 : F) else 0) = 0 ∨ (if Q wu = 0 then (1 : F) else 0) = 1 := by
    split_ifs; exacts [Or.inr rfl, Or.inl rfl]
  have hbv : (if Q wv = 0 then (1 : F) else 0) = 0 ∨ (if Q wv = 0 then (1 : F) else 0) = 1 := by
    split_ifs; exacts [Or.inr rfl, Or.inl rfl]
  intro hjeq
  exact pairCount_ne_of_chiSep_field hcardK hK hbu hbv hcu hcv hne hu hvv (by exact_mod_cast hjeq)

end ChainDescent

--#print axioms ChainDescent.cone_count_zero_splitK
--#print axioms ChainDescent.levelset_count_collapseK
--#print axioms ChainDescent.fullcount_pair_closedK
--#print axioms ChainDescent.chi_configDet_eq_chi_pairFormK
--#print axioms ChainDescent.jointIsoCountK_pair_closed_corr0
--#print axioms ChainDescent.jointIsoCountK_ne_of_chiSep_pair
