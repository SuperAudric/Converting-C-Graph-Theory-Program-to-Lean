/-
# The observable↔count bridge (prime field) — `χ(det G₂) ↔ Z_u(S)`.

Turns the per-pair separating invariant `χ(det G₂(u; t, t₀))` into the observable joint isotropic counts
`Z_u(S) = jointIsoCount Q u S`, over the prime field `ZMod p`. The chain (all for the `|S| = 2` sub-frame `{t, t₀}`,
even form dimension `d`):

* **wrap (collapse) `levelset_count_collapse`** — the `s`-sum of the Lemma-A (`IsotropicIncidenceCount`) closed form
  collapses, for `|S| = 2` and even `d`, to `count · q³ = |V| + χ(D)·(gaussSum²·∑ψ(Q))·(q·[c=0] − 1)`, with the config
  dependence entering ONLY through `χ(D)` (= the pair invariant). `χ-kills-squares` lives in wrap (iii).
* **wrap (i) `fullcount_eq_jointIsoCount_add_corr`** — the Lemma-A fullcount = the observable `jointIsoCount` + the
  `y=0` correction indicator.
* **wrap (ii) `fullcount_pair_eq_levelset` / `fullcount_pair_closed`** — index the pair as a `Fin 2` config and feed
  the fullcount through the collapse, giving the fullcount closed form over `{t, t₀}`.
* **wrap (iii) `chi_configDet_eq_chi_pairForm`** — `χ(D) = χ(I_w(t))`: the `½·polar` factor-2 and the
  `finBasis ↔ basisFun` change of basis both enter as SQUARES, killed by `χ`.
* **assembly `jointIsoCount_pair_closed_corr0`** + the ℂ-restated distinctness (`chiSep_imp_zSep_field` /
  `pairCount_ne_of_chiSep_field`) ⟹ the per-pair capstone **`jointIsoCount_ne_of_chiSep_pair`**: `χ(I)`-separation ⟹
  `Z`-separation. Feeds `ScratchBridgeK.zProfileSeparatesK_of_zSep` (via the abstract-K lift `ScratchBridgeAllK`).

(Merge of the former `ScratchBridge{A,B,C,D}`. The abstract-`K` mirror is `ScratchBridgeAllK`.)
-/
import ChainDescent.IsotropicIncidenceCount
import ChainDescent.ProfileReduction
import ChainDescent.PairForm

namespace ChainDescent

open QuadraticMap Finset Module Matrix

variable {p d : ℕ} [Fact p.Prime]

-- ═══ collapse (was ScratchBridgeA) ═══
open scoped Classical in
/-- **B1a analytic core — the `|S|=2`, even-`d` `s`-sum collapse.** For a nondegenerate config Gram (`hG`), config
size `m = 2`, and **even** `d` with an orthogonal anisotropic basis `v` of `Q` (`hv`/`hw`), the level-set count at
level `c` satisfies
`count · q³ = |V| + χ(D) · (gaussSum² · W) · (q·[c=0] − 1)`,
`D = det` of `associated (configForm Q a)` at `finBasis`, `W = ∑_x ψ(Q x)`. The config-dependence enters **only**
through `χ(D)` (= the pair invariant `χ(det G₂)`) — the property the bridge needs. -/
theorem levelset_count_collapse (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (a : Fin 2 → (Fin d → ZMod p)) (c : ZMod p) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q (a i) (a j)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ((Finset.univ.filter (fun x : Fin d → ZMod p =>
        (∀ j, QuadraticMap.polar Q x (a j) = 0) ∧ Q x = c)).card : R') * (p : R') ^ 3
      = (Fintype.card (Fin d → ZMod p) : R')
        + ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
            ((LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
              (QuadraticMap.associated (configForm Q a))).det)
          * (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) ψ ^ 2
              * ∑ x : Fin d → ZMod p, ψ (Q x))
          * ((p : R') * (if c = 0 then 1 else 0) - 1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R') with hχ
  set g := gaussSum χ ψ with hg
  set W := ∑ x : Fin d → ZMod p, ψ (Q x) with hW
  set D := (LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
      (QuadraticMap.associated (configForm Q a))).det with hD
  -- the landed closed form, then collapse the `s`-sum
  rw [show ((p : R') ^ 3) = (p : R') ^ (2 + 1) from by norm_num, levelset_count_eq Q a c hG hψ]
  congr 1
  -- per-`s` evaluation of the inner `ρ`-sum
  have hsq : ∀ t : ZMod p, t ≠ 0 → χ t ^ 2 = 1 := by
    intro t ht
    have h := quadraticChar_sq_one (F := ZMod p) ht
    have : (χ t) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hterm : ∀ s ∈ Finset.univ.erase (0 : ZMod p),
      (∑ ρ : Fin 2 → ZMod p, ψ (-(s * c)) *
          (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x)))
        = ψ (-(s * c)) * (χ D * (g ^ 2 * W)) := by
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    -- factor out the `ρ`-independent pieces
    have hfac : ∀ ρ : Fin 2 → ZMod p,
        ψ (-(s * c)) * (ψ (-(s⁻¹ * Q (∑ j, ρ j • a j))) * ∑ x : Fin d → ZMod p, ψ (s * Q x))
          = (ψ (-(s * c)) * ∑ x : Fin d → ZMod p, ψ (s * Q x))
            * ψ ((-(s⁻¹)) * configForm Q a ρ) := by
      intro ρ
      rw [configForm_apply, show (-(s⁻¹)) * Q (∑ j, ρ j • a j) = -(s⁻¹ * Q (∑ j, ρ j • a j)) from by
        ring]
      ring
    rw [Finset.sum_congr rfl (fun ρ _ => hfac ρ), ← Finset.mul_sum]
    -- config `ρ`-sum via `configGaussSum_eq_det` at the unit `s' = -s⁻¹`
    have hsinv : (-(s⁻¹)) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
    have hcfg := configGaussSum_eq_det Q hF a hG hψ (Units.mk0 (-(s⁻¹)) hsinv)
    rw [Units.val_mk0] at hcfg
    rw [hcfg]
    -- global `x`-sum via `sum_addChar_quadForm_smul` at the unit `s`
    have hglob := sum_addChar_quadForm_smul hF hψ Q v hv hw (Units.mk0 s hs0)
    rw [Units.val_mk0] at hglob
    rw [hglob, ← hW]
    -- kill the `s`-character powers (`m = 2` even, `d` even) by rewriting only the power subterms
    have hp1 : χ (-(s⁻¹)) ^ (Module.finrank (ZMod p) (Fin 2 → ZMod p)) = 1 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]; exact hsq _ hsinv
    have hp2 : χ s ^ (Module.finrank (ZMod p) (Fin d → ZMod p)) = 1 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]
      obtain ⟨r, hr⟩ := hd
      rw [hr, ← two_mul, pow_mul, hsq s hs0, one_pow]
    have hp3 : g ^ (Module.finrank (ZMod p) (Fin 2 → ZMod p)) = g ^ 2 := by
      rw [Module.finrank_fin_fun (R := ZMod p)]
    rw [hp1, hp2, hp3]
    simp only [hχ, hg, hW, hD]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  -- additive orthogonality: `∑_{s≠0} ψ(−(s·c)) = q·[c=0] − 1`
  have horth : (∑ s ∈ Finset.univ.erase (0 : ZMod p), ψ (-(s * c)))
      = (p : R') * (if c = 0 then 1 else 0) - 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod p)),
      Finset.sum_congr rfl (fun s _ => by rw [show -(s * c) = s * (-c) from by ring]),
      AddChar.sum_mulShift (-c) hψ]
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, ZMod.card, neg_eq_zero]
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · simp [hc]
  rw [horth]
  ring


-- ═══ wrap i (was ScratchBridgeB) ═══
open scoped Classical in
/-- **B1a wrap (i) — `fullcount = jointIsoCount + (y=0 correction)`.** The Lemma-A fullcount over `V`
(`#{y : Q y = 0 ∧ ∀ t∈S, Q(y−(t̄−ū)) = 0}`, the `reduction_to_levelset_nondeg` entry point) equals the observable
`jointIsoCount Q u S` (the same count restricted to `y ≠ 0`) plus the correction `[∀ t∈S, Q(t̄−ū)=0]`. Pure compose of
`cone_count_zero_split` (full = restricted + corr) and `jointIsoCount_eq_restricted` (jointIsoCount = restricted). -/
theorem fullcount_eq_jointIsoCount_add_corr (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (S : Finset (Fin (p ^ d))) (u : Fin (p ^ d)) :
    (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ t ∈ S, Q (y - (affineE.symm t - affineE.symm u)) = 0)).card
      = jointIsoCount Q u S
        + (if ∀ t ∈ S, Q (affineE.symm t - affineE.symm u) = 0 then 1 else 0) := by
  rw [cone_count_zero_split Q S u, ← jointIsoCount_eq_restricted]


-- ═══ wrap ii (was ScratchBridgeC) ═══
open scoped Classical in
/-- **B1a wrap (ii-a) — fullcount over `{t,t₀}` = the homogeneous level-set count.** Index the pair `{t,t₀}` as the
`Fin 2` config `a = ![t̄−ū, t̄₀−ū]`; on the config-nondegenerate locus (`hG : IsUnit (config Gram det)`) the Lemma-A
fullcount equals the level-set count of `Q|_{Uᗮ}` at level `−Q w₀` for the spanning `w₀ = ∑ c k • a k`. Pure compose of
the `Finset {t,t₀}` ↔ `Fin 2` predicate conversion with the landed `reduction_to_levelset_nondeg`. -/
theorem fullcount_pair_eq_levelset (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (u t t₀ : Fin (p ^ d))
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det) :
    ∃ c : Fin 2 → ZMod p,
      (Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
            Q (y - (affineE.symm s - affineE.symm u)) = 0)).card
        = (Finset.univ.filter (fun x : Fin d → ZMod p =>
          (∀ j, QuadraticMap.polar Q x
              (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j) = 0)
          ∧ Q x = - Q (∑ k, c k •
              (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k)))).card := by
  set a : Fin 2 → (Fin d → ZMod p) :=
    ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] with ha
  -- the Finset-`{t,t₀}` membership predicate equals the `Fin 2`-config predicate
  have hpred : (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
          Q (y - (affineE.symm s - affineE.symm u)) = 0))
      = (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ j, Q (y - a j) = 0)) := by
    apply Finset.filter_congr
    intro y _
    refine and_congr_right (fun _ => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Fin.forall_fin_two, ha, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpred]
  exact reduction_to_levelset_nondeg Q a hG

open scoped Classical in
/-- **B1a wrap (ii-b) — the fullcount closed form over `{t,t₀}`.** Composing wrap (ii-a) with
`levelset_count_collapse`: for even `d` and a config-nondegenerate Gram, the Lemma-A fullcount over `{t,t₀}` satisfies
`fullcount · q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀ = 0] − 1)`, with `w₀ = ∑ c k • a k` the spanning solution and
`D = det` of the config Gram. The level bit `[c=0]` is `[−Q w₀ = 0] = [Q w₀ = 0]`. This is the fullcount side of the
bridge's per-pair closed form; the observable `jointIsoCount` then equals `fullcount − corr` (wrap (i)). -/
theorem fullcount_pair_closed (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (u t t₀ : Fin (p ^ d)) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar (ZMod p) R'} (hψ : ψ.IsPrimitive)
    (v : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ v) (hw : ∀ i, Q (v i) ≠ 0) :
    ∃ w₀ : Fin d → ZMod p,
      ((Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
            Q (y - (affineE.symm s - affineE.symm u)) = 0)).card : R') * (p : R') ^ 3
        = (Fintype.card (Fin d → ZMod p) : R')
          + ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
              ((LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
                (QuadraticMap.associated (configForm Q
                  ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u]))).det)
            * (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) ψ ^ 2
                * ∑ x : Fin d → ZMod p, ψ (Q x))
            * ((p : R') * (if Q w₀ = 0 then 1 else 0) - 1) := by
  obtain ⟨c, hc⟩ := fullcount_pair_eq_levelset Q u t t₀ hG
  refine ⟨∑ k, c k • (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k), ?_⟩
  rw [hc, levelset_count_collapse Q hF
      ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u]
      (- Q (∑ k, c k • (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] k)))
      hd hG hψ v hv hw]
  simp only [neg_eq_zero]


-- ═══ wrap iii + assembly (was ScratchBridgeD) ═══
/-- The config polar-Gram determinant (the `IsUnit` hypothesis matrix of `fullcount_pair_closed`/`levelset_count_collapse`)
is the pair invariant `pairForm`. `det_fin_two` + `polar_self` (`polar Q x x = 2 Q x`) + `polar_comm` + the structural
`detG2_eq_pairForm` (`4 Q(a₀) Q(a₁) − B(a₀,a₁)² = pairForm`). -/
theorem configPolarDet_eq_pairForm (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (u t t₀ : Fin (p ^ d)) :
    (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det
      = pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    QuadraticMap.polar_self,
    QuadraticMap.polar_comm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u),
    nsmul_eq_mul]
  rw [← detG2_eq_pairForm Q (affineE.symm u) (affineE.symm t₀) (affineE.symm t)]
  push_cast
  ring

/-- **wrap (iii) — `χ(D) = χ(I_w(t))`.** The `Module.finBasis` config-Gram determinant `D` appearing in
`fullcount_pair_closed` has the same quadratic character as the pair invariant `pairForm Q (t̄₀−ū)(t̄−ū) = det G₂`.
Both the `associated = ½·polar` factor (`(⅟2)²`) and the `finBasis ↔ Pi.basisFun` change of basis (`(det P)²`) enter as
**squares**, which `χ` kills (`hkill`). No identification of `finBasis` with the standard basis is needed. -/
theorem chi_configDet_eq_chi_pairForm (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (u t t₀ : Fin (p ^ d))
    {R' : Type*} [CommRing R'] [IsDomain R'] :
    ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
        (LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p))
          (QuadraticMap.associated (configForm Q
            ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u]))).det
      = ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R'))
          (pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u)) := by
  classical
  set χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R') with hχ
  set a : Fin 2 → (Fin d → ZMod p) :=
    ![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] with ha
  set Bil := QuadraticMap.associated (R := ZMod p) (configForm Q a) with hBil
  set Mfin := LinearMap.BilinForm.toMatrix (Module.finBasis (ZMod p) (Fin 2 → ZMod p)) Bil with hMfin
  set Mbf := LinearMap.BilinForm.toMatrix (Pi.basisFun (ZMod p) (Fin 2)) Bil with hMbf
  -- `χ` kills nonzero squares
  have hsq : ∀ s : ZMod p, s ≠ 0 → (χ s) ^ 2 = 1 := by
    intro s hs
    have h := quadraticChar_sq_one (F := ZMod p) hs
    have : (χ s) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hkill : ∀ s x : ZMod p, s ≠ 0 → χ (s ^ 2 * x) = χ x := by
    intro s x hs
    rw [map_mul, map_pow, hsq s hs, one_mul]
  -- reindex `finBasis` (indexed by `Fin (finrank)`) to `Fin 2` — det is preserved, so `χ` is unchanged
  set e : Fin (Module.finrank (ZMod p) (Fin 2 → ZMod p)) ≃ Fin 2 :=
    finCongr (Module.finrank_fin_fun (R := ZMod p)) with he
  set b₂ := (Module.finBasis (ZMod p) (Fin 2 → ZMod p)).reindex e with hb₂
  set Mr := LinearMap.BilinForm.toMatrix b₂ Bil with hMr
  have hMrsub : Mr = Mfin.submatrix e.symm e.symm := by
    ext i j
    rw [hMr, LinearMap.BilinForm.toMatrix_apply, Matrix.submatrix_apply, hMfin,
      LinearMap.BilinForm.toMatrix_apply, hb₂, Basis.reindex_apply, Basis.reindex_apply]
  have hMrdet : Mr.det = Mfin.det := by rw [hMrsub, Matrix.det_submatrix_equiv_self]
  -- change of basis between the two `Fin 2`-indexed bases: `Pᵀ · Mr · P = Mbf`
  set P := b₂.toMatrix (Pi.basisFun (ZMod p) (Fin 2)) with hP
  have hPne : P.det ≠ 0 := by
    intro h0
    have hmul : P.det * ((Pi.basisFun (ZMod p) (Fin 2)).toMatrix b₂).det = 1 := by
      rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    rw [h0, zero_mul] at hmul
    exact one_ne_zero hmul.symm
  have hcong : Pᵀ * Mr * P = Mbf :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b₂) (Pi.basisFun (ZMod p) (Fin 2)) Bil
  have hdet : Mbf.det = P.det ^ 2 * Mr.det := by
    rw [← hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hstep1 : χ Mfin.det = χ Mbf.det := by
    rw [hdet, ← hMrdet]; exact (hkill P.det Mr.det hPne).symm
  -- entrywise: `Mbf i j = ⅟2 · polar Q (a i) (a j)`
  have hentry : ∀ i j, Mbf i j = ⅟(2 : ZMod p) * QuadraticMap.polar Q (a i) (a j) := by
    intro i j
    rw [hMbf, LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    have hpolar : QuadraticMap.polar (configForm Q a) (Pi.single i 1) (Pi.single j 1)
        = 2 • Bil (Pi.single i 1) (Pi.single j 1) := by
      rw [hBil, ← QuadraticMap.polarBilin_apply_apply, ← two_nsmul_associated (S := ZMod p)]
      simp only [LinearMap.smul_apply]
    rw [polar_configForm_single] at hpolar
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hpolar
    rw [hpolar, ← mul_assoc, invOf_mul_self, one_mul]
  -- `det Mbf = (⅟2)² · det (config polar Gram) = (⅟2)² · pairForm`
  have hMbfdet : Mbf.det = (⅟(2 : ZMod p)) ^ 2
      * pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u) := by
    rw [← configPolarDet_eq_pairForm Q u t t₀]
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [hentry, Matrix.of_apply, ha]
    ring
  have h2ne : (⅟(2 : ZMod p)) ≠ 0 := by
    intro h0
    have hms := invOf_mul_self (2 : ZMod p)
    rw [h0, zero_mul] at hms
    exact one_ne_zero hms.symm
  have hstep2 : χ Mbf.det
      = χ (pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u)) := by
    rw [hMbfdet]; exact hkill _ _ h2ne
  exact hstep1.trans hstep2

/-- The quadratic character of a nonzero element is `±1` (its square is `1`, a domain has no other roots). -/
theorem chi_eq_one_or_neg_one {R' : Type*} [CommRing R'] [IsDomain R'] {x : ZMod p} (hx : x ≠ 0) :
    ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) x = 1
      ∨ ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R')) x = -1 := by
  set χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R') with hχ
  have hsq : (χ x) ^ 2 = 1 := by
    have h := quadraticChar_sq_one (F := ZMod p) hx
    have : (χ x) ^ 2 = ((1 : ℤ) : R') := by
      rw [hχ, MulChar.ringHomComp_apply, ← map_pow]; exact_mod_cast congrArg (Int.cast (R := R')) h
    simpa using this
  have hmm : χ x * χ x = 1 := by rw [← pow_two]; exact hsq
  exact mul_self_eq_one_iff.mp hmm

/-- **The ℂ-restated B1b (`chiSep_imp_zSep`) over a `CharZero` field.** The four-value distinctness of the closed
form `n + c·K·(q·b − 1)` (`c ∈ {±1}`, `b ∈ {0,1}`, `K ≠ 0`, `q > 2`), but stated over a `CharZero` field `F` (= ℂ),
so the `R' → ℕ` integrality descent is unnecessary — distinctness holds directly over `F`. The `q(bᵤ+bᵥ) − 2 ≠ 0`
step (which `omega` discharged over `ℤ`) is here a `CharZero` nat-cast argument (`q ≠ 1, 2`). -/
theorem chiSep_imp_zSep_field {F : Type*} [Field F] [CharZero F]
    {n K cu cv bu bv : F} {q : ℕ} (hq : 2 < q) (hK : K ≠ 0)
    (hbu : bu = 0 ∨ bu = 1) (hbv : bv = 0 ∨ bv = 1)
    (hcu : cu = 1 ∨ cu = -1) (hcv : cv = 1 ∨ cv = -1) (hne : cu ≠ cv) :
    n + cu * K * ((q : F) * bu - 1) ≠ n + cv * K * ((q : F) * bv - 1) := by
  have hcv' : cv = -cu := by rcases hcu with h | h <;> rcases hcv with h' | h' <;> simp_all
  have hcu0 : cu ≠ 0 := by rcases hcu with h | h <;> subst h <;> norm_num
  have hq2 : (q : F) ≠ 2 := by exact_mod_cast (by omega : q ≠ 2)
  have hq1 : (q : F) ≠ 1 := by exact_mod_cast (by omega : q ≠ 1)
  have hbb : (q : F) * (bu + bv) - 2 ≠ 0 := by
    rcases hbu with rfl | rfl <;> rcases hbv with rfl | rfl
    · have : (q : F) * (0 + 0) - 2 = -2 := by ring
      rw [this]; norm_num
    · have : (q : F) * (0 + 1) - 2 = (q : F) - 2 := by ring
      rw [this, sub_ne_zero]; exact hq2
    · have : (q : F) * (1 + 0) - 2 = (q : F) - 2 := by ring
      rw [this, sub_ne_zero]; exact hq2
    · have : (q : F) * (1 + 1) - 2 = 2 * ((q : F) - 1) := by ring
      rw [this]; exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr hq1)
  rw [← sub_ne_zero,
    show (n + cu * K * ((q : F) * bu - 1)) - (n + cv * K * ((q : F) * bv - 1))
        = cu * K * ((q : F) * (bu + bv) - 2) from by rw [hcv']; ring]
  exact mul_ne_zero (mul_ne_zero hcu0 hK) hbb

/-- **B1b in count form over a `CharZero` field — the per-pair bridge step.** Two pivots whose pair invariants `χ(I)`
differ (`hne`) have different joint isotropic counts at a sub-frame, given each point's closed form
`Z_w · q³ = n + χ_w·K·(q·b_w − 1)`. The ℂ analogue of `ScratchBridge.pairCount_ne_of_chiSep`. -/
theorem pairCount_ne_of_chiSep_field {F : Type*} [Field F] [CharZero F]
    {Zu Zv n K cu cv bu bv : F} {q : ℕ} (hq : 2 < q) (hK : K ≠ 0)
    (hbu : bu = 0 ∨ bu = 1) (hbv : bv = 0 ∨ bv = 1)
    (hcu : cu = 1 ∨ cu = -1) (hcv : cv = 1 ∨ cv = -1) (hne : cu ≠ cv)
    (hZu : Zu * (q : F) ^ 3 = n + cu * K * ((q : F) * bu - 1))
    (hZv : Zv * (q : F) ^ 3 = n + cv * K * ((q : F) * bv - 1)) :
    Zu ≠ Zv := by
  intro h
  exact chiSep_imp_zSep_field hq hK hbu hbv hcu hcv hne (by rw [← hZu, ← hZv, h])

open scoped Classical in
/-- **B1a final assembly — the observable per-pair closed form (corr = 0).** Combining wrap (i)
(`fullcount = jointIsoCount + corr`), wrap (ii) (`fullcount_pair_closed`), and wrap (iii)
(`chi_configDet_eq_chi_pairForm`): on the `corr = 0` locus (`hcorr`: not both config-differences isotropic), the
observable joint isotropic count over the sub-frame `{t,t₀}` satisfies
`jointIsoCount Q u {t,t₀} · p³ = |V| + χ(I_u(t))·K·(p·[Q w₀ = 0] − 1)`, `K = gaussSum²·∑ψ(Q)`,
`I_u(t) = det G₂(u;t,t₀) = pairForm Q (t̄₀−ū)(t̄−ū)`. This is the hypothesis `pairCount_ne_of_chiSep_field` consumes,
now with the pivot invariant `χ(pairForm)` (the quantity increments 3/4 separate on) in place of the opaque `χ(D)`. -/
theorem jointIsoCount_pair_closed_corr0 (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (u t t₀ : Fin (p ^ d)) (hd : Even d)
    (hG : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {F : Type*} [Field F] [CharZero F] {ψ : AddChar (ZMod p) F} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (hcorr : ¬ (Q (affineE.symm t - affineE.symm u) = 0 ∧ Q (affineE.symm t₀ - affineE.symm u) = 0)) :
    ∃ w₀ : Fin d → ZMod p,
      (jointIsoCount Q u {t, t₀} : F) * (p : F) ^ 3
        = (Fintype.card (Fin d → ZMod p) : F)
          + ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F))
              (pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u))
            * (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F)) ψ ^ 2
                * ∑ x : Fin d → ZMod p, ψ (Q x))
            * ((p : F) * (if Q w₀ = 0 then 1 else 0) - 1) := by
  obtain ⟨w₀, hfc⟩ := fullcount_pair_closed Q hF u t t₀ hd hG hψ vb hv hw
  refine ⟨w₀, ?_⟩
  -- the `y = 0` correction vanishes on the `corr = 0` locus
  have hcorr0 : (if ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
      Q (affineE.symm s - affineE.symm u) = 0 then 1 else 0) = (0 : ℕ) := by
    rw [if_neg]
    intro hall
    exact hcorr ⟨hall t (by simp), hall t₀ (by simp)⟩
  have hcard : (Finset.univ.filter (fun y : Fin d → ZMod p =>
      Q y = 0 ∧ ∀ s ∈ ({t, t₀} : Finset (Fin (p ^ d))),
        Q (y - (affineE.symm s - affineE.symm u)) = 0)).card
      = jointIsoCount Q u {t, t₀} := by
    rw [fullcount_eq_jointIsoCount_add_corr Q {t, t₀} u, hcorr0, add_zero]
  rw [hcard, chi_configDet_eq_chi_pairForm Q u t t₀] at hfc
  exact hfc

open scoped Classical in
/-- **THE BRIDGE, per-pair end-to-end (`χ(I)`-separation ⟹ `Z`-separation).** For two pivots `u ≠ v` and a sub-frame
`{t, t₀}`, on the config-nondegenerate (`hGu`/`hGv`), `corr = 0` (`hcorru`/`hcorrv`) locus: if the pair invariants
`χ(det G₂) = χ(pairForm)` differ at the two pivots (`hne` — the increment-4 separation output), then the joint
isotropic counts differ (`jointIsoCount Q u {t,t₀} ≠ jointIsoCount Q v {t,t₀}`). This is exactly the per-pair input
to `ScratchBridgeZ.zProfileSeparates_of_zSep`, completing the observable↔count bridge over `F = ℂ`.

The Gauss-factor nonvanishing `gaussSum²·∑ψ(Q) ≠ 0` is now **discharged internally** (no longer a hypothesis):
`gaussSum² = χ(-1)·card K ≠ 0` (`gaussSum_sq_ne_zero`) and `∑ψ(Q) = (∏ χ(Q vᵢ))·gaussSumᵈ ≠ 0`
(`sum_addChar_quadForm_ne_zero`, from the anisotropic basis `vb`/`hv`/`hw`). -/
theorem jointIsoCount_ne_of_chiSep_pair (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    [Invertible (2 : ZMod p)] (hF : ringChar (ZMod p) ≠ 2)
    (u v t t₀ : Fin (p ^ d)) (hd : Even d)
    (hGu : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] i)
        (![affineE.symm t - affineE.symm u, affineE.symm t₀ - affineE.symm u] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    (hGv : IsUnit (Matrix.of (fun i j => QuadraticMap.polar Q
        (![affineE.symm t - affineE.symm v, affineE.symm t₀ - affineE.symm v] i)
        (![affineE.symm t - affineE.symm v, affineE.symm t₀ - affineE.symm v] j)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det)
    {F : Type*} [Field F] [CharZero F] {ψ : AddChar (ZMod p) F} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank (ZMod p) (Fin d → ZMod p))) (ZMod p) (Fin d → ZMod p))
    (hv : (QuadraticMap.associated (R := ZMod p) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (hcorru : ¬ (Q (affineE.symm t - affineE.symm u) = 0 ∧ Q (affineE.symm t₀ - affineE.symm u) = 0))
    (hcorrv : ¬ (Q (affineE.symm t - affineE.symm v) = 0 ∧ Q (affineE.symm t₀ - affineE.symm v) = 0))
    (hne : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F))
            (pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u))
          ≠ ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F))
            (pairForm Q (affineE.symm t₀ - affineE.symm v) (affineE.symm t - affineE.symm v))) :
    jointIsoCount Q u {t, t₀} ≠ jointIsoCount Q v {t, t₀} := by
  -- the carried Gauss-factor nonvanishing `hK` is discharged from `hF`/`hψ` + the anisotropic basis `vb`
  have hK : gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F)) ψ ^ 2
      * ∑ x : Fin d → ZMod p, ψ (Q x) ≠ 0 :=
    mul_ne_zero (gaussSum_sq_ne_zero hF hψ) (sum_addChar_quadForm_ne_zero hF hψ Q vb hv hw)
  -- `q = p > 2` (p odd prime)
  have hp2 : p ≠ 2 := by rw [ZMod.ringChar_zmod_n p] at hF; exact hF
  have hq : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  -- `χ(pairForm) ∈ {±1}` from config-nondegeneracy
  have hpu : pairForm Q (affineE.symm t₀ - affineE.symm u) (affineE.symm t - affineE.symm u) ≠ 0 := by
    have h := hGu; rw [configPolarDet_eq_pairForm Q u t t₀] at h; exact h.ne_zero
  have hpv : pairForm Q (affineE.symm t₀ - affineE.symm v) (affineE.symm t - affineE.symm v) ≠ 0 := by
    have h := hGv; rw [configPolarDet_eq_pairForm Q v t t₀] at h; exact h.ne_zero
  have hcu := chi_eq_one_or_neg_one (R' := F) hpu
  have hcv := chi_eq_one_or_neg_one (R' := F) hpv
  -- the per-pivot closed forms
  obtain ⟨wu, hu⟩ := jointIsoCount_pair_closed_corr0 Q hF u t t₀ hd hGu hψ vb hv hw hcorru
  obtain ⟨wv, hvv⟩ := jointIsoCount_pair_closed_corr0 Q hF v t t₀ hd hGv hψ vb hv hw hcorrv
  have hbu : (if Q wu = 0 then (1 : F) else 0) = 0 ∨ (if Q wu = 0 then (1 : F) else 0) = 1 := by
    split_ifs; exacts [Or.inr rfl, Or.inl rfl]
  have hbv : (if Q wv = 0 then (1 : F) else 0) = 0 ∨ (if Q wv = 0 then (1 : F) else 0) = 1 := by
    split_ifs; exacts [Or.inr rfl, Or.inl rfl]
  intro hjeq
  exact pairCount_ne_of_chiSep_field hq hK hbu hbv hcu hcv hne hu hvv (by exact_mod_cast hjeq)


end ChainDescent

--#print axioms ChainDescent.levelset_count_collapse
--#print axioms ChainDescent.fullcount_eq_jointIsoCount_add_corr
--#print axioms ChainDescent.fullcount_pair_eq_levelset
--#print axioms ChainDescent.fullcount_pair_closed
--#print axioms ChainDescent.configPolarDet_eq_pairForm
--#print axioms ChainDescent.chi_configDet_eq_chi_pairForm
--#print axioms ChainDescent.chiSep_imp_zSep_field
--#print axioms ChainDescent.pairCount_ne_of_chiSep_field
--#print axioms ChainDescent.jointIsoCount_pair_closed_corr0
--#print axioms ChainDescent.jointIsoCount_ne_of_chiSep_pair
