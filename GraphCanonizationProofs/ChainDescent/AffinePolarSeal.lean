/-
# Increment 5 — the matching assembly (`c̄₀ < 1` ⟹ a separating base ⟹ `zSep` ⟹ seal).

The final wiring of the affine-polar `VO^ε` seal in the regime the landed increment-4 inputs support
(`q ≳ 32 d`, hence `q ≥ 256` for the lead `d`): the per-good-anchor fail bound `c = 15/16·|V|`
(`good_anchor_fail_le_const`) plus the bad-anchor density `β = O(d/q)` (`beta_full_count_closed`) give
`c̄₀ = c/|V| + β/|V| < 1`; the matching trick (`exists_separating_base`) then turns that into a base whose
2-element sub-frames separate every pair in the joint isotropic counts (`zSep`), discharging
`ZProfileSeparatesK` → `IsotropySeparatesAtBaseK` → the seal.

This file starts with the scope-independent **ℕ-smallness helper** feeding `exists_separating_base`'s `hlt`.

NOTE (scope): the matching has an INDEPENDENT `q`-floor from the isotropic-shell counts `#{I_u=0}+#{I_v=0}`,
which `good_anchor_fail_le` folds into `c` and `good_anchor_fail_le_const` controls only via the loose
`zeroCountShift_card_le` (`q ≥ 256`). The small-`q` per-anchor tail (`c0_le_route2`) tightens `NS` but does
NOT remove the shell overhead, so it does not lower this matching's floor; that is a separate follow-up.

Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build.
-/
import ChainDescent.Matching
import ChainDescent.BadAnchorCount
import ChainDescent.GoodAnchorNonvacuity
import ChainDescent.ObservableCountBridgeK
import ChainDescent.FieldGeneric

namespace ChainDescent

open Finset

/-- **ℕ-smallness helper for the matching trick.** If the per-target fail count `F` is strictly below the
anchor-space size `|W|`, then for some base length `m` the matching inequality `|ι|·Fᵐ < |W|ᵐ` holds — exactly
`exists_separating_base`'s `hlt`. (Real proof: `F/|W| < 1` ⟹ `(|W|/F)ᵐ → ∞`, so `|ι| < (|W|/F)ᵐ` eventually.) -/
theorem exists_pow_matching_lt {ι W : Type*} [Fintype ι] [Fintype W] (F : ℕ)
    (hF : F < Fintype.card W) :
    ∃ m : ℕ, Fintype.card ι * F ^ m < Fintype.card W ^ m := by
  have hw : 0 < Fintype.card W := lt_of_le_of_lt (Nat.zero_le F) hF
  rcases Nat.eq_zero_or_pos F with hF0 | hFpos
  · refine ⟨1, ?_⟩
    subst hF0
    simpa using hw
  · have hFR : (0 : ℝ) < F := by exact_mod_cast hFpos
    have hr : (1 : ℝ) < (Fintype.card W : ℝ) / F :=
      (one_lt_div hFR).2 (by exact_mod_cast hF)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Fintype.card ι : ℝ) hr
    refine ⟨m, ?_⟩
    rw [div_pow, lt_div_iff₀ (pow_pos hFR m)] at hm
    exact_mod_cast hm

/-- **The matching length is logarithmic — explicit bound.** Refines `exists_pow_matching_lt` with
`m ≤ log|ι| / log(|W|/F) + 1`. (The base size `≤ 2m` is then `O(log|ι|/δ)` once `|W|/F ≥ 1/c̄₀` is bounded away
from `1`.) Proof: `m := ⌊L⌋₊ + 1` for `L = log|ι|/log(|W|/F)`; `m > L ⟹ (|W|/F)^m > |ι| ⟹ |ι|·F^m < |W|^m`. -/
theorem exists_pow_matching_le {ι W : Type*} [Fintype ι] [Fintype W] (F : ℕ)
    (hF : F < Fintype.card W) (hι : 0 < Fintype.card ι) :
    ∃ m : ℕ,
      (m : ℝ) ≤ Real.log (Fintype.card ι) / Real.log (Fintype.card W / F) + 1
        ∧ Fintype.card ι * F ^ m < Fintype.card W ^ m := by
  have hWpos : 0 < Fintype.card W := lt_of_le_of_lt (Nat.zero_le F) hF
  rcases Nat.eq_zero_or_pos F with hF0 | hFpos
  · subst hF0
    refine ⟨1, ?_, ?_⟩
    · simp [Real.log_zero]
    · simpa using hWpos
  · have hFR : (0 : ℝ) < F := by exact_mod_cast hFpos
    have hιR : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hι
    have hr : (1 : ℝ) < (Fintype.card W : ℝ) / F := (one_lt_div hFR).2 (by exact_mod_cast hF)
    have hlogr : 0 < Real.log ((Fintype.card W : ℝ) / F) := Real.log_pos hr
    have hlogι : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg hιR
    set L := Real.log (Fintype.card ι) / Real.log ((Fintype.card W : ℝ) / F) with hLdef
    have hLnn : 0 ≤ L := div_nonneg hlogι hlogr.le
    refine ⟨⌊L⌋₊ + 1, ?_, ?_⟩
    · have := Nat.floor_le hLnn
      push_cast; linarith
    · set m := ⌊L⌋₊ + 1 with hmdef
      have hmR : (m : ℝ) = (⌊L⌋₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
      have hLm : L < (m : ℝ) := by rw [hmR]; exact Nat.lt_floor_add_one L
      have heq : L * Real.log ((Fintype.card W : ℝ) / F) = Real.log (Fintype.card ι) := by
        rw [hLdef]; exact div_mul_cancel₀ _ (ne_of_gt hlogr)
      have hlog : Real.log (Fintype.card ι) < (m : ℝ) * Real.log ((Fintype.card W : ℝ) / F) := by
        rw [← heq]; exact mul_lt_mul_of_pos_right hLm hlogr
      have hlog2 : Real.log (Fintype.card ι) < Real.log (((Fintype.card W : ℝ) / F) ^ m) := by
        rw [Real.log_pow]; exact hlog
      have hpow : (Fintype.card ι : ℝ) < ((Fintype.card W : ℝ) / F) ^ m :=
        (Real.log_lt_log_iff (by linarith) (by positivity)).mp hlog2
      rw [div_pow, lt_div_iff₀ (by positivity : (0:ℝ) < (F:ℝ)^m)] at hpow
      exact_mod_cast hpow

/-- **The matching length is logarithmic — log-free block bound.** From the *ratio* hypothesis `64·F ≤ 63·|W|`
(i.e. `F/|W| ≤ 63/64`), the matching inequality holds with `m = 64·(Nat.log 2 |ι| + 1) = O(log|ι|)`, stated with
`Nat.log` (no `Real.log`). Proof: the block fact `2·63⁶⁴ ≤ 64⁶⁴` gives `2·F⁶⁴ ≤ |W|⁶⁴`; raising to
`k = Nat.log 2 |ι| + 1` gives `2ᵏ·F^(64k) ≤ |W|^(64k)`, and `|ι| < 2ᵏ` (`Nat.lt_pow_succ_log_self`). -/
theorem exists_pow_matching_block {ι W : Type*} [Fintype ι] [Fintype W] (F : ℕ)
    (hF63 : 64 * F ≤ 63 * Fintype.card W) (hWpos : 0 < Fintype.card W) :
    ∃ m : ℕ, m ≤ 64 * (Nat.log 2 (Fintype.card ι) + 1)
      ∧ Fintype.card ι * F ^ m < Fintype.card W ^ m := by
  set W' := Fintype.card W with hW'def
  set k := Nat.log 2 (Fintype.card ι) + 1 with hkdef
  refine ⟨64 * k, le_refl _, ?_⟩
  have hιlt : Fintype.card ι < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) _
  -- block inequality: `2·F⁶⁴ ≤ W'⁶⁴`
  have hblock : 2 * F ^ 64 ≤ W' ^ 64 := by
    have h1 : (64 * F) ^ 64 ≤ (63 * W') ^ 64 := Nat.pow_le_pow_left hF63 64
    have hconst : 2 * 63 ^ 64 ≤ 64 ^ 64 := by norm_num
    have h2 : 2 * 64 ^ 64 * F ^ 64 ≤ 64 ^ 64 * W' ^ 64 := by
      calc 2 * 64 ^ 64 * F ^ 64 = 2 * (64 * F) ^ 64 := by rw [mul_pow]; ring
        _ ≤ 2 * (63 * W') ^ 64 := Nat.mul_le_mul (le_refl 2) h1
        _ = (2 * 63 ^ 64) * W' ^ 64 := by rw [mul_pow]; ring
        _ ≤ 64 ^ 64 * W' ^ 64 := Nat.mul_le_mul hconst (le_refl _)
    have hpos : 0 < 64 ^ 64 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 64 ^ 64 * (2 * F ^ 64) = 2 * 64 ^ 64 * F ^ 64 := by ring
      _ ≤ 64 ^ 64 * W' ^ 64 := h2
  -- raise to the `k`-th power: `2ᵏ·F^(64k) ≤ W'^(64k)`
  have hpow : (2 * F ^ 64) ^ k ≤ (W' ^ 64) ^ k := Nat.pow_le_pow_left hblock k
  rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
  rcases Nat.eq_zero_or_pos F with hF0 | hFpos
  · subst hF0
    have hmpos : 0 < 64 * k := by positivity
    rw [Nat.zero_pow hmpos, mul_zero]
    exact pow_pos hWpos _
  · calc Fintype.card ι * F ^ (64 * k)
        < 2 ^ k * F ^ (64 * k) := mul_lt_mul_of_pos_right hιlt (pow_pos hFpos _)
      _ ≤ W' ^ (64 * k) := hpow

/-- **The matching mechanics, packaged.** Given a per-pair fail predicate `Fail g t t₀` over probe `t` and anchor
`t₀`, with a uniform per-good-anchor probe-fail bound `cN`, a uniform bad-anchor count bound `βN`, and the
`c̄₀ < 1` condition `cN + βN < |V|`, there is a base `P : Fin m → V × V` such that every target `g` has a
base-pair `P j = (t, t₀)` it does NOT fail. Pure matching-trick assembly: `matching_F_bound` →
`exists_pow_matching_lt` → `exists_separating_base` over `W = V × V`. -/
theorem exists_separating_base_of_split
    {ι : Type*} [Fintype ι] {V : Type*} [Fintype V] [DecidableEq V]
    (Fail : ι → V → V → Prop) [∀ g t₀, DecidablePred (fun t => Fail g t t₀)]
    (Good : ι → V → Prop) [∀ g, DecidablePred (Good g)] (cN βN : ℕ)
    (hc : ∀ g t₀, Good g t₀ → (Finset.univ.filter (fun t => Fail g t t₀)).card ≤ cN)
    (hβ : ∀ g, (Finset.univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN)
    (hlt : cN + βN < Fintype.card V) :
    ∃ (m : ℕ) (P : Fin m → V × V), ∀ g : ι, ∃ j, ¬ Fail g (P j).1 (P j).2 := by
  classical
  have hvpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hFlt : cN * Fintype.card V + Fintype.card V * βN < Fintype.card (V × V) := by
    rw [Fintype.card_prod]
    calc cN * Fintype.card V + Fintype.card V * βN
        = Fintype.card V * (cN + βN) := by ring
      _ < Fintype.card V * Fintype.card V := mul_lt_mul_of_pos_left hlt hvpos
  obtain ⟨m, hm⟩ := exists_pow_matching_lt (ι := ι) (W := V × V)
    (cN * Fintype.card V + Fintype.card V * βN) hFlt
  have hFbound := matching_F_bound (fun g a b => Fail g a b) (fun g b => Good g b) cN βN hc hβ
  obtain ⟨P, hP⟩ := exists_separating_base (fun (g : ι) (w : V × V) => Fail g w.1 w.2) m
    (cN * Fintype.card V + Fintype.card V * βN) (fun g => hFbound g) hm
  exact ⟨m, P, hP⟩

/-- **The matching mechanics with a logarithmic base bound.** The `exists_separating_base_of_split` sibling that
carries `m ≤ 64·(Nat.log 2 |ι| + 1)`, from the *ratio* hypothesis `64·(cN+βN) ≤ 63·|V|` (strictly stronger than
`cN+βN < |V|`). Routes through `exists_pow_matching_block` over `W = V × V` (so `64·F ≤ 63·|W|` reduces to the
ratio after factoring `|V|`), giving the base size `≤ 2m = O(log|ι|)` once threaded. -/
theorem exists_separating_base_of_split_bounded
    {ι : Type*} [Fintype ι] {V : Type*} [Fintype V] [DecidableEq V]
    (Fail : ι → V → V → Prop) [∀ g t₀, DecidablePred (fun t => Fail g t t₀)]
    (Good : ι → V → Prop) [∀ g, DecidablePred (Good g)] (cN βN : ℕ)
    (hc : ∀ g t₀, Good g t₀ → (Finset.univ.filter (fun t => Fail g t t₀)).card ≤ cN)
    (hβ : ∀ g, (Finset.univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN)
    (hle : 64 * (cN + βN) ≤ 63 * Fintype.card V) (hVpos : 0 < Fintype.card V) :
    ∃ (m : ℕ) (P : Fin m → V × V),
      m ≤ 64 * (Nat.log 2 (Fintype.card ι) + 1)
        ∧ ∀ g : ι, ∃ j, ¬ Fail g (P j).1 (P j).2 := by
  classical
  have hF63 : 64 * (cN * Fintype.card V + Fintype.card V * βN)
      ≤ 63 * Fintype.card (V × V) := by
    rw [Fintype.card_prod]
    calc 64 * (cN * Fintype.card V + Fintype.card V * βN)
        = Fintype.card V * (64 * (cN + βN)) := by ring
      _ ≤ Fintype.card V * (63 * Fintype.card V) := Nat.mul_le_mul (le_refl _) hle
      _ = 63 * (Fintype.card V * Fintype.card V) := by ring
  have hWVpos : 0 < Fintype.card (V × V) := by
    rw [Fintype.card_prod]; exact Nat.mul_pos hVpos hVpos
  obtain ⟨m, hmle, hm⟩ := exists_pow_matching_block (ι := ι) (W := V × V)
    (cN * Fintype.card V + Fintype.card V * βN) hF63 hWVpos
  have hFbound := matching_F_bound (fun g a b => Fail g a b) (fun g b => Good g b) cN βN hc hβ
  obtain ⟨P, hP⟩ := exists_separating_base (fun (g : ι) (w : V × V) => Fail g w.1 w.2) m
    (cN * Fintype.card V + Fintype.card V * βN) (fun g => hFbound g) hm
  exact ⟨m, P, hmle, hP⟩

/-- **The `c̄₀ < 1` arithmetic.** From the good-anchor fail bound `16·cN ≤ 15·N` (i.e. `cN ≤ 15/16·N`) and the
bad-anchor density `q·βN ≤ (2d+4)·N + 2·q` (i.e. `βN ≤ (2d+4)·N/q + 2`), with `q ≥ 32·(2d+4)` and `N > 64`,
the matching threshold `cN + βN < N` holds. Proved over `ℝ` (multiply by `16q`) then cast back. -/
theorem cbar_lt {N q d cN βN : ℕ}
    (h16 : 16 * cN ≤ 15 * N) (hqβ : q * βN ≤ (2 * d + 4) * N + 2 * q)
    (hqthr : 32 * (2 * d + 4) ≤ q) (hNthr : 64 < N) (hqpos : 0 < q) :
    cN + βN < N := by
  have h16' : (16 : ℝ) * cN ≤ 15 * N := by exact_mod_cast h16
  have hqβ' : (q : ℝ) * βN ≤ (2 * d + 4) * N + 2 * q := by exact_mod_cast hqβ
  have hqthr' : (32 : ℝ) * (2 * d + 4) ≤ q := by exact_mod_cast hqthr
  have hNthr' : (64 : ℝ) < N := by exact_mod_cast hNthr
  have hqpos' : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hNpos' : (0 : ℝ) < N := by linarith
  have goalR : (cN : ℝ) + βN < N := by
    nlinarith [h16', hqβ', hqthr', hNthr', hqpos', hNpos',
      mul_le_mul_of_nonneg_left h16' hqpos'.le,
      mul_le_mul_of_nonneg_right hqthr' hNpos'.le,
      mul_lt_mul_of_pos_right hNthr' hqpos']
  exact_mod_cast goalR

open QuadraticMap in
/-- **Piece 3 — bridge wiring: the separation event fires the count inequality.** If at the sub-frame `{t, t₀}`
the two pair invariants have different (ℤ-valued) quadratic characters, both config invariants are nonzero, and
the anchor is `Q`-nondegenerate at both `u, v` (`Q(t₀-u), Q(t₀-v) ≠ 0`), then the joint isotropic counts differ.
Repackages `ScratchBridgeAllK.jointIsoCountK_ne_of_chiSep_pair`: `I≠0 ⟹` config Gram unit
(`configPolarDet_eq_pairFormK`+`isUnit_iff_ne_zero`); `Q(t₀-·)≠0 ⟹ hcorr`; ℤ-`χ`-inequality casts to `R'`. -/
theorem jointIsoCountK_ne_of_sep {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (u v t t₀ : Fin d → K)
    (hIu : pairForm Q (t₀ - u) (t - u) ≠ 0) (hIv : pairForm Q (t₀ - v) (t - v) ≠ 0)
    (hQu : Q (t₀ - u) ≠ 0) (hQv : Q (t₀ - v) ≠ 0)
    (hchi : quadraticChar K (pairForm Q (t₀ - u) (t - u))
          ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))) :
    jointIsoCountK Q u {t, t₀} ≠ jointIsoCountK Q v {t, t₀} := by
  refine jointIsoCountK_ne_of_chiSep_pair Q hF hcardK u v t t₀ hd ?_ ?_ hψ vb hv hw ?_ ?_ ?_
  · rw [configPolarDet_eq_pairFormK Q u t t₀]; exact isUnit_iff_ne_zero.mpr hIu
  · rw [configPolarDet_eq_pairFormK Q v t t₀]; exact isUnit_iff_ne_zero.mpr hIv
  · exact fun h => hQu h.2
  · exact fun h => hQv h.2
  · intro heq
    rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, eq_intCast, eq_intCast] at heq
    exact hchi (by exact_mod_cast heq)

open QuadraticMap in
/-- **Piece 5 — the family assembly: a bounded base whose joint isotropic counts separate every pair.**
For a nondegenerate quadratic form `Q` on `Fin d → K` (even `d`), with the family thresholds `q ≳ 32d`, `q ≥ 256`,
the matching trick produces a finite base `T` with `ZProfileSeparatesK Q T`. Wires: `good_anchor_fail_le_const`
(input `c = 15/16·|V|`) + `beta_full_count_closed`/`exists_hgood` (bad-anchor `β = O(d/q)`) + `cbar_lt` (`c̄₀<1`)
→ `exists_separating_base_of_split` → `jointIsoCountK_ne_of_sep` per pair → `zProfileSeparatesK_of_zSep`. -/
theorem exists_zProfileSeparatesK {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card (Fin d → K))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K) (hq3 : 256 ≤ (Fintype.card K : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card K)
    (_hNthr : 64 < Fintype.card (Fin d → K)) :
    ∃ T : Finset (Fin d → K),
      T.card ≤ 128 * (Nat.log 2 (Fintype.card (Fin d → K) ^ 2) + 1)
        ∧ ZProfileSeparatesK Q T := by
  classical
  set V := Fin d → K
  set cardV := Fintype.card V with hcardVdef
  set cardK := Fintype.card K with hcardKdef
  -- threshold consequences in ℕ
  have h256 : (256 : ℕ) ≤ cardK := by rw [hcardKdef]; exact_mod_cast hq3
  have hcardK7 : 7 ≤ cardK := by omega
  have hcardK2 : 2 < cardK := by omega
  have hKpos : 0 < cardK := by omega
  have hfinrank : 2 ≤ Module.finrank K V := by
    have : Module.finrank K V = d := by
      show Module.finrank K (Fin d → K) = d
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hsepL : (QuadraticMap.associated Q).SeparatingLeft := associated_separatingLeft_of_polarRad Q hQrad
  obtain ⟨vb, hv, hw⟩ := exists_orthoAnisotropic_basis Q hsepL
  -- Nontrivial V (for exists_anisotropic)
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial V := by
    show Nontrivial (Fin d → K); infer_instance
  obtain ⟨w₀, hw₀⟩ := exists_anisotropic Q hQrad
  let b : Module.Basis (Fin d) K V := Pi.basisFun K (Fin d)
  -- the matching predicates
  set Good : {p : V × V // p.1 ≠ p.2} → V → Prop := fun g t₀ =>
    (∀ y z : K, y ≠ 0 → z ≠ 0 → y • pairForm Q (t₀ - g.1.1) + z • pairForm Q (t₀ - g.1.2) ≠ 0)
      ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - g.1.1) + z • pairForm Q (t₀ - g.1.2)) = ⊥)
      ∧ pairForm Q (t₀ - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) ≠ 0
      ∧ Q (t₀ - g.1.1) ≠ 0 ∧ Q (t₀ - g.1.2) ≠ 0 with hGoodDef
  set Fail : {p : V × V // p.1 ≠ p.2} → V → V → Prop := fun g t t₀ =>
    ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
          ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
        ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0
        ∧ Q (t₀ - g.1.1) ≠ 0 ∧ Q (t₀ - g.1.2) ≠ 0) with hFailDef
  set cN : ℕ := 15 * cardV / 16 with hcNdef
  set βN : ℕ := ((2 * d + 4) * cardV + 2 * cardK) / cardK with hβNdef
  -- hc : per-good-anchor fail bound
  have hc : ∀ g t₀, Good g t₀ → (Finset.univ.filter (fun t => Fail g t t₀)).card ≤ cN := by
    intro g t₀ hG
    obtain ⟨hnz, hgood, hPu, hPv, hQu0, hQv0⟩ := hG
    have hsetEq : (Finset.univ.filter (fun t => Fail g t t₀))
        = (Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))) := by
      apply Finset.filter_congr
      intro t _
      simp only [hFailDef, not_iff_not]
      constructor
      · rintro ⟨h1, h2, h3, _, _⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, hQu0, hQv0⟩
    rw [hsetEq]
    have hreal := good_anchor_fail_le_const (b := b) hF hψ Q g.1.1 g.1.2 t₀ hnz hgood hPu hPv hq1 hq2 hq3
    -- (#fail : ℝ) ≤ 15/16·cardV ⟹ #fail ≤ (15·cardV)/16 (ℕ)
    have h16 : 16 * (Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))).card
        ≤ 15 * cardV := by
      have : (16 : ℝ) * ((Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))).card : ℝ)
          ≤ 15 * cardV := by rw [hcardVdef]; linarith [hreal]
      exact_mod_cast this
    rw [hcNdef]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith [h16])
  -- hβ : bad-anchor count bound
  have hβ : ∀ g, (Finset.univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN := by
    intro g
    obtain ⟨t₀₀, y₀, z₀, hrad, _, _⟩ := exists_hgood Q hQrad g.1.1 g.1.2 g.2 hfinrank hcardK7
    have hbeta := beta_full_count_closed (b := b) Q y₀ z₀ g.1.1 g.1.2 t₀₀ w₀ hrad hw₀
    rw [hβNdef]
    refine (Nat.le_div_iff_mul_le hKpos).mpr ?_
    refine le_trans (le_of_eq ?_) hbeta
    congr 1
  -- hVpos and `128 ≤ |V|` (from hq1 + hq3), feeding the ratio bound
  have hVpos : 0 < cardV := by rw [hcardVdef]; exact Fintype.card_pos
  have hcardV128 : 128 ≤ cardV := by
    have hR : (128 : ℝ) ≤ (cardV : ℝ) := by
      rw [hcardVdef]; nlinarith [hq1, hq3, sq_nonneg ((cardK : ℝ) - 256)]
    exact_mod_cast hR
  -- hle : 64·(cN+βN) ≤ 63·|V|  (the ratio form of c̄₀ < 1, needed for the log base bound)
  have hA : 16 * cN ≤ 15 * cardV := by rw [hcNdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hB : cardK * βN ≤ (2 * d + 4) * cardV + 2 * cardK := by
    rw [hβNdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hle : 64 * (cN + βN) ≤ 63 * cardV := by
    have h64cN : 64 * cN ≤ 60 * cardV := by omega
    have h64βN : 64 * βN ≤ 2 * cardV + 128 := by
      have step2 : 64 * ((2 * d + 4) * cardV) ≤ 2 * cardV * cardK := by
        calc 64 * ((2 * d + 4) * cardV) = 2 * cardV * (32 * (2 * d + 4)) := by ring
          _ ≤ 2 * cardV * cardK := Nat.mul_le_mul (le_refl _) hqthr
      have step3 : (64 * βN) * cardK ≤ (2 * cardV + 128) * cardK := by
        calc (64 * βN) * cardK = 64 * (cardK * βN) := by ring
          _ ≤ 64 * ((2 * d + 4) * cardV + 2 * cardK) := Nat.mul_le_mul (le_refl _) hB
          _ = 64 * ((2 * d + 4) * cardV) + 128 * cardK := by ring
          _ ≤ 2 * cardV * cardK + 128 * cardK := Nat.add_le_add_right step2 _
          _ = (2 * cardV + 128) * cardK := by ring
      exact Nat.le_of_mul_le_mul_right step3 hKpos
    omega
  -- run the matching (bounded variant carries `m ≤ 64·(log₂|ι| + 1)`)
  obtain ⟨m, P, hmle, hP⟩ := exists_separating_base_of_split_bounded Fail Good cN βN hc hβ hle hVpos
  refine ⟨(Finset.univ.image (fun j => (P j).1)) ∪ (Finset.univ.image (fun j => (P j).2)), ?_, ?_⟩
  · -- base-size bound: T.card ≤ 2m ≤ 128·(log₂|ι| + 1) ≤ 128·(log₂|V|² + 1)
    have hcardι_le : Fintype.card {p : V × V // p.1 ≠ p.2} ≤ cardV ^ 2 := by
      have h1 : Fintype.card {p : V × V // p.1 ≠ p.2} ≤ Fintype.card (V × V) := Fintype.card_subtype_le _
      rw [Fintype.card_prod, ← hcardVdef] at h1
      calc Fintype.card {p : V × V // p.1 ≠ p.2} ≤ cardV * cardV := h1
        _ = cardV ^ 2 := (pow_two cardV).symm
    have him1 : (Finset.univ.image (fun j => (P j).1)).card ≤ m := by
      refine le_trans Finset.card_image_le ?_; rw [Finset.card_univ, Fintype.card_fin]
    have him2 : (Finset.univ.image (fun j => (P j).2)).card ≤ m := by
      refine le_trans Finset.card_image_le ?_; rw [Finset.card_univ, Fintype.card_fin]
    calc ((Finset.univ.image (fun j => (P j).1)) ∪ (Finset.univ.image (fun j => (P j).2))).card
        ≤ (Finset.univ.image (fun j => (P j).1)).card
            + (Finset.univ.image (fun j => (P j).2)).card := Finset.card_union_le _ _
      _ ≤ 2 * m := by omega
      _ ≤ 2 * (64 * (Nat.log 2 (Fintype.card {p : V × V // p.1 ≠ p.2}) + 1)) :=
          Nat.mul_le_mul (le_refl _) hmle
      _ = 128 * (Nat.log 2 (Fintype.card {p : V × V // p.1 ≠ p.2}) + 1) := by ring
      _ ≤ 128 * (Nat.log 2 (cardV ^ 2) + 1) :=
          Nat.mul_le_mul (le_refl _) (Nat.add_le_add_right (Nat.log_mono_right hcardι_le) 1)
  · -- zSep ⟹ ZProfileSeparatesK
    apply zProfileSeparatesK_of_zSep
    intro u u' hne
    obtain ⟨j, hj⟩ := hP ⟨(u, u'), hne⟩
    rw [hFailDef] at hj
    simp only [not_not] at hj
    obtain ⟨hchi, hIu, hIv, hQu, hQv⟩ := hj
    refine ⟨{(P j).1, (P j).2}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> subst hx
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
    · exact jointIsoCountK_ne_of_sep Q hF hcardK2 hd hψ vb hv hw u u' (P j).1 (P j).2 hIu hIv hQu hQv hchi

open QuadraticMap in
/-- **Increment 5, the seal-ready deliverable.** The matching base `T` of `exists_zProfileSeparatesK` discharges the
Witt-free seal input `IsotropySeparatesAtBaseK Q T` (via `isotropySeparatesK_of_zProfileSeparatesK`, needing only
`Q.polarBilin` nondegenerate). So the affine-polar `VO^ε` residue at `q ≳ 32d` has a finite separating base whose
fine isotropy-count profile pins every vertex — the predicate the Witt-free capstone
`reachesRigidOrCameron_viaIsotropySeparatesK_wittFree` consumes (modulo mapping `T` through `affineE`). The base is
logarithmic — `T.card ≤ 128·(log₂|V|² + 1) = O(d log q)` — exposed via `exists_separating_base_of_split_bounded`. -/
theorem exists_isotropySeparatesAtBaseK {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥) (hQnd : (Q.polarBilin).Nondegenerate)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card (Fin d → K))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K) (hq3 : 256 ≤ (Fintype.card K : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card K)
    (hNthr : 64 < Fintype.card (Fin d → K)) :
    ∃ T : Finset (Fin d → K),
      T.card ≤ 128 * (Nat.log 2 (Fintype.card (Fin d → K) ^ 2) + 1)
        ∧ IsotropySeparatesAtBaseK Q T := by
  obtain ⟨T, hTcard, hT⟩ := exists_zProfileSeparatesK Q hF hd hdge hψ hQrad hq1 hq2 hq3 hqthr hNthr
  exact ⟨T, hTcard, isotropySeparatesK_of_zProfileSeparatesK Q hQnd hT⟩

open QuadraticMap in
/-- **Piece 6 — the q = p seal.** The matching base of `exists_isotropySeparatesAtBaseK`, transported through the
digit bijection `affineE`, feeds the Witt-free seal capstone: for an odd prime `p` and a nondegenerate `Q` on
`Fin d → ZMod p` with the family thresholds (`p ≥ 256`, `p ≳ 32d`), the affine-polar `VO^ε` residue **reaches
`reachesRigidOrCameron` modulo `{G3}`** — no Witt, no `hSmallAutThin`. The base is `T = (matching base).image affineE`
and the depth bound is `T.card`, now **explicitly carried as logarithmic**:
`T.card ≤ 128·(log₂(|points|²) + 1) = O(d log p)` (`|points| = p^d`), via the matching keystone
`exists_pow_matching_block`. So the seal is non-vacuous — a genuine **quasipolynomial** WL-base for this slice. -/
theorem reachesRigidOrCameron_affinePolar {p d : ℕ} [Fact p.Prime]
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hp2 : p ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥) (hQnd : (Q.polarBilin).Nondegenerate)
    (hq1 : 64 * (Fintype.card (ZMod p) : ℝ) ^ 2 ≤ Fintype.card (Fin d → ZMod p))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card (ZMod p))
    (hq3 : 256 ≤ (Fintype.card (ZMod p) : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card (ZMod p))
    (hNthr : 64 < Fintype.card (Fin d → ZMod p)) :
    ∃ T : Finset (Fin (p ^ d)),
      T.card ≤ 128 * (Nat.log 2 (Fintype.card (Fin d → ZMod p) ^ 2) + 1)
        ∧ (((SchemeBlockRecovered (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))
            ∨ AbelianConsumed (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)))
            ∨ SchemeRecoveredByDepth (p ^ d)
                (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) T.card)
          ∨ IsCameronScheme (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨myT, hmyTcard, hsep⟩ :=
    exists_isotropySeparatesAtBaseK Q hF hd hdge hψ hQrad hQnd hq1 hq2 hq3 hqthr hNthr
  refine ⟨myT.image affineE, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hmyTcard
  have himg : (myT.image affineE).image affineE.symm = myT := by
    rw [Finset.image_image,
      show (affineE.symm ∘ affineE) = id from funext (fun x => affineE.symm_apply_apply x),
      Finset.image_id]
  exact reachesRigidOrCameron_viaIsotropySeparatesK_wittFree Q (myT.image affineE) (le_refl _)
    (by rw [himg]; exact hsep)

end ChainDescent

#print axioms ChainDescent.exists_pow_matching_lt
#print axioms ChainDescent.exists_pow_matching_le
#print axioms ChainDescent.exists_pow_matching_block
#print axioms ChainDescent.exists_separating_base_of_split
#print axioms ChainDescent.exists_separating_base_of_split_bounded
#print axioms ChainDescent.cbar_lt
#print axioms ChainDescent.jointIsoCountK_ne_of_sep
#print axioms ChainDescent.exists_zProfileSeparatesK
#print axioms ChainDescent.exists_isotropySeparatesAtBaseK
#print axioms ChainDescent.reachesRigidOrCameron_affinePolar
