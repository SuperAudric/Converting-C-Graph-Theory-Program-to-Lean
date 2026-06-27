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
import ChainDescent.ScratchMatching
import ChainDescent.ScratchIncr4
import ChainDescent.ScratchIncr4d
import ChainDescent.ScratchBridgeAllK
import ChainDescent.ScratchBridgeK
import ChainDescent.ScratchFieldGenAdapter
import Mathlib.Tactic

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

end ChainDescent

#print axioms ChainDescent.exists_pow_matching_lt
#print axioms ChainDescent.exists_separating_base_of_split
#print axioms ChainDescent.cbar_lt
#print axioms ChainDescent.jointIsoCountK_ne_of_sep
