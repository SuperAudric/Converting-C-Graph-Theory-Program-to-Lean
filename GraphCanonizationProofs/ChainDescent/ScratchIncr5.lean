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
    (hc : ∀ g t₀, Good g t₀ → (univ.filter (fun t => Fail g t t₀)).card ≤ cN)
    (hβ : ∀ g, (univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN)
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

end ChainDescent

#print axioms ChainDescent.exists_pow_matching_lt
#print axioms ChainDescent.exists_separating_base_of_split
