/-
# Increment 4 — the good-anchor averaging that produces the matching-trick `F` (SCRATCH).

The matching trick (`ScratchMatching.exists_separating_base`) consumes a per-target fail-set bound
`F ≥ #{w : W | fail g w}` with `|ι|·Fᵐ < |W|ᵐ`. Here the matched-pair space is `W = V × V` (probe `t` × anchor `t₀`)
and a target `g = (u,v)` is *separated* by `(t,t₀)` when the joint isotropic counts differ. The plan: combine

* **increment 3** (`ScratchC0Final.c0_le_threequarters`) — for a **good anchor** `t₀`, the non-separating probe count
  `#{t : χ(I_u(t)) = χ(I_v(t))} ≤ ¾·|V|` (plus the `O(|V|/√q)` zero-count / `corr` corrections), and
* **the bad-anchor density** (Schwartz–Zippel in `t₀`) — `#{t₀ : ¬good t₀} ≤ O(|V|/q)`,

into `F = #{(t,t₀) : ¬sep} ≤ c·|V| + |V|·β`, where `c` = the per-good-anchor fail bound and `β` = the bad-anchor
count. Dividing by `|V|² = |W|` gives `c̄₀ = c/|V| + β/|V| ≤ ¾ + O(1/√q) + O(1/q) < 1` — the matching-trick input.

**This module lands the structural backbone + input `c`:**
* the anchor-averaging split `fail_count_split` (pure finite counting) + its `exists_separating_base`-ready corollary
  `matching_F_bound` (`F ≤ c·|B| + |A|·β`);
* **input `c` (the good-anchor fail bound), DONE** — `good_anchor_fail_le` (decomposition `fail ⟹ {χ-eq} ∨ {I_u=0} ∨
  {I_v=0}` + `c0_le_threequarters`) + `zeroCountShift_card_le` (`P≠0 ⟹ #{t:P(t−u)=0}·q ≤ |V|+(q−1)|V|/√q`) ⟹ capstone
  **`good_anchor_fail_le_const`: a good anchor has `#{t:¬sep} ≤ 15/16·|V|`** (`q≥256`), so `c/|V| ≤ 15/16 < 1`.

The other input — the bad-anchor count `β` (Schwartz–Zippel in `t₀`) — is in `ScratchIncr4b` (reduction) + `ScratchIncr4c`
(the representing-polynomial construction). The matching assembly (`c̄₀ = c/|V| + β/|V| < 1` → `exists_separating_base`)
is increment 5.

NOT in build (scratch; `lake env lean ChainDescent/ScratchIncr4.lean`, after `lake build ChainDescent.ScratchC0Final`).
-/
import ChainDescent.ScratchMatching
import ChainDescent.ScratchC0Final

namespace ChainDescent

open Finset Module

/-- **Anchor-averaging split — the increment-4 backbone.** For a fail predicate `fail : A → B → Prop` over a product
space (`A` = probe, `B` = anchor), if every **good** anchor `b` has `#{a : fail a b} ≤ c` and the bad anchors number
`≤ β`, then the total fail count over `A × B` is `≤ c·|B| + |A|·β`. Pure finite counting: split `∑_b #{a : fail a b}`
into good (`≤ c` each) and bad (`≤ |A|` each) anchors. This is the device that turns the per-good-anchor bound
(increment 3) plus the bad-anchor density (Schwartz–Zippel) into the matching-trick `F`. -/
theorem fail_count_split {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (fail : A → B → Prop) [∀ b, DecidablePred (fun a => fail a b)]
    (good : B → Prop) [DecidablePred good] (c β : ℕ)
    (hgoodbound : ∀ b, good b → (univ.filter (fun a => fail a b)).card ≤ c)
    (hbad : (univ.filter (fun b => ¬ good b)).card ≤ β) :
    (univ.filter (fun w : A × B => fail w.1 w.2)).card ≤ c * Fintype.card B + Fintype.card A * β := by
  classical
  -- the product fail count is the sum over anchors of the per-anchor probe-fail count
  have hsplit : (univ.filter (fun w : A × B => fail w.1 w.2)).card
      = ∑ b : B, (univ.filter (fun a : A => fail a b)).card := by
    simp_rw [Finset.card_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit]
  -- bound each anchor's term by `c + (bad ? |A| : 0)`
  have hterm : ∀ b : B, (univ.filter (fun a : A => fail a b)).card
      ≤ c + (if ¬ good b then Fintype.card A else 0) := by
    intro b
    by_cases hb : good b
    · simp only [hb, not_true, if_false, add_zero]
      exact hgoodbound b hb
    · simp only [hb, not_false_iff, if_true]
      calc (univ.filter (fun a : A => fail a b)).card
          ≤ Fintype.card A := by
            simpa using Finset.card_filter_le (univ : Finset A) (fun a => fail a b)
        _ ≤ c + Fintype.card A := Nat.le_add_left _ _
  calc ∑ b : B, (univ.filter (fun a : A => fail a b)).card
      ≤ ∑ b : B, (c + (if ¬ good b then Fintype.card A else 0)) := Finset.sum_le_sum (fun b _ => hterm b)
    _ = c * Fintype.card B + Fintype.card A * (univ.filter (fun b => ¬ good b)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        ring
    _ ≤ c * Fintype.card B + Fintype.card A * β := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hbad) _

/-- **The matching-trick `F`, ready for `exists_separating_base`.** A target-indexed fail predicate
`fail : ι → A → B → Prop` (`g = (u,v)`, `(a,b) = (t,t₀)`) with uniform per-good-anchor bound `c` and uniform
bad-anchor count `β` gives, for *every* target, `#{(t,t₀) : fail g} ≤ c·|B| + |A|·β =: F`. This is exactly
`exists_separating_base`'s `hF` (with `W := A × B`, `fun g w => fail g w.1 w.2`), so feeding it `F` separates every
target once `|ι|·Fᵐ < (|A|·|B|)ᵐ` — i.e. `c̄₀ := F/(|A|·|B|) = c/|A| + β/|B| < 1`, `m = O(log|ι| / log(1/c̄₀))`. -/
theorem matching_F_bound {A B ι : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (fail : ι → A → B → Prop) [∀ g b, DecidablePred (fun a => fail g a b)]
    (good : ι → B → Prop) [∀ g, DecidablePred (good g)] (c β : ℕ)
    (hgoodbound : ∀ g b, good g b → (univ.filter (fun a => fail g a b)).card ≤ c)
    (hbad : ∀ g, (univ.filter (fun b => ¬ good g b)).card ≤ β) :
    ∀ g : ι, (univ.filter (fun w : A × B => fail g w.1 w.2)).card
        ≤ c * Fintype.card B + Fintype.card A * β :=
  fun g => fail_count_split (fail g) (good g) c β (hgoodbound g) (hbad g)

/-- **Increment 4 — the good-anchor fail bound (input `c`).** For a **good anchor** `t₀` (the `c0_le_threequarters`
hypotheses `hnz`/`hgood`/`hPu` + the size thresholds), the probes `t` that the bridge FAILS to use for separation —
those where the separation criterion `χ(I_u(t)) ≠ χ(I_v(t)) ∧ I_u(t) ≠ 0 ∧ I_v(t) ≠ 0` (both configs nondeg, `χ`
differ; the `corr` term is folded into the bad-anchor set, which for a good anchor also requires `Q(t₀−u),Q(t₀−v)≠0`)
fails — number at most `¾·|V| + #{I_u=0} + #{I_v=0}`. Decomposition: `fail ⟹ {χ-eq} ∨ {I_u=0} ∨ {I_v=0}`
(de Morgan), card-subadditivity, then `c0_le_threequarters` bounds `#{χ-eq} ≤ ¾·|V|`. The two zero-counts are
`O(|V|/√q)` (the genuine dominant gap, `zeroCount_sq_le` + `radical_card_mul_card_le`) — that bound is the remaining
piece of input `c`. -/
theorem good_anchor_fail_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
    (hPu : pairForm Q (t₀ - u) ≠ 0)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card V)
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K)
    (hq3 : 256 ≤ (Fintype.card K : ℝ)) :
    ((Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - u) (t - u))
              ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))
            ∧ pairForm Q (t₀ - u) (t - u) ≠ 0 ∧ pairForm Q (t₀ - v) (t - v) ≠ 0))).card : ℝ)
      ≤ 3 / 4 * Fintype.card V
        + (Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
        + (Finset.univ.filter (fun t : V => pairForm Q (t₀ - v) (t - v) = 0)).card := by
  classical
  -- the failing probes split into {χ-equal} ∪ {I_u = 0} ∪ {I_v = 0}
  have hsub : (univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - u) (t - u))
            ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))
          ∧ pairForm Q (t₀ - u) (t - u) ≠ 0 ∧ pairForm Q (t₀ - v) (t - v) ≠ 0)))
      ⊆ (univ.filter (fun t : V => quadraticChar K (pairForm Q (t₀ - u) (t - u))
              = quadraticChar K (pairForm Q (t₀ - v) (t - v)))
          ∪ univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0))
        ∪ univ.filter (fun t : V => pairForm Q (t₀ - v) (t - v) = 0) := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and, ne_eq, not_and_or, not_not] at ht
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  -- card subadditivity, then `c0_le_threequarters` on the χ-equal block
  have hcard := le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc0 := c0_le_threequarters hF hψ Q u v t₀ b hnz hgood hPu hq1 hq2 hq3
  calc ((univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - u) (t - u))
                ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))
              ∧ pairForm Q (t₀ - u) (t - u) ≠ 0 ∧ pairForm Q (t₀ - v) (t - v) ≠ 0))).card : ℝ)
      ≤ (((univ.filter (fun t : V => quadraticChar K (pairForm Q (t₀ - u) (t - u))
              = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card
            + (univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
            + (univ.filter (fun t : V => pairForm Q (t₀ - v) (t - v) = 0)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ 3 / 4 * Fintype.card V
        + (univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
        + (univ.filter (fun t : V => pairForm Q (t₀ - v) (t - v) = 0)).card := by
        push_cast; linarith [hc0]

/-- **The shifted zero-count bound (the remaining piece of input `c`).** For any *nonzero* quadratic form `P` and
shift `u`, `#{t : P(t−u) = 0} · |K| ≤ |V| + (|K|−1)·|V|/√|K|` — so `#{t : P(t−u)=0}/|V| ≤ 1/q + (q−1)/(q√q) = O(1/√q)`.
Reindex `t ↦ t−u` to the homogeneous count, then `zeroCount_sq_le` (the `‖∑ψ‖` zero-count inequality) +
`radical_card_mul_card_le` (proper-subspace radical, `|radical|·q ≤ |V|`) + `abs_le_of_sq_le_sq'`. Applied to
`P = pairForm Q (t₀−u)` (resp. `t₀−v`) this bounds the two zero-counts in `good_anchor_fail_le`, completing input `c`.
(Extracted from the `z_u` block of `ScratchC0Final.c0_le_threequarters`.) -/
theorem zeroCountShift_card_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) (P : QuadraticForm K V) (hP : P ≠ 0) (u : V) :
    ((univ.filter (fun t : V => P (t - u) = 0)).card : ℝ) * Fintype.card K
      ≤ Fintype.card V + (Fintype.card K - 1) * Fintype.card V / Real.sqrt (Fintype.card K) := by
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsqqpos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.2 hqpos
  have hq1c : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos
  -- reindex `{t : P (t-u) = 0}` to the homogeneous `{x : P x = 0}`
  have hreindex : (univ.filter (fun t : V => P (t - u) = 0)).card
      = (univ.filter (fun x : V => P x = 0)).card := by
    apply Finset.card_nbij' (fun t => t - u) (fun x => x + u) <;> intro x hx <;> simp_all
  have hzc := zeroCount_sq_le hψ P
  have hradR : ((univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card : ℝ)
      * (Fintype.card K : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast radical_card_mul_card_le P hP
  set zP : ℝ := ((univ.filter (fun x : V => P x = 0)).card : ℝ) with hzPdef
  set radP : ℝ := ((univ.filter (fun h : V => ∀ x, QuadraticMap.polar P x h = 0)).card : ℝ)
    with hradPdef
  have hKnn : 0 ≤ (Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K) :=
    div_nonneg (by nlinarith [hq1c, hnpos.le]) hsqqpos.le
  have hsq : (zP * Fintype.card K - Fintype.card V) ^ 2
      ≤ ((Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K)) ^ 2 := by
    have hKsq : ((Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K)) ^ 2
        = (Fintype.card K - 1 : ℝ) ^ 2 * ((Fintype.card V) * (Fintype.card V / Fintype.card K)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hqpos.le]; ring
    rw [hKsq]
    refine le_trans hzc ?_
    have hradle : radP ≤ (Fintype.card V : ℝ) / Fintype.card K :=
      (le_div_iff₀ hqpos).2 (by linarith [hradR])
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hradle hnpos.le) (by positivity)
  have hzu : zP * Fintype.card K ≤ (Fintype.card V : ℝ)
      + (Fintype.card K - 1) * (Fintype.card V) / Real.sqrt (Fintype.card K) := by
    have := (abs_le_of_sq_le_sq' hsq hKnn).2
    linarith
  rw [hreindex]
  exact hzu

/-- **Input `c` — the per-good-anchor fail bound with an explicit sub-1 constant.** Combining `good_anchor_fail_le`
(`#fail ≤ ¾|V| + #{I_u=0} + #{I_v=0}`) with two `zeroCountShift_card_le` bounds (each zero-count `≤ 3/32·|V|` once
`q ≥ 256`, since `z/|V| ≤ 1/q + (q−1)/(q√q) ≤ 1/256 + 1/16 = 17/256 < 3/32`): a good anchor has
`#{t : ¬sep} ≤ (15/16)·|V|`. So `c/|V| ≤ 15/16 < 1` — the good-anchor side of `c̄₀ < 1` (the bad-anchor `β` is the
remaining `O(1/q)` Schwartz–Zippel term). Needs `hPv` (the `v`-pivot form is nonzero) alongside `hPu`. -/
theorem good_anchor_fail_le_const {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
    (hPu : pairForm Q (t₀ - u) ≠ 0) (hPv : pairForm Q (t₀ - v) ≠ 0)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card V)
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K)
    (hq3 : 256 ≤ (Fintype.card K : ℝ)) :
    ((Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - u) (t - u))
              ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))
            ∧ pairForm Q (t₀ - u) (t - u) ≠ 0 ∧ pairForm Q (t₀ - v) (t - v) ≠ 0))).card : ℝ)
      ≤ 15 / 16 * Fintype.card V := by
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hspos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.2 hqpos
  have hqs : (Fintype.card K : ℝ) = Real.sqrt (Fintype.card K) ^ 2 := (Real.sq_sqrt hqpos.le).symm
  have hs16 : (16 : ℝ) ≤ Real.sqrt (Fintype.card K) := by
    have h := Real.sqrt_le_sqrt hq3
    rwa [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16)] at h
  have hfail := good_anchor_fail_le hF hψ Q u v t₀ b hnz hgood hPu hq1 hq2 hq3
  -- each zero-count is ≤ 3/32·|V|
  have hzbound : ∀ (P : QuadraticForm K V) (w : V), P ≠ 0 →
      ((Finset.univ.filter (fun t : V => P (t - w) = 0)).card : ℝ) ≤ 3 / 32 * Fintype.card V := by
    intro P w hP
    set z : ℝ := ((Finset.univ.filter (fun t : V => P (t - w) = 0)).card : ℝ) with hzdef
    have hz0 : 0 ≤ z := by rw [hzdef]; exact Nat.cast_nonneg _
    have hzc := zeroCountShift_card_le hψ P hP w
    set s := Real.sqrt (Fintype.card K) with hsdef
    -- clear the division by `s`, then a polynomial bound in `s ≥ 16`
    have hzc' : z * Fintype.card K * s ≤ Fintype.card V * s + (Fintype.card K - 1) * Fintype.card V := by
      have hmul := mul_le_mul_of_nonneg_right hzc hspos.le
      rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hspos)] at hmul
    rw [hqs] at hzc'
    -- `z·s³ ≤ |V|s + (s²−1)|V|` and `s ≥ 16` ⟹ `z ≤ 3/32·|V|`
    nlinarith [hzc', hs16, hnpos, hspos, hz0, mul_pos (mul_pos hspos hspos) hspos,
      mul_nonneg hz0 (mul_pos (mul_pos hspos hspos) hspos).le, sq_nonneg (s - 16),
      mul_nonneg hnpos.le (mul_nonneg hspos.le hspos.le)]
  have hzu := hzbound (pairForm Q (t₀ - u)) u hPu
  have hzv := hzbound (pairForm Q (t₀ - v)) v hPv
  linarith [hfail, hzu, hzv]

end ChainDescent

#print axioms ChainDescent.fail_count_split
#print axioms ChainDescent.matching_F_bound
#print axioms ChainDescent.good_anchor_fail_le
#print axioms ChainDescent.zeroCountShift_card_le
#print axioms ChainDescent.good_anchor_fail_le_const
