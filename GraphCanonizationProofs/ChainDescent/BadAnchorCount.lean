/-
# Bad-anchor count `β` and the good-anchor fail bound (increment 4).

Produces the matching-trick inputs `c` (per-good-anchor fail) and the reduction toward `β` (bad-anchor density):

* **good-anchor fail `c`** (was `ScratchIncr4`): `good_anchor_fail_le_const` — `#{t : ¬sep} ≤ 15/16·|V|` on a good
  anchor (from `PerAnchorBound.c0_le_threequarters` + the zero-count shift).
* **structural reduction** (was `ScratchIncr4b`): because `pairForm Q (t₀−v)` is always degenerate, `hgood` alone
  forces `hnz`/`hPu`/`hPv`, so the good-anchor predicate collapses to `hgood ∧ Q(t₀−u)≠0 ∧ Q(t₀−v)≠0`; the bad-anchor
  count then needs one representing polynomial (built in `Coordinatization`).

(Merge of the former `ScratchIncr4` + `ScratchIncr4b`.)
-/
import ChainDescent.PerAnchorBound
import ChainDescent.PencilTBound
import ChainDescent.Matching

namespace ChainDescent

section -- ═══════════ was ScratchIncr4 ═══════════

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

end

section -- ═══════════ was ScratchIncr4b ═══════════

open Finset Module

/-- **Schwartz–Zippel in `Fin d` — the bad-anchor counting engine.** For a *nonzero* `d`-variable polynomial `p`, the
zero set over `K^d` satisfies `#{f : Fin d → K | eval f p = 0} · |K| ≤ p.totalDegree · |K^d|`, i.e.
`#{zeros}/|K^d| ≤ totalDegree/|K| = O(1/q)`. Generalizes `ScratchGoodAnchor.mvPoly_zeros_count_le` (the `Fin 2` case)
to arbitrary arity — the form needed to count bad anchors `t₀ ∈ V ≅ K^d`. Direct from
`MvPolynomial.schwartz_zippel_totalDegree` with `S = univ`. -/
theorem mvPoly_zeros_count_le_dim {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    {p : MvPolynomial (Fin d) K} (hp : p ≠ 0) :
    (univ.filter (fun f : Fin d → K => MvPolynomial.eval f p = 0)).card * Fintype.card K
      ≤ p.totalDegree * Fintype.card (Fin d → K) := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  set Sz : ℕ := (univ.filter (fun f : Fin d → K => MvPolynomial.eval f p = 0)).card with hSz
  set q : ℕ := Fintype.card K with hqdef
  have hqQ : (0 : ℚ≥0) < (q : ℚ≥0) := by exact_mod_cast hq
  -- `hsz : (Sz : ℚ≥0) / q^d ≤ totalDegree / q`; cross-multiply
  rw [div_le_div_iff₀ (by positivity) hqQ] at hsz
  -- `hsz : (Sz : ℚ≥0) * q ≤ totalDegree * q^d`
  have hcard : Fintype.card (Fin d → K) = q ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  exact_mod_cast hsz

section Reduction
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Every scalar multiple `c • pairForm Q a` has the anchor `a` in its polar-radical (`pairForm_polar_anchor`
transports through `polar_smul`). -/
theorem mem_polarRad_smul_pairForm (Q : QuadraticForm K V) (a : V) (c : K) :
    a ∈ polarRad (c • pairForm Q a) := by
  rw [mem_polarRad]
  intro x
  have h : QuadraticMap.polar (c • pairForm Q a) x a
      = c • QuadraticMap.polar (pairForm Q a) x a := by
    simp only [QuadraticMap.polar, QuadraticMap.smul_apply, smul_sub]
  rw [h, pairForm_polar_anchor, smul_zero]

/-- A nonzero scalar-multiple-of-`pairForm` form has nontrivial radical (the anchor `a ≠ 0`), hence is degenerate. -/
theorem polarRad_smul_pairForm_ne_bot (Q : QuadraticForm K V) {a : V} (ha : a ≠ 0) (c : K) :
    polarRad (c • pairForm Q a) ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨a, mem_polarRad_smul_pairForm Q a c, ha⟩

variable (Q : QuadraticForm K V) (u v t₀ : V)

/-- **`hgood ⟹ hPu`.** A nondeg pencil member forces `pairForm Q (t₀−u) ≠ 0`: if it were `0` the pencil would reduce
to `z • pairForm Q (t₀−v)`, degenerate (anchor `t₀−v ≠ 0`). -/
theorem hPu_of_hgood (hv : t₀ ≠ v)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    pairForm Q (t₀ - u) ≠ 0 := by
  intro hPu0
  obtain ⟨y, z, hyz⟩ := hg
  rw [hPu0, smul_zero, zero_add] at hyz
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hv) z hyz

/-- **`hgood ⟹ hPv`** (symmetric to `hPu_of_hgood`). -/
theorem hPv_of_hgood (hu : t₀ ≠ u)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    pairForm Q (t₀ - v) ≠ 0 := by
  intro hPv0
  obtain ⟨y, z, hyz⟩ := hg
  rw [hPv0, smul_zero, add_zero] at hyz
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hu) y hyz

/-- **`hgood ⟹ hnz`.** A nondeg pencil member forbids a zero member on `y,z ≠ 0`: a zero member makes
`pairForm Q (t₀−u) ∝ pairForm Q (t₀−v)`, collapsing the *whole* pencil to a scalar multiple of the (degenerate)
`pairForm Q (t₀−v)` — so no member could be nondegenerate. -/
theorem hnz_of_hgood (hv : t₀ ≠ v)
    (hg : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    ∀ y z : K, y ≠ 0 → z ≠ 0 → y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0 := by
  intro y₁ z₁ hy1 _ hyz1
  have h1 : y₁ • pairForm Q (t₀ - u) = -(z₁ • pairForm Q (t₀ - v)) :=
    eq_neg_of_add_eq_zero_left hyz1
  have hPueq : pairForm Q (t₀ - u) = (y₁⁻¹ * (-z₁)) • pairForm Q (t₀ - v) := by
    rw [mul_smul, neg_smul, ← h1, smul_smul, inv_mul_cancel₀ hy1, one_smul]
  obtain ⟨y₀, z₀, hyz0⟩ := hg
  rw [hPueq, smul_smul, ← add_smul] at hyz0
  exact polarRad_smul_pairForm_ne_bot Q (sub_ne_zero.mpr hv) _ hyz0

open scoped Classical in
/-- **The bad-anchor reduction (input `β`).** The full good-anchor predicate `hnz ∧ hgood ∧ hPu ∧ hPv` (what
`good_anchor_fail_le_const` consumes) fails on at most `#{t₀ : ¬hgood} + 2` anchors — i.e. `β ≤ #{¬hgood} + 2`. By the
three implications, the only way to fail `hnz`/`hPu`/`hPv` while `hgood` holds is `t₀ ∈ {u,v}` (two points). So the
bad-anchor count is governed by the single locus `{¬hgood} = {t₀ : pencilDisc(·;t₀) ≡ 0}`, the remaining
Schwartz–Zippel-in-`t₀` target (via `mvPoly_zeros_count_le_dim`). -/
theorem bad_anchor_card_le_hgood [Fintype V] [DecidableEq V] (Q : QuadraticForm K V) (u v : V) :
    (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
      ≤ (univ.filter (fun t₀ : V =>
          ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2 := by
  classical
  have hsub : (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
            y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
          ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
          ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0)))
      ⊆ (univ.filter (fun t₀ : V =>
          ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)) ∪ {u, v} := by
    intro t₀ ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases hgt : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥
    · refine Or.inr ?_
      by_contra hne
      rw [not_or] at hne
      exact ht ⟨hnz_of_hgood Q u v t₀ hne.2 hgt, hgt,
        hPu_of_hgood Q u v t₀ hne.2 hgt, hPv_of_hgood Q u v t₀ hne.1 hgt⟩
    · exact Or.inl hgt
  calc (univ.filter (fun t₀ : V => ¬ ((∀ y z : K, y ≠ 0 → z ≠ 0 →
              y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
            ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)
            ∧ pairForm Q (t₀ - u) ≠ 0 ∧ pairForm Q (t₀ - v) ≠ 0))).card
      ≤ ((univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥))
          ∪ ({u, v} : Finset V)).card := Finset.card_le_card hsub
    _ ≤ (univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card
          + ({u, v} : Finset V).card := Finset.card_union_le _ _
    _ ≤ (univ.filter (fun t₀ : V =>
            ¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥)).card + 2 :=
        Nat.add_le_add_left ((Finset.card_insert_le _ _).trans (by simp)) _

end Reduction

section SchwartzZippelCount
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

/-- **Bad-anchor count via a representing polynomial — the rigorous Schwartz–Zippel reduction.** If a bad-anchor
predicate `badpred` is contained in the zero set of a *nonzero* polynomial `P` read off the anchor's coordinates
(`hrep : badpred t₀ → eval (b.equivFun t₀) P = 0`), then `#{t₀ : badpred} · |K| ≤ P.totalDegree · |V|`, i.e.
density `≤ totalDegree/q`. Coordinatize `V ≅ K^d` via `b.equivFun`, then `mvPoly_zeros_count_le_dim`. For `β` this is
applied with `badpred = ¬hgood` and `P` = the pencil determinant at a fixed nondeg witness `(y₀,z₀)` (which a good
anchor makes `≠ 0`); `hrep` then holds because `¬hgood ⟹` every pencil member is degenerate
(`polarRad_ne_bot_iff_det_eq_zero`). -/
theorem bad_anchor_count_le_of_poly {d : ℕ} (b : Basis (Fin d) K V)
    (badpred : V → Prop) [DecidablePred badpred]
    (P : MvPolynomial (Fin d) K) (hP : P ≠ 0)
    (hrep : ∀ t₀, badpred t₀ → MvPolynomial.eval (b.equivFun t₀) P = 0) :
    (univ.filter badpred).card * Fintype.card K ≤ P.totalDegree * Fintype.card V := by
  classical
  have hsub : univ.filter badpred
      ⊆ univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0) := by
    intro t₀ ht
    rw [mem_filter] at ht ⊢
    exact ⟨ht.1, hrep t₀ ht.2⟩
  have hreindex : (univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0)).card
      = (univ.filter (fun f : Fin d → K => MvPolynomial.eval f P = 0)).card := by
    apply Finset.card_nbij' (fun t₀ => b.equivFun t₀) (fun f => b.equivFun.symm f)
    · intro t₀ ht
      rw [Finset.mem_coe, mem_filter] at ht ⊢
      exact ⟨mem_univ _, ht.2⟩
    · intro f hf
      rw [Finset.mem_coe, mem_filter] at hf ⊢
      exact ⟨mem_univ _, by rw [LinearEquiv.apply_symm_apply]; exact hf.2⟩
    · intro t₀ _; simp only [LinearEquiv.symm_apply_apply]
    · intro f _; simp only [LinearEquiv.apply_symm_apply]
  calc (univ.filter badpred).card * Fintype.card K
      ≤ (univ.filter (fun t₀ : V => MvPolynomial.eval (b.equivFun t₀) P = 0)).card * Fintype.card K :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ = (univ.filter (fun f : Fin d → K => MvPolynomial.eval f P = 0)).card * Fintype.card K := by
        rw [hreindex]
    _ ≤ P.totalDegree * Fintype.card (Fin d → K) := mvPoly_zeros_count_le_dim hP
    _ = P.totalDegree * Fintype.card V := by
        rw [← Fintype.card_congr b.equivFun.toEquiv]

omit [Fintype K] [DecidableEq K] [Fintype V] in
/-- **`hrep` for `¬hgood`, from a representing polynomial.** If `P` represents the pencil-determinant at a fixed witness
`(y₀,z₀)` — `eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u + z₀•pairForm_v)))` — then on every
`¬hgood` anchor `eval (coords t₀) P = 0` (the witness member is degenerate there, `polarRad_ne_bot_iff_det_eq_zero`).
This discharges `bad_anchor_count_le_of_poly`'s `hrep`, so the ONLY remaining obligation to close `β` is **constructing
such a `P` (with `P ≠ 0`)** — i.e. coordinatizing the pencil determinant + nonzero by a good-anchor witness. -/
theorem notHgood_eval_zero_of_repr {d : ℕ} (b : Basis (Fin d) K V) (Q : QuadraticForm K V)
    (y₀ z₀ : K) (u v : V) (P : MvPolynomial (Fin d) K)
    (hrepP : ∀ t₀, MvPolynomial.eval (b.equivFun t₀) P
      = (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin
          (y₀ • pairForm Q (t₀ - u) + z₀ • pairForm Q (t₀ - v)))).det) :
    ∀ t₀, (¬ ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) →
      MvPolynomial.eval (b.equivFun t₀) P = 0 := by
  intro t₀ hbad
  rw [hrepP t₀]
  apply (polarRad_ne_bot_iff_det_eq_zero b _).mp
  intro hbot
  exact hbad ⟨y₀, z₀, hbot⟩

end SchwartzZippelCount

end

end ChainDescent

#print axioms ChainDescent.fail_count_split
#print axioms ChainDescent.matching_F_bound
#print axioms ChainDescent.good_anchor_fail_le
#print axioms ChainDescent.zeroCountShift_card_le
#print axioms ChainDescent.good_anchor_fail_le_const
#print axioms ChainDescent.mvPoly_zeros_count_le_dim
#print axioms ChainDescent.hPu_of_hgood
#print axioms ChainDescent.hPv_of_hgood
#print axioms ChainDescent.hnz_of_hgood
#print axioms ChainDescent.bad_anchor_card_le_hgood
#print axioms ChainDescent.bad_anchor_count_le_of_poly
#print axioms ChainDescent.notHgood_eval_zero_of_repr
