/-
# Increment 3 CLOSED: `c₀ ≤ 3/4` for a good anchor (q ≥ q₀).

Assembles every landed piece into the final per-anchor non-separation bound:
* `card_agree_le`     : `2·NS ≤ 2·z_u + n + ‖T‖`           (the counting identity, 3e-iii)
* `normT_bucket_bound`: `q·‖T‖ ≤ q²√n + (d·q)(n/√q)`        (the |T| bound, 3e-ii)
* `zeroCount_sq_le` + `radical_card_mul_card_le` : the `z_u` bound (proper-subspace radical)
* `c0_le`             : the final arithmetic ⟹ `NS ≤ ¾·n`.
Under the threshold `64q² ≤ n` (⟺ `d ≥ 3`, the open node), `64d² ≤ q`, `256 ≤ q`.

NOT in build (scratch; build oleans of imported scratch modules first).
-/
import ChainDescent.ScratchTBound
import ChainDescent.ScratchC0

namespace ChainDescent

open Finset Module

/-- **THE PER-ANCHOR `c₀` BOUND (increment 3, closed).** For a good anchor (`hgood`) with no zero member (`hnz`) and a
nonzero pivot form (`hPu`), under the threshold `q ≥ q₀`, the agreement count `NS = #{t : χ(I_u t) = χ(I_v t)}` satisfies
`NS ≤ ¾·|V|`, i.e. `c₀ = NS/|V| ≤ ¾ < 1`. -/
theorem c0_le_threequarters {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
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
    ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ)
      ≤ 3 / 4 * Fintype.card V := by
  classical
  have hqpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsqqpos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.2 hqpos
  -- the complex character sum and its norm
  set T : ℝ := ‖∑ t : V,
      ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖ with hTdef
  -- (1) counting identity (`card_agree_le`); beta-reduce the lambdas so the norm folds to `T`
  have hcount := card_agree_le (K := K) (V := V)
    (fun t => pairForm Q (t₀ - u) (t - u)) (fun t => pairForm Q (t₀ - v) (t - v))
  rw [← hTdef] at hcount
  -- (2) the |T| bound, divided by q
  have hbt := normT_bucket_bound hF hψ Q u v t₀ b hnz hgood
  rw [← hTdef] at hbt
  have hT : T ≤ (Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
      + (d : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K) := by
    have heq : (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) * Real.sqrt (Fintype.card V)
          + (d : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K))
        = (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
          + ((d : ℝ) * Fintype.card K) * (Fintype.card V / Real.sqrt (Fintype.card K)) := by ring
    refine le_of_mul_le_mul_left ?_ hqpos
    rw [heq]; exact hbt
  -- (3) the z_u bound: reindex `{I_u(t)=0}` to `{P x = 0}`, then `zeroCount_sq_le` + radical bound
  have hreindex : (Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card
      = (Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card := by
    apply Finset.card_nbij' (fun t => t - u) (fun x => x + u) <;> intro x hx <;> simp_all
  have hzc := zeroCount_sq_le hψ (pairForm Q (t₀ - u))
  have hradR : ((Finset.univ.filter
        (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card : ℝ)
        * (Fintype.card K : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast radical_card_mul_card_le (pairForm Q (t₀ - u)) hPu
  set zP : ℝ := ((Finset.univ.filter (fun x : V => pairForm Q (t₀ - u) x = 0)).card : ℝ) with hzPdef
  set radP : ℝ := ((Finset.univ.filter
      (fun h : V => ∀ x, QuadraticMap.polar (pairForm Q (t₀ - u)) x h = 0)).card : ℝ) with hradPdef
  have hKnn : 0 ≤ (Fintype.card K - 1 : ℝ) * (Fintype.card V) / Real.sqrt (Fintype.card K) :=
    div_nonneg (by nlinarith [hq3, hnpos.le]) hsqqpos.le
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
  -- assemble via `c0_le`
  have hfinal := c0_le (n := (Fintype.card V : ℝ)) (q := (Fintype.card K : ℝ)) (dR := (d : ℝ))
    (T := T) (zu := zP)
    (NS := ((Finset.univ.filter (fun t : V =>
        quadraticChar K (pairForm Q (t₀ - u) (t - u))
          = quadraticChar K (pairForm Q (t₀ - v) (t - v)))).card : ℝ))
    hnpos hqpos (by positivity) ?_ hT hzu hq1 hq2 hq3
  · exact hfinal
  · -- hcount, with `z_u` rewritten through the reindex to `zP`
    have hzeq : zP = ((Finset.univ.filter (fun t : V => pairForm Q (t₀ - u) (t - u) = 0)).card : ℝ) := by
      rw [hzPdef, ← hreindex]
    rw [hzeq]; exact hcount

end ChainDescent

#print axioms ChainDescent.c0_le_threequarters
