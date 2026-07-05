/-
# Per-anchor non-separation bound (increment 3) — `c₀ ≤ ¾ < 1` for a good anchor.

Turns the `‖T‖` magnitude bound (`PencilTBound`) into a bound on the per-good-anchor non-separating probe count
`NS = #{t : χ(I_u t) = χ(I_v t)}`:

* **counting identity** (was `ScratchCount`): `2·NS ≤ 2·z_u + |V| + T_ℤ` (`z_u = #{I_u = 0}`), from a per-element
  χ-value inequality.
* **ℤ↔ℂ connect** (was `ScratchC0`): `T_ℤ ≤ |T_ℤ| = ‖T_ℂ‖`, so `2·NS ≤ 2·z_u + |V| + ‖T_ℂ‖`.
* **capstone `c0_le_threequarters`** (was `ScratchC0Final`): assembling the counting identity, `normT_bucket_bound`,
  and the `z_u` proper-subspace bound ⟹ `NS ≤ ¾·|V|` for a good anchor (`q ≥ q₀`, `d ≥ 3`).

(Merge of the former `ScratchCount` + `ScratchC0` + `ScratchC0Final`.)
-/
import ChainDescent.PencilTBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace ChainDescent

section -- ═══════════ was ScratchCount ═══════════

open Finset

/-- Per-element χ-value inequality (the heart of the counting identity). For `ca, cb ∈ {-1,0,1}`:
`2·[ca=cb] ≤ 2·[ca=0] + 1 + ca·cb`. -/
theorem int_char_pointwise (ca cb : ℤ)
    (hca : ca = -1 ∨ ca = 0 ∨ ca = 1) (hcb : cb = -1 ∨ cb = 0 ∨ cb = 1) :
    2 * (if ca = cb then (1 : ℤ) else 0) ≤ 2 * (if ca = 0 then (1 : ℤ) else 0) + 1 + ca * cb := by
  rcases hca with h | h | h <;> rcases hcb with h' | h' | h' <;> subst h <;> subst h' <;> decide

/-- **The c₀ counting identity.** `2·#{t : χ(a t) = χ(b t)} ≤ 2·#{t : a t = 0} + |V| + ∑_t χ(a t)·χ(b t)`,
for the quadratic character `χ = quadraticChar K`. (`a, b = I_u, I_v`.) -/
theorem counting_identity {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℤ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℤ)
        + (Fintype.card V : ℤ)
        + ∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) := by
  have hval : ∀ k : K, quadraticChar K k = -1 ∨ quadraticChar K k = 0 ∨ quadraticChar K k = 1 := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [quadraticChar_zero]; tauto
    · rcases quadraticChar_dichotomy hk with h | h <;> tauto
  -- replace the `a t = 0` filter by the `χ(a t) = 0` filter
  have hz : (Finset.univ.filter (fun t => a t = 0))
          = (Finset.univ.filter (fun t => quadraticChar K (a t) = 0)) := by
    apply Finset.filter_congr
    intro t _
    rw [quadraticChar_eq_zero_iff]
  rw [hz, Finset.card_filter, Finset.card_filter,
    show (Fintype.card V : ℤ) = ∑ _t : V, (1 : ℤ) from by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => int_char_pointwise _ _ (hval _) (hval _))

end

section -- ═══════════ was ScratchC0 ═══════════

open Finset

/-- The integer character sum is `≤` the norm of the complex character sum (`T_ℤ ≤ |T_ℤ| = ‖T_ℂ‖`). -/
theorem charSum_int_le_norm {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] (a b : V → K) :
    ((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ)
      ≤ ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
          * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t)‖ := by
  have hcast : (∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
        * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t))
      = (((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ) : ℂ) := by
    push_cast [MulChar.ringHomComp_apply]
    simp only [eq_intCast]
  rw [hcast, Complex.norm_real]
  exact le_abs_self _

/-- **The count controlled by the magnitude.** `2·#{χ(a)=χ(b)} ≤ 2·#{a=0} + |V| + ‖T_ℂ‖` over ℝ, combining
`counting_identity` with `charSum_int_le_norm`. -/
theorem card_agree_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℝ)
        + (Fintype.card V : ℝ)
        + ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t)‖ := by
  have hc := counting_identity a b
  have hT := charSum_int_le_norm a b
  have hcR : 2 * ((Finset.univ.filter
        (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ 2 * ((Finset.univ.filter (fun t => a t = 0)).card : ℝ) + (Fintype.card V : ℝ)
        + ((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ) := by
    exact_mod_cast hc
  linarith [hcR, hT]

end

section -- ═══════════ was ScratchC0Final ═══════════

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

end

end ChainDescent

--#print axioms ChainDescent.int_char_pointwise
--#print axioms ChainDescent.counting_identity
--#print axioms ChainDescent.charSum_int_le_norm
--#print axioms ChainDescent.card_agree_le
--#print axioms ChainDescent.c0_le_threequarters
