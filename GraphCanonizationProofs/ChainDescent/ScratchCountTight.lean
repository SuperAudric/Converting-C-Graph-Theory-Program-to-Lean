/-
# The TIGHT c₀ counting identity (Route 2 / small-q tail).

`card_agree_le` (ScratchC0) gives `2·NS ≤ 2·z_u + |V| + T`. For the small-q tail (odd `q < 16`, where the threshold
route Route 0 does not reach) this `2·z_u` is too lossy: closing `c₀ < 1` needs `T/n < 1 − 2/q`, but the triangle
`T`-bound is `(1−1/q)² = 1 − 2/q + 1/q²`, which exceeds it by `1/q²`.

The fix is a **strictly tighter** counting identity: the per-element inequality `2·[ca=cb] ≤ 1 + [ca=0] + ca·cb`
(coefficient `1` on `[ca=0]`, not `2` — verified by `decide` on all `9` value pairs `ca,cb ∈ {-1,0,1}`) sums to
`2·NS ≤ |V| + z_u + T`. With the exact `z_u = |V|/q` (corank-1 quadric count) and the triangle `T ≤ (1−1/q)²·|V|`,
this gives `NS/|V| ≤ ½ + 1/(2q) + (1−1/q)²/2 < 1` for all odd `q ∈ [3,13]` — closing the whole odd-char tail uniformly
(`δ ≈ 0.036`), with NO `line_regroup`, NO per-line `card_quadForm`, NO `hq3`. (C# `Probe_Route2ExactSmallQ`: the exact
identity `NS = Z_both0 + (N_nz+S)/2` held `16/16`, exact `c₀ ≤ 0.556 < 1`; this `card_agree_le_tight` is the provable
upper bound feeding it.)

NOT in build (scratch; `lake env lean ChainDescent/ScratchCountTight.lean` after its imports' oleans build). -/
import ChainDescent.ScratchC0

namespace ChainDescent

open Finset

/-- **Tight per-element χ-value inequality.** For `ca, cb ∈ {-1,0,1}`: `2·[ca=cb] ≤ 1 + [ca=0] + ca·cb` — the
coefficient on `[ca=0]` is `1` (vs `2` in `int_char_pointwise`), binding exactly at `ca=cb=0` and `ca=cb=±1`
(both `2 ≤ 2`). Verified by `decide` over all `9` pairs. -/
theorem int_char_pointwise_tight (ca cb : ℤ)
    (hca : ca = -1 ∨ ca = 0 ∨ ca = 1) (hcb : cb = -1 ∨ cb = 0 ∨ cb = 1) :
    2 * (if ca = cb then (1 : ℤ) else 0)
      ≤ (if ca = 0 then (1 : ℤ) else 0) + 1 + ca * cb := by
  rcases hca with h | h | h <;> rcases hcb with h' | h' | h' <;> subst h <;> subst h' <;> decide

/-- **The tight c₀ counting identity** (ℤ). `2·#{χ(a)=χ(b)} ≤ #{a=0} + |V| + ∑_t χ(a t)·χ(b t)` — strictly tighter
than `counting_identity` (coefficient `1` on `#{a=0}`). Same proof skeleton, the tighter pointwise lemma. -/
theorem counting_identity_tight {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℤ)
      ≤ ((Finset.univ.filter (fun t => a t = 0)).card : ℤ)
        + (Fintype.card V : ℤ)
        + ∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) := by
  have hval : ∀ k : K, quadraticChar K k = -1 ∨ quadraticChar K k = 0 ∨ quadraticChar K k = 1 := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [quadraticChar_zero]; tauto
    · rcases quadraticChar_dichotomy hk with h | h <;> tauto
  have hz : (Finset.univ.filter (fun t => a t = 0))
          = (Finset.univ.filter (fun t => quadraticChar K (a t) = 0)) := by
    apply Finset.filter_congr
    intro t _
    rw [quadraticChar_eq_zero_iff]
  rw [hz, Finset.card_filter, Finset.card_filter,
    show (Fintype.card V : ℤ) = ∑ _t : V, (1 : ℤ) from by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => int_char_pointwise_tight _ _ (hval _) (hval _))

/-- **The tight count controlled by the magnitude** (ℝ). `2·#{χ(a)=χ(b)} ≤ #{a=0} + |V| + ‖T_ℂ‖` — the small-q-tail
replacement for `card_agree_le`, with `#{a=0}` (one copy of `z_u`, not two). Combines `counting_identity_tight` with
`charSum_int_le_norm`. -/
theorem card_agree_le_tight {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V → K) :
    2 * ((Finset.univ.filter (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ ((Finset.univ.filter (fun t => a t = 0)).card : ℝ)
        + (Fintype.card V : ℝ)
        + ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (a t)
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (b t)‖ := by
  have hc := counting_identity_tight a b
  have hT := charSum_int_le_norm a b
  have hcR : 2 * ((Finset.univ.filter
        (fun t => quadraticChar K (a t) = quadraticChar K (b t))).card : ℝ)
      ≤ ((Finset.univ.filter (fun t => a t = 0)).card : ℝ) + (Fintype.card V : ℝ)
        + ((∑ t : V, quadraticChar K (a t) * quadraticChar K (b t) : ℤ) : ℝ) := by
    exact_mod_cast hc
  linarith [hcR, hT]

end ChainDescent

#print axioms ChainDescent.int_char_pointwise_tight
#print axioms ChainDescent.counting_identity_tight
#print axioms ChainDescent.card_agree_le_tight
