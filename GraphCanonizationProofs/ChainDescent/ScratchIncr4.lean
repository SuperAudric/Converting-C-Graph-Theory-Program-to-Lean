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

**This module lands the structural backbone** — the anchor-averaging split `fail_count_split` (a pure finite-counting
identity, no analysis) that turns "per-good-anchor bound + bad-anchor count" into the product-space fail bound `F`, and
its `exists_separating_base`-ready corollary `matching_F_bound`. The two analytic inputs (the good-anchor `c` from
increment 3 + zero-counts, and the bad-anchor `β` from Schwartz–Zippel in `t₀`) are the remaining increment-4 work;
this lemma is what consumes them and is where they plug in.

NOT in build (scratch; `lake env lean ChainDescent/ScratchIncr4.lean`).
-/
import ChainDescent.ScratchMatching

namespace ChainDescent

open Finset

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

end ChainDescent

#print axioms ChainDescent.fail_count_split
#print axioms ChainDescent.matching_F_bound
