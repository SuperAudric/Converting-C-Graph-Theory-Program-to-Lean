import ChainDescent.KernelTransport
import ChainDescent.SupplyCost

/-!
# `②` FOR THE OBJECT OF RECORD — the four supplies and the holonomy key, billed

## Why this file exists (audited 2026-07-28, by grep, not by argument)

`SupplyCost.lean` bills `matchSupply` / `deepMatchSupply` / `partialMatchSupply` / `prunedSupply`, and
`SelectNode`'s two end-to-end theorems (`descentCostS_selNode_pruned_lookahead_le`,
`descentCostS_selNode_match_lookahead_le`) are stated at **`lookaheadKey` + `prunedSupply`**. But
`Publication.canonForm?` is a *different object*:

    Select.canonFormFastS? (Hol.holKeyFast) (foldSupplyFast ++ deckSupply ++ deck2Supply ++ kernelSupply)

and **not one of those five components had a cost bound.** So the object whose `①` trio is axiom-clean
had no `②` at all, `Publication.cost` was an `opaque` stub, and `canon_poly_or_flag` a `sorry`. That is
the T2 house rule ("closed-form `c₂` at land time") not having been applied to the record.

This file pays it. Nothing here is deep — every one of the four supplies already bills a *closed form*;
what was missing was the arithmetic tying those forms to `n` and composing them through `appendSupply`.
That is the point: the debt was bookkeeping, and bookkeeping left unpaid is exactly how a `②` claim
becomes unfalsifiable (the 2026-07-14 "`Key`/`Supply` were cost-free" finding, recurring).

## What is proved

* §1 generic list helpers + **`supplyCost_appendSupply`** (definitional — `appendSupply` sums the costs).
* §2 the four supplies' **work** bounds and **candidate-count** bounds, and `holKeyFast`'s `keyCost`.
* §3 the composite: `recordSupplyBound` / `recordGensBound`, and the two bounds at `recordSupplyFast`.
* §4 **`descentCostS_selNode_record_le`** — `②` end-to-end for the canonizer of record, an explicit
  polynomial on **every** input, with **no hypotheses**. Fan-out `≤ 1` is structural
  (`selNode_children_length_le_one`), so unlike the guarded bound this carries no `ResolvedAll`.

⚠ **What this does NOT say.** A closed-form bound is not a *tight* bound, and `n⁷`-ish constants here
are deliberately generous — the supplies bill flat per-call charges that dominate their real work. The
value is that the bound is now **parametric in the real components**, so a future supply with an
exponential charge shows up instead of hiding. It also does not cover `deepenSupply` (still prose-only,
remaining-work §1T T2) — that supply is not in the record.
-/

namespace ChainDescent
namespace RecordCost

open ChainDescent.Descend
open ChainDescent.Consume (Supply gens supplyCost)
open ChainDescent.Force (Key keyCost)

variable {n : Nat}

/-! ## 1. Helpers -/

/-- A `flatMap` whose blocks are uniformly bounded. -/
theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (k : Nat)
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul _ k ?_) ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx
  · rw [List.length_map, smul_eq_mul]

/-- **`appendSupply` sums the costs** — definitional, and the reason composing the four bounds is free. -/
@[simp] theorem supplyCost_appendSupply (S₁ S₂ : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Deck.appendSupply S₁ S₂) adj χ = supplyCost S₁ adj χ + supplyCost S₂ adj χ := rfl

/-- …and concatenates the candidate lists. -/
@[simp] theorem gens_appendSupply_length (S₁ S₂ : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (Deck.appendSupply S₁ S₂) adj χ).length
      = (gens S₁ adj χ).length + (gens S₂ adj χ).length :=
  List.length_append ..

/-! ## 2. The four supplies, and the key

Each supply bills a closed form already; these lemmas replace `(branches χ).length` by `n`
(`SupplyCost.branches_length_le`) and bound the candidate lists. -/

/-! ### 2a. `foldSupplyFast` (F2a) and `deckSupply` (F2b) — the all-pairs shape -/

theorem supplyCost_foldSupplyFast_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Fold.foldSupplyFast (n := n)) adj χ ≤ n * n * (n * n * n * n * n) :=
  Nat.mul_le_mul_right _
    (Nat.mul_le_mul (SupplyCost.branches_length_le χ) (SupplyCost.branches_length_le χ))

theorem gens_foldSupplyFast_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (Fold.foldSupplyFast (n := n)) adj χ).length ≤ n * n := by
  refine le_trans (length_flatMap_le _ _ n ?_) ?_
  · exact fun _ _ => le_trans (List.length_filterMap_le ..) (SupplyCost.branches_length_le χ)
  · exact Nat.mul_le_mul_right n (SupplyCost.branches_length_le χ)

theorem supplyCost_deckSupply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Deck.deckSupply (n := n)) adj χ ≤ n * n * (n * n * n * n * n) :=
  Nat.mul_le_mul_right _
    (Nat.mul_le_mul (SupplyCost.branches_length_le χ) (SupplyCost.branches_length_le χ))

theorem gens_deckSupply_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (Deck.deckSupply (n := n)) adj χ).length ≤ n * n := by
  refine le_trans (length_flatMap_le _ _ n ?_) ?_
  · exact fun _ _ => le_trans (List.length_filterMap_le ..) (SupplyCost.branches_length_le χ)
  · exact Nat.mul_le_mul_right n (SupplyCost.branches_length_le χ)

/-! ### 2b. `deck2Supply` (F2c) — the second-seed shape

The extra factor over 2a is the seed list: `secondsV` is a `flatMap` over `finRange n` whose blocks are
filters of `finRange n`, hence `≤ n²` seeds, and `deck2Batch` `filterMap`s that list. -/

theorem length_secondsV_le (adj : AdjMatrix n) (χ : Colouring n)
    (mf : Vector (Option (Fin n)) n) : (Deck2.secondsV adj χ mf).length ≤ n * n := by
  refine le_trans (length_flatMap_le _ _ n ?_) ?_
  · intro v₁ _
    cases mf.get v₁ with
    | some _ => simp
    | none =>
        simp only [List.length_map]
        exact le_trans (List.length_filter_le ..) (by simp)
  · simp

theorem length_deck2Batch_le (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    (Deck2.deck2Batch adj χ u₁ u₂).length ≤ n * n :=
  le_trans (List.length_filterMap_le ..) (length_secondsV_le adj χ _)

theorem supplyCost_deck2Supply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Deck2.deck2Supply (n := n)) adj χ
      ≤ n * n * (1 + n * n) * (n * n * n * n * n) :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul (SupplyCost.branches_length_le χ) (SupplyCost.branches_length_le χ)))

theorem gens_deck2Supply_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (Deck2.deck2Supply (n := n)) adj χ).length ≤ n * (n * (n * n)) := by
  refine le_trans (length_flatMap_le _ _ (n * (n * n)) ?_) ?_
  · intro u₁ _
    refine le_trans (length_flatMap_le _ _ (n * n) ?_) ?_
    · exact fun u₂ _ => length_deck2Batch_le adj χ u₁ u₂
    · exact Nat.mul_le_mul_right _ (SupplyCost.branches_length_le χ)
  · exact Nat.mul_le_mul_right _ (SupplyCost.branches_length_le χ)

/-! ### 2c. `kernelSupply` (C3a) — a flat charge and a rank-bounded basis

`nullBasis m rows` emits **one word per free column**, so its length is `≤ m`; the column count is the
rail count, and rails are a `filterMap` of `finRange n`. Hence at most `n` generators. -/

theorem length_nullBasis_le (m : Nat) (rows : List (List Bool)) :
    (Kernel.nullBasis m rows).length ≤ m := by
  simp only [Kernel.nullBasis, List.length_map]
  exact le_trans (List.length_filter_le ..) (by simp)

theorem length_rails_le (adj : AdjMatrix n) (χ : Colouring n) :
    (Kernel.rails adj χ).length ≤ n :=
  le_trans (List.length_filterMap_le ..) (by simp)

theorem supplyCost_kernelSupply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (Kernel.kernelSupply (n := n)) adj χ ≤ n * n * n * n * n := le_rfl

theorem gens_kernelSupply_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (Kernel.kernelSupply (n := n)) adj χ).length ≤ n := by
  show (Kernel.kernelGens adj χ).length ≤ n
  simp only [Kernel.kernelGens]
  split
  · exact le_trans (List.length_filterMap_le ..)
      (le_trans (length_nullBasis_le ..) (length_rails_le adj χ))
  · simp

/-! ### 2d. `holKeyFast` — the force key of record

The charge is flat (`n⁵`) by definition, so the `_le` form is `le_of_eq`. It is recorded as a named
lemma because `selProbeCost_le` asks for a bound, and because a *declared* flat charge is exactly the
shape the 2026-07-27 `orbKeyG` work had to repair — here it is honest, since `holSig` really is one
`n⁵` sweep and delegates nothing. -/

theorem keyCost_holKeyFast_le (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyCost (Hol.holKeyFast (n := n)) adj χ v ≤ n * n * n * n * n := le_rfl

/-! ## 3. The composite -/

/-- The record consume-side supply, in the exact shape `Publication.canonForm?` uses. -/
abbrev recordSupplyFast : Supply n :=
  Deck.appendSupply (Fold.foldSupplyFast (n := n))
    (Deck.appendSupply (Deck.deckSupply (n := n))
      (Deck.appendSupply (Deck2.deck2Supply (n := n)) (Kernel.kernelSupply (n := n))))

/-- The record's per-node **work** budget: the four supplies' closed forms, summed. -/
def recordSupplyBound (n : Nat) : Nat :=
  n * n * (n * n * n * n * n)
    + (n * n * (n * n * n * n * n)
      + (n * n * (1 + n * n) * (n * n * n * n * n) + n * n * n * n * n))

/-- The record's **candidate-count** budget. -/
def recordGensBound (n : Nat) : Nat :=
  n * n + (n * n + (n * (n * (n * n)) + n))

theorem supplyCost_record_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (recordSupplyFast (n := n)) adj χ ≤ recordSupplyBound n := by
  simp only [recordSupplyFast, supplyCost_appendSupply, recordSupplyBound]
  exact Nat.add_le_add (supplyCost_foldSupplyFast_le adj χ)
    (Nat.add_le_add (supplyCost_deckSupply_le adj χ)
      (Nat.add_le_add (supplyCost_deck2Supply_le adj χ) (supplyCost_kernelSupply_le adj χ)))

theorem gens_record_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (recordSupplyFast (n := n)) adj χ).length ≤ recordGensBound n := by
  simp only [recordSupplyFast, gens_appendSupply_length, recordGensBound]
  exact Nat.add_le_add (gens_foldSupplyFast_length_le adj χ)
    (Nat.add_le_add (gens_deckSupply_length_le adj χ)
      (Nat.add_le_add (gens_deck2Supply_length_le adj χ) (gens_kernelSupply_length_le adj χ)))

/-! ## 4. ★★★ `②` END-TO-END FOR THE CANONIZER OF RECORD

The shape mirrors `SelectNode.descentCostS_selNode_pruned_lookahead_le` exactly; what is new is that it
is stated at the object `Publication.canonForm?` actually is. **No hypotheses**: the fan-out bound is
`selNode_children_length_le_one`, which holds by construction. -/

theorem descentCostS_selNode_record_le (adj : AdjMatrix n) :
    Select.descentCostS (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (recordSupplyFast (n := n))) adj
      ≤ n * n * n + (n + 1)
          * (1 + (Select.selProbeBound n (recordSupplyBound n) (recordGensBound n)
              (n * n * n * n * n) + n * n * n)) := by
  refine Select.descentCostS_le_of_le_one
    (fun χ _ => Select.selNode_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine Select.selNode_cost_le (Select.selProbeCost_le (supplyCost_record_le adj χ)
    (gens_record_length_le adj χ) (fun v => keyCost_holKeyFast_le adj χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-- **The record capstone: `①` + `②` in one place.** `①` is `Kernel.holKey_foldDeck2KernelFast_selNode_canonizer`
(2026-07-19, axiom-clean); `②` is the theorem above. Together they are exactly what
`Publication.canon_sound` / `canon_complete` / `flag_iso_invariant` / `canon_poly_or_flag` need — the
`②` obligation there can now stop being a `sorry` over an `opaque cost`. -/
theorem record_canonizer_with_cost :
    CanonSpec.IsCanonicalFormOpt
        (Select.canonFormS? (Refine.encodeFreeFast (n := n))
          (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
            (recordSupplyFast (n := n))))
    ∧ ∀ adj : AdjMatrix n,
        Select.descentCostS (Refine.encodeFreeFast (n := n))
            (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
              (recordSupplyFast (n := n))) adj
          ≤ n * n * n + (n + 1)
              * (1 + (Select.selProbeBound n (recordSupplyBound n) (recordGensBound n)
                  (n * n * n * n * n) + n * n * n)) :=
  ⟨Kernel.holKey_foldDeck2KernelFast_selNode_canonizer, descentCostS_selNode_record_le⟩

end RecordCost
end ChainDescent
