/-
# ScratchCostModelWarmRefine.lean — the `warmRefine` per-node cost (pilot brick; WIP, NOT in build.sh)

The first concrete piece of the pilot's per-node bound `w n` (cost-model doc §4): the refinement summand.
`warmRefine` is the dominant per-descent-node work. This brick ties a polynomial cost to its REAL structure
and surfaces the one honesty issue the doc must record (renumbering / unit-cost colours, below).

**What is real here (proved against the actual `ChainDescent.warmRefine`):**
  · `warmRefine_eq_iterate` — `warmRefine = (refineStep)^[n]`: the round count is exactly `n` (the def).
  · `signature_card` — the per-vertex signature has exactly `n-1` entries: the real input size the per-vertex
    refineStep cost is a function of.

**What is DECLARED (D7 unit-cost primitives):** the cost of one `refineStep` evaluation at a vertex —
building the size-`(n-1)` signature, `Multiset.sort`, `Encodable.encode` — is `≤ sigCost n`.

**★ THE HONESTY FINDING this brick surfaces (for the doc §4/§7/§8).** `refineStep` recolours via
`Encodable.encode (sigKey …)` with **no cell renumbering**, so colour Nats **blow up in bit-size** across
rounds (encode of encode of …). Hence `warmRefine` as defined is poly **only under a unit-cost-RAM D7
declaration** (colour compare/encode = O(1)); a genuine *bit-cost* poly bound needs a **renumbering
`refineStep` variant** (cells → `0..k-1` each round, as the C# does). This is a real design item, not a
formality — the cost model must either declare colour-ops unit-cost (recorded in the D7 list) or the Runtime
Phase must define the renumbering variant. Flagged; not resolved here.

Imports `ChainDescent` (⟹ Mathlib) — the pilot's heavy import path, surfaced early as planned. Quality bar:
axiom-clean, no `sorry`. Compile: `cd GraphCanonizationProofs && lake env lean ChainDescent/ScratchCostModelWarmRefine.lean`
-/
import ChainDescent

namespace ChainDescent.CostModel.WarmRefine

open ChainDescent

variable {n : Nat}

/-! ## 1. Real structure of `warmRefine` (proved against the actual definition) -/

/-- **`warmRefine` is exactly `n` rounds of `refineStep`.** The round count = the vertex count `n`; this is
the definition, but stating it fixes the "node_count-inside-warmRefine" factor as real, not declared. -/
theorem warmRefine_eq_iterate (adj : AdjMatrix n) (P : PMatrix n) (init : Colouring n) :
    warmRefine adj P init = (refineStep adj P)^[n] init := rfl

/-- **The per-vertex signature has exactly `n-1` entries** — the real input size that the declared per-vertex
`refineStep` cost is a function of. (One tuple per other vertex.) -/
theorem signature_card (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) (v : Fin n) :
    Multiset.card (signature adj P χ v) = n - 1 := by
  unfold signature
  rw [Multiset.card_map]
  show (Finset.univ.filter (· ≠ v)).card = n - 1
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
    Fintype.card_fin]

/-! ## 2. The declared per-vertex cost and the structural warmRefine cost (D7)

`sigCost n` = the DECLARED cost of one `refineStep` evaluation (signature of size `n-1` + sort + encode).
Kept linear in `n` (the sort's log factor and the unit-cost-colour declaration, §HONESTY above, are folded
into the per-primitive constant). Adjusting `sigCost` only changes the degree in `warmRefineCost_eq`. -/
def sigCost (n : Nat) : Nat := n

/-- One refinement round recolours all `n` vertices: `n` `refineStep` evaluations. -/
def roundCost (n : Nat) : Nat := n * sigCost n

/-- `warmRefine`'s cost: `n` rounds (`warmRefine_eq_iterate`), each `roundCost n`. This is the refinement
summand of the pilot's per-node bound `w n` (`w n = warmRefineCost n + oracleCost n + selectCost n`). -/
def warmRefineCost (n : Nat) : Nat := n * roundCost n

/-- **The refinement per-node cost is cubic in `n`** (explicit degree, D5): `n·n·n` (= `n³`). Under the
declared `sigCost n = n`, this is exact. -/
theorem warmRefineCost_eq (n : Nat) : warmRefineCost n = n * n * n := by
  unfold warmRefineCost roundCost sigCost
  exact (Nat.mul_assoc n n n).symm

/-- The bound form used by the pilot's `w` (`n³`, D5). -/
theorem warmRefineCost_le (n : Nat) : warmRefineCost n ≤ n * n * n :=
  (warmRefineCost_eq n).le

end ChainDescent.CostModel.WarmRefine
