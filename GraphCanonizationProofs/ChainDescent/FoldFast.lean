import ChainDescent.HolKey

/-!
# The F2a evaluation constant — `foldSupplyFast`, the materialised-table twin of `foldSupply`

## What this is (`docs/chain-descent-fold-tower-plan.md` §5b follow-on; `HolKey.lean` Build-state note)

`foldSupply`'s rfl-twins (`swapFunFast`/`swapCandFast`) bind each `relComp` closure once **per candidate
call** — but the supply makes `|cell|²` candidate calls, each of which recomputes the closures of its two
seed copies and (inside the involution gate) the fiber closure of every vertex. At `n = 30` that recomputation
is what blocked the F3a composite measurement (`HolKey.lean` §Build-state). This file materialises the
component-membership tables **once per supply call** and reads everything off forced data — the same move as
F3a's `compTbl`, adapted to F2a.

## ⚠ Why membership ROWS, not `compIdx` id-tables (a real caveat, worth keeping)

The F3a id-table equivalence `compIdx_eq_iff` (id-equality ⟺ component membership) requires the relation to
be **symmetric** — that is why F3a symmetrizes (`symSame`/`symCross`). F2a's spec is older and uses the
**directed** closures `relComp (sameCellRel adj χ) b` / `relComp (crossCellRel adj χ) b` from a base vertex;
on an asymmetric `AdjMatrix` those are reachability sets, not equivalence classes, and id-equality would NOT
be value-equal to the spec's membership tests. So the port materialises the membership **rows**
(`compRow rel b = the Boolean row of relComp rel b`) — value-equal to the spec **by construction**, no
symmetry needed, same `O(1)`-read eval constant. `foldSupply`'s definition is untouched: the twin is a
separate function with a proved function-level equality (`foldSupplyFast_eq`), so every theorem about
`foldSupply` — capstones, equivariance, firing — transfers by rewriting.

## Contents

- `compRow`/`compRows` — the forced membership tables (data, not functions — trap #1), `compRows_get`.
- `swapFunT`/`swapCandT` — the table-reading candidate constructor; value-equality `swapFunT_eq`/`swapCandT_eq`.
- `foldSupplyFast` + **`foldSupplyFast_eq`** — the supply twin and its bridge (tables bound once per call).
- Equivariance transfers (`gensEquivariant_foldSupplyFast`, `supplyEquivariant_foldSupplyFast`) and
  **`holKey_foldDeckFast_selNode_canonizer`** — the F3a canonizer of record with every component in its
  runnable form (force = `holKeyFast`, consume = `foldSupplyFast ++ deckSupply`).
-/

namespace ChainDescent
namespace Fold

open ChainDescent.Descend
open ChainDescent.Consume (Supply)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)

variable {n : Nat}

/-! ## 1. The forced membership tables -/

/-- The Boolean membership row of `relComp rel b` — the closure is computed ONCE (the `let`), then read
`n` times. Data, not a function (trap #1). -/
def compRow (rel : Fin n → Fin n → Bool) (b : Fin n) : Vector Bool n :=
  let C := relComp rel b
  Vector.ofFn (fun w => decide (w ∈ C))

/-- All membership rows: entry `b` is the row of `relComp rel b`. `n` closures per table, once per supply
call — replacing the per-candidate recomputation. -/
def compRows (rel : Fin n → Fin n → Bool) : Vector (Vector Bool n) n :=
  Vector.ofFn (fun b => compRow rel b)

theorem compRows_get (rel : Fin n → Fin n → Bool) (b w : Fin n) :
    ((compRows rel).get b).get w = decide (w ∈ relComp rel b) := by
  simp [compRows, compRow, Vector.get]

/-! ## 2. The table-reading candidate constructor -/

/-- `swapFun`, reading the forced tables: all component-membership tests are `O(1)` `.get`s and the
unique-partner scan is `Deck.uniqueFilter` with an `O(1)` predicate. -/
def swapFunT (sameR crossR : Vector (Vector Bool n) n) (u₁ u₂ : Fin n) (v : Fin n) : Fin n :=
  let A := crossR.get u₁
  let B := crossR.get u₂
  if A.get v then
    let fib := sameR.get v
    (Deck.uniqueFilter (fun w => fib.get w && B.get w)).getD v
  else if B.get v then
    let fib := sameR.get v
    (Deck.uniqueFilter (fun w => fib.get w && A.get w)).getD v
  else v

/-- **The table form computes exactly the spec form** (at the tables of the right relations). -/
theorem swapFunT_eq (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ v : Fin n) :
    swapFunT (compRows (sameCellRel adj χ)) (compRows (crossCellRel adj χ)) u₁ u₂ v
      = swapFun adj χ u₁ u₂ v := by
  simp only [swapFunT, swapFun, compRows_get, Deck.uniqueFilter_eq_uniqueMem,
    decide_eq_true_eq]

/-- The candidate constructor over the forced tables (involution gate unchanged). -/
def swapCandT (sameR crossR : Vector (Vector Bool n) n) (u₁ u₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  if h : ∀ v, swapFunT sameR crossR u₁ u₂ (swapFunT sameR crossR u₁ u₂ v) = v then
    some (Function.Involutive.toPerm _ h)
  else none

theorem swapCandT_eq (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    swapCandT (compRows (sameCellRel adj χ)) (compRows (crossCellRel adj χ)) u₁ u₂
      = swapCand adj χ u₁ u₂ := by
  have hfe : ∀ x, swapFunT (compRows (sameCellRel adj χ)) (compRows (crossCellRel adj χ)) u₁ u₂ x
      = swapFun adj χ u₁ u₂ x := swapFunT_eq adj χ u₁ u₂
  unfold swapCandT swapCand
  by_cases h : ∀ x, swapFun adj χ u₁ u₂ (swapFun adj χ u₁ u₂ x) = x
  · rw [dif_pos (fun x => by rw [hfe, hfe]; exact h x), dif_pos h]
    exact congrArg some (Equiv.ext fun x => hfe x)
  · rw [dif_neg (fun hc => h fun x => by rw [← hfe, ← hfe]; exact hc x), dif_neg h]

/-! ## 3. The supply twin -/

/-- **★ The materialised-table fold supply.** Same enumeration, same gates, same cost bill as `foldSupply` —
the two tables are forced ONCE per supply call (the `let`s) and every candidate reads them. Value-equal
(`foldSupplyFast_eq`), so it IS `foldSupply` for every theorem. -/
def foldSupplyFast : Supply n := fun adj χ =>
  let sameR := compRows (sameCellRel adj χ)
  let crossR := compRows (crossCellRel adj χ)
  let B := branches χ
  (B.flatMap (fun u₁ => B.filterMap (fun u₂ => swapCandT sameR crossR u₁ u₂)),
   B.length * B.length * (n * n * n * n * n))

/-- **★★ The twin is the supply of record** — a function-level equality, so capstones, equivariance and
firing theorems all transfer by rewriting. -/
theorem foldSupplyFast_eq : (foldSupplyFast : Supply n) = foldSupply := by
  funext adj χ
  simp only [foldSupplyFast, foldSupply, swapCandT_eq, swapCandFast_eq]

theorem gensEquivariant_foldSupplyFast : GensEquivariant (foldSupplyFast (n := n)) := by
  rw [foldSupplyFast_eq]
  exact gensEquivariant_foldSupply

theorem supplyEquivariant_foldSupplyFast : SupplyEquivariant (foldSupplyFast (n := n)) := by
  rw [foldSupplyFast_eq]
  exact supplyEquivariant_foldSupply

/-! ## 4. The all-fast capstone of record -/

/-- **★★★ The F3a canonizer of record, every component in its runnable form**: force = `holKeyFast`,
consume = `foldSupplyFast ++ deckSupply`, fused selector. Identical (by `foldSupplyFast_eq` /
`holKeyFast_eq`) to `Hol.holKey_foldDeck_selNode_canonizer`'s object — this is the form the measurements
run. -/
theorem holKey_foldDeckFast_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Hol.holKeyFast (n := n))
          (Deck.appendSupply (foldSupplyFast (n := n)) (Deck.deckSupply (n := n))))) := by
  rw [foldSupplyFast_eq]
  exact Hol.holKey_foldDeck_selNode_canonizer

end Fold
end ChainDescent
