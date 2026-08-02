/-
# Examples.lean — runnable examples for the Lean canonizer

Not part of any build target (like `Publication.lean`, it sits at the package root rather than
under `ChainDescent/`, so neither `lake build` nor `scripts/build.sh` compiles it). Run it with:

    cd GraphCanonizationProofs
    lake env lean Examples.lean

Every `#eval` below prints its result. See `docs/USER-GUIDE.md` for what the output means and for
the C# path, which is the one to use if you actually want to canonize graphs.

⚠ SPEED. This is the Lean definition run by the Lean interpreter. Measured on this repo: the
whole file below is ~8 s once mathlib is in the page cache, and a 5-cycle is ~32 s; a cold first
run is much slower because it pays to load mathlib. It degrades steeply past that — the project's
own `n = 15` regression case takes ~410 s. That is the cost of interpreting the proof object, not
a property of the algorithm. Use the C# implementation for anything real.
-/
import ChainDescent.RecordKey
import ChainDescent.RecordCost
import ChainDescent.Select

open ChainDescent

/-- The canonizer. This is character-for-character the definition of `Publication.canonForm?`;
it is repeated here so this file depends on no `axiom` and no `sorry`.

`AdjMatrix n` is a structure wrapping `adj : Fin n → Fin n → Nat`, so edge "colours" are
naturals rather than booleans — `0` means no edge. -/
def canonForm? (n : ℕ) (G : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  Select.canonFormFastS? (RecordKey.recordKey (n := n)) (RecordCost.recordSupplyFast (n := n)) G

/-- Build an `AdjMatrix` from an undirected edge list. -/
def ofEdges (n : ℕ) (es : List (Fin n × Fin n)) : AdjMatrix n :=
  ⟨fun i j => if es.any (fun e => (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i)) then 1 else 0⟩

/-- `canonForm?` returns a *function*, which `#eval` cannot print. Render it as rows. -/
def rows? (n : ℕ) (G : AdjMatrix n) : Option (List (List Nat)) :=
  (canonForm? n G).map fun f =>
    (List.finRange n).map fun i => (List.finRange n).map fun j => f i j

/-! ## 1. A triangle

Every labelling of `K₃` is the same graph, so there is nothing to decide.
Expect `some [[0,1,1],[1,0,1],[1,1,0]]`. -/

#eval rows? 3 (ofEdges 3 [(0,1),(1,2),(0,2)])

/-! ## 2. The point of a canonizer: two labellings, one answer

`0-1-2` and `1-2-0` are the same path, written differently. The canonical forms are equal,
and that equality is what `canon_complete` proves in general — same form iff isomorphic. -/

#eval rows? 3 (ofEdges 3 [(0,1),(1,2)])          -- some [[0,0,1],[0,0,1],[1,1,0]]
#eval rows? 3 (ofEdges 3 [(1,2),(2,0)])          -- identical to the line above

/-! ## 3. Same again on four vertices -/

#eval rows? 4 (ofEdges 4 [(0,1),(1,2),(2,3)])    -- some [[0,0,0,1],[0,0,1,0],[0,1,0,1],[1,0,1,0]]
#eval rows? 4 (ofEdges 4 [(3,1),(1,0),(0,2)])    -- identical

/-! ## 4. Comparing two graphs

Canonize both and compare. `none` on either side means the canonizer *flagged* — it declined to
answer rather than answering wrongly, which is the `canon_poly_or_flag` escape hatch. A flag is
not a failure of correctness; it is the residue the project never closed. -/

def sameGraph? (n : ℕ) (G H : AdjMatrix n) : Option Bool :=
  match canonForm? n G, canonForm? n H with
  | some cg, some ch => some (decide (∀ i j, cg i j = ch i j))
  | _, _ => none

#eval sameGraph? 4 (ofEdges 4 [(0,1),(1,2),(2,3)]) (ofEdges 4 [(3,1),(1,0),(0,2)])  -- some true
#eval sameGraph? 4 (ofEdges 4 [(0,1),(1,2),(2,3)]) (ofEdges 4 [(0,1),(2,3)])        -- some false
