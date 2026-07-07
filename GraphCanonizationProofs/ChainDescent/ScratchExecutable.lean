/-
# ScratchExecutable.lean — the executable track (Tier A demo: the descent RUNS) (WIP, NOT in build.sh)

Home for the "raise the Lean canonizer to executable form" track (docs: cost-model / executable scope). **Tier A**
= the per-node-capped descent is now *computable* (`Decidable (Discrete)` replaced the `Classical` `done`, so
`spineCappedCanonizer`/`descent`/`descentResult`/`descentCost` reduce). This file demonstrates it by `#eval`-ing the
descent on a concrete graph — the first time any of the runtime object actually executes.

Still noncomputable (Tier B/C): the OUTPUT `canonForm?`/`canonFormOf` (via the `Classical.choose` leaf extraction +
`Equiv.ofBijective` rank permutation + the exponential lex-min `canonForm`). Tier A only makes the DESCENT run.
-/
import ChainDescent.ScratchCanonFormCapped

namespace ChainDescent.Executable

open ChainDescent
open ChainDescent.CanonForm

/-- A concrete tiny graph: the triangle `K₃` (complete graph on 3 vertices). -/
def triangle : AdjMatrix 3 := ⟨fun i j => if i = j then 0 else 1⟩

/-- A concrete tiny graph: the path `0–1–2`. -/
def path3 : AdjMatrix 3 := ⟨fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
                                         ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 else 0⟩

-- Tier A validation: the descent RUNS (these `#eval`s reduce — the runtime executes).
#eval descentResult triangle   -- expected: `some k` (a leaf level ≤ 3)
#eval descentCost triangle     -- expected: a concrete Nat (capped cost)
#eval descentResult path3
#eval descentCost path3

end ChainDescent.Executable
