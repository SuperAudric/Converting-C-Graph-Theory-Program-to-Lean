/-
# ScratchCostModelSpine.lean — the CappedCanonizer instance over `defaultSpineChain` (WIP, NOT in build.sh)

The seam crossing: instantiate the core per-node-capped cost model (`ScratchCostModelPerNode`) over the **real**
Mathlib-heavy spine descent (`defaultSpineChain`, `Spine.lean`). This turns ② from an abstract framework theorem
into a **concrete polynomial cost bound on the actual canonizer's descent**.

**The instance.** State `σ = ℕ` = the descent level `k` (the spine is a *function* of `k`:
`defaultSpineChain adj P₀ χι₀ sel : Nat → SpineChain … k`). One step advances a level; the node budget is `n`
(the proven descent depth `defaultSpineChain_reaches_leaf : ∃ k ≤ n, IsLeaf`); the per-node bound is
`warmRefineCost n` (the per-level warmRefine cost, `ScratchCostModelWarmRefine`). `done k` = the level-`k`
partition is discrete (a leaf).

**Result.** `spineCappedCanonizer_cost_le`: the capped run costs `≤ n · warmRefineCost n = n⁴`, **unconditionally**
— the per-node cap discharges ② with no per-node-cost hypothesis (a quasipoly oracle, added later, would flag, not
break the bound). This is the first *concrete* ② discharge on the real descent; it matches the C# `DefaultBudget`'s
`16·n⁴` shape.

**Not yet here (next sub-steps):** completeness (`defaultSpineChain_reaches_leaf` ⟹ the run returns `some`, not a
flag — the ③-forward side); the output map `canonForm? = leaf.canonAdj`; the oracle summand of `w`.

Imports the Mathlib spine — expect slower compiles. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.ScratchCostModelPerNode
import ChainDescent.ScratchCostModelWarmRefine
import ChainDescent.Spine

namespace ChainDescent.CostModel.SpineInstance

open ChainDescent
open ChainDescent.CostModel
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.WarmRefine

variable {n : Nat}

open scoped Classical in
/-- **The per-node-capped canonizer over the real spine.** `σ = ℕ` is the descent level: `step` advances one level
charging the warmRefine per-level cost; `done` = the level-`k` partition is discrete (`IsLeaf`); node budget `n`
(the proven depth); per-node bound `w = warmRefineCost n`. `noncomputable` only because `done` uses classical
decidability of discreteness — irrelevant to the cost bound, which holds for any `done`. -/
noncomputable def spineCappedCanonizer (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : CappedCanonizer Nat where
  step := fun k => (k + 1, warmRefineCost n)
  done := fun k => decide (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf
  nbud := fun _ => n
  w := fun _ => warmRefineCost n

/-- **② over the real spine (concrete, unconditional).** The capped run over `defaultSpineChain` costs
`≤ n · warmRefineCost n = n · n³ = n⁴`. No per-node-cost hypothesis — the cap makes ② free even if a later oracle
summand of `w` is quasipoly (it would flag via `flagsAt`, not break this bound). The node budget `n` is the proven
descent depth (`defaultSpineChain_reaches_leaf`); `warmRefineCost n = n³` is the per-level warmRefine cost. -/
theorem spineCappedCanonizer_cost_le (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (s₀ : Nat) :
    ((spineCappedCanonizer adj P₀ χι₀ sel).run n s₀).2 ≤ n * (n * n * n) := by
  have h := CappedCanonizer.cost_run_le (spineCappedCanonizer adj P₀ χι₀ sel) n s₀
  have hw : (spineCappedCanonizer adj P₀ χι₀ sel).nbud n
      * (spineCappedCanonizer adj P₀ χι₀ sel).w n = n * (n * n * n) := by
    simp [spineCappedCanonizer, warmRefineCost_eq]
  rwa [hw] at h

end ChainDescent.CostModel.SpineInstance
