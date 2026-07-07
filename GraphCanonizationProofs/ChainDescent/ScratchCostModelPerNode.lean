/-
# ScratchCostModelPerNode.lean — the per-node-flag / per-node-cap cost variant (WIP, core-only, NOT in build.sh)

**What this adds over `ScratchCostModel`.** The landed `budgetedIterate` flags on *global* budget exhaustion and
needs `hstep : ∀ s, (step s).2 ≤ w` to bound the cost. This module adds the **per-node cap**: each node charges
`min (trueCost) w`, so ② (`cost ≤ nbud · w`) holds **unconditionally — with NO `hstep`**, even when the true
per-node cost is unknown or unbounded (e.g. a quasipoly harvest). The per-node budget relocates the cost assumption
*into the algorithm*, which is exactly the confinement / assume-VT design: a node whose harvest exceeds `w` does not
break the bound — it *flags*, and the flag's **phase** decides the action (symmetric ⟹ assume-VT-prune-and-continue;
rigid ⟹ honest unhandled `none`).

**Attachment point (scoping, 2026-07-07).** The concrete descent this instantiates over is **`defaultSpineChain`**
(`Spine.lean`): its node bound is *already proven* — `defaultSpineChain_reaches_leaf : ∃ k ≤ n, IsLeaf` gives
`nbud = n`; correctness rides `spine_branch_independent` + `SpineChain.canonAdj` (the output → `canonForm?`); the
per-node work is `warmRefine adj chain.P chain.χι` + oracle (the `w` of `ScratchCostModelWarmRefine`). It is
single-path (matches assume-VT `leaves = 1`), so the `≤ n` path is the whole cost — no branch-frontier σ needed.

Core-only (`Nat`/`Option`/`Prod`), axiom-clean `[propext, Quot.sound]`, `lake env lean`. Imports the core framework.
-/
import ChainDescent.ScratchCostModel

namespace ChainDescent.CostModel.PerNode

open ChainDescent.CostModel

variable {σ : Type u}

/-- The two descent phases (deferred-decisions model). `symmetric` = Phase 1 (residual symmetry to consume; a
per-node over-budget here triggers assume-VT-prune and CONTINUES). `rigid` = Phase 2 (the deferred rigid residue; a
per-node over-budget here is the honest unhandled flag). The flag's phase discriminates the `UnhandledResidue` atom
(`Publication.lean`). -/
inductive Phase | symmetric | rigid
  deriving DecidableEq, Repr

/-- **The per-node cap.** Charge `min (trueCost) w` for one step: the value is unchanged, the cost is capped at the
per-node budget `w`. This is the sole difference from the global-budget `budgetedIterate` — the cap is what makes ②
unconditional. -/
def capStep (step : σ → CostM σ) (w : Nat) : σ → CostM σ :=
  fun s => ((step s).1, min (step s).2 w)

@[simp] theorem value_capStep (step : σ → CostM σ) (w : Nat) (s : σ) :
    (capStep step w s).1 = (step s).1 := rfl

/-- Every capped step charges `≤ w` by construction — the `hstep` hypothesis, now free. -/
theorem cost_capStep_le (step : σ → CostM σ) (w : Nat) (s : σ) : (capStep step w s).2 ≤ w :=
  Nat.min_le_right _ _

/-- **② is UNCONDITIONAL under per-node capping — no `hstep`.** Each node charges `≤ w` by construction
(`cost_capStep_le`), so a whole run over `fuel` nodes costs `≤ fuel · w` for ANY underlying `step`, even one whose
true per-node cost is unknown or unbounded. The per-node refinement of `cost_budgetedIterate_le`: capping relocates
the `∀ s, (step s).2 ≤ w` assumption into the algorithm. -/
theorem cost_budgetedIterate_capped_le (step : σ → CostM σ) (done : σ → Bool) (w fuel : Nat) (s : σ) :
    (budgetedIterate (capStep step w) done fuel s).2 ≤ fuel * w :=
  cost_budgetedIterate_le (capStep step w) done w (cost_capStep_le step w) fuel s

/-- **A per-node flag fires** at a node when the step's TRUE cost exceeds the per-node budget `w` (the harvest was
too expensive). `capStep` still charges only `w`, so ② is unaffected; the flag is a value-level event, and its
phase (below) decides the action. -/
def flagsAt (step : σ → CostM σ) (w : Nat) (s : σ) : Bool := decide (w < (step s).2)

theorem flagsAt_iff (step : σ → CostM σ) (w : Nat) (s : σ) :
    flagsAt step w s = true ↔ w < (step s).2 := by
  unfold flagsAt; exact decide_eq_true_iff

/-- When a node does not flag, the cap is vacuous — it charged the true cost. -/
theorem capStep_cost_eq_of_not_flags (step : σ → CostM σ) (w : Nat) (s : σ)
    (h : flagsAt step w s = false) : (capStep step w s).2 = (step s).2 := by
  have : ¬ w < (step s).2 := by rw [← flagsAt_iff]; simp [h]
  show min (step s).2 w = (step s).2
  omega

/-! ## The packaged per-node-capped canonizer (② for free, no obligation) -/

/-- A **per-node-capped** canonizer: like `BudgetedCanonizer`, but the per-node cap is built in, so there is **no
`hstep` field** — ② holds for any `step`. This is the shape `canonForm?`-over-`defaultSpineChain` instantiates:
`step` = one spine level (refine + oracle), `nbud n = n` (`defaultSpineChain_reaches_leaf`), `w n` = the warmRefine
+ oracle per-node bound. -/
structure CappedCanonizer (σ : Type u) where
  step : σ → CostM σ
  done : σ → Bool
  nbud : Nat → Nat
  w : Nat → Nat

/-- Run the capped canonizer: the per-node cap is applied at every step. -/
def CappedCanonizer.run (M : CappedCanonizer σ) (n : Nat) (s₀ : σ) : CostM (Option σ) :=
  budgetedIterate (capStep M.step (M.w n)) M.done (M.nbud n) s₀

/-- **② for a capped canonizer — unconditional, no obligation.** `cost (run) ≤ nbud n · w n`, with no hypothesis
on the step's true cost. The explicit polynomial budget `costConst · n^costDeg` is `nbud n · w n`. -/
theorem CappedCanonizer.cost_run_le (M : CappedCanonizer σ) (n : Nat) (s₀ : σ) :
    (M.run n s₀).2 ≤ M.nbud n * M.w n :=
  cost_budgetedIterate_capped_le M.step M.done (M.w n) (M.nbud n) s₀

/-- Completion soundness carries over unchanged: a `some` result is a `done` (leaf) state. -/
theorem CappedCanonizer.done_of_run_some (M : CappedCanonizer σ) (n : Nat) (s₀ s' : σ)
    (h : (M.run n s₀).1 = some s') : M.done s' :=
  done_of_budgetedIterate_some (capStep M.step (M.w n)) M.done (M.nbud n) s₀ s' h

end ChainDescent.CostModel.PerNode
