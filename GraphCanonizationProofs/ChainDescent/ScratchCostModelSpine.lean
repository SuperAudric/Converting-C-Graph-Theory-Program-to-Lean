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

**The oracle summand is now wired (2026-07-07, §"Oracle-wired instance" below).** `spineCappedCanonizerO` extends
the warmRefine-only `spineCappedCanonizer` by charging the per-node **orbit-harvest** cost `oracleCost n (baseAt k)`
in addition to the co-defined warmRefine cost, and raising the per-node budget to `nodeBudget = warmRefine +
oracleBudget n`. This is the first instance on which the flag can **actually fire** on the real descent (at a node
whose harvest base exceeds `baseMax n`), and it carries P1's cost half specialized to the spine.

**Not yet here (next sub-steps):** completeness (`defaultSpineChain_reaches_leaf` ⟹ the run returns `some`, not a
flag — the ③-forward side); the output map `canonForm? = leaf.canonAdj`; the **graph-side of P1** (small-`Aut` residue
⟹ `baseAt k ≤ baseMax n`, via `exists_greedy_base_le_log`) that turns `not_flagsAt_of_base_le_spine` from a cost
statement into the largeness contrapositive.

Imports the Mathlib spine — expect slower compiles. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.ScratchCostModelPerNode
import ChainDescent.ScratchCostModelWarmRefine
import ChainDescent.ScratchCostModelCostedWarmRefine
import ChainDescent.ScratchCostModelOracle
import ChainDescent.Spine

namespace ChainDescent.CostModel.SpineInstance

open ChainDescent
open ChainDescent.CostModel
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.WarmRefine
open ChainDescent.CostModel.CostedWarmRefine
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **`Discrete` is decidable** — `∀ i j : Fin n, χ i = χ j → i = j` is a decidable `∀` over a `Fintype` with
`DecidableEq`. Replaces the `Classical` decidability the descent's `done` used, so the descent is **computable**
(Tier A of the executable track). -/
instance decidableDiscrete (χ : Colouring n) : Decidable (Discrete χ) := by
  unfold Discrete; infer_instance

/-- **A leaf is decidable** — `IsLeaf` unfolds to `Discrete chain.partition`. Makes `spineCappedCanonizer.done`
computable (no `Classical`). -/
instance decidableIsLeaf {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) : Decidable chain.IsLeaf := by
  unfold SpineChain.IsLeaf; infer_instance

/-- **The per-node-capped canonizer over the real spine.** `σ = ℕ` is the descent level: `step` advances one level,
charging the **co-defined** per-level cost `(costedWarmRefine adj chₖ.P chₖ.χι).cost` — the actual accumulated cost of
running the refinement loop at level `k` (not a fiat literal; `cost_costedWarmRefine` proves it equals
`warmRefineCost n`). `done` = the level-`k` partition is discrete (`IsLeaf`); node budget `n` (the proven depth);
per-node bound `w = warmRefineCost n`. **Computable** (Tier A): `done` uses the real `decidableIsLeaf`, `step`/`nbud`/`w`
are all computable, so the descent runs. -/
def spineCappedCanonizer (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : CappedCanonizer Nat where
  step := fun k =>
    let ch := defaultSpineChain adj P₀ χι₀ sel k
    (k + 1, (costedWarmRefine adj ch.P ch.χι).cost)
  done := fun k => decide (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf
  nbud := fun _ => n
  w := fun _ => warmRefineCost n

/-- **The per-node charge IS the real co-defined warmRefine cost** = `warmRefineCost n`. This is the seam closed: the
number charged (and capped) per node is the actual accumulated cost of running the refinement loop
(`cost_costedWarmRefine`), not an asserted literal. -/
theorem spineCappedCanonizer_step_cost (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) :
    ((spineCappedCanonizer adj P₀ χι₀ sel).step k).2 = warmRefineCost n :=
  cost_costedWarmRefine adj _ _

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

/-! ## Oracle-wired instance — the flag can now FIRE on the real descent

`spineCappedCanonizer` charges only the warmRefine cost, so its per-node budget `w = warmRefineCost n` is never
exceeded (the object is *total* — the flag never fires; ③ against it would be vacuous). This instance adds the
**oracle summand** `oracleCost n (baseAt k)` to each node's true cost and raises the per-node budget to
`nodeBudget (warmRefineCost n) n = warmRefineCost n + oracleBudget n`. Now a node whose harvest base `baseAt k`
exceeds `baseMax n` charges more than the budget ⟹ **`flagsAt` fires** (`spineCappedCanonizerO_flagsAt_iff`), and a
small-base node provably does **not** flag (`not_flagsAt_of_base_le_spine` = P1's cost half on the spine). The base
`baseAt : Nat → Nat` is abstract here — the concrete "small-`Aut` ⟹ `baseAt k ≤ baseMax n`" link is the graph-side
of P1 (a later step). ② stays unconditional (per-node cap), now at the honest **quasipoly** budget. -/

/-- **The oracle-wired capped canonizer over the real spine.** Same descent as `spineCappedCanonizer`, but each node's
true cost is `warmRefine + oracleCost n (baseAt k)` (co-defined warmRefine + declared harvest at base `baseAt k`), and
the per-node budget is `nodeBudget (warmRefineCost n) n = warmRefineCost n + oracleBudget n`. The flag fires exactly
when the harvest base exceeds the small-`Aut` threshold. -/
def spineCappedCanonizerO (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat) : CappedCanonizer Nat where
  step := fun k =>
    let ch := defaultSpineChain adj P₀ χι₀ sel k
    (k + 1, (costedWarmRefine adj ch.P ch.χι).cost + oracleCost n (baseAt k))
  done := fun k => decide (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf
  nbud := fun _ => n
  w := fun _ => nodeBudget (warmRefineCost n) n

/-- **The oracle-wired per-node charge IS the honest `nodeCost`** = `warmRefineCost n + oracleCost n (baseAt k)` — the
co-defined warmRefine cost (`cost_costedWarmRefine`) plus the declared harvest cost at this node's base. -/
theorem spineCappedCanonizerO_step_cost (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat) (k : Nat) :
    ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step k).2
      = nodeCost (warmRefineCost n) n (baseAt k) := by
  show (costedWarmRefine adj _ _).cost + oracleCost n (baseAt k) = nodeCost (warmRefineCost n) n (baseAt k)
  rw [cost_costedWarmRefine]; rfl

/-- **② over the oracle-wired spine (concrete, unconditional, quasipoly).** The capped run costs
`≤ n · (warmRefineCost n + oracleBudget n)` — the per-node cap discharges ② with no per-node-cost hypothesis even
though the true node cost now includes the (possibly quasipoly) harvest. This is the honest quasipoly ② the pilot
targets; the poly upgrade sharpens `oracleBudget` (via R1), this proof unchanged. -/
theorem spineCappedCanonizerO_cost_le (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat) (s₀ : Nat) :
    ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).run n s₀).2
      ≤ n * (warmRefineCost n + oracleBudget n) := by
  have h := CappedCanonizer.cost_run_le (spineCappedCanonizerO adj P₀ χι₀ sel baseAt) n s₀
  have hw : (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).nbud n
      * (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n = n * (warmRefineCost n + oracleBudget n) := by
    simp [spineCappedCanonizerO, nodeBudget]
  rwa [hw] at h

/-- **The flag FIRES iff the harvest base exceeds the threshold.** With the warmRefine cost common to budget and
charge, it cancels: the node flags exactly when `oracleBudget n < oracleCost n (baseAt k)`, i.e. (for `n ≥ 2`) when
`baseAt k > baseMax n`. The first statement of a *fireable* flag on the actual descent. -/
theorem spineCappedCanonizerO_flagsAt_iff (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat) (k : Nat) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true
      ↔ oracleBudget n < oracleCost n (baseAt k) := by
  rw [flagsAt_iff, spineCappedCanonizerO_step_cost]
  show nodeBudget (warmRefineCost n) n < nodeCost (warmRefineCost n) n (baseAt k) ↔ _
  unfold nodeBudget nodeCost
  exact Nat.add_lt_add_iff_left

/-- **P1, cost half on the real spine: a small-base node does NOT flag.** If the harvest base at node `k` is within
the small-`Aut` threshold (`baseAt k ≤ baseMax n`), the node fits its budget and `flagsAt = false`. The contrapositive
— a Phase-1 flag ⟹ `baseAt k > baseMax n` ⟹ large `Aut` — is the confinement-P1 largeness step; the remaining graph-side
obligation is `small-Aut residue ⟹ baseAt k ≤ baseMax n`. -/
theorem not_flagsAt_of_base_le_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat) (k : Nat)
    (hn : 1 ≤ n) (h : baseAt k ≤ baseMax n) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = false :=
  not_flagsAt_of_base_le hn h (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step k
    (spineCappedCanonizerO_step_cost adj P₀ χι₀ sel baseAt k)

end ChainDescent.CostModel.SpineInstance
