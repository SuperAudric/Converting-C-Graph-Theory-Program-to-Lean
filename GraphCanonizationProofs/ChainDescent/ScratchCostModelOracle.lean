/-
# ScratchCostModelOracle.lean — the ORACLE summand of the per-node cost `w` (core-only, WIP, NOT in build.sh)

The second constituent of the per-node bound `w n = warmRefineCost n + oracleCost n + selectCost n`
(cost-model doc §4). `warmRefineCost` (the refinement summand) is landed; this brick adds **`oracleCost`** — the
per-node **orbit-harvest** cost, and with it the piece that makes the flag actually FIRE and the confinement-P1
largeness clause statable on the cost side.

**The model (D7-declared, like the warmRefine brick).** At a descent node with individualization base of size
`b`, the orbit-harvest explores ≤ `n^b` candidate maps (a base-`b` stabiliser chain). So the declared harvest
cost is `oracleCost n b = n^b`. The real harvest is the C#/abstract oracle; here it is a *declared* cost as a
function of the node's base — exactly the cost-model's D7 surface.

**Why this is the correctness-critical summand (cost-model §7a / confinement-P1).** The per-node BUDGET is the
harvest cost at the **small-`Aut` base threshold** `baseMax n = log₂ n` (from `exists_greedy_base_le_log`: small
`Aut` ⟹ base `O(log n)`). A node whose base is ≤ `baseMax` costs ≤ budget ⟹ **does not flag**; a node that
flags therefore has base > `baseMax` ⟹ **large `Aut`** — which is precisely the confinement-P1 largeness step.
So this brick supplies the cost half of P1: `oracleCost_le_budget_of_base_le` + `not_flagsAt_of_base_le`.

**Quasipoly, honestly.** `oracleBudget n = n^{log₂ n}` is *quasipoly*, not poly — matching the doc's quasipoly
pilot. The poly target needs the poly branching/base bound (R1); it drops into `baseMax`/`oracleBudget` verbatim,
the P1 lemmas unchanged.

Core-only (`Nat`), axiom target `[propext, Quot.sound]`. Imports the per-node cost core. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchCostModelPerNode

namespace ChainDescent.CostModel.Oracle

open ChainDescent.CostModel
open ChainDescent.CostModel.PerNode

variable {σ : Type u}

/-- **Declared per-node harvest cost at base `b`.** The orbit-harvest at an individualization base of size `b`
explores ≤ `n^b` candidate maps (a base-`b` stabiliser chain), so the declared cost is `n^b`. D7 surface — the
real harvest is the abstract/C# oracle. -/
def oracleCost (n b : Nat) : Nat := n ^ b

/-- **The base threshold** `(log₂ n)²` (superlogarithmic). A node whose harvest base exceeds this is "large"
(the confinement-P1 largeness cut). **Why `(log₂ n)²`, not `log₂ n` (the threshold decision, 2026-07-08):** the
flag delivers `residual > 2^(baseMax n)`, so the threshold sets the largeness the confinement lemma can rely on.
`log₂ n` gives only `residual > n`, which is **unsound** — a poly-`Aut` non-Schurian SRG (e.g. a Chang graph,
`|Aut| = 384 > 28 = n`) would flag and be assume-VT-pruned *incorrectly*. A **superlogarithmic** threshold
`baseMax = ω(log n)` makes the flag fire **only** for super-polynomial `|Aut|` (`2^{(log₂ n)²} = n^{log₂ n}`,
super-poly): for any fixed poly degree `c`, `c·log₂ n ≤ (log₂ n)²` for large `n`, so every poly-`Aut` residue is
below threshold and does **not** flag. Super-poly-`Aut` rank-3 residues are Schurian/classified (Cameron/Babai),
where assume-VT is sound. The lemmas below are threshold-agnostic (they use only `b ≤ baseMax ⟹ n^b ≤ n^{baseMax}`),
so raising the threshold leaves them unchanged; the budget `oracleBudget n = n^{(log₂ n)²}` stays **quasipoly**. -/
def baseMax (n : Nat) : Nat := (Nat.log2 n) ^ 2

/-- **The per-node oracle BUDGET** = harvest cost at the threshold base = `n^{log₂ n}` (QUASIPOLY). A node with
base ≤ `baseMax` fits; a node with base > `baseMax` exceeds it and flags. The poly target sharpens `baseMax`
(via R1); the lemmas below are unchanged. -/
def oracleBudget (n : Nat) : Nat := n ^ (baseMax n)

/-- **P1, oracle half: small base ⟹ harvest within budget.** For `b ≤ baseMax n` (a small-`Aut` residue),
`oracleCost n b ≤ oracleBudget n`. Contrapositive: harvest over budget ⟹ `base > baseMax` ⟹ large `Aut`. -/
theorem oracleCost_le_budget_of_base_le {n b : Nat} (hn : 1 ≤ n) (h : b ≤ baseMax n) :
    oracleCost n b ≤ oracleBudget n :=
  Nat.pow_le_pow_right hn h

/-! ## The full per-node cost (refinement + harvest) and the flag interface

`warmCost` (= `warmRefineCost n`, the refinement summand) is passed in so this brick stays core-only /
Mathlib-free; the spine instance supplies the concrete `warmRefineCost n`. -/

/-- **The node's TRUE per-node cost** = refinement + harvest = `warmCost + oracleCost n b`. -/
def nodeCost (warmCost n b : Nat) : Nat := warmCost + oracleCost n b

/-- **The per-node BUDGET `w`** = refinement + oracle budget = `warmCost + oracleBudget n`. -/
def nodeBudget (warmCost n : Nat) : Nat := warmCost + oracleBudget n

/-- **P1, full cost half: small base ⟹ node within budget.** -/
theorem nodeCost_le_budget_of_base_le {warmCost n b : Nat} (hn : 1 ≤ n) (h : b ≤ baseMax n) :
    nodeCost warmCost n b ≤ nodeBudget warmCost n :=
  Nat.add_le_add_left (oracleCost_le_budget_of_base_le hn h) warmCost

/-- **The confinement-P1 cost interface: a small-base node does NOT flag.** With the per-node budget
`w = nodeBudget warmCost n` and a `step` whose true cost is the honest `nodeCost warmCost n b`, a node with
`base ≤ baseMax n` (small `Aut`) never fires the flag (`flagsAt = false`). **The contrapositive is P1's
largeness clause: a Phase-1 flag ⟹ base > baseMax n ⟹ large `Aut`** — which (with P2/P3) forces the residue to
be primitive rank-3 / VT, making the assume-VT prune sound. This is where the cost model and correctness
interlock. -/
theorem not_flagsAt_of_base_le {warmCost n b : Nat} (hn : 1 ≤ n) (h : b ≤ baseMax n)
    (step : σ → CostM σ) (s : σ) (hstep : (step s).2 = nodeCost warmCost n b) :
    flagsAt step (nodeBudget warmCost n) s = false := by
  rw [flagsAt, decide_eq_false_iff_not, hstep]
  exact Nat.not_lt.mpr (nodeCost_le_budget_of_base_le hn h)

end ChainDescent.CostModel.Oracle
