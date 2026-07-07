/-
# ScratchCostModelCostedWarmRefine.lean — the CO-DEFINED warmRefine cost (WIP, NOT in build.sh)

Closes the "fiat cost" seam (D1): the spine cost model charged `warmRefineCost n` as a *literal*, decoupled from the
actual `warmRefine` computation. This module makes it **co-defined** — `costedWarmRefine` runs the *real* refinement
loop in the cost monad, so:
  · `value_costedWarmRefine` — its VALUE is exactly `warmRefine` (all spine correctness transfers unchanged);
  · `cost_costedWarmRefine` — its COST is `warmRefineCost n`, accumulated by the loop (not asserted).

The per-round charge `roundCost n` is the D7-declared cost of one refinement round; the *iteration* (n rounds) and the
*value* (actually running `refineStep`) are co-defined. So "the spine CAN be refined in `n³`" becomes "running the
refinement IS `n³` (co-defined)". This is the Level-1 upgrade; the value-side descent co-definition (σ = descent state)
is the next level.

Also lands the reusable `CostM.iterate` combinator (its `value_iterate` needs Mathlib's `Function.iterate` lemmas, so
it sits here, not in core `ScratchCostModel`). Imports the Mathlib spine — slower compiles. Axiom target
`[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.ScratchCostModel
import ChainDescent.ScratchCostModelWarmRefine

namespace ChainDescent.CostModel

open ChainDescent
open ChainDescent.CostModel.WarmRefine

namespace CostM

variable {α : Type u}

/-- **Costed iteration.** Run a costed step `f` exactly `k` times, threading the value and SUMMING the cost —
matches `pure`/`bind` but written inline to stay unambiguous. -/
def iterate (f : α → CostM α) : Nat → α → CostM α
  | 0, a => (a, 0)
  | (k + 1), a => let r := f a; let r' := iterate f k r.1; (r'.1, r.2 + r'.2)

/-- **The value of a costed iterate is the plain `k`-fold iterate of the value-step** — it computes the real thing. -/
theorem value_iterate (f : α → CostM α) (k : Nat) (a : α) :
    (iterate f k a).value = (fun x => (f x).value)^[k] a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    show (iterate f k (f a).value).value = (fun x => (f x).value)^[k + 1] a
    rw [ih, Function.iterate_succ_apply]

/-- **If each step costs exactly `c`, the whole loop costs `k · c`** — the cost co-defined by the loop. -/
theorem cost_iterate_const (f : α → CostM α) (c : Nat) (hf : ∀ x, (f x).cost = c) :
    ∀ (k : Nat) (a : α), (iterate f k a).cost = k * c := by
  intro k
  induction k with
  | zero => intro a; simp [iterate, cost]
  | succ k ih =>
    intro a
    show (f a).cost + (iterate f k (f a).value).cost = (k + 1) * c
    rw [hf a, ih (f a).value, Nat.succ_mul]
    omega

end CostM

namespace CostedWarmRefine

open ChainDescent.CostModel.CostM

variable {n : Nat}

/-- One costed refinement round: value = the real `refineStep`, cost = the declared per-round cost `roundCost n`. -/
def costedRound (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) : CostM (Colouring n) :=
  (refineStep adj P χ, roundCost n)

/-- **Costed warmRefine** — `n` costed rounds; value and cost co-defined by the loop. -/
def costedWarmRefine (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) : CostM (Colouring n) :=
  CostM.iterate (costedRound adj P) n χ

/-- **The costed warmRefine COMPUTES the real `warmRefine`.** value = `warmRefine`, so every spine correctness theorem
transfers with no re-proof. -/
theorem value_costedWarmRefine (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    (costedWarmRefine adj P χ).value = warmRefine adj P χ := by
  unfold costedWarmRefine
  rw [CostM.value_iterate]
  show (refineStep adj P)^[n] χ = warmRefine adj P χ
  rw [warmRefine_eq_iterate]

/-- **The costed warmRefine COST is `warmRefineCost n` (= n³), accumulated by the loop — not a fiat literal.** -/
theorem cost_costedWarmRefine (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    (costedWarmRefine adj P χ).cost = warmRefineCost n := by
  unfold costedWarmRefine warmRefineCost
  exact CostM.cost_iterate_const (costedRound adj P) (roundCost n) (fun _ => rfl) n χ

end CostedWarmRefine
