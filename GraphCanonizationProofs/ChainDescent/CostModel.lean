/-
# ChainDescent.CostModel — the Runtime-Phase cost model (ported from the ScratchCostModel* cluster)

The operation-count cost model for the descent, and the ② `poly-or-flag` cost side.
Bundles, in dependency order:

  · `CostM` + `budgetedIterate` + `cost_budgetedIterate_le`      (core cost monad + budgeted loop)
  · `WarmRefine` cost accounting (`warmRefineCost n = n³`)
  · `PerNode` per-node cap (`capStep`, `flagsAt`, `CappedCanonizer`) — ② with NO `hstep`
  · `CostedWarmRefine` co-defined cost (`value = warmRefine`, `cost = n³`, closes the D1 seam)
  · `Oracle` summand (`oracleCost`, `baseMax = (log₂ n)²`, `oracleBudget`) — the fireable-flag threshold
  · `SpineInstance` — attaches to `defaultSpineChain`: `spineCappedCanonizer_cost_le` (`cost ≤ n⁴`,
    unconditional) + `spineCappedCanonizerO` (the FIREABLE-flag object).

Axiom-clean `[propext, Classical.choice, Quot.sound]`. Ported 2026-07-09 from:
ScratchCostModel, ScratchCostModelWarmRefine, ScratchCostModelPerNode,
ScratchCostModelCostedWarmRefine, ScratchCostModelOracle, ScratchCostModelSpine.
-/
import ChainDescent
import ChainDescent.Spine


/- ═══════════════════════════ (was ScratchCostModel.lean) ═══════════════════════════ -/


namespace ChainDescent.CostModel

universe u v

variable {α : Type u} {β : Type v} {σ : Type u}

/-! ## 1. The cost monad (D1)

`CostM α = α × Nat`: a value paired with its operation count (ticks). Cost is composed with the value, so it
is tied to the actual computation rather than tracked by a parallel bookkeeping function. Writing the future
`canonForm?` in this monad makes `cost` and `canonForm?` co-defined (the D1 recommendation). -/

/-- The cost monad: a value paired with an operation count. -/
abbrev CostM (α : Type u) : Type u := α × Nat

namespace CostM

/-- Extract the computed value. -/
def value (x : CostM α) : α := x.1
/-- Extract the accumulated operation count. -/
def cost (x : CostM α) : Nat := x.2

/-- A pure value costs nothing. -/
def pure (a : α) : CostM α := (a, 0)
/-- Charge `k` operations. -/
def tick (k : Nat) : CostM Unit := ((), k)
/-- Sequence two costed computations, adding their costs. -/
def bind (x : CostM α) (f : α → CostM β) : CostM β := ((f x.1).1, x.2 + (f x.1).2)

@[simp] theorem value_pure (a : α) : value (pure a) = a := rfl
@[simp] theorem cost_pure (a : α) : cost (pure a) = 0 := rfl
@[simp] theorem cost_tick (k : Nat) : cost (tick k) = k := rfl
@[simp] theorem value_bind (x : CostM α) (f : α → CostM β) : value (bind x f) = value (f (value x)) := rfl
@[simp] theorem cost_bind (x : CostM α) (f : α → CostM β) :
    cost (bind x f) = cost x + cost (f (value x)) := rfl

end CostM

/-! ## 2. The budgeted process (D2 + D3 + D4)

A `step : σ → CostM σ` is one costed descent action (refine + oracle + individualize). `budgetedIterate`
runs it up to `fuel` times (fuel = node budget), stopping at a `done` state (a discrete leaf), and **flags**
(`none`) if the budget is exhausted first. Cost accumulates along the path taken. -/

/-- Run `step` from `s`, at most `fuel` times, stopping when `done`. Returns `some s'` on reaching a `done`
state within budget, else `none` (a FLAG). This is the abstract shape of the budgeted descent: `fuel` is the
node budget `Nbud`, each `step` charges the per-node work. -/
def budgetedIterate (step : σ → CostM σ) (done : σ → Bool) : Nat → σ → CostM (Option σ)
  | 0, s => if done s then (some s, 0) else (none, 0)
  | (fuel + 1), s =>
      if done s then (some s, 0)
      else
        let s' := step s
        let r := budgetedIterate step done fuel s'.1
        (r.1, s'.2 + r.2)

/-- **The ② mechanism (unconditional).** If every step costs `≤ w`, then a whole budgeted run costs
`≤ fuel · w` — with NO hypothesis on `done`, the path, or the state. Setting the budget `= fuel · w` makes
`cost ≤ budget` hold by construction; the disjunction `∨ flag` in `canon_poly_or_flag` is therefore
discharged by the left side always. Poly-completeness ("handled ⟹ returns `some`") is a *separate*
statement (③-forward), not this one. -/
theorem cost_budgetedIterate_le (step : σ → CostM σ) (done : σ → Bool) (w : Nat)
    (hstep : ∀ s, (step s).2 ≤ w) :
    ∀ (fuel : Nat) (s : σ), (budgetedIterate step done fuel s).2 ≤ fuel * w := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    simp only [budgetedIterate]
    split <;> simp
  | succ f ih =>
    intro s
    simp only [budgetedIterate]
    split
    · simp
    · have h1 := hstep s
      have h2 := ih (step s).1
      have hexp : (f + 1) * w = f * w + w := Nat.succ_mul f w
      show (step s).2 + (budgetedIterate step done f (step s).1).2 ≤ (f + 1) * w
      omega

/-- **Completion soundness.** If the budgeted run returns `some s'`, then `s'` is a `done` (discrete-leaf)
state — the flag is emitted *exactly* when no `done` state was reached within budget. (The value-side
companion of the cost bound; used later to connect `canonForm? = none` to "did not discretize in budget".) -/
theorem done_of_budgetedIterate_some (step : σ → CostM σ) (done : σ → Bool) :
    ∀ (fuel : Nat) (s s' : σ), (budgetedIterate step done fuel s).1 = some s' → done s' := by
  intro fuel
  induction fuel with
  | zero =>
    intro s s' h
    simp only [budgetedIterate] at h
    split at h
    · rename_i hd; simp only [Option.some.injEq] at h; subst h; exact hd
    · simp at h
  | succ f ih =>
    intro s s' h
    simp only [budgetedIterate] at h
    split at h
    · rename_i hd; simp only [Option.some.injEq] at h; subst h; exact hd
    · exact ih (step s).1 s' h

/-! ## 3. The cost-model interface for a canonizer (D2 + D5 + D6)

Packages the budget as `Nbud · w` with an explicit polynomial node budget and per-node bound, both in the
vertex count `n`. A concrete canonizer supplies `step`/`done`/`Nbud`/`w`; the cost bound is then free. -/

/-- A budgeted canonizer over states `σ` for an `n`-vertex input: one costed `step`, a `done` predicate, an
explicit polynomial **node budget** `nbud n` (D5/D6: `= C·nᵏ`), and a per-node cost bound `w n`. -/
structure BudgetedCanonizer (σ : Type u) where
  step : σ → CostM σ
  done : σ → Bool
  nbud : Nat → Nat
  w : Nat → Nat
  hstep : ∀ n s, (step s).2 ≤ w n

/-- Run the canonizer on an initial state for an `n`-vertex input. -/
def BudgetedCanonizer.run (M : BudgetedCanonizer σ) (n : Nat) (s₀ : σ) : CostM (Option σ) :=
  budgetedIterate M.step M.done (M.nbud n) s₀

/-- **② for any budgeted canonizer, unconditional.** `cost (run) ≤ nbud n · w n` — the explicit polynomial
budget `costConst · n^costDeg` is `nbud n · w n`. Discharges `canon_poly_or_flag` via the left disjunct. -/
theorem BudgetedCanonizer.cost_run_le (M : BudgetedCanonizer σ) (n : Nat) (s₀ : σ) :
    (M.run n s₀).2 ≤ M.nbud n * M.w n :=
  cost_budgetedIterate_le M.step M.done (M.w n) (M.hstep n) (M.nbud n) s₀

/-! ## 4. PILOT TARGETS (stubs — gated on the Runtime-Phase descent model)

The two remaining pieces the pilot needs, both requiring `canonForm?` as a `BudgetedCanonizer` instance over
the real descent — the concrete "solidify the doc" targets, kept out of the axiom-clean framework above.

  · **Per-node bound.** Instantiate `w n` from the real per-node primitives (`warmRefine`: `n` rounds over
    `Fin n`; the oracle: poly-size `F_q` arithmetic) — the D7 declared unit-cost list. TARGET: `w n ≤ n^c`.
  · **Node budget met on handled inputs (③-forward, quasipoly).** For a handled affine-polar `VO^ε` residue,
    the descent reaches a `done` (discrete) state within `nbud n = n^{O(log)}` steps — i.e. `run` returns
    `some`, does NOT flag. This is where the seal's base bound `reachesRigidOrCameron_affinePolar`
    (`T.card ≤ O(d log p)`) plus a per-level branching bound (`bᵢ ≤ q²`, recovery-route) feed in. The pilot
    proves the *quasipoly* version; the poly version reuses the same shape once `∏ bᵢ ≤ poly` lands. -/

end ChainDescent.CostModel

/- ═══════════════════════════ (was ScratchCostModelWarmRefine.lean) ═══════════════════════════ -/


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

/- ═══════════════════════════ (was ScratchCostModelPerNode.lean) ═══════════════════════════ -/


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

/- ═══════════════════════════ (was ScratchCostModelCostedWarmRefine.lean) ═══════════════════════════ -/


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

end ChainDescent.CostModel  -- (close the namespace the CostedWarmRefine source auto-closed at its EOF)

/- ═══════════════════════════ (was ScratchCostModelOracle.lean) ═══════════════════════════ -/


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

/- ═══════════════════════════ (was ScratchCostModelSpine.lean) ═══════════════════════════ -/


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
