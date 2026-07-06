/-
# ScratchCostModel.lean — the cost-model framework, foundational brick (WIP; NOT in build.sh)

The concrete beginning of the cost model (`docs/chain-descent-cost-model.md`, to be written from this file).
This brick is the part **decoupled** from the open research (the `∏ bᵢ` branching bound) and from the
not-yet-built `canonForm?`: the **cost monad** and the **budget-cap mechanism** that makes obligation ②
(`Publication.lean : canon_poly_or_flag`) hold *unconditionally* by construction.

**The seven locked decisions (see the doc-to-be):** D1 cost monad (tie cost to the code); D2 decompose
`cost = node_count × per_node`; D3 budget-capped (⟹ ② near-definitional, poly-completeness relocated to
③-forward `residue_if_flag`); D4 the descent becomes a budgeted, node-counted branching process; D5 explicit
`C·nᵏ`; D6 input size = vertex count; D7 an explicit declared unit-cost primitive list.

**What this brick proves.** For the generic budgeted process (`budgetedIterate`): each run's cost is
`≤ fuel · w` (fuel = node budget `Nbud`, `w` = per-node bound) — ALWAYS, no hypothesis. So with the budget
set to `Nbud · w`, `cost ≤ budget` is unconditional; the flag (`none`) carries only the *completeness*
meaning ("did we finish, or give up"), which is ③-forward's job, not ②'s. This is the mechanism the doc
describes; the pilot then instantiates it on the affine-polar residue with `Nbud = quasipoly` (feeding the
seal's base bound `reachesRigidOrCameron_affinePolar`, `T.card ≤ O(d log p)`).

**Not here yet (pilot targets, gated):** the per-node poly lemmas tying `w` to real primitives
(`warmRefine`, the oracle) and `canonForm?` as a `budgetedIterate` instance — both need the Runtime-Phase
descent model. Marked as stubs at the end.

Core-only (no Mathlib import — `import Mathlib` is pathologically slow in this env; the framework needs only
`Nat`/`Option`/`Prod` + `omega`). Quality bar: axiom-clean, no `sorry` in the FRAMEWORK. Compile:
  cd GraphCanonizationProofs && lake env lean ChainDescent/ScratchCostModel.lean
-/

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
