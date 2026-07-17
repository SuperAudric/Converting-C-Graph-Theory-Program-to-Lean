import ChainDescent.Descend

/-!
# `Select` — the resolver-aware NODE resolver (sel + hand-forward, ONE interface; handoff §6.1 design pass)

## What this is

The first increment of the **sel rewrite** (2026-07-17, user-approved, ordering reversed — do BEFORE F2/F3 and
P3c-2nd-half). `descend` hard-wires the branch cell to the **least non-singleton colour** (`branches χ`) and
recomputes each child's refinement inside the recursion. Both defects (§6.1 the resolvability-blind selector,
§6.4 the duplicate-refine loss) are fixed by ONE interface change: generalize the per-node step to a

  **node resolver** `N : AdjMatrix n → Colouring n → CostM (List (Fin n × Colouring n))`

returning the kept children of a cell of ITS choosing, each **with its already-computed refined colouring**.
`[] = flag` (`aggregate [] = none` propagates, exactly the guard's channel) — so for a fused selector, "no
resolvable cell" IS the true mutual stall, and `Stall.guard`'s job is absorbed into the instance.

## ⚠ No exponential is reintroduced (the branching accounting)

The fused selector widens the supply's **harvest** (candidate table), never the descent's **fan-out**:
- sel commits to ONE cell, and only one already narrowed to `≤ 1` branch; otherwise `[]` = flag. Fan-out `≤ 1`
  **by construction** — the single path of `≤ n + 1` nodes is unchanged (each step still individualizes a vertex
  of a non-singleton cell, so `ncol` strictly increases: the `NodeProper` obligation below).
- the probe examines `≤ n` cells per node but descends into one; probe work is **additive per node** — no tree.
- the all-cells harvest is bounded by the SAME `tableBound n d = n·(n+1)^d` already proved in `SupplyCost.lean`
  (its counting only ever used `|branches| ≤ n`; cells partition the vertex set, so `Σ_C |C| ≤ n`).

## The two obligations (pinned here; discharged per instance in later increments)

1. **`NodeProper`** — every emitted child individualizes a vertex with a same-coloured partner (⟹ `ncol`
   strictly increases ⟹ totality/fuel is a pure depth bound) and hands forward **exactly** that child's refined
   colouring (`vc.2 = refineV rf adj (indivOne χ vc.1)`) — the hand-forward is licensed by a proved equation,
   never trusted.
2. **`NodeEquivariant`** (next increment, with the transport pass) — the emitted children transport under σ.
   For the fused instance this is conditional on exactly the hypotheses the guarded object already carries
   (`KeyEquivariant` + supply equivariance / `SameOrbits`): `①b`/`①c` already route through
   `Stall.StallEquivariant` (`Residue.narrowFnEquivariant_guardedRef`), so NO new hypothesis class appears.

## The safety net (this file's capstone)

`descendS (blindNode rf R) = descend rf R` — an **exact `CostM` equation** (value AND cost), where `blindNode`
is today's behaviour (least cell, resolver narrowing, per-child refine). Everything built so far is literally
the blind instance of the new object; migration can proceed theorem-by-theorem against this equation.

⚠ **Runtime note (trap #1):** `blindNode` is a *proof artifact* — it stores `refineV`-closures exactly as
`descend` passes them today, so it is no worse; but a CONCRETE node resolver (the fused selector) must
materialize its colourings through `Refine.ColData` before wrapping them, never through a `… → Colouring n`
definition (the ~10⁴× eta trap).

## Roadmap (next increments)
- transport pass: `NodeEquivariant` + `descendS_transport` (mirror `descend_transport`), then
  `isCanonicalFormOpt` for `descendS` via the node-level contract (the `NarrowFn` shape `①c` already uses).
- the fused instance `selNode key S` over `forceThenConsume` with the **all-cells harvest** supplies;
  `Stall.stalled` becomes the true mutual stall; `Handled`/`CellResolved` become sel-aware (residue deflates).
- widen `Descend.Reaches.step` (any non-singleton-cell vertex) + `HandledBridge.ValidPath` to cover sel-descents.
-/

namespace ChainDescent
namespace Select

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend

variable {n : Nat}

/-! ## 1. The node resolver and the generalized descent -/

/-- **The node resolver.** At a non-discrete node it picks a cell, narrows it, and returns the kept children
`(v, χᵥ)` — the individualized vertex together with its **already-computed** refined colouring. `[]` = flag
(the mutual stall: no cell it can act on). The cost component bills the probe AND the children's refinements
(they are the same work — that is the §6.4 fix). -/
abbrev NodeRes (n : Nat) := AdjMatrix n → Colouring n → CostM (List (Fin n × Colouring n))

/-- **The generalized descent.** Structurally `descend` with the per-node step delegated to the node resolver:
leaf on discrete, else aggregate over the resolver's children. Fuel is per-layer, never threaded (same design
commitment as `descend`). -/
def descendS (N : NodeRes n) (adj : AdjMatrix n) :
    Nat → Colouring n → CostM (Option (Labelled n))
  | 0, χ => if _h : Discrete χ then (some (leafMatrix adj χ), 1) else (none, 1)
  | fuel + 1, χ =>
      if _h : Discrete χ then
        (some (leafMatrix adj χ), 1)
      else
        let rr := N adj χ
        let results := rr.1.map (fun vc => descendS N adj fuel vc.2)
        (aggregate (results.map Prod.fst), 1 + rr.2 + (results.map Prod.snd).sum)

/-- The top-level object: root colouring from the refiner (the root has no parent to hand it forward), then
`descendS`. -/
def canonFormS? (rf : Refiner n) (N : NodeRes n) (adj : AdjMatrix n) : Option (Labelled n) :=
  (descendS N adj n (refineV rf adj (fun _ => 0))).1

/-- The cost projection of the same definition. -/
def descentCostS (rf : Refiner n) (N : NodeRes n) (adj : AdjMatrix n) : Nat :=
  (rf adj (fun _ => 0)).2 + (descendS N adj n (refineV rf adj (fun _ => 0))).2

/-! ### The value equations (mirroring `descend`'s) -/

theorem descendS_val_leaf (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : Discrete χ) : ∀ fuel, (descendS N adj fuel χ).1 = some (leafMatrix adj χ)
  | 0 => by rw [descendS, dif_pos h]
  | _ + 1 => by rw [descendS, dif_pos h]

theorem descendS_val_zero (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) : (descendS N adj 0 χ).1 = none := by
  rw [descendS, dif_neg h]

theorem descendS_val_succ (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) (fuel : Nat) :
    (descendS N adj (fuel + 1) χ).1
      = aggregate ((N adj χ).1.map (fun vc => (descendS N adj fuel vc.2).1)) := by
  rw [descendS, dif_neg h]
  simp [List.map_map, Function.comp_def]

theorem descendS_cost_succ (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) (fuel : Nat) :
    (descendS N adj (fuel + 1) χ).2
      = 1 + (N adj χ).2 + ((N adj χ).1.map (fun vc => (descendS N adj fuel vc.2).2)).sum := by
  rw [descendS, dif_neg h]
  simp [List.map_map, Function.comp_def]

/-- **The flag channel:** a node resolver that returns no children flags the node (and the flag propagates to
the root through `aggregate`) — the `[] = flag` semantics, stated once. -/
theorem descendS_val_stall (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) (hstall : (N adj χ).1 = []) (fuel : Nat) :
    (descendS N adj (fuel + 1) χ).1 = none := by
  rw [descendS_val_succ N adj h fuel, hstall]
  rfl

/-! ## 2. The blind instance — today's object, exactly -/

/-- **The blind node resolver**: least non-singleton cell (`branches`), the resolver's narrowing, one refine per
kept child. This is `descend rf R`'s per-node step, packaged — see `descendS_blind`. -/
def blindNode (rf : Refiner n) (R : Resolver n) : NodeRes n := fun adj χ =>
  let rr := R adj χ (branches χ)
  let B' := rr.1.getD (branches χ)
  (B'.map (fun v => (v, refineV rf adj (indivOne χ v))),
   rr.2 + (B'.map (fun v => (rf adj (indivOne χ v)).2)).sum)

@[simp] theorem blindNode_children (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n)
    (χ : Colouring n) :
    (blindNode rf R adj χ).1
      = (narrow R adj χ).map (fun v => (v, refineV rf adj (indivOne χ v))) := rfl

/-- Sums distribute over a pointwise-added map (local helper for the cost equation). -/
theorem sum_map_add {α : Type*} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- **★ THE SAFETY NET — the blind instance IS today's object, as an exact `CostM` equation** (value AND cost).
Every theorem about `descend rf R` is a theorem about `descendS (blindNode rf R)` and vice versa; the migration
to the resolver-aware selector proceeds against this equation with nothing re-proved twice. -/
theorem descendS_blind (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n),
      descendS (blindNode rf R) adj fuel χ = descend rf R adj fuel χ := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      rw [descendS, descend]
  | succ fuel ih =>
      intro χ
      rw [descendS, descend]
      by_cases h : Discrete χ
      · simp only [dif_pos h]
      · simp only [dif_neg h, blindNode, List.map_map, Function.comp_def]
        refine Prod.ext ?_ ?_
        · simp only [ih, refineV]
        · simp only [ih, refineV, sum_map_add]
          omega

/-- The top-level equality, value side. -/
theorem canonFormS?_blind (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) :
    canonFormS? rf (blindNode rf R) adj = canonForm? rf R adj := by
  unfold canonFormS? canonForm?
  rw [descendS_blind]

/-- The top-level equality, cost side. -/
theorem descentCostS_blind (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) :
    descentCostS rf (blindNode rf R) adj = descentCost rf R adj := by
  unfold descentCostS descentCost
  rw [descendS_blind]

/-! ## 3. The properness obligation (obligation 1 of 2; equivariance comes with the transport pass) -/

/-- **`NodeProper`** — every emitted child (i) individualizes a vertex that genuinely sits in a non-singleton
cell (a same-coloured partner exists ⟹ `ncol` strictly increases ⟹ the depth bound is honest), and (ii) hands
forward **exactly** its refined colouring (the §6.4 hand-forward is licensed by a proved equation, never
trusted). -/
def NodeProper (rf : Refiner n) (N : NodeRes n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n), ∀ vc ∈ (N adj χ).1,
    (∃ u, u ≠ vc.1 ∧ χ u = χ vc.1) ∧ vc.2 = refineV rf adj (indivOne χ vc.1)

/-- The blind instance is proper whenever the resolver's narrowing stays inside the branch cell — the same
`hsub` hypothesis the totality theorems already carry (`NarrowProperAt`'s second half). -/
theorem nodeProper_blindNode {rf : Refiner n} {R : Resolver n}
    (hsub : ∀ (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
      v ∈ narrow R adj χ → v ∈ branches χ) :
    NodeProper rf (blindNode rf R) := by
  intro adj χ vc hvc
  rw [blindNode_children] at hvc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvc
  exact ⟨exists_partner_of_mem_branches (hsub adj χ v hv), rfl⟩

end Select
end ChainDescent
