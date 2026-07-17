import ChainDescent.Composite

/-!
# `②` — the cost projection: **polynomial when the resolvers resolve**

(`docs/chain-descent-cost-model.md`; `docs/chain-descent-mixed-composition.md` Stage 4.)

`descentCost` is the **`cost` projection of the same definition** `①a`/`①b`/`①c` ride on (cost-model D1), so `②`
is a theorem about `descend` itself — no second object, no bridge lemma.

## The shape of the bound, and why it is not vacuous

The banked `n⁴` (`CanonForm.descentCost_le`) is against the **single-path** `spineCappedCanonizer` (`nbud = n`,
assume-VT, `leaves = 1`) and does **not** transfer to a branching object: with fan-out `k` at every level the tree
has `kⁿ` nodes and no polynomial bound exists.

So the cost of the branching descent is governed by **exactly one quantity: the fan-out the resolvers leave
behind.** That is why `②` had to wait for the *firing* theorems, and it is where they cash out:

> **`ResolvedAll`** — at every non-discrete node the resolvers narrow the cell to **≤ 1** branch.
> Then the descent is a **single path** of depth ≤ `n`, and `descentCost ≤ (n+1)·(1 + c_refine + c_resolve)`.

The content is *not* in this bound (a single path is obviously cheap). The content is in **what discharges
`ResolvedAll`**, and that is precisely the two firing theorems:

* `Consume.consume_singleton_of_cellIsOrbit` — the cell is one orbit of the verified generators;
* `Force.forceBy_singleton_of_separating` — the key separates the cell.

giving **`poly_of_cells_resolved`**: *a graph every one of whose cells is **either** supply-connected **or**
key-separated is canonized in polynomial time.* That is `②` with real content — an honest, checkable, non-vacuous
characterization of the handled set — and the residue is its complement, exactly as the architecture says.

⚠ **This is a lower bound on the handled set, not a wall.** `ResolvedAll` is the *sufficient* condition proved
here. Bounded (non-stacking) fan-out is also polynomial and is **not** yet captured; that is the next increment
(the verify-consume monovariant), not a barrier. Nothing here says a graph outside `ResolvedAll` is hard.
-/

namespace ChainDescent
namespace Cost

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV KeyEquivariant)
open ChainDescent.Consume (Supply)

variable {n : Nat}

/-! ## 1. The cost equations (the `cost` projection, isolated once) -/

theorem descend_cost_leaf (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : Discrete χ) : ∀ fuel, (descend rf R adj fuel χ).2 = 1
  | 0 => by rw [descend, dif_pos h]
  | _ + 1 => by rw [descend, dif_pos h]

theorem descend_cost_zero (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) : (descend rf R adj 0 χ).2 = 1 := by
  rw [descend, dif_neg h]

/-- The branch case's cost: the node itself, plus the resolver's work, plus — per **surviving** branch — one
refinement and the subtree. Note the sum is over `narrow`, not `branches`: **what the resolvers discard is never
paid for.** -/
theorem descend_cost_succ (rf : Refiner n) (R : Resolver n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) (fuel : Nat) :
    (descend rf R adj (fuel + 1) χ).2
      = 1 + (R adj χ (branches χ)).2
        + ((narrow R adj χ).map (fun v =>
            (rf adj (indivOne χ v)).2
              + (descend rf R adj fuel (refineV rf adj (indivOne χ v))).2)).sum := by
  rw [descend, dif_neg h]
  simp only [narrow, refineV, List.map_map, Function.comp_def]

/-! ## 2. ★ THE BOUND — a resolved descent is a single path -/

/-- **The resolvers leave no fan-out**: every non-discrete node is narrowed to at most one branch.

This is the *whole* hypothesis of the polynomial bound, and it is a statement about **firing**, not soundness. It is
discharged per-cell by either route (§3). -/
def ResolvedAll (R : Resolver n) (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, ¬ Discrete χ → (narrow R adj χ).length ≤ 1

/-- **★★ THE COST BOUND.** With bounded per-node refiner and resolver work (`c₁`, `c₂`) and no residual fan-out,
the descent's cost is **linear in the fuel** — i.e. the descent is a single path of depth ≤ `n`.

⚠ **The resolver-cost hypothesis is stated at the descent's ONLY call site, `B = branches χ` (2026-07-17
weakening).** The previous `∀ B` form was **unsatisfiable** for any resolver whose cost reads `B.length` — which
is *both* built resolvers (`consume` bills per candidate-verification over `B`, `forceBy` bills one key evaluation
per element of `B`), and `B : List (Fin n)` ranges over arbitrary (duplicating, unboundedly long) lists. So no
concrete `c₂` existed and the bound could not be instantiated (standing trap #8: a hypothesis nothing satisfies).
`descend` only ever calls `R adj χ (branches χ)` (`descend_cost_succ`), so this is the honest per-node cost. -/
theorem descend_cost_le_of_resolved {rf : Refiner n} {R : Resolver n} {adj : AdjMatrix n}
    (hres : ResolvedAll R adj) {c₁ c₂ : Nat}
    (hrf : ∀ χ : Colouring n, (rf adj χ).2 ≤ c₁)
    (hR : ∀ χ : Colouring n, (R adj χ (branches χ)).2 ≤ c₂) :
    ∀ (fuel : Nat) (χ : Colouring n),
      (descend rf R adj fuel χ).2 ≤ (fuel + 1) * (1 + c₁ + c₂) := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      have hone : (descend rf R adj 0 χ).2 = 1 := by
        by_cases hd : Discrete χ
        · exact descend_cost_leaf rf R adj hd 0
        · exact descend_cost_zero rf R adj hd
      rw [hone, Nat.one_mul]
      omega
  | succ fuel ih =>
      intro χ
      set K := 1 + c₁ + c₂ with hK
      -- `K ≤ (fuel+2)·K`, and the recursion peels off exactly one `K`.
      -- (Written as `fuel + 1 + 1` to match the goal's atom exactly — omega does not normalize products.)
      have hKle : K ≤ (fuel + 1 + 1) * K := Nat.le_mul_of_pos_left K (by omega)
      have hexp : (fuel + 1 + 1) * K = K + (fuel + 1) * K := by ring
      by_cases hd : Discrete χ
      · rw [descend_cost_leaf rf R adj hd (fuel + 1)]; omega
      · rw [descend_cost_succ rf R adj hd fuel]
        have hRc : (R adj χ (branches χ)).2 ≤ c₂ := hR χ
        -- the narrowed list has ≤ 1 element: no child, or exactly one
        have hcase : narrow R adj χ = [] ∨ ∃ v, narrow R adj χ = [v] := by
          have hlen := hres χ hd
          rcases hnar : narrow R adj χ with _ | ⟨v, t⟩
          · exact Or.inl rfl
          · rw [hnar] at hlen
            simp only [List.length_cons] at hlen
            have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
            exact Or.inr ⟨v, by rw [ht]⟩
        rcases hcase with h0 | ⟨v, h0⟩
        · rw [h0]; simp only [List.map_nil, List.sum_nil]; omega
        · rw [h0]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          have h1 : (rf adj (indivOne χ v)).2 ≤ c₁ := hrf _
          have h2 : (descend rf R adj fuel (refineV rf adj (indivOne χ v))).2
              ≤ (fuel + 1) * K := ih _
          omega

/-- **★★★ `②` FOR THE TOP-LEVEL OBJECT.** A resolved descent costs `O(n · (c₁ + c₂))` — **polynomial**, whenever the
per-node refiner and resolver costs are. -/
theorem descentCost_le_of_resolved {rf : Refiner n} {R : Resolver n} {adj : AdjMatrix n}
    (hres : ResolvedAll R adj) {c₁ c₂ : Nat}
    (hrf : ∀ χ : Colouring n, (rf adj χ).2 ≤ c₁)
    (hR : ∀ χ : Colouring n, (R adj χ (branches χ)).2 ≤ c₂) :
    descentCost rf R adj ≤ c₁ + (n + 1) * (1 + c₁ + c₂) := by
  unfold descentCost
  have h1 : (rf adj (fun _ => 0)).2 ≤ c₁ := hrf _
  have h2 := descend_cost_le_of_resolved hres hrf hR n (refineV rf adj (fun _ => 0))
  omega

/-! ## 3. ★ WHAT DISCHARGES `ResolvedAll` — the firing theorems, cashed out

This is where `②` gets its content. A cell is **resolved** when *either* route can act on it, and the two firing
theorems turn each into a singleton. Note the disjunction is per-cell, not per-graph: a graph may be handled by
consume at one cell and by force at the next — that is exactly what the **mixed** resolver is for. -/

/-- A cell the composite resolves: **either** the supply connects it (consume's domain) **or** the key separates it
(force's domain). -/
def CellResolved (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  Consume.CellIsOrbit S adj χ
  ∨ (∀ u ∈ branches χ, ∀ w ∈ branches χ, keyV key adj χ u = keyV key adj χ w → u = w)

/-- Every resolved cell is narrowed to a single branch. -/
theorem resolvedAll_of_cellResolved {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, ¬ Discrete χ → CellResolved key S adj χ) :
    ResolvedAll (Composite.forceThenConsume key S) adj := by
  intro χ hd
  rcases h χ hd with horb | hsep
  · exact le_of_eq (Composite.forceThenConsume_singleton_of_cellIsOrbit hd horb)
  · exact le_of_eq (Composite.forceThenConsume_singleton_of_separating hd hsep)

/-- **★★★ THE `②` PAYOFF — POLYNOMIAL ON THE RESOLVED SET.**

*A graph every one of whose cells is **either** supply-connected **or** key-separated is canonized in time
polynomial in `n`* (given per-node refiner/resolver costs `c₁`, `c₂`, which are polynomial for the built
instances). Combined with `Composite.composite_canonizer` — sound, iso-invariant, complete, and it always answers —
this is **poly-time canonization on the resolved set**, with no hypothesis on the oracle supply's *correctness* and
none on the key beyond `KeyEquivariant`.

The residue is the complement: cells where the supply does not connect **and** the key does not separate
(`Composite.forceThenConsume_stall`, which *attributes* each such cell to one side's weakness).

⚠ **`ResolvedAll` is a SUFFICIENT condition — a lower bound on the handled set, not a wall.** Bounded,
non-stacking fan-out is also polynomial and is not yet captured here; capturing it is the next increment. -/
theorem poly_of_cells_resolved {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (hcells : ∀ χ : Colouring n, ¬ Discrete χ → CellResolved key S adj χ)
    {c₁ c₂ : Nat}
    (hrf : ∀ χ : Colouring n, (Refine.encodeFreeFast (n := n) adj χ).2 ≤ c₁)
    (hR : ∀ χ : Colouring n, (Composite.forceThenConsume key S adj χ (branches χ)).2 ≤ c₂) :
    descentCost (Refine.encodeFreeFast (n := n)) (Composite.forceThenConsume key S) adj
      ≤ c₁ + (n + 1) * (1 + c₁ + c₂) :=
  descentCost_le_of_resolved (resolvedAll_of_cellResolved hcells) hrf hR

/-- The refiner's per-node cost is exactly `n³` — one of the two summands is discharged outright. -/
theorem refiner_cost (adj : AdjMatrix n) (χ : Colouring n) :
    (Refine.encodeFreeFast (n := n) adj χ).2 = n * n * n := by
  show CostModel.WarmRefine.warmRefineCost n = n * n * n
  exact CostModel.WarmRefine.warmRefineCost_eq n

end Cost
end ChainDescent
