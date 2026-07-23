import ChainDescent.RigidSeal

/-!
# P3-I — the rigid-solver interface (the seam between the solver contract and `compKey`)

This is the **interface / reduction layer** of the rigid seal's P3 (`docs/chain-descent-rigid-seal.md` §8.2 P3).
It reduces the two obligations the composite force key `compKey` carries — `KeyEquivariant` (its `①` obligation)
and `SolverSeparates` (its firing obligation) — to a **standard solver contract**, so that *building the
concrete solver* (P3-F₂ / P3-ring) is all that remains. This mirrors exactly how `Phase2.Solver` /
`Phase2.Sound` / `Phase2.IsoInvariant` (`Phase2Handoff.lean`) is "the clean typed object" with Algorithm R as
its future witness — here at the *pointed, coloured, per-node* granularity the interleaved descent needs.

## The contract (`PtSolver`)

A **pointed coloured solver** canonizes a pointed coloured graph `(adj, χ, v)` — a canonical form (`some c`) or
an honest flag (`none`). Its two obligations:

* `PtIsoInvariant` — relabelling the input leaves the form unchanged (`Phase2.IsoInvariant`, pointed/coloured).
* `PtSound` — two vertices with the *same* non-flag form are carried onto each other by a **colour-automorphism**
  (`Phase2.Sound` in its separation form: equal forms ⟹ isomorphic-and-pin-matched). This is the iso-reflection
  the concrete solver proves by construction (the ring-canonical form is a complete pointed-coloured invariant);
  it is **not** discharged here — P3-I only *reduces to* it.

## What P3-I delivers (all axiom-clean, no solver internals)

* `skOf sol : Force.Key n` — wire the solver into `compKey`'s non-discretizing slot.
* `keyEquivariant_skOf` : `PtIsoInvariant sol → KeyEquivariant (skOf sol)` — the `①` reduction.
* `solverSeparates_skOf` : `PtSound sol → (no-flag on the cell) → SolverSeparates (compKey (skOf sol)) adj χ`
  — the firing reduction. The **no-flag** hypothesis is the carried *completeness* (claim #2, discharged
  per-family R2); where the solver flags, the pair stays in the residue `¬HandledS` (non-linear rigid).
-/

namespace ChainDescent
namespace RigidSolver

open ChainDescent.Descend
open ChainDescent.Force
open ChainDescent.Consume (IsColAut)
open ChainDescent.RigidSeal

variable {n : Nat}

/-! ## 1. The pointed coloured solver contract -/

/-- A **pointed coloured solver**: a canonical form of the pointed coloured graph `(adj, χ, v)`, or a flag. -/
abbrev PtSolver (n : Nat) : Type := AdjMatrix n → Colouring n → Fin n → Option (List Nat)

/-- **Iso-invariance** (pointed/coloured `Phase2.IsoInvariant`): relabelling the input leaves the form fixed. -/
def PtIsoInvariant (sol : PtSolver n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n),
    sol (relabelAdj σ adj) (transportColouring σ χ) (σ v) = sol adj χ v

/-- **Soundness / separation** (`Phase2.Sound`, iso-reflection form): two pins with the *same* non-flag form
are carried onto each other by a colour-automorphism. The concrete solver proves this from its canonical form
being a complete pointed-coloured invariant; P3-I reduces to it, does not discharge it. -/
def PtSound (sol : PtSolver n) : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n) (c : List Nat),
    sol adj χ u = some c → sol adj χ w = some c →
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w

/-! ## 2. Wiring the solver into a force key -/

/-- Encode the solver's `Option` output as a key value: a flag (`none`) collapses to the constant sentinel `[]`
(so all flagged pairs *tie* — they are the residue, deliberately not separated), and a form `some c` injects to
`0 :: c`. Injective on forms; forms are disjoint from the flag. -/
def encodeOpt : Option (List Nat) → List Nat
  | none => []
  | some c => 0 :: c

/-- A placeholder `②` cost. `keyCost` carries **no** `①` obligation (an expensive key is sound, just slow), so
the interface fixes any poly stand-in; the real bound lands with the concrete solver's complexity. -/
def skCost (n : Nat) : Nat := n * n * n

/-- **`skOf sol`** — the solver as a `Force.Key`, ready for `compKey`'s non-discretizing slot. -/
def skOf (sol : PtSolver n) : Key n := fun adj χ v => (encodeOpt (sol adj χ v), skCost n)

@[simp] theorem keyV_skOf (sol : PtSolver n) (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    keyV (skOf sol) adj χ v = encodeOpt (sol adj χ v) := rfl

/-! ## 3. The `①` reduction — `KeyEquivariant` from `PtIsoInvariant` -/

/-- **★ P3-I(a).** The solver key is equivariant whenever the solver is iso-invariant. Direct: the key value is
just the solver's form, and `PtIsoInvariant` says the form is relabelling-invariant. Feeds
`keyEquivariant_compKey`. -/
theorem keyEquivariant_skOf (sol : PtSolver n) (h : PtIsoInvariant sol) :
    KeyEquivariant (skOf sol) := by
  intro σ adj χ v
  simp only [keyV_skOf]
  rw [h σ adj χ v]

/-! ## 4. The firing reduction — `SolverSeparates` from `PtSound` + no-flag -/

/-- **★★ P3-I(b).** On a cell where the solver **emits on every non-discretizing branch vertex** (`hemit` = the
carried completeness / no-flag), `PtSound` discharges `SolverSeparates` for the composite key: two
non-automorphic non-discretizing branches get distinct forms, so their `compKey` values differ. Where the
solver instead flags, the pair stays in the residue `¬HandledS` — that is the honest non-linear-rigid remainder,
not covered by this theorem's `hemit`. -/
theorem solverSeparates_skOf (sol : PtSolver n) (adj : AdjMatrix n) (χ : Colouring n)
    (hsound : PtSound sol)
    (hemit : ∀ u ∈ branches χ, ¬ Discrete (lookData adj χ u).col → (sol adj χ u).isSome) :
    SolverSeparates (compKey (skOf sol)) adj χ := by
  intro u hu w hw hrig hdu hdw hkey
  -- non-discretizing ⟹ `compKey` value is `0 :: (solver form)`
  rw [keyV_compKey_not_disc (skOf sol) adj χ u hdu,
      keyV_compKey_not_disc (skOf sol) adj χ w hdw, keyV_skOf, keyV_skOf] at hkey
  -- both branches emit a form
  obtain ⟨cu, hcu⟩ := Option.isSome_iff_exists.mp (hemit u hu hdu)
  obtain ⟨cw, hcw⟩ := Option.isSome_iff_exists.mp (hemit w hw hdw)
  rw [hcu, hcw] at hkey
  simp only [encodeOpt] at hkey
  -- equal forms: `cu = cw` (peel the `0 :: 0 ::` tag)
  obtain ⟨_, h2⟩ := List.cons.inj hkey
  obtain ⟨_, hcc⟩ := List.cons.inj h2
  subst hcc
  -- `PtSound` gives the colour-automorphism `u ↦ w`, contradicting non-automorphy
  obtain ⟨σ, hσ, hσuw⟩ := hsound adj χ u w cu hcu hcw
  exact hrig σ hσ hσuw

end RigidSolver
end ChainDescent
