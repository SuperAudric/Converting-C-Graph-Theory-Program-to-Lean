/-
# ScratchConfinementX3Reconcile.lean — X3 step (ii), the confinement reconciliation (WIP, NOT in build.sh)

**Goal.** Discharge `hrec` in `ScratchConfinementX3.ifCanon_iso_invariant_of_reconcile`: for `H = π·G`, the index-free
one-step descent picks on `H` are the `π`-image of `G`'s, up to an `H`-automorphism `b`. That reconciling `b` comes
from confinement (`ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt` ⟹ `SelectedCellIsOrbit`).

**The obstacle this file clears first (ii-a).** Confinement's `SelectedCellIsOrbit` / `OrbitPartition`
(`NodeCountBridge`) are stated over **set-individualization** `warmRefine adj P (individualizedColouring n S)`, but the
one-step descent (`ConfinementX3Spine.oneStepSpineChain`) refines the **one-at-a-time** `oneStepColouring`. To invoke
confinement on the one-step descent's selected cells we need: **same one-step cell ⟹ same set-individualization cell**,
i.e. `Refines (warmRefine (oneStepColouring k)) (warmRefine (individualizedColouring (oneStepD k)))`.

This is the EASY direction (1-WL from the committed set is at least as fine as the one-at-a-time colouring): it follows
from `DescentTrace.singletons` (committed vertices are `oneStepColouring`-singletons) + the existing
`warmRefine_refines_initial` (monotonicity). The hard direction (full `samePartition`) is NOT needed for the
reconciliation — only this one implication, which turns a one-step cell coincidence into a set-individualization one.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Spine
import ChainDescent.Cascade

namespace ChainDescent.ConfinementX3Reconcile

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Spine
open ChainDescent.CanonSound

variable {n : Nat}

/-- **The one-step colouring refines the set-individualization of its committed set.**
`Refines (oneStepColouring k) (individualizedColouring (oneStepD k))`: if two vertices share an `oneStepColouring`
colour, neither is committed (committed vertices are `oneStepColouring`-singletons, `DescentTrace.singletons`), so both
lie outside `oneStepD k` and get `individualizedColouring = 0`. A seed-level refinement fact, discharged from the
trace's singleton invariant — no colour-value bookkeeping. -/
theorem oneStepColouring_refines_indiv (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (k : Nat) :
    Refines (oneStepColouring adj P₀ χι₀ k)
      (individualizedColouring n (oneStepD adj P₀ χι₀ k)) := by
  intro a b hab
  have hsing := DescentTrace.singletons (oneStepTrace adj P₀ χι₀ k)
  by_cases haD : a ∈ oneStepD adj P₀ χι₀ k
  · -- a committed ⟹ singleton ⟹ b = a
    by_cases hba : b = a
    · rw [hba]
    · exact absurd hab.symm (hsing a haD b hba)
  · by_cases hbD : b ∈ oneStepD adj P₀ χι₀ k
    · -- b committed, a not ⟹ a ≠ b ⟹ colours differ, contradicting hab
      exact absurd hab (hsing b hbD a (fun h => haD (h ▸ hbD)))
    · -- both uncommitted ⟹ both get individualizedColouring = 0
      simp only [individualizedColouring, if_neg haD, if_neg hbD]

/-- **★ ii-a — the confinement bridge: same one-step cell ⟹ same set-individualization cell.**
`Refines (warmRefine (oneStepColouring k)) (warmRefine (individualizedColouring (oneStepD k)))`. Monotonicity
(`warmRefine_refines_initial`) applied to the seed refinement above. This is the implication that lets confinement's
`SelectedCellIsOrbit`/`OrbitPartition` (set-individualization-based) speak about the index-free one-step descent's
selected cells: two vertices the one-step descent leaves in one cell are in one set-individualization cell, whence
(confinement) one `Stab`-orbit. -/
theorem oneStep_cell_refines_setIndiv (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (k : Nat) :
    Refines (warmRefine adj P₀ (oneStepColouring adj P₀ χι₀ k))
      (warmRefine adj P₀ (individualizedColouring n (oneStepD adj P₀ χι₀ k))) :=
  warmRefine_refines_initial (oneStepColouring_refines_indiv adj P₀ χι₀ k)

end ChainDescent.ConfinementX3Reconcile
