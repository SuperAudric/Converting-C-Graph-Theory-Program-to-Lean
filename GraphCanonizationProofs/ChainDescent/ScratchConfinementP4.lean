/-
# ScratchConfinementP4.lean — P4 of the confinement lemma: the structural (non-WL) route to
# `SelectedCellIsOrbit` (WIP, NOT in build.sh)

**Context (docs/chain-descent-route-c-plan.md §7c, sub-obligation P4).** The assume-VT poly mechanism (§7b)
prunes a Phase-1 over-budget flag by ASSUMING vertex-transitivity: the residue is primitive rank-3
(node-4/Cameron, from the seal `reachesRigidOrCameron` + largeness P1) ⟹ VT ⟹ the *selected* cell is a single
`Stab(S)`-orbit ⟹ pruning it to one root is sound and loses no canonical (prune completeness).

**What the descent scheduler needs is already named:** `NodeCountBridge.SelectedCellIsOrbit` — "same-colour
vertices *of the selected cell* are `Stab(S)`-orbit-equivalent", strictly weaker than full `CellsAreOrbits` — and
its consumer (`selectedCell_single_stabOrbit`, prune completeness ⟹ single sibling-class ⟹ no branching) is
LANDED. The ONLY existing producer, `selectedCellIsOrbit_of_cellsAreOrbits`, routes through full `CellsAreOrbits`
— i.e. through the multi-base `JointProfileRecoversAt` **wall** (WL must reach the orbits at a bounded base, the
open node-4 content).

**This module opens the SECOND producer — the structural one that sidesteps the wall.** The assume-VT route does
not ask WL to *reach* the orbits; it asks that the selected cell *sits inside one `Stab(S)`-orbit* — a statement
about the residue's automorphism GROUP (for primitive rank-3: the point-stabilizer is transitive on each of its
three classes `{p}, Γ(p), Γ̄(p)`, recursing down the point-stabilizer chain `VO_d → VO_{d−2} → …`), NOT about
1-WL refinement. That is `SelectedCellSubsetOrbit` below; it implies `SelectedCellIsOrbit` by simply dropping the
colour-equality hypothesis (same-orbit is then automatic — both vertices lie in the one orbit).

**Split of the remaining work.**
  · `selectedCellIsOrbit_of_subsetOrbit` (HERE) — the trivial bridge SubsetOrbit ⟹ SelectedCellIsOrbit, wiring
    the structural target to the landed prune-completeness consumer. Done.
  · `SelectedCellSubsetOrbit` for the primitive rank-3 residue (NEXT increment) — the genuine P4 content: the
    selected cell is contained in one `Stab(S)`-orbit, from the rank-3 group structure. Single-base is already
    free (`cellsAreOrbits_schemeAdj_singleton` / `jointProfileRecoversAt_singleton`); the crux is the recursion,
    and proving it does NOT silently collapse back onto the multi-base `JointProfileRecoversAt` wall.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchNodeCountBridge

namespace ChainDescent.ConfinementP4

open ChainDescent
open ChainDescent.NodeCountBridge

variable {n : Nat}

/-- **The structural (assume-VT) target: the selected cell is contained in a single `Stab(S)`-orbit.** Unlike
`SelectedCellIsOrbit`, there is NO colour-equality hypothesis — *every* pair in the selected cell is
`Stab(S)`-orbit-equivalent, i.e. the cell sits inside one orbit. This is the property VT / primitive rank-3
delivers from the GROUP (the selector picks a stabilizer-orbit: `{p}`, `Γ(p)` or `Γ̄(p)` for rank-3), with no
appeal to 1-WL reaching the orbit partition — the route that sidesteps the multi-base `JointProfileRecoversAt`
wall. It is logically stronger than `SelectedCellIsOrbit` but proved by a DIFFERENT (structural) method. -/
def SelectedCellSubsetOrbit (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ v w,
    v ∈ sel (warmRefine adj P (individualizedColouring n S)) →
    w ∈ sel (warmRefine adj P (individualizedColouring n S)) →
    OrbitPartition adj P S v w

/-- **The second producer of `SelectedCellIsOrbit` — structural, wall-free.** If the selected cell sits inside a
single `Stab(S)`-orbit, then in particular any two *same-colour* cell vertices are orbit-equivalent — dropping the
colour hypothesis. This wires the assume-VT structural target into the LANDED prune-completeness consumer
(`selectedCell_single_stabOrbit`), the sibling of `selectedCellIsOrbit_of_cellsAreOrbits` that avoids the
`CellsAreOrbits` / multi-base-WL wall. -/
theorem selectedCellIsOrbit_of_subsetOrbit
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (h : SelectedCellSubsetOrbit adj P sel S) :
    SelectedCellIsOrbit adj P sel S :=
  fun v w hv hw _hcolour => h v w hv hw

end ChainDescent.ConfinementP4
