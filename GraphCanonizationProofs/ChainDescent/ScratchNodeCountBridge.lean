/-
# The node-count bridge (Route B, Increment 0) — single-path disposition ⟹ the poly ingredients

**What this module builds.** The CellsAreOrbits route's payoff mechanism. The route proves `poly ⟸ B` along
three steps (doc §1): (1) `twinsRealizedByResidualAut_iff_cellsAreOrbits` [LANDED]; (2) assemble it across descent
nodes into a single-path tree; (3) single path ⟹ poly node count. The reviewer correctly flagged steps 2+3 as the
route's *missing pillar*. Grounding against the spine substrate showed most of it is already landed:

* **node count `≤ n`** — `defaultSpineChain_reaches_leaf` (`ChainDescent.lean`): the descent reaches a discrete
  leaf in `≤ n` levels. (NOT `exists_potential_descent` — that bounds the base *size* to `O(log n)` and is the
  *quasipoly-base* engine; reusing it here would re-derive quasipoly.)
* **prune soundness** — `covered_sound` / `orbit_pathFixing_sound` (`Cascade.lean`): dropping an orbit-equivalent
  sibling subtree is sound.
* **per-node firing** — `colourMatch_exists_of_cellsAreOrbits` (`CascadeOracle.lean`).

The genuinely missing piece was **prune *completeness*** — that the *consumed* cell is a *single* orbit, so there is
exactly one sibling-class and the cheap single path loses no canonical. This module supplies it.

**Keyed on the weaker predicate.** The canonizer's scheduler only individualizes within `sel`'s targeted cell, so
poly needs only that the *selected* cell is one orbit — `SelectedCellIsOrbit`, strictly weaker than full
`CellsAreOrbits` (all cells). The §4 forms-graph math (`CellsAreOrbits` modulo Witt + the wall) discharges it for free
(`selectedCellIsOrbit_of_cellsAreOrbits`).

**Capstone.** `certifiedSinglePath_of_disposition` — the single-path disposition delivers *both* poly ingredients:
bounded node count (`≤ n`) and every consumed cell certified as a single residual orbit. The remaining seam (NOT here,
Increment-0 residual): the *transport* "a `CertifiedSinglePath` computes the iso-invariant lex-min canonical" =
representative-choice invariance of the leaf canonical over certified single-orbit cells — the `canonAdj`-level
plumbing the *meta* poly-argument consumes. Isolated in prose, next increment.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.Cascade

namespace ChainDescent.NodeCountBridge

open ChainDescent

variable {n : Nat}

/-! ## 0a — the weaker, scheduler-matching predicate -/

/-- **The consumed cell is a single orbit.** `CellsAreOrbits` restricted to `sel`'s targeted cell: any two
same-coloured vertices *of the selected cell* are `Stab(S)`-orbit-equivalent. Strictly weaker than full
`CellsAreOrbits` (which quantifies over *all* cells); it is exactly what the descent's scheduler needs, since the
descent only ever individualizes within the selected cell. -/
def SelectedCellIsOrbit (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ v w,
    v ∈ sel (warmRefine adj P (individualizedColouring n S)) →
    w ∈ sel (warmRefine adj P (individualizedColouring n S)) →
    warmRefine adj P (individualizedColouring n S) v
      = warmRefine adj P (individualizedColouring n S) w →
    OrbitPartition adj P S v w

/-! ## 0b — the §4 math discharges it for free -/

/-- **Full `CellsAreOrbits` ⟹ the weak disposition.** The forms-graph induction (Increments 2/3, modulo Witt + the
wall) targets full `CellsAreOrbits`; it feeds the bridge by simply dropping the cell-membership hypotheses. So the
bridge is keyed on the weaker predicate while the math still discharges it. -/
theorem selectedCellIsOrbit_of_cellsAreOrbits {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (h : CellsAreOrbits adj P S) : SelectedCellIsOrbit adj P sel S :=
  fun v w _ _ hcell => h v w hcell

/-! ## 0c — completeness: the consumed cell is a single residual orbit -/

/-- **Prune completeness (the missing pillar).** Under `SelectedCellIsOrbit`, any two same-coloured vertices of the
consumed cell lie in a single `StabilizerAt`-orbit. This is the direction prune *soundness* (`covered_sound`) does
not give: soundness says a dropped sibling *was* isomorphic; completeness says the consumed cell is *one* orbit, so
there is exactly one sibling-class and consuming a single representative branches *not at all*. The bridge between
`OrbitPartition` and the residual group action is the landed `mem_orbit_stabilizerAt_iff`. -/
theorem selectedCell_single_stabOrbit {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (h : SelectedCellIsOrbit adj P sel S) {v w : Fin n}
    (hv : v ∈ sel (warmRefine adj P (individualizedColouring n S)))
    (hw : w ∈ sel (warmRefine adj P (individualizedColouring n S)))
    (hcell : warmRefine adj P (individualizedColouring n S) v
      = warmRefine adj P (individualizedColouring n S) w) :
    w ∈ MulAction.orbit (StabilizerAt adj P S) v := by
  rw [mem_orbit_stabilizerAt_iff]
  exact h v w hv hw hcell

/-- **Prune sound *and* complete.** The two same-cell representatives are *mutually* orbit-equivalent: dropping
either in favour of the other is sound (they are isomorphic) and complete (no un-isomorphic class is lost). This is
the precise content that turns "fork over representatives" into "descend on one". -/
theorem selectedCell_prune_sound_complete {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (h : SelectedCellIsOrbit adj P sel S) {v w : Fin n}
    (hv : v ∈ sel (warmRefine adj P (individualizedColouring n S)))
    (hw : w ∈ sel (warmRefine adj P (individualizedColouring n S)))
    (hcell : warmRefine adj P (individualizedColouring n S) v
      = warmRefine adj P (individualizedColouring n S) w) :
    OrbitPartition adj P S v w ∧ OrbitPartition adj P S w v :=
  ⟨h v w hv hw hcell, (h v w hv hw hcell).symm⟩

/-! ## The node-count half (re-export of the landed `≤ n` termination) -/

/-- **Node count `≤ n` (landed).** Under the standard selector hypotheses, the default spine reaches a discrete
leaf within `n` levels. This is step (3)'s entire content — single-path node count is bounded *for free*; no
monovariant/potential argument is needed (that bounds the base *size*, a different quantity, and yields quasipoly).
Re-exported here as the bridge's second ingredient. -/
theorem spine_node_count_le {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel) :
    ∃ k ≤ n, (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf :=
  defaultSpineChain_reaches_leaf adj P₀ χι₀ hcell hne

/-! ## The disposition + the capstone -/

/-- **The single-path disposition.** Every base's consumed cell is a single orbit — the bridge-keyed hypothesis
(weaker than `∀ S, CellsAreOrbits`). This is the structural form of the empirical `Phase2Nodes = 0` / single-path
finding. -/
def SinglePathDisposition (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), SelectedCellIsOrbit adj P sel S

/-- The forms-graph math (full `CellsAreOrbits` at every base, modulo Witt + the wall) discharges the disposition. -/
theorem singlePathDisposition_of_cellsAreOrbits {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} (h : ∀ S, CellsAreOrbits adj P S) :
    SinglePathDisposition adj P sel :=
  fun S => selectedCellIsOrbit_of_cellsAreOrbits (h S)

/-- **The certified single path** — the two poly ingredients, bundled and discharged. `boundedNodes`: the descent
is `≤ n` levels (single path has bounded node count). `cellsCertified`: at every base, the consumed cell is a single
residual orbit (no real branching). Both are *proved* from the disposition (`certifiedSinglePath_of_disposition`).
The *meta* poly-argument reads "poly time" off this structural object: `≤ n` nodes × per-node poly work, with the
single-orbit certification justifying single-representative descent. -/
structure CertifiedSinglePath (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Prop where
  boundedNodes : ∃ k ≤ n, (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf
  cellsCertified : ∀ S : Finset (Fin n), ∀ v w,
    v ∈ sel (warmRefine adj P₀ (individualizedColouring n S)) →
    w ∈ sel (warmRefine adj P₀ (individualizedColouring n S)) →
    warmRefine adj P₀ (individualizedColouring n S) v
      = warmRefine adj P₀ (individualizedColouring n S) w →
    w ∈ MulAction.orbit (StabilizerAt adj P₀ S) v

/-- **★ The bridge capstone (Increment 0).** The single-path disposition delivers *both* poly ingredients at once:
bounded node count (landed termination) and every consumed cell certified as a single residual orbit (the
completeness core). This is the structural reduction the doc's §1 "step 2 + step 3" asked for — discharged, modulo
the documented `canonAdj`-transport seam (representative-choice invariance of the leaf canonical), which the meta
poly-argument consumes and which is the Increment-0 residual. -/
theorem certifiedSinglePath_of_disposition {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hdisp : SinglePathDisposition adj P₀ sel) :
    CertifiedSinglePath adj P₀ χι₀ sel where
  boundedNodes := defaultSpineChain_reaches_leaf adj P₀ χι₀ hcell hne
  cellsCertified := fun S _ _ hv hw hcelleq =>
    selectedCell_single_stabOrbit (hdisp S) hv hw hcelleq

end ChainDescent.NodeCountBridge
