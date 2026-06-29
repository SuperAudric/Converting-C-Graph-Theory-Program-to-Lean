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

/-! ## The transport seam — representative-choice invariance (depth-1 core)

The Increment-0 residual: that a `CertifiedSinglePath` computes the *iso-invariant* canonical, i.e. consuming a
different *representative* of a single-orbit cell does not change the leaf canonical. This is the analogue of the
landed `spine_branch_independent` (guess-*direction* invariance), but across *representative choice* — and it is the
piece that lets the meta poly-argument read "the cheap single path = the true canonical".

**This section builds its depth-1 core.** An orbit automorphism `g ∈ Stab(S)` carrying one representative `v₁ ↦ v₂`
transports the one-deeper partition: the `v₂`-individualized descent, *pulled back by `g`*, has the *same partition* as
the `v₁`-individualized descent. So the two representative choices yield `g`-relabelings of one another — the same graph.

The mechanism is the cross-config `warmRefine_transport` (an automorphism carries one config's refinement onto
another's) plus the `samePartition` congruence of `warmRefine`. The subtlety the seam turns on: `individualizedColouring`
labels each pinned vertex by its *own index*, so `g` moves the literal labels and the colourings are **not** equal — but
their *partitions* coincide (singletons exactly on the pinned set, one class elsewhere), which is all the canonical
needs. The remaining (downstream) work — iterate across levels and lift the partition-relabeling to `canonAdj` equality
— is partly blocked on `canonForm` (the lex-min wrapper, a §15.7 placeholder); this depth-1 core is the load-bearing
equivariance it will rest on. -/

/-- **`warmRefine` is a `samePartition` congruence in its seed** (the `D = ∅` case of `warmRefine_agree_off'`):
refining two same-partition seed colourings yields same-partition results. The engine that lets the
representative-transport pass through warm refinement. -/
theorem warmRefine_congr_samePartition {adj : AdjMatrix n} {P : PMatrix n} {χ χ' : Colouring n}
    (h : samePartition χ χ') :
    samePartition (warmRefine adj P χ) (warmRefine adj P χ') :=
  warmRefine_agree_off' adj P P χ χ' ∅ h (fun _ _ _ => rfl)
    (fun x hx => absurd hx (by simp))

/-- **Membership transport for the pinned set.** An `S`-fixing automorphism `g` with `g v₁ = v₂` carries
`insert v₁ S` onto `insert v₂ S`: `g i ∈ insert v₂ S ↔ i ∈ insert v₁ S`. -/
theorem mem_insert_transport {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hgfix : ∀ s ∈ S, g s = s) {v₁ v₂ : Fin n} (hgv : g v₁ = v₂) (i : Fin n) :
    g i ∈ insert v₂ S ↔ i ∈ insert v₁ S := by
  rw [Finset.mem_insert, Finset.mem_insert]
  have hv : g i = v₂ ↔ i = v₁ := by rw [← hgv]; exact g.injective.eq_iff
  have hS : g i ∈ S ↔ i ∈ S := by
    constructor
    · intro hgi
      have hfix : g (g i) = g i := hgfix (g i) hgi
      have : g i = i := g.injective hfix
      rwa [this] at hgi
    · intro hi; rwa [hgfix i hi]
  rw [hv, hS]

/-- **Seed transport (`samePartition`).** The `v₁`-individualized seed and the `g`-pullback of the `v₂`-individualized
seed induce the *same partition*: both are "singletons on the pinned set, one class elsewhere", and `g` matches the
pinned sets (`mem_insert_transport`). The literal label values differ (index-based), but the partition does not. -/
theorem indiv_samePartition_transport {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hgfix : ∀ s ∈ S, g s = s) {v₁ v₂ : Fin n} (hgv : g v₁ = v₂) :
    samePartition (individualizedColouring n (insert v₁ S))
      (fun v => individualizedColouring n (insert v₂ S) (g v)) := by
  intro i j
  have hi := mem_insert_transport hgfix hgv i
  have hj := mem_insert_transport hgfix hgv j
  simp only [individualizedColouring]
  by_cases hI : i ∈ insert v₁ S <;> by_cases hJ : j ∈ insert v₁ S
  · rw [if_pos hI, if_pos hJ, if_pos (hi.mpr hI), if_pos (hj.mpr hJ)]
    simp only [add_left_inj, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq]
  · rw [if_pos hI, if_neg hJ, if_pos (hi.mpr hI), if_neg (fun h => hJ (hj.mp h))]
    simp
  · rw [if_neg hI, if_pos hJ, if_neg (fun h => hI (hi.mp h)), if_pos (hj.mpr hJ)]
    simp
  · rw [if_neg hI, if_neg hJ, if_neg (fun h => hI (hi.mp h)), if_neg (fun h => hJ (hj.mp h))]

/-- **★ The representative-transport core (depth 1).** An orbit automorphism `g ∈ Stab(S)` carrying representative
`v₁ ↦ v₂` makes the `v₂`-individualized descent, *pulled back by `g`*, have the *same partition* as the
`v₁`-individualized descent. So choosing a different representative of a single-orbit consumed cell yields a
`g`-relabeling of the same partition — the seam's load-bearing equivariance. Proof: seed transport
(`indiv_samePartition_transport`) → `warmRefine` `samePartition`-congruence → cross-config `warmRefine_transport`
collapses the pullback `warmRefine (χ₂ ∘ g)` to `(warmRefine χ₂) ∘ g`. -/
theorem repTransport {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} {v₁ v₂ : Fin n}
    (hgaut : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgfix : ∀ s ∈ S, g s = s) (hgv : g v₁ = v₂) :
    samePartition (warmRefine adj P (individualizedColouring n (insert v₁ S)))
      (fun v => warmRefine adj P (individualizedColouring n (insert v₂ S)) (g v)) := by
  have hcong := warmRefine_congr_samePartition (adj := adj) (P := P)
    (indiv_samePartition_transport hgfix hgv)
  have hfe : warmRefine adj P (fun w => individualizedColouring n (insert v₂ S) (g w))
      = fun v => warmRefine adj P (individualizedColouring n (insert v₂ S)) (g v) :=
    funext fun v => (warmRefine_transport hgaut hgP (fun _ => rfl) v).symm
  rwa [hfe] at hcong

/-- **The representative-transport from the orbit witness.** Repackages `repTransport` with the automorphism `g`
supplied by `OrbitPartition adj P S v₁ v₂` — exactly what `selectedCell_single_stabOrbit` yields between two
representatives of a single-orbit consumed cell. So: two representatives of a certified cell give descents that are
`g`-relabelings of one another (same partition up to `g`). -/
theorem repTransport_of_orbitPartition {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    {v₁ v₂ : Fin n} (h : OrbitPartition adj P S v₁ v₂) :
    ∃ g : Equiv.Perm (Fin n), IsAut g adj ∧ (∀ s ∈ S, g s = s) ∧ g v₁ = v₂ ∧
      samePartition (warmRefine adj P (individualizedColouring n (insert v₁ S)))
        (fun v => warmRefine adj P (individualizedColouring n (insert v₂ S)) (g v)) := by
  obtain ⟨g, hgaut, hgP, hgfix, hgv⟩ := h
  exact ⟨g, hgaut, hgfix, hgv, repTransport hgaut hgP hgfix hgv⟩

end ChainDescent.NodeCountBridge
