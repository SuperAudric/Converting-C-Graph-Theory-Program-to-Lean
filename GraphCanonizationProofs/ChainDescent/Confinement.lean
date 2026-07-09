/-
# ChainDescent.Confinement — the confinement lemma (Algorithm A / assume-VT), core (ported)

The non-rigid correctness core: a Phase-1 over-budget flag ⟹ (P1 large ∧ P2 ¬rigid ∧ P3 primitive-rank-3
∧ P4/Witt) ⟹ the selected cell is one `Stab`-orbit (`SelectedCellIsOrbit`), so assume-VT pruning is sound.
Bundles, in dependency order:

  · `NodeCountBridge`      — the representative-transport / base-transport seam (`baseTransport`, `repTransport`)
  · `ConfinementP1`        — largeness confinement (flag ⟹ super-poly residual `Aut`); `spineResidualCard`
  · `ConfinementP4`        — prune-soundness core, reduced to `FrameSelectorTransitive` (Witt)
  · `Confinement`          — the assembly (P1 ∧ P2 wired; `flag_imp_symmetric_spine`; `confinement_selectedCellIsOrbit_spine`)
  · `ConfinementP3`        — seal recomposition (`ResidueSchemeModel`, real `exhaustiveObstruction_scheme`)
  · `ConfinementWitt`      — Witt factored; capstone `confinement_selectedCellIsOrbit_spine_witt` (①b core,
                             carrying ONLY named citations {G3, model M, hprim, Witt+Liebeck})
  · `ConfinementSchurianModel` — the on-`Fin n` scheme-extraction constructor `residueModel_of_orbitalGroup`

Axiom-clean `[propext, Classical.choice, Quot.sound]`. Ported 2026-07-09 from ScratchNodeCountBridge,
ScratchConfinementP1, ScratchConfinementP4, ScratchConfinement, ScratchConfinementP3, ScratchConfinementWitt,
ScratchConfinementSchurianModel. (The index-free `descentCanon` ①b showcase + the faithful cell model +
the RRU handoff sit ON TOP of this core and are ported separately once the RRU object is fixed.)
-/
import ChainDescent.Cascade
import ChainDescent.CostModel


/- ═══════════════════════════ (was ScratchNodeCountBridge.lean) ═══════════════════════════ -/


namespace ChainDescent.NodeCountBridge

open ChainDescent

variable {n : Nat}

/-! ## 0a — the weaker, scheduler-matching predicate -/

/-- **The consumed cell is a single orbit.** `CellsAreOrbits` restricted to `sel`'s targeted cell: any two
same-coloured vertices *of the selected cell* are `Stab(S)`-orbit-equivalent. Strictly weaker than full
`CellsAreOrbits` (which quantifies over *all* cells); it is exactly what the descent's scheduler needs, since the
descent only ever individualizes within the selected cell. -/
def SelectedCellIsOrbit (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (χ : Colouring n) (S : Finset (Fin n)) : Prop :=
  ∀ v w,
    v ∈ sel χ →
    w ∈ sel χ →
    χ v = χ w →
    OrbitPartition adj P S v w

/-- **The default selection colouring** — `warmRefine adj P (individualizedColouring n S)` at each base `S`. Passing
this recovers the original `individualizedColouring`-based predicates; the runtime descent instead passes its own
(index-free `oneStepColouring`-based) selection colouring, which is what makes the *equivariant* cross-graph selector
land in the same cell the descent runs on. The confinement chain is generic in the colouring — it only reads
membership and same-colour, concluding the colouring-free `OrbitPartition`. -/
def indivχ (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) : Colouring n :=
  warmRefine adj P (individualizedColouring n S)

/-! ## 0b — the §4 math discharges it for free -/

/-- **Full `CellsAreOrbits` ⟹ the weak disposition.** The forms-graph induction (Increments 2/3, modulo Witt + the
wall) targets full `CellsAreOrbits`; it feeds the bridge by simply dropping the cell-membership hypotheses. So the
bridge is keyed on the weaker predicate while the math still discharges it. -/
theorem selectedCellIsOrbit_of_cellsAreOrbits {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (h : CellsAreOrbits adj P S) : SelectedCellIsOrbit adj P sel (indivχ adj P S) S :=
  fun v w _ _ hcell => h v w hcell

/-! ## 0c — completeness: the consumed cell is a single residual orbit -/

/-- **Prune completeness (the missing pillar).** Under `SelectedCellIsOrbit`, any two same-coloured vertices of the
consumed cell lie in a single `StabilizerAt`-orbit. This is the direction prune *soundness* (`covered_sound`) does
not give: soundness says a dropped sibling *was* isomorphic; completeness says the consumed cell is *one* orbit, so
there is exactly one sibling-class and consuming a single representative branches *not at all*. The bridge between
`OrbitPartition` and the residual group action is the landed `mem_orbit_stabilizerAt_iff`. -/
theorem selectedCell_single_stabOrbit {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χ : Colouring n} {S : Finset (Fin n)}
    (h : SelectedCellIsOrbit adj P sel χ S) {v w : Fin n}
    (hv : v ∈ sel χ) (hw : w ∈ sel χ) (hcell : χ v = χ w) :
    w ∈ MulAction.orbit (StabilizerAt adj P S) v := by
  rw [mem_orbit_stabilizerAt_iff]
  exact h v w hv hw hcell

/-- **Prune sound *and* complete.** The two same-cell representatives are *mutually* orbit-equivalent: dropping
either in favour of the other is sound (they are isomorphic) and complete (no un-isomorphic class is lost). This is
the precise content that turns "fork over representatives" into "descend on one". -/
theorem selectedCell_prune_sound_complete {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χ : Colouring n} {S : Finset (Fin n)}
    (h : SelectedCellIsOrbit adj P sel χ S) {v w : Fin n}
    (hv : v ∈ sel χ) (hw : w ∈ sel χ) (hcell : χ v = χ w) :
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
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n) : Prop :=
  ∀ S : Finset (Fin n), SelectedCellIsOrbit adj P sel (χsel S) S

/-- The forms-graph math (full `CellsAreOrbits` at every base, modulo Witt + the wall) discharges the disposition. -/
theorem singlePathDisposition_of_cellsAreOrbits {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} (h : ∀ S, CellsAreOrbits adj P S) :
    SinglePathDisposition adj P sel (indivχ adj P) :=
  fun S => selectedCellIsOrbit_of_cellsAreOrbits (h S)

/-- **The certified single path** — the two poly ingredients, bundled and discharged. `boundedNodes`: the descent
is `≤ n` levels (single path has bounded node count). `cellsCertified`: at every base, the consumed cell is a single
residual orbit (no real branching). Both are *proved* from the disposition (`certifiedSinglePath_of_disposition`).
The *meta* poly-argument reads "poly time" off this structural object: `≤ n` nodes × per-node poly work, with the
single-orbit certification justifying single-representative descent. -/
structure CertifiedSinglePath (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n) : Prop where
  boundedNodes : ∃ k ≤ n, (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf
  cellsCertified : ∀ S : Finset (Fin n), ∀ v w,
    v ∈ sel (χsel S) →
    w ∈ sel (χsel S) →
    χsel S v = χsel S w →
    w ∈ MulAction.orbit (StabilizerAt adj P₀ S) v

/-- **★ The bridge capstone (Increment 0).** The single-path disposition delivers *both* poly ingredients at once:
bounded node count (landed termination) and every consumed cell certified as a single residual orbit (the
completeness core). This is the structural reduction the doc's §1 "step 2 + step 3" asked for — discharged, modulo
the documented `canonAdj`-transport seam (representative-choice invariance of the leaf canonical), which the meta
poly-argument consumes and which is the Increment-0 residual. -/
theorem certifiedSinglePath_of_disposition {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hdisp : SinglePathDisposition adj P₀ sel χsel) :
    CertifiedSinglePath adj P₀ χι₀ sel χsel where
  boundedNodes := defaultSpineChain_reaches_leaf adj P₀ χι₀ hcell hne
  cellsCertified := fun S _ _ hv hw hcelleq =>
    selectedCell_single_stabOrbit (hdisp S) hv hw hcelleq

/-- **Recovery route — angle (b), the explicit composition.** Full `CellsAreOrbits` at every base discharges the
single-path disposition (`singlePathDisposition_of_cellsAreOrbits`), hence the certified single path. This is the path
the recovery route takes when going *through* the (stronger) forms-graph `CellsAreOrbits` scaffold
(`ScratchWallKernel` → `CellsAreOrbits` → here) rather than proving `SelectedCellIsOrbit` directly on the sphere.
Named for the recovery-route wiring (`chain-descent-recovery-route.md` §6 step 1). -/
theorem certifiedSinglePath_of_cellsAreOrbits {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (h : ∀ S, CellsAreOrbits adj P₀ S) :
    CertifiedSinglePath adj P₀ χι₀ sel (indivχ adj P₀) :=
  certifiedSinglePath_of_disposition hcell hne (singlePathDisposition_of_cellsAreOrbits h)

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

/-! ### Iterating across levels — the full-base `g`-equivariance

`repTransport` is depth-1 (one consumed cell). The descent continues, individualizing more vertices until the leaf.
Because the orbit automorphism `g` is **global** (an automorphism of the whole graph, fixing the committed prefix),
the iteration does **not** need an induction: `g` carries the *entire* descent subtree at once. The clean statement is
the depth-1 lemma with the pinned set generalised from `insert v₁ S` to an **arbitrary base `T`** and its image `g(T)`:
for any automorphism `g`, the descent at `g(T)` is the `g`-relabeling of the descent at `T`. Taking `T` to be a leaf
base gives the full-leaf transport — the "iterate across levels" piece, in one lemma. -/

/-- **Membership transport, general base.** `g i ∈ T.image g ↔ i ∈ T` (just injectivity of `g`). -/
theorem mem_image_transport {T : Finset (Fin n)} {g : Equiv.Perm (Fin n)} (i : Fin n) :
    g i ∈ T.image g ↔ i ∈ T := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hga⟩; rwa [g.injective hga] at ha
  · intro hi; exact ⟨i, hi, rfl⟩

/-- **Seed transport, general base.** The `T`-individualized seed and the `g`-pullback of the `g(T)`-individualized
seed induce the same partition. The general form of `indiv_samePartition_transport`. -/
theorem indiv_samePartition_image {T : Finset (Fin n)} {g : Equiv.Perm (Fin n)} :
    samePartition (individualizedColouring n T)
      (fun v => individualizedColouring n (T.image g) (g v)) := by
  intro i j
  have hi := mem_image_transport (T := T) (g := g) i
  have hj := mem_image_transport (T := T) (g := g) j
  simp only [individualizedColouring]
  by_cases hI : i ∈ T <;> by_cases hJ : j ∈ T
  · rw [if_pos hI, if_pos hJ, if_pos (hi.mpr hI), if_pos (hj.mpr hJ)]
    simp only [add_left_inj, Fin.val_inj, EmbeddingLike.apply_eq_iff_eq]
  · rw [if_pos hI, if_neg hJ, if_pos (hi.mpr hI), if_neg (fun h => hJ (hj.mp h))]; simp
  · rw [if_neg hI, if_pos hJ, if_neg (fun h => hI (hi.mp h)), if_pos (hj.mpr hJ)]; simp
  · rw [if_neg hI, if_neg hJ, if_neg (fun h => hI (hi.mp h)), if_neg (fun h => hJ (hj.mp h))]

/-- **★ Full-base `g`-equivariance (the "iterate across levels" lemma).** For any automorphism `g` (preserving `P`)
and any base `T`, the descent at `g(T)`, pulled back by `g`, has the *same partition* as the descent at `T`. Because
`g` is global, this holds at **every** base — in particular at a leaf base — so it subsumes the level-by-level
iteration of `repTransport` in a single statement: the whole single-orbit-rep-swap descent is a `g`-relabeling. -/
theorem baseTransport {adj : AdjMatrix n} {P : PMatrix n} {T : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} (hgaut : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u) :
    samePartition (warmRefine adj P (individualizedColouring n T))
      (fun v => warmRefine adj P (individualizedColouring n (T.image g)) (g v)) := by
  have hcong := warmRefine_congr_samePartition (adj := adj) (P := P)
    (indiv_samePartition_image (T := T) (g := g))
  have hfe : warmRefine adj P (fun w => individualizedColouring n (T.image g) (g w))
      = fun v => warmRefine adj P (individualizedColouring n (T.image g)) (g v) :=
    funext fun v => (warmRefine_transport hgaut hgP (fun _ => rfl) v).symm
  rwa [hfe] at hcong

/-- **`repTransport` is the `S`-fixing instance of `baseTransport`.** When `g` fixes `S` pointwise and `g v₁ = v₂`,
the image `(insert v₁ S).image g` is exactly `insert v₂ S`, so `baseTransport` at `T = insert v₁ S` recovers
`repTransport`. (Confirms the depth-1 lemma is the orbit-cell specialisation of the general equivariance.) -/
theorem repTransport_eq_baseTransport_instance {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hgfix : ∀ s ∈ S, g s = s) {v₁ v₂ : Fin n} (hgv : g v₁ = v₂) :
    (insert v₁ S).image g = insert v₂ S := by
  have hSimg : S.image g = S := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; rwa [hgfix a ha]
    · intro hx; exact ⟨x, hx, hgfix x hx⟩
  rw [Finset.image_insert, hgv, hSimg]

/-! ### Lifting the partition-relabeling to the labelled canonical

The descent's leaf partitions under two single-orbit representatives are `g`-relabelings of one another
(`baseTransport`). The canonical *output* is `labelledAdj (rankPerm π) adj`. The atom below shows that output is
**invariant** under a `g`-relabeling of the discrete leaf colouring, for `g` an automorphism: relabeling the colouring
by `g` conjugate-shifts the rank permutation (`rankPerm_comp`), and an automorphism is invisible at the labelled level
(`labelledAdj_eq_of_isAut`). So once the leaf colourings are related by a *literal* `g`-relabel, the labelled
canonical agrees.

**The remaining gap (precisely).** `baseTransport` delivers `samePartition`, **not** a literal `π₂ = π₁ ∘ g`, because
`individualizedColouring` labels each pinned vertex by its own *index* — so `g` moves the literal colour values while
preserving the partition. `rankPerm`/`labelledAdj` read colour *values* (via `vertexRank`), so the atom needs the
literal relabel, which the index-based seed does not provide. Bridging `samePartition` → equal labelled canonical is
exactly the job of `canonForm` (the lex-min over `DirAssignment`s, designed to depend only on the partition + graph) —
a §15.7 *placeholder*. So the lift is complete *modulo* `canonForm`; this atom is the relabel-invariance it will use. -/

/-- **Labelled-output invariance under an automorphism relabel.** If `g` is an automorphism of `adj` and `π` is a
discrete colouring, the labelled adjacency from the `g`-relabeled colouring `π ∘ g` equals that from `π`. Via
`rankPerm_comp` (`rankPerm (π ∘ g) = rankPerm π · g`) + `labelledAdj_eq_of_isAut` (automorphisms are invisible at the
labelled level). The canonical-output half of the transport lift; pairs with `baseTransport` once the seed is made
literal-relabel (the `canonForm` step). -/
theorem labelledAdj_rankPerm_transport {adj : AdjMatrix n} {π : Colouring n}
    {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (h₁ : Discrete π) (h₂ : Discrete (fun v => π (g v))) :
    labelledAdj (Colouring.rankPerm (fun v => π (g v)) h₂) adj
      = labelledAdj (Colouring.rankPerm π h₁) adj := by
  rw [rankPerm_comp π g h₁ h₂]
  funext i j
  simp only [labelledAdj]
  have hsymm : ∀ x : Fin n, (Colouring.rankPerm π h₁ * g).symm x
      = g.symm ((Colouring.rankPerm π h₁).symm x) := fun x =>
    (Equiv.symm_apply_eq _).mpr (by simp [Equiv.Perm.mul_apply])
  rw [hsymm i, hsymm j]
  have hg' := congrFun (congrFun (labelledAdj_eq_of_isAut hg)
    ((Colouring.rankPerm π h₁).symm i)) ((Colouring.rankPerm π h₁).symm j)
  simpa only [labelledAdj] using hg'

end ChainDescent.NodeCountBridge

/- ═══════════════════════════ (was ScratchConfinementP1.lean) ═══════════════════════════ -/


namespace ChainDescent.ConfinementP1

open ChainDescent
open ChainDescent.CostModel.Oracle
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance

variable {n : Nat}

/-- **`log₂ ≤ baseMax`.** The oracle threshold is `baseMax m = (Nat.log2 m)² = (Nat.log 2 m)²` (superlogarithmic,
the 2026-07-08 threshold decision), and `log₂ m ≤ (log₂ m)²` always (`Nat.le_self_pow`, `2 ≠ 0`). So a greedy base
of length `≤ log₂|Aut| ≤ log₂ n` still fits under `baseMax n` — the P1 graph-side survives the threshold raise
(it now needs only `≤`, not `=`). -/
theorem log_two_le_baseMax (m : Nat) : Nat.log 2 m ≤ baseMax m := by
  unfold baseMax
  rw [Nat.log2_eq_log_two]
  exact Nat.le_self_pow (by norm_num) _

/-- **The graph side of P1 (pure content): a small-`Aut` node's greedy harvest base is `≤ baseMax n`.**
`exists_greedy_base_le_log` gives a base of length `≤ log₂|Aut^P ∅|`; if the residual order is small (`≤ n`), `log₂`
monotonicity + the `baseMax` bridge put that length `≤ baseMax n`. So a small-`Aut` node's harvest base fits the oracle
budget — the combinatorial half of confinement-P1. -/
theorem greedy_base_card_le_baseMax {adj : AdjMatrix n} {P : PMatrix n}
    (hsmall : Nat.card (StabilizerAt adj P ∅) ≤ n) :
    ∃ bs : List (Fin n),
      IsBase adj P (bs.foldl (fun s b => insert b s) ∅) ∧ bs.length ≤ baseMax n := by
  obtain ⟨bs, hbase, hlen⟩ := exists_greedy_base_le_log (adj := adj) (P := P)
  refine ⟨bs, hbase, ?_⟩
  calc bs.length ≤ Nat.log 2 (Nat.card (StabilizerAt adj P ∅)) := hlen
    _ ≤ Nat.log 2 n := Nat.log_mono_right hsmall
    _ ≤ baseMax n := log_two_le_baseMax n

/-- **P1 assembled on the real spine: a small-residual node does NOT flag.** Given (i) the harvest base at node `k`
is at most a greedy base of the node's residual (`baseAt k ≤ log₂(residualCard k)` — the harvest-algorithm property,
justified by `greedy_base_card_le_baseMax`) and (ii) the node's residual order is small (`residualCard k ≤ n`), the
node fits its budget and `flagsAt = false`. **Contrapositive = P1's largeness clause on the real descent: a Phase-1
flag ⟹ the node's residual `Aut` is large** — the confinement-P1 step the assume-VT prune rests on. -/
theorem not_flagsAt_of_smallAut_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt residualCard : Nat → Nat) (k : Nat)
    (hn : 1 ≤ n)
    (hbase : baseAt k ≤ Nat.log 2 (residualCard k))
    (hsmall : residualCard k ≤ n) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = false := by
  apply not_flagsAt_of_base_le_spine adj P₀ χι₀ sel baseAt k hn
  calc baseAt k ≤ Nat.log 2 (residualCard k) := hbase
    _ ≤ Nat.log 2 n := Nat.log_mono_right hsmall
    _ ≤ baseMax n := log_two_le_baseMax n

/-! ## The residue-at-node concrete definitions — the last P1 seam

`flag_imp_large` (in `ScratchConfinement.lean`) carries the harvest base `baseAt` and the residual order
`residualCard` as *abstract* functions plus a greedy hypothesis `hgreedy`. This section gives them concrete
definitions on the real default spine and turns `hgreedy` into a theorem, so the confinement interface is fed by
the actual descent, not a guessed shape.

The level-`k` residue is `(adj, P₀)` with the spine's accumulated prefix `D_k = (defaultSpineChain … k).D`
individualized; its automorphism group is the pointed stabilizer `StabilizerAt adj P₀ D_k`, and a greedy base
*extending* `D_k` (from `exists_greedy_base_aux`, the pointed form of `exists_greedy_base_le_log`) has length
`≤ log₂ |StabilizerAt adj P₀ D_k|`. -/

/-- **The level-`k` residue's `Aut` order** — `|StabilizerAt adj P₀ D_k|`, the residual automorphism group after
the default spine individualizes its level-`k` prefix. This is the concrete `residualCard`: "`n < spineResidualCard
k`" is exactly "the node-`k` residue has large `Aut`" (the largeness clause P3 consumes). -/
noncomputable def spineResidualCard (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) : Nat :=
  Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
    (defaultSpineChain adj P₀ χι₀ sel k).D)

/-- **The level-`k` harvest base length** — how many extra individualizations a greedy base needs to discretize
the level-`k` residue (a base *extending* the prefix `D_k`), via `exists_greedy_base_aux`. This is the concrete
`baseAt` fed to `spineCappedCanonizerO`'s per-node harvest cost `oracleCost n (baseAt k) = n^(baseAt k)` (the
D7-declared model: harvest at base `b` explores ≤ `n^b` maps; any greedy base bounds it). Noncomputable (greedy
choice) — the cost model is a proof artifact; the executable track is separate. -/
noncomputable def spineBaseAt (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) : Nat :=
  (Classical.choose (exists_greedy_base_aux (adj := adj)
    (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
    (Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D))
    (defaultSpineChain adj P₀ χι₀ sel k).D le_rfl)).length

/-- **The greedy property, now a THEOREM (discharges the confinement interface's `hgreedy`).** On the concrete
spine functions the harvest base is at most `log₂` of the residual `Aut` — `spineBaseAt k ≤ log₂ (spineResidualCard
k)` — from `exists_greedy_base_aux`'s `2^|bs| ≤ |StabilizerAt … D_k|`. So `flag_imp_large`'s carried greedy
hypothesis holds by construction on the real descent; nothing is left abstract in P1's largeness half. -/
theorem spineBaseAt_le_log (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) :
    spineBaseAt adj P₀ χι₀ sel k ≤ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) := by
  have hspec := Classical.choose_spec (exists_greedy_base_aux (adj := adj)
    (P := (defaultSpineChain adj P₀ χι₀ sel k).P)
    (Nat.card (StabilizerAt adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D))
    (defaultSpineChain adj P₀ χι₀ sel k).D le_rfl)
  have h2 : 2 ^ spineBaseAt adj P₀ χι₀ sel k ≤ spineResidualCard adj P₀ χι₀ sel k := hspec.2
  exact Nat.le_log_of_pow_le (by norm_num) h2

end ChainDescent.ConfinementP1

/- ═══════════════════════════ (was ScratchConfinementP4.lean) ═══════════════════════════ -/


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
    (sel : Colouring n → Finset (Fin n)) (χ : Colouring n) (S : Finset (Fin n)) : Prop :=
  ∀ v w,
    v ∈ sel χ →
    w ∈ sel χ →
    OrbitPartition adj P S v w

/-- **The second producer of `SelectedCellIsOrbit` — structural, wall-free.** If the selected cell sits inside a
single `Stab(S)`-orbit, then in particular any two *same-colour* cell vertices are orbit-equivalent — dropping the
colour hypothesis. This wires the assume-VT structural target into the LANDED prune-completeness consumer
(`selectedCell_single_stabOrbit`), the sibling of `selectedCellIsOrbit_of_cellsAreOrbits` that avoids the
`CellsAreOrbits` / multi-base-WL wall. -/
theorem selectedCellIsOrbit_of_subsetOrbit
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χ : Colouring n} {S : Finset (Fin n)}
    (h : SelectedCellSubsetOrbit adj P sel χ S) :
    SelectedCellIsOrbit adj P sel χ S :=
  fun v w hv hw _hcolour => h v w hv hw

/-! ## The structural discharge — `SelectedCellSubsetOrbit` from residual-group transitivity

The content of P4 is that the residue's automorphism group `StabilizerAt adj P S` acts transitively on the
selected cell — a GROUP fact (for primitive rank-3: the point-stabilizer is transitive on each of its three
classes `{p}, Γ(p), Γ̄(p)`), **not** a claim that 1-WL reaches the orbit partition. These lemmas discharge
`SelectedCellSubsetOrbit` from that transitivity, isolating the remaining family-specific obligation to "the
residual group is transitive on the selected cell" — which sidesteps the multi-base `JointProfileRecoversAt` wall
(that wall is 1-WL *reaching* orbits; transitivity is a property of the group action itself). -/

/-- **The orbit-cover reduction — the interface for the rank-3 recursion.** If some representative `r`'s
`Stab(S)`-orbit covers the whole selected cell, then every pair in the cell is `Stab(S)`-orbit-equivalent, i.e.
the cell lies in one orbit. Reduces `SelectedCellSubsetOrbit` to the single-orbit-cover condition, where the
residue's group transitivity plugs in. Proof: `v, w ∈ orbit r` ⟹ `orbit v = orbit r = orbit w` ⟹ `w ∈ orbit v`. -/
theorem selectedCellSubsetOrbit_of_orbit_cover
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χ : Colouring n} {S : Finset (Fin n)} {r : Fin n}
    (hcover : ∀ w, w ∈ sel χ → OrbitPartition adj P S r w) :
    SelectedCellSubsetOrbit adj P sel χ S := by
  intro v w hv hw
  have hvr := mem_orbit_stabilizerAt_iff.mpr (hcover v hv)
  have hwr := mem_orbit_stabilizerAt_iff.mpr (hcover w hw)
  have hmem : w ∈ MulAction.orbit (StabilizerAt adj P S) v := by
    rw [MulAction.orbit_eq_iff.mpr hvr, ← MulAction.orbit_eq_iff.mpr hwr]
    exact MulAction.mem_orbit_self w
  exact mem_orbit_stabilizerAt_iff.mp hmem

/-- **Full residual transitivity ⟹ discharge (the VT root anchor).** When `StabilizerAt adj P S` acts
transitively on *all* vertices — e.g. `S = ∅` on a vertex-transitive scheme — the selected cell is trivially
within one orbit. The depth-0 anchor of the assume-VT recursion, discharged with **no** WL / `CellsAreOrbits`
input, purely from the group action. -/
theorem selectedCellSubsetOrbit_of_pretransitive
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χ : Colouring n} {S : Finset (Fin n)}
    (htrans : MulAction.IsPretransitive (StabilizerAt adj P S) (Fin n)) :
    SelectedCellSubsetOrbit adj P sel χ S := by
  intro v w _ _
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq v w
  exact mem_orbit_stabilizerAt_iff.mp ⟨g, hg⟩

/-! ## Per-node uniformity — the "recursion" is a per-prefix universal, not an unrolling

The descent never needs `VO_d → VO_{d−2}` reasoned as a chain: the confinement property is **quantified over
prefixes** (exactly the shape of `RecoversWhileSymmetric = ∀ T ⊇ S₀, ¬IsBase T → CellsAreOrbits T`), so a single
uniform per-node lemma discharges it at *whatever* residue each node presents. "Every node-4 residue harvests its
next step" is precisely this per-node form — no family-specific chain. -/

/-- **The per-prefix target** — `SelectedCellSubsetOrbit` at every prefix `T ⊇ S₀`. Mirrors
`RecoversWhileSymmetric`'s `∀ T ⊇ S₀` shape; the descent's recursion IS this universal. -/
def SelectedCellSubsetOrbitAt (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S₀ : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), S₀ ⊆ T → SelectedCellSubsetOrbit adj P sel (χsel T) T

/-- **Uniform per-node discharge — no recursion.** If at every prefix `T ⊇ S₀` some representative's `Stab(T)`-orbit
covers the selected cell, the per-prefix target holds: one lemma applied at each node. The confinement content is
thus reduced to the per-prefix cover hypothesis = the residue's **group transitivity on the selected cell**
(forms-graph / rank-3 structure) — the same statement at every node, never a `VO_d → VO_{d−2}` unrolling. -/
theorem selectedCellSubsetOrbitAt_of_cover
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    {S₀ : Finset (Fin n)}
    (h : ∀ T : Finset (Fin n), S₀ ⊆ T → ∃ r : Fin n,
        ∀ w, w ∈ sel (χsel T) → OrbitPartition adj P T r w) :
    SelectedCellSubsetOrbitAt adj P sel χsel S₀ := by
  intro T hT
  obtain ⟨r, hr⟩ := h T hT
  exact selectedCellSubsetOrbit_of_orbit_cover hr

/-! ## The frame-base selector — its sole requirement, and where it is discharged

The reduction above pins the entire confinement-P4 content to one property of the selector at each prefix: the
residual group `StabilizerAt adj P T` acts **transitively on the selected cell** (equivalently, some frame origin
`r`'s orbit covers it). Naming it as `FrameSelectorTransitive` isolates exactly the classical-group fact that the
frame-base selector relies on.

**Where it comes from — and why it is family-specific.** For the forms-graph residues this is **Witt's theorem**:
the orthogonal group `O(Q)` is transitive on isometric (isotropic) frames/flags of each type, so after
individualizing an isotropic frame `T` the residual group is transitive on the next isotropic-point cell. This is
a *citable classical theorem* (Artin, *Geometric Algebra*), **not** the multi-base `JointProfileRecoversAt` /
bounded-WL-dim wall (which is 1-WL *reaching* orbits — a different, open, quantitative question). It is genuinely
family-specific: for a Clebsch-type scheme the point-stabilizer is **not** transitive on the colour classes
(`ClebschConcrete.lean`), which is exactly why Clebsch is routed through a different leg — so `FrameSelectorTransitive`
must be tied to the confined (forms-graph) residue, delivered by the confinement lemma (P1+P3), never assumed
generically. Terminal anchor: at the seal's `SeparatesAtBoundedBase` (a `Discrete` base, all singletons) the cover
holds trivially; the intermediate prune nodes are the ones needing Witt-transitivity. -/

/-- **The frame-base selector's requirement (per prefix): the residual group is transitive on the selected cell.**
Stated with a distinguished frame origin `r` (as a frame base has), whose `Stab(T)`-orbit covers the cell — i.e.
Witt flag-transitivity of the residue's automorphism group. This is the ONE remaining input to confinement-P4;
for the forms graphs it is Witt's theorem (citable classical), false for Clebsch-like (family-specific). -/
def FrameSelectorTransitive (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S₀ : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), S₀ ⊆ T → ∃ r : Fin n,
    ∀ w, w ∈ sel (χsel T) →
      OrbitPartition adj P T r w

/-- **Frame-selector transitivity discharges confinement-P4 (the full reduction).** With the residual group
transitive on every selected cell, the per-prefix `SelectedCellSubsetOrbit` holds — hence (via
`selectedCellIsOrbit_of_subsetOrbit`) the landed prune-completeness consumer fires at every node, wall-free. The
assume-VT prune is sound exactly under `FrameSelectorTransitive`, whose forms-graph instance is Witt's theorem. -/
theorem selectedCellSubsetOrbitAt_of_frameSelectorTransitive
    {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {χsel : Finset (Fin n) → Colouring n}
    {S₀ : Finset (Fin n)}
    (h : FrameSelectorTransitive adj P sel χsel S₀) :
    SelectedCellSubsetOrbitAt adj P sel χsel S₀ :=
  selectedCellSubsetOrbitAt_of_cover h

end ChainDescent.ConfinementP4

/- ═══════════════════════════ (was ScratchConfinement.lean) ═══════════════════════════ -/


namespace ChainDescent.Confinement

open ChainDescent
open ChainDescent.CostModel.Oracle
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.NodeCountBridge

variable {n : Nat}

/-! ## P1 — largeness confinement, wired REAL on the spine

`flag_imp_large` is P1's contrapositive on the actual descent object: a Phase-1 flag forces the node's residual
`Aut` to be large. It is the landed `not_flagsAt_of_smallAut_spine` read contrapositively — the ONE place the cost
model (`flagsAt` on `spineCappedCanonizerO`) and correctness (the residue's `|Aut|`) interlock. The two seam inputs
are honest: `hgreedy` = the harvest algorithm's greedy-base property (`greedy_base_card_le_baseMax`), and
`residualCard` = the residue-at-node's `Aut` order (the last P1 wiring). -/
theorem flag_imp_large
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt residualCard : Nat → Nat) (k : Nat)
    (hn : 1 ≤ n)
    (hgreedy : baseAt k ≤ Nat.log 2 (residualCard k))
    (hflag : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true) :
    n < residualCard k := by
  by_contra hle
  rw [Nat.not_lt] at hle
  have hf := not_flagsAt_of_smallAut_spine adj P₀ χι₀ sel baseAt residualCard k hn hgreedy hle
  rw [hf] at hflag
  exact absurd hflag (by decide)

/-! ## The confinement lemma — flag ⟹ the cell is one orbit

The core reduction, with P1 plugged in real and P2/P3/Witt carried as the three open seams. Conclusion is exactly
the input the landed prune-completeness consumer needs (`SelectedCellIsOrbit`). -/

/-- **CONFINEMENT (the ①b core).** At a Phase-1 flagging node (level `k`, prefix `S`), the target cell is a single
`Stab(S)`-orbit. Chain: P1 (`hP1`) ⟹ `Large`; P2 (`hP2`) ⟹ `SymmetricFlag`; P3 (`hP3`, the seal recomposed with
classicality) ⟹ `PrimRank3Classical`; Witt (`hWitt`) ⟹ `FrameSelectorTransitive`; P4
(`selectedCellSubsetOrbitAt_of_frameSelectorTransitive` + `selectedCellIsOrbit_of_subsetOrbit`, real) ⟹
`SelectedCellIsOrbit`. Largeness is abstracted into `Large` + `hP1` — the concrete instantiation supplies the
*delivered* bound (`flag_imp_pow_baseMax_lt`: `2^(baseMax n) < residual`, super-poly), decoupling the assembly from
the threshold. The abstract `Large`/`SymmetricFlag`/`PrimRank3Classical` are the honest interface; discharging
`hP1`/`hP2`/`hP3`/`hWitt` = landing P1/P2/P3/Witt. -/
theorem confinement_selectedCellIsOrbit
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat)
    (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat)
    (Large SymmetricFlag PrimRank3Classical : Nat → Prop)
    (hP1 : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true → Large k)
    (hP2 : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true → SymmetricFlag k)
    (hP3 : Large k → SymmetricFlag k → PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  selectedCellIsOrbit_of_subsetOrbit
    (selectedCellSubsetOrbitAt_of_frameSelectorTransitive
      (hWitt (hP3 (hP1 hflag) (hP2 hflag))) S (Finset.Subset.refl S))

/-! ## Disposition assembly — flag case ∪ witness case ⟹ SinglePathDisposition

`SinglePathDisposition` (`∀ S, SelectedCellIsOrbit`) is what feeds `CertifiedSinglePath`. It needs the cell-is-orbit
property at EVERY node, split by the §7b dichotomy: a flagging node uses CONFINEMENT (above); a non-flagging node
uses the harvest WITNESS (`hWitness`, sound by construction). The `nodeOf` map (each prefix `S` is consumed at some
level) is the descent-model seam linking the per-node flag to the per-prefix disposition. -/

/-- **The single-path disposition from confinement + witness.** Every selected cell is one orbit: at `S`'s node
`nodeOf S`, either it flagged (⟹ `hFlagCase`, i.e. confinement) or it did not (⟹ `hWitness`, the certified-harvest
branch). This is the structural form of the empirical single-path finding (`leaves = 1`). -/
theorem singlePathDisposition_of_confinement
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (baseAt : Nat → Nat)
    (χsel : Finset (Fin n) → Colouring n)
    (nodeOf : Finset (Fin n) → Nat)
    (hFlagCase : ∀ S : Finset (Fin n),
        flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
          ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) = true →
        SelectedCellIsOrbit adj P₀ sel (χsel S) S)
    (hWitness : ∀ S : Finset (Fin n),
        flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
          ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) = false →
        SelectedCellIsOrbit adj P₀ sel (χsel S) S) :
    SinglePathDisposition adj P₀ sel χsel := by
  intro S
  cases hb : flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel baseAt).step
      ((spineCappedCanonizerO adj P₀ χι₀ sel baseAt).w n) (nodeOf S) with
  | true => exact hFlagCase S hb
  | false => exact hWitness S hb

/-- **The certified single path from the disposition (real).** Straight through the landed
`certifiedSinglePath_of_disposition`: the confinement-driven disposition delivers both poly ingredients — bounded
node count (`≤ n`) and every consumed cell a single residual orbit (the completeness core). -/
theorem certifiedSinglePath_of_confinement
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (hcell : TargetsNonsingletonCell sel) (hne : NonemptyOnNonDiscrete sel)
    (hdisp : SinglePathDisposition adj P₀ sel χsel) :
    CertifiedSinglePath adj P₀ χι₀ sel χsel :=
  certifiedSinglePath_of_disposition hcell hne hdisp

/-! ## The remaining seam BEYOND P1–P4 — representative-transport invariance (①b completeness)

`CertifiedSinglePath` says the single path visits single-orbit cells and terminates in `≤ n` nodes. Turning that
into `canon_complete` (①b) needs one more fact the P1–P4 chain does NOT supply: choosing a *different
representative* of a single-orbit cell yields the SAME leaf canonical (else the single-path output is not
iso-invariant). The depth-1 core is landed — `NodeCountBridge.repTransport` / `repTransport_of_orbitPartition`
transport the one-deeper partition along the orbit automorphism — but the level-iteration and the lift to
`canonAdj` equality are OPEN (partly blocked on the `canonForm` lex-min placeholder). It is pinned here as
`RepresentativeInvariant` so the full ①b path is visible: P1–P4 ⟹ `CertifiedSinglePath`, then
`RepresentativeInvariant` ⟹ `canon_complete`.

**★ SUPERSEDED (2026-07-08) — the real ①b lives in `ScratchConfinementCompleteness.lean`.** That module lands the
①b **← direction** (`canonForm?_complete_mpr`) and pins the → direction to the honest **X3** open lemma
(`CanonPartitionInvariant`; the `samePartition ⟹ equal canonForm` framing in the prose above turned out FALSE — X3
is a §15.7 `canonForm`/individualization design piece, see that file's header). The two placeholder decls below
(`IsoInvariantCanonical = True → True`, `isoInvariantCanonical_of_certifiedSinglePath`) are the earlier skeleton;
keep for the `CertifiedSinglePath` shape, but the authoritative ①b interface is `ScratchConfinementCompleteness`. -/

/-- **[SUPERSEDED placeholder — see `ScratchConfinementCompleteness` for the real ①b.]** An abstract predicate for
"the certified single path computes the iso-invariant canonical". Kept only for the skeleton shape below. -/
def IsoInvariantCanonical
    (_adj : AdjMatrix n) (_P₀ : PMatrix n) (_χι₀ : Colouring n)
    (_sel : Colouring n → Finset (Fin n)) : Prop := True → True  -- placeholder shape; Runtime Phase swaps in `canonForm?`-completeness

/-- **The full ①b path, pinned.** `CertifiedSinglePath` + the representative-transport invariance ⟹ the
iso-invariant canonical (①b). `RepresentativeInvariant` is the transport seam (level-lift of `repTransport`); its
discharge is the last ingredient of non-rigid completeness beyond P1–P4. Stated so the dependency is machine-visible
and cannot be silently skipped. -/
theorem isoInvariantCanonical_of_certifiedSinglePath
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (_hpath : CertifiedSinglePath adj P₀ χι₀ sel χsel)
    (RepresentativeInvariant : Prop)
    (_hrep : RepresentativeInvariant)
    (hbridge : CertifiedSinglePath adj P₀ χι₀ sel χsel → RepresentativeInvariant →
        IsoInvariantCanonical adj P₀ χι₀ sel) :
    IsoInvariantCanonical adj P₀ χι₀ sel :=
  hbridge _hpath _hrep

/-! ## P1 fully wired on the concrete spine — the last seam discharged

Specializing `flag_imp_large` with the concrete `spineBaseAt` / `spineResidualCard` (the level-`k` residue's
harvest base and `Aut` order, `ScratchConfinementP1`) and the proved `spineBaseAt_le_log` removes the abstract
`baseAt` / `residualCard` / `hgreedy` from P1's largeness half: on the real spine
`spineCappedCanonizerO … spineBaseAt`, a Phase-1 flag at node `k` implies the level-`k` residue's automorphism
group is large. -/

/-- **P1 on the concrete spine (no carried hypotheses).** A flag at node `k` of the spine instantiated with the
real per-node harvest base `spineBaseAt` implies `n < spineResidualCard k = |StabilizerAt adj P₀ D_k|` — the
node-`k` residue has large `Aut`. This is confinement-P1's largeness clause on the actual descent, with the
residue-at-node seam (concrete `baseAt`/`residualCard`) closed; it feeds P3 (large ∧ ¬rigid ⟹ primitive rank-3). -/
theorem flag_imp_large_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    n < spineResidualCard adj P₀ χι₀ sel k :=
  flag_imp_large adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)
    (spineResidualCard adj P₀ χι₀ sel) k hn
    (spineBaseAt_le_log adj P₀ χι₀ sel k) hflag

/-- **P1, the STRONG delivered bound (threshold-explicit largeness).** A Phase-1 flag at node `k` implies the
residual `Aut` exceeds `2^(baseMax n)` — the honest largeness the flag delivers, set by the threshold `baseMax n =
(log₂ n)²`, giving `2^(baseMax n) = n^{log₂ n}` (super-poly). **This is what makes the seal's super-poly
`IsLargeScheme` satisfiable** (P3's `hLargeBridge`); the weaker `flag_imp_large_spine` (`n < residual`) is a
corollary. Proof: the flag gives `oracleBudget n < oracleCost n (spineBaseAt k)` = `n^{baseMax n} < n^{spineBaseAt
k}` ⟹ (`n ≥ 2`) `baseMax n < spineBaseAt k ≤ log₂(residual)` ⟹ `2^{baseMax n} < 2^{log₂ residual} ≤ residual`. -/
theorem flag_imp_pow_baseMax_lt (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k := by
  have hiff := (spineCappedCanonizerO_flagsAt_iff adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) k).mp hflag
  simp only [oracleBudget, oracleCost] at hiff
  rw [Nat.pow_lt_pow_iff_right hn] at hiff
  have hlt : baseMax n < Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) :=
    lt_of_lt_of_le hiff (spineBaseAt_le_log adj P₀ χι₀ sel k)
  have hpos : 0 < spineResidualCard adj P₀ χι₀ sel k := card_stabilizerAt_pos
  calc 2 ^ baseMax n
      < 2 ^ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) :=
        (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hlt
    _ ≤ spineResidualCard adj P₀ χι₀ sel k := Nat.pow_log_le_self 2 hpos.ne'

/-- **Satisfiability / soundness: a residue with `|Aut| ≤ 2^(baseMax n)` does NOT flag.** The exact converse of
`flag_imp_pow_baseMax_lt` — only residues with super-poly `Aut` (`> 2^(baseMax n) = n^{log₂ n}`) flag. So every
**poly-`Aut`** residue (`|Aut| ≤ n^c ≤ 2^(baseMax n)` once `c ≤ log₂ n`) is below threshold and is NOT
assume-VT-pruned. This is precisely why the non-Schurian-SRG danger is excluded: a Chang graph
(`|Aut| = 384`, poly-bounded, non-VT) never Phase-1-flags, so it is never unsoundly pruned — the soundness the
threshold raise buys. Proof: `spineBaseAt k ≤ log₂(residual) ≤ log₂(2^{baseMax n}) = baseMax n` ⟹ not_flagsAt. -/
theorem not_flagsAt_of_residualCard_le_pow (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hle : spineResidualCard adj P₀ χι₀ sel k ≤ 2 ^ baseMax n) :
    flagsAt (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = false := by
  apply not_flagsAt_of_base_le_spine adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) k hn
  calc spineBaseAt adj P₀ χι₀ sel k
      ≤ Nat.log 2 (spineResidualCard adj P₀ χι₀ sel k) := spineBaseAt_le_log adj P₀ χι₀ sel k
    _ ≤ Nat.log 2 (2 ^ baseMax n) := Nat.log_mono_right hle
    _ = baseMax n := Nat.log_pow (by norm_num : (1:ℕ) < 2) (baseMax n)

/-! ## P2 — deferral confinement on the concrete spine

The phase split is `IsBase T` (rigid / base-reached — residual symmetry exhausted, `DiscretizesAtBases` /
IR-core) vs `¬IsBase T` (symmetric — residual symmetry present, `RecoversWhileSymmetric`). P2 says a Phase-1
flag is confined to the symmetric side, and it falls straight out of P1: a flag forces a *large* residual `Aut`
(`flag_imp_large_spine`), but a base has a *trivial* residual (`card = 1`, `card_stabilizerAt_eq_one_iff_isBase`).
So a flag cannot occur at a base — "rigid decisions are deferred (trivial residual ⟹ `oracleCost = n^0`, cheap),
never expensively harvested; a Phase-1 flag is not rigid-caused." -/

/-- **P2 (deferral confinement).** A Phase-1 flag at node `k` implies the level-`k` prefix is **not a base** — the
node is in the symmetric domain (`¬IsBase`, residual symmetry still present). Proof: P1 gives `n < spineResidualCard
k`; a base has trivial residual (`spineResidualCard k = 1`); with `n ≥ 1` that is a contradiction. Hence
rigid/base-reached / IR-core nodes (trivial residual, cheap harvest) never Phase-1-flag. -/
theorem flag_imp_symmetric_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (hn : 1 ≤ n)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P (defaultSpineChain adj P₀ χι₀ sel k).D := by
  intro hbase
  have hlarge := flag_imp_large_spine adj P₀ χι₀ sel k hn hflag
  have hone : spineResidualCard adj P₀ χι₀ sel k = 1 :=
    card_stabilizerAt_eq_one_iff_isBase.mpr hbase
  omega

/-! ## Confinement on the concrete spine — P1 ∧ P2 discharged, only P3/Witt abstract

Instantiating `confinement_selectedCellIsOrbit` with the STRONG largeness `Large k := 2^(baseMax n) <
spineResidualCard k` (P1, via `flag_imp_pow_baseMax_lt` — the super-poly delivered bound that makes the seal's
`IsLargeScheme` satisfiable) and the concrete symmetric predicate `¬IsBase` (P2, via `flag_imp_symmetric_spine`)
leaves only the two genuinely-open seams as hypotheses: **P3** (`hP3`: large ∧ ¬rigid ⟹ primitive rank-3 classical)
and **Witt** (`hWitt`). Requires `2 ≤ n` (the threshold arithmetic; `n ≤ 1` is trivially canonical). -/

/-- **Confinement on the real spine (P1 ∧ P2 wired; P3/Witt carried).** A Phase-1 flag at node `k` ⟹ the target
cell at prefix `S` is one `Stab(S)`-orbit, given only P3 (`hP3`, now consuming the **super-poly** bound `2^(baseMax
n) < residual`) and Witt (`hWitt`). P1 (via `flag_imp_pow_baseMax_lt`) and P2 (via `flag_imp_symmetric_spine`) are
discharged from the spine. -/
theorem confinement_selectedCellIsOrbit_spine (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    (PrimRank3Classical : Nat → Prop)
    (hP3 : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k →
        ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P (defaultSpineChain adj P₀ χι₀ sel k).D →
        PrimRank3Classical k)
    (hWitt : PrimRank3Classical k → FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel) χsel S k
    (fun j => 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel j)
    (fun j => ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel j).P (defaultSpineChain adj P₀ χι₀ sel j).D)
    PrimRank3Classical
    (fun hf => flag_imp_pow_baseMax_lt adj P₀ χι₀ sel k hn hf)
    (fun hf => flag_imp_symmetric_spine adj P₀ χι₀ sel k (by omega) hf)
    hP3 hWitt hflag

end ChainDescent.Confinement

/- ═══════════════════════════ (was ScratchConfinementP3.lean) ═══════════════════════════ -/


namespace ChainDescent.ConfinementP3

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.Confinement
open ChainDescent.NodeCountBridge
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **The residue-scheme model at node `k` (the model bridge — carried).** A `SchurianScheme n` `S_k` presenting
the level-`k` residue: all relations occur (`hne`), rank ≥ 2 (`hrank`), and its scheme-automorphism order equals
the residue's residual `Aut` order (`hcard`), so P1's largeness transfers onto the scheme side. This is the
`SchurianScheme` model-faithfulness gap; a residue for which no such faithful `S_k` exists is *non-schurian* and is
honestly flagged into `UnhandledResidue` (D0), never assume-VT-pruned. The `hcard` field keeps the model non-vacuous
(it must match the actual residue, not be an arbitrary scheme). -/
structure ResidueSchemeModel (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) where
  S : SchurianScheme n
  hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true
  hrank : 2 ≤ S.rank
  hcard : Nat.card S.toAssociationScheme.SchemeAutGroup = spineResidualCard adj P₀ χι₀ sel k

/-- **`PrimRank3Classical` — the predicate P3 produces and Witt (P4) consumes.** The residue is presented by a
scheme model `M` that the seal classifies as a **Cameron section** (`IsCameronScheme n M.S`) — the primitive
rank-3 node-4/hidden-Johnson residue. Parameterized by the seal's `IsCameronScheme` (the endgame supplies "what
counts as Cameron"). The subsequent classicality step (Liebeck) + Witt turns this into `FrameSelectorTransitive`
(the assembly's `hWitt`). -/
def PrimRank3Classical (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n))
    (IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop) (k : Nat) : Prop :=
  ∃ M : ResidueSchemeModel adj P₀ χι₀ sel k, IsCameronScheme n M.S

/-- **P3 — the seal recomposition (provable core wired REAL).** Given the residue-scheme model `M`, the largeness
bridge `hLargeBridge` (piece 2, the threshold carrier), primitivity `hprim` (piece 3, `hImprim`-inherited), and the
cited classification `hClassify` (G3), a flag's large residual (`n < spineResidualCard k`) makes the residue a
**Cameron section** via the landed `exhaustiveObstruction_scheme`. Produces exactly the assembly's `hP3` shape
(`n < spineResidualCard k → ¬IsBase D_k → PrimRank3Classical k`). The `¬IsBase` (symmetric) input is part of the
interface but is subsumed by largeness (P2 *derived* `¬IsBase` from it), so it is unused in the derivation. -/
theorem residue_primRank3Classical (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat)
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hLargeBridge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hlarge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k)
    (_hsym : ¬ IsBase adj (defaultSpineChain adj P₀ χι₀ sel k).P
      (defaultSpineChain adj P₀ χι₀ sel k).D) :
    PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k :=
  ⟨M, exhaustiveObstruction_scheme hClassify M.S M.hne hprim M.hrank (hLargeBridge hlarge)⟩

/-! ## Confinement on the real spine — P1 ∧ P2 ∧ P3 all wired, only Witt + the P3 carriers remaining

Feeding `residue_primRank3Classical` (P3, via the real seal) into `confinement_selectedCellIsOrbit_spine`
(P1 ∧ P2 wired) leaves as hypotheses exactly: the cited classification `hClassify` (G3), the residue-scheme model
`M` (the `SchurianScheme` gap, D0-absorbed), the largeness bridge `hLargeBridge` (the threshold decision), the
primitivity `hprim` (`hImprim`), and Witt `hWitt` (`PrimRank3Classical ⟹ FrameSelectorTransitive` — Liebeck +
Witt). Everything else — P1, P2, P3's composition, P4's producer — is proved. -/

/-- **Confinement on the real spine, P1 ∧ P2 ∧ P3 wired.** A Phase-1 flag at node `k` ⟹ the target cell at prefix
`S` is one `Stab(S)`-orbit, carrying only the P3 pieces (`hClassify`/`M`/`hLargeBridge`/`hprim`) and Witt
(`hWitt`). The whole confinement chain now composes through the real seal `exhaustiveObstruction_scheme`; the
remaining obligations are the carried citations/gaps, not project logic. -/
theorem confinement_selectedCellIsOrbit_spine_P3 (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsLargeScheme IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification IsLargeScheme IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hLargeBridge : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k → IsLargeScheme n M.S)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine adj P₀ χι₀ sel χsel S k hn
    (PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme)
    (fun hlarge hsym =>
      residue_primRank3Classical adj P₀ χι₀ sel k hClassify M hLargeBridge hprim hlarge hsym)
    hWitt hflag

/-! ## Satisfiability of `hLargeBridge` — it is DISCHARGEABLE at the raised threshold

The threshold decision's payoff: with `baseMax = (log₂ n)²`, the flag delivers `2^(baseMax n) < residual`
(super-poly), and the seal's largeness predicate can be instantiated at exactly that threshold — at which the
largeness bridge is not merely *assumable* but **provable** (from `M.hcard`). With the old `baseMax = log₂ n`
(delivering only `residual > n`) the same bridge would be *false* for a super-poly `IsLargeScheme` (a residue with
`n < |Aut| ≤ n^{log₂ n}` satisfies the flag's bound but not super-poly largeness). So the raise is exactly what
makes the P3 input satisfiable. -/

/-- **The confinement's largeness predicate at the delivered threshold** — `|Aut| > 2^(baseMax n) = n^{log₂ n}`, a
super-polynomial threshold. A genuine Cameron classification (G3) holds at any super-poly threshold, so `hClassify`
at this predicate is the real citation. -/
def confinementLargeScheme (n : Nat) : ∀ (m : Nat), SchurianScheme m → Prop :=
  IsLargeSchemeViaAut (fun c => 2 ^ baseMax n < c)

/-- **`hLargeBridge` is DISCHARGEABLE (the satisfiability check).** With `IsLargeScheme := confinementLargeScheme n`,
the largeness bridge `2^(baseMax n) < spineResidualCard k → IsLargeScheme n M.S` is *provable*: the residual order
IS the scheme-Aut order (`M.hcard`), so the delivered super-poly bound transfers verbatim. So the P3 largeness input
is real, not a placeholder — the raised threshold made it so. -/
theorem largeBridge_confinementLargeScheme (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (h : 2 ^ baseMax n < spineResidualCard adj P₀ χι₀ sel k) :
    confinementLargeScheme n n M.S := by
  show 2 ^ baseMax n < Nat.card M.S.toAssociationScheme.SchemeAutGroup
  rw [M.hcard]; exact h

/-- **Confinement with `hLargeBridge` DISCHARGED** — carries only the genuine citations/gaps: `hClassify` (G3 at the
super-poly `confinementLargeScheme`), the model `M`, primitivity `hprim`, and Witt `hWitt`. The largeness bridge is
gone (proved by `largeBridge_confinementLargeScheme`). This is the confinement chain at its tightest: P1 ∧ P2 ∧ P3
wired, largeness satisfiable, only the named external results remaining. -/
theorem confinement_selectedCellIsOrbit_spine_P3_discharged (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      FrameSelectorTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine_P3 adj P₀ χι₀ sel χsel S k hn hClassify M
    (largeBridge_confinementLargeScheme adj P₀ χι₀ sel k M) hprim hWitt hflag

end ChainDescent.ConfinementP3

/- ═══════════════════════════ (was ScratchConfinementWitt.lean) ═══════════════════════════ -/


namespace ChainDescent.ConfinementWitt

open ChainDescent
open ChainDescent.ConfinementP1
open ChainDescent.ConfinementP4
open ChainDescent.ConfinementP3
open ChainDescent.Confinement
open ChainDescent.NodeCountBridge
open ChainDescent.CostModel.PerNode
open ChainDescent.CostModel.SpineInstance
open ChainDescent.CostModel.Oracle

variable {n : Nat}

/-- **Witt cell-transitivity (the honest citation shape).** At every prefix `T ⊇ S₀`, the residual group is
transitive on the selected cell: any two cell vertices are `Stab(T)`-orbit-equivalent (`OrbitPartition`). This is
Witt's theorem for the forms-graph residue — `O(Q)` acts transitively on the isometric isotropic points after
fixing an isotropic frame `T`. Deliberately **distinct** from `FrameSelectorTransitive` (the ∃-frame-origin form);
the reduction below derives that from this. -/
def WittCellTransitive (adj : AdjMatrix n) (P₀ : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S₀ : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), S₀ ⊆ T →
    ∀ v w, v ∈ sel (χsel T) →
      w ∈ sel (χsel T) →
      OrbitPartition adj P₀ T v w

/-- **The Witt reduction (PROVED): cell-transitivity ⟹ `FrameSelectorTransitive`.** Per prefix `T`, produce a
frame origin `r` whose `Stab(T)`-orbit covers the selected cell. If the cell is nonempty, take `r` to be any cell
element — cell-transitivity gives `OrbitPartition r w` for every cell `w`. If it is empty, any vertex `r` works
(the covering condition is vacuous). Needs `Nonempty (Fin n)` for the empty-cell fallback. This is the genuine
group-action content the Witt step contributes on top of the citation. -/
theorem frameSelectorTransitive_of_wittCellTransitive [Nonempty (Fin n)]
    {adj : AdjMatrix n} {P₀ : PMatrix n} {sel : Colouring n → Finset (Fin n)}
    {χsel : Finset (Fin n) → Colouring n} {S₀ : Finset (Fin n)}
    (h : WittCellTransitive adj P₀ sel χsel S₀) :
    FrameSelectorTransitive adj P₀ sel χsel S₀ := by
  intro T hT
  by_cases hne : (sel (χsel T)).Nonempty
  · obtain ⟨r, hr⟩ := hne
    exact ⟨r, fun w hw => h T hT r w hr hw⟩
  · obtain ⟨r⟩ := ‹Nonempty (Fin n)›
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨r, fun w hw => ?_⟩
    rw [hne] at hw
    simp at hw

/-! ## The confinement lemma carrying ONLY named external results

`confinement_selectedCellIsOrbit_spine_P3_discharged` (P3, largeness bridge already discharged) needs `hWitt :
PrimRank3Classical k → FrameSelectorTransitive`. Supplying it via the Witt reduction leaves only the four named
citations. -/

/-- **★ Confinement on the real spine, reduced to named citations only.** A Phase-1 flag at node `k` ⟹ the target
cell at prefix `S` is one `Stab(S)`-orbit, carrying **only**: `hClassify` (G3 at the super-poly
`confinementLargeScheme`), the residue-scheme model `M` (the `SchurianScheme` gap = D0 non-schurian flag),
primitivity `hprim` (= `hImprim`), and `hCitation` (Witt + Liebeck = `Publication.witt_flag_transitivity`).
Everything else — P1 (super-poly threshold), P2 (deferral), P3's seal composition, the discharged largeness bridge,
the Witt reduction, P4's producer — is **proved** axiom-clean. This is the whole non-rigid confinement lemma
reduced to its trusted base. -/
theorem confinement_selectedCellIsOrbit_spine_witt (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hCitation : PrimRank3Classical adj P₀ χι₀ sel IsCameronScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact confinement_selectedCellIsOrbit_spine_P3_discharged adj P₀ χι₀ sel χsel S k hn hClassify M hprim
    (fun h => frameSelectorTransitive_of_wittCellTransitive (hCitation h)) hflag

/-! ## Classicality-threaded form — the compound Witt citation split into Liebeck + Witt

**Why (route-c-plan §7c gap (b) — the silent-correctness guard).** Witt's cell-transitivity theorem applies to
**classical** residues, but the compound `hCitation : PrimRank3Classical → WittCellTransitive` above jumps straight
from *Cameron* (`IsCameronScheme`) to cell-transitive, bearing the classicality step implicitly. A Cameron-but-non-
classical primitive rank-3 residue would then be assume-VT-pruned as if handled, yet Witt need not apply — a silent
correctness risk. The honest form threads classicality explicitly as **two** faithful citations:
  · `hLiebeck` — **Liebeck**: a Cameron (large primitive rank-3) scheme is **classical** (`IsCameronScheme n T →
    IsClassicalScheme n T`). Largeness is baked into `IsCameronScheme` (the G3-classification output), which is what
    rules out the bounded-order non-classical rank-3 exceptions.
  · `hWitt` — **Witt**: a *classical* residue's cell is transitive (`PrimRank3Classical … IsClassicalScheme k →
    WittCellTransitive`). Reuses `PrimRank3Classical` at the classical predicate — its Witt-faithful antecedent.
So the `ConfinementCitations` bundle reads {G3, **Liebeck**, **Witt**, hImprim, D0} — the true citation set — rather
than a compound. Same conclusion, composed internally from the split. -/

/-- **★ Confinement, classicality-threaded (the reviewer-faithful citation split).** Identical conclusion to
`confinement_selectedCellIsOrbit_spine_witt`, but the compound Witt citation is split into Liebeck
(`hLiebeck : Cameron ⟹ classical`) + Witt (`hWitt : classical ⟹ cell-transitive`), with an explicit
`IsClassicalScheme` predicate threaded between. Closes the §7c gap (b): classicality is a *checked* step (via
Liebeck, using the largeness inside `IsCameronScheme`), not a bundled assumption, so a non-classical Cameron residue
cannot be silently Witt-pruned. -/
theorem confinement_selectedCellIsOrbit_spine_witt_classical (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (χsel : Finset (Fin n) → Colouring n)
    (S : Finset (Fin n)) (k : Nat) (hn : 2 ≤ n)
    {IsCameronScheme IsClassicalScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hClassify : PrimitiveCCClassification (confinementLargeScheme n) IsCameronScheme)
    (M : ResidueSchemeModel adj P₀ χι₀ sel k)
    (hprim : M.S.toAssociationScheme.IsPrimitive)
    (hLiebeck : ∀ T : SchurianScheme n, IsCameronScheme n T → IsClassicalScheme n T)
    (hWitt : PrimRank3Classical adj P₀ χι₀ sel IsClassicalScheme k →
      WittCellTransitive adj P₀ sel χsel S)
    (hflag : flagsAt
        (spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).step
        ((spineCappedCanonizerO adj P₀ χι₀ sel (spineBaseAt adj P₀ χι₀ sel)).w n) k = true) :
    SelectedCellIsOrbit adj P₀ sel (χsel S) S :=
  confinement_selectedCellIsOrbit_spine_witt adj P₀ χι₀ sel χsel S k hn hClassify M hprim
    (fun hCam => hWitt (hCam.imp (fun M' hM' => hLiebeck M'.S hM'))) hflag

end ChainDescent.ConfinementWitt

/- ═══════════════════════════ (was ScratchConfinementSchurianModel.lean) ═══════════════════════════ -/


namespace ChainDescent.ConfinementSchurianModel

open ChainDescent
open ChainDescent.ConfinementP3
open ChainDescent.ConfinementP1

variable {n : Nat}

/-- **★ The scheme-extraction constructor.** Build the confinement's `ResidueSchemeModel` from a residual automorphism
group `G` (pretransitive + generously transitive), its rank ≥ 2, the 2-closure citation `h2c`, and the faithfulness
count `hcount`. The `S := orbitalScheme G` is schurian by construction; `hne` is proved outright; `hcard` is `h2c`
composed with `hcount`. This crystallizes the SchurianScheme modelling gap into its three genuine inputs and shows the
scheme-construction itself is not a gap. -/
noncomputable def residueModel_of_orbitalGroup
    (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (k : Nat)
    [Nonempty (Fin n)]
    {G : Subgroup (Equiv.Perm (Fin n))}
    (htrans : MulAction.IsPretransitive G (Fin n))
    (hsymm : ∀ v w : Fin n, (orbMk v w : Orbital G) = orbMk w v)
    (hrank : 2 ≤ (orbitalScheme G htrans hsymm).rank)
    (h2c : (orbitalScheme G htrans hsymm).toAssociationScheme.SchemeAutGroup = G)
    (hcount : Nat.card G = spineResidualCard adj P₀ χι₀ sel k) :
    ResidueSchemeModel adj P₀ χι₀ sel k where
  S := orbitalScheme G htrans hsymm
  hne := fun i => by
    refine ⟨(orbitalIdx G i).out.1, (orbitalIdx G i).out.2, ?_⟩
    show decide (orbitalIdx G i = orbMk (orbitalIdx G i).out.1 (orbitalIdx G i).out.2) = true
    rw [orbMk_out, decide_eq_true_eq]
  hrank := hrank
  hcard := by rw [h2c]; exact hcount

end ChainDescent.ConfinementSchurianModel
