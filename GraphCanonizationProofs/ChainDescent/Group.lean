import ChainDescent
import ChainDescent.CascadeOracle
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Part A (A1–A3) — the automorphism group, its action, and normal chains

Until now the proof stack represented automorphisms only as the *predicate*
`IsAut π adj` on a single permutation and the orbit *relation*
`OrbitPartition adj P S v w`. There was **no group object** — no `Subgroup`,
no `MulAction`, no quotient — anywhere in the sources. Tier 3's vocabulary
(`H₀ ⊵ … ⊵ H_k`, quotient graphs `G/Hᵢ`) is meaningless without one.

This module is the **glue tier** of `docs/chain-descent-tier3-tractable-buildout.md`
Part A:

* **A1** — `AutGroup adj : Subgroup (Equiv.Perm (Fin n))`, the group `{π | IsAut π adj}`,
  with the `Subgroup` axioms discharged from the existing `IsAut.refl/.trans/.symm`.
  Plus the bridge `orbitPartition_iff_autGroup` keeping `OrbitPartition` the working
  object while exposing the group element.
* **A2** — the vertex `MulAction` (inherited from `Equiv.Perm`'s action on `Fin n`,
  restricted to the subgroup) and the **orbit bridge** relating `MulAction.orbit
  (AutGroup adj) v` to `OrbitPartition adj P ∅`-classes (the `P`-preservation conjunct
  handled by a `P`-invariance hypothesis, per the Tier-2 `hP_invariant` pattern).
* **A3** — `LayerChain adj`, a finite descending chain of relatively-normal subgroups
  `AutGroup adj ⊵ … ⊵ ⊥`, with the trivial one-step chain as an inhabitant.

Everything here is glue over Mathlib group theory + the existing `IsAut` lemmas.
The one Mathlib gap (A4, the quotient *graph* `G/H` and the cell = quotient-vertex
lemma) is deliberately **not** in this file — it is the medium-risk piece gating B1.

This lifts the permutation-level **support backbone** (`CascadeOracle.lean §C.0.1`:
`orbitPartition_of_support_disjoint`, `exists_orbit_witness_of_aut`) to the group level:
those lemmas pin `π ∈ Aut_S ⟺ Disjoint S π.support` for a *single* `π`; A1's `AutGroup`
+ A2's action make "the pointwise-`S`-stabilizer" and "`v`'s orbit" first-class.
-/

namespace ChainDescent

open scoped Pointwise

variable {n : Nat}

/-! ## A1 — `Aut(G)` as a group -/

/-- **The automorphism group.** The subgroup of `Equiv.Perm (Fin n)` consisting of
the permutations that preserve the adjacency matrix. The `Subgroup` axioms are exactly
the already-proved `IsAut.refl` (identity), `IsAut.trans` (composition), and
`IsAut.symm` (inverse) — note `Equiv.Perm` multiplication `a * b = b.trans a`, so
`mul_mem'` reads `IsAut.trans hb ha`. -/
def AutGroup (adj : AdjMatrix n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | IsAut π adj}
  one_mem' := IsAut.refl
  mul_mem' := by
    intro a b ha hb
    show IsAut (a * b) adj
    rw [Equiv.Perm.mul_def]
    exact IsAut.trans hb ha
  inv_mem' := by
    intro a ha
    show IsAut a⁻¹ adj
    rw [Equiv.Perm.inv_def]
    exact IsAut.symm ha

@[simp] theorem mem_autGroup {adj : AdjMatrix n} {π : Equiv.Perm (Fin n)} :
    π ∈ AutGroup adj ↔ IsAut π adj := Iff.rfl

/-- **The `OrbitPartition` ↔ `AutGroup` bridge.** The orbit relation is exactly:
"some group element in the pointwise-`S`-stabilizer (the `FixesPointwise` conjunct)
that also preserves `P` sends `v` to `w`." Repackages the bare permutation `π` of
`OrbitPartition` as a genuine `g : AutGroup adj`, keeping `OrbitPartition` the working
object while making the group element available where the chain is referenced. -/
theorem orbitPartition_iff_autGroup {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {v w : Fin n} :
    OrbitPartition adj P S v w ↔
      ∃ g : AutGroup adj,
        (∀ x u, P ((g : Equiv.Perm (Fin n)) x) ((g : Equiv.Perm (Fin n)) u) = P x u) ∧
        FixesPointwise (g : Equiv.Perm (Fin n)) S ∧ (g : Equiv.Perm (Fin n)) v = w := by
  constructor
  · rintro ⟨π, hπ, hP, hfix, hvw⟩
    exact ⟨⟨π, hπ⟩, hP, hfix, hvw⟩
  · rintro ⟨⟨π, hπ⟩, hP, hfix, hvw⟩
    exact ⟨π, hπ, hP, hfix, hvw⟩

/-! ## A2 — action on vertices + orbit bridge

`AutGroup adj` acts on `Fin n` by the restriction of `Equiv.Perm (Fin n)`'s natural
action (`π • v = π v`). The `MulAction (AutGroup adj) (Fin n)` instance is found
automatically (subgroup restriction of `Equiv.Perm.applyMulAction`). The smul is
`g • v = (↑g) v`. -/

/-- The subgroup action's `smul` is application of the underlying permutation. -/
@[simp] theorem autGroup_smul {adj : AdjMatrix n} (g : AutGroup adj) (v : Fin n) :
    g • v = (g : Equiv.Perm (Fin n)) v := rfl

/-- **Orbit membership, unfolded.** `w` is in `v`'s `AutGroup`-orbit iff some
automorphism sends `v` to `w`. (The pure-orbit statement, before the `P`-preservation
refinement of `OrbitPartition`.) -/
theorem mem_orbit_autGroup_iff {adj : AdjMatrix n} {v w : Fin n} :
    w ∈ MulAction.orbit (AutGroup adj) v ↔ ∃ π : Equiv.Perm (Fin n), IsAut π adj ∧ π v = w := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨(g : Equiv.Perm (Fin n)), g.2, by simpa using hg⟩
  · rintro ⟨π, hπ, hvw⟩
    exact ⟨⟨π, hπ⟩, by simpa using hvw⟩

/-- **The orbit bridge.** Under a `P`-invariance hypothesis (every automorphism of
`adj` preserves `P` — the Tier-2 `hP_invariant` pattern; holds for the trivial/profile
`P`), `v`'s `AutGroup`-orbit coincides with the **root** orbit relation
`OrbitPartition adj P ∅` (no individualization: `FixesPointwise π ∅` is vacuous).
This is the group-level reading of the support backbone's root case. -/
theorem mem_orbit_autGroup_iff_orbitPartition {adj : AdjMatrix n} {P : PMatrix n}
    (hPinv : ∀ π : Equiv.Perm (Fin n), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    {v w : Fin n} :
    w ∈ MulAction.orbit (AutGroup adj) v ↔ OrbitPartition adj P ∅ v w := by
  rw [mem_orbit_autGroup_iff]
  constructor
  · rintro ⟨π, hπ, hvw⟩
    exact ⟨π, hπ, hPinv π hπ, fun s hs => absurd hs (Finset.notMem_empty s), hvw⟩
  · rintro ⟨π, hπ, _, _, hvw⟩
    exact ⟨π, hπ, hvw⟩

/-! ## A3 — normal subgroup chains

A `LayerChain adj` is a finite descending chain
`AutGroup adj = layer 0 ⊵ layer 1 ⊵ … ⊵ layer len = ⊥`
of subgroups, each **relatively normal** in its predecessor
(`(layer (i+1)).subgroupOf (layer i)` is `Normal`). This is the `H₀ ⊵ … ⊵ H_k`
substrate Tier 3a (B1) is stated over; the quotients `layer i / layer (i+1)` (via
`(layer (i+1)).subgroupOf (layer i)`) are the per-layer groups whose cascade class
B1 reasons about. -/

/-- A finite descending normal chain from `AutGroup adj` to `⊥`. `layer` is total on
`ℕ` but only constrained up to `len`. -/
structure LayerChain (adj : AdjMatrix n) where
  /-- chain length (number of quotients) -/
  len : Nat
  /-- the subgroups of the chain -/
  layer : Nat → Subgroup (Equiv.Perm (Fin n))
  /-- the chain starts at the full automorphism group -/
  head_eq : layer 0 = AutGroup adj
  /-- the chain ends at the trivial subgroup -/
  last_eq : layer len = ⊥
  /-- each layer is contained in its predecessor -/
  descending : ∀ i, i < len → layer (i + 1) ≤ layer i
  /-- each layer is normal in its predecessor -/
  normal : ∀ i, i < len → ((layer (i + 1)).subgroupOf (layer i)).Normal

namespace LayerChain

/-- **The trivial chain** `AutGroup adj ⊵ ⊥` (length 1). Witnesses that `LayerChain`
is inhabited: `⊥` is normal in any subgroup, so the one-step chain is always valid. -/
def trivial (adj : AdjMatrix n) : LayerChain adj where
  len := 1
  layer := fun i => if i = 0 then AutGroup adj else ⊥
  head_eq := by simp
  last_eq := by simp
  descending := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    show (⊥ : Subgroup (Equiv.Perm (Fin n))) ≤ AutGroup adj
    exact bot_le
  normal := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    show ((⊥ : Subgroup (Equiv.Perm (Fin n))).subgroupOf (AutGroup adj)).Normal
    rw [Subgroup.bot_subgroupOf]
    infer_instance

instance (adj : AdjMatrix n) : Inhabited (LayerChain adj) := ⟨trivial adj⟩

end LayerChain

/-! ## A4 — the quotient graph `G/H` and the cell = quotient-vertex lemma

The one piece Mathlib does not package: the quotient of a graph by the orbits of a
(normal) subgroup of its automorphism group. Here the relevant orbits are the
`Aut_S`-orbits — the classes of `OrbitPartition adj P S` (the pointwise-`S`-stabilizer
orbits; `= MulAction.orbit` of the stabilizer subgroup, bridged by A1/A2 at the root).
`OrbitPartition` is already an equivalence relation (`refl/symm/trans` proved), so its
quotient is the quotient **vertex set**; the **cell = quotient-vertex** lemma
(`cell_iff_orbitMk_eq`) is then immediate from the cascade machinery
(`CellsAreOrbits` + `OrbitPartition.subset_warmRefine`). This is the lemma B1's
induction step rests on.

The quotient *graph adjacency* is the genuinely conditional part: `adj v w` is **not**
constant on orbit-pairs in general (`adj (g v) w = adj v (g⁻¹ w)`, a different
representative), so a simple induced adjacency is well-defined exactly under
`QuotientAdjCompatible`. We give the lift under that hypothesis and its defining
equation — honest about where the friction the doc flags actually sits. -/

variable {n : Nat}

/-- The `Aut_S`-orbit relation as a `Setoid` — `OrbitPartition`'s proved
`refl`/`symm`/`trans` packaged as an equivalence. -/
def orbitSetoid (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Setoid (Fin n) where
  r := OrbitPartition adj P S
  iseqv := ⟨OrbitPartition.refl, OrbitPartition.symm, OrbitPartition.trans⟩

/-- **The quotient vertex set** `V(G)/Aut_S` — vertices of the quotient graph. -/
abbrev OrbitQuotient (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) : Type :=
  Quotient (orbitSetoid adj P S)

/-- The quotient map sending a vertex to its `Aut_S`-orbit (its quotient vertex). -/
def orbitMk (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) (v : Fin n) :
    OrbitQuotient adj P S :=
  Quotient.mk (orbitSetoid adj P S) v

/-- `orbitMk v = orbitMk w` iff `v, w` lie in the same `Aut_S`-orbit. -/
theorem orbitMk_eq_iff {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    {v w : Fin n} : orbitMk adj P S v = orbitMk adj P S w ↔ OrbitPartition adj P S v w :=
  Quotient.eq

/-- The quotient vertex set is finite (a quotient of `Fin n`). -/
noncomputable instance (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Fintype (OrbitQuotient adj P S) := Fintype.ofFinite _

noncomputable instance (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    DecidableEq (OrbitQuotient adj P S) := Classical.decEq _

/-- **The cell = quotient-vertex lemma.** Under `CellsAreOrbits` (cells are no coarser
than orbits — the open localisation half, proved on the cascade class), two vertices
share a 1-WL cell of `(G, S)` **iff** they are the same quotient vertex. The forward
direction is `CellsAreOrbits` + `Quotient.sound`; the backward is the unconditional
`OrbitPartition.subset_warmRefine` (orbits refine cells) + `Quotient.exact`. This is
the correspondence B1's cascade-composition induction steps through: the per-layer
cascade class runs on the quotient `G/Aut_S`, whose vertices are exactly the cells. -/
theorem cell_iff_orbitMk_eq {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    (hco : CellsAreOrbits adj P S) (v w : Fin n) :
    warmRefine adj P (individualizedColouring n S) v =
        warmRefine adj P (individualizedColouring n S) w ↔
      orbitMk adj P S v = orbitMk adj P S w := by
  constructor
  · intro hcell
    exact Quotient.sound (hco v w hcell)
  · intro hmk
    exact OrbitPartition.subset_warmRefine (Quotient.exact hmk)

/-! ### The quotient graph adjacency (conditional on compatibility) -/

/-- **Quotient-adjacency compatibility.** The adjacency `adj v w` is constant on
`Aut_S`-orbit pairs — exactly the well-definedness condition for a simple induced
adjacency on the quotient. Holds trivially at discreteness (orbits are singletons);
fails for coarser `S` in general (the multigraph/symmetrisation subtlety the doc
flags). The quotient *graph* is well-defined precisely here. -/
def QuotientAdjCompatible (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n)) :
    Prop :=
  ∀ v v' w w', OrbitPartition adj P S v v' → OrbitPartition adj P S w w' →
    adj.adj v w = adj.adj v' w'

/-- **The induced adjacency on the quotient graph**, well-defined under
`QuotientAdjCompatible`. Lifts `adj.adj` along both quotient coordinates. -/
def quotientAdj {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    (h : QuotientAdjCompatible adj P S) :
    OrbitQuotient adj P S → OrbitQuotient adj P S → Nat :=
  Quotient.lift₂ (fun v w => adj.adj v w) (fun v w v' w' hv hw => h v v' w w' hv hw)

/-- The quotient adjacency's defining equation: on representatives it is the original
adjacency. (`Quotient.lift₂` computation; `rfl`.) -/
@[simp] theorem quotientAdj_mk {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    (h : QuotientAdjCompatible adj P S) (v w : Fin n) :
    quotientAdj h (orbitMk adj P S v) (orbitMk adj P S w) = adj.adj v w := rfl

/-- At discreteness the compatibility holds for free (orbits are singletons, so
`v' = v` and `w' = w`): the quotient graph is always well-defined at the recursion
bottom — the same anchor as `cellsAreOrbits_of_discrete`. -/
theorem quotientAdjCompatible_of_discrete {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S))) :
    QuotientAdjCompatible adj P S := by
  intro v v' w w' hvv' hww'
  -- orbits collapse to equality at discreteness (`subset_warmRefine` + `Discrete`).
  have hv : v = v' := hd v v' (OrbitPartition.subset_warmRefine hvv')
  have hw : w = w' := hd w w' (OrbitPartition.subset_warmRefine hww')
  rw [hv, hw]

/-! ### Tying A4 back to the group object (A1/A2)

The quotient above is by the *relation* `OrbitPartition adj P ∅` (the working object).
Under `P`-invariance it coincides with the orbit relation of the **group** `AutGroup adj`
(A1) acting on vertices (A2) — so the quotient vertex set is literally `V(G)/Aut(G)`,
the group-theoretic object the Tier-3 narrative names. This honors the doc's
"quotient by a (normal) subgroup of `Aut(G)`" framing for the root case. -/

/-- The root orbit relation = the `AutGroup` MulAction orbit relation (under
`P`-invariance). The relational form of the A2 orbit bridge, symmetrised for the
`orbitRel` direction. -/
theorem orbitPartition_empty_iff_orbitRel {adj : AdjMatrix n} {P : PMatrix n}
    (hPinv : ∀ π : Equiv.Perm (Fin n), IsAut π adj → ∀ x u, P (π x) (π u) = P x u)
    (a b : Fin n) :
    OrbitPartition adj P ∅ a b ↔ (MulAction.orbitRel (AutGroup adj) (Fin n)).r a b := by
  rw [MulAction.orbitRel_apply, ← mem_orbit_autGroup_iff_orbitPartition hPinv,
      MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  -- goal: (∃ g, g • a = b) ↔ (∃ g, g • b = a)
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · rintro ⟨g, hg⟩; exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-- **The root quotient is `V(G)/Aut(G)`.** Under `P`-invariance, the relational
quotient `OrbitQuotient adj P ∅` is equivalent to the `MulAction` orbit quotient of
the group `AutGroup adj` — the group-theoretic quotient vertex set. -/
noncomputable def orbitQuotientEquivAutGroup {adj : AdjMatrix n} {P : PMatrix n}
    (hPinv : ∀ π : Equiv.Perm (Fin n), IsAut π adj → ∀ x u, P (π x) (π u) = P x u) :
    OrbitQuotient adj P ∅ ≃ MulAction.orbitRel.Quotient (AutGroup adj) (Fin n) :=
  Quotient.congr (Equiv.refl (Fin n)) (by
    intro a b
    simpa using orbitPartition_empty_iff_orbitRel hPinv a b)

end ChainDescent
