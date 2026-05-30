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

end ChainDescent
