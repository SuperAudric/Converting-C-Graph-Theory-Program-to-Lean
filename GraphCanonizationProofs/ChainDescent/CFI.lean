import ChainDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

/-!
# CFI infrastructure (Stage 1: foundational definitions)

Concrete construction of CFI graphs in Lean, mirroring
[`CfiGraphGenerator.cs`](../../GraphCanonizationProject/CfiGraphGenerator.cs).
Discharges (in stages) the Tier-1 placeholder axioms `IsCFI`,
`cfi_depth_bound`, `cfi_cascades_polynomially` declared in
`ChainDescent.lean` §17.4.

The full CFI program is structured as four stages:

1. **Stage 1 (this file, present revision)** — `CFIBase` structure,
   neighbours/degree primitives, vertex count formula. Foundations
   only; no proofs of substance.
2. **Stage 2** — `CFIVertex H` inductive type, `Fintype` instance,
   flattening bijection to `Fin N`, the CFI adjacency function.
   Replaces the abstract `IsCFI` axiom with a concrete predicate.
3. **Stage 3** — `Aut(CFI(H)) ≅ Z₂^{β_H} ⋊ Aut(H)` structure lemma.
   Multi-week; not strictly required for Theorem 1.
4. **Stage 4** — the cascade lemma (Cai-Fürer-Immerman WL-dim
   result). Discharges `cfi_cascades_polynomially`. Multi-week.

Stage 1 has no Mathlib dependency beyond `Finset` / `Fintype`; we
keep the bare `AdjMatrix n` representation used in `ChainDescent.lean`
rather than introducing `SimpleGraph` from Mathlib.

This file lives separate from `ChainDescent.lean` to keep the main
chain-descent proofs file under ~4000 lines; CFI infrastructure may
grow to ≥1000 lines by Stage 2.
-/

namespace ChainDescent

/-! ## §1 — `CFIBase`: a base graph for CFI

A **CFI base graph** on vertex set `Fin m` is a simple graph (symmetric,
loopless adjacency) with every vertex of degree ≥ 2. The degree
constraint is structural — CFI gadgets need at least 2 endpoints per
vertex, otherwise the subset vertex `a_S` set degenerates. -/

/-- A **CFI base graph** on `Fin m`: simple (symmetric, loopless) with
every vertex of degree ≥ 2. -/
structure CFIBase (m : Nat) where
  /-- The adjacency matrix. Entries 0/1 (treated as boolean). -/
  adj : AdjMatrix m
  /-- Symmetric: `adj u v = adj v u`. -/
  symm : ∀ u v : Fin m, adj.adj u v = adj.adj v u
  /-- Loopless: no self-edges. -/
  loopless : ∀ v : Fin m, adj.adj v v = 0
  /-- Every vertex has at least 2 neighbours. -/
  deg_ge_two : ∀ v : Fin m,
    2 ≤ (Finset.univ.filter (fun w : Fin m => adj.adj v w ≠ 0)).card

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-! ## §2 — Neighbours and degree -/

/-- The neighbour set of `v` in the base graph. -/
def neighbors (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun w => H.adj.adj v w ≠ 0)

/-- The degree of `v` in the base graph. -/
def degree (v : Fin m) : Nat := (H.neighbors v).card

/-- `w ∈ H.neighbors v` iff `adj v w ≠ 0`. -/
@[simp] theorem mem_neighbors {v w : Fin m} :
    w ∈ H.neighbors v ↔ H.adj.adj v w ≠ 0 := by
  simp [neighbors]

/-- Degree is at least 2 (structural CFI requirement). -/
theorem degree_ge_two (v : Fin m) : 2 ≤ H.degree v := H.deg_ge_two v

/-- Loops are not neighbours. -/
theorem not_self_mem_neighbors (v : Fin m) : v ∉ H.neighbors v := by
  rw [mem_neighbors]
  rw [H.loopless v]
  decide

/-- Neighbour relation is symmetric: `w ∈ N(v) ↔ v ∈ N(w)`. -/
theorem mem_neighbors_symm {v w : Fin m} :
    w ∈ H.neighbors v ↔ v ∈ H.neighbors w := by
  rw [mem_neighbors, mem_neighbors, H.symm]

/-- The number of edges in the base graph, counted by ordered pairs. -/
def edgeCountOrdered : Nat :=
  Finset.univ.sum H.degree

/-! ## §3 — CFI vertex count formula

Each base vertex `v` of degree `d = degree v` produces a gadget with
`2^(d-1) + 2*d` vertices:
- `2^(d-1)` subset vertices `a_S^v` (one per even-cardinality
  `S ⊆ N(v)`).
- `2 * d` endpoint vertices `e^b_{v→w}` (two per neighbour, indexed
  by `b ∈ {0, 1}`).

Total CFI vertex count is the sum of gadget sizes. -/

/-- Size of the gadget at `v` in `CFI(H)`. -/
def gadgetSize (v : Fin m) : Nat :=
  2 ^ (H.degree v - 1) + 2 * H.degree v

/-- Total vertex count of `CFI(H)`. -/
def cfiVertexCount : Nat :=
  Finset.univ.sum H.gadgetSize

/-- Gadget size is at least 6 (since `degree ≥ 2` gives `2^1 + 4 = 6`). -/
theorem gadgetSize_ge_six (v : Fin m) : 6 ≤ H.gadgetSize v := by
  unfold gadgetSize
  have h := H.degree_ge_two v
  -- 2^(d-1) ≥ 2 when d-1 ≥ 1; 2*d ≥ 4 when d ≥ 2.
  have hd1 : 1 ≤ H.degree v - 1 := by omega
  have h1 : (2 : Nat) ≤ 2 ^ (H.degree v - 1) := by
    have : (2 : Nat) ^ 1 ≤ 2 ^ (H.degree v - 1) :=
      Nat.pow_le_pow_right (by decide) hd1
    simpa using this
  have h2 : 4 ≤ 2 * H.degree v := by omega
  omega

/-- `cfiVertexCount H` is positive when `m > 0`. -/
theorem cfiVertexCount_pos (hm : 0 < m) : 0 < H.cfiVertexCount := by
  unfold cfiVertexCount
  apply Finset.sum_pos
  · intro v _
    have := H.gadgetSize_ge_six v
    omega
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩

/-! ## §4 — Even-cardinality subsets of N(v) (Stage 2 prerequisite)

The subset vertices `a_S^v` of `CFI(H)` are indexed by
even-cardinality subsets `S ⊆ N(v)`. This section defines that
Finset, used by Stage 2's `CFIVertex` constructor. -/

/-- Even-cardinality subsets of `N(v)`. The subset vertices `a_S^v` of
`CFI(H)` are indexed by this Finset. -/
def evenSubsetsOfNeighbors (v : Fin m) : Finset (Finset (Fin m)) :=
  (H.neighbors v).powerset.filter (fun S => S.card % 2 = 0)

/-- The empty set is an even subset of `N(v)`. -/
theorem empty_mem_evenSubsetsOfNeighbors (v : Fin m) :
    (∅ : Finset (Fin m)) ∈ H.evenSubsetsOfNeighbors v := by
  simp [evenSubsetsOfNeighbors]

/-- Membership characterisation: `S ∈ evenSubsetsOfNeighbors v` iff
`S ⊆ N(v)` and `|S|` is even. -/
@[simp] theorem mem_evenSubsetsOfNeighbors {v : Fin m} {S : Finset (Fin m)} :
    S ∈ H.evenSubsetsOfNeighbors v ↔ S ⊆ H.neighbors v ∧ S.card % 2 = 0 := by
  simp [evenSubsetsOfNeighbors]

end CFIBase

/-! ## §5 — Concrete example: `triangleBase` smoke test

A minimal concrete `CFIBase` to confirm the structure is inhabited.
`CFI(triangle) = CFI(K_3)` has 18 vertices: 3 gadgets × 6 vertices each
(2^1 subsets + 2*2 endpoints). -/

/-- The triangle `K_3` as a `CFIBase`. Smallest base graph satisfying
the degree-≥-2 invariant. -/
def triangleBase : CFIBase 3 where
  adj := ⟨fun i j => if i = j then 0 else 1⟩
  symm := by
    intros u v
    by_cases h : u = v
    · subst h; rfl
    · have hne : v ≠ u := fun h' => h h'.symm
      simp [h, hne]
  loopless := by intro v; simp
  deg_ge_two := by decide

/-- Every vertex of `triangleBase` has degree 2. -/
theorem triangleBase_degree : ∀ v : Fin 3, triangleBase.degree v = 2 := by
  decide

/-- `triangleBase`'s CFI has 18 vertices: `3 × (2^1 + 2*2)`. -/
theorem triangleBase_cfiVertexCount : triangleBase.cfiVertexCount = 18 := by
  decide

end ChainDescent
