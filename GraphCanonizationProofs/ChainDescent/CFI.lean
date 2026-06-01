import ChainDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.SymmDiff

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
private def edgeCountOrdered : Nat :=
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
private theorem cfiVertexCount_pos (hm : 0 < m) : 0 < H.cfiVertexCount := by
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

/-! ## §6 — CFI vertex type (Stage 2.1)

The vertex set of `CFI(H)` decomposes into two kinds:
- **Subset vertices** `a_S^v`: indexed by `(v, S)` with `v ∈ V_H` and
  `S ⊆ N(v)` of even cardinality.
- **Endpoint vertices** `e^b_{v→w}`: indexed by `(v, w, b)` with
  `v ∈ V_H`, `w ∈ N(v)`, `b ∈ {0, 1}`.

We encode each kind as a `Σ` type bundling base-vertex with the
constructor-specific data (a subtype of even subsets, or a
neighbour × Bool pair). `CFIVertex H` is their sum. The `Fintype`
and `DecidableEq` instances derive automatically from the sub-pieces.

This is the type-level skeleton; the adjacency function on
`CFIVertex H` and the flattening bijection to
`Fin (cfiVertexCount H)` are Stage 2.2 and 2.3 respectively. -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-- Subset vertex of `CFI(H)`: `(v, S)` with `S ∈ evenSubsetsOfNeighbors v`. -/
abbrev SubsetVertex : Type :=
  Σ v : Fin m, { S : Finset (Fin m) // S ∈ H.evenSubsetsOfNeighbors v }

/-- Endpoint vertex of `CFI(H)`: `(v, w, b)` with `w ∈ N(v)` and
`b : Bool`. -/
abbrev EndpointVertex : Type :=
  Σ v : Fin m, { w : Fin m // w ∈ H.neighbors v } × Bool

/-- Vertex of `CFI(H)`: subset + endpoint vertices, as a sum. -/
abbrev CFIVertex : Type :=
  H.SubsetVertex ⊕ H.EndpointVertex

-- The Fintype/DecidableEq instances for Sigma over Subtype-of-Finset
-- do not derive automatically via `inferInstance` (Lean's typeclass
-- search doesn't unify Subtype/Finset.mem in this context). We
-- provide them explicitly via `Subtype.fintype` and Sigma/Sum
-- composition.

instance (H : CFIBase m) (v : Fin m) :
    Fintype { S : Finset (Fin m) // S ∈ H.evenSubsetsOfNeighbors v } :=
  Subtype.fintype _

instance (H : CFIBase m) (v : Fin m) :
    Fintype { w : Fin m // w ∈ H.neighbors v } :=
  Subtype.fintype _

instance (H : CFIBase m) : Fintype H.SubsetVertex :=
  inferInstanceAs (Fintype (Σ v : Fin m, { S : Finset (Fin m) // S ∈ H.evenSubsetsOfNeighbors v }))

instance (H : CFIBase m) : Fintype H.EndpointVertex :=
  inferInstanceAs (Fintype (Σ v : Fin m, { w : Fin m // w ∈ H.neighbors v } × Bool))

instance (H : CFIBase m) : Fintype H.CFIVertex :=
  inferInstanceAs (Fintype (H.SubsetVertex ⊕ H.EndpointVertex))

instance (H : CFIBase m) : DecidableEq H.SubsetVertex :=
  inferInstanceAs (DecidableEq (Σ v : Fin m, { S : Finset (Fin m) // S ∈ H.evenSubsetsOfNeighbors v }))

instance (H : CFIBase m) : DecidableEq H.EndpointVertex :=
  inferInstanceAs (DecidableEq (Σ v : Fin m, { w : Fin m // w ∈ H.neighbors v } × Bool))

instance (H : CFIBase m) : DecidableEq H.CFIVertex :=
  inferInstanceAs (DecidableEq (H.SubsetVertex ⊕ H.EndpointVertex))

end CFIBase

/-! ## §7 — Stage 2.1 smoke test on `triangleBase`

Verify the vertex type cardinalities match the formula
`cfiVertexCount = 18` for `triangleBase`:
- `SubsetVertex`: 3 base vertices × 2 even subsets each (sizes 0 and 2)
  = 6.
- `EndpointVertex`: 3 base vertices × 2 neighbours × 2 parities = 12.
- Total: 18. -/

/-- Triangle's subset vertices: 6 total (3 base vertices × 2 even subsets).

Proved by kernel `decide` (axiom-clean: `[propext, Classical.choice,
Quot.sound]`). These triangle cardinalities are *subsumed* by the general,
structural §11 lemmas (`card_SubsetVertex` / `card_EndpointVertex` /
`card_CFIVertex`); they are retained as direct Stage-2.1 smoke tests that
do not forward-reference §11. (Formerly `native_decide`, which compiled to
native code but polluted the axiom set with `native_decide.ax`; kernel
`decide` keeps the whole module axiom-clean — the Fintype enumeration is
small enough to reduce in the kernel.) -/
example : Fintype.card triangleBase.SubsetVertex = 6 := by decide

/-- Triangle's endpoint vertices: 12 total (3 × 2 × 2). -/
example : Fintype.card triangleBase.EndpointVertex = 12 := by decide

/-- Triangle's full CFI vertex type: 18 elements, matching `cfiVertexCount`. -/
theorem triangleBase_cfiVertex_card :
    Fintype.card triangleBase.CFIVertex = 18 := by decide

/-! ## §8 — CFI adjacency function (Stage 2.2)

The adjacency relation on `CFIVertex H`, encoding the construction of
[`CfiGraphGenerator.cs`](../../GraphCanonizationProject/CfiGraphGenerator.cs):

- **Intra-gadget**: a subset vertex `a_S^v` and an endpoint vertex
  `e^b_{v→w}` are adjacent iff they are in the same gadget (`v_a =
  v_e`) and `(w ∈ S) ⊕ (b = true)`. Concretely:
  - `a_S^v ∼ e^0_{v→w}` iff `w ∈ S`.
  - `a_S^v ∼ e^1_{v→w}` iff `w ∉ S`.
- **Inter-gadget bridge** (untwisted): endpoint `e^b_{v→w}` adjacent
  to endpoint `e^b_{w→v}` (same parity, mirror direction).
- All other pairs (subset-subset, subset-endpoint across gadgets,
  endpoint-endpoint within same gadget): not adjacent.

We model this as `H.CFIVertex → H.CFIVertex → Nat` returning 0 or 1,
matching `AdjMatrix`'s convention. The Stage 2.3 task will lift this
through the flattening bijection to produce an `AdjMatrix
H.cfiVertexCount`. -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-- CFI adjacency function on `CFIVertex H`. Returns 1 (adjacent) or
0 (not adjacent). -/
def cfiAdj : H.CFIVertex → H.CFIVertex → Nat
  -- Subset-subset: never adjacent.
  | .inl _, .inl _ => 0
  -- Subset-endpoint: adjacent iff same gadget AND `w ∈ S` XOR `b`.
  | .inl ⟨v_a, S_pair⟩, .inr ⟨v_e, w_pair, b⟩ =>
      if v_a = v_e ∧ decide (w_pair.val ∈ S_pair.val) ≠ b then 1 else 0
  -- Endpoint-subset: symmetric formula.
  | .inr ⟨v_e, w_pair, b⟩, .inl ⟨v_a, S_pair⟩ =>
      if v_a = v_e ∧ decide (w_pair.val ∈ S_pair.val) ≠ b then 1 else 0
  -- Endpoint-endpoint: untwisted bridge iff `v₁ = w₂ ∧ w₁ = v₂ ∧ b₁ = b₂`.
  | .inr ⟨v₁, w_pair₁, b₁⟩, .inr ⟨v₂, w_pair₂, b₂⟩ =>
      if v₁ = w_pair₂.val ∧ w_pair₁.val = v₂ ∧ b₁ = b₂ then 1 else 0

/-- **Symmetry**: `cfiAdj x y = cfiAdj y x`. The subset-endpoint and
endpoint-subset clauses use identical formulae; subset-subset is
trivially 0; endpoint-endpoint requires `Eq.comm` on each conjunct. -/
theorem cfiAdj_symm (x y : H.CFIVertex) : H.cfiAdj x y = H.cfiAdj y x := by
  match x, y with
  | .inl _, .inl _ => rfl
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl
  | .inr ⟨v₁, w_pair₁, b₁⟩, .inr ⟨v₂, w_pair₂, b₂⟩ =>
    show (if v₁ = w_pair₂.val ∧ w_pair₁.val = v₂ ∧ b₁ = b₂ then 1 else 0) =
         (if v₂ = w_pair₁.val ∧ w_pair₂.val = v₁ ∧ b₂ = b₁ then 1 else 0)
    by_cases h : v₁ = w_pair₂.val ∧ w_pair₁.val = v₂ ∧ b₁ = b₂
    · obtain ⟨h1, h2, h3⟩ := h
      have h' : v₂ = w_pair₁.val ∧ w_pair₂.val = v₁ ∧ b₂ = b₁ :=
        ⟨h2.symm, h1.symm, h3.symm⟩
      rw [if_pos ⟨h1, h2, h3⟩, if_pos h']
    · have h' : ¬ (v₂ = w_pair₁.val ∧ w_pair₂.val = v₁ ∧ b₂ = b₁) := by
        rintro ⟨h1, h2, h3⟩
        exact h ⟨h2.symm, h1.symm, h3.symm⟩
      rw [if_neg h, if_neg h']

/-- **Looplessness**: `cfiAdj x x = 0`. Subset-subset is trivial;
endpoint-endpoint requires that `w ≠ v` (the neighbour can't equal
the base vertex by `not_self_mem_neighbors`), which falsifies the
`v = w` conjunct. -/
theorem cfiAdj_loopless (x : H.CFIVertex) : H.cfiAdj x x = 0 := by
  match x with
  | .inl _ => rfl
  | .inr ⟨v, w_pair, b⟩ =>
    show (if v = w_pair.val ∧ w_pair.val = v ∧ b = b then 1 else 0) = 0
    have hw : w_pair.val ∈ H.neighbors v := w_pair.property
    have hne : v ≠ w_pair.val := by
      intro heq
      apply H.not_self_mem_neighbors v
      exact Eq.subst (motive := fun x => x ∈ H.neighbors v) heq.symm hw
    have hcond : ¬ (v = w_pair.val ∧ w_pair.val = v ∧ b = b) := by
      rintro ⟨h1, _, _⟩
      exact hne h1
    rw [if_neg hcond]

end CFIBase

/-! ## §8.1 — CFI has no twins (the twin slice is complementary to CFI)

A **twin pair** is two distinct vertices with identical adjacency to every other
vertex; a twin pair is resolved by the *transposition* `(v w)`, the witness behind
`CascadeOracle.cellsAreOrbits_of_twin_cells` / `orbitPartition_swap_of_twin` and the
linear oracle's `configSwap_of_twin`. A natural question (raised when wiring the twin
slice to CFI completeness) is whether CFI's abelian `Z₂` symmetry discharges the twin
hypothesis. **It does not** — `CFI(H)` has *no* twins at all:

- Every endpoint `e^b_{v→w}` has **exactly one** endpoint-neighbour, its bridge partner
  `e^b_{w→v}`, which is unique to it — so two distinct endpoints have distinct
  endpoint-neighbours, never twins.
- Every subset vertex `a_S^v` has `degree v ≥ 2` endpoint-neighbours and its
  neighbourhood encodes `S` uniquely — so distinct subset vertices differ, and a subset
  vertex (≥ 2 endpoint-neighbours) is never a twin of an endpoint (exactly 1).

So CFI's `Z₂` is realised by a **global gadget-flip involution**, *not* a transposition
(matching `LinearOracle.configSwap_of_swap`'s non-`hgfix` general case). The twin slice
(`cellsAreOrbits_of_twin_cells`) and CFI are therefore **complementary** abelian classes:
the twin slice covers genuine-twin / module graphs; CFI completeness routes through the
*general* orbit recovery (`theorem_1_HOR_cfi_oddDeg`) plus the general gadget twist, not
the twin lemma. Confirmed concretely for `CFI(triangle)` below; the argument above is
general.

Proved by kernel `decide` (axiom-clean: `[propext, Classical.choice, Quot.sound]`).
Formerly `native_decide`, which compiled the `∀∀∃`-over-18-vertices search to native code
but added a `native_decide.ax` axiom to the module; the kernel reduces the same search
directly, keeping the file axiom-clean. -/
theorem cfi_triangle_no_twins :
    ∀ x y : triangleBase.CFIVertex, x ≠ y →
      ∃ z, triangleBase.cfiAdj x z ≠ triangleBase.cfiAdj y z := by
  decide

/-! ## §9 — Stage 2.3: lift to `AdjMatrix` + concrete `IsCFI`

Three deliverables:

1. **`cfiAdjMatrix`** — `cfiAdj` lifted through the canonical
   `CFIVertex H ≃ Fin (Fintype.card H.CFIVertex)` bijection
   (`Fintype.equivFin`) to a concrete `AdjMatrix (Fintype.card
   H.CFIVertex)`. Noncomputable since `Fintype.equivFin` is.
2. **`cfiAdjMatrix_symm` / `cfiAdjMatrix_loopless`** — basic
   properties lifted from `cfiAdj_symm`/`cfiAdj_loopless`.
3. **`IsCFI'`** — concrete `Prop` predicate "`adj` is the adjacency
   matrix of `CFI(H)` for some base `H`." Coexists with the abstract
   `axiom IsCFI` declared in `ChainDescent.lean §17.4`; retiring the
   axiom is a follow-on refactor that requires touching the Tier-1
   theorems' `IsCFI` hypotheses.

A separate combinatorial follow-on (out of scope here) would prove
`Fintype.card H.CFIVertex = H.cfiVertexCount` so that `cfiAdjMatrix`
can be cast to `AdjMatrix H.cfiVertexCount` — the identity reduces to
"the number of even subsets of a `d`-element set is `2^(d-1)`". -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-- **The CFI adjacency matrix**, indexed by `Fin (Fintype.card
H.CFIVertex)`. Lifts `cfiAdj` through `Fintype.equivFin`.

Noncomputable because `Fintype.equivFin` is. The classical witness
that the CFI construction produces a well-defined adjacency matrix
on `Fin N` for some `N`; downstream consumers (e.g., `IsCFI'`) treat
it existentially. -/
noncomputable def cfiAdjMatrix : AdjMatrix (Fintype.card H.CFIVertex) :=
  let e : Fin (Fintype.card H.CFIVertex) ≃ H.CFIVertex :=
    (Fintype.equivFin H.CFIVertex).symm
  ⟨fun i j => H.cfiAdj (e i) (e j)⟩

/-- The CFI adjacency matrix is symmetric. -/
theorem cfiAdjMatrix_symm (i j : Fin (Fintype.card H.CFIVertex)) :
    H.cfiAdjMatrix.adj i j = H.cfiAdjMatrix.adj j i := by
  show H.cfiAdj _ _ = H.cfiAdj _ _
  exact H.cfiAdj_symm _ _

/-- The CFI adjacency matrix is loopless. -/
theorem cfiAdjMatrix_loopless (i : Fin (Fintype.card H.CFIVertex)) :
    H.cfiAdjMatrix.adj i i = 0 := by
  show H.cfiAdj _ _ = 0
  exact H.cfiAdj_loopless _

end CFIBase

/-- **Concrete `IsCFI` predicate.** A graph `adj : AdjMatrix n` is a
CFI graph when it admits a base graph `H : CFIBase m` and a bijection
`Fin n ≃ H.CFIVertex` through which `adj` matches `cfiAdj H`.

Modelled as a `structure` rather than `∃` so the base graph is
addressable as data (`h.H`, `h.m`, etc.) — load-bearing for the
`cfi_depth_bound` API, which needs to expose the base size to claim a
bound stronger than the trivial `≤ n`.

The bijection requirement implicitly forces `n = Fintype.card
H.CFIVertex`; the existence of an `Equiv` between two finite types
implies their cardinalities match. -/
structure IsCFI' {n : Nat} (adj : AdjMatrix n) : Type where
  /-- Number of vertices in the base graph `H`. Aliased by `IsCFI'.baseSize`. -/
  m : Nat
  /-- The base graph. -/
  H : CFIBase m
  /-- Bijection from `adj`'s vertex set to the abstract `CFIVertex` type. -/
  e : Fin n ≃ H.CFIVertex
  /-- Adjacency in `adj` matches the CFI construction through `e`. -/
  matching : ∀ i j, adj.adj i j = H.cfiAdj (e i) (e j)

/-- **Base size** of a CFI witness — the number of base graph vertices.
Strictly smaller than `n` (in fact `6 * baseSize ≤ n` via
`IsCFI'.six_baseSize_le`); the depth bound API in §10 ties
`cfi_depth_bound h` to `h.baseSize`, giving a bound strictly tighter
than the trivial `n`-bound. -/
abbrev IsCFI'.baseSize {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj) : Nat := h.m

/-- **Self-witness**: every CFI base graph's `cfiAdjMatrix` satisfies
`IsCFI'`. The witness is the same bijection used to define
`cfiAdjMatrix`, so adjacency matching is `rfl`.

Now `noncomputable def` (was `theorem`) since `IsCFI'` is in `Type`
and the `Fintype.equivFin` field is noncomputable. -/
noncomputable def cfiAdjMatrix_is_cfi (H : CFIBase m) : IsCFI' H.cfiAdjMatrix where
  m := m
  H := H
  e := (Fintype.equivFin H.CFIVertex).symm
  matching := fun _ _ => rfl

-- The connector `IsCFI'.six_baseSize_le : 6 * h.baseSize ≤ n` requires
-- `CFIBase.card_CFIVertex` from §11 below; it lives in §12 to avoid a
-- forward reference.

/-- **Smoke test**: `triangleBase`'s `cfiAdjMatrix` has the
expected `AdjMatrix 18` type (via the cardinality identity for the
triangle). -/
noncomputable example : AdjMatrix (Fintype.card triangleBase.CFIVertex) :=
  triangleBase.cfiAdjMatrix

/-- The cardinality identity for `triangleBase` is `18`, matching
both `cfiVertexCount` and `Fintype.card`. (Subsumed by the general
`card_CFIVertex` proven in §11; kept here as a direct smoke test
that doesn't forward-reference.) -/
example : Fintype.card triangleBase.CFIVertex = triangleBase.cfiVertexCount := by
  rw [triangleBase_cfiVertex_card, triangleBase_cfiVertexCount]

/-- **Concrete witness**: `triangleBase.cfiAdjMatrix` satisfies `IsCFI'`. -/
noncomputable example : IsCFI' triangleBase.cfiAdjMatrix :=
  cfiAdjMatrix_is_cfi triangleBase

/-! ## §10 — Tier-1 CFI form of Theorem 1

The Tier-1 CFI specialisation of `theorem_1_HOR_at_depth`. Formerly in
[`ChainDescent.lean §17.4`](../ChainDescent.lean) using an abstract
`axiom IsCFI`; now uses the concrete `IsCFI'` `structure : Type` from
§9, with the base graph addressable as data via projections (load-
bearing for the depth-bound API).

**Axiom status (Stage 4 progress):**
- `cfi_depth_bound` — was an axiom; **discharged in M1** as
  `def cfi_depth_bound h := h.baseSize`.
- `cfi_depth_bound_le` — was an axiom; **discharged in M1** as
  `Nat.le_refl _`.
- `cfi_cascades_polynomially` — the cascade lemma proper. **The sole
  remaining Tier-1 axiom.** Discharging it is M2-M4 (multi-week):
  gadget-level distinguishability + bridge propagation + assembly.

The Tier 2 analogue (`IsSchurianSchemeGraph`,
`schurian_scheme_profile_exists`) still lives in `ChainDescent.lean
§18` and uses an abstract Prop; it'll be relocated similarly once
its concrete-scheme-based predicate is built. -/

/-- **Cascade-depth function for CFI graphs.** Concretely defined as
`h.baseSize` — the cascade depth is bounded by the number of base
graph vertices.

This is the M1 milestone of Stage 4: committing to a concrete depth
value, removing the `cfi_depth_bound` axiom. The bound is the
"one-individualization-per-gadget" depth; the classical
Cai-Fürer-Immerman bound `tw H` (≤ `baseSize`) is a sharper bound
that requires the canonical picker and is deferred to M5.

For the chain-descent polynomial-runtime corollary, any polynomial
bound suffices — `h.baseSize ≤ n / 6` (via `IsCFI'.six_baseSize_le`,
§12) is polynomial in `n`. -/
def cfi_depth_bound {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj) : Nat :=
  h.baseSize

/-- **The CFI depth bound is `≤ baseSize`.** Trivial after M1's
concretization (`cfi_depth_bound := h.baseSize`); previously an
axiom. -/
theorem cfi_depth_bound_le {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj) :
    cfi_depth_bound h ≤ h.baseSize := Nat.le_refl _

/-- **Fact A (polynomial-depth form).** A CFI graph cascades at depth
`cfi_depth_bound h`. Stated using the concrete `IsCFI'` structure;
combined with `cfi_depth_bound_le`, gives orbit recovery at depth
`≤ h.baseSize`.

Becomes a theorem once the Cai-Fürer-Immerman cascade argument is
formalised in Lean (Stage 4 of the CFI program). -/
axiom cfi_cascades_polynomially {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (P : PMatrix n) :
    CascadesAt adj P (cfi_depth_bound h)

/-- **Theorem 1 (CFI form, polynomial-depth).** A CFI graph admits
orbit recovery at depth `cfi_depth_bound h ≤ h.baseSize`. Conditional
on the Tier-1 placeholder axioms (`cfi_depth_bound`,
`cfi_depth_bound_le`, `cfi_cascades_polynomially`). The depth bound
references the witness `h` (not just `n`), so the result is strictly
tighter than the axiom-free `theorem_1_HOR_at_n`. -/
theorem theorem_1_HOR_cfi {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ cfi_depth_bound h ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w :=
  theorem_1_HOR_at_depth (cfi_cascades_polynomially h P)

/-- **Corollary (baseSize bound).** Combining `theorem_1_HOR_cfi` with
`cfi_depth_bound_le` exposes the simpler `S.card ≤ h.baseSize` claim.

The headline CFI-specific result for downstream consumers that only
need a `Nat`-shaped bound; see also `theorem_1_HOR_cfi_n_bound` below
for the further-weakened `≤ n / 6` form via §12's connector. -/
theorem theorem_1_HOR_cfi_baseSize {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ h.baseSize ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, hS, hd, hpart⟩ := theorem_1_HOR_cfi h P
  exact ⟨S, le_trans hS (cfi_depth_bound_le h), hd, hpart⟩

/-! ## §11 — Combinatorial: `Fintype.card CFIVertex = cfiVertexCount`

The vertex count formula `H.cfiVertexCount = Σ v, (2^(deg v - 1) + 2 *
deg v)` matches `Fintype.card H.CFIVertex` exactly. The proof
decomposes into:
- `Fintype.card H.CFIVertex = card H.SubsetVertex + card H.EndpointVertex`
  (since `CFIVertex = ⊕`).
- `card H.SubsetVertex = Σ v, (evenSubsetsOfNeighbors v).card`
  (Sigma + Subtype-of-Finset.mem).
- `card H.EndpointVertex = Σ v, deg v * 2` (Sigma + Subtype-of-Finset
  + Bool).
- **Key combinatorial step**: `(evenSubsetsOfNeighbors v).card =
  2^(deg v - 1)` (for `deg v ≥ 1`) — the classical identity "the
  number of even-cardinality subsets of a `d`-element set is
  `2^(d-1)`."

The classical step uses Mathlib's `Finset.sum_powerset_neg_one_pow_card_of_nonempty`
(alternating sum = 0 for nonempty sets) to conclude even-count =
odd-count, combined with even + odd = `2^d`. -/

/-- **Even-cardinality subsets of a nonempty finset count `2^(card-1)`.**

Standard combinatorial identity. Proof: alternating sum of `(-1)^|T|`
over the powerset equals zero (for nonempty s), so even-cardinality
subsets count equals odd-cardinality subsets count; combined with
total powerset count `2^|s|`, each half is `2^(|s|-1)`. -/
private theorem Finset.card_powerset_filter_even {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    (s.powerset.filter (fun T => T.card % 2 = 0)).card = 2 ^ (s.card - 1) := by
  have hpos : 1 ≤ s.card := Finset.card_pos.mpr hs
  -- A = even count, B = odd count.
  set A := (s.powerset.filter (fun T => T.card % 2 = 0)).card with hAdef
  set B := (s.powerset.filter (fun T => ¬ T.card % 2 = 0)).card with hBdef
  -- A + B = 2^s.card.
  have hAB : A + B = 2 ^ s.card := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not, Finset.card_powerset]
  -- A = B via alternating sum.
  have hAeqB : A = B := by
    -- Lift to Int: A - B = ∑ T, (-1)^T.card = 0.
    have hsum : ∑ T ∈ s.powerset, ((-1 : ℤ))^T.card = 0 :=
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
    have hsplit : ∑ T ∈ s.powerset, ((-1 : ℤ))^T.card =
        (∑ T ∈ s.powerset.filter (fun T => T.card % 2 = 0), ((-1 : ℤ))^T.card) +
        (∑ T ∈ s.powerset.filter (fun T => ¬ T.card % 2 = 0), ((-1 : ℤ))^T.card) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    -- Evaluate each piece: even part = A, odd part = -B.
    have h_even_eval :
        (∑ T ∈ s.powerset.filter (fun T => T.card % 2 = 0), ((-1 : ℤ))^T.card) = A := by
      rw [Finset.sum_congr rfl (g := fun _ => 1)]
      · simp [hAdef]
      · intro T hT
        rw [Finset.mem_filter] at hT
        exact (Nat.even_iff.mpr hT.2).neg_one_pow
    have h_odd_eval :
        (∑ T ∈ s.powerset.filter (fun T => ¬ T.card % 2 = 0), ((-1 : ℤ))^T.card) = -B := by
      rw [Finset.sum_congr rfl (g := fun _ => -1)]
      · simp [hBdef]
      · intro T hT
        rw [Finset.mem_filter] at hT
        have hmod : T.card % 2 = 1 := by
          have := Nat.mod_two_eq_zero_or_one T.card
          omega
        exact (Nat.odd_iff.mpr hmod).neg_one_pow
    -- Combine: A - B = 0 in Int.
    rw [h_even_eval, h_odd_eval] at hsplit
    have : (A : ℤ) - B = 0 := by linarith [hsplit, hsum]
    omega
  -- A + B = 2^n and A = B ⇒ 2A = 2^n ⇒ A = 2^(n-1) (since n ≥ 1).
  have h2A : 2 * A = 2 ^ s.card := by omega
  have hpow : (2 : ℕ) ^ s.card = 2 * 2 ^ (s.card - 1) := by
    conv_lhs => rw [show s.card = (s.card - 1) + 1 from by omega]
    ring
  omega

/-! ### Stepping the identity through `CFIVertex`'s structure -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-- The number of even-cardinality subsets of `H.neighbors v` is
`2^(H.degree v - 1)`. Applies `Finset.card_powerset_filter_even` to
the neighbour set, which is nonempty since `H.degree v ≥ 2`. -/
private theorem card_evenSubsetsOfNeighbors (v : Fin m) :
    (H.evenSubsetsOfNeighbors v).card = 2 ^ (H.degree v - 1) := by
  have hnonempty : (H.neighbors v).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < H.degree v
    have := H.degree_ge_two v
    omega
  exact Finset.card_powerset_filter_even hnonempty

/-- `Fintype.card SubsetVertex = ∑ v, 2^(degree v - 1)`. -/
private theorem card_SubsetVertex :
    Fintype.card H.SubsetVertex = ∑ v, 2 ^ (H.degree v - 1) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_coe]
  exact H.card_evenSubsetsOfNeighbors v

/-- `Fintype.card EndpointVertex = ∑ v, 2 * degree v`. -/
private theorem card_EndpointVertex :
    Fintype.card H.EndpointVertex = ∑ v, 2 * H.degree v := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
  show (H.neighbors v).card * 2 = 2 * H.degree v
  change H.degree v * 2 = 2 * H.degree v
  ring

/-- **The cardinality identity**: `Fintype.card CFIVertex = cfiVertexCount`.
Combines `card_SubsetVertex` and `card_EndpointVertex` via the
`CFIVertex = SubsetVertex ⊕ EndpointVertex` structure, matching the
gadget-size sum `∑ v, (2^(degree v - 1) + 2 * degree v)`. -/
theorem card_CFIVertex : Fintype.card H.CFIVertex = H.cfiVertexCount := by
  rw [Fintype.card_sum, card_SubsetVertex, card_EndpointVertex,
    ← Finset.sum_add_distrib]
  rfl

end CFIBase

/-! ## §12 — Connector: `6 * baseSize ≤ n`

The combinatorial size relation between a CFI graph's vertex count `n`
and its base graph's vertex count `h.baseSize = h.m`. Since each
gadget has at least 6 vertices (`gadgetSize_ge_six`) and there are `m`
gadgets, the CFI graph has at least `6 m` vertices.

Combined with the depth-bound axiom `cfi_depth_bound h ≤ h.baseSize`
(§10), this gives `cfi_depth_bound h ≤ n / 6`. So
`theorem_1_HOR_cfi_n_bound` (below) yields a strictly tighter
specialisation than `theorem_1_HOR_at_n`: orbit recovery on a CFI
graph happens at depth `≤ n / 6`, not just `≤ n`. The CFI-specific
axioms now carry meaningful content. -/

/-- **Connector**: a CFI graph has at least `6 * baseSize` vertices.

Proof: `n = Fintype.card H.CFIVertex = H.cfiVertexCount =
∑ v, gadgetSize v ≥ ∑ v, 6 = 6 * m`. The first equality uses the
bijection `h.e`; the second is `card_CFIVertex` (§11); the
inequality is `gadgetSize_ge_six` summed. -/
theorem IsCFI'.six_baseSize_le {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) : 6 * h.baseSize ≤ n := by
  -- Get h.H.cfiVertexCount = n via the bijection + card_CFIVertex.
  have h_card : h.H.cfiVertexCount = n := by
    have hc : Fintype.card (Fin n) = Fintype.card h.H.CFIVertex :=
      Fintype.card_congr h.e
    rw [Fintype.card_fin, h.H.card_CFIVertex] at hc
    exact hc.symm
  -- Show 6 * h.m ≤ h.H.cfiVertexCount, then chain through h_card.
  have hsum : 6 * h.m ≤ h.H.cfiVertexCount := by
    unfold CFIBase.cfiVertexCount
    -- Sum of constants: ∑ _v : Fin m, 6 = 6 * m, via Finset.sum_const_nat.
    have hconst : (∑ _v ∈ (Finset.univ : Finset (Fin h.m)), (6 : Nat)) = 6 * h.m := by
      have hsc : (∑ _v ∈ (Finset.univ : Finset (Fin h.m)), (6 : Nat))
          = (Finset.univ : Finset (Fin h.m)).card * 6 :=
        Finset.sum_const_nat (fun _ _ => rfl)
      rw [hsc, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
    calc 6 * h.m
        = ∑ _v ∈ (Finset.univ : Finset (Fin h.m)), (6 : Nat) := hconst.symm
      _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin h.m)), h.H.gadgetSize v :=
          Finset.sum_le_sum (fun v _ => h.H.gadgetSize_ge_six v)
  -- Chain: 6 * h.baseSize = 6 * h.m ≤ h.H.cfiVertexCount = n.
  exact hsum.trans h_card.le

/-- **Corollary (n-shaped bound).** Orbit recovery on a CFI graph holds
at depth `≤ n / 6` — strictly tighter than the trivial `≤ n` bound
provided axiom-free by `theorem_1_HOR_at_n`.

This is the CFI-specific content: even before discharging Stage 4
(the cascade lemma), the two CFI-specific axioms already buy us a
factor-of-6 improvement on the depth bound, just from gadget size
geometry. Once Stage 4 lands and `cfi_depth_bound h` is realised as
`tw h.H`, the bound tightens further (treewidth is typically much
smaller than `m / 6 = n / 36`). -/
theorem theorem_1_HOR_cfi_n_bound {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      6 * S.card ≤ n ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, hS, hd, hpart⟩ := theorem_1_HOR_cfi_baseSize h P
  refine ⟨S, ?_, hd, hpart⟩
  calc 6 * S.card ≤ 6 * h.baseSize := by exact Nat.mul_le_mul_left 6 hS
    _ ≤ n := h.six_baseSize_le

/-! ## §13 — M2: gadget-level distinguishability lemmas

First set of cascade lemmas — how a single individualized subset
vertex `a_∅^v` propagates to distinguish endpoints in its gadget.

§13.1 — Named CFI vertex constructors (`aEmpty`, `endpoint`).
§13.2 — Direct adjacency computations involving these.
§13.3 — General signature lemma about colour-singleton vertices.
§13.4 — **M2.1**: the headline cascade lemma — `a_∅^v` singleton
        implies endpoints at any `(v,w)` split after one refineStep. -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-! ### §13.1 — Named CFI vertex constructors -/

/-- The CFI vertex `a_∅^v`: the subset vertex at gadget `v` with empty
subset. Always inhabits `evenSubsetsOfNeighbors v` since `|∅| = 0` is
even. The "canonical seed" vertex used in the M2-M4 cascade
construction. -/
def aEmpty (v : Fin m) : H.CFIVertex :=
  Sum.inl ⟨v, ⟨∅, H.empty_mem_evenSubsetsOfNeighbors v⟩⟩

/-- The CFI vertex `e^b_{v→w}`: the endpoint at gadget `v` pointing
toward neighbour `w ∈ N(v)` with parity bit `b ∈ {false, true}`. -/
def endpoint {v w : Fin m} (hw : w ∈ H.neighbors v) (b : Bool) : H.CFIVertex :=
  Sum.inr ⟨v, ⟨w, hw⟩, b⟩

/-! ### §13.2 — Adjacency facts for named vertices

`a_∅^v` connects to an endpoint `e^b_{v→w}` iff `(w ∈ ∅) ⊕ b = b`,
i.e. iff `b = true`. So `cfiAdj a_∅^v e^false = 0` and
`cfiAdj a_∅^v e^true = 1` — the parity bit `b` is exactly the
adjacency. -/

/-- `cfiAdj (a_∅^v) (e^0_{v→w}) = 0` — the b=0 endpoint is NOT
adjacent to the empty-subset seed. -/
theorem cfiAdj_aEmpty_endpoint_false {v w : Fin m} (hw : w ∈ H.neighbors v) :
    H.cfiAdj (H.aEmpty v) (H.endpoint hw false) = 0 := by
  show (if v = v ∧ decide (w ∈ (∅ : Finset (Fin m))) ≠ false then 1 else 0) = 0
  simp [Finset.notMem_empty]

/-- `cfiAdj (a_∅^v) (e^1_{v→w}) = 1` — the b=1 endpoint IS adjacent
to the empty-subset seed. -/
theorem cfiAdj_aEmpty_endpoint_true {v w : Fin m} (hw : w ∈ H.neighbors v) :
    H.cfiAdj (H.aEmpty v) (H.endpoint hw true) = 1 := by
  show (if v = v ∧ decide (w ∈ (∅ : Finset (Fin m))) ≠ true then 1 else 0) = 1
  simp [Finset.notMem_empty]

/-- `aEmpty v` and `endpoint hw b` are distinct CFI vertices (one is
`Sum.inl`, the other `Sum.inr`). -/
theorem aEmpty_ne_endpoint {v w : Fin m} (hw : w ∈ H.neighbors v) (b : Bool) :
    H.aEmpty v ≠ H.endpoint hw b := by
  intro heq
  unfold aEmpty endpoint at heq
  -- heq : Sum.inl _ = Sum.inr _ ; injection closes via case mismatch.
  injection heq

/-- **Cross-gadget non-adjacency.** `aEmpty v` is not adjacent to
`endpoint hw b` when v ≠ v' (different gadgets): subset-endpoint pairs
in CFI graphs are adjacent only within the same gadget.

The within-gadget case is covered by `cfiAdj_aEmpty_endpoint_false`
(adj=0 for b=false) and `cfiAdj_aEmpty_endpoint_true` (adj=1 for
b=true). This lemma handles the cross-gadget case (adj=0 always). -/
theorem cfiAdj_aEmpty_endpoint_diff_gadget {v v' w : Fin m}
    (hw : w ∈ H.neighbors v') (b : Bool) (hvv : v ≠ v') :
    H.cfiAdj (H.aEmpty v) (H.endpoint hw b) = 0 := by
  show (if v = v' ∧ decide (w ∈ (∅ : Finset (Fin m))) ≠ b then 1 else 0) = 0
  rw [if_neg]
  rintro ⟨h_eq, _⟩
  exact hvv h_eq

/-- **The bridge edge.** The CFI graph's inter-gadget connections are
"bridges" between `e^b_{v→w}` and `e^b_{w→v}` — endpoint vertices at
gadgets `v` and `w` (with `w ∈ N(v)`) pointing toward each other,
both with the same parity bit. This lemma evaluates `cfiAdj` on a
bridge pair, giving `1`.

The companion `cfiAdj` clauses for endpoint-endpoint pairs:
- Within the same gadget: never adjacent (handled by `cfiAdj_loopless`-
  style reasoning — the bridge condition requires `v₁ = w_pair₂.val`,
  but within-gadget means `v₁ = v₂`, and `v₂` is a base vertex while
  `w_pair₂.val` is a *neighbour*, forcing `v₁ = w_pair₂.val` to
  conflict with `v₁ ∉ N(v₁)`).
- Different gadgets, non-bridge: adj=0 (bridge condition fails). -/
theorem cfiAdj_bridge {v w : Fin m} (hw : w ∈ H.neighbors v) (b : Bool) :
    H.cfiAdj (H.endpoint hw b) (H.endpoint (H.mem_neighbors_symm.mp hw) b) = 1 := by
  show (if v = v ∧ w = w ∧ b = b then 1 else 0) = 1
  simp

end CFIBase

/-! ### §13.3 — Fin-n level extractors via the `IsCFI'` bijection

Lift the abstract `H.CFIVertex` constructors `aEmpty` / `endpoint` to
the `Fin n` index space using the `h.e : Fin n ≃ H.CFIVertex`
bijection (and its inverse `h.e.symm`).

These extractors are the "named" `Fin n` vertices the M2-M4 cascade
construction individualizes (the seed) or probes (the endpoints). -/

/-- The `Fin n` vertex corresponding to `a_∅^v` (the canonical seed at
base vertex `v`) in `h : IsCFI' adj`. -/
def IsCFI'.seedVertex {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj)
    (v : Fin h.m) : Fin n :=
  h.e.symm (h.H.aEmpty v)

/-- The `Fin n` vertex corresponding to `e^b_{v→w}` (the parity-`b`
endpoint at gadget `v` pointing toward `w ∈ N(v)`) in `h : IsCFI' adj`. -/
def IsCFI'.endpointVertex {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) (b : Bool) : Fin n :=
  h.e.symm (h.H.endpoint hw b)

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- `h.e (h.seedVertex v) = h.H.aEmpty v`. The bijection round-trip. -/
@[simp] theorem e_seedVertex (h : IsCFI' adj) (v : Fin h.m) :
    h.e (h.seedVertex v) = h.H.aEmpty v := by
  unfold seedVertex
  exact Equiv.apply_symm_apply _ _

/-- `h.e (h.endpointVertex hw b) = h.H.endpoint hw b`. -/
@[simp] theorem e_endpointVertex (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) :
    h.e (h.endpointVertex hw b) = h.H.endpoint hw b := by
  unfold endpointVertex
  exact Equiv.apply_symm_apply _ _

/-- Seed vertices and endpoint vertices are distinct in `Fin n` (since
their abstract counterparts have different `Sum` tags). -/
theorem seedVertex_ne_endpointVertex (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) :
    h.seedVertex v ≠ h.endpointVertex hw b := by
  intro heq
  apply h.H.aEmpty_ne_endpoint hw b
  -- Apply h.e to both sides, simplify via the bijection round-trip.
  have hcong := congrArg h.e heq
  rw [e_seedVertex, e_endpointVertex] at hcong
  exact hcong

end IsCFI'

/-! ### §13.4 — Adjacency facts at the `Fin n` level via `h.matching`

The CFI graph's adjacency matrix `adj`, evaluated on the named
extractors `seedVertex` / `endpointVertex`, reduces to the abstract
`cfiAdj` evaluation lemmas of §13.2 through the bijection `h.e` and
the matching identity `adj.adj i j = cfiAdj (h.e i) (h.e j)`. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- `adj (seedVertex v) (endpointVertex v w false) = 0` — the b=0
endpoint is NOT adjacent to the seed. -/
theorem adj_seed_endpoint_false (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) :
    adj.adj (h.seedVertex v) (h.endpointVertex hw false) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  exact h.H.cfiAdj_aEmpty_endpoint_false hw

/-- `adj (seedVertex v) (endpointVertex v w true) = 1` — the b=1
endpoint IS adjacent to the seed. -/
theorem adj_seed_endpoint_true (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) :
    adj.adj (h.seedVertex v) (h.endpointVertex hw true) = 1 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  exact h.H.cfiAdj_aEmpty_endpoint_true hw

/-- Symmetric form: `adj (endpointVertex v w false) (seedVertex v) = 0`. -/
theorem adj_endpoint_seed_false (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) :
    adj.adj (h.endpointVertex hw false) (h.seedVertex v) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  rw [h.H.cfiAdj_symm]
  exact h.H.cfiAdj_aEmpty_endpoint_false hw

/-- Symmetric form: `adj (endpointVertex v w true) (seedVertex v) = 1`. -/
theorem adj_endpoint_seed_true (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) :
    adj.adj (h.endpointVertex hw true) (h.seedVertex v) = 1 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  rw [h.H.cfiAdj_symm]
  exact h.H.cfiAdj_aEmpty_endpoint_true hw

/-- **Cross-gadget**: `adj (seedVertex v) (endpointVertex v' w b) = 0`
when v ≠ v'. Seeds and endpoints in different gadgets are never
adjacent. -/
private theorem adj_seed_endpoint_diff_gadget (h : IsCFI' adj)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v') (b : Bool) :
    adj.adj (h.seedVertex v) (h.endpointVertex hw b) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  exact h.H.cfiAdj_aEmpty_endpoint_diff_gadget hw b hvv

/-- Symmetric: `adj (endpointVertex v' w b) (seedVertex v) = 0` when
v ≠ v'. -/
private theorem adj_endpoint_seed_diff_gadget (h : IsCFI' adj)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v') (b : Bool) :
    adj.adj (h.endpointVertex hw b) (h.seedVertex v) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex, h.H.cfiAdj_symm]
  exact h.H.cfiAdj_aEmpty_endpoint_diff_gadget hw b hvv

/-- **Bridge adjacency (Fin n)**: the endpoint `e^b_{v→w}` is adjacent
to its bridge partner `e^b_{w→v}`. Lifts `CFIBase.cfiAdj_bridge`
through `h.matching`. -/
private theorem adj_bridge (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) :
    adj.adj (h.endpointVertex hw b)
            (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b) = 1 := by
  rw [h.matching, e_endpointVertex, e_endpointVertex]
  exact h.H.cfiAdj_bridge hw b

/-- **Endpoint distinct from its bridge partner.** The endpoint at
gadget `v` and the endpoint at gadget `w` (its bridge partner) are
distinct `Fin n` vertices, because `v ≠ w` follows from `w ∈ N(v)` +
looplessness. -/
private theorem endpointVertex_ne_bridge (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) :
    h.endpointVertex hw b ≠
    h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b := by
  intro heq
  -- (1) v ≠ w via loopless (w ∈ N(v) ⟹ w ≠ v).
  have hvw : v ≠ w := by
    intro hvw_eq
    rw [hvw_eq] at hw
    exact h.H.not_self_mem_neighbors w hw
  -- (2) Lift equality up to the abstract CFIVertex level via h.e.
  have habs : h.H.endpoint hw b =
              h.H.endpoint (h.H.mem_neighbors_symm.mp hw) b := by
    have := congrArg h.e heq
    rwa [e_endpointVertex, e_endpointVertex] at this
  -- (3) Extract v = w from the Sigma first component — contradiction.
  unfold CFIBase.endpoint at habs
  injection habs with hSig
  exact hvw (congrArg Sigma.fst hSig)

end IsCFI'

/-! ### §13.5 — Singleton individualization lemmas

General facts about `individualizedColouring n {seed}` — the
colouring produced by individualizing a single vertex. The seed gets
a positive fresh colour `seed.val + 1`; every other vertex gets `0`.

These are graph-agnostic facts; placed here because M2's signature
distinction is the first proof that needs them. -/

/-- `individualizedColouring n {seed} seed = seed.val + 1`. -/
@[simp] theorem individualizedColouring_singleton_self {n : Nat} (seed : Fin n) :
    individualizedColouring n {seed} seed = seed.val + 1 := by
  simp [individualizedColouring]

/-- For `u ≠ seed`, `individualizedColouring n {seed} u = 0`. -/
@[simp] theorem individualizedColouring_singleton_other {n : Nat}
    {seed u : Fin n} (h : u ≠ seed) :
    individualizedColouring n {seed} u = 0 := by
  simp [individualizedColouring, h]

/-- The seed's colour is positive (i.e. nonzero). -/
private theorem individualizedColouring_singleton_self_pos {n : Nat} (seed : Fin n) :
    individualizedColouring n {seed} seed ≠ 0 := by
  rw [individualizedColouring_singleton_self]
  exact Nat.succ_ne_zero _

/-- **Uniqueness**: `individualizedColouring n {seed} u = individualizedColouring n {seed} seed`
iff `u = seed`. The forward direction is the key fact powering M2's
signature distinction — only the seed has the fresh colour. -/
private theorem individualizedColouring_singleton_eq_seed_iff {n : Nat}
    {seed u : Fin n} :
    individualizedColouring n {seed} u =
      individualizedColouring n {seed} seed ↔ u = seed := by
  constructor
  · intro hχ
    by_contra hne
    rw [individualizedColouring_singleton_self,
      individualizedColouring_singleton_other hne] at hχ
    exact Nat.succ_ne_zero _ hχ.symm
  · rintro rfl; rfl

/-! ### §13.6 — M2.4: signature distinction

The key cascade lemma: under the individualized colouring of the seed
`{h.seedVertex v}`, the multiset signatures of the b=0 and b=1
endpoints at gadget `v` toward neighbour `w` differ.

Witness tuple `t = (χ seed, 1, P endpoint_true seed)`:
- t ∈ signature endpoint_true: contributed by u = seed (since seed is
  the unique fresh-coloured vertex, adjacent to endpoint_true).
- t ∉ signature endpoint_false: any u with χ u = χ seed must be seed,
  but seed is NOT adjacent to endpoint_false, so the adjacency
  component fails. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M2.4 — Signature distinction.** The signatures of the b=0 and
b=1 endpoints at gadget `v` (toward `w ∈ N(v)`) differ under the
individualized colouring of the seed vertex `h.seedVertex v`. -/
private theorem signature_endpoint_false_ne_true (h : IsCFI' adj) (P : PMatrix n)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) :
    signature adj P (individualizedColouring n {h.seedVertex v})
        (h.endpointVertex hw false) ≠
    signature adj P (individualizedColouring n {h.seedVertex v})
        (h.endpointVertex hw true) := by
  intro hsig
  set seed := h.seedVertex v
  set ef := h.endpointVertex hw false
  set et := h.endpointVertex hw true
  set χ := individualizedColouring n {seed}
  -- Witness tuple in the b=1 endpoint's signature.
  let t : Nat × Nat × POE := (χ seed, 1, P et seed)
  -- (a) t ∈ signature et — contributed by u = seed.
  have ht_in_et : t ∈ signature adj P χ et := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨seed, ?_, ?_⟩
    · -- seed ∈ (univ.filter (· ≠ et)).val
      rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.seedVertex_ne_endpointVertex hw true⟩
    · -- (χ seed, adj.adj et seed, P et seed) = (χ seed, 1, P et seed)
      show (χ seed, adj.adj et seed, P et seed) = t
      rw [h.adj_endpoint_seed_true hw]
  -- (b) t ∉ signature ef — no vertex u satisfies both colour and adjacency.
  have ht_notin_ef : t ∉ signature adj P χ ef := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, hu_mem, hu_eq⟩
    -- hu_eq : (χ u, adj.adj ef u, P ef u) = (χ seed, 1, P et seed)
    -- Split into components via `congrArg Prod.fst / Prod.snd`.
    have hχu : χ u = χ seed := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ef u, P ef u) = ((1, P et seed) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ef u = 1 := congrArg Prod.fst hrest
    -- From χ u = χ seed: u = seed (only seed has the fresh colour).
    have hu_seed : u = seed := individualizedColouring_singleton_eq_seed_iff.mp hχu
    -- Substituting u = seed: adj.adj ef seed should be 1, but it's 0.
    rw [hu_seed] at hadj
    rw [h.adj_endpoint_seed_false hw] at hadj
    exact absurd hadj (by decide)
  -- The same multiset can't both contain and not contain t.
  rw [hsig] at ht_notin_ef
  exact ht_notin_ef ht_in_et

/-! ### §13.7 — M2.5: refineStep distinguishes endpoints (M2 headline)

Lift the signature distinction (M2.4) to a refineStep distinction via
`refineStep_iff`: equal `refineStep` outputs would require equal
signatures, which M2.4 rules out. -/

/-- **M2.5 — Endpoint split (M2 headline).** After **one** round of
`refineStep` on the colouring `individualizedColouring n {seedVertex v}`,
the b=0 and b=1 endpoints at gadget `v` toward `w ∈ N(v)` have distinct
colours.

This is the foundational M2 cascade lemma: individualizing one seed
per gadget makes 1-WL distinguish v's endpoints by parity in a single
round. -/
private theorem refineStep_endpoint_false_ne_true (h : IsCFI' adj) (P : PMatrix n)
    {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) :
    refineStep adj P (individualizedColouring n {h.seedVertex v})
        (h.endpointVertex hw false) ≠
    refineStep adj P (individualizedColouring n {h.seedVertex v})
        (h.endpointVertex hw true) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_endpoint_false_ne_true P hw hboth.2

end IsCFI'

/-! ### §13.8 — M3.A: multi-seed cascade setup

The cascade individualization is `allSeeds = {h.seedVertex v : v ∈ Fin h.m}`
— one seed per base graph vertex. This section defines `allSeeds` and
proves the foundational structural facts:

- `seedVertex` is injective (different bases give different Fin n indices).
- `|allSeeds| = h.baseSize` (= h.m). Combined with `h.six_baseSize_le`,
  the cascade individualization has size ≤ n / 6.
- Multi-seed individualizedColouring uniqueness: for `v ∈ S`,
  `χ_S u = χ_S v ↔ u = v`. The generalisation of §13.5's singleton
  uniqueness; the engine for the M2 → multi-seed lift in §13.9. -/

/-- **Multi-seed uniqueness**: under `individualizedColouring n S`, if
`v ∈ S` and `u` has the same colour as `v`, then `u = v`. (Members of
`S` get distinct fresh colours `u.val + 1`; non-members get `0`.)

Generalises §13.5's `individualizedColouring_singleton_eq_seed_iff`
from `S = {v}` to arbitrary `S` containing `v`. -/
theorem individualizedColouring_eq_iff_of_mem {n : Nat} (S : Finset (Fin n))
    {v u : Fin n} (hv : v ∈ S) :
    individualizedColouring n S u = individualizedColouring n S v ↔ u = v := by
  constructor
  · intro hχ
    by_cases hu : u ∈ S
    · simp only [individualizedColouring, if_pos hu, if_pos hv] at hχ
      exact Fin.eq_of_val_eq (by omega)
    · simp only [individualizedColouring, if_neg hu, if_pos hv] at hχ
      exact absurd hχ (by omega)
  · rintro rfl; rfl

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- The cascade individualization set: `{h.seedVertex v : v ∈ Fin h.m}`,
i.e. one seed per base graph vertex.

Used as the witness in `cfi_cascades_polynomially`: this is `S` in
"there exists `S` of size ≤ `cfi_depth_bound h` such that
`warmRefine adj P χ_S` is `Discrete`." -/
def allSeeds (h : IsCFI' adj) : Finset (Fin n) :=
  Finset.univ.image h.seedVertex

/-- `seedVertex` is injective: different base vertices map to different
`Fin n` indices.

Proof: `aEmpty v` has its base index `v` recoverable from the `Sigma`
first component, so `aEmpty` is injective on `v`. Combined with
`h.e.symm` (an `Equiv`) being injective, `seedVertex v := h.e.symm (aEmpty v)`
is injective in `v`. -/
theorem seedVertex_injective (h : IsCFI' adj) :
    Function.Injective h.seedVertex := by
  intro v v' hvv
  -- Apply h.e to both sides; the bijection round-trip exposes h.H.aEmpty equality.
  have habs : h.H.aEmpty v = h.H.aEmpty v' := by
    have := congrArg h.e hvv
    rwa [e_seedVertex, e_seedVertex] at this
  unfold CFIBase.aEmpty at habs
  -- Sum.inl ⟨v, _⟩ = Sum.inl ⟨v', _⟩ → Sigma equality.
  injection habs with hSig
  -- Sigma first component projection.
  exact congrArg Sigma.fst hSig

/-- `seedVertex v ∈ h.allSeeds` for every base vertex `v`. -/
theorem seedVertex_mem_allSeeds (h : IsCFI' adj) (v : Fin h.m) :
    h.seedVertex v ∈ h.allSeeds :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

/-- `|allSeeds| = h.baseSize`. Combined with `h.six_baseSize_le`,
the cascade individualization has at most `n / 6` vertices. -/
@[simp] theorem allSeeds_card (h : IsCFI' adj) :
    h.allSeeds.card = h.baseSize := by
  unfold allSeeds
  rw [Finset.card_image_of_injective Finset.univ h.seedVertex_injective,
    Finset.card_univ, Fintype.card_fin]

/-- `|allSeeds| ≤ h.baseSize`. Convenience form for downstream use. -/
private theorem allSeeds_card_le_baseSize (h : IsCFI' adj) :
    h.allSeeds.card ≤ h.baseSize :=
  le_of_eq h.allSeeds_card

end IsCFI'

/-! ### §13.9 — M3.B: M2 endpoint split, lifted to multi-seed `χ_{allSeeds}`

The cascade construction in M4 individualizes ALL seeds simultaneously,
not just one. The M2 endpoint split (`signature_endpoint_false_ne_true`
/ `refineStep_endpoint_false_ne_true`) generalizes verbatim: the same
signature-distinction argument works under `χ_{allSeeds}`, with the
multi-seed uniqueness lemma (`individualizedColouring_eq_iff_of_mem`)
replacing the singleton form.

These are the M2 lemmas as they will actually be used by M4. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M3.B / signature** — multi-seed analogue of M2.4. Under
`χ_{allSeeds}`, the b=0 and b=1 endpoints at gadget `v` toward
`w ∈ N(v)` have different signature multisets.

Witness tuple: `(χ seed_v, 1, P endpoint_true seed_v)`. Same argument
as M2.4, with `individualizedColouring_eq_iff_of_mem` providing
uniqueness from `seed_v ∈ allSeeds`. -/
private theorem signature_endpoint_false_ne_true_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) :
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw false) ≠
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hsig
  set seed := h.seedVertex v
  set ef := h.endpointVertex hw false
  set et := h.endpointVertex hw true
  set χ := individualizedColouring n h.allSeeds
  have hseed_mem : seed ∈ h.allSeeds := h.seedVertex_mem_allSeeds v
  -- Witness tuple in the b=1 endpoint's signature.
  let t : Nat × Nat × POE := (χ seed, 1, P et seed)
  -- (a) t ∈ signature et — contributed by u = seed.
  have ht_in_et : t ∈ signature adj P χ et := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨seed, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.seedVertex_ne_endpointVertex hw true⟩
    · show (χ seed, adj.adj et seed, P et seed) = t
      rw [h.adj_endpoint_seed_true hw]
  -- (b) t ∉ signature ef — no u satisfies both colour and adjacency.
  have ht_notin_ef : t ∉ signature adj P χ ef := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    -- Decompose hu_eq via Prod.fst/Prod.snd.
    have hχu : χ u = χ seed := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ef u, P ef u) = ((1, P et seed) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ef u = 1 := congrArg Prod.fst hrest
    -- Multi-seed uniqueness: χ u = χ seed → u = seed.
    have hu_seed : u = seed :=
      (individualizedColouring_eq_iff_of_mem h.allSeeds hseed_mem).mp hχu
    -- But adj.adj ef seed = 0, not 1.
    rw [hu_seed, h.adj_endpoint_seed_false hw] at hadj
    exact absurd hadj (by decide)
  -- Contradiction: t ∈ signature et = signature ef but t ∉ signature ef.
  rw [hsig] at ht_notin_ef
  exact ht_notin_ef ht_in_et

/-- **M3.B / refineStep (M3 first headline)** — multi-seed analogue of
M2.5. Under `χ_{allSeeds}`, one `refineStep` round gives the b=0 and
b=1 endpoints at gadget `v` (toward `w ∈ N(v)`) distinct colours.

The natural cascade-context generalisation of M2: the same parity-split
holds under the actual M4 individualization (all seeds). -/
private theorem refineStep_endpoint_false_ne_true_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v w : Fin h.m} (hw : w ∈ h.H.neighbors v) :
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw false) ≠
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_endpoint_false_ne_true_allSeeds P hw hboth.2

end IsCFI'

/-! ### §13.10 — M3.C: b=true endpoint inter-gadget distinction

The first **inter-gadget** cascade lemma. Under `χ_{allSeeds}`, one
`refineStep` round distinguishes b=true endpoints at different
gadgets:

  `refineStep χ (e^1_{v→w}) ≠ refineStep χ (e^1_{v'→w'})` for v ≠ v'.

Witness argument (analogous to M3.B): the tuple `(c_v, 1, ?)` (where
c_v is seed_v's fresh colour) is in `e^1_{v→w}`'s signature (via
adjacency to seed_v in the same gadget) but not in `e^1_{v'→w'}`'s
signature (seed_v is in a different gadget, hence not adjacent to
`e^1_{v'→w'}`; and multi-seed uniqueness forces c_v's witness u to be
seed_v).

**Note**: The corresponding b=false case (`e^0_{v→w}` vs `e^0_{v'→w'}`
across gadgets) is **NOT** distinguishable at round 1 — neither
endpoint is adjacent to seed_v, so the (c_v, _, _) tuples coincide.
b=false inter-gadget distinction requires multi-round bridge
propagation (deferred to M3.D-multi-round + M4). -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M3.C / signature** — inter-gadget signature distinction for b=true
endpoints. Same witness tuple `(c_v, 1, ?)` as M3.B; the only difference
is that the "absence" argument uses cross-gadget non-adjacency
(`adj_endpoint_seed_diff_gadget`) rather than within-gadget
parity-mismatch (`adj_endpoint_seed_false`). -/
private theorem signature_endpoint_true_inter_gadget (h : IsCFI' adj) (P : PMatrix n)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v') :
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) ≠
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw' true) := by
  intro hsig
  set seed_v := h.seedVertex v
  set ev := h.endpointVertex hw true
  set ev' := h.endpointVertex hw' true
  set χ := individualizedColouring n h.allSeeds
  have hseed_mem : seed_v ∈ h.allSeeds := h.seedVertex_mem_allSeeds v
  let t : Nat × Nat × POE := (χ seed_v, 1, P ev seed_v)
  -- (a) t ∈ signature ev — contributed by u = seed_v in v's own gadget.
  have ht_in_ev : t ∈ signature adj P χ ev := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨seed_v, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.seedVertex_ne_endpointVertex hw true⟩
    · show (χ seed_v, adj.adj ev seed_v, P ev seed_v) = t
      rw [h.adj_endpoint_seed_true hw]
  -- (b) t ∉ signature ev' — at gadget v' ≠ v, the seed_v is in a different gadget.
  have ht_notin_ev' : t ∉ signature adj P χ ev' := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ u = χ seed_v := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ev' u, P ev' u) = ((1, P ev seed_v) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ev' u = 1 := congrArg Prod.fst hrest
    have hu_seed : u = seed_v :=
      (individualizedColouring_eq_iff_of_mem h.allSeeds hseed_mem).mp hχu
    -- ev' is at gadget v', seed_v at gadget v ≠ v' — not adjacent.
    rw [hu_seed, h.adj_endpoint_seed_diff_gadget hvv hw' true] at hadj
    exact absurd hadj (by decide)
  -- ht_notin_ev' : t ∉ signature ev'; ht_in_ev : t ∈ signature ev = signature ev' (via hsig).
  rw [← hsig] at ht_notin_ev'
  exact ht_notin_ev' ht_in_ev

/-- **M3.C / refineStep (M3 second headline)** — under `χ_{allSeeds}`,
one `refineStep` round gives b=true endpoints at different gadgets
distinct colours.

Combined with M3.B (same-gadget parity split), we have: at round 1,
b=true endpoints split by `v` (gadget); b=0 vs b=1 split within each
gadget. Remaining cases (b=0 inter-gadget, within-gadget by `w`,
subset vertex distinction) require multi-round bridge propagation. -/
private theorem refineStep_endpoint_true_inter_gadget (h : IsCFI' adj)
    (P : PMatrix n) {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v') :
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) ≠
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw' true) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_endpoint_true_inter_gadget P hvv hw hw' hboth.2

end IsCFI'

/-! ### §13.11 — M3.D Phase 1: local bridge propagation step lemma

The **inductive engine** for the cascade: given an arbitrary colouring
`χ`, if the bridge partners of two endpoints have distinct colours
under `χ` AND that distinction colour doesn't accidentally appear at
another adj=1 neighbour, then one `refineStep` distinguishes the
endpoints themselves.

This is the local step. Iterating it (Phase 2, deferred) propagates
distinction along bridges to cover the b=0 inter-gadget case and the
within-gadget by-partner case. Phase 2 must establish the
"no-match" precondition at each round, typically by maintaining a
uniqueness invariant on the iterated colouring.

The proof shape is identical to M2/M3.B/M3.C — signature-distinction
via a witness tuple — with the witness coming from the bridge partner
rather than an own-gadget seed. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M3.D / signature — bridge propagation at the signature level.**
Generalises the M2/M3.B/M3.C signature-distinction pattern to an
arbitrary colouring `χ` and uses a bridge partner as the witness.

Preconditions:
- `hbridge`: bridge partners distinguished by χ.
- `hno_match`: the bridge partner's colour does not appear at any
  `adj=1` neighbour of `ev'` (the second endpoint).

Conclusion: the signature multisets of the two endpoints under χ
differ. -/
private theorem signature_bridge_step (h : IsCFI' adj) (P : PMatrix n)
    (χ : Colouring n) {v w v' w' : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (hw' : w' ∈ h.H.neighbors v') (b : Bool)
    (hbridge : χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b) ≠
               χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw') b))
    (hno_match : ∀ u, adj.adj (h.endpointVertex hw' b) u = 1 →
                   χ u ≠ χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b)) :
    signature adj P χ (h.endpointVertex hw b) ≠
    signature adj P χ (h.endpointVertex hw' b) := by
  -- Note `hbridge` is consumed by the disequality conclusion, not directly used in
  -- the signature argument. It's present to document the intent: the lemma is
  -- vacuous otherwise (if partners share a colour, `hno_match` can fail).
  let _ := hbridge
  intro hsig
  set bp  := h.endpointVertex (h.H.mem_neighbors_symm.mp hw)  b with hbp
  set bp' := h.endpointVertex (h.H.mem_neighbors_symm.mp hw') b with hbp'
  set ev  := h.endpointVertex hw  b with hev
  set ev' := h.endpointVertex hw' b with hev'
  -- Witness tuple: (χ bp, 1, P ev bp).
  let t : Nat × Nat × POE := (χ bp, 1, P ev bp)
  -- (a) t ∈ signature ev — contributed by u = bp (adj ev bp = 1 from bridge).
  have ht_in_ev : t ∈ signature adj P χ ev := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨bp, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (h.endpointVertex_ne_bridge hw b).symm⟩
    · show (χ bp, adj.adj ev bp, P ev bp) = t
      rw [h.adj_bridge hw b]
  -- (b) t ∉ signature ev' — by hno_match.
  have ht_notin_ev' : t ∉ signature adj P χ ev' := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ u = χ bp := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ev' u, P ev' u) = ((1, P ev bp) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ev' u = 1 := congrArg Prod.fst hrest
    exact (hno_match u hadj) hχu
  rw [hsig] at ht_in_ev
  exact ht_notin_ev' ht_in_ev

/-- **M3.D / refineStep — Phase 1 headline.** Given a colouring χ
where bridge partners are distinguished and the bridge-partner colour
is "unique within adj=1 reach" of the second endpoint, `refineStep`
distinguishes the original endpoint pair.

This is the local step lemma that, iterated through the cascade
(Phase 2, deferred), propagates distinction along bridges.

**Symmetry note**: The hypotheses are asymmetric — they only require
uniqueness at `ev'`, not `ev`. This is intentional: the proof finds a
witness tuple in `ev`'s signature and absent from `ev'`'s. The
symmetric version (uniqueness at `ev` instead) follows by swapping
arguments. -/
private theorem refineStep_bridge_step (h : IsCFI' adj) (P : PMatrix n)
    (χ : Colouring n) {v w v' w' : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (hw' : w' ∈ h.H.neighbors v') (b : Bool)
    (hbridge : χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b) ≠
               χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw') b))
    (hno_match : ∀ u, adj.adj (h.endpointVertex hw' b) u = 1 →
                   χ u ≠ χ (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b)) :
    refineStep adj P χ (h.endpointVertex hw b) ≠
    refineStep adj P χ (h.endpointVertex hw' b) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_bridge_step P χ hw hw' b hbridge hno_match hboth.2

end IsCFI'

/-! ### §13.12 — M3.D Phase 2.0: structural adjacency characterisations

Helper lemmas characterising when two specific CFI vertex types are
adjacent in `adj`. These are the "structural CFI facts" that drive
Phase 2's verification of the bridge-step lemma's (P2) precondition. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Endpoint-endpoint adjacency formula.** Two endpoints in `adj` are
adjacent iff they form a bridge pair: `v_a = w_b ∧ w_a = v_b ∧ b_a = b_b`.

This is `cfiAdj`'s endpoint-endpoint clause, lifted to Fin n via
`h.matching`. The within-gadget case (`v_a = v_b`) fails because
`w_a ∈ N(v_a)` and `v_a ∉ N(v_a)` (loopless), so `v_a = w_b ∧ w_a = v_b`
would force a self-loop. -/
theorem adj_endpointVertex_eq_one_iff (h : IsCFI' adj)
    {v_a w_a v_b w_b : Fin h.m}
    (hwa : w_a ∈ h.H.neighbors v_a) (hwb : w_b ∈ h.H.neighbors v_b)
    (b_a b_b : Bool) :
    adj.adj (h.endpointVertex hwa b_a) (h.endpointVertex hwb b_b) = 1 ↔
    v_a = w_b ∧ w_a = v_b ∧ b_a = b_b := by
  rw [h.matching, e_endpointVertex, e_endpointVertex]
  show (if v_a = w_b ∧ w_a = v_b ∧ b_a = b_b then 1 else 0) = 1 ↔
       v_a = w_b ∧ w_a = v_b ∧ b_a = b_b
  constructor
  · intro h_eq
    by_contra hc
    rw [if_neg hc] at h_eq
    exact absurd h_eq (by decide)
  · intro hc
    rw [if_pos hc]

/-- **Seed-adjacency characterisation.** A vertex `u` is adjacent to
the seed `seedVertex w` iff `u` is a b=true endpoint at gadget `w`.

The (only-if) direction: case analysis on `h.e u`. If `u` is a subset
vertex, subset-subset adj=0. If `u` is an endpoint at gadget `v_e`
with partner `x` and parity `b`, then `adj endpoint aEmpty_w` requires
`v_e = w ∧ b = true` (from the `cfiAdj` endpoint-subset clause with
S = ∅).

This is the key structural fact for Phase 2's (P2) verifications:
the only CFI vertices that "see" a specific seed's fresh colour with
adj=1 are the b=true endpoints in that seed's gadget. -/
theorem adj_seedVertex_eq_one_iff (h : IsCFI' adj) (w : Fin h.m) (u : Fin n) :
    adj.adj u (h.seedVertex w) = 1 ↔
    ∃ (x : Fin h.m) (hx : x ∈ h.H.neighbors w), u = h.endpointVertex hx true := by
  constructor
  · -- Forward: case analysis on h.e u.
    intro h_adj
    rw [h.matching, e_seedVertex] at h_adj
    -- h_adj : h.H.cfiAdj (h.e u) (h.H.aEmpty w) = 1
    cases h_eu : h.e u with
    | inl sub =>
      -- u is a subset vertex; subset-subset = 0 contradicts adj=1.
      exfalso
      rw [h_eu] at h_adj
      -- h_adj : h.H.cfiAdj (Sum.inl sub) (h.H.aEmpty w) = 1
      -- aEmpty w = Sum.inl _; so this is the Sum.inl/Sum.inl case = 0.
      have : h.H.cfiAdj (Sum.inl sub) (h.H.aEmpty w) = 0 := by
        unfold CFIBase.aEmpty
        rfl
      rw [this] at h_adj
      exact absurd h_adj (by decide)
    | inr endp =>
      -- u is an endpoint; destructure to (v_e, x, hx, b).
      obtain ⟨v_e, ⟨x, hx⟩, b⟩ := endp
      rw [h_eu] at h_adj
      -- h_adj : h.H.cfiAdj (Sum.inr ⟨v_e, ⟨x, hx⟩, b⟩) (h.H.aEmpty w) = 1
      -- = if w = v_e ∧ decide(x ∈ ∅) ≠ b then 1 else 0
      -- = if w = v_e ∧ b = true then 1 else 0.
      have h_form : h.H.cfiAdj (Sum.inr ⟨v_e, ⟨x, hx⟩, b⟩) (h.H.aEmpty w) =
          if w = v_e ∧ b = true then 1 else 0 := by
        show (if w = v_e ∧ decide (x ∈ (∅ : Finset (Fin h.m))) ≠ b then 1 else 0) =
             (if w = v_e ∧ b = true then 1 else 0)
        have hne : decide (x ∈ (∅ : Finset (Fin h.m))) = false := by simp
        rw [hne]
        by_cases hb : b
        · simp [hb]
        · simp [hb]
      rw [h_form] at h_adj
      -- h_adj : (if w = v_e ∧ b = true then 1 else 0) = 1
      have hc : w = v_e ∧ b = true := by
        by_contra hc
        rw [if_neg hc] at h_adj
        exact absurd h_adj (by decide)
      obtain ⟨hw_eq, hb_true⟩ := hc
      -- Now: v_e = w (from hw_eq.symm), b = true.
      -- So h.e u = Sum.inr ⟨w, ⟨x, hx⟩, true⟩ where hx : x ∈ N(v_e) = N(w).
      -- That is, u = endpointVertex (with the right hx after rewriting v_e to w) true.
      refine ⟨x, ?_, ?_⟩
      · -- hx : x ∈ N(v_e); want x ∈ N(w). Use hw_eq : w = v_e.
        rw [hw_eq]; exact hx
      · -- u = h.endpointVertex (hx after rewrite) true.
        -- h.e u = Sum.inr ⟨v_e, ⟨x, hx⟩, b⟩ = Sum.inr ⟨w, ⟨x, hx after rewrite⟩, true⟩.
        -- So u = h.e.symm (Sum.inr _) = h.endpointVertex (rewrite of hx) true.
        apply h.e.injective
        rw [e_endpointVertex, h_eu, hb_true]
        -- Need: Sum.inr ⟨v_e, ⟨x, hx⟩, true⟩ = h.H.endpoint (hw_eq ▸ hx) true.
        unfold CFIBase.endpoint
        congr 1
        -- Sigma equality: ⟨v_e, ⟨x, hx⟩, true⟩ = ⟨w, ⟨x, hw_eq ▸ hx⟩, true⟩.
        -- v_e = w by hw_eq.symm.
        subst hw_eq
        rfl
  · -- Backward: u = endpointVertex hx true ⟹ adj u seed_w = 1.
    rintro ⟨x, hx, rfl⟩
    exact h.adj_endpoint_seed_true hx

end IsCFI'

/-! ### §13.13 — M3.D Phase 2.1: within-gadget b=true endpoint split at round 2

The first cascade step that **uses** the Phase 1 bridge step lemma.

Under `χ_1 = refineStep χ_{allSeeds}`, the b=true endpoints at the
same gadget `v` toward different partners `w, w' ∈ N(v)` (with
`w ≠ w'`) get distinct colours after one more `refineStep` round.

Sketch:
- **(P1)** Bridge partners are `e^1_{w→v}` and `e^1_{w'→v}` — b=true
  endpoints at different gadgets `w ≠ w'`. M3.C
  (`refineStep_endpoint_true_inter_gadget`) gives them distinct
  `χ_1` colours.
- **(P2)** For any `u` adj=1 to `e^1_{v→w'}` (the second endpoint):
  show `χ_1 u ≠ χ_1 (e^1_{w→v})`. By a signature-tuple argument:
  the tuple `(χ_0 seed_w, 1, P · seed_w)` is in `e^1_{w→v}`'s
  signature (own-gadget seed adjacency) but not in `u`'s (since `u`
  is not adj=1 to seed_w — proved by combining
  `adj_seedVertex_eq_one_iff` with `adj_endpointVertex_eq_one_iff`
  to force `w = w'`, contradicting our hypothesis).

This validates the Phase 1 + Phase 2 strategy: an arbitrary cascade
case can be discharged by applying the local step lemma + verifying
(P2) via tuple-presence + structural CFI facts. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M3.D Phase 2.1 — within-gadget b=true endpoint split at round 2.**

Under `χ_1 = refineStep χ_{allSeeds}`, applying one more refineStep
distinguishes b=true endpoints at the same gadget toward different
partners. -/
private theorem refineStep_endpoint_true_intra_gadget_partner (h : IsCFI' adj)
    (P : PMatrix n) {v w w' : Fin h.m} (hww : w ≠ w')
    (hw : w ∈ h.H.neighbors v) (hw' : w' ∈ h.H.neighbors v) :
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.endpointVertex hw true) ≠
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.endpointVertex hw' true) := by
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  -- Apply the Phase 1 step lemma with χ = χ_1.
  apply h.refineStep_bridge_step P χ_1 hw hw' true
  · -- (P1): bridge partners e^1_{w→v}, e^1_{w'→v} distinguished by χ_1
    --       via M3.C (refineStep_endpoint_true_inter_gadget at gadgets w ≠ w').
    exact h.refineStep_endpoint_true_inter_gadget P hww
      (h.H.mem_neighbors_symm.mp hw) (h.H.mem_neighbors_symm.mp hw')
  · -- (P2): for any u adj=1 to e^1_{v→w'}, show χ_1 u ≠ χ_1 (e^1_{w→v}).
    intro u hu_adj_ev'
    -- Names for the relevant Fin n vertices.
    set seed_w := h.seedVertex w
    set bp := h.endpointVertex (h.H.mem_neighbors_symm.mp hw) true
    have hseed_mem : seed_w ∈ h.allSeeds := h.seedVertex_mem_allSeeds w
    -- Suppose χ_1 u = χ_1 bp; derive a contradiction.
    intro hχ_eq
    -- refineStep_iff splits this into χ_0 equality + signature equality.
    have hboth := (refineStep_iff adj P χ_0 _ _).mp hχ_eq
    -- Witness tuple in bp's signature: (χ_0 seed_w, 1, P bp seed_w).
    let t : Nat × Nat × POE := (χ_0 seed_w, 1, P bp seed_w)
    -- (a) t ∈ signature χ_0 bp via u' = seed_w (adj bp seed_w = 1).
    have ht_in_bp : t ∈ signature adj P χ_0 bp := by
      unfold signature
      rw [Multiset.mem_map]
      refine ⟨seed_w, ?_, ?_⟩
      · rw [Finset.mem_val, Finset.mem_filter]
        exact ⟨Finset.mem_univ _,
          h.seedVertex_ne_endpointVertex (h.H.mem_neighbors_symm.mp hw) true⟩
      · show (χ_0 seed_w, adj.adj bp seed_w, P bp seed_w) = t
        rw [h.adj_endpoint_seed_true (h.H.mem_neighbors_symm.mp hw)]
    -- (b) Transport via signature equality: t ∈ signature χ_0 u.
    rw [← hboth.2] at ht_in_bp
    -- Unpack: ∃ u' ≠ u, χ_0 u' = χ_0 seed_w, adj u u' = 1, P u u' = P bp seed_w.
    unfold signature at ht_in_bp
    rw [Multiset.mem_map] at ht_in_bp
    obtain ⟨u', _, hu'_eq⟩ := ht_in_bp
    have hχu' : χ_0 u' = χ_0 seed_w := congrArg Prod.fst hu'_eq
    have hrest : (adj.adj u u', P u u') = ((1, P bp seed_w) : Nat × POE) :=
      congrArg Prod.snd hu'_eq
    have hadj_u_u' : adj.adj u u' = 1 := congrArg Prod.fst hrest
    -- (c) Multi-seed uniqueness: χ_0 u' = χ_0 seed_w forces u' = seed_w.
    have hu'_seed : u' = seed_w :=
      (individualizedColouring_eq_iff_of_mem h.allSeeds hseed_mem).mp hχu'
    rw [hu'_seed] at hadj_u_u'
    -- hadj_u_u' : adj.adj u seed_w = 1
    -- (d) By adj_seedVertex_eq_one_iff: u = endpointVertex hx true for some x ∈ N(w).
    obtain ⟨x, hx, hu_eq⟩ := (h.adj_seedVertex_eq_one_iff w u).mp hadj_u_u'
    -- (e) Combined with hu_adj_ev', apply adj_endpointVertex_eq_one_iff to force w' = w.
    rw [hu_eq] at hu_adj_ev'
    rw [h.adj_endpointVertex_eq_one_iff hw' hx true true] at hu_adj_ev'
    -- hu_adj_ev' : v = x ∧ w' = w ∧ true = true. Extract w' = w.
    obtain ⟨_, hw'_eq_w, _⟩ := hu_adj_ev'
    exact hww hw'_eq_w.symm

end IsCFI'

/-! ### §13.14 — Phase 2.3 prereqs: subset vertex helpers

Phase 2.3 distinguishes subset vertices `a_S^v` vs `a_{S'}^{v'}` at
different gadgets (`v ≠ v'`) one refineStep beyond `χ_{allSeeds}`. The
proof reuses M3.C (b=1 inter-gadget) and M3.B+ (b=0 vs b=1 cross-gadget,
proved in §13.15) via a new "subset step lemma" (§13.16).

This section introduces the helpers needed:
- `CFIBase.subset hS` — abstract subset vertex constructor for arbitrary
  even subsets (generalises `aEmpty v` from §13.1, which is the S = ∅
  case).
- `IsCFI'.subsetVertex hS` — Fin-n level extractor via `h.e.symm`.
- Adjacency facts at both levels.
- `adj_subsetVertex_eq_one_iff` — characterisation lemma (parallel to
  `adj_seedVertex_eq_one_iff` from §13.12): only endpoints at the
  subset's gadget with the right parity-mismatch are adj=1. -/

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-- The CFI vertex `a_S^v`: the subset vertex at gadget `v` with even
subset `S ⊆ N(v)`. Generalises `aEmpty v` (= `subset` at the empty-set
membership witness). -/
def subset {v : Fin m} {S : Finset (Fin m)}
    (hS : S ∈ H.evenSubsetsOfNeighbors v) : H.CFIVertex :=
  Sum.inl ⟨v, ⟨S, hS⟩⟩

/-- `aEmpty v` is the empty-subset case of `subset`. -/
private theorem aEmpty_eq_subset_empty (v : Fin m) :
    H.aEmpty v = H.subset (H.empty_mem_evenSubsetsOfNeighbors v) := rfl

/-- `cfiAdj (a_S^v) (e^1_{v→w}) = 1` when `w ∉ S`. The Phase 2.3 witness
adjacency: a non-saturated subset has at least one b=1 endpoint as a
neighbour. -/
private theorem cfiAdj_subset_endpoint_same_gadget_true_of_not_mem {v w : Fin m}
    {S : Finset (Fin m)} (hS : S ∈ H.evenSubsetsOfNeighbors v)
    (hw : w ∈ H.neighbors v) (hwS : w ∉ S) :
    H.cfiAdj (H.subset hS) (H.endpoint hw true) = 1 := by
  show (if v = v ∧ decide (w ∈ S) ≠ true then 1 else 0) = 1
  rw [if_pos]
  refine ⟨rfl, ?_⟩
  simp [hwS]

/-- `cfiAdj (a_S^v) (e^0_{v→w}) = 1` when `w ∈ S`. The Phase 2.2 witness
adjacency: a subset containing `w` is adjacent to the b=0 endpoint
pointing at `w`. -/
private theorem cfiAdj_subset_endpoint_same_gadget_false_of_mem {v w : Fin m}
    {S : Finset (Fin m)} (hS : S ∈ H.evenSubsetsOfNeighbors v)
    (hw : w ∈ H.neighbors v) (hwS : w ∈ S) :
    H.cfiAdj (H.subset hS) (H.endpoint hw false) = 1 := by
  show (if v = v ∧ decide (w ∈ S) ≠ false then 1 else 0) = 1
  rw [if_pos]
  refine ⟨rfl, ?_⟩
  simp [hwS]

/-- **Cross-gadget non-adjacency for subsets.** `subset hS` at gadget `v`
is not adjacent to `endpoint hw b` at gadget `v' ≠ v`. Generalises
`cfiAdj_aEmpty_endpoint_diff_gadget` from §13.2. -/
private theorem cfiAdj_subset_endpoint_diff_gadget {v v' w : Fin m}
    {S : Finset (Fin m)} (hS : S ∈ H.evenSubsetsOfNeighbors v)
    (hw : w ∈ H.neighbors v') (b : Bool) (hvv : v ≠ v') :
    H.cfiAdj (H.subset hS) (H.endpoint hw b) = 0 := by
  show (if v = v' ∧ decide (w ∈ S) ≠ b then 1 else 0) = 0
  rw [if_neg]
  rintro ⟨h_eq, _⟩
  exact hvv h_eq

/-- `subset hS ≠ endpoint hw b` — distinct CFI vertices (Sum tags
differ). -/
private theorem subset_ne_endpoint {v w : Fin m} {S : Finset (Fin m)}
    (hS : S ∈ H.evenSubsetsOfNeighbors v) (hw : w ∈ H.neighbors v) (b : Bool) :
    H.subset hS ≠ H.endpoint hw b := by
  intro heq
  unfold subset endpoint at heq
  injection heq

end CFIBase

/-- The `Fin n` vertex corresponding to `a_S^v` in `h : IsCFI' adj`.
Generalises `seedVertex v` (= `subsetVertex` at the empty-set membership
witness). -/
def IsCFI'.subsetVertex {n : Nat} {adj : AdjMatrix n} (h : IsCFI' adj)
    {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) : Fin n :=
  h.e.symm (h.H.subset hS)

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- Bijection round-trip: `h.e (h.subsetVertex hS) = h.H.subset hS`. -/
@[simp] theorem e_subsetVertex (h : IsCFI' adj)
    {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) :
    h.e (h.subsetVertex hS) = h.H.subset hS := by
  unfold subsetVertex
  exact Equiv.apply_symm_apply _ _

/-- `seedVertex v` is the empty-subset case of `subsetVertex`. -/
private theorem seedVertex_eq_subsetVertex_empty (h : IsCFI' adj) (v : Fin h.m) :
    h.seedVertex v =
      h.subsetVertex (h.H.empty_mem_evenSubsetsOfNeighbors v) := rfl

/-- Subset vertices and endpoint vertices are distinct in `Fin n`. -/
private theorem subsetVertex_ne_endpointVertex (h : IsCFI' adj)
    {v w : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) (hw : w ∈ h.H.neighbors v) (b : Bool) :
    h.subsetVertex hS ≠ h.endpointVertex hw b := by
  intro heq
  apply h.H.subset_ne_endpoint hS hw b
  have := congrArg h.e heq
  rwa [e_subsetVertex, e_endpointVertex] at this

/-- `adj (subsetVertex_v hS) (endpointVertex_v hw true) = 1` when `w ∉ S`
(Fin-n level). The Phase 2.3 witness adjacency. -/
private theorem adj_subsetVertex_endpoint_same_gadget_true_of_not_mem (h : IsCFI' adj)
    {v w : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) (hw : w ∈ h.H.neighbors v)
    (hwS : w ∉ S) :
    adj.adj (h.subsetVertex hS) (h.endpointVertex hw true) = 1 := by
  rw [h.matching, e_subsetVertex, e_endpointVertex]
  exact h.H.cfiAdj_subset_endpoint_same_gadget_true_of_not_mem hS hw hwS

/-- `adj (subsetVertex_v hS) (endpointVertex_v hw false) = 1` when `w ∈ S`
(Fin-n level). The Phase 2.2 witness adjacency. -/
private theorem adj_subsetVertex_endpoint_same_gadget_false_of_mem (h : IsCFI' adj)
    {v w : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) (hw : w ∈ h.H.neighbors v)
    (hwS : w ∈ S) :
    adj.adj (h.subsetVertex hS) (h.endpointVertex hw false) = 1 := by
  rw [h.matching, e_subsetVertex, e_endpointVertex]
  exact h.H.cfiAdj_subset_endpoint_same_gadget_false_of_mem hS hw hwS

/-- Cross-gadget Fin-n non-adjacency:
`adj (subsetVertex_v hS) (endpointVertex_v' hw b) = 0` when v ≠ v'. -/
private theorem adj_subsetVertex_endpoint_diff_gadget (h : IsCFI' adj)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    (hw : w ∈ h.H.neighbors v') (b : Bool) :
    adj.adj (h.subsetVertex hS) (h.endpointVertex hw b) = 0 := by
  rw [h.matching, e_subsetVertex, e_endpointVertex]
  exact h.H.cfiAdj_subset_endpoint_diff_gadget hS hw b hvv

/-- **Subset-adjacency characterisation.** `adj u (subsetVertex_{v'} hS') = 1`
iff `u` is an endpoint at gadget `v'` with partner `w' ∈ N(v')` and
parity `b` satisfying `(w' ∈ S') ⊕ b = true`.

Parallel to `adj_seedVertex_eq_one_iff` (§13.12), which is the `S' = ∅`
specialisation: `w' ∉ ∅` always, so `b = true` is forced there. -/
theorem adj_subsetVertex_eq_one_iff (h : IsCFI' adj)
    {v' : Fin h.m} {S' : Finset (Fin h.m)}
    (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v') (u : Fin n) :
    adj.adj u (h.subsetVertex hS') = 1 ↔
    ∃ (w' : Fin h.m) (hw' : w' ∈ h.H.neighbors v') (b : Bool),
      decide (w' ∈ S') ≠ b ∧ u = h.endpointVertex hw' b := by
  constructor
  · intro h_adj
    rw [h.matching, e_subsetVertex] at h_adj
    cases h_eu : h.e u with
    | inl sub =>
      -- Subset-subset adj=0; contradicts h_adj.
      exfalso
      rw [h_eu] at h_adj
      have : h.H.cfiAdj (Sum.inl sub) (h.H.subset hS') = 0 := by
        unfold CFIBase.subset
        rfl
      rw [this] at h_adj
      exact absurd h_adj (by decide)
    | inr endp =>
      obtain ⟨v_e, ⟨x, hx⟩, b⟩ := endp
      rw [h_eu] at h_adj
      -- cfiAdj (Sum.inr ⟨v_e, ⟨x, hx⟩, b⟩) (subset hS')
      -- = if v' = v_e ∧ decide (x ∈ S') ≠ b then 1 else 0
      have h_form : h.H.cfiAdj (Sum.inr ⟨v_e, ⟨x, hx⟩, b⟩) (h.H.subset hS') =
          if v' = v_e ∧ decide (x ∈ S') ≠ b then 1 else 0 := by
        unfold CFIBase.subset
        rfl
      rw [h_form] at h_adj
      have hc : v' = v_e ∧ decide (x ∈ S') ≠ b := by
        by_contra hc
        rw [if_neg hc] at h_adj
        exact absurd h_adj (by decide)
      obtain ⟨hv_eq, hb_parity⟩ := hc
      refine ⟨x, ?_, b, ?_, ?_⟩
      · rw [hv_eq]; exact hx
      · -- decide (x ∈ S') ≠ b, after rewriting v_e to v' (no S' change).
        exact hb_parity
      · apply h.e.injective
        rw [e_endpointVertex, h_eu]
        unfold CFIBase.endpoint
        congr 1
        subst hv_eq
        rfl
  · rintro ⟨w', hw', b, hparity, rfl⟩
    rw [h.matching, e_endpointVertex, e_subsetVertex, h.H.cfiAdj_symm]
    show (if v' = v' ∧ decide (w' ∈ S') ≠ b then 1 else 0) = 1
    rw [if_pos ⟨rfl, hparity⟩]

end IsCFI'

/-! ### §13.15 — Phase 2.3 prereqs: M3.B+ generalised parity distinction

A strengthening of M3.B from "same gadget" to "b=0 endpoint at any gadget
vs b=1 endpoint at gadget `v` are distinguished at round 1 under
`χ_{allSeeds}`." Used in Phase 2.3's no-match precondition when an
offending adj=1 neighbour at gadget `v'` has parity b=false.

Witness tuple `(c_v, 1, P et seed_v)` where `et = e^1_{v→w}` and
`c_v = χ seed_v`. Present in `et`'s signature (own-gadget seed-endpoint
adjacency, like M3.B); absent from any b=0 endpoint's signature
(no seed is adj=1 to a b=0 endpoint, whether own-gadget via
`adj_endpoint_seed_false` or cross-gadget via
`adj_endpoint_seed_diff_gadget`). -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M3.B+ / signature** — generalised parity distinction at round 1.

A b=0 endpoint at any gadget `v'` has a different signature multiset
from a b=1 endpoint at gadget `v` (regardless of whether v = v') under
`χ_{allSeeds}`. -/
private theorem signature_endpoint_b0_ne_b1_general_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v v' : Fin h.m}
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v') :
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw' false) ≠
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hsig
  set seed_v := h.seedVertex v
  set ef := h.endpointVertex hw' false
  set et := h.endpointVertex hw true
  set χ := individualizedColouring n h.allSeeds
  have hseed_mem : seed_v ∈ h.allSeeds := h.seedVertex_mem_allSeeds v
  let t : Nat × Nat × POE := (χ seed_v, 1, P et seed_v)
  -- (a) t ∈ signature et — via u = seed_v (own-gadget b=true endpoint to seed).
  have ht_in_et : t ∈ signature adj P χ et := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨seed_v, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.seedVertex_ne_endpointVertex hw true⟩
    · show (χ seed_v, adj.adj et seed_v, P et seed_v) = t
      rw [h.adj_endpoint_seed_true hw]
  -- (b) t ∉ signature ef — no u with χ u = c_v is adj=1 to a b=0 endpoint.
  have ht_notin_ef : t ∉ signature adj P χ ef := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ u = χ seed_v := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ef u, P ef u) = ((1, P et seed_v) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ef u = 1 := congrArg Prod.fst hrest
    -- Multi-seed uniqueness: χ u = c_v forces u = seed_v.
    have hu_seed : u = seed_v :=
      (individualizedColouring_eq_iff_of_mem h.allSeeds hseed_mem).mp hχu
    rw [hu_seed] at hadj
    -- b=0 endpoint ef = e^0_{v'→w'} is not adjacent to seed_v = a_∅^v.
    -- Case split: v = v' (own-gadget) or v ≠ v' (cross-gadget); both adj=0.
    by_cases hvv : v = v'
    · subst hvv
      rw [h.adj_endpoint_seed_false hw'] at hadj
      exact absurd hadj (by decide)
    · rw [h.adj_endpoint_seed_diff_gadget hvv hw' false] at hadj
      exact absurd hadj (by decide)
  rw [hsig] at ht_notin_ef
  exact ht_notin_ef ht_in_et

/-- **M3.B+ / refineStep** — generalised parity distinction at round 1
(refineStep form). Under `χ_{allSeeds}`, one refineStep round gives the
b=0 endpoint at any gadget `v'` and the b=1 endpoint at gadget `v`
distinct colours. -/
private theorem refineStep_endpoint_b0_ne_b1_general_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v v' : Fin h.m}
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v') :
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw' false) ≠
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_endpoint_b0_ne_b1_general_allSeeds P hw hw' hboth.2

end IsCFI'

/-! ### §13.16 — Phase 2.3 step lemma: subset step (Approach 3, factored)

Generic step lemma for subset distinction: given any colouring `χ` and a
b=true witness endpoint `et = e^1_{v→w}` (with `w ∈ N(v) \ S`) whose
colour does NOT appear at any adj=1 neighbour of `subset_{v'} hS'`, one
refineStep distinguishes the two subset vertices.

Parallel to `refineStep_bridge_step` (§13.11) for bridge propagation:
both are signature-tuple step lemmas with a "uniqueness on the second
vertex's neighbourhood" precondition. The witness here comes from a
within-gadget endpoint adjacency rather than a cross-gadget bridge.

This is the **Approach 3** primitive for subset propagation — generic
over χ, ready to be applied at any cascade round once the no-match
precondition can be verified. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Subset step / signature** — generic subset signature distinction.

Preconditions:
- `hwS`: `w ∉ S` (so `subset hS` has `e^1_{v→w}` as an adj=1 neighbour;
  this is the witness endpoint).
- `hno_match`: the witness colour `χ (e^1_{v→w})` does not appear at any
  adj=1 neighbour of `subset hS'`.

Conclusion: the signature multisets under χ differ. -/
private theorem signature_subset_step (h : IsCFI' adj) (P : PMatrix n)
    (χ : Colouring n) {v v' w : Fin h.m}
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {S' : Finset (Fin h.m)} (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v')
    (hw : w ∈ h.H.neighbors v) (hwS : w ∉ S)
    (hno_match : ∀ u, adj.adj (h.subsetVertex hS') u = 1 →
                   χ u ≠ χ (h.endpointVertex hw true)) :
    signature adj P χ (h.subsetVertex hS) ≠
    signature adj P χ (h.subsetVertex hS') := by
  intro hsig
  set av  := h.subsetVertex hS  with hav
  set av' := h.subsetVertex hS' with hav'
  set et  := h.endpointVertex hw true with het
  let t : Nat × Nat × POE := (χ et, 1, P av et)
  -- (a) t ∈ signature av — via u = et (own-gadget b=1 adjacency).
  have ht_in_av : t ∈ signature adj P χ av := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨et, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact h.subsetVertex_ne_endpointVertex hS hw true heq.symm
    · show (χ et, adj.adj av et, P av et) = t
      rw [h.adj_subsetVertex_endpoint_same_gadget_true_of_not_mem hS hw hwS]
  -- (b) t ∉ signature av' — directly from hno_match.
  have ht_notin_av' : t ∉ signature adj P χ av' := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ u = χ et := congrArg Prod.fst hu_eq
    have hrest : (adj.adj av' u, P av' u) = ((1, P av et) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj av' u = 1 := congrArg Prod.fst hrest
    exact (hno_match u hadj) hχu
  rw [hsig] at ht_in_av
  exact ht_notin_av' ht_in_av

/-- **Subset step / refineStep** — generic subset refineStep distinction.

Given the same preconditions as `signature_subset_step`, one refineStep
distinguishes the two subset vertices.

This is the **Approach 3 primitive** for subset propagation: pair it
with a concrete-round driver (Phase 2.3 instantiates at χ = χ_1; later
phases may instantiate at other rounds) to discharge specific cascade
cases. -/
private theorem refineStep_subset_step (h : IsCFI' adj) (P : PMatrix n)
    (χ : Colouring n) {v v' w : Fin h.m}
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {S' : Finset (Fin h.m)} (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v')
    (hw : w ∈ h.H.neighbors v) (hwS : w ∉ S)
    (hno_match : ∀ u, adj.adj (h.subsetVertex hS') u = 1 →
                   χ u ≠ χ (h.endpointVertex hw true)) :
    refineStep adj P χ (h.subsetVertex hS) ≠
    refineStep adj P χ (h.subsetVertex hS') := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_subset_step P χ hS hS' hw hwS hno_match hboth.2

end IsCFI'

/-! ### §13.16.5 — General `adj` symmetry for CFI graphs

CFI graphs are symmetric (`cfiAdj_symm` from §8); this lifts that fact
through `h.matching` so `adj.adj` can be swapped freely. Used in Phase 2.3
and later phases to reconcile the signature/iff conventions:
- `signature χ v` produces tuples with `adj.adj v u` (subject-on-left).
- `adj_seedVertex_eq_one_iff` / `adj_subsetVertex_eq_one_iff` are phrased
  with `adj.adj u (anchor)` (candidate-on-left).

The bridge between conventions is `IsCFI'.adj_symm`. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **CFI adjacency is symmetric** (Fin-n level). Lifts
`CFIBase.cfiAdj_symm` through the matching identity. -/
theorem adj_symm (h : IsCFI' adj) (i j : Fin n) :
    adj.adj i j = adj.adj j i := by
  rw [h.matching, h.matching, h.H.cfiAdj_symm]

end IsCFI'

/-! ### §13.17 — Phase 2.3 headline: subset by gadget at round 2

Under `χ_1 = refineStep χ_{allSeeds}`, applying one more refineStep
distinguishes subset vertices at different gadgets, provided the LHS
subset has a witness `w ∈ N(v) \ S` (so it has at least one b=1
adjacent endpoint).

Application of `refineStep_subset_step` (§13.16) with `χ = χ_1`:
- (P2 / `hno_match`): for any `u` adj=1 to `subset_{v'} hS'`,
  `χ_1 u ≠ χ_1 (e^1_{v→w})`.
  - By `adj_subsetVertex_eq_one_iff` (§13.14), `u = endpointVertex hw'' b''`
    at gadget `v'`.
  - If `b'' = false`: M3.B+ (§13.15) gives `χ_1 (e^0_{v'→w''}) ≠ χ_1 (e^1_{v→w})`.
  - If `b'' = true`: M3.C (§13.10) gives `χ_1 (e^1_{v'→w''}) ≠ χ_1 (e^1_{v→w})`
    since v ≠ v'.

**Hypothesis qualifier.** The `w ∉ S` assumption is essential: it
provides the b=1 witness endpoint. For deg-even bases (e.g., Rook3x3),
the degenerate case `S = N(v)` lacks any b=1 adjacency; that case is
deferred to a later cascade round once b=0 endpoints become
distinguishable by gadget (after Phase 2.2). -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Phase 2.3 / signature** — subset by gadget at round 2.

Under `χ_1 = refineStep χ_{allSeeds}`, the signature multisets (at χ_1)
of two subset vertices at different gadgets differ, provided the LHS
subset has a witness `w ∈ N(v) \ S`. -/
private theorem signature_subset_inter_gadget_round2 (h : IsCFI' adj) (P : PMatrix n)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {S' : Finset (Fin h.m)} (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v) (hwS : w ∉ S) :
    signature adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS) ≠
    signature adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS') := by
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  -- Apply the §13.16 step lemma at χ = χ_1.
  apply h.signature_subset_step P χ_1 hS hS' hw hwS
  -- Verify (P2 / hno_match): any u adj=1 to subset_{v'} hS' has
  -- χ_1 u ≠ χ_1 (e^1_{v→w}).
  intro u hu_adj_av'
  -- hu_adj_av' : adj.adj (h.subsetVertex hS') u = 1 (subject-on-left from
  -- signature). The iff lemma is phrased with candidate-on-left; swap via
  -- adj_symm to bridge conventions.
  rw [h.adj_symm] at hu_adj_av'
  obtain ⟨w'', hw'', b'', _hparity, hu_eq⟩ :=
    (h.adj_subsetVertex_eq_one_iff hS' u).mp hu_adj_av'
  rw [hu_eq]
  cases b'' with
  | false =>
    -- b''=false: M3.B+ gives χ_1 (e^0_{v'→w''}) ≠ χ_1 (e^1_{v→w}).
    exact h.refineStep_endpoint_b0_ne_b1_general_allSeeds P hw hw''
  | true =>
    -- b''=true: M3.C gives the b=1 inter-gadget distinction (v' ≠ v form).
    intro hχ_eq
    exact h.refineStep_endpoint_true_inter_gadget P hvv.symm hw'' hw hχ_eq

/-- **Phase 2.3 / refineStep (M3.D Phase 2.3 headline)** — subset by
gadget at round 2.

Under `χ_1 = refineStep χ_{allSeeds}`, applying one more refineStep
gives subset vertices at different gadgets distinct colours, provided
the LHS subset has a witness `w ∈ N(v) \ S` (a b=1 adjacent endpoint).

This is the **subset distinction at cascade round 2** — the second-round
analogue of the b=1 endpoint inter-gadget distinction (M3.C, round 1).
Unlocks Phase 2.2 (b=0 endpoint inter-gadget at round 3 via subset
adjacencies). -/
private theorem refineStep_subset_inter_gadget_round2 (h : IsCFI' adj) (P : PMatrix n)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {S' : Finset (Fin h.m)} (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v) (hwS : w ∉ S) :
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS) ≠
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS') := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_subset_inter_gadget_round2 P hvv hS hS' hw hwS hboth.2

end IsCFI'

/-! ### §13.18 — Phase 2.2 prereq: M3.B++ (subset vs b=1 endpoint at round 1)

The third "round-1 parity-discriminator" in the M3.B family:
- M3.B (§13.9): b=0 endpoint at v vs b=1 endpoint at v (same gadget).
- M3.B+ (§13.15): b=0 endpoint at any v' vs b=1 endpoint at v.
- **M3.B++ (this section)**: subset vertex at any (v', T) vs b=1
  endpoint at v.

Used by §13.19's cross-type round-2 distinction (subset vs b=0
endpoint at χ_2) when the b=0 endpoint's adj=1 neighbour is a subset.

Same witness tuple as M3.B+ — `(c_v, 1, P et seed_v)`. Absence argument
is **cleaner**: subsets have NO seed adjacencies at all (subset-subset
adj is 0 in CFI), so the multi-seed-forced u = seed_v contradicts the
adj=1 assumption directly. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Subset-subset non-adjacency (Fin-n).** Subset and seed vertices
(which are subsets) are never CFI-adjacent. Special case of the general
"subset-subset adj = 0" fact, instantiated for the seed on the right —
the form needed in M3.B++. -/
private theorem adj_subsetVertex_seedVertex (h : IsCFI' adj)
    {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) (w : Fin h.m) :
    adj.adj (h.subsetVertex hS) (h.seedVertex w) = 0 := by
  rw [seedVertex_eq_subsetVertex_empty, h.matching, e_subsetVertex,
      e_subsetVertex]
  rfl

/-- **M3.B++ / signature** — subset vertex (any gadget, any T) vs b=1
endpoint at gadget v are distinguished at round 1 under `χ_{allSeeds}`.

Same witness tuple as M3.B+; the absence argument is even cleaner —
multi-seed uniqueness forces `u = seed_v`, but `adj subsetVertex seed_v
= 0` (subset-subset) directly contradicts `adj subsetVertex u = 1`. -/
private theorem signature_subsetVertex_ne_endpoint_true_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v : Fin h.m}
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {v' : Fin h.m} {T : Finset (Fin h.m)}
    (hT : T ∈ h.H.evenSubsetsOfNeighbors v') :
    signature adj P (individualizedColouring n h.allSeeds)
        (h.subsetVertex hT) ≠
    signature adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hsig
  set seed_v := h.seedVertex v
  set av := h.subsetVertex hT
  set et := h.endpointVertex hw true
  set χ := individualizedColouring n h.allSeeds
  have hseed_mem : seed_v ∈ h.allSeeds := h.seedVertex_mem_allSeeds v
  let t : Nat × Nat × POE := (χ seed_v, 1, P et seed_v)
  -- (a) t ∈ signature et — via u = seed_v.
  have ht_in_et : t ∈ signature adj P χ et := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨seed_v, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.seedVertex_ne_endpointVertex hw true⟩
    · show (χ seed_v, adj.adj et seed_v, P et seed_v) = t
      rw [h.adj_endpoint_seed_true hw]
  -- (b) t ∉ signature av — subsets have no seed adjacencies.
  have ht_notin_av : t ∉ signature adj P χ av := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ u = χ seed_v := congrArg Prod.fst hu_eq
    have hrest : (adj.adj av u, P av u) = ((1, P et seed_v) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj av u = 1 := congrArg Prod.fst hrest
    have hu_seed : u = seed_v :=
      (individualizedColouring_eq_iff_of_mem h.allSeeds hseed_mem).mp hχu
    rw [hu_seed] at hadj
    rw [h.adj_subsetVertex_seedVertex hT v] at hadj
    exact absurd hadj (by decide)
  rw [hsig] at ht_notin_av
  exact ht_notin_av ht_in_et

/-- **M3.B++ / refineStep** — subset vertex (any) vs b=1 endpoint at v
distinguished after one `refineStep` round on `χ_{allSeeds}`. -/
private theorem refineStep_subsetVertex_ne_endpoint_true_allSeeds (h : IsCFI' adj)
    (P : PMatrix n) {v : Fin h.m}
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {v' : Fin h.m} {T : Finset (Fin h.m)}
    (hT : T ∈ h.H.evenSubsetsOfNeighbors v') :
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.subsetVertex hT) ≠
    refineStep adj P (individualizedColouring n h.allSeeds)
        (h.endpointVertex hw true) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_subsetVertex_ne_endpoint_true_allSeeds P hw hT hboth.2

end IsCFI'

/-! ### §13.19 — Phase 2.2 prereq: cross-type round-2 distinction
(subset with witness vs b=0 endpoint at χ_2)

The cross-type chunk needed by Phase 2.2's hno_match: when the offending
adj=1 neighbour of the second b=0 endpoint is its **bridge partner**
(itself a b=0 endpoint), we need to show its χ_2 colour differs from
the subset witness's χ_2 colour.

**Proof structure.** Witness at χ_1: `(χ_1 (e^1_{v→x}), 1, P av (e^1_{v→x}))`
where `x ∈ N(v) \ S` (the subset's own Phase-2.3-style witness).
- (a) Present in `av = subsetVertex hS`'s χ_1-signature via u' = e^1_{v→x}.
- (b) Absent from `ef = e^0_{v_f→w_f}`'s χ_1-signature: case analysis on
  h.e u' for any adj=1 candidate.
  - u' is subset at gadget v_f containing w_f: M3.B++ rules out χ_1 match.
  - u' is endpoint = bridge partner e^0_{w_f→v_f}: M3.B+ rules out χ_1 match.

Conclude χ_2 (refineStep χ_1) outputs differ via `refineStep_iff`. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Cross-type signature distinction at χ_1.** Subset with witness vs
b=0 endpoint (any gadget): their χ_1-signatures differ.

Hypotheses:
- `(S, hS, x, hx, hxS)`: even subset at v with witness x ∈ N(v) \ S
  (so `subsetVertex hS` has `endpointVertex hx true` as an adj=1
  neighbour with M3.C-distinguished χ_1 colour).
- `(v_f, w_f, hwf)`: any b=0 endpoint location.

Conclusion: round-1 signatures of `subsetVertex hS` and
`endpointVertex hwf false` (under χ_1 = refineStep χ_{allSeeds}) differ.
Combined with `refineStep_iff`, χ_2 colours differ. -/
private theorem signature_subsetVertex_ne_endpoint_false_round2 (h : IsCFI' adj)
    (P : PMatrix n)
    {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {x : Fin h.m} (hx : x ∈ h.H.neighbors v) (hxS : x ∉ S)
    {v_f w_f : Fin h.m} (hwf : w_f ∈ h.H.neighbors v_f) :
    signature adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS) ≠
    signature adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.endpointVertex hwf false) := by
  intro hsig
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  set av := h.subsetVertex hS with hav_def
  set ef := h.endpointVertex hwf false with hef_def
  set et := h.endpointVertex hx true with het_def
  -- Witness tuple at χ_1: (χ_1 et, 1, P av et).
  let t : Nat × Nat × POE := (χ_1 et, 1, P av et)
  -- (a) t ∈ signature χ_1 av — via u' = et.
  have ht_in_av : t ∈ signature adj P χ_1 av := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨et, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact h.subsetVertex_ne_endpointVertex hS hx true heq.symm
    · show (χ_1 et, adj.adj av et, P av et) = t
      rw [h.adj_subsetVertex_endpoint_same_gadget_true_of_not_mem hS hx hxS]
  -- (b) t ∉ signature χ_1 ef — case analysis on u.
  have ht_notin_ef : t ∉ signature adj P χ_1 ef := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ_1 u = χ_1 et := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ef u, P ef u) = ((1, P av et) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ef u = 1 := congrArg Prod.fst hrest
    -- Convert adj.adj ef u = 1 into cfiAdj form for case analysis.
    rw [h.matching, e_endpointVertex] at hadj
    -- hadj : cfiAdj (endpoint hwf false) (h.e u) = 1
    -- Case on h.e u to determine u's structure.
    cases h_eu : h.e u with
    | inl sub =>
      -- u is a subset.
      obtain ⟨v_s, ⟨S_u, hSu⟩⟩ := sub
      rw [h_eu] at hadj
      -- hadj reduces by cfiAdj's endpoint-subset clause to:
      -- (if v_s = v_f ∧ decide (w_f ∈ S_u) ≠ false then 1 else 0) = 1
      have hc : v_s = v_f ∧ decide (w_f ∈ S_u) ≠ false := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hwf false)
              (Sum.inl ⟨v_s, ⟨S_u, hSu⟩⟩ : h.H.CFIVertex) = 0 := by
          show (if v_s = v_f ∧ decide (w_f ∈ S_u) ≠ false then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hadj
        exact absurd hadj (by decide)
      obtain ⟨hvs_eq, _⟩ := hc
      subst hvs_eq
      -- u = h.subsetVertex hSu (via h_eu).
      have hu_subset : u = h.subsetVertex hSu := by
        apply h.e.injective
        rw [e_subsetVertex, h_eu]
        rfl
      rw [hu_subset] at hχu
      -- Apply M3.B++ : χ_1 (subsetVertex hSu) ≠ χ_1 et.
      exact h.refineStep_subsetVertex_ne_endpoint_true_allSeeds P hx hSu hχu
    | inr endp =>
      -- u is an endpoint = bridge partner of ef.
      obtain ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ := endp
      rw [h_eu] at hadj
      -- hadj reduces by cfiAdj's endpoint-endpoint clause to:
      -- (if v_f = x_e ∧ w_f = v_e ∧ false = b_e then 1 else 0) = 1
      have hc : v_f = x_e ∧ w_f = v_e ∧ false = b_e := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hwf false)
              (Sum.inr ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ : h.H.CFIVertex) = 0 := by
          show (if v_f = x_e ∧ w_f = v_e ∧ false = b_e then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hadj
        exact absurd hadj (by decide)
      obtain ⟨_, _, hb_eq⟩ := hc
      have hb_e_false : b_e = false := hb_eq.symm
      subst hb_e_false
      -- u = h.endpointVertex hxe false (via h_eu, with b_e now false).
      have hu_endp : u = h.endpointVertex hxe false := by
        apply h.e.injective
        rw [e_endpointVertex, h_eu]
        rfl
      rw [hu_endp] at hχu
      -- Apply M3.B+: χ_1 (e^0_{v_e→x_e}) ≠ χ_1 (e^1_{v→x}).
      exact h.refineStep_endpoint_b0_ne_b1_general_allSeeds P hx hxe hχu
  rw [hsig] at ht_in_av
  exact ht_notin_ef ht_in_av

/-- **Cross-type refineStep distinction at χ_2.** Subset with witness vs
b=0 endpoint (any gadget): their χ_2 colours differ.

Lift of `signature_subsetVertex_ne_endpoint_false_round2` through
`refineStep_iff`. -/
private theorem refineStep_subsetVertex_ne_endpoint_false_round2 (h : IsCFI' adj)
    (P : PMatrix n)
    {v : Fin h.m} {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    {x : Fin h.m} (hx : x ∈ h.H.neighbors v) (hxS : x ∉ S)
    {v_f w_f : Fin h.m} (hwf : w_f ∈ h.H.neighbors v_f) :
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.subsetVertex hS) ≠
    refineStep adj P (refineStep adj P (individualizedColouring n h.allSeeds))
        (h.endpointVertex hwf false) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_subsetVertex_ne_endpoint_false_round2 P hS hx hxS hwf hboth.2

end IsCFI'

/-! ### §13.20 — Phase 2.2 headline: b=0 endpoint inter-gadget at round 3

Under `χ_2 = refineStep (refineStep χ_{allSeeds})`, applying one more
refineStep distinguishes b=0 endpoints at different gadgets, given a
witness subset at the LHS gadget.

**Mechanism.** Direct signature-tuple argument at χ_2 (NOT bridge-step,
since b=0 bridge partners aren't distinguished early). Witness tuple:
`(χ_2 (a_S^v), 1, P (e^0_{v→w}) (a_S^v))` with `w ∈ S` (adjacency) and
`x ∈ N(v) \ S` (subset's Phase 2.3 witness).

For the no-match argument on the RHS b=0 endpoint, case analysis on u:
- u is subset at v' containing w': Phase 2.3 (§13.17) gives the
  distinction (with our LHS subset's witness x).
- u is bridge partner (b=0 at gadget w'): §13.19's cross-type round-2
  lemma gives the distinction.

**Hypothesis qualifier.** The witness (S, x) with `w ∈ S` and
`x ∈ N(v) \ S` requires `deg(v) ≥ 3` (so a 2-element even subset {w, y}
with y ≠ x exists). For `deg(v) = 2` cases, Phase 2.2 as stated doesn't
apply — those need a separate argument (likely more cascade rounds via
subset propagation through neighbouring gadgets). -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Phase 2.2 / signature** — b=0 endpoint inter-gadget signature
distinction at χ_2.

Under `χ_2 = refineStep χ_1 = refineStep (refineStep χ_{allSeeds})`,
the signature multisets of two b=0 endpoints at different gadgets
differ, given a witness subset `a_S^v` with `w ∈ S` and `x ∈ N(v) \ S`. -/
private theorem signature_endpoint_false_inter_gadget_round3 (h : IsCFI' adj)
    (P : PMatrix n)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v')
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    (hwS : w ∈ S)
    {x : Fin h.m} (hx : x ∈ h.H.neighbors v) (hxS : x ∉ S) :
    signature adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds)))
        (h.endpointVertex hw false) ≠
    signature adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds)))
        (h.endpointVertex hw' false) := by
  intro hsig
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  set χ_2 := refineStep adj P χ_1 with hχ_2
  set av := h.subsetVertex hS with hav_def
  set ef := h.endpointVertex hw false with hef_def
  set ef' := h.endpointVertex hw' false with hef'_def
  -- Witness tuple at χ_2.
  let t : Nat × Nat × POE := (χ_2 av, 1, P ef av)
  -- (a) t ∈ signature χ_2 ef — via u' = av (adj=1 since w ∈ S).
  have ht_in_ef : t ∈ signature adj P χ_2 ef := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨av, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact h.subsetVertex_ne_endpointVertex hS hw false heq
    · show (χ_2 av, adj.adj ef av, P ef av) = t
      -- adj ef av = adj av ef via symmetry; then subset-endpoint with w ∈ S.
      rw [h.adj_symm, h.adj_subsetVertex_endpoint_same_gadget_false_of_mem hS hw hwS]
  -- (b) t ∉ signature χ_2 ef' — case analysis on u.
  have ht_notin_ef' : t ∉ signature adj P χ_2 ef' := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ_2 u = χ_2 av := congrArg Prod.fst hu_eq
    have hrest : (adj.adj ef' u, P ef' u) = ((1, P ef av) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj ef' u = 1 := congrArg Prod.fst hrest
    rw [h.matching, e_endpointVertex] at hadj
    cases h_eu : h.e u with
    | inl sub =>
      -- u is a subset; characterise as subsetVertex hSu at gadget v' with w' ∈ S_u.
      obtain ⟨v_s, ⟨S_u, hSu⟩⟩ := sub
      rw [h_eu] at hadj
      have hc : v_s = v' ∧ decide (w' ∈ S_u) ≠ false := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hw' false)
              (Sum.inl ⟨v_s, ⟨S_u, hSu⟩⟩ : h.H.CFIVertex) = 0 := by
          show (if v_s = v' ∧ decide (w' ∈ S_u) ≠ false then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hadj
        exact absurd hadj (by decide)
      obtain ⟨hvs_eq, _⟩ := hc
      subst hvs_eq
      have hu_subset : u = h.subsetVertex hSu := by
        apply h.e.injective
        rw [e_subsetVertex, h_eu]
        rfl
      rw [hu_subset] at hχu
      -- Phase 2.3: χ_2 (subsetVertex hS) ≠ χ_2 (subsetVertex hSu).
      -- hχu (after symm): χ_2 (subsetVertex hS) = χ_2 (subsetVertex hSu).
      exact h.refineStep_subset_inter_gadget_round2 P hvv hS hSu hx hxS hχu.symm
    | inr endp =>
      -- u is an endpoint = bridge partner e^0_{w'→v'}.
      obtain ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ := endp
      rw [h_eu] at hadj
      have hc : v' = x_e ∧ w' = v_e ∧ false = b_e := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hw' false)
              (Sum.inr ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ : h.H.CFIVertex) = 0 := by
          show (if v' = x_e ∧ w' = v_e ∧ false = b_e then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hadj
        exact absurd hadj (by decide)
      obtain ⟨_, _, hb_eq⟩ := hc
      have hb_e_false : b_e = false := hb_eq.symm
      subst hb_e_false
      have hu_endp : u = h.endpointVertex hxe false := by
        apply h.e.injective
        rw [e_endpointVertex, h_eu]
        rfl
      rw [hu_endp] at hχu
      -- Cross-type round-2 (§13.19): χ_2 (subsetVertex hS) ≠ χ_2 (e^0_{v_e→x_e}).
      -- hχu (after symm): χ_2 (subsetVertex hS) = χ_2 (e^0_{v_e→x_e}).
      exact h.refineStep_subsetVertex_ne_endpoint_false_round2 P hS hx hxS hxe hχu.symm
  rw [hsig] at ht_in_ef
  exact ht_notin_ef' ht_in_ef

/-- **Phase 2.2 / refineStep (M3.D Phase 2.2 headline)** — b=0 endpoint
inter-gadget distinction at round 3.

Under three nested `refineStep` rounds applied to `χ_{allSeeds}`, b=0
endpoints at different gadgets get distinct colours, given a witness
subset `a_S^v` with `w ∈ S` and `x ∈ N(v) \ S` (which exists when
`deg(v) ≥ 3`).

This unlocks Phase 2.X (b=0 within-gadget partner distinction) via the
bridge step lemma at round 4. -/
private theorem refineStep_endpoint_false_inter_gadget_round3 (h : IsCFI' adj)
    (P : PMatrix n)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v)
    {w' : Fin h.m} (hw' : w' ∈ h.H.neighbors v')
    {S : Finset (Fin h.m)} (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    (hwS : w ∈ S)
    {x : Fin h.m} (hx : x ∈ h.H.neighbors v) (hxS : x ∉ S) :
    refineStep adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds)))
        (h.endpointVertex hw false) ≠
    refineStep adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds)))
        (h.endpointVertex hw' false) := by
  intro hrefine
  have hboth := (refineStep_iff adj P _ _ _).mp hrefine
  exact h.signature_endpoint_false_inter_gadget_round3
    P hvv hw hw' hS hwS hx hxS hboth.2

end IsCFI'

/-! ### §13.21 — OddDegree: restricted CFI class for clean cascade

Phase 2.X (b=0 within-gadget partner), Phase 2.4 (subset by S), and M4
have a degenerate sub-case for **saturated** subsets `S = N(v)`. This
case requires extra cascade rounds and threading extra hypotheses
through the proofs.

A clean alternative: restrict to CFI bases where every vertex has
**odd degree**. Then `|S|` even and `|S| ≤ deg(v) − 1 < deg(v)` forces
`S ⊊ N(v)`, killing the saturated case.

CFI bases in this class include K₄, K₃,₃, Petersen — covering the
dominant interesting cases. Excluded: Rook3×3 (deg 4 even). The
general-degree case is deferred to a future-work follow-on with extra
cascade rounds.

This section adds `IsCFI'.OddDegree` and a witness-existence helper.
Downstream phases (Phase 2.X, 2.4, M4) take `h.OddDegree` as a
hypothesis. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Odd-degree CFI base.** Every base vertex has odd degree, ensuring
no even subset `S ⊆ N(v)` is saturated (`S = N(v)`). -/
def OddDegree (h : IsCFI' adj) : Prop :=
  ∀ v : Fin h.m, h.H.degree v % 2 = 1

/-- Under `OddDegree`, every even subset of `N(v)` has a strict
non-element `y ∈ N(v) \ S` — the Phase-2.3-style witness. Used by
Phase 2.X / 2.4 / M4 to construct subset distinction witnesses
automatically. -/
theorem exists_witness_of_oddDegree (h : IsCFI' adj) (h_odd : h.OddDegree)
    (v : Fin h.m) {S : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v) :
    ∃ y, y ∈ h.H.neighbors v ∧ y ∉ S := by
  rw [h.H.mem_evenSubsetsOfNeighbors] at hS
  obtain ⟨hSsub, hSeven⟩ := hS
  -- |S| even, deg(v) odd ⟹ S ≠ N(v).
  have hSne : S ≠ h.H.neighbors v := by
    intro h_eq
    rw [h_eq] at hSeven
    have h_v_deg : (h.H.neighbors v).card % 2 = 1 := h_odd v
    omega
  have h_ssub : S ⊂ h.H.neighbors v := by
    refine ⟨hSsub, ?_⟩
    intro hsupset
    exact hSne (Finset.Subset.antisymm hSsub hsupset)
  obtain ⟨y, hy_in, hy_notin⟩ := Finset.exists_of_ssubset h_ssub
  exact ⟨y, hy_in, hy_notin⟩

/-- **Phase 2.2 witness construction under OddDegree.** Given any
`v ∈ N(w)`, construct an even subset `S ⊆ N(w)` with `v ∈ S` and a
witness `x ∈ N(w) \ S`. Used by Phase 2.X to invoke Phase 2.2 at the
bridge-partner gadget `w`. Builds `S = {v, x_other}` with
`x_other ∈ N(w) \ {v}` (exists because `deg(w) ≥ 3` under OddDegree). -/
private theorem exists_phase22_witness (h : IsCFI' adj) (h_odd : h.OddDegree)
    {w v : Fin h.m} (hv_in_Nw : v ∈ h.H.neighbors w) :
    ∃ (S : Finset (Fin h.m)),
      ∃ (_hS : S ∈ h.H.evenSubsetsOfNeighbors w),
      v ∈ S ∧ ∃ (x : Fin h.m), x ∈ h.H.neighbors w ∧ x ∉ S := by
  -- Step 1: deg(w) ≥ 3 from deg_ge_two + odd.
  have hcard_3 : 3 ≤ (h.H.neighbors w).card := by
    have h_odd_w : (h.H.neighbors w).card % 2 = 1 := h_odd w
    have h_ge_two : 2 ≤ (h.H.neighbors w).card := h.H.degree_ge_two w
    omega
  -- Step 2: pick x_other ∈ N(w) with x_other ≠ v.
  obtain ⟨x_other, hxother_in_Nw, hxother_ne_v⟩ :
      ∃ x ∈ h.H.neighbors w, x ≠ v := by
    by_contra h_no
    push Not at h_no
    have hsub : h.H.neighbors w ⊆ {v} := fun x hx =>
      Finset.mem_singleton.mpr (h_no x hx)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega
  -- Step 3: construct S = {v, x_other}.
  have hSsub : ({v, x_other} : Finset (Fin h.m)) ⊆ h.H.neighbors w := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h1 | h2
    · rw [h1]; exact hv_in_Nw
    · rw [Finset.mem_singleton] at h2
      rw [h2]; exact hxother_in_Nw
  have hScard : ({v, x_other} : Finset (Fin h.m)).card = 2 :=
    Finset.card_pair (fun h => hxother_ne_v h.symm)
  have hS : ({v, x_other} : Finset (Fin h.m)) ∈
      h.H.evenSubsetsOfNeighbors w := by
    rw [h.H.mem_evenSubsetsOfNeighbors]
    exact ⟨hSsub, by rw [hScard]⟩
  have hvS : v ∈ ({v, x_other} : Finset (Fin h.m)) :=
    Finset.mem_insert_self v _
  -- Step 4: pick witness x ∈ N(w) \ S via S ⊊ N(w).
  have h_ssub : ({v, x_other} : Finset (Fin h.m)) ⊂ h.H.neighbors w := by
    refine ⟨hSsub, ?_⟩
    intro h_supset
    have h_eq : ({v, x_other} : Finset (Fin h.m)) = h.H.neighbors w :=
      Finset.Subset.antisymm hSsub h_supset
    rw [h_eq] at hScard
    omega
  obtain ⟨x, hx_in_Nw, hx_notin_S⟩ := Finset.exists_of_ssubset h_ssub
  exact ⟨({v, x_other} : Finset (Fin h.m)), hS, hvS, x, hx_in_Nw, hx_notin_S⟩

end IsCFI'

/-! ### §13.22 — Phase 2.X: b=0 within-gadget partner at round 4

The b=0 analogue of Phase 2.1 (b=1 within-gadget partner at round 2),
but adapted for b=0 — uses Phase 2.2 (round 3) as (P1) rather than M3.C
(round 1).

Apply `refineStep_bridge_step` at χ_3 with b = false:
- (P1): bridge partners e^0_{w→v}, e^0_{w'→v} (b=0 endpoints at gadgets
  w ≠ w', both pointing to v) distinguished by χ_3 via Phase 2.2.
- (P2): for u adj=1 to e^0_{v→w'}, χ_3 u ≠ χ_3 (e^0_{w→v}).
  - u = subset at v: cross-type round-2 lifted to χ_3 (via OddDegree witness).
  - u = bridge partner = e^0_{w'→v}: Phase 2.2 (with witness at w via OddDegree).

Conclusion: refineStep χ_3 distinguishes e^0_{v→w} from e^0_{v→w'},
i.e., χ_4 distinguishes them. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Phase 2.X / refineStep** — b=0 within-gadget partner distinction
at round 4 (OddDegree form).

Under four nested `refineStep` rounds on `χ_{allSeeds}`, b=0 endpoints
at gadget v toward different partners w ≠ w' get distinct colours.

Hypothesis `h.OddDegree` ensures all needed witness subsets exist
automatically (S = {v, x_other} for various v/w/x_other). -/
private theorem refineStep_endpoint_false_intra_gadget_partner_round4
    (h : IsCFI' adj) (h_odd : h.OddDegree) (P : PMatrix n)
    {v w w' : Fin h.m} (hww : w ≠ w')
    (hw : w ∈ h.H.neighbors v) (hw' : w' ∈ h.H.neighbors v) :
    refineStep adj P (refineStep adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds))))
        (h.endpointVertex hw false) ≠
    refineStep adj P (refineStep adj P (refineStep adj P (refineStep adj P
      (individualizedColouring n h.allSeeds))))
        (h.endpointVertex hw' false) := by
  -- Construct Phase 2.2 witness at gadget w (for distinguishing bridge partners).
  obtain ⟨S_w, hS_w, hvS_w, x_w, hx_w_inN, hx_wS⟩ :=
    h.exists_phase22_witness h_odd (h.H.mem_neighbors_symm.mp hw)
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  set χ_2 := refineStep adj P χ_1 with hχ_2
  set χ_3 := refineStep adj P χ_2 with hχ_3
  -- Apply bridge step at χ = χ_3, b = false.
  apply h.refineStep_bridge_step P χ_3 hw hw' false
  · -- (P1): bridge partners e^0_{w→v}, e^0_{w'→v} distinguished by χ_3.
    -- Phase 2.2 at gadgets (w, w') with witness at w.
    have hv_in_Nw : v ∈ h.H.neighbors w := h.H.mem_neighbors_symm.mp hw
    have hv_in_Nw' : v ∈ h.H.neighbors w' := h.H.mem_neighbors_symm.mp hw'
    exact h.refineStep_endpoint_false_inter_gadget_round3
      P hww hv_in_Nw hv_in_Nw' hS_w hvS_w hx_w_inN hx_wS
  · -- (P2): for u adj=1 to e^0_{v→w'}, χ_3 u ≠ χ_3 (e^0_{w→v}).
    intro u hu_adj_ev'
    rw [h.matching, e_endpointVertex] at hu_adj_ev'
    cases h_eu : h.e u with
    | inl sub =>
      -- u is a subset at gadget v containing w'.
      obtain ⟨v_s, ⟨S_u, hSu⟩⟩ := sub
      rw [h_eu] at hu_adj_ev'
      have hc : v_s = v ∧ decide (w' ∈ S_u) ≠ false := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hw' false)
              (Sum.inl ⟨v_s, ⟨S_u, hSu⟩⟩ : h.H.CFIVertex) = 0 := by
          show (if v_s = v ∧ decide (w' ∈ S_u) ≠ false then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hu_adj_ev'
        exact absurd hu_adj_ev' (by decide)
      obtain ⟨hvs_eq, _⟩ := hc
      subst hvs_eq
      have hu_subset : u = h.subsetVertex hSu := by
        apply h.e.injective
        rw [e_subsetVertex, h_eu]
        rfl
      rw [hu_subset]
      -- Construct cross-type witness via OddDegree.
      obtain ⟨y, hy_in_N, hy_notin⟩ := h.exists_witness_of_oddDegree h_odd v_s hSu
      have hv_in_Nw : v_s ∈ h.H.neighbors w := h.H.mem_neighbors_symm.mp hw
      -- Apply cross-type round-2 at χ_2, lift to χ_3 via refineStep_iff.
      have hχ2_ne :
          refineStep adj P χ_1 (h.subsetVertex hSu) ≠
          refineStep adj P χ_1 (h.endpointVertex hv_in_Nw false) :=
        h.refineStep_subsetVertex_ne_endpoint_false_round2
          P hSu hy_in_N hy_notin hv_in_Nw
      intro hχ3_eq
      apply hχ2_ne
      exact ((refineStep_iff adj P χ_2 _ _).mp hχ3_eq).1
    | inr endp =>
      -- u = bridge partner of e^0_{v→w'} = e^0_{w'→v} (b=0 at gadget w').
      obtain ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ := endp
      rw [h_eu] at hu_adj_ev'
      have hc : v = x_e ∧ w' = v_e ∧ false = b_e := by
        by_contra hc
        have hzero :
            h.H.cfiAdj (h.H.endpoint hw' false)
              (Sum.inr ⟨v_e, ⟨x_e, hxe⟩, b_e⟩ : h.H.CFIVertex) = 0 := by
          show (if v = x_e ∧ w' = v_e ∧ false = b_e then 1 else 0) = 0
          rw [if_neg hc]
        rw [hzero] at hu_adj_ev'
        exact absurd hu_adj_ev' (by decide)
      obtain ⟨hxe_eq_v, hwprime_eq_ve, hb_eq⟩ := hc
      have hb_e_false : b_e = false := hb_eq.symm
      subst hb_e_false
      have hu_endp : u = h.endpointVertex hxe false := by
        apply h.e.injective
        rw [e_endpointVertex, h_eu]
        rfl
      rw [hu_endp]
      -- Goal: χ_3 (endpointVertex hxe false) ≠ χ_3 (endpointVertex hv_in_Nw false).
      -- u at gadget v_e (= w') with partner x_e (= v). Need Phase 2.2 with v_phase22 = v_e.
      have hv_in_Nve : v ∈ h.H.neighbors v_e := by
        rw [hxe_eq_v]; exact hxe
      obtain ⟨S_ve, hS_ve, hvS_ve, x_ve, hx_ve_inN, hx_veS⟩ :=
        h.exists_phase22_witness h_odd hv_in_Nve
      -- Need: v_e ≠ w (use hwprime_eq_ve : w' = v_e + hww : w ≠ w').
      have hve_ne_w : v_e ≠ w := by
        intro h_eq
        rw [← hwprime_eq_ve] at h_eq
        exact hww h_eq.symm
      have hv_in_Nw : v ∈ h.H.neighbors w := h.H.mem_neighbors_symm.mp hw
      -- hxe : x_e ∈ N(v_e); with hxe_eq_v : v = x_e, we have hxe : ⟨v⟩ ∈ N(v_e).
      -- Construct witness's containment in S_ve (have hvS_ve : v ∈ S_ve, x_e = v).
      have hxeS_ve : x_e ∈ S_ve := by rw [← hxe_eq_v]; exact hvS_ve
      exact h.refineStep_endpoint_false_inter_gadget_round3
        P hve_ne_w hxe hv_in_Nw hS_ve hxeS_ve hx_ve_inN hx_veS

end IsCFI'

/-! ### §13.23 — Phase 2.4: subset by S at same gadget at round 5

Two subset vertices `a_S^v` and `a_{S'}^v` at the same gadget v differ
in their adjacency patterns when `S ≠ S'`: some `y` exists with
`y ∈ S \ S'` (or vice versa), giving `a_S^v` an adj=1 link to
`e^0_{v→y}` that `a_{S'}^v` lacks.

Direct signature-tuple argument at χ_4. Witness:
`(χ_4 (e^0_{v→y}), 1, P (a_S^v) (e^0_{v→y}))`.
- (a) In `a_S^v`'s χ_4-signature: via u' = `e^0_{v→y}` (adj=1 since y ∈ S).
- (b) Not in `a_{S'}^v`'s χ_4-signature: case on u' adj=1 to `a_{S'}^v`.
  Use `adj_subsetVertex_eq_one_iff` (with `adj_symm`) to characterise
  u' as an endpoint at gadget v with parity-matching.
  - b'' = false: u' = `e^0_{v→x}` for x ∈ S'. Since y ∉ S', x ≠ y.
    Phase 2.X (round 4) distinguishes b=0 same-gadget different-partner.
  - b'' = true: u' = `e^1_{v→x}` for x ∉ S'. M3.B+ (round 1) lifted
    to χ_4 via 3-step `refineStep_iff` chain. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **Phase 2.4 / refineStep** — subset by S at same gadget, round 5.

Under five nested `refineStep` rounds on `χ_{allSeeds}`, two subset
vertices at gadget v with `S ≠ S'` (witnessed by `y ∈ S, y ∉ S'`)
get distinct colours. -/
private theorem refineStep_subset_intra_gadget_S_round5
    (h : IsCFI' adj) (h_odd : h.OddDegree) (P : PMatrix n)
    {v : Fin h.m} {S S' : Finset (Fin h.m)}
    (hS : S ∈ h.H.evenSubsetsOfNeighbors v)
    (hS' : S' ∈ h.H.evenSubsetsOfNeighbors v)
    {y : Fin h.m} (hy_in_Nv : y ∈ h.H.neighbors v)
    (hyS : y ∈ S) (hyS' : y ∉ S') :
    refineStep adj P (refineStep adj P (refineStep adj P (refineStep adj P
      (refineStep adj P (individualizedColouring n h.allSeeds)))))
        (h.subsetVertex hS) ≠
    refineStep adj P (refineStep adj P (refineStep adj P (refineStep adj P
      (refineStep adj P (individualizedColouring n h.allSeeds)))))
        (h.subsetVertex hS') := by
  intro hrefine
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0
  set χ_1 := refineStep adj P χ_0 with hχ_1
  set χ_2 := refineStep adj P χ_1 with hχ_2
  set χ_3 := refineStep adj P χ_2 with hχ_3
  set χ_4 := refineStep adj P χ_3 with hχ_4
  have hboth := (refineStep_iff adj P χ_4 _ _).mp hrefine
  set av := h.subsetVertex hS with hav_def
  set av' := h.subsetVertex hS' with hav'_def
  set ef := h.endpointVertex hy_in_Nv false with hef_def
  let t : Nat × Nat × POE := (χ_4 ef, 1, P av ef)
  -- (a) t ∈ signature χ_4 av — via u' = ef.
  have ht_in_av : t ∈ signature adj P χ_4 av := by
    unfold signature
    rw [Multiset.mem_map]
    refine ⟨ef, ?_, ?_⟩
    · rw [Finset.mem_val, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact h.subsetVertex_ne_endpointVertex hS hy_in_Nv false heq.symm
    · show (χ_4 ef, adj.adj av ef, P av ef) = t
      rw [h.adj_subsetVertex_endpoint_same_gadget_false_of_mem hS hy_in_Nv hyS]
  -- (b) t ∉ signature χ_4 av' — case on u' adj=1 to av'.
  have ht_notin_av' : t ∉ signature adj P χ_4 av' := by
    unfold signature
    rw [Multiset.mem_map]
    rintro ⟨u, _, hu_eq⟩
    have hχu : χ_4 u = χ_4 ef := congrArg Prod.fst hu_eq
    have hrest : (adj.adj av' u, P av' u) = ((1, P av ef) : Nat × POE) :=
      congrArg Prod.snd hu_eq
    have hadj : adj.adj av' u = 1 := congrArg Prod.fst hrest
    rw [h.adj_symm] at hadj
    obtain ⟨x, hx_in_Nv, b, hparity, hu_eq⟩ :=
      (h.adj_subsetVertex_eq_one_iff hS' u).mp hadj
    rw [hu_eq] at hχu
    cases b with
    | false =>
      -- hparity : decide (x ∈ S') ≠ false → x ∈ S'.
      have hxS' : x ∈ S' := by
        by_contra hxS'_neg
        apply hparity
        simp [hxS'_neg]
      have hxy : x ≠ y := by
        intro h_eq
        rw [h_eq] at hxS'
        exact hyS' hxS'
      -- hχu : χ_4 (e^0_x) = χ_4 (e^0_y). Phase 2.X gives ≠.
      exact h.refineStep_endpoint_false_intra_gadget_partner_round4
        h_odd P hxy hx_in_Nv hy_in_Nv hχu
    | true =>
      -- M3.B+ at round 1: χ_1 (e^0_y) ≠ χ_1 (e^1_x). Lift hχu down 3 rounds.
      have hχ1_ne :
          refineStep adj P χ_0 (h.endpointVertex hy_in_Nv false) ≠
          refineStep adj P χ_0 (h.endpointVertex hx_in_Nv true) :=
        h.refineStep_endpoint_b0_ne_b1_general_allSeeds P hx_in_Nv hy_in_Nv
      apply hχ1_ne
      have h3 : χ_3 (h.endpointVertex hx_in_Nv true) =
                χ_3 (h.endpointVertex hy_in_Nv false) :=
        ((refineStep_iff adj P χ_3 _ _).mp hχu).1
      have h2 : χ_2 (h.endpointVertex hx_in_Nv true) =
                χ_2 (h.endpointVertex hy_in_Nv false) :=
        ((refineStep_iff adj P χ_2 _ _).mp h3).1
      have h1 : χ_1 (h.endpointVertex hx_in_Nv true) =
                χ_1 (h.endpointVertex hy_in_Nv false) :=
        ((refineStep_iff adj P χ_1 _ _).mp h2).1
      exact h1.symm
  rw [hboth.2] at ht_in_av
  exact ht_notin_av' ht_in_av

end IsCFI'

/-! ### §13.24 — M4 assembly

Assembles all phase lemmas (M2-M3 + Phase 2.0-2.4) into a single
`Discrete (warmRefine adj P χ_{allSeeds})` proof under `OddDegree`.
Discharges the Tier-1 cascade axiom `cfi_cascades_polynomially` for
the OddDegree CFI class.

The two iteration helpers (`refineStep_iter_le_eq` and
`warmRefine_eq_iter_eq`) used to bridge per-round distinctions to
`warmRefine` are now tier-agnostic and live in `ChainDescent.lean`
§16.4; both Tier 1 (here) and Tier 2 (planned Step 2) use them. -/

namespace IsCFI'

variable {n : Nat} {adj : AdjMatrix n}

/-- **M4 — `cfi_cascades_polynomially` discharged under `OddDegree`.**

For OddDegree CFI graphs (every base vertex has odd degree, ≥ 3),
`warmRefine adj P (individualizedColouring n h.allSeeds)` is `Discrete`.
Hence `CascadesAt adj P (cfi_depth_bound h)` holds with the canonical
seed set witness.

The OddDegree class covers the dominant interesting CFI bases (K₄,
K₃,₃, Petersen). Even-degree bases (Rook3×3) are deferred to future
work — they need additional cascade rounds for saturated subsets.

**Proof structure**: case-split on the base-size dichotomy.
- `h.m = 0`: `CFIVertex` is empty, so `n = 0`; `CascadesAt` is
  vacuous with `S = ∅`.
- `h.m ≥ 1`: `six_baseSize_le` gives `n ≥ 6`, hence `5 ≤ n`. Then
  case-split on vertex types via `h.e`; each case applies a Phase
  lemma at round ≤ 5 and lifts to `warmRefine` via
  `warmRefine_eq_iter_eq`.

The previous `5 ≤ n` hypothesis is now derived from the base-size
dichotomy and so no longer appears. -/
theorem cfi_cascades_polynomially_oddDeg
    (h : IsCFI' adj) (h_odd : h.OddDegree)
    (P : PMatrix n) :
    CascadesAt adj P (cfi_depth_bound h) := by
  -- Establish either `n = 0` (vacuous cascade) or `5 ≤ n` from the
  -- combinatorial fact `n = 0 ∨ 6 ≤ n` (proved via `six_baseSize_le`
  -- combined with `h.m = 0 → n = 0` from the CFI bijection).
  by_cases hm0 : h.m = 0
  · -- m = 0: every gadget index is uninhabited, so cfiVertexCount = 0,
    -- so n = 0 (via the bijection h.e : Fin n ≃ CFIVertex).
    have hcvc : h.H.cfiVertexCount = 0 := by
      unfold CFIBase.cfiVertexCount
      apply Finset.sum_eq_zero
      intro v _
      exfalso
      have := v.isLt
      omega
    have hn_eq : n = 0 := by
      have hc : Fintype.card (Fin n) = Fintype.card h.H.CFIVertex :=
        Fintype.card_congr h.e
      rw [Fintype.card_fin, h.H.card_CFIVertex, hcvc] at hc
      exact hc
    refine ⟨∅, by simp, ?_⟩
    intro i _ _
    exfalso
    have := i.isLt
    omega
  -- m ≥ 1: from `six_baseSize_le`, `6 ≤ n`, hence `5 ≤ n`.
  have hn_ge_5 : 5 ≤ n := by
    have hm_pos : 0 < h.m := Nat.pos_of_ne_zero hm0
    have h6 : 6 * h.m ≤ n := h.six_baseSize_le
    omega
  refine ⟨h.allSeeds, le_of_eq h.allSeeds_card, ?_⟩
  intro i j hwarm
  by_contra hne
  have he_ne : h.e i ≠ h.e j := fun h_eq => hne (h.e.injective h_eq)
  set χ_0 := individualizedColouring n h.allSeeds with hχ_0_def
  -- Convert hwarm to iterate-r form for various r ≤ 5.
  have lift1 : ((refineStep adj P)^[1]) χ_0 i = ((refineStep adj P)^[1]) χ_0 j :=
    warmRefine_eq_iter_eq adj P χ_0 1 (by omega) hwarm
  have lift2 : ((refineStep adj P)^[2]) χ_0 i = ((refineStep adj P)^[2]) χ_0 j :=
    warmRefine_eq_iter_eq adj P χ_0 2 (by omega) hwarm
  have lift3 : ((refineStep adj P)^[3]) χ_0 i = ((refineStep adj P)^[3]) χ_0 j :=
    warmRefine_eq_iter_eq adj P χ_0 3 (by omega) hwarm
  have lift4 : ((refineStep adj P)^[4]) χ_0 i = ((refineStep adj P)^[4]) χ_0 j :=
    warmRefine_eq_iter_eq adj P χ_0 4 (by omega) hwarm
  have lift5 : ((refineStep adj P)^[5]) χ_0 i = ((refineStep adj P)^[5]) χ_0 j :=
    warmRefine_eq_iter_eq adj P χ_0 5 (by omega) hwarm
  -- Unfold iterates to nested refineStep form for matching phase lemma outputs.
  simp only [Function.iterate_succ_apply',
    Function.iterate_zero_apply] at lift1 lift2 lift3 lift4 lift5
  -- Case-split on h.e i, h.e j.
  cases h_eu_i : h.e i with
  | inl sub_i =>
    obtain ⟨v_i, ⟨S_i, hSi⟩⟩ := sub_i
    have hi_eq : i = h.subsetVertex hSi := by
      apply h.e.injective; rw [e_subsetVertex, h_eu_i]; rfl
    cases h_eu_j : h.e j with
    | inl sub_j =>
      -- subset/subset
      obtain ⟨v_j, ⟨S_j, hSj⟩⟩ := sub_j
      have hj_eq : j = h.subsetVertex hSj := by
        apply h.e.injective; rw [e_subsetVertex, h_eu_j]; rfl
      by_cases hvij : v_i = v_j
      · -- Same gadget. Phase 2.4.
        subst hvij
        have hSij : S_i ≠ S_j := by
          intro hSij_eq
          apply he_ne
          rw [h_eu_i, h_eu_j]
          subst hSij_eq
          rfl
        have h_or : (∃ y ∈ S_i, y ∉ S_j) ∨ (∃ y ∈ S_j, y ∉ S_i) := by
          by_contra h_no
          push Not at h_no
          exact hSij (Finset.Subset.antisymm h_no.1 h_no.2)
        rcases h_or with ⟨y, hy_in_Si, hy_notin_Sj⟩ |
                          ⟨y, hy_in_Sj, hy_notin_Si⟩
        · have hy_in_Nv : y ∈ h.H.neighbors v_i :=
            (h.H.mem_evenSubsetsOfNeighbors.mp hSi).1 hy_in_Si
          apply h.refineStep_subset_intra_gadget_S_round5
            h_odd P hSi hSj hy_in_Nv hy_in_Si hy_notin_Sj
          rw [← hi_eq, ← hj_eq]; exact lift5
        · have hy_in_Nv : y ∈ h.H.neighbors v_i :=
            (h.H.mem_evenSubsetsOfNeighbors.mp hSj).1 hy_in_Sj
          apply h.refineStep_subset_intra_gadget_S_round5
            h_odd P hSj hSi hy_in_Nv hy_in_Sj hy_notin_Si
          rw [← hi_eq, ← hj_eq]; exact lift5.symm
      · -- Different gadget. Phase 2.3.
        obtain ⟨x, hx_in_Nv, hx_notin_Si⟩ :=
          h.exists_witness_of_oddDegree h_odd v_i hSi
        apply h.refineStep_subset_inter_gadget_round2
          P hvij hSi hSj hx_in_Nv hx_notin_Si
        rw [← hi_eq, ← hj_eq]; exact lift2
    | inr endp_j =>
      -- subset/endpoint cross-type
      obtain ⟨v_j, ⟨w_j, hwj⟩, b_j⟩ := endp_j
      have hj_eq : j = h.endpointVertex hwj b_j := by
        apply h.e.injective; rw [e_endpointVertex, h_eu_j]; rfl
      cases b_j with
      | true =>
        -- M3.B++ at round 1.
        apply h.refineStep_subsetVertex_ne_endpoint_true_allSeeds P hwj hSi
        rw [← hi_eq, ← hj_eq]; exact lift1
      | false =>
        -- Cross-type round 2.
        obtain ⟨y, hy_in_Nv, hy_notin_Si⟩ :=
          h.exists_witness_of_oddDegree h_odd v_i hSi
        apply h.refineStep_subsetVertex_ne_endpoint_false_round2
          P hSi hy_in_Nv hy_notin_Si hwj
        rw [← hi_eq, ← hj_eq]; exact lift2
  | inr endp_i =>
    obtain ⟨v_i, ⟨w_i, hwi⟩, b_i⟩ := endp_i
    have hi_eq : i = h.endpointVertex hwi b_i := by
      apply h.e.injective; rw [e_endpointVertex, h_eu_i]; rfl
    cases h_eu_j : h.e j with
    | inl sub_j =>
      -- endpoint/subset (symmetric to subset/endpoint via .symm)
      obtain ⟨v_j, ⟨S_j, hSj⟩⟩ := sub_j
      have hj_eq : j = h.subsetVertex hSj := by
        apply h.e.injective; rw [e_subsetVertex, h_eu_j]; rfl
      cases b_i with
      | true =>
        apply (h.refineStep_subsetVertex_ne_endpoint_true_allSeeds P hwi hSj).symm
        rw [← hi_eq, ← hj_eq]; exact lift1
      | false =>
        obtain ⟨y, hy_in_Nv, hy_notin_Sj⟩ :=
          h.exists_witness_of_oddDegree h_odd v_j hSj
        apply (h.refineStep_subsetVertex_ne_endpoint_false_round2
          P hSj hy_in_Nv hy_notin_Sj hwi).symm
        rw [← hi_eq, ← hj_eq]; exact lift2
    | inr endp_j =>
      -- endpoint/endpoint
      obtain ⟨v_j, ⟨w_j, hwj⟩, b_j⟩ := endp_j
      have hj_eq : j = h.endpointVertex hwj b_j := by
        apply h.e.injective; rw [e_endpointVertex, h_eu_j]; rfl
      cases b_i with
      | false => cases b_j with
        | false =>
          -- Both b=false.
          by_cases hvij : v_i = v_j
          · -- Same gadget. Phase 2.X (round 4).
            subst hvij
            have hwij : w_i ≠ w_j := by
              intro hwij_eq
              apply he_ne
              rw [h_eu_i, h_eu_j]
              subst hwij_eq
              rfl
            apply h.refineStep_endpoint_false_intra_gadget_partner_round4
              h_odd P hwij hwi hwj
            rw [← hi_eq, ← hj_eq]; exact lift4
          · -- Different gadget. Phase 2.2 (round 3) with witness via OddDegree.
            obtain ⟨S_w, _hS_w, hw_in_Sw, x_w, hx_w_in, hx_w_not⟩ :=
              h.exists_phase22_witness h_odd hwi
            apply h.refineStep_endpoint_false_inter_gadget_round3
              P hvij hwi hwj _hS_w hw_in_Sw hx_w_in hx_w_not
            rw [← hi_eq, ← hj_eq]; exact lift3
        | true =>
          -- b_i=false, b_j=true. M3.B+ (round 1).
          apply (h.refineStep_endpoint_b0_ne_b1_general_allSeeds P hwj hwi)
          rw [← hi_eq, ← hj_eq]; exact lift1
      | true => cases b_j with
        | false =>
          -- b_i=true, b_j=false. M3.B+ (round 1) with .symm.
          apply (h.refineStep_endpoint_b0_ne_b1_general_allSeeds P hwi hwj).symm
          rw [← hi_eq, ← hj_eq]; exact lift1
        | true =>
          -- Both b=true.
          by_cases hvij : v_i = v_j
          · -- Same gadget. Phase 2.1 (round 2).
            subst hvij
            have hwij : w_i ≠ w_j := by
              intro hwij_eq
              apply he_ne
              rw [h_eu_i, h_eu_j]
              subst hwij_eq
              rfl
            apply h.refineStep_endpoint_true_intra_gadget_partner
              P hwij hwi hwj
            rw [← hi_eq, ← hj_eq]; exact lift2
          · -- Different gadget. M3.C (round 1).
            apply h.refineStep_endpoint_true_inter_gadget P hvij hwi hwj
            rw [← hi_eq, ← hj_eq]; exact lift1

/-- **Theorem 1 (CFI form, OddDegree, axiom-free).** Orbit recovery
for OddDegree CFI graphs at depth ≤ `h.baseSize`. Unlike
`theorem_1_HOR_cfi`, this is **conditional on neither**
`cfi_cascades_polynomially` (discharged by M4) nor any other CFI axiom
— only the `OddDegree` hypothesis.

The earlier `5 ≤ n` side condition has been discharged inside
`cfi_cascades_polynomially_oddDeg` via the base-size dichotomy
(`h.m = 0 → n = 0` ∨ `h.m ≥ 1 → 6 ≤ n`), so it no longer needs to
be supplied here. -/
theorem theorem_1_HOR_cfi_oddDeg {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ cfi_depth_bound h ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w :=
  theorem_1_HOR_at_depth (h.cfi_cascades_polynomially_oddDeg h_odd P)

end IsCFI'

/-! ## §15 — Stage 3: gadget-flip automorphisms (the `Z₂^β` generators)

The `Aut(CFI(H)) ≅ Z₂^{β_H} ⋊ Aut(H)` structure (file header, Stage 3) is needed
downstream only for its **existence half** — the `Z₂^β` generators, *not* the full
isomorphism (whose hard surjectivity content no consumer needs). The two consumers both
want the *same* object, a CFI automorphism with controlled support:

- the **linear oracle** (`LinearOracle.configSwap_of_aut` ⟶ `configSwapRecoverable_of_cfi`)
  wants an involution swapping a decision pair, fixing the seeds, preserving the direction
  assignment off the pair;
- **Tier-3a B1** (`Cascade.cascadeComposition_pathFixing`'s `hwit`) wants a `P`-preserving
  automorphism with support disjoint from the committed set, sending `v ↦ w`.

Both are realised by the **cycle-space flip**: for an edge set of `H` in which every vertex
has even degree (`F` an even subgraph = an element of the GF(2) cycle space), the involution
that toggles endpoint parities along `F` and complements subset membership by the `F`-incident
neighbours. The even-degree condition is exactly what keeps subset vertices' even-cardinality
invariant — so the construction earns the cycle space rather than single edges.

This section builds the construction (Phase 1) and validates it on `triangleBase` (Phase 0);
the adjacency-preservation proof (Phase 2), the `Fin n` lift (Phase 3), support/locality
(Phase 4), `P`-preservation (Phase 5) and the consumer wiring (Phase 6) follow. The
construction is **class-agnostic** (any `CFIBase`, any even subgraph) — odd degree enters only
downstream, where the decision-pair existence (cascade-1b) is discharged. -/

/-- **Parity of a symmetric-difference cardinality.** `|S ∆ T| ≡ |S| + |T| (mod 2)`. The
algebraic fact behind "an even subgraph preserves the even-subset invariant." -/
private theorem card_symmDiff_mod_two {α : Type*} [DecidableEq α] (S T : Finset α) :
    (symmDiff S T).card % 2 = (S.card + T.card) % 2 := by
  have key : (symmDiff S T).card + 2 * (S ∩ T).card = S.card + T.card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have h1 := Finset.card_sdiff_add_card_inter S T
    have h2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at h2
    omega
  omega

namespace CFIBase

variable {m : Nat} (H : CFIBase m)

/-! ### Phase 1 — the cycle-space flip on `CFIVertex H` -/

/-- The `F`-incident neighbours of `v`: neighbours `w ∈ N(v)` with the flip-edge indicator
`F v w` set. `F : Fin m → Fin m → Bool` represents a subgraph of `H`; `flipSet F v` is the set
of `v`-incident flip edges, viewed as a subset of `N(v)`. -/
def flipSet (F : Fin m → Fin m → Bool) (v : Fin m) : Finset (Fin m) :=
  (H.neighbors v).filter (fun w => F v w = true)

/-- `flipSet F v ⊆ N(v)`. -/
theorem flipSet_subset (F : Fin m → Fin m → Bool) (v : Fin m) :
    H.flipSet F v ⊆ H.neighbors v :=
  Finset.filter_subset _ _

/-- Membership in the flip set. -/
@[simp] theorem mem_flipSet {F : Fin m → Fin m → Bool} {v w : Fin m} :
    w ∈ H.flipSet F v ↔ w ∈ H.neighbors v ∧ F v w = true := by
  simp [flipSet]

/-- **The even subgraph preserves the even-subset invariant.** If every `flipSet F v` has even
cardinality (`F` an even subgraph), then `S ∆ flipSet F v` is again an even subset of `N(v)`. -/
theorem symmDiff_flipSet_mem_even (F : Fin m → Fin m → Bool)
    (hEven : ∀ v, (H.flipSet F v).card % 2 = 0)
    {v : Fin m} {S : Finset (Fin m)} (hS : S ∈ H.evenSubsetsOfNeighbors v) :
    symmDiff S (H.flipSet F v) ∈ H.evenSubsetsOfNeighbors v := by
  rw [mem_evenSubsetsOfNeighbors] at hS ⊢
  obtain ⟨hSsub, hScard⟩ := hS
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with ⟨hxS, _⟩ | ⟨hxf, _⟩
    · exact hSsub hxS
    · exact H.flipSet_subset F v hxf
  · have hF := hEven v
    rw [card_symmDiff_mod_two]
    omega

/-- **The cycle-space gadget flip** on `CFIVertex H`, for an even subgraph `F`. Toggles every
endpoint parity along an `F`-edge (`e^b_{v→w} ↦ e^{b ⊕ F v w}_{v→w}`) and complements each
subset vertex by its `F`-incident neighbours (`a_S^v ↦ a_{S ∆ flipSet F v}^v`). The
even-subgraph hypothesis keeps the subset image even. -/
def cfiFlip (F : Fin m → Fin m → Bool)
    (hEven : ∀ v, (H.flipSet F v).card % 2 = 0) :
    H.CFIVertex → H.CFIVertex
  | Sum.inl ⟨v, S, hS⟩ =>
      Sum.inl ⟨v, symmDiff S (H.flipSet F v), H.symmDiff_flipSet_mem_even F hEven hS⟩
  | Sum.inr ⟨v, ⟨w, hw⟩, b⟩ =>
      Sum.inr ⟨v, ⟨w, hw⟩, xor b (F v w)⟩

/-- **The gadget flip is an involution.** Flipping along `F` twice restores every vertex:
`(S ∆ F) ∆ F = S` on subsets, `(b ⊕ c) ⊕ c = b` on endpoint parities. -/
theorem cfiFlip_involutive (F : Fin m → Fin m → Bool)
    (hEven : ∀ v, (H.flipSet F v).card % 2 = 0) :
    Function.Involutive (H.cfiFlip F hEven) := by
  rintro (⟨v, S, hS⟩ | ⟨v, ⟨w, hw⟩, b⟩)
  · simp only [cfiFlip, symmDiff_symmDiff_cancel_right]
  · simp only [cfiFlip]
    cases b <;> cases hF : F v w <;> rfl

/-- The gadget flip packaged as a permutation of `CFIVertex H` (it is its own inverse). -/
def cfiFlipEquiv (F : Fin m → Fin m → Bool)
    (hEven : ∀ v, (H.flipSet F v).card % 2 = 0) :
    Equiv.Perm H.CFIVertex :=
  Function.Involutive.toPerm _ (H.cfiFlip_involutive F hEven)

end CFIBase

/-! ### Phase 0 — `triangleBase` prototype (β = 1: the single 3-cycle)

`triangleBase = K₃` has cycle-space dimension `β = |E| − |V| + 1 = 3 − 3 + 1 = 1`: the unique
nontrivial gadget flip is the all-edges flip `F = (i ≠ j)`. (Triangle is even-degree, so it
tests the *construction mechanics* only, not the odd-degree completeness path — exactly the
cheap de-risking we want before the general Phase 2 proof.) -/

/-- The triangle's unique nontrivial even subgraph: all three edges. -/
def triFlipEdges : Fin 3 → Fin 3 → Bool := fun i j => decide (i ≠ j)

/-- The triangle's flip set at every vertex is its 2-element neighbourhood — even. -/
theorem triFlip_even : ∀ v, (triangleBase.flipSet triFlipEdges v).card % 2 = 0 := by decide

/-- **Phase-0 smoke test (involution).** The triangle gadget flip is an involution
(decidable pointwise form). -/
theorem triFlip_involutive_check :
    ∀ x : triangleBase.CFIVertex,
      triangleBase.cfiFlip triFlipEdges triFlip_even
          (triangleBase.cfiFlip triFlipEdges triFlip_even x) = x := by decide

/-- **Phase-0 smoke test (the crux: it is an automorphism).** The triangle gadget flip
preserves `cfiAdj` on all `18 × 18` vertex pairs — validating the cycle-flip-is-automorphism
computation on the smallest case before the general Phase-2 proof. -/
theorem triFlip_isAut_check :
    ∀ x y : triangleBase.CFIVertex,
      triangleBase.cfiAdj (triangleBase.cfiFlip triFlipEdges triFlip_even x)
          (triangleBase.cfiFlip triFlipEdges triFlip_even y)
        = triangleBase.cfiAdj x y := by decide

/-- **Phase-0 smoke test (nontriviality).** The triangle gadget flip genuinely moves some
vertex (e.g. flips an endpoint parity), so it witnesses a nontrivial automorphism of
`CFI(triangle)`. -/
theorem triFlip_nontrivial :
    ∃ x : triangleBase.CFIVertex,
      triangleBase.cfiFlip triFlipEdges triFlip_even x ≠ x := by decide

end ChainDescent
