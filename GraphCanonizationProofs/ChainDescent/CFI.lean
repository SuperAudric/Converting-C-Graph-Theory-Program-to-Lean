import ChainDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum

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

`native_decide` is required: kernel `decide` chokes on the Fintype
instance's `Finset.attach`-based enumeration. The native-compiled
form reduces in milliseconds. -/
example : Fintype.card triangleBase.SubsetVertex = 6 := by native_decide

/-- Triangle's endpoint vertices: 12 total (3 × 2 × 2). -/
example : Fintype.card triangleBase.EndpointVertex = 12 := by native_decide

/-- Triangle's full CFI vertex type: 18 elements, matching `cfiVertexCount`. -/
theorem triangleBase_cfiVertex_card :
    Fintype.card triangleBase.CFIVertex = 18 := by native_decide

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
theorem card_evenSubsetsOfNeighbors (v : Fin m) :
    (H.evenSubsetsOfNeighbors v).card = 2 ^ (H.degree v - 1) := by
  have hnonempty : (H.neighbors v).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < H.degree v
    have := H.degree_ge_two v
    omega
  exact Finset.card_powerset_filter_even hnonempty

/-- `Fintype.card SubsetVertex = ∑ v, 2^(degree v - 1)`. -/
theorem card_SubsetVertex :
    Fintype.card H.SubsetVertex = ∑ v, 2 ^ (H.degree v - 1) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_coe]
  exact H.card_evenSubsetsOfNeighbors v

/-- `Fintype.card EndpointVertex = ∑ v, 2 * degree v`. -/
theorem card_EndpointVertex :
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

end ChainDescent
