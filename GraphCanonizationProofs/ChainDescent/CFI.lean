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
theorem adj_seed_endpoint_diff_gadget (h : IsCFI' adj)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v') (b : Bool) :
    adj.adj (h.seedVertex v) (h.endpointVertex hw b) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex]
  exact h.H.cfiAdj_aEmpty_endpoint_diff_gadget hw b hvv

/-- Symmetric: `adj (endpointVertex v' w b) (seedVertex v) = 0` when
v ≠ v'. -/
theorem adj_endpoint_seed_diff_gadget (h : IsCFI' adj)
    {v v' : Fin h.m} (hvv : v ≠ v')
    {w : Fin h.m} (hw : w ∈ h.H.neighbors v') (b : Bool) :
    adj.adj (h.endpointVertex hw b) (h.seedVertex v) = 0 := by
  rw [h.matching, e_seedVertex, e_endpointVertex, h.H.cfiAdj_symm]
  exact h.H.cfiAdj_aEmpty_endpoint_diff_gadget hw b hvv

/-- **Bridge adjacency (Fin n)**: the endpoint `e^b_{v→w}` is adjacent
to its bridge partner `e^b_{w→v}`. Lifts `CFIBase.cfiAdj_bridge`
through `h.matching`. -/
theorem adj_bridge (h : IsCFI' adj) {v w : Fin h.m}
    (hw : w ∈ h.H.neighbors v) (b : Bool) :
    adj.adj (h.endpointVertex hw b)
            (h.endpointVertex (h.H.mem_neighbors_symm.mp hw) b) = 1 := by
  rw [h.matching, e_endpointVertex, e_endpointVertex]
  exact h.H.cfiAdj_bridge hw b

/-- **Endpoint distinct from its bridge partner.** The endpoint at
gadget `v` and the endpoint at gadget `w` (its bridge partner) are
distinct `Fin n` vertices, because `v ≠ w` follows from `w ∈ N(v)` +
looplessness. -/
theorem endpointVertex_ne_bridge (h : IsCFI' adj) {v w : Fin h.m}
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
theorem individualizedColouring_singleton_self_pos {n : Nat} (seed : Fin n) :
    individualizedColouring n {seed} seed ≠ 0 := by
  rw [individualizedColouring_singleton_self]
  exact Nat.succ_ne_zero _

/-- **Uniqueness**: `individualizedColouring n {seed} u = individualizedColouring n {seed} seed`
iff `u = seed`. The forward direction is the key fact powering M2's
signature distinction — only the seed has the fresh colour. -/
theorem individualizedColouring_singleton_eq_seed_iff {n : Nat}
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
theorem signature_endpoint_false_ne_true (h : IsCFI' adj) (P : PMatrix n)
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
theorem refineStep_endpoint_false_ne_true (h : IsCFI' adj) (P : PMatrix n)
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
noncomputable def allSeeds (h : IsCFI' adj) : Finset (Fin n) :=
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
theorem allSeeds_card_le_baseSize (h : IsCFI' adj) :
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
theorem signature_endpoint_false_ne_true_allSeeds (h : IsCFI' adj)
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
theorem refineStep_endpoint_false_ne_true_allSeeds (h : IsCFI' adj)
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
theorem signature_endpoint_true_inter_gadget (h : IsCFI' adj) (P : PMatrix n)
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
theorem refineStep_endpoint_true_inter_gadget (h : IsCFI' adj)
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
theorem signature_bridge_step (h : IsCFI' adj) (P : PMatrix n)
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
theorem refineStep_bridge_step (h : IsCFI' adj) (P : PMatrix n)
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

end ChainDescent
