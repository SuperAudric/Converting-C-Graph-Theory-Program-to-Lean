import FullCorrectness.Isomorphic

/-!
# §3  Pipeline equivariance under `Aut G`  (scaffolding)

This module sets up the permutation action on the canonizer's intermediate data
structures (`PathSegment`, `PathsBetween`, `PathsFrom`, `PathState`, `RankState`)
and states the four equivariance theorems (Stages A–D) described in the plan.

All four theorems are quantified over `σ ∈ Aut G`, **not** arbitrary `σ : Equiv.Perm (Fin n)`.
This is the key correction over the old flat proof: `breakTie` is only equivariant under
automorphisms, because only automorphisms preserve the Aut(G)-orbit structure that
`breakTie`'s tied-vertex set lives in.

## Status
- Action definitions: defined below.
- Stage A (`initializePaths_Aut_equivariant`):       stated; proof pending.
- Stage B (`calculatePathRankings_Aut_equivariant`): stated; proof pending.
- Stage C (`orderVertices_Aut_equivariant`):         stated; proof pending (depends on §6).
- Stage D (`labelEdges_Aut_equivariant`):            stated; proof pending (depends on §7).

Stage A is self-contained and can be tackled first. Stages B–D build on it and on each
other, and on §6/§7 as noted.

## Type-system streamlining (algorithm refactor)

After switching `PathSegment`/`PathsBetween`/`PathsFrom`/`PathState` to be parametrized
by `vertexCount` with `Fin vertexCount`-typed vertex slots (and `VertexType`/`EdgeType`
to `Nat`), the per-element action on `PathSegment` is just `σ.toFun` applied to each
vertex slot — no `Nat → Nat` lift, no out-of-range branching. The remaining permutation
work lives in the *positional* re-indexing of `connectedSubPaths`/`pathsToVertex` (which
are still `List`s with positionally-meaningful entries), and that uses `Nat` positions
because `List` is `Nat`-indexed. That residual `Nat`-position bookkeeping is captured by
the small `permNat` helper below. The `n = 0` case is handled by an explicit pattern
match on `n` in each `.permute` definition (avoiding any `Inhabited`/`NeZero` plumbing).
-/

namespace Graph

variable {n : Nat}

/-! ## Permutation action on `Nat` positions (positional re-indexing) -/

def permNat (σ : Equiv.Perm (Fin n)) (i : Nat) : Nat :=
  if h : i < n then (σ ⟨i, h⟩).val else i

@[simp] theorem permNat_one (i : Nat) : permNat (n := n) 1 i = i := by
  unfold permNat; split <;> simp

theorem permNat_lt {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ i < n := by
  unfold permNat; simp [h, (σ ⟨i, h⟩).isLt]

theorem permNat_of_lt {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ i = (σ ⟨i, h⟩).val := by
  unfold permNat; simp [h]

theorem permNat_of_ge {σ : Equiv.Perm (Fin n)} {i : Nat} (h : n ≤ i) :
    permNat σ i = i := by
  unfold permNat; simp [Nat.not_lt.mpr h]

@[simp] theorem permNat_inv_perm {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ⁻¹ (permNat σ i) = i := by
  rw [permNat_of_lt h, permNat_of_lt (σ ⟨i, h⟩).isLt]
  show (σ⁻¹ (σ ⟨i, h⟩)).val = i
  simp

@[simp] theorem permNat_perm_inv {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ (permNat σ⁻¹ i) = i := by
  rw [permNat_of_lt h, permNat_of_lt (σ⁻¹ ⟨i, h⟩).isLt]
  show (σ (σ⁻¹ ⟨i, h⟩)).val = i
  simp

@[simp] theorem permNat_fin (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permNat σ i.val = (σ i).val := by
  rw [permNat_of_lt i.isLt]

/-! ## Permutation action on path structures

Each vertex slot (now `Fin n`-typed in the structure definitions) is mapped through `σ`
directly. Positional re-indexing (for `connectedSubPaths`/`pathsToVertex`) uses `permNat`
on the `Nat` list positions. The `n = 0` case is handled by an explicit pattern match,
giving us a valid default value (`.bottom 0`, etc.) in the `n ≥ 1` branch where the
default is needed. -/

/-- Relabel the vertex indices inside a `PathSegment n`. -/
def PathSegment.permute (σ : Equiv.Perm (Fin n)) : PathSegment n → PathSegment n
  | .bottom v            => .bottom (σ v)
  | .inner e d s mid     => .inner e d (σ s) (σ mid)

/--
Relabel vertex indices inside a `PathsBetween n`. Depth is unchanged.

For `depth = 0`, `connectedSubPaths` is either `[.bottom v]` or `[]` — `List.map` suffices.
For `depth > 0`, `connectedSubPaths` has length `n` (one entry per intermediate vertex);
we reindex by `σ⁻¹` and apply `PathSegment.permute σ`. The `n = 0` case is degenerate:
no `Fin 0` value exists, so the structure carries no information and we return as-is.
-/
def PathsBetween.permute : {n : Nat} → Equiv.Perm (Fin n) → PathsBetween n → PathsBetween n
  | 0,     _, p => p
  | k + 1, σ, p =>
    { depth             := p.depth
      startVertexIndex  := σ p.startVertexIndex
      endVertexIndex    := σ p.endVertexIndex
      connectedSubPaths :=
        if p.depth = 0 then
          p.connectedSubPaths.map (PathSegment.permute σ)
        else
          (List.finRange (k + 1)).map fun i =>
            PathSegment.permute σ
              (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (.bottom 0)) }

/--
Relabel vertex indices inside a `PathsFrom n`, **reordering the `pathsToVertex` list** so
that the entry describing paths ending at new-vertex `e` sits at list position `e`.
-/
def PathsFrom.permute : {n : Nat} → Equiv.Perm (Fin n) → PathsFrom n → PathsFrom n
  | 0,     _, p => p
  | k + 1, σ, p =>
    { depth            := p.depth
      startVertexIndex := σ p.startVertexIndex
      pathsToVertex    :=
        (List.finRange (k + 1)).map fun i =>
          PathsBetween.permute σ
            (p.pathsToVertex.getD (permNat σ⁻¹ i.val)
              { depth := 0, startVertexIndex := 0, endVertexIndex := 0, connectedSubPaths := [] }) }

/--
Relabel a full `PathState n` by `σ`. Slot `s` in the output (at any depth) is the σ-permuted
image of slot `σ.symm s` in the input — consistent with `AdjMatrix.permute`, which defines
`(G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j)`.
-/
def PathState.permute : {n : Nat} → Equiv.Perm (Fin n) → PathState n → PathState n
  | 0,     _, st => st
  | k + 1, σ, st =>
    { pathsOfLength := st.pathsOfLength.map fun pathsByStart =>
        (Array.range (k + 1)).map fun newStart =>
          let oldStart := permNat σ⁻¹ newStart
          PathsFrom.permute σ (pathsByStart.getD oldStart
            { depth := 0, startVertexIndex := 0, pathsToVertex := [] }) }

/-- Relabel a `RankState` by `σ`: slot `(d, s, e)` / `(d, s)` in the output is the value
at `(d, σ.symm s, σ.symm e)` / `(d, σ.symm s)` in the input. -/
def RankState.permute (σ : Equiv.Perm (Fin n)) (rs : RankState) : RankState :=
  let nDepth := rs.fromRanks.size
  { betweenRanks :=
      (Array.range nDepth).map fun d =>
        let slice := rs.betweenRanks.getD d #[]
        (Array.range n).map fun s =>
          let origStart := permNat σ⁻¹ s
          let row := slice.getD origStart #[]
          (Array.range n).map fun e => row.getD (permNat σ⁻¹ e) 0
    fromRanks :=
      (Array.range nDepth).map fun d =>
        let slice := rs.fromRanks.getD d #[]
        (Array.range n).map fun s => slice.getD (permNat σ⁻¹ s) 0 }

/-! ## Structural sanity lemmas -/

@[simp] theorem initializePaths_pathsOfLength_size (G : AdjMatrix n) :
    (initializePaths G).pathsOfLength.size = n := by
  unfold initializePaths
  simp

@[simp] theorem PathState_permute_pathsOfLength_size
    (σ : Equiv.Perm (Fin n)) (st : PathState n) :
    (PathState.permute σ st).pathsOfLength.size = st.pathsOfLength.size := by
  cases n with
  | zero => rfl
  | succ k => simp [PathState.permute]

/-- For `d < n`, the depth-`d` slice of `(initializePaths G).pathsOfLength` is a length-`n`
array of `PathsFrom` records, indexed by start vertex. -/
theorem initializePaths_pathsOfLength_get_size
    (G : AdjMatrix n) {d : Nat} (hd : d < n) :
    ((initializePaths G).pathsOfLength[d]'(by simp; exact hd)).size = n := by
  unfold initializePaths
  simp

/-! ## §3 Stage A — `initializePaths` equivariance

**Theorem.** For *any* `σ : Equiv.Perm (Fin n)` — no `Aut G` hypothesis needed — the path
state built for `G.permute σ` equals the σ-relabeling of the path state built for `G`:

```
initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)
```

**Why this is now (much) more tractable.** With vertex-typed slots (`Fin n`) the inner
`PathSegment` action is `σ`-applied, eliminating the entire `permNat` lift on stored
indices. The remaining work is positional re-indexing of the `connectedSubPaths` (depth>0)
and `pathsToVertex` lists, which is structurally the same regardless of the storage type
of indices: at each list position `i` in the new labeling, we want the σ-permuted version
of the old position `σ⁻¹ i`. -/

theorem initializePaths_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) :
    initializePaths (G.permute σ) = PathState.permute σ (initializePaths G) := by
  sorry

/-! ## §3 Stage B — `calculatePathRankings` equivariance -/

theorem calculatePathRankings_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    calculatePathRankings (PathState.permute σ (initializePaths G)) vts
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts) := by
  sorry

/-! ## §4 — `convergeLoop` preserves Aut(G)-invariance -/

theorem convergeOnce_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0) :
    ∀ v : Fin n,
      (convergeOnce (initializePaths G) vts).1.getD (σ v).val 0 =
      (convergeOnce (initializePaths G) vts).1.getD v.val 0 := by
  sorry

theorem convergeLoop_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType) (fuel : Nat)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0) :
    ∀ v : Fin n,
      (convergeLoop (initializePaths G) vts fuel).getD (σ v).val 0 =
      (convergeLoop (initializePaths G) vts fuel).getD v.val 0 := by
  induction fuel generalizing vts with
  | zero =>
    intro v
    show vts.getD (σ v).val 0 = vts.getD v.val 0
    exact hvts v
  | succ k ih =>
    have hStep := convergeOnce_Aut_invariant G σ hσ vts hvts
    intro v
    change (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD (σ v).val 0 =
           (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD v.val 0
    split
    · exact ih _ hStep v
    · exact hStep v

theorem convergeLoop_zeros_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G) (fuel : Nat) :
    ∀ v : Fin n,
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD (σ v).val 0 =
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD v.val 0 := by
  apply convergeLoop_Aut_invariant G σ hσ
  intro v
  simp [v.isLt, (σ v).isLt]

/-! ## §3 Stage C — `orderVertices` equivariance -/

theorem orderVertices_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    orderVertices (PathState.permute σ (initializePaths G)) vts
      = orderVertices (initializePaths G) vts := by
  sorry

/-! ## §3 Stage D — `labelEdgesAccordingToRankings` equivariance -/

theorem labelEdges_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    labelEdgesAccordingToRankings vts (G.permute σ)
      = labelEdgesAccordingToRankings vts G := by
  sorry

end Graph
