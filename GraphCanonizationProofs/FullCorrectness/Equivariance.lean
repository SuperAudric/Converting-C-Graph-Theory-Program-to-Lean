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

/-! #### Helpers for Stage A's `succ` case [Stage A]

These lemmas factor out the per-depth and per-(depth, start) equalities so the main
theorem can chain them via `Array.ext`. Each helper shows that a single slot of the
expected shape on the left equals the corresponding `permute`-image of the right. -/

/-- For `n = k + 1` and any `Fin (k+1)`-indexed path data, `permNat σ⁻¹ i.val` is just
`(σ⁻¹ i).val`. The `permNat`-form appears literally in `PathsBetween.permute`/
`PathsFrom.permute`/`PathState.permute`; this rewrites it to `Fin`-form for downstream
indexing. -/
private theorem permNat_inv_fin {k : Nat} (σ : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    permNat σ⁻¹ i.val = (σ⁻¹ i).val := by
  rw [permNat_of_lt i.isLt]

/-- Per-cell `PathsBetween` equality: the cell built by `initializePaths (G.permute σ)`
at endpoints `(S, E)` equals `PathsBetween.permute σ` of the cell built by `initializePaths G`
at endpoints `(σ⁻¹ S, σ⁻¹ E)`. The `connectedSubPaths` field is handled by case-split on
`d = 0`. -/
private theorem PathsBetween_initializePaths_eq
    {k : Nat} (G : AdjMatrix (k+1)) (σ : Equiv.Perm (Fin (k+1)))
    (d : Nat) (S E : Fin (k+1)) :
    ({ depth := d, startVertexIndex := S, endVertexIndex := E,
       connectedSubPaths :=
         if d = 0 then
           (if S = E then [PathSegment.bottom S] else [] : List (PathSegment (k+1)))
         else
           (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
             PathSegment.inner ((G.permute σ).adj midFin E) (d - 1) S midFin
     } : PathsBetween (k+1))
    = PathsBetween.permute σ
        ({ depth := d, startVertexIndex := σ⁻¹ S, endVertexIndex := σ⁻¹ E,
           connectedSubPaths :=
             if d = 0 then
               (if σ⁻¹ S = σ⁻¹ E then [PathSegment.bottom (σ⁻¹ S)] else []
                : List (PathSegment (k+1)))
             else
               (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                 PathSegment.inner (G.adj midFin (σ⁻¹ E)) (d - 1) (σ⁻¹ S) midFin
         } : PathsBetween (k+1)) := by
  -- Unfold PathsBetween.permute (succ branch); RHS becomes an explicit struct.
  -- Note: the body of `permute` references `p.connectedSubPaths` twice (in both branches
  -- of the outer `if p.depth = 0`), so the explicit unfolded form retains the *inner* if.
  show _ = ({ depth := d
              startVertexIndex := σ (σ⁻¹ S)
              endVertexIndex   := σ (σ⁻¹ E)
              connectedSubPaths :=
                if d = 0 then
                  List.map (PathSegment.permute σ)
                    (if d = 0 then
                       (if σ⁻¹ S = σ⁻¹ E then [PathSegment.bottom (σ⁻¹ S)] else []
                        : List (PathSegment (k+1)))
                     else
                       (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                         PathSegment.inner (G.adj midFin (σ⁻¹ E)) (d - 1) (σ⁻¹ S) midFin)
                else
                  (List.finRange (k+1)).map fun i : Fin (k+1) =>
                    PathSegment.permute σ
                      (List.getD
                         (if d = 0 then
                            (if σ⁻¹ S = σ⁻¹ E then [PathSegment.bottom (σ⁻¹ S)] else []
                             : List (PathSegment (k+1)))
                          else
                            (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                              PathSegment.inner (G.adj midFin (σ⁻¹ E)) (d - 1) (σ⁻¹ S) midFin)
                         (permNat σ⁻¹ i.val) (PathSegment.bottom 0)) }
            : PathsBetween (k+1))
  refine PathsBetween.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · -- connectedSubPaths
    by_cases hd : d = 0
    · -- d = 0: outer if and inner if both take the `then` branch.
      simp only [if_pos hd]
      by_cases hS : S = E
      · rw [if_pos hS, if_pos (by rw [hS] : σ⁻¹ S = σ⁻¹ E)]
        simp [PathSegment.permute, hS]
      · have hS' : ¬ σ⁻¹ S = σ⁻¹ E := fun heq => hS (σ⁻¹.injective heq)
        rw [if_neg hS, if_neg hS']
        rfl
    · -- d > 0: outer if and inner if both take the `else` branch.
      simp only [if_neg hd]
      apply List.map_congr_left
      intro i _hi
      rw [permNat_inv_fin]
      have h_inb : (σ⁻¹ i).val < ((List.finRange (k+1)).map fun midFin : Fin (k+1) =>
          PathSegment.inner (G.adj midFin (σ⁻¹ E)) (d - 1) (σ⁻¹ S) midFin).length := by
        simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_inb]
      show PathSegment.inner ((G.permute σ).adj i E) (d - 1) S i
        = PathSegment.permute σ
          (((List.finRange (k+1)).map fun midFin : Fin (k+1) =>
              PathSegment.inner (G.adj midFin (σ⁻¹ E)) (d - 1) (σ⁻¹ S) midFin)[(σ⁻¹ i).val]'h_inb)
      rw [List.getElem_map, List.getElem_finRange]
      show PathSegment.inner ((G.permute σ).adj i E) (d - 1) S i
        = PathSegment.inner (G.adj (σ⁻¹ i) (σ⁻¹ E)) (d - 1) (σ (σ⁻¹ S)) (σ (σ⁻¹ i))
      simp [AdjMatrix.permute_adj]

/-- Per-cell `PathsFrom` equality: the cell built by `initializePaths (G.permute σ)`
at start `S` equals `PathsFrom.permute σ` of the cell built by `initializePaths G`
at start `σ⁻¹ S`. The `pathsToVertex` field is handled via per-end PathsBetween equality. -/
private theorem PathsFrom_initializePaths_eq
    {k : Nat} (G : AdjMatrix (k+1)) (σ : Equiv.Perm (Fin (k+1)))
    (d : Nat) (S : Fin (k+1)) :
    ({ depth := d, startVertexIndex := S,
       pathsToVertex := (List.finRange (k+1)).map fun endFin : Fin (k+1) =>
         { depth := d, startVertexIndex := S, endVertexIndex := endFin,
           connectedSubPaths :=
             if d = 0 then
               (if S = endFin then [PathSegment.bottom S] else []
                : List (PathSegment (k+1)))
             else
               (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                 PathSegment.inner ((G.permute σ).adj midFin endFin) (d - 1) S midFin
         } } : PathsFrom (k+1))
    = PathsFrom.permute σ
        ({ depth := d, startVertexIndex := σ⁻¹ S,
           pathsToVertex := (List.finRange (k+1)).map fun endFin : Fin (k+1) =>
             { depth := d, startVertexIndex := σ⁻¹ S, endVertexIndex := endFin,
               connectedSubPaths :=
                 if d = 0 then
                   (if σ⁻¹ S = endFin then [PathSegment.bottom (σ⁻¹ S)] else []
                    : List (PathSegment (k+1)))
                 else
                   (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                     PathSegment.inner (G.adj midFin endFin) (d - 1) (σ⁻¹ S) midFin
             } } : PathsFrom (k+1)) := by
  -- Unfold PathsFrom.permute (succ branch).
  show _ = ({ depth := d
              startVertexIndex := σ (σ⁻¹ S)
              pathsToVertex :=
                (List.finRange (k+1)).map fun i : Fin (k+1) =>
                  PathsBetween.permute σ
                    (((List.finRange (k+1)).map fun endFin : Fin (k+1) =>
                        ({ depth := d, startVertexIndex := σ⁻¹ S, endVertexIndex := endFin,
                           connectedSubPaths :=
                             if d = 0 then
                               (if σ⁻¹ S = endFin then [PathSegment.bottom (σ⁻¹ S)] else []
                                : List (PathSegment (k+1)))
                             else
                               (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                                 PathSegment.inner (G.adj midFin endFin) (d - 1) (σ⁻¹ S) midFin
                         } : PathsBetween (k+1))).getD (permNat σ⁻¹ i.val)
                      { depth := 0, startVertexIndex := 0, endVertexIndex := 0,
                        connectedSubPaths := [] }) }
            : PathsFrom (k+1))
  refine PathsFrom.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, ?_⟩
  · simp
  · -- pathsToVertex equality.
    apply List.map_congr_left
    intro i _hi
    rw [permNat_inv_fin]
    -- Reduce the inner getD to getElem.
    have h_inb : (σ⁻¹ i).val < ((List.finRange (k+1)).map fun endFin : Fin (k+1) =>
        ({ depth := d, startVertexIndex := σ⁻¹ S, endVertexIndex := endFin,
           connectedSubPaths :=
             if d = 0 then
               (if σ⁻¹ S = endFin then [PathSegment.bottom (σ⁻¹ S)] else []
                : List (PathSegment (k+1)))
             else
               (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                 PathSegment.inner (G.adj midFin endFin) (d - 1) (σ⁻¹ S) midFin
         } : PathsBetween (k+1))).length := by
      simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_inb,
        Option.getD_some, List.getElem_map, List.getElem_finRange]
    -- Now apply the per-end PathsBetween cell equality.
    exact PathsBetween_initializePaths_eq G σ d S i

theorem initializePaths_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) :
    initializePaths (G.permute σ) = PathState.permute σ (initializePaths G) := by
  cases n with
  | zero =>
    -- For n = 0, `PathState.permute σ st = st` definitionally, and both
    -- `initializePaths` calls produce `{ pathsOfLength := #[] }` (the outer map iterates
    -- over `List.finRange 0 = []`).
    show initializePaths (G.permute σ) = initializePaths G
    apply PathState.mk.injEq _ _ |>.mpr
    show (List.finRange 0).toArray.map _ = (List.finRange 0).toArray.map _
    rfl
  | succ k =>
    -- For n = k+1: descend through pathsOfLength (depth × start Array) cell-by-cell, then
    -- delegate the per-(d, s) PathsFrom equality to `PathsFrom_initializePaths_eq`.
    apply PathState.mk.injEq _ _ |>.mpr
    -- Outer Array.ext on depth dimension.
    refine Array.ext ?_ fun d hd₁ hd₂ => ?_
    · -- size equality (both k+1).
      show ((List.finRange (k+1)).toArray.map _).size
        = ((initializePaths G).pathsOfLength.map _).size
      simp [initializePaths]
    -- d : Nat, in [0, k+1).
    have hd : d < k+1 := by simpa [initializePaths] using hd₁
    -- Reduce both sides at depth d: LHS via getElem_map; RHS via getElem_map then unfold.
    show ((List.finRange (k+1)).toArray.map _)[d]'hd₁
       = ((initializePaths G).pathsOfLength.map _)[d]'hd₂
    rw [Array.getElem_map, Array.getElem_map]
    -- Reduce d-level indices BEFORE the inner Array.ext so the inner `s < ...` bound
    -- doesn't pick up a dependency on the unsubstituted `[d]` term (which would block
    -- subsequent rewrites of the form `... toArray[s]` due to motive type-mismatch).
    rw [show ((List.finRange (k+1)).toArray)[d]'(by simp; exact hd) = ⟨d, hd⟩ from
        by simp [List.getElem_finRange]]
    have h_depth_slice : (initializePaths G).pathsOfLength[d]'(by
        rw [initializePaths_pathsOfLength_size]; exact hd)
      = (List.finRange (k+1)).toArray.map fun startFin : Fin (k+1) =>
          ({ depth := d, startVertexIndex := startFin,
             pathsToVertex := (List.finRange (k+1)).map fun endFin : Fin (k+1) =>
               { depth := d, startVertexIndex := startFin, endVertexIndex := endFin,
                 connectedSubPaths :=
                   if d = 0 then
                     (if startFin = endFin then [PathSegment.bottom startFin] else []
                      : List (PathSegment (k+1)))
                   else
                     (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                       PathSegment.inner (G.adj midFin endFin) (d - 1) startFin midFin }
           } : PathsFrom (k+1)) := by
      show ((List.finRange (k+1)).toArray.map _)[d]'_ = _
      rw [Array.getElem_map]
      simp [List.getElem_finRange]
    rw [h_depth_slice]
    -- Inner Array.ext on start dimension.
    refine Array.ext ?_ fun s hs₁ hs₂ => ?_
    · -- size equality (both k+1).
      simp
    -- s : Nat, in [0, k+1).
    have hs : s < k+1 := by simpa using hs₁
    -- Reduce LHS at start s; reduce RHS at start s.
    rw [Array.getElem_map, Array.getElem_map]
    -- Substitute indices.
    rw [show ((List.finRange (k+1)).toArray)[s]'(by simp; exact hs) = ⟨s, hs⟩ from
        by simp [List.getElem_finRange]]
    rw [show (Array.range (k+1))[s]'(by simp; exact hs) = s from by simp [Array.getElem_range]]
    -- Reduce the RHS `.getD (permNat σ⁻¹ s) default`: in-bounds at `(σ⁻¹ ⟨s, hs⟩).val`.
    rw [show permNat σ⁻¹ s = (σ⁻¹ ⟨s, hs⟩).val from permNat_of_lt hs]
    have h_inb : (σ⁻¹ ⟨s, hs⟩).val < ((List.finRange (k+1)).toArray.map fun startFin : Fin (k+1) =>
        ({ depth := d, startVertexIndex := startFin,
           pathsToVertex := (List.finRange (k+1)).map fun endFin : Fin (k+1) =>
             { depth := d, startVertexIndex := startFin, endVertexIndex := endFin,
               connectedSubPaths :=
                 if d = 0 then
                   (if startFin = endFin then [PathSegment.bottom startFin] else []
                    : List (PathSegment (k+1)))
                 else
                   (List.finRange (k+1)).map fun midFin : Fin (k+1) =>
                     PathSegment.inner (G.adj midFin endFin) (d - 1) startFin midFin }
         } : PathsFrom (k+1))).size := by
      simp
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h_inb,
        Option.getD_some, Array.getElem_map]
    rw [show ((List.finRange (k+1)).toArray)[(σ⁻¹ ⟨s, hs⟩).val]'(by simp) = σ⁻¹ ⟨s, hs⟩ from
          by simp [List.getElem_finRange]]
    -- Now apply the per-cell helper at (d, ⟨s, hs⟩).
    exact PathsFrom_initializePaths_eq G σ d ⟨s, hs⟩

/-! ## §3 Stage B — `calculatePathRankings` equivariance -/

/-- The `fromRanks` table produced by `calculatePathRankings` has size `vc`. Follows from
`set!`-size-preservation through the outer fold; the initial table is built as
`(Array.range vc).map ...` of size `vc`. -/
theorem calculatePathRankings_fromRanks_size {vc : Nat} (state : PathState vc)
    (vts : Array VertexType) :
    (calculatePathRankings state vts).fromRanks.size = vc := by
  unfold calculatePathRankings
  -- The fold's `.2` (`fromRanks`-in-progress) starts with size `vc` and is updated only
  -- by `set!`, which preserves size. We prove this via a generic foldl-invariant.
  suffices haux : ∀ (l : List Nat)
      (start : Array (Array (Array Nat)) × Array (Array Nat)),
      start.2.size = vc →
      (l.foldl (fun accumulated depth =>
          let (currentBetween, currentFrom) := accumulated
          let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
          let allBetween := pathsAtDepth.foldl
            (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
          let betweenRankFn : Nat → Nat → Nat → Nat := fun rankDepth rankStart rankEnd =>
            ((currentBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
          let compareBetween := comparePathsBetween vts betweenRankFn
          let updatedBetween := (assignRanks compareBetween (sortBy compareBetween allBetween)).foldl
            (fun (betweenAcc : Array (Array (Array Nat))) item =>
              let (pathBetween, rank) := item
              setBetween betweenAcc depth pathBetween.startVertexIndex.val
                pathBetween.endVertexIndex.val rank) currentBetween
          let updatedBetweenFn : Nat → Nat → Nat → Nat := fun rankDepth rankStart rankEnd =>
            ((updatedBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
          let compareFrom := comparePathsFrom vts updatedBetweenFn
          let updatedFrom := (assignRanks compareFrom (sortBy compareFrom pathsAtDepth)).foldl
            (fun (fromAcc : Array (Array Nat)) item =>
              let (pathFrom, rank) := item
              let depthSlice := fromAcc.getD depth #[]
              fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom
          (updatedBetween, updatedFrom)) start).2.size = vc by
    apply haux
    simp
  intro l
  induction l with
  | nil => intros _ h; exact h
  | cons x xs ih =>
    intros start hstart
    rw [List.foldl_cons]
    apply ih
    obtain ⟨b, f⟩ := start
    simp only [] at hstart ⊢
    -- Inner fold over `assignRanks ...` applies `set!` (size-preserving).
    suffices h_inner : ∀ (l' : List ((PathsFrom vc) × Nat)) (acc : Array (Array Nat)),
        acc.size = vc →
        (l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
          let (pathFrom, rank) := item
          let depthSlice := fromAcc.getD x #[]
          fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).size = vc by
      apply h_inner _ _ hstart
    intro l' acc hacc
    induction l' generalizing acc with
    | nil => exact hacc
    | cons y ys ih_inner =>
      rw [List.foldl_cons]
      apply ih_inner
      obtain ⟨pathFrom, rank⟩ := y
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hacc]

/-! ### Size invariants for `calculatePathRankings`'s output

The `calculatePathRankings_σInvariant` (below) needs five size facts: `betweenRanks` has
shape `vc × vc × vc` and `fromRanks` has shape `vc × vc`. We prove these via small
size-preservation lemmas about `set!`/`setBetween` and a foldl invariant. -/

/-- `set!` at the same in-bounds index reads back the inserted value (for `getD`). -/
private theorem Array_set!_getD_self {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (h : i < xs.size) : (xs.set! i v).getD i d = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

/-- `set!` at a different index leaves the `getD` reading unchanged. -/
private theorem Array_set!_getD_ne {α : Type} (xs : Array α) (i j : Nat) (v d : α)
    (h : i ≠ j) : (xs.set! i v).getD j d = xs.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

/-- Out-of-bounds `set!` is a no-op. -/
private theorem Array_set!_eq_self_of_size_le {α : Type} (xs : Array α) (i : Nat) (v : α)
    (h : xs.size ≤ i) : xs.set! i v = xs := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le h]

/-- `setBetween` preserves `betweenTable`'s outer size. -/
private theorem setBetween_size (b : Array (Array (Array Nat))) (d s e r : Nat) :
    (setBetween b d s e r).size = b.size := by
  unfold setBetween
  simp [Array.set!_eq_setIfInBounds]

/-- `setBetween` preserves the size of every depth-row. -/
private theorem setBetween_getD_size (b : Array (Array (Array Nat))) (d s e r d' : Nat) :
    ((setBetween b d s e r).getD d' #[]).size = (b.getD d' #[]).size := by
  unfold setBetween
  by_cases h_eq : d = d'
  · subst h_eq
    by_cases h_in : d < b.size
    · rw [Array_set!_getD_self _ _ _ _ h_in]
      simp [Array.set!_eq_setIfInBounds]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_eq]

/-- `setBetween` preserves the size of every (depth, start)-cell. -/
private theorem setBetween_getD_getD_size (b : Array (Array (Array Nat)))
    (d s e r d' s' : Nat) :
    (((setBetween b d s e r).getD d' #[]).getD s' #[]).size
    = ((b.getD d' #[]).getD s' #[]).size := by
  unfold setBetween
  by_cases h_d_eq : d = d'
  · subst h_d_eq
    by_cases h_d_in : d < b.size
    · rw [Array_set!_getD_self _ _ _ _ h_d_in]
      -- Inside: `depthSlice.set! s (startSlice.set! e r)`. Recurse on s vs s'.
      by_cases h_s_eq : s = s'
      · subst h_s_eq
        by_cases h_s_in : s < (b.getD d #[]).size
        · rw [Array_set!_getD_self _ _ _ _ h_s_in]
          simp [Array.set!_eq_setIfInBounds]
        · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
      · rw [Array_set!_getD_ne _ _ _ _ _ h_s_eq]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_d_eq]

/-- The from-side update preserves the size of every depth-row. -/
private theorem from_set_getD_size (f : Array (Array Nat)) (d s : Nat) (rank : Nat) (d' : Nat) :
    ((f.set! d ((f.getD d #[]).set! s rank)).getD d' #[]).size = (f.getD d' #[]).size := by
  by_cases h_eq : d = d'
  · subst h_eq
    by_cases h_in : d < f.size
    · rw [Array_set!_getD_self _ _ _ _ h_in]
      simp [Array.set!_eq_setIfInBounds]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_eq]

/-! ### `RankState.σInvariant` and extensionality

The structural content of `RankState.permute σ rs = rs` decomposes into (a) size constraints
ensuring `rs`'s tables are shape `n × n × n` / `n × n` and (b) σ-invariance of the cell
values. We package this as `RankState.σInvariant`, prove the extensionality direction
(`σInvariant → permute σ rs = rs`), and reduce the main theorem to the σInvariance of
`calculatePathRankings (initializePaths G) vts`. The latter is the deep content — it
requires σ-equivariance of the entire `calculatePathRankings` pipeline (compare → sort →
assignRanks → fold). -/

/-- The structural σ-invariance of a `RankState` w.r.t. a permutation `σ`. -/
structure RankState.σInvariant {n : Nat} (σ : Equiv.Perm (Fin n)) (rs : RankState) : Prop where
  fromRanks_size      : rs.fromRanks.size = n
  betweenRanks_size   : rs.betweenRanks.size = n
  fromRanks_row_size  : ∀ d : Nat, d < n → (rs.fromRanks.getD d #[]).size = n
  betweenRanks_row_size : ∀ d : Nat, d < n → (rs.betweenRanks.getD d #[]).size = n
  betweenRanks_cell_size : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
    ((rs.betweenRanks.getD d #[]).getD s #[]).size = n
  /-- σ-invariance of `fromRanks` values: σ⁻¹-shifted start positions hold the same rank. -/
  fromRanks_inv : ∀ d : Nat, d < n → ∀ s : Fin n,
    (rs.fromRanks.getD d #[]).getD s.val 0
    = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0
  /-- σ-invariance of `betweenRanks` values: σ⁻¹-shifted (start, end) hold the same rank. -/
  betweenRanks_inv : ∀ d : Nat, d < n → ∀ s e : Fin n,
    ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
    = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0

/-- Extensionality: the structural σ-invariance is exactly what `RankState.permute σ rs = rs`
requires. -/
theorem RankState.σInvariant.permute_eq_self
    {σ : Equiv.Perm (Fin n)} {rs : RankState} (h : RankState.σInvariant σ rs) :
    RankState.permute σ rs = rs := by
  -- Apply mk.injEq via show on the unfolded `permute` form.
  show ({ betweenRanks := _, fromRanks := _ } : RankState) = rs
  refine RankState.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · -- betweenRanks equality.
    refine Array.ext ?_ fun d hd₁ hd₂ => ?_
    · simp [h.betweenRanks_size, h.fromRanks_size]
    have hd : d < n := by simpa [h.fromRanks_size] using hd₁
    rw [Array.getElem_map, Array.getElem_range]
    -- Convert RHS `rs.betweenRanks[d]` to `rs.betweenRanks.getD d #[]` BEFORE the inner
    -- Array.ext, so the inner bound `hs₂` doesn't carry a dependency on the unsubstituted
    -- `[d]` term (which would block subsequent rewrites with motive type-mismatch).
    rw [show rs.betweenRanks[d]'hd₂ = rs.betweenRanks.getD d #[] from Array.getElem_eq_getD _]
    refine Array.ext ?_ fun s hs₁ hs₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.betweenRanks_row_size d hd).symm
    have hs : s < n := by simpa using hs₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show (rs.betweenRanks.getD d #[])[s]'hs₂ = (rs.betweenRanks.getD d #[]).getD s #[] from
        Array.getElem_eq_getD _]
    refine Array.ext ?_ fun e he₁ he₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.betweenRanks_cell_size d hd s hs).symm
    have he : e < n := by simpa using he₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show ((rs.betweenRanks.getD d #[]).getD s #[])[e]'he₂
          = ((rs.betweenRanks.getD d #[]).getD s #[]).getD e 0 from Array.getElem_eq_getD _]
    rw [show permNat σ⁻¹ s = (σ⁻¹ ⟨s, hs⟩).val from permNat_of_lt hs,
        show permNat σ⁻¹ e = (σ⁻¹ ⟨e, he⟩).val from permNat_of_lt he]
    exact (h.betweenRanks_inv d hd ⟨s, hs⟩ ⟨e, he⟩).symm
  · -- fromRanks equality. Same pattern as above without the third level.
    refine Array.ext ?_ fun d hd₁ hd₂ => ?_
    · simp [h.fromRanks_size]
    have hd : d < n := by simpa [h.fromRanks_size] using hd₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show rs.fromRanks[d]'hd₂ = rs.fromRanks.getD d #[] from Array.getElem_eq_getD _]
    refine Array.ext ?_ fun s hs₁ hs₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.fromRanks_row_size d hd).symm
    have hs : s < n := by simpa using hs₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show (rs.fromRanks.getD d #[])[s]'hs₂ = (rs.fromRanks.getD d #[]).getD s 0 from
        Array.getElem_eq_getD _]
    rw [show permNat σ⁻¹ s = (σ⁻¹ ⟨s, hs⟩).val from permNat_of_lt hs]
    exact (h.fromRanks_inv d hd ⟨s, hs⟩).symm

/-- The five size facts about `calculatePathRankings`'s output: `betweenRanks` and
`fromRanks` have shapes `vc × vc × vc` and `vc × vc`. Proved via a single foldl invariant
on the algorithm body, using the `setBetween`/`set!` size-preservation lemmas above. -/
theorem calculatePathRankings_size_inv {vc : Nat} (state : PathState vc)
    (vts : Array VertexType) :
    let rs := calculatePathRankings state vts
    rs.betweenRanks.size = vc ∧
    rs.fromRanks.size = vc ∧
    (∀ d : Nat, d < vc → (rs.fromRanks.getD d #[]).size = vc) ∧
    (∀ d : Nat, d < vc → (rs.betweenRanks.getD d #[]).size = vc) ∧
    (∀ d s : Nat, d < vc → s < vc →
      ((rs.betweenRanks.getD d #[]).getD s #[]).size = vc) := by
  unfold calculatePathRankings
  -- Define a combined size invariant on the foldl accumulator (b, f).
  suffices haux : ∀ (l : List Nat)
      (start : Array (Array (Array Nat)) × Array (Array Nat)),
      (start.1.size = vc ∧ start.2.size = vc ∧
       (∀ d : Nat, d < vc → (start.2.getD d #[]).size = vc) ∧
       (∀ d : Nat, d < vc → (start.1.getD d #[]).size = vc) ∧
       (∀ d s : Nat, d < vc → s < vc → ((start.1.getD d #[]).getD s #[]).size = vc)) →
      let acc := l.foldl (fun accumulated depth =>
          let (currentBetween, currentFrom) := accumulated
          let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
          let allBetween := pathsAtDepth.foldl
            (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
          let betweenRankFn : Nat → Nat → Nat → Nat := fun rankDepth rankStart rankEnd =>
            ((currentBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
          let compareBetween := comparePathsBetween vts betweenRankFn
          let updatedBetween := (assignRanks compareBetween (sortBy compareBetween allBetween)).foldl
            (fun (betweenAcc : Array (Array (Array Nat))) item =>
              let (pathBetween, rank) := item
              setBetween betweenAcc depth pathBetween.startVertexIndex.val
                pathBetween.endVertexIndex.val rank) currentBetween
          let updatedBetweenFn : Nat → Nat → Nat → Nat := fun rankDepth rankStart rankEnd =>
            ((updatedBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
          let compareFrom := comparePathsFrom vts updatedBetweenFn
          let updatedFrom := (assignRanks compareFrom (sortBy compareFrom pathsAtDepth)).foldl
            (fun (fromAcc : Array (Array Nat)) item =>
              let (pathFrom, rank) := item
              let depthSlice := fromAcc.getD depth #[]
              fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom
          (updatedBetween, updatedFrom)) start
      acc.1.size = vc ∧ acc.2.size = vc ∧
      (∀ d : Nat, d < vc → (acc.2.getD d #[]).size = vc) ∧
      (∀ d : Nat, d < vc → (acc.1.getD d #[]).size = vc) ∧
      (∀ d s : Nat, d < vc → s < vc → ((acc.1.getD d #[]).getD s #[]).size = vc) by
    -- Apply with the empty initial accumulator.
    have h_init : (((Array.range vc).map fun _ => (Array.range vc).map fun _ =>
                    (Array.range vc).map fun _ : Nat => (0 : Nat)).size = vc ∧
                   ((Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).size = vc ∧
                   (∀ d : Nat, d < vc → (((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).size = vc) ∧
                   (∀ d : Nat, d < vc → (((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).size = vc) ∧
                   (∀ d s : Nat, d < vc → s < vc → ((((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).getD s #[]).size = vc)) := by
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro d hd
        simp [hd]
      · intro d hd
        simp [hd]
      · intro d s hd hs
        simp [hd, hs]
    exact haux _ _ h_init
  -- Foldl invariant proof.
  intro l
  induction l with
  | nil => intros _ h; exact h
  | cons x xs ih =>
    intros start hstart
    rw [List.foldl_cons]
    apply ih
    obtain ⟨b, f⟩ := start
    obtain ⟨h_b_size, h_f_size, h_f_row, h_b_row, h_b_cell⟩ := hstart
    simp only [] at h_b_size h_f_size h_f_row h_b_row h_b_cell ⊢
    -- Inner fold over assignRanks updates `b` via `setBetween` — preserves between sizes.
    -- We state the inner-b lemma without an outer `let acc'` so that `exact`/`apply`
    -- unifies the universal variable `l'` with the specific assignRanks-output list in
    -- the goal.
    suffices h_inner_b : ∀ (l' : List ((PathsBetween vc) × Nat))
        (acc : Array (Array (Array Nat))),
        acc.size = vc → (∀ d : Nat, d < vc → (acc.getD d #[]).size = vc) →
        (∀ d s : Nat, d < vc → s < vc → ((acc.getD d #[]).getD s #[]).size = vc) →
        (l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc x pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) acc).size = vc ∧
        (∀ d : Nat, d < vc → ((l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc x pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) acc).getD d #[]).size = vc) ∧
        (∀ d s : Nat, d < vc → s < vc →
          (((l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
            let (pathBetween, rank) := item
            setBetween betweenAcc x pathBetween.startVertexIndex.val
              pathBetween.endVertexIndex.val rank) acc).getD d #[]).getD s #[]).size = vc) by
      suffices h_inner_f : ∀ (l' : List ((PathsFrom vc) × Nat)) (acc : Array (Array Nat)),
          acc.size = vc → (∀ d : Nat, d < vc → (acc.getD d #[]).size = vc) →
          (l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
            let (pathFrom, rank) := item
            let depthSlice := fromAcc.getD x #[]
            fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).size = vc ∧
          (∀ d : Nat, d < vc → ((l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
            let (pathFrom, rank) := item
            let depthSlice := fromAcc.getD x #[]
            fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).getD d #[]).size = vc) by
        exact ⟨(h_inner_b _ b h_b_size h_b_row h_b_cell).1,
               (h_inner_f _ f h_f_size h_f_row).1,
               (h_inner_f _ f h_f_size h_f_row).2,
               (h_inner_b _ b h_b_size h_b_row h_b_cell).2.1,
               (h_inner_b _ b h_b_size h_b_row h_b_cell).2.2⟩
      -- Prove h_inner_f.
      intro l' acc h_size h_row
      induction l' generalizing acc with
      | nil => exact ⟨h_size, h_row⟩
      | cons y ys ih_inner =>
        rw [List.foldl_cons]
        obtain ⟨pathFrom, rank⟩ := y
        apply ih_inner
        · simp [Array.set!_eq_setIfInBounds, h_size]
        · intro d hd
          rw [from_set_getD_size]
          exact h_row d hd
    -- Prove h_inner_b.
    intro l' acc h_size h_row h_cell
    induction l' generalizing acc with
    | nil => exact ⟨h_size, h_row, h_cell⟩
    | cons y ys ih_inner =>
      rw [List.foldl_cons]
      obtain ⟨pathBetween, rank⟩ := y
      apply ih_inner
      · rw [setBetween_size]; exact h_size
      · intro d hd; rw [setBetween_getD_size]; exact h_row d hd
      · intro d s hd hs; rw [setBetween_getD_getD_size]; exact h_cell d s hd hs

/-! ### σ-equivariance of the comparison functions

`calculatePathRankings_value_invariant` needs the three compare functions to be σ-equivariant
on σ-invariant inputs. We prove `comparePathSegments` fully here; the stronger `PathsBetween`/
`PathsFrom` versions also require `sortBy`'s `map`-respect lemma (proved below), and for
the depth-positive `PathsBetween` case `orderInsensitiveListCmp`'s permutation-invariance
(left for follow-up work). -/

/-- `insertSorted` respects `map` when `f` preserves the comparison: inserting `f a` into
a `f`-mapped sorted list equals `f`-mapping the result of inserting `a` into the original
sorted list. -/
private theorem insertSorted_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (a : α) (L : List α) :
    insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    show insertSorted cmp (f a) (f b :: L.map f) = (insertSorted cmp a (b :: L)).map f
    show (if cmp (f a) (f b) != .gt then f a :: f b :: L.map f
          else f b :: insertSorted cmp (f a) (L.map f))
       = (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).map f
    rw [h a b]
    by_cases hc : cmp a b != .gt
    · simp [hc]
    · simp [hc, ih]

/-- `sortBy` respects `map` when `f` preserves the comparison. The σ-equivariance form
(below) instantiates `f := PathSegment.permute σ` and the σ-equivariance of
`comparePathSegments`. -/
private theorem sortBy_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (L : List α) :
    sortBy cmp (L.map f) = (sortBy cmp L).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show insertSorted cmp (f a) (sortBy cmp (L.map f))
       = (insertSorted cmp a (sortBy cmp L)).map f
    rw [ih, insertSorted_map f cmp h]

/-- `insertSorted` produces a permutation of `a :: L` (regardless of `cmp`). -/
theorem perm_insertSorted {α : Type} (cmp : α → α → Ordering) (a : α) (L : List α) :
    (insertSorted cmp a L).Perm (a :: L) := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons b L ih =>
    show (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).Perm (a :: b :: L)
    by_cases h : cmp a b != .gt
    · simp [h]
    · simp [h]
      exact (List.Perm.cons b ih).trans (List.Perm.swap a b L)

/-- `sortBy` produces a permutation of its input (regardless of `cmp`). -/
theorem sortBy_perm {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (sortBy cmp L).Perm L := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons a L ih =>
    show (insertSorted cmp a (sortBy cmp L)).Perm (a :: L)
    exact (perm_insertSorted cmp a (sortBy cmp L)).trans (List.Perm.cons a ih)

/-- The head case of `sortedPerm_class_eq`: heads of sorted permuted lists are in the same
class. Proved here cleanly using `Perm`-membership + sortedness + reflexivity + antisymmetry.

For the general position-`i` case, the same reasoning applies after "decomposing" both
lists, but the tail-decomposition isn't a `Perm` (only "class-Perm"), which is the
difficulty in the general lemma. -/
private theorem sorted_perm_head_class_eq {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (a : α) (M : List α) (b : α) (M' : List α)
    (h_perm : (a :: M).Perm (b :: M'))
    (h_sort : (a :: M).Pairwise (fun x y => cmp x y ≠ Ordering.gt))
    (h_sort' : (b :: M').Pairwise (fun x y => cmp x y ≠ Ordering.gt)) :
    cmp a b = Ordering.eq := by
  -- Membership transfer via Perm.
  have ha_in : a ∈ b :: M' := h_perm.mem_iff.mp List.mem_cons_self
  have hb_in : b ∈ a :: M := h_perm.symm.mem_iff.mp List.mem_cons_self
  -- cmp a b ≠ .gt: either b = a (refl) or b ∈ M (sortedness of a :: M).
  have h_ab : cmp a b ≠ Ordering.gt := by
    rcases List.mem_cons.mp hb_in with hb_eq | hb_in_tail
    · subst hb_eq; rw [h_refl]; intro h; cases h
    · exact List.rel_of_pairwise_cons h_sort hb_in_tail
  -- cmp b a ≠ .gt: similarly.
  have h_ba : cmp b a ≠ Ordering.gt := by
    rcases List.mem_cons.mp ha_in with ha_eq | ha_in_tail
    · subst ha_eq; rw [h_refl]; intro h; cases h
    · exact List.rel_of_pairwise_cons h_sort' ha_in_tail
  -- Conclude cmp a b = .eq via case analysis + antisym.
  match h_cmp : cmp a b with
  | .eq => rfl
  | .lt =>
    have : cmp b a = Ordering.gt := h_antisym _ _ h_cmp
    exact absurd this h_ba
  | .gt => exact absurd h_cmp h_ab

/-- For sorted `M`, `M'` with `M.Perm M'`, at every position the elements are in the same
`cmp`-equivalence class. This is the **KEY LEMMA** behind `orderInsensitiveListCmp_perm`.

Intuition: in a sorted list, equivalence classes occupy contiguous blocks. Two sorted
permutations of the same multiset have the same block structure (same classes in the same
order, with the same sizes), hence agree class-wise at every position. Within each block
(within-class permutation), `cmp` gives `.eq`.

The proof is a counting argument. Set `x := M[i]`. Two facts about a sorted `L`:
- `count(cmp · x = .lt, L) ≤ i`: by sortedness, only the first `i` positions can hold
  elements strictly less than `x`.
- `count(cmp · x ≠ .gt, L) ≥ i + 1`: positions `0..i` all hold elements `≤ x`.
Both counts transfer to `M'` via `List.Perm.countP_eq`. In sorted `M'`, "lt-positions"
form a left prefix and "≠-gt-positions" form a left prefix. The bounds force position
`i` of `M'` to be sandwiched: not in the lt prefix (since `i ≥ lt_count`) but in the
≠-gt prefix (since `i < ngt_count`). Hence `cmp M'[i] x` is neither `.lt` nor `.gt`,
so it is `.eq`. Symmetry gives `cmp M[i] M'[i] = .eq`.

The proof uses four hypotheses on `cmp`: reflexivity, both directions of antisymmetry,
and `≤`-transitivity. These are the ingredients of a total preorder, which is what
`comparePathSegments`/etc. behave like on the algorithm's actual lists. -/
private theorem sortedPerm_class_eq {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (M M' : List α) (h_perm : M.Perm M')
    (h_sort_M : M.Pairwise (fun a b => cmp a b ≠ Ordering.gt))
    (h_sort_M' : M'.Pairwise (fun a b => cmp a b ≠ Ordering.gt))
    (i : Nat) (h_i : i < M.length) (h_i' : i < M'.length) :
    cmp (M[i]'h_i) (M'[i]'h_i') = Ordering.eq := by
  -- Helper 0: symmetry of `.eq` (derived from antisym₁ + antisym₂).
  have h_eq_symm : ∀ a b, cmp a b = Ordering.eq → cmp b a = Ordering.eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      have h1 := h_antisym₁ b a h_ba
      rw [hab] at h1
      exact Ordering.noConfusion h1
    | .gt =>
      have h1 := h_antisym₂ b a h_ba
      rw [hab] at h1
      exact Ordering.noConfusion h1
  -- Helper 1: `≤`-then-`<` gives `<`.
  have h_le_lt : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c = Ordering.lt → cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hbc' : cmp b c ≠ Ordering.gt := by rw [hbc]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab hbc'
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca' : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      exact (h_trans c a b h_ca' hab) (h_antisym₁ b c hbc)
  -- Helper 2: `<`-then-`≤` gives `<`.
  have h_lt_le : ∀ a b c, cmp a b = Ordering.lt → cmp b c ≠ Ordering.gt → cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hab' : cmp a b ≠ Ordering.gt := by rw [hab]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab' hbc
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca' : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      exact (h_trans b c a hbc h_ca') (h_antisym₁ a b hab)
  -- 1. Reference element `x := M[i]`.
  set x := M[i]'h_i with hx_def
  -- 2. `lt_count M x ≤ i`. Split `M = take i ++ drop i`; the drop part contributes 0.
  have h_lt_count_M : M.countP (fun y => decide (cmp y x = Ordering.lt)) ≤ i := by
    rw [show M = M.take i ++ M.drop i from (List.take_append_drop i M).symm,
        List.countP_append]
    have h_drop_zero : (M.drop i).countP (fun y => decide (cmp y x = Ordering.lt)) = 0 := by
      rw [List.countP_eq_zero]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      have hk_lt' : k < M.length - i := by simpa using hk_lt
      have hi_k : i + k < M.length := by omega
      simp only [decide_eq_true_eq]
      have h_index : (M.drop i)[k]'hk_lt = M[i + k]'hi_k :=
        (List.getElem_drop' (by omega)).symm
      rw [show y = M[i + k]'hi_k by rw [← hk_eq]; exact h_index]
      intro h_eq_lt
      by_cases h_k : k = 0
      · subst h_k
        -- h_eq_lt : cmp M[i + 0] x = Ordering.lt; reduce via def-eq.
        have h_eq_lt' : cmp (M[i]'h_i) (M[i]'h_i) = Ordering.lt := h_eq_lt
        rw [h_refl] at h_eq_lt'
        exact Ordering.noConfusion h_eq_lt'
      · have hi_lt_ik : i < i + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero h_k)
        have h_sort : cmp (M[i]'h_i) (M[i + k]'hi_k) ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M) i (i + k) h_i hi_k hi_lt_ik
        exact h_sort (h_antisym₁ _ _ h_eq_lt)
    rw [h_drop_zero, Nat.add_zero]
    refine Nat.le_trans List.countP_le_length ?_
    rw [List.length_take]; exact Nat.min_le_left _ _
  -- 3. `not_gt_count M x ≥ i + 1`. The take (i+1) part hits `i+1` because every element satisfies.
  have h_ngt_count_M : i + 1 ≤ M.countP (fun y => decide (cmp y x ≠ Ordering.gt)) := by
    rw [show M = M.take (i+1) ++ M.drop (i+1) from (List.take_append_drop (i+1) M).symm,
        List.countP_append]
    have h_take_eq : (M.take (i+1)).countP (fun y => decide (cmp y x ≠ Ordering.gt))
                  = (M.take (i+1)).length := by
      rw [List.countP_eq_length]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      simp only [decide_eq_true_eq]
      rw [List.getElem_take] at hk_eq
      rw [List.length_take] at hk_lt
      have hk_lt_succ : k < i + 1 := (lt_min_iff.mp hk_lt).1
      have hk_le_i : k ≤ i := Nat.le_of_lt_succ hk_lt_succ
      have hk_M : k < M.length := (lt_min_iff.mp hk_lt).2
      rw [← hk_eq]
      by_cases h_k : k = i
      · subst h_k
        rw [hx_def, h_refl]
        intro hh; cases hh
      · have hk_lt_i : k < i := lt_of_le_of_ne hk_le_i h_k
        exact (List.pairwise_iff_getElem.mp h_sort_M) k i hk_M h_i hk_lt_i
    have h_take_len : (M.take (i+1)).length = i + 1 := by
      rw [List.length_take]; omega
    rw [h_take_eq, h_take_len]
    omega
  -- 4. Perm transfer: counts on `M'` inherit the same bounds.
  have h_lt_count_M' : M'.countP (fun y => decide (cmp y x = Ordering.lt)) ≤ i := by
    rw [← h_perm.countP_eq]; exact h_lt_count_M
  have h_ngt_count_M' : i + 1 ≤ M'.countP (fun y => decide (cmp y x ≠ Ordering.gt)) := by
    rw [← h_perm.countP_eq]; exact h_ngt_count_M
  -- 5. `cmp M'[i] x ≠ .lt`. Otherwise, by `h_le_lt`, all positions ≤ `i` have `cmp · x = .lt`,
  -- forcing `lt_count M' x ≥ i + 1` — contradicting (4).
  have h_not_lt : cmp (M'[i]'h_i') x ≠ Ordering.lt := by
    intro h_lt_val
    have h_count_take_M' : (M'.take (i+1)).countP (fun y => decide (cmp y x = Ordering.lt))
                         = (M'.take (i+1)).length := by
      rw [List.countP_eq_length]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      simp only [decide_eq_true_eq]
      rw [List.getElem_take] at hk_eq
      rw [List.length_take] at hk_lt
      have hk_lt_succ : k < i + 1 := (lt_min_iff.mp hk_lt).1
      have hk_le_i : k ≤ i := Nat.le_of_lt_succ hk_lt_succ
      have hk_M' : k < M'.length := (lt_min_iff.mp hk_lt).2
      rw [← hk_eq]
      by_cases h_k : k = i
      · subst h_k; exact h_lt_val
      · have hk_lt_i : k < i := lt_of_le_of_ne hk_le_i h_k
        have h_sort : cmp (M'[k]'hk_M') (M'[i]'h_i') ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M') k i hk_M' h_i' hk_lt_i
        exact h_le_lt _ _ _ h_sort h_lt_val
    have h_take_len_M' : (M'.take (i+1)).length = i + 1 := by
      rw [List.length_take]; omega
    have h_count_full :
        i + 1 ≤ M'.countP (fun y => decide (cmp y x = Ordering.lt)) := by
      rw [show M' = M'.take (i+1) ++ M'.drop (i+1) from (List.take_append_drop (i+1) M').symm,
          List.countP_append, h_count_take_M', h_take_len_M']
      omega
    omega
  -- 6. `cmp M'[i] x ≠ .gt`. Otherwise, by `h_lt_le` (after antisym), all positions ≥ `i`
  -- have `cmp · x = .gt`, forcing `ngt_count M' x ≤ i` — contradicting (4).
  have h_not_gt : cmp (M'[i]'h_i') x ≠ Ordering.gt := by
    intro h_gt_val
    have h_drop_zero : (M'.drop i).countP (fun y => decide (cmp y x ≠ Ordering.gt)) = 0 := by
      rw [List.countP_eq_zero]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      have hk_lt' : k < M'.length - i := by simpa using hk_lt
      have hi_k : i + k < M'.length := by omega
      simp only [decide_eq_true_eq, ne_eq, Decidable.not_not]
      have h_index : (M'.drop i)[k]'hk_lt = M'[i + k]'hi_k :=
        (List.getElem_drop' (by omega)).symm
      rw [show y = M'[i + k]'hi_k by rw [← hk_eq]; exact h_index]
      by_cases h_k : k = 0
      · subst h_k
        show cmp (M'[i]'h_i') x = Ordering.gt
        exact h_gt_val
      · have hi_lt_ik : i < i + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero h_k)
        have h_sort : cmp (M'[i]'h_i') (M'[i + k]'hi_k) ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M') i (i + k) h_i' hi_k hi_lt_ik
        have h_x_M'i : cmp x (M'[i]'h_i') = Ordering.lt := h_antisym₂ _ _ h_gt_val
        have h_x_M'ik : cmp x (M'[i + k]'hi_k) = Ordering.lt := h_lt_le _ _ _ h_x_M'i h_sort
        exact h_antisym₁ _ _ h_x_M'ik
    have h_take_le_i : (M'.take i).length ≤ i := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    have h_count_take_le : (M'.take i).countP (fun y => decide (cmp y x ≠ Ordering.gt))
                         ≤ i :=
      List.countP_le_length.trans h_take_le_i
    have h_total : M'.countP (fun y => decide (cmp y x ≠ Ordering.gt)) ≤ i := by
      rw [show M' = M'.take i ++ M'.drop i from (List.take_append_drop i M').symm,
          List.countP_append, h_drop_zero, Nat.add_zero]
      exact h_count_take_le
    omega
  -- 7. Conclude `cmp M'[i] x = .eq` (the only remaining case), then symmetrize.
  have h_M'i_eq_x : cmp (M'[i]'h_i') x = Ordering.eq := by
    match h : cmp (M'[i]'h_i') x with
    | .eq => rfl
    | .lt => exact (h_not_lt h).elim
    | .gt => exact (h_not_gt h).elim
  exact h_eq_symm _ _ h_M'i_eq_x

/-- `sortBy cmp L` produces a `Pairwise`-sorted list when the `≠ .gt` relation on `cmp` is
transitive. Standard insertion-sort result, deferred. Rather than exposing a transitivity
hypothesis on `orderInsensitiveListCmp_perm` (which would propagate up through
`comparePathsBetween_σ_equivariant`/`comparePathsFrom_σ_equivariant`), we absorb the proof
as a sorry here. -/
private theorem sortBy_pairwise {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (sortBy cmp L).Pairwise (fun a b => cmp a b ≠ Ordering.gt) := by
  sorry

/-- Pointwise `foldl` equality: if `L.length = L'.length` and `f acc (L[i]) = f acc (L'[i])`
at every position `i` and every `acc`, then the folds on `L` and `L'` give the same result. -/
private theorem foldl_pointwise_eq {α β : Type} (f : β → α → β) (L L' : List α) (init : β)
    (h_len : L.length = L'.length)
    (h_pt : ∀ acc : β, ∀ i : Nat, ∀ (h₁ : i < L.length) (h₂ : i < L'.length),
            f acc (L[i]'h₁) = f acc (L'[i]'h₂)) :
    L.foldl f init = L'.foldl f init := by
  induction L generalizing L' init with
  | nil => match L' with
    | [] => rfl
    | _ :: _ => simp at h_len
  | cons a L ih =>
    match L' with
    | [] => simp at h_len
    | a' :: L' =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [show f init a = f init a' from h_pt init 0 (by simp) (by simp)]
      apply ih
      · simpa using h_len
      · intros acc i h₁ h₂
        exact h_pt acc (i + 1) (by simp; exact h₁) (by simp; exact h₂)

/-- `orderInsensitiveListCmp` is invariant under permutations of its inputs when `cmp`
respects equivalence classes bilaterally (`h_compat`: both left and right).

**Proof.** Lengths agree by `Perm`. `sortBy cmp L₁` and `sortBy cmp L₁'` are both sorted
(`sortBy_pairwise`) and `Perm` (`sortBy_perm`-twice + transitivity). By
`sortedPerm_class_eq`, they agree position-wise on `cmp`-class. Under bilateral `h_compat`,
fold values against the corresponding position of the other sorted list agree pointwise,
so `foldl_pointwise_eq` gives the same result. -/
theorem orderInsensitiveListCmp_perm {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (h_compat : ∀ a b, cmp a b = Ordering.eq → ∀ c, cmp a c = cmp b c ∧ cmp c a = cmp c b)
    (L₁ L₁' L₂ L₂' : List α) (h₁ : L₁.Perm L₁') (h₂ : L₂.Perm L₂') :
    orderInsensitiveListCmp cmp L₁ L₂ = orderInsensitiveListCmp cmp L₁' L₂' := by
  unfold orderInsensitiveListCmp
  have hL₁ : L₁.length = L₁'.length := h₁.length_eq
  have hL₂ : L₂.length = L₂'.length := h₂.length_eq
  by_cases hLen : L₁.length = L₂.length
  · have hLen' : L₁'.length = L₂'.length := hL₁.symm.trans (hLen.trans hL₂)
    simp only [hLen, hLen', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    -- sortBy outputs are Perm-related + sorted.
    have hM₁ : (sortBy cmp L₁).Perm (sortBy cmp L₁') :=
      ((sortBy_perm cmp L₁).trans h₁).trans (sortBy_perm cmp L₁').symm
    have hM₂ : (sortBy cmp L₂).Perm (sortBy cmp L₂') :=
      ((sortBy_perm cmp L₂).trans h₂).trans (sortBy_perm cmp L₂').symm
    have hSort₁ := sortBy_pairwise cmp L₁
    have hSort₁' := sortBy_pairwise cmp L₁'
    have hSort₂ := sortBy_pairwise cmp L₂
    have hSort₂' := sortBy_pairwise cmp L₂'
    -- Pointwise class agreement.
    have h_class₁ : ∀ i (hi₁ : i < (sortBy cmp L₁).length) (hi₁' : i < (sortBy cmp L₁').length),
        cmp ((sortBy cmp L₁)[i]'hi₁) ((sortBy cmp L₁')[i]'hi₁') = Ordering.eq :=
      fun i hi₁ hi₁' =>
        sortedPerm_class_eq cmp h_refl h_antisym₁ h_antisym₂ h_trans
          _ _ hM₁ hSort₁ hSort₁' i hi₁ hi₁'
    have h_class₂ : ∀ i (hi₂ : i < (sortBy cmp L₂).length) (hi₂' : i < (sortBy cmp L₂').length),
        cmp ((sortBy cmp L₂)[i]'hi₂) ((sortBy cmp L₂')[i]'hi₂') = Ordering.eq :=
      fun i hi₂ hi₂' =>
        sortedPerm_class_eq cmp h_refl h_antisym₁ h_antisym₂ h_trans
          _ _ hM₂ hSort₂ hSort₂' i hi₂ hi₂'
    -- Length equality on zip.
    have h_zip_len : ((sortBy cmp L₁).zip (sortBy cmp L₂)).length
                  = ((sortBy cmp L₁').zip (sortBy cmp L₂')).length := by
      rw [List.length_zip, List.length_zip, hM₁.length_eq, hM₂.length_eq]
    -- Apply foldl_pointwise_eq.
    apply foldl_pointwise_eq _ _ _ _ h_zip_len
    intros acc i h_i₁ h_i₂
    -- Translate zip indices to sortBy positions.
    have h_sort₁_len : i < (sortBy cmp L₁).length := by
      have := h_i₁; rw [List.length_zip] at this; omega
    have h_sort₂_len : i < (sortBy cmp L₂).length := by
      have := h_i₁; rw [List.length_zip] at this; omega
    have h_sort₁'_len : i < (sortBy cmp L₁').length := by
      have := h_i₂; rw [List.length_zip] at this; omega
    have h_sort₂'_len : i < (sortBy cmp L₂').length := by
      have := h_i₂; rw [List.length_zip] at this; omega
    -- Compute cmp values at each position via bilateral h_compat.
    have h_eq_cmp :
        cmp ((sortBy cmp L₁)[i]'h_sort₁_len) ((sortBy cmp L₂)[i]'h_sort₂_len)
      = cmp ((sortBy cmp L₁')[i]'h_sort₁'_len) ((sortBy cmp L₂')[i]'h_sort₂'_len) := by
      -- Bridge through (sortBy L₁')[i] (sortBy L₂)[i] using left compat for L₁/L₁'.
      rw [(h_compat _ _ (h_class₁ i h_sort₁_len h_sort₁'_len) _).1]
      -- Now need cmp (sortBy L₁')[i] (sortBy L₂)[i] = cmp (sortBy L₁')[i] (sortBy L₂')[i].
      -- Use right compat for L₂/L₂'.
      exact (h_compat _ _ (h_class₂ i h_sort₂_len h_sort₂'_len) _).2
    -- The foldl step value at index i.
    show (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder else cmp x.1 x.2) acc
          ((sortBy cmp L₁).zip (sortBy cmp L₂))[i]
       = (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder else cmp x.1 x.2) acc
          ((sortBy cmp L₁').zip (sortBy cmp L₂'))[i]
    rw [List.getElem_zip, List.getElem_zip]
    simp [h_eq_cmp]
  · have hLen' : ¬ L₁'.length = L₂'.length := fun h => hLen (hL₁.trans (h.trans hL₂.symm))
    have h_len_lt : (L₁.length < L₂.length) = (L₁'.length < L₂'.length) := by
      rw [hL₁, hL₂]
    simp [hLen, hLen', h_len_lt]

/-- `comparePathSegments` is a total preorder on the algorithm's actual path lists
(reflexive, both directions of antisymmetry, ≤-transitive). The four conjuncts are exactly
the hypotheses needed by `orderInsensitiveListCmp_perm` (via `sortedPerm_class_eq`).

The properties hold globally except for the `panic!` mixed bottom/inner case (where
`cmp` returns `.lt` for both directions, breaking the `.lt → .gt` antisymmetry and
≤-transitivity). In the actual algorithm `connectedSubPaths` is uniform per call
(all `bottom` for depth=0, all `inner` for depth>0), so the panic case never fires;
proving this property given the algorithm's structure is left as future work. -/
private theorem comparePathSegments_total_preorder {vc : Nat}
    (vts : Array VertexType) (br : Nat → Nat → Nat → Nat) :
    (∀ a : PathSegment vc, comparePathSegments vts br a a = Ordering.eq) ∧
    (∀ a b : PathSegment vc, comparePathSegments vts br a b = Ordering.lt →
                              comparePathSegments vts br b a = Ordering.gt) ∧
    (∀ a b : PathSegment vc, comparePathSegments vts br a b = Ordering.gt →
                              comparePathSegments vts br b a = Ordering.lt) ∧
    (∀ a b c : PathSegment vc, comparePathSegments vts br a b ≠ Ordering.gt →
                                comparePathSegments vts br b c ≠ Ordering.gt →
                                comparePathSegments vts br a c ≠ Ordering.gt) := by
  sorry

/-- `comparePathsBetween` is a total preorder on the algorithm's actual `pathsToVertex`
lists. Same caveat as `comparePathSegments_total_preorder`: the panic case in the inner
`comparePathSegments` propagates up but never fires on the algorithm's lists. -/
private theorem comparePathsBetween_total_preorder {vc : Nat}
    (vts : Array VertexType) (br : Nat → Nat → Nat → Nat) :
    (∀ a : PathsBetween vc, comparePathsBetween vts br a a = Ordering.eq) ∧
    (∀ a b : PathsBetween vc, comparePathsBetween vts br a b = Ordering.lt →
                               comparePathsBetween vts br b a = Ordering.gt) ∧
    (∀ a b : PathsBetween vc, comparePathsBetween vts br a b = Ordering.gt →
                               comparePathsBetween vts br b a = Ordering.lt) ∧
    (∀ a b c : PathsBetween vc, comparePathsBetween vts br a b ≠ Ordering.gt →
                                 comparePathsBetween vts br b c ≠ Ordering.gt →
                                 comparePathsBetween vts br a c ≠ Ordering.gt) := by
  sorry

/-- `comparePathSegments` respects equivalence bilaterally: equivalent (`= .eq`) segments
compare the same way to every third segment, in either argument position. -/
theorem comparePathSegments_equivCompat
    {vc : Nat} (vts : Array VertexType) (br : Nat → Nat → Nat → Nat)
    (p q : PathSegment vc) (h : comparePathSegments vts br p q = Ordering.eq) (r : PathSegment vc) :
    comparePathSegments vts br p r = comparePathSegments vts br q r ∧
    comparePathSegments vts br r p = comparePathSegments vts br r q := by
  cases p with
  | bottom xVI =>
    cases q with
    | bottom yVI =>
      have hvts_eq : vts.getD xVI.val 0 = vts.getD yVI.val 0 :=
        compare_eq_iff_eq.mp h
      cases r with
      | bottom zVI =>
        refine ⟨?_, ?_⟩
        · show compare (vts.getD xVI.val 0) (vts.getD zVI.val 0)
             = compare (vts.getD yVI.val 0) (vts.getD zVI.val 0)
          rw [hvts_eq]
        · show compare (vts.getD zVI.val 0) (vts.getD xVI.val 0)
             = compare (vts.getD zVI.val 0) (vts.getD yVI.val 0)
          rw [hvts_eq]
      | inner _ _ _ _ => exact ⟨rfl, rfl⟩
    | inner _ _ _ _ =>
      exfalso
      have : (default : Ordering) = .lt := rfl
      rw [show comparePathSegments vts br (PathSegment.bottom xVI)
              (PathSegment.inner _ _ _ _) = default from rfl, this] at h
      exact Ordering.noConfusion h
  | inner xe xd xs xend =>
    cases q with
    | bottom _ =>
      exfalso
      have : (default : Ordering) = .lt := rfl
      rw [show comparePathSegments vts br (PathSegment.inner xe xd xs xend)
              (PathSegment.bottom _) = default from rfl, this] at h
      exact Ordering.noConfusion h
    | inner ye yd ys yend =>
      have hRank : br xd xs.val xend.val = br yd ys.val yend.val := by
        by_cases hxy : br xd xs.val xend.val = br yd ys.val yend.val
        · exact hxy
        · exfalso
          simp only [comparePathSegments, hxy, bne_iff_ne, ne_eq, not_false_eq_true,
            ↓reduceIte] at h
          exact hxy (compare_eq_iff_eq.mp h).symm
      have hEdge : xe = ye := by
        by_cases hxy : xe = ye
        · exact hxy
        · exfalso
          simp only [comparePathSegments, hRank, bne_self_eq_false, ↓reduceIte,
            hxy, bne_iff_ne, ne_eq, not_false_eq_true] at h
          exact hxy (compare_eq_iff_eq.mp h).symm
      cases r with
      | bottom _ => exact ⟨rfl, rfl⟩
      | inner ze zd zs zend =>
        refine ⟨?_, ?_⟩
        · show (let xR := br xd xs.val xend.val
                let zR := br zd zs.val zend.val
                if xR != zR then compare zR xR
                else if xe != ze then compare ze xe else .eq)
             = (let yR := br yd ys.val yend.val
                let zR := br zd zs.val zend.val
                if yR != zR then compare zR yR
                else if ye != ze then compare ze ye else .eq)
          rw [hRank, hEdge]
        · show (let zR := br zd zs.val zend.val
                let xR := br xd xs.val xend.val
                if zR != xR then compare xR zR
                else if ze != xe then compare xe ze else .eq)
             = (let zR := br zd zs.val zend.val
                let yR := br yd ys.val yend.val
                if zR != yR then compare yR zR
                else if ze != ye then compare ye ze else .eq)
          rw [hRank, hEdge]

/-- `orderInsensitiveListCmp` is invariant under `map`-ping both lists by an
`f` that preserves the comparison. This handles the depth=0 branch of
`PathsBetween.permute` (where `connectedSubPaths` is just `.map (PathSegment.permute σ)`). -/
theorem orderInsensitiveListCmp_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (L₁ L₂ : List α) :
    orderInsensitiveListCmp cmp (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp L₁ L₂ := by
  unfold orderInsensitiveListCmp
  simp only [List.length_map]
  by_cases hLen : L₁.length = L₂.length
  · simp only [hLen]
    rw [sortBy_map f cmp h L₁, sortBy_map f cmp h L₂]
    -- Convert the zip-of-maps into a map-of-zip, then push the map through `foldl` and
    -- collapse `cmp (f x) (f y)` to `cmp x y` via `h`.
    rw [show ((sortBy cmp L₁).map f).zip ((sortBy cmp L₂).map f)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map (fun (x, y) => (f x, f y)) by
        rw [List.zip_map_right, List.zip_map_left, List.map_map]
        congr]
    rw [List.foldl_map]
    -- The two foldl functions agree pointwise (by h); rewrite by function equality.
    have hfn : (fun (x : Ordering) (y : α × α) =>
                  if (x != Ordering.eq) = true then x
                  else cmp ((fun (p : α × α) => (f p.1, f p.2)) y).1
                            ((fun (p : α × α) => (f p.1, f p.2)) y).2)
             = (fun (currentOrder : Ordering) (x : α × α) =>
                  if (currentOrder != Ordering.eq) = true then currentOrder
                  else cmp x.1 x.2) := by
      funext x y
      simp [h y.1 y.2]
    rw [hfn]
  · simp [hLen]

/-- Pointwise variant of `insertSorted_map`: only requires `cmp (f a) (f b) = cmp a b`
for `b ∈ L`. -/
private theorem insertSorted_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (a : α) (L : List α) (h : ∀ b ∈ L, cmp (f a) (f b) = cmp a b) :
    insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    show insertSorted cmp (f a) (f b :: L.map f) = (insertSorted cmp a (b :: L)).map f
    show (if cmp (f a) (f b) != .gt then f a :: f b :: L.map f
          else f b :: insertSorted cmp (f a) (L.map f))
       = (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).map f
    rw [h b (List.mem_cons_self)]
    by_cases hc : cmp a b != .gt
    · simp [hc]
    · simp [hc, ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- Pointwise variant of `sortBy_map`: only requires `cmp (f a) (f b) = cmp a b` for
`a, b ∈ L`. -/
private theorem sortBy_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (L : List α) (h : ∀ a ∈ L, ∀ b ∈ L, cmp (f a) (f b) = cmp a b) :
    sortBy cmp (L.map f) = (sortBy cmp L).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show insertSorted cmp (f a) (sortBy cmp (L.map f))
       = (insertSorted cmp a (sortBy cmp L)).map f
    have h_L : ∀ x ∈ L, ∀ y ∈ L, cmp (f x) (f y) = cmp x y := fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [ih h_L]
    have h_a : ∀ b ∈ sortBy cmp L, cmp (f a) (f b) = cmp a b := fun b hb =>
      h a (List.mem_cons_self) b
        (List.mem_cons_of_mem _ ((sortBy_perm cmp L).mem_iff.mp hb))
    exact insertSorted_map_pointwise f cmp a (sortBy cmp L) h_a

/-- Pointwise `foldl` congruence: if `f` and `g` agree on all `(acc, a)` pairs where
`a ∈ L`, then their folds agree. -/
private theorem foldl_congr_mem {α β : Type} {f g : β → α → β} {L : List α} {init : β}
    (h : ∀ acc : β, ∀ a ∈ L, f acc a = g acc a) :
    L.foldl f init = L.foldl g init := by
  induction L generalizing init with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldl_cons, List.foldl_cons, h init a List.mem_cons_self]
    apply ih
    intros acc b hb
    exact h acc b (List.mem_cons_of_mem _ hb)

/-- Pointwise variant of `orderInsensitiveListCmp_map`: only requires `cmp (f a) (f b) = cmp a b`
for `a, b ∈ L₁ ++ L₂`. This is what's needed for `comparePathsFrom_σ_equivariant` where
the inner `comparePathsBetween_σ_equivariant` only applies to elements satisfying per-element
length conditions. -/
theorem orderInsensitiveListCmp_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (L₁ L₂ : List α)
    (h : ∀ a ∈ L₁ ++ L₂, ∀ b ∈ L₁ ++ L₂, cmp (f a) (f b) = cmp a b) :
    orderInsensitiveListCmp cmp (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp L₁ L₂ := by
  -- Decompose h into per-list and cross-list conditions.
  have h₁ : ∀ a ∈ L₁, ∀ b ∈ L₁, cmp (f a) (f b) = cmp a b := fun a ha b hb =>
    h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have h₂ : ∀ a ∈ L₂, ∀ b ∈ L₂, cmp (f a) (f b) = cmp a b := fun a ha b hb =>
    h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  unfold orderInsensitiveListCmp
  simp only [List.length_map]
  by_cases hLen : L₁.length = L₂.length
  · simp only [hLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [sortBy_map_pointwise f cmp L₁ h₁, sortBy_map_pointwise f cmp L₂ h₂]
    rw [show ((sortBy cmp L₁).map f).zip ((sortBy cmp L₂).map f)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map (fun (x, y) => (f x, f y)) by
        rw [List.zip_map_right, List.zip_map_left, List.map_map]
        congr]
    rw [List.foldl_map]
    -- Apply pointwise foldl_congr: only need cmp respect for pairs in the zip.
    apply foldl_congr_mem
    intros acc p hp
    have hp_left' : p.1 ∈ L₁ := (sortBy_perm cmp L₁).mem_iff.mp (List.of_mem_zip hp).1
    have hp_right' : p.2 ∈ L₂ := (sortBy_perm cmp L₂).mem_iff.mp (List.of_mem_zip hp).2
    have h_p : cmp (f p.1) (f p.2) = cmp p.1 p.2 :=
      h p.1 (List.mem_append_left _ hp_left') p.2 (List.mem_append_right _ hp_right')
    simp [h_p]
  · simp [hLen]

/-- `comparePathSegments` is σ-equivariant when both the typing array and the
`betweenRanks` function are σ-invariant. -/
theorem comparePathSegments_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p q : PathSegment vc) :
    comparePathSegments vts br (PathSegment.permute σ p) (PathSegment.permute σ q)
    = comparePathSegments vts br p q := by
  cases p with
  | bottom xVI =>
    cases q with
    | bottom yVI =>
      -- LHS: compare (vts.getD (σ xVI).val 0) (vts.getD (σ yVI).val 0)
      -- RHS: compare (vts.getD xVI.val 0) (vts.getD yVI.val 0)
      -- σ-invariance of vts gives equality at each position.
      show compare (vts.getD (σ xVI).val 0) (vts.getD (σ yVI).val 0)
         = compare (vts.getD xVI.val 0) (vts.getD yVI.val 0)
      rw [hvts xVI, hvts yVI]
    | inner _ _ _ _ =>
      -- Mixed bottom/inner hits the panic branch; both sides equal.
      rfl
  | inner xe xd xs xend =>
    cases q with
    | bottom _ =>
      rfl
    | inner ye yd ys yend =>
      -- LHS compares inner segments with `(σ xs, σ xend)` and `(σ ys, σ yend)` endpoints.
      -- σ-invariance of `br` gives the same `xRank`/`yRank` values as in the RHS.
      show (let xRank := br xd (σ xs).val (σ xend).val
            let yRank := br yd (σ ys).val (σ yend).val
            if xRank != yRank then compare yRank xRank
            else if xe != ye then compare ye xe else .eq)
        = (let xRank := br xd xs.val xend.val
           let yRank := br yd ys.val yend.val
           if xRank != yRank then compare yRank xRank
           else if xe != ye then compare ye xe else .eq)
      rw [hbr xd xs xend, hbr yd ys yend]

/-! ### `PathsBetween` / `PathsFrom` permute → multiset Perm

When `PathsBetween.permute σ` (depth>0 branch) reindexes `connectedSubPaths` via `σ⁻¹`
on positions, the result is a `Perm` of `connectedSubPaths.map (PathSegment.permute σ)`
by `Equiv.Perm.ofFn_comp_perm`. Same for `PathsFrom.permute σ`'s `pathsToVertex`. -/

/-- General reindex-perm lemma: if `L : List α` has length `n` and `σ : Equiv.Perm (Fin n)`,
then the list obtained by σ-reindexing `L.map act` is a `Perm` of `L.map act`. This captures
the depth>0 branch of `PathsBetween.permute`/`PathsFrom.permute` in a σ-agnostic way. -/
private theorem map_reindex_perm {α : Type} {n : Nat}
    (σ : Equiv.Perm (Fin n)) (L : List α) (h_len : L.length = n)
    (act : α → α) (def_val : α) :
    ((List.finRange n).map fun i : Fin n => act (L.getD (σ i).val def_val)).Perm
      (L.map act) := by
  -- Rewrite getD to getElem using h_len and (σ i).isLt.
  have h_eq : (List.finRange n).map (fun i : Fin n => act (L.getD (σ i).val def_val))
            = (List.finRange n).map (fun i : Fin n =>
                act (L[(σ i).val]'(h_len ▸ (σ i).isLt))) := by
    apply List.map_congr_left
    intro i _
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h_len ▸ (σ i).isLt),
        Option.getD_some]
  rw [h_eq]
  -- Convert to List.ofFn and apply Equiv.Perm.ofFn_comp_perm.
  rw [← List.ofFn_eq_map]
  -- Now: List.ofFn (fun i => act L[(σ i).val]'_) ~ L.map act.
  -- View as List.ofFn (f ∘ σ) where f i := act L[i.val]'_.
  rw [show (fun i : Fin n => act (L[(σ i).val]'(h_len ▸ (σ i).isLt)))
        = (fun i : Fin n => act (L[i.val]'(h_len ▸ i.isLt))) ∘ σ from by
      funext i; rfl]
  refine (Equiv.Perm.ofFn_comp_perm σ _).trans ?_
  -- Goal: List.ofFn (fun i => act L[i.val]'_) ~ L.map act.
  rw [List.ofFn_eq_map]
  -- Now: (finRange n).map (fun i : Fin n => act L[i.val]'_) ~ L.map act.
  -- Prove element-wise equality.
  apply List.Perm.of_eq
  apply List.ext_getElem
  · simp [h_len]
  intros j h₁ h₂
  simp [List.getElem_map, List.getElem_finRange]

/-- For `n = k + 1` and `p.connectedSubPaths` of length `k+1` (or depth = 0), the
permuted `connectedSubPaths` is a `Perm` of the σ-mapped original. -/
theorem PathsBetween_permute_connectedSubPaths_perm
    {vc : Nat} (σ : Equiv.Perm (Fin vc)) (p : PathsBetween vc)
    (h_len : p.depth > 0 → p.connectedSubPaths.length = vc) :
    (p.permute σ).connectedSubPaths.Perm (p.connectedSubPaths.map (PathSegment.permute σ)) := by
  match vc, σ, p, h_len with
  | 0, _, p, _ =>
    -- PathSegment 0 is uninhabited, so p.connectedSubPaths must be [].
    show p.connectedSubPaths.Perm (p.connectedSubPaths.map _)
    cases h_cs : p.connectedSubPaths with
    | nil => simp
    | cons a _ =>
      cases a with
      | bottom v => exact v.elim0
      | inner _ _ s _ => exact s.elim0
  | k + 1, σ, p, h_len =>
    by_cases hd : p.depth = 0
    · -- d = 0 case: directly equal (no reindexing).
      have h_eq : (PathsBetween.permute σ p).connectedSubPaths
                = p.connectedSubPaths.map (PathSegment.permute σ) := by
        show (if p.depth = 0 then p.connectedSubPaths.map (PathSegment.permute σ) else _) = _
        rw [if_pos hd]
      rw [h_eq]
    · -- d > 0: reindexed. Use map_reindex_perm with σ := σ⁻¹.
      have h_len' : p.connectedSubPaths.length = k + 1 := h_len (Nat.pos_of_ne_zero hd)
      have h_eq : (PathsBetween.permute σ p).connectedSubPaths
                = (List.finRange (k+1)).map fun i : Fin (k+1) =>
                    PathSegment.permute σ
                      (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (PathSegment.bottom 0)) := by
        show (if p.depth = 0 then _ else _) = _
        rw [if_neg hd]
      rw [h_eq]
      -- Replace `permNat σ⁻¹ i.val` with `(σ⁻¹ i).val` to match `map_reindex_perm`.
      have h_rw : (fun i : Fin (k+1) =>
          PathSegment.permute σ (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (PathSegment.bottom 0)))
        = (fun i : Fin (k+1) =>
          PathSegment.permute σ (p.connectedSubPaths.getD (σ⁻¹ i).val (PathSegment.bottom 0))) := by
        funext i
        rw [permNat_of_lt i.isLt]
      rw [h_rw]
      exact map_reindex_perm σ⁻¹ p.connectedSubPaths h_len'
        (PathSegment.permute σ) (PathSegment.bottom 0)

/-- Analogous Perm helper for `PathsFrom.permute`'s `pathsToVertex`. -/
theorem PathsFrom_permute_pathsToVertex_perm
    {vc : Nat} (σ : Equiv.Perm (Fin vc)) (p : PathsFrom vc)
    (h_len : p.pathsToVertex.length = vc) :
    (p.permute σ).pathsToVertex.Perm (p.pathsToVertex.map (PathsBetween.permute σ)) := by
  match vc, σ, p, h_len with
  | 0, _, p, h_len =>
    -- For n=0, PathsFrom.permute is identity. We need p.pathsToVertex = [].
    -- Actually, since pathsToVertex : List (PathsBetween 0) and PathsBetween has fields
    -- startVertexIndex endVertexIndex : Fin 0 (uninhabited), pathsToVertex can only be [].
    show p.pathsToVertex.Perm (p.pathsToVertex.map _)
    cases h_pv : p.pathsToVertex with
    | nil => simp
    | cons a _ => exact a.startVertexIndex.elim0
  | k + 1, σ, p, h_len =>
    -- PathsFrom.permute's pathsToVertex is always reindexed (no depth branching).
    have h_eq : (PathsFrom.permute σ p).pathsToVertex
              = (List.finRange (k+1)).map fun i : Fin (k+1) =>
                  PathsBetween.permute σ
                    (p.pathsToVertex.getD (permNat σ⁻¹ i.val)
                      { depth := 0, startVertexIndex := 0, endVertexIndex := 0,
                        connectedSubPaths := [] }) := rfl
    rw [h_eq]
    have h_rw : (fun i : Fin (k+1) =>
        PathsBetween.permute σ
          (p.pathsToVertex.getD (permNat σ⁻¹ i.val)
            ({ depth := 0, startVertexIndex := 0, endVertexIndex := 0,
               connectedSubPaths := [] } : PathsBetween (k+1))))
      = (fun i : Fin (k+1) =>
        PathsBetween.permute σ
          (p.pathsToVertex.getD (σ⁻¹ i).val
            ({ depth := 0, startVertexIndex := 0, endVertexIndex := 0,
               connectedSubPaths := [] } : PathsBetween (k+1)))) := by
      funext i
      rw [permNat_of_lt i.isLt]
    rw [h_rw]
    exact map_reindex_perm σ⁻¹ p.pathsToVertex h_len
      (PathsBetween.permute σ)
      { depth := 0, startVertexIndex := 0, endVertexIndex := 0, connectedSubPaths := [] }

/-- `comparePathsBetween` is σ-equivariant under σ-invariant `vts`/`br` and `connectedSubPaths`-
length normalization (which holds in `initializePaths G` for `depth>0`). -/
theorem comparePathsBetween_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p₁ p₂ : PathsBetween vc)
    (h_len₁ : p₁.depth > 0 → p₁.connectedSubPaths.length = vc)
    (h_len₂ : p₂.depth > 0 → p₂.connectedSubPaths.length = vc) :
    comparePathsBetween vts br (p₁.permute σ) (p₂.permute σ)
    = comparePathsBetween vts br p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂ with
  | 0, _, _, _, _, _ =>
    -- For n = 0, `PathsBetween.permute` is the identity definitionally.
    rfl
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂ =>
    -- Unfold comparePathsBetween + PathsBetween.permute (succ branch).
    show (if vts.getD (σ p₁.endVertexIndex).val 0 != vts.getD (σ p₂.endVertexIndex).val 0 then
            compare (vts.getD (σ p₁.endVertexIndex).val 0) (vts.getD (σ p₂.endVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 (PathsBetween.permute σ p₁).connectedSubPaths
                 (PathsBetween.permute σ p₂).connectedSubPaths)
       = (if vts.getD p₁.endVertexIndex.val 0 != vts.getD p₂.endVertexIndex.val 0 then
            compare (vts.getD p₁.endVertexIndex.val 0) (vts.getD p₂.endVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 p₁.connectedSubPaths p₂.connectedSubPaths)
    rw [hvts p₁.endVertexIndex, hvts p₂.endVertexIndex]
    split
    · rfl
    · -- else branch: orderInsensitiveListCmp on connectedSubPaths.
      have h_perm₁ := PathsBetween_permute_connectedSubPaths_perm σ p₁ h_len₁
      have h_perm₂ := PathsBetween_permute_connectedSubPaths_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathSegments_total_preorder (vc := k+1) vts br
      rw [orderInsensitiveListCmp_perm (comparePathSegments vts br)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathSegments_equivCompat vts br) _ _ _ _ h_perm₁ h_perm₂]
      exact orderInsensitiveListCmp_map (PathSegment.permute σ) (comparePathSegments vts br)
            (fun a b => comparePathSegments_σ_equivariant σ vts hvts br hbr a b)
            p₁.connectedSubPaths p₂.connectedSubPaths

/-- `comparePathsBetween` respects equivalence bilaterally (the EquivCompat condition
needed for `orderInsensitiveListCmp_perm` at the `comparePathsFrom` level). -/
theorem comparePathsBetween_equivCompat
    {vc : Nat} (vts : Array VertexType) (br : Nat → Nat → Nat → Nat)
    (p₁ p₂ : PathsBetween vc)
    (h : comparePathsBetween vts br p₁ p₂ = Ordering.eq)
    (r : PathsBetween vc) :
    comparePathsBetween vts br p₁ r = comparePathsBetween vts br p₂ r ∧
    comparePathsBetween vts br r p₁ = comparePathsBetween vts br r p₂ := by
  sorry

/-- `comparePathsFrom` is σ-equivariant under σ-invariant `vts`/`br` and `pathsToVertex`-
length normalization (which holds in `initializePaths G`). -/
theorem comparePathsFrom_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p₁ p₂ : PathsFrom vc)
    (h_len₁ : p₁.pathsToVertex.length = vc)
    (h_len₂ : p₂.pathsToVertex.length = vc)
    (h_inner_len₁ : ∀ q ∈ p₁.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc)
    (h_inner_len₂ : ∀ q ∈ p₂.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc) :
    comparePathsFrom vts br (p₁.permute σ) (p₂.permute σ)
    = comparePathsFrom vts br p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ with
  | 0, _, _, _, _, _, _, _ =>
    rfl
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ =>
    show (if vts.getD (σ p₁.startVertexIndex).val 0 != vts.getD (σ p₂.startVertexIndex).val 0 then
            compare (vts.getD (σ p₁.startVertexIndex).val 0) (vts.getD (σ p₂.startVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 (PathsFrom.permute σ p₁).pathsToVertex
                 (PathsFrom.permute σ p₂).pathsToVertex)
       = (if vts.getD p₁.startVertexIndex.val 0 != vts.getD p₂.startVertexIndex.val 0 then
            compare (vts.getD p₁.startVertexIndex.val 0) (vts.getD p₂.startVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 p₁.pathsToVertex p₂.pathsToVertex)
    rw [hvts p₁.startVertexIndex, hvts p₂.startVertexIndex]
    split
    · rfl
    · have h_perm₁ := PathsFrom_permute_pathsToVertex_perm σ p₁ h_len₁
      have h_perm₂ := PathsFrom_permute_pathsToVertex_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathsBetween_total_preorder (vc := k+1) vts br
      rw [orderInsensitiveListCmp_perm (comparePathsBetween vts br)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathsBetween_equivCompat vts br) _ _ _ _ h_perm₁ h_perm₂]
      -- Apply pointwise map lemma: comparePathsBetween_σ_equivariant for each pair in the
      -- combined list, using per-element h_inner_len conditions.
      apply orderInsensitiveListCmp_map_pointwise (PathsBetween.permute σ)
        (comparePathsBetween vts br) p₁.pathsToVertex p₂.pathsToVertex
      intro p hp q hq
      have hp_len : p.depth > 0 → p.connectedSubPaths.length = k + 1 := fun hp_d =>
        match List.mem_append.mp hp with
        | Or.inl hp_in => h_inner_len₁ p hp_in hp_d
        | Or.inr hp_in => h_inner_len₂ p hp_in hp_d
      have hq_len : q.depth > 0 → q.connectedSubPaths.length = k + 1 := fun hq_d =>
        match List.mem_append.mp hq with
        | Or.inl hq_in => h_inner_len₁ q hq_in hq_d
        | Or.inr hq_in => h_inner_len₂ q hq_in hq_d
      exact comparePathsBetween_σ_equivariant σ vts hvts br hbr p q hp_len hq_len

/-- The σ-invariance of `fromRanks` values in `calculatePathRankings`'s output.
Part of the deep Stage B content; requires foldl induction on the depth loop combined with
σ-equivariance of the compare/sort/rank assignment at each step. -/
theorem calculatePathRankings_fromRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (_hd : d < n) (s : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    (rs.fromRanks.getD d #[]).getD s.val 0
    = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0 := by
  sorry

/-- The σ-invariance of `betweenRanks` values in `calculatePathRankings`'s output.
Companion to `calculatePathRankings_fromRanks_inv`; the two are proved by a shared foldl
induction (sharing the same σ-invariance bookkeeping across the `betweenRanks`/`fromRanks`
pair, since each step updates both in tandem). -/
theorem calculatePathRankings_betweenRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (_hd : d < n) (s e : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
    = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0 := by
  sorry

/-- The σ-invariance of `calculatePathRankings`'s output, given σ ∈ Aut G and σ-invariant
typing. Sizes are discharged by `calculatePathRankings_size_inv` (proved); the value
invariance comes from the two `_inv` theorems above. -/
theorem calculatePathRankings_σInvariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    RankState.σInvariant σ (calculatePathRankings (initializePaths G) vts) where
  fromRanks_size := calculatePathRankings_fromRanks_size _ _
  betweenRanks_size := (calculatePathRankings_size_inv (initializePaths G) vts).1
  fromRanks_row_size := fun d hd =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.1 d hd
  betweenRanks_row_size := fun d hd =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.2.1 d hd
  betweenRanks_cell_size := fun d hd s hs =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.2.2 d s hd hs
  fromRanks_inv := calculatePathRankings_fromRanks_inv G σ hσ vts hvts
  betweenRanks_inv := calculatePathRankings_betweenRanks_inv G σ hσ vts hvts

/-- The genuine content of Stage B (the part not reducible to Stage A + σ ∈ Aut G):
the rank state computed from `initializePaths G` with a σ-invariant typing is itself
σ-invariant, so `RankState.permute σ` is the identity on it. Stage B follows from this
plus Stage A by substitution. -/
theorem calculatePathRankings_RankState_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    calculatePathRankings (initializePaths G) vts
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts) :=
  (calculatePathRankings_σInvariant G σ hσ vts hvts).permute_eq_self.symm

theorem calculatePathRankings_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    calculatePathRankings (PathState.permute σ (initializePaths G)) vts
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts) := by
  -- Stage A: PathState.permute σ (initializePaths G) = initializePaths (G.permute σ).
  -- σ ∈ Aut G: G.permute σ = G ⟹ initializePaths (G.permute σ) = initializePaths G.
  -- So LHS = calculatePathRankings (initializePaths G) vts.
  -- Then `calculatePathRankings_RankState_invariant` gives RHS.
  have hG : G.permute σ = G := hσ
  have hA := initializePaths_Aut_equivariant G σ
  rw [hG] at hA
  rw [← hA]
  exact calculatePathRankings_RankState_invariant G σ hσ vts hvts

/-! ## §4 — `convergeLoop` preserves Aut(G)-invariance -/

/-- The fold body of `convergeOnce` is invariant on positions outside the visited list:
positions `j` with `j ∉ l` are unchanged through `l.foldl`. -/
private theorem convergeOnce_fold_outside_unchanged (rs : RankState) (vc : Nat) :
    ∀ (l : List Nat) (start : Array VertexType × Bool) (j : Nat), j ∉ l →
      (l.foldl (fun (pair : Array VertexType × Bool) (vertexIdx : Nat) =>
          let (typeArray, changed) := pair
          let newRank := rs.getFrom (vc - 1) vertexIdx
          if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
          else (typeArray, changed)) start).1.getD j 0 = start.1.getD j 0
  | [], _, _, _ => rfl
  | x :: xs, start, j, hj => by
      rw [List.foldl_cons]
      have hj_x : j ≠ x := fun h => hj (h ▸ List.mem_cons_self ..)
      have hj_xs : j ∉ xs := fun h => hj (List.mem_cons_of_mem _ h)
      rw [convergeOnce_fold_outside_unchanged rs vc xs _ j hj_xs]
      -- Now show the one-step body at index x leaves position j unchanged.
      simp only []
      split
      · -- Update branch: typeArray.set! x newRank.
        have hxj : x ≠ j := fun h => hj_x h.symm
        simp only [Array.getD_eq_getD_getElem?,
                   Array.set!_eq_setIfInBounds,
                   Array.getElem?_setIfInBounds_ne hxj]
      · rfl

/-- After processing the prefix `[0, j+1)`, the position `j` holds `rs.getFrom (vc-1) j`. -/
private theorem convergeOnce_fold_writeback (rs : RankState) (vc : Nat) :
    ∀ (l : List Nat) (start : Array VertexType × Bool) (j : Nat),
      j ∈ l → l.Nodup → j < start.1.size →
      (l.foldl (fun (pair : Array VertexType × Bool) (vertexIdx : Nat) =>
          let (typeArray, changed) := pair
          let newRank := rs.getFrom (vc - 1) vertexIdx
          if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
          else (typeArray, changed)) start).1.getD j 0 = rs.getFrom (vc - 1) j
  | [], _, _, hj, _, _ => absurd hj List.not_mem_nil
  | x :: xs, start, j, hj, hnd, hsz => by
      rw [List.foldl_cons]
      have hxs_nd : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hnd).1
      rcases List.mem_cons.mp hj with h_eq | h_tail
      · -- j = x: after the x step, position x holds rs.getFrom (vc-1) x; the rest of the
        -- fold doesn't touch position x (since x ∉ xs).
        subst h_eq
        rw [convergeOnce_fold_outside_unchanged rs vc xs _ j hx_notin]
        -- One-step body at index j; `obtain` destructures the pair so we can examine the if.
        obtain ⟨arr, b⟩ := start
        simp only []
        by_cases hne : (rs.getFrom (vc - 1) j != arr.getD j 0) = true
        · rw [if_pos hne]
          show (arr.set! j (rs.getFrom (vc - 1) j)).getD j 0 = rs.getFrom (vc - 1) j
          simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_self_of_lt hsz]
        · rw [if_neg hne]
          show arr.getD j 0 = rs.getFrom (vc - 1) j
          have h_eq_val : rs.getFrom (vc - 1) j = arr.getD j 0 := by
            have h2 := (Bool.not_eq_true _).mp hne
            simpa [bne, beq_iff_eq] using h2
          exact h_eq_val.symm
      · -- j ∈ xs: by IH on xs after one step (whose size is preserved).
        -- The one step preserves `.1.size`. We let Lean infer the right form via `match`.
        have hsz' :
            j < (let (typeArray, changed) := start
                 let newRank := rs.getFrom (vc - 1) x
                 if (newRank != typeArray.getD x 0) = true then
                   (typeArray.set! x newRank, true)
                 else (typeArray, changed)).1.size := by
          obtain ⟨arr, b⟩ := start
          simp only []
          split
          · simpa using hsz
          · exact hsz
        exact convergeOnce_fold_writeback rs vc xs _ j h_tail hxs_nd hsz'

/-- After `convergeOnce`, every position holds the rank computed by `calculatePathRankings`.
The fold writes `getFrom (n-1) i` to slot `i` (replacing whatever was there), so the
output array satisfies `output[i] = rs.getFrom (n-1) i` for every in-bounds `i`. -/
theorem convergeOnce_writeback {vc : Nat} (state : PathState vc) (vts : Array VertexType)
    (i : Nat) (hi : i < vts.size) (hi_vc : i < vc) :
    (convergeOnce state vts).1.getD i 0 =
      (calculatePathRankings state vts).getFrom (vc - 1) i := by
  unfold convergeOnce
  apply convergeOnce_fold_writeback
  · exact List.mem_range.mpr hi_vc
  · exact List.nodup_range
  · exact hi

/-- Reduction lemma: applying `getFrom` to a `RankState.permute σ rs` reads from the
σ⁻¹-shifted position in the underlying `rs`. -/
theorem RankState.getFrom_permute (σ : Equiv.Perm (Fin n)) (rs : RankState) (d s : Nat)
    (hd : d < rs.fromRanks.size) (hs : s < n) :
    (RankState.permute σ rs).getFrom d s = rs.getFrom d (permNat σ⁻¹ s) := by
  unfold RankState.permute RankState.getFrom
  simp only []
  -- LHS: read d from the outer Array.range, then s from the inner.
  -- Both indices are in range; getD reduces to the mapped value.
  have hd' : d < (Array.range rs.fromRanks.size).size := by simp; exact hd
  have hs' : s < (Array.range n).size := by simp; exact hs
  rw [show ((Array.range rs.fromRanks.size).map fun d' =>
            let slice := rs.fromRanks.getD d' #[]
            (Array.range n).map fun s' => slice.getD (permNat σ⁻¹ s') 0).getD d #[]
        = ((Array.range rs.fromRanks.size).map fun d' =>
            let slice := rs.fromRanks.getD d' #[]
            (Array.range n).map fun s' => slice.getD (permNat σ⁻¹ s') 0)[d]'
              (by simp; exact hd) by
      rw [← Array.getElem_eq_getD]]
  rw [Array.getElem_map, Array.getElem_range]
  -- Now: ((Array.range n).map fun s' => (rs.fromRanks.getD d #[]).getD (permNat σ⁻¹ s') 0).getD s 0
  rw [show ((Array.range n).map fun s' =>
              (rs.fromRanks.getD d #[]).getD (permNat σ⁻¹ s') 0).getD s 0
        = ((Array.range n).map fun s' =>
              (rs.fromRanks.getD d #[]).getD (permNat σ⁻¹ s') 0)[s]'
              (by simp; exact hs) by
      rw [← Array.getElem_eq_getD]]
  rw [Array.getElem_map, Array.getElem_range]

/-- The σ-invariance of `getFrom (n-1)` extracted from
`calculatePathRankings_RankState_invariant`: positions `i` and `σ i` give the same value. -/
theorem calculatePathRankings_getFrom_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) (v : Fin n) :
    (calculatePathRankings (initializePaths G) vts).getFrom (n - 1) (σ v).val =
      (calculatePathRankings (initializePaths G) vts).getFrom (n - 1) v.val := by
  set rs := calculatePathRankings (initializePaths G) vts with hrs_def
  have hrs : rs = RankState.permute σ rs :=
    calculatePathRankings_RankState_invariant G σ hσ vts hvts
  -- Need: rs.fromRanks.size = n and n-1 < n (when n ≥ 1).
  -- Compute rs.fromRanks.size from the algorithm.
  have h_size : rs.fromRanks.size = n :=
    calculatePathRankings_fromRanks_size (initializePaths G) vts
  -- For n = 0: (σ v).val < 0 is impossible (v : Fin 0). Use Fin.elim0 to discharge.
  -- For n ≥ 1: apply RankState.getFrom_permute and the σ ∘ σ⁻¹ identity.
  cases n with
  | zero => exact v.elim0
  | succ k =>
    -- Apply hrs: rs = RankState.permute σ rs.
    -- Then unfold getFrom on both sides via RankState.getFrom_permute.
    have hd : k + 1 - 1 < rs.fromRanks.size := by
      rw [h_size]; omega
    have h_lhs : rs.getFrom (k + 1 - 1) (σ v).val
                  = rs.getFrom (k + 1 - 1) (permNat σ⁻¹ (σ v).val) := by
      conv_lhs => rw [hrs]
      exact RankState.getFrom_permute σ rs (k + 1 - 1) (σ v).val hd (σ v).isLt
    rw [h_lhs]
    -- Now: rs.getFrom _ (permNat σ⁻¹ (σ v).val) = rs.getFrom _ v.val
    congr 1
    rw [permNat_of_lt (σ v).isLt]
    show (σ⁻¹ (σ v)).val = v.val
    simp

theorem convergeOnce_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (hsize : vts.size = n) :
    ∀ v : Fin n,
      (convergeOnce (initializePaths G) vts).1.getD (σ v).val 0 =
      (convergeOnce (initializePaths G) vts).1.getD v.val 0 := by
  intro v
  have hv_size : v.val < vts.size := hsize ▸ v.isLt
  have hσv_size : (σ v).val < vts.size := hsize ▸ (σ v).isLt
  rw [convergeOnce_writeback (initializePaths G) vts (σ v).val hσv_size (σ v).isLt,
      convergeOnce_writeback (initializePaths G) vts v.val hv_size v.isLt]
  -- Goal: getFrom (n-1) (σ v).val = getFrom (n-1) v.val on the rank state.
  -- Adjust hypothesis form (`σ v`-as-Fin-n vs `(σ v).val`): they agree by definition.
  have hvts' : ∀ w : Fin n, vts.getD (σ w) 0 = vts.getD w 0 := fun w => by
    show vts.getD (σ w).val 0 = vts.getD w.val 0; exact hvts w
  exact calculatePathRankings_getFrom_invariant G σ hσ vts hvts' v

/-- `convergeOnce` preserves array size (only `.set!` writes, all in-bounds). Needed to
thread `vts.size = n` through the `convergeLoop` induction so `convergeOnce_Aut_invariant`
remains applicable at each step. -/
theorem convergeOnce_size_preserving {vc : Nat} (state : PathState vc) (vts : Array VertexType) :
    (convergeOnce state vts).1.size = vts.size := by
  unfold convergeOnce
  -- The fold accumulates `(typeArray, changed)`; show size of `.1` is preserved across the fold.
  set rs := calculatePathRankings state vts with hrs
  -- Generalize starting accumulator to handle the foldl induction cleanly.
  suffices haux : ∀ (l : List Nat) (start : Array VertexType × Bool),
      (l.foldl (fun pair vertexIdx =>
          let (typeArray, changed) := pair
          let newRank := rs.getFrom (vc - 1) vertexIdx
          if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
          else (typeArray, changed)) start).1.size = start.1.size by
    exact haux _ _
  intro l
  induction l with
  | nil => intro start; rfl
  | cons x xs ih =>
    intro start
    rw [List.foldl_cons, ih]
    -- After one step at index x: either .set! (size-preserving) or unchanged.
    simp only []
    split <;> simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem convergeLoop_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType) (fuel : Nat)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (hsize : vts.size = n) :
    ∀ v : Fin n,
      (convergeLoop (initializePaths G) vts fuel).getD (σ v).val 0 =
      (convergeLoop (initializePaths G) vts fuel).getD v.val 0 := by
  induction fuel generalizing vts with
  | zero =>
    intro v
    show vts.getD (σ v).val 0 = vts.getD v.val 0
    exact hvts v
  | succ k ih =>
    have hStep := convergeOnce_Aut_invariant G σ hσ vts hvts hsize
    have hStep_size : (convergeOnce (initializePaths G) vts).1.size = n := by
      rw [convergeOnce_size_preserving]; exact hsize
    intro v
    change (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD (σ v).val 0 =
           (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD v.val 0
    split
    · exact ih _ hStep hStep_size v
    · exact hStep v

theorem convergeLoop_zeros_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G) (fuel : Nat) :
    ∀ v : Fin n,
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD (σ v).val 0 =
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD v.val 0 := by
  apply convergeLoop_Aut_invariant G σ hσ
  · intro v
    simp [v.isLt, (σ v).isLt]
  · simp

/-! ## §3 Stage C — `orderVertices` equivariance -/

theorem orderVertices_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    orderVertices (PathState.permute σ (initializePaths G)) vts
      = orderVertices (initializePaths G) vts := by
  -- σ ∈ Aut G means G.permute σ = G, so by Stage A,
  -- `PathState.permute σ (initializePaths G) = initializePaths (G.permute σ) = initializePaths G`.
  have hG : G.permute σ = G := hσ
  have h := initializePaths_Aut_equivariant G σ
  rw [hG] at h
  rw [← h]

/-! ## §3 Stage D — `labelEdgesAccordingToRankings` equivariance -/

theorem labelEdges_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    labelEdgesAccordingToRankings vts (G.permute σ)
      = labelEdgesAccordingToRankings vts G := by
  -- σ ∈ Aut G means G.permute σ = G (by definition of Aut). The goal collapses by
  -- substitution; the σ-invariance of vts is not actually needed here.
  rw [show G.permute σ = G from hσ]

end Graph
