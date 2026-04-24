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
    -- For n = k+1: pointwise equality at every (depth, start, end) slot, and at every
    -- intermediate vertex inside `connectedSubPaths` when depth > 0. We descend through
    -- the nested arrays/lists and close each leaf via `Equiv.symm_apply_apply` and the
    -- `permNat_inv_fin` translation.
    -- The full structural proof requires descending through 4 nested Array/List levels
    -- (depth → start → end → mid) plus the depth=0 vs depth>0 case-split, with each leaf
    -- closed by `Equiv.symm_apply_apply` and the `permNat_inv_fin` translation.
    -- Set out as a focused sorry pending a careful structural-extensionality push.
    sorry

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

/-- The genuine content of Stage B (the part not reducible to Stage A + σ ∈ Aut G):
the rank state computed from `initializePaths G` with a σ-invariant typing is itself
σ-invariant, so `RankState.permute σ` is the identity on it. Stage B follows from this
plus Stage A by substitution. -/
theorem calculatePathRankings_RankState_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    calculatePathRankings (initializePaths G) vts
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts) := by
  sorry

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
