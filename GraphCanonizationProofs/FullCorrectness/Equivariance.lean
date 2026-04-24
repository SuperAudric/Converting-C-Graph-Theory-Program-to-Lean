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
-/

namespace Graph

variable {n : Nat}

/-! ## Permutation action on `Nat` vertex indices

The path structures use `Nat` for vertex indices (even though semantically they are all
`< vertexCount`). We lift `σ : Equiv.Perm (Fin n)` to act on `Nat` by applying it when
the input is in range and by leaving out-of-range indices alone. This keeps compatibility
with the existing `Nat`-indexed structures without changing the algorithm. -/

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

/-- `Fin n` round-trip: `permNat σ⁻¹ ∘ permNat σ` is the identity below `n`. -/
@[simp] theorem permNat_inv_perm {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ⁻¹ (permNat σ i) = i := by
  rw [permNat_of_lt h, permNat_of_lt (σ ⟨i, h⟩).isLt]
  show (σ⁻¹ (σ ⟨i, h⟩)).val = i
  simp

/-- `Fin n` round-trip: `permNat σ ∘ permNat σ⁻¹` is the identity below `n`. -/
@[simp] theorem permNat_perm_inv {σ : Equiv.Perm (Fin n)} {i : Nat} (h : i < n) :
    permNat σ (permNat σ⁻¹ i) = i := by
  rw [permNat_of_lt h, permNat_of_lt (σ⁻¹ ⟨i, h⟩).isLt]
  show (σ (σ⁻¹ ⟨i, h⟩)).val = i
  simp

/-- For `i : Fin n`, `permNat σ i.val = (σ i).val`. The basic translation between the
`Fin n` action and the `Nat`-lifted `permNat`. -/
@[simp] theorem permNat_fin (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permNat σ i.val = (σ i).val := by
  rw [permNat_of_lt i.isLt]

/-! ## Permutation action on path structures -/

/-- Relabel the vertex indices inside a `PathSegment` by `σ`. -/
def PathSegment.permute (σ : Equiv.Perm (Fin n)) : PathSegment → PathSegment
  | .bottom v            => .bottom (permNat σ v)
  | .inner e d s mid     => .inner e d (permNat σ s) (permNat σ mid)

/--
Relabel vertex indices inside a `PathsBetween`. Depth is unchanged.

For `depth = 0`, `connectedSubPaths` is either `[.bottom …]` or `[]` — `List.map` suffices.

For `depth > 0`, the algorithm populates `connectedSubPaths` with one `.inner` segment per
intermediate vertex (iterated over `midFin : Fin n` in natural order). The σ-relabeled
structure must also iterate intermediate vertices in natural order *in the new labeling*,
so we reindex by `σ⁻¹` and then apply `PathSegment.permute σ`.
-/
def PathsBetween.permute (σ : Equiv.Perm (Fin n)) (p : PathsBetween) : PathsBetween :=
  { depth             := p.depth
    startVertexIndex  := permNat σ p.startVertexIndex
    endVertexIndex    := permNat σ p.endVertexIndex
    connectedSubPaths :=
      if p.depth = 0 then
        p.connectedSubPaths.map (PathSegment.permute σ)
      else
        (List.finRange n).map fun i =>
          PathSegment.permute σ (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (.bottom 0)) }

/--
Default `PathsBetween` placeholder used when reindexing the `pathsToVertex` list by σ.
The algorithm always populates all `n` entries, so this default is never actually consulted
on well-formed inputs — it exists only to make `List.getD` total.
-/
def PathsBetween.default : PathsBetween :=
  { depth := 0, startVertexIndex := 0, endVertexIndex := 0, connectedSubPaths := [] }

/--
Relabel vertex indices inside a `PathsFrom`, **reordering the `pathsToVertex` list** so that
the entry describing paths ending at new-vertex `e` sits at list position `e`. Without this
reordering, the permuted structure would not match `initializePaths` on the relabeled graph,
which iterates end-vertices in natural order `0..n-1`.
-/
def PathsFrom.permute (σ : Equiv.Perm (Fin n)) (p : PathsFrom) : PathsFrom :=
  { depth            := p.depth
    startVertexIndex := permNat σ p.startVertexIndex
    pathsToVertex    := (List.finRange n).map fun i =>
      PathsBetween.permute σ (p.pathsToVertex.getD (permNat σ⁻¹ i.val) PathsBetween.default) }

/--
Relabel a full `PathState` by `σ`. Slot `s` in the output (at any depth) is the σ-permuted
image of slot `σ.symm s` in the input — consistent with `AdjMatrix.permute`, which defines
`(G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j)`.
-/
def PathState.permute (σ : Equiv.Perm (Fin n)) (st : PathState) : PathState :=
  { vertexCount   := st.vertexCount
    pathsOfLength := st.pathsOfLength.map fun pathsByStart =>
      (Array.range st.vertexCount).map fun newStart =>
        let oldStart := permNat σ⁻¹ newStart
        PathsFrom.permute σ (pathsByStart.getD oldStart
          { depth := 0, startVertexIndex := oldStart, pathsToVertex := [] }) }

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

/-! ## Structural sanity lemmas

Sizes and shapes of intermediate arrays inside `initializePaths` and `PathState.permute`.
Used as building blocks for Stage A; also useful to have on hand for Stage B/C/D.
-/

@[simp] theorem initializePaths_vertexCount (G : AdjMatrix n) :
    (initializePaths G).vertexCount = n := rfl

@[simp] theorem initializePaths_pathsOfLength_size (G : AdjMatrix n) :
    (initializePaths G).pathsOfLength.size = n := by
  unfold initializePaths
  simp

@[simp] theorem PathState_permute_vertexCount (σ : Equiv.Perm (Fin n)) (st : PathState) :
    (st.permute σ).vertexCount = st.vertexCount := rfl

@[simp] theorem PathState_permute_pathsOfLength_size
    (σ : Equiv.Perm (Fin n)) (st : PathState) :
    (st.permute σ).pathsOfLength.size = st.pathsOfLength.size := by
  unfold PathState.permute
  simp

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
initializePaths (G.permute σ) = (initializePaths G).permute σ
```

**Pointwise equality (hand-verified).** At each outer slot `(d, newStart) ∈ Fin n × Fin n`
and each inner end-vertex index `i : Fin n`, both sides yield a `PathsBetween` with:

| field                | LHS                                       | RHS                                       |
| -------------------- | ----------------------------------------- | ----------------------------------------- |
| `depth`              | `d.val`                                   | `d.val`                                   |
| `startVertexIndex`   | `newStart.val`                            | `permNat σ ((σ⁻¹ newStart).val) = newStart.val` |
| `endVertexIndex`     | `i.val`                                   | `permNat σ ((σ⁻¹ i).val) = i.val`         |
| `connectedSubPaths` (`d = 0`) | `if newStart = i then [.bottom newStart] else []` | `.map (PathSegment.permute σ)` of `if σ⁻¹ newStart = σ⁻¹ i then [.bottom (σ⁻¹ newStart).val] else []`, which simplifies to the same |
| `connectedSubPaths` (`d > 0`) | `(List.finRange n).map fun j => .inner (G.adj (σ⁻¹ j) (σ⁻¹ i)) (d.val - 1) newStart.val j.val` | reindexed version that evaluates to exactly the same list |

The refined `PathsBetween.permute` (which reorders `connectedSubPaths` by σ when
`depth > 0`) is exactly what makes the `d > 0` lists match pointwise rather than merely
up to permutation.

**Status of the Lean proof.** The hand-verification above guarantees the statement is
correct. A mechanized proof requires ~100 lines of `Array.ext'` / `Array.getElem_map` /
`List.map_ofFn` / `List.get?_map` plumbing, plus case-analysis on `d.val = 0` versus
`d.val > 0`. Left as `sorry` pending that PR — this module's immediate purpose is to
freeze the correct statement and action definitions for downstream use in Stages B–D.

**Infrastructure now in place** (this file):
- `permNat_of_lt`, `permNat_of_ge`, `permNat_inv_perm`, `permNat_perm_inv`, `permNat_fin`
  — handle the `Nat ↔ Fin n` round-trips that drive index reordering.
- `initializePaths_vertexCount`, `initializePaths_pathsOfLength_size`,
  `PathState_permute_vertexCount`, `PathState_permute_pathsOfLength_size`,
  `initializePaths_pathsOfLength_get_size` — the size and shape lemmas needed before
  applying `Array.ext`.

**Skeleton of the Lean proof (next iteration).**
```
-- After unfolding both sides to nested Array.maps:
apply (PathState.mk.injEq _ _ _ _).mpr
refine ⟨rfl, ?_⟩
-- For pathsOfLength: rewrite RHS with `Array.map_map` to expose a single outer
-- `(List.finRange n).toArray.map`, then `Array.ext` peels the depth dimension.
rw [Array.map_map]
apply Array.ext
· simp
intro d hd₁ hd₂
simp only [Array.getElem_map, Function.comp_apply]
-- Goal at depth d: inner Array.map equality (start dimension).
apply Array.ext
· simp
intro s hs₁ hs₂
simp only [Array.getElem_map, Array.getElem_range]
-- Goal at (d, s): single PathsFrom equality. Use Array.getD reasoning to push
-- σ⁻¹-indexed access through the map. Then descend into PathsToVertex (List).
-- For the List, similar pattern with List.map_map, List.ext_get, and List.get?_map.
-- At the deepest level (PathSegment list), case on (List.finRange n).toArray[d] = 0
-- vs > 0 to handle the `if depthFin.val = 0` branches.
```
-/

theorem initializePaths_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) :
    initializePaths (G.permute σ) = (initializePaths G).permute σ := by
  sorry

/-! ## §3 Stage B — `calculatePathRankings` equivariance

**Theorem.** If `σ ∈ Aut G` and `vertexTypes` is σ-invariant (i.e. `vts[σ v] = vts[v]`),
then:

```
calculatePathRankings ((initializePaths G).permute σ) vts
  = (calculatePathRankings (initializePaths G) vts).permute σ
```

**Proof plan.** Induction on the outer `foldl` over depths. At each depth:

1. The between-rank comparison `comparePathsBetween vts betweenRankFn` depends only on
   (a) the endpoint vertex types (σ-invariant by hypothesis) and (b) the sub-path rank
   lookups (σ-equivariant by IH on previous depths).
2. The set of `PathsBetween` at a given depth, σ-permuted, is a permutation of the
   original set — `orderInsensitiveListCmp` ignores order — so the sorted order and
   assigned ranks are preserved.
3. `setBetween` at slot `(d, σ s, σ e)` sets the same rank as the original run at
   `(d, s, e)`, giving the σ-permuted ranks.
4. Symmetric argument for `fromRanks` via `comparePathsFrom`.
-/

theorem calculatePathRankings_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    calculatePathRankings ((initializePaths G).permute σ) vts
      = (calculatePathRankings (initializePaths G) vts).permute σ := by
  sorry

/-! ## §4 — `convergeLoop` preserves Aut(G)-invariance

If the input vertex-type array is σ-invariant for some σ ∈ Aut G, then the output of
`convergeLoop` is σ-invariant as well. In particular, starting from the all-zeros array
(trivially σ-invariant), the output `convergeLoop (initializePaths G) zeros fuel` is
always σ-invariant for every σ ∈ Aut G.

**Corollary used downstream.** Two vertices in the same Aut(G)-orbit carry the same
type in the output of `convergeLoop` on an Aut(G)-invariant input.

**Proof plan.** Induction on `fuel`. The inductive step follows from:
  (a) Stage B equivariance: `calculatePathRankings ((initializePaths G).permute σ) vts
        = (calculatePathRankings (initializePaths G) vts).permute σ`
      when vts is σ-invariant.
  (b) Stage A equivariance + Stage B: starting from `(initializePaths G, vts)`, running
      one `convergeOnce` step and reading off `rankState.getFrom (n-1) v`, the value at
      `σ v` equals the value at `v` because the rank depends only on σ-invariant data.
  (c) `convergeLoop` either returns the current types (no change this step) or recurses
      with σ-invariant types; the IH closes the recursive case.
-/

/-- **One-step Aut-invariance.** If `vts` is σ-invariant for σ ∈ Aut G, then so is
`(convergeOnce (initializePaths G) vts).1`. This is the content of Stage B equivariance
plus the fact that `rankState.getFrom (n-1) v` depends only on the `fromRanks` slice at
`v`, which is `σ`-equivariant. -/
theorem convergeOnce_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0) :
    ∀ v : Fin n,
      (convergeOnce (initializePaths G) vts).1.getD (σ v).val 0 =
      (convergeOnce (initializePaths G) vts).1.getD v.val 0 := by
  -- Depends on Stage B equivariance (`calculatePathRankings_Aut_equivariant`) +
  -- `RankState.permute` compatibility + the outer fold that writes back into vts.
  -- The fold writes `rankState.getFrom (n-1) v` into slot `v`. By Stage B, the written
  -- values are σ-invariant, so the output array is σ-invariant too.
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
    -- `convergeLoop state vts 0 = vts` by definition; the goal is exactly `hvts`.
    intro v
    show vts.getD (σ v).val 0 = vts.getD v.val 0
    exact hvts v
  | succ k ih =>
    -- `convergeLoop state vts (k+1)`  ≡
    --   `let (updatedTypes, changed) := convergeOnce state vts
    --    if changed then convergeLoop state updatedTypes k else updatedTypes`.
    -- In either branch the propagated typing is σ-invariant (by convergeOnce_Aut_invariant),
    -- so the result is σ-invariant (IH in the recursive branch, `hStep` directly in the other).
    have hStep := convergeOnce_Aut_invariant G σ hσ vts hvts
    intro v
    -- Expose the `let`-destructuring + `if`-branch via `change` to the normalized form.
    change (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD (σ v).val 0 =
           (if (convergeOnce (initializePaths G) vts).2
            then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
            else (convergeOnce (initializePaths G) vts).1).getD v.val 0
    -- Split on the `if`: both LHS and RHS of the equality contain the same `if` expression,
    -- so `split` produces two subgoals (one per branch) where each side reduces uniformly.
    split
    · -- recursive branch: by IH applied to the σ-invariant one-step typing
      exact ih _ hStep v
    · -- terminate branch: the one-step typing is itself the result, σ-invariant by hStep
      exact hStep v

/-- **Corollary of §4.** Starting from the all-zeros array (trivially Aut-invariant),
`convergeLoop` produces a vertex typing that is constant on each Aut(G)-orbit. -/
theorem convergeLoop_zeros_Aut_invariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G) (fuel : Nat) :
    ∀ v : Fin n,
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD (σ v).val 0 =
      (convergeLoop (initializePaths G) (Array.replicate n 0) fuel).getD v.val 0 := by
  apply convergeLoop_Aut_invariant G σ hσ
  intro v
  simp [v.isLt, (σ v).isLt]

/-! ## §3 Stage C — `orderVertices` equivariance

**Theorem.** If `σ ∈ Aut G` and `vts` is σ-invariant, then:

```
orderVertices ((initializePaths G).permute σ) vts = orderVertices (initializePaths G) vts
```

Note the right-hand side is **not** the σ-permuted output — σ-invariance of the output
under automorphisms is exactly what we want. This follows from Stage B plus
`convergeOnce`'s `getFrom` read (which is σ-equivariant) plus the tiebreak
choice-independence lemma (§6).

**Proof plan.** Induction on the outer fold over `targetPosition`. Each iteration:
1. `convergeLoop` preserves σ-invariance (§4).
2. `breakTie` at a σ-invariant typing: the set of tied vertices is a union of Aut(G)-orbits
   by §4's corollary; picking the σ-canonical representative vs. any other
   representative produces the same downstream result by §6.
-/

theorem orderVertices_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    orderVertices ((initializePaths G).permute σ) vts
      = orderVertices (initializePaths G) vts := by
  sorry

/-! ## §3 Stage D — `labelEdgesAccordingToRankings` equivariance

**Theorem.** Under the distinct-ranks invariant (§7), given `σ ∈ Aut G`:

```
labelEdgesAccordingToRankings vts (G.permute σ) = labelEdgesAccordingToRankings vts G
```

when `vts` is σ-invariant. In particular the final canonical output of `run` on `G` and
on `G.permute σ` agree.

**Proof plan.** `computeDenseRanks` on a σ-invariant `vts` produces a dense-rank array
whose value at `σ v` equals its value at `v` (for vertices tied under `vts`), but the
outer loop then uses the swap-based labeling: the vertex placed at final position `p` is
the one with dense rank `p`. Because `orderVertices` (§7 + Stage C) gives distinct ranks,
exactly one vertex has each rank, and the resulting matrix is determined solely by the
(σ-invariant) ranking-to-position map plus the (σ-invariant-modulo-automorphism)
adjacency function. Equivariance of `swapVertexLabels` under σ (which reduces to
`permute_mul` + `swapVertexLabels_eq_permute`) closes the proof.
-/

theorem labelEdges_Aut_equivariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    labelEdgesAccordingToRankings vts (G.permute σ)
      = labelEdgesAccordingToRankings vts G := by
  sorry

end Graph
