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
