import FullCorrectness.Isomorphic

/-!
# Permutation actions on path data structures  (`FullCorrectness.Equivariance.Actions`)

Defines `permNat` and the `Equiv.Perm (Fin n)` action on the canonizer's intermediate
data structures: `PathSegment.permute`, `PathsBetween.permute`, `PathsFrom.permute`,
`PathState.permute`, `RankState.permute`.

Also contains structural sanity lemmas (`initializePaths_pathsOfLength_size`, etc.)
that are needed throughout the equivariance proof.
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


end Graph
