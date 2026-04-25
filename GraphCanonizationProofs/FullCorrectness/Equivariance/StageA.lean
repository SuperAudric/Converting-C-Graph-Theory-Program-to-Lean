import FullCorrectness.Equivariance.Actions

/-!
# §3 Stage A — `initializePaths` equivariance  (`FullCorrectness.Equivariance.StageA`)

Proves that for any `σ : Equiv.Perm (Fin n)`, the path state built for `G.permute σ`
equals the σ-relabeling of the path state built for `G`:

```
initializePaths (G.permute σ) = PathState.permute σ (initializePaths G)
```

No `Aut G` hypothesis is needed for Stage A — it holds for any permutation.
-/

namespace Graph

variable {n : Nat}

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


end Graph
