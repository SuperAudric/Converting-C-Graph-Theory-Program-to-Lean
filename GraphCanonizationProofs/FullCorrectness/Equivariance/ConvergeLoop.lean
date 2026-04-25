import FullCorrectness.Equivariance.PathEquivariance

/-!
# §4 — `convergeLoop` Aut(G)-invariance and Stages C/D  (`FullCorrectness.Equivariance.ConvergeLoop`)

Proves that one step and the full convergence loop preserve Aut(G)-invariance of vertex
type arrays, and assembles the trivial Stage C / Stage D equivariance results.

## Key theorems

- `convergeOnce_writeback` — after `convergeOnce`, position `v` holds `getFrom (n-1) v`.
- `RankState.getFrom_permute` — `getFrom` on a permuted rank state.
- `calculatePathRankings_getFrom_invariant` — σ-invariance of `getFrom (n-1)` on the
  `calculatePathRankings` output (derived from `calculatePathRankings_RankState_invariant`).
- `convergeOnce_Aut_invariant` — one `convergeOnce` step preserves Aut-invariance.
- `convergeOnce_size_preserving` — `convergeOnce` preserves the type-array size.
- `convergeLoop_Aut_invariant` — full loop preserves Aut-invariance (induction on fuel).
- `convergeLoop_zeros_Aut_invariant` — corollary for the all-zeros starting array.
- `orderVertices_Aut_equivariant` — Stage C (trivial via Stage A + σ ∈ Aut G).
- `labelEdges_Aut_equivariant` — Stage D (trivial: G.permute σ = G for σ ∈ Aut G).
-/

namespace Graph

variable {n : Nat}

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
