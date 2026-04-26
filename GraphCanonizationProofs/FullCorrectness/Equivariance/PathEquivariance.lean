import FullCorrectness.Equivariance.AssignListRankClosure

/-!
# Stage B σ-equivariance assembly  (`FullCorrectness.Equivariance.PathEquivariance`)

Assembles Stage B from the modular pieces in
`Equivariance.{CompareEquivariant, PathsAtDepthStructure, ChainSetInvariant, AssignListRankClosure}`:

The σ-cell-invariance of `calculatePathRankings`'s output is
`calculatePathRankings_σ_cell_inv_facts`, proved by depth-foldl induction
(`calculatePathRankings_body_preserves_inv` is the body step) using:
- `set_chain_σInvariant` / `setBetween_chain_σInvariant` (chain σ-inv preservation),
- `from_assignList_σ_rank_closure` / `between_assignList_σ_rank_closure` (σ-rank-closure),
- `initializePaths_pathsAtDepth_structure` / `initializePaths_allBetween_pairs_facts`
  (structural facts on `pathsAtDepth` and `allBetween`).

The two cell-level σ-invariance projections (`calculatePathRankings_fromRanks_inv`,
`calculatePathRankings_betweenRanks_inv`), the combined `RankState.σInvariant` form, and
the final `calculatePathRankings_Aut_equivariant` (Stage B in fixed-point form) are also
exposed here.
-/

namespace Graph

variable {n : Nat}

/-- The combined σ-cell-invariance + size invariant on a `(currentBetween, currentFrom)`
pair: this is the loop invariant of the depth foldl in `calculatePathRankings`. -/
private def CalcRankingsInv {n : Nat} (σ : Equiv.Perm (Fin n))
    (acc : Array (Array (Array Nat)) × Array (Array Nat)) : Prop :=
  acc.1.size = n ∧
  acc.2.size = n ∧
  (∀ d : Nat, d < n → (acc.1.getD d #[]).size = n) ∧
  (∀ d : Nat, d < n → (acc.2.getD d #[]).size = n) ∧
  (∀ d : Nat, d < n → ∀ s : Nat, s < n → ((acc.1.getD d #[]).getD s #[]).size = n) ∧
  (∀ d : Nat, d < n → ∀ s e : Fin n,
      ((acc.1.getD d #[]).getD s.val #[]).getD e.val 0
      = ((acc.1.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) ∧
  (∀ d : Nat, d < n → ∀ s : Fin n,
      (acc.2.getD d #[]).getD s.val 0
      = (acc.2.getD d #[]).getD (σ⁻¹ s).val 0)

/-- The body of the depth-foldl in `calculatePathRankings` preserves the combined invariant
`CalcRankingsInv σ`. -/
private theorem calculatePathRankings_body_preserves_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (acc : Array (Array (Array Nat)) × Array (Array Nat))
    (h_inv : CalcRankingsInv σ acc)
    (depth : Nat) (h_depth : depth < n) :
    CalcRankingsInv σ
      (let (currentBetween, currentFrom) := acc
       let pathsAtDepth := ((initializePaths G).pathsOfLength.getD depth #[]).toList
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
       (updatedBetween, updatedFrom)) := by
  obtain ⟨cb, cf⟩ := acc
  obtain ⟨h_cb_size, h_cf_size, h_cb_row, h_cf_row, h_cb_cell, h_cb_inv, h_cf_inv⟩ := h_inv
  -- State σ-fixed via Aut.
  have h_state_σ_fixed : PathState.permute σ (initializePaths G) = initializePaths G :=
    (initializePaths_σInv_via_Aut G σ hσ).symm
  -- Length facts about pathsAtDepth.
  obtain ⟨h_outer_len, h_starts_eq, h_pathsToVertex_len, h_inner_conn_len⟩ :=
    initializePaths_pathsAtDepth_structure G h_depth
  obtain ⟨h_pairs_nodup, h_pairs_complete⟩ :=
    initializePaths_allBetween_pairs_facts G h_depth
  -- σ-inv of betweenRankFn (current state) for all d (extended from d < n via the
  -- out-of-bounds case where cb.getD d #[] = #[]).
  have h_br_inv : ∀ d : Nat, ∀ s e : Fin n,
      ((cb.getD d #[]).getD (σ s).val #[]).getD (σ e).val 0
      = ((cb.getD d #[]).getD s.val #[]).getD e.val 0 := by
    intros d s e
    by_cases hd : d < n
    · exact betweenRankFn_σ_inv_from_cells σ cb h_cb_inv d hd s e
    · push_neg at hd
      have h : cb.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_cb_size]; exact hd),
            Option.getD_none]
      rw [h]
      simp
  -- between assignList: σ-rank-closure.
  have h_b_σ_closure :=
    between_assignList_σ_rank_closure σ (initializePaths G) h_state_σ_fixed
      vts hvts (fun rd rs re => ((cb.getD rd #[]).getD rs #[]).getD re 0)
      h_br_inv depth h_depth h_outer_len h_pathsToVertex_len h_inner_conn_len
  -- between assignList: Nodup of (s, e) pairs.
  set compareBetween := comparePathsBetween vts
    (fun rd rs re => ((cb.getD rd #[]).getD rs #[]).getD re 0) with h_compareBetween_def
  set allBetween := ((initializePaths G).pathsOfLength.getD depth #[]).toList.foldl
    (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [] with h_allBetween_def
  set assignList_b := assignRanks compareBetween (sortBy compareBetween allBetween) with h_assignList_b_def
  have h_b_nodup : (assignList_b.map (fun item =>
      (item.1.startVertexIndex.val, item.1.endVertexIndex.val))).Nodup := by
    have h_fst : assignList_b.map (·.1) = sortBy compareBetween allBetween := by
      rw [h_assignList_b_def]; exact assignRanks_map_fst _ _
    have h_eq : assignList_b.map (fun item => (item.1.startVertexIndex.val, item.1.endVertexIndex.val))
              = (sortBy compareBetween allBetween).map (fun pb : PathsBetween n =>
                  (pb.startVertexIndex.val, pb.endVertexIndex.val)) := by
      rw [← h_fst, List.map_map]; rfl
    rw [h_eq]
    have h_perm : ((sortBy compareBetween allBetween).map (fun pb : PathsBetween n =>
        (pb.startVertexIndex.val, pb.endVertexIndex.val))).Perm
        (allBetween.map (fun pb : PathsBetween n =>
          (pb.startVertexIndex.val, pb.endVertexIndex.val))) :=
      (sortBy_perm compareBetween allBetween).map _
    exact h_perm.nodup_iff.mpr h_pairs_nodup
  -- between assignList: Completeness of (s, e) pairs.
  have h_b_complete : ∀ s e : Fin n, ∃ item ∈ assignList_b,
      item.1.startVertexIndex.val = s.val ∧ item.1.endVertexIndex.val = e.val := by
    intros s e
    obtain ⟨q, h_q_in, h_q_start, h_q_end⟩ := h_pairs_complete s e
    have h_q_in_sort : q ∈ sortBy compareBetween allBetween :=
      (sortBy_perm compareBetween allBetween).mem_iff.mpr h_q_in
    have h_q_in_map : q ∈ assignList_b.map (·.1) := by
      rw [h_assignList_b_def, assignRanks_map_fst]; exact h_q_in_sort
    obtain ⟨item, h_item_in, h_item_eq⟩ := List.mem_map.mp h_q_in_map
    refine ⟨item, h_item_in, ?_, ?_⟩
    · rw [h_item_eq]; exact h_q_start
    · rw [h_item_eq]; exact h_q_end
  -- Apply setBetween_chain_σInvariant.
  have h_chain_b := setBetween_chain_σInvariant σ cb h_cb_size h_cb_row h_cb_cell h_cb_inv
    depth h_depth assignList_b h_b_nodup h_b_complete h_b_σ_closure
  -- Updated between σ-inv.
  obtain ⟨h_ub_size, h_ub_row, h_ub_cell, h_ub_inv⟩ := h_chain_b
  -- σ-inv of updatedBetweenFn.
  set updatedBetween := assignList_b.foldl
    (fun (betweenAcc : Array (Array (Array Nat))) item =>
      let (pathBetween, rank) := item
      setBetween betweenAcc depth pathBetween.startVertexIndex.val
        pathBetween.endVertexIndex.val rank) cb with h_updatedBetween_def
  have h_updatedBr_inv : ∀ d : Nat, ∀ s e : Fin n,
      ((updatedBetween.getD d #[]).getD (σ s).val #[]).getD (σ e).val 0
      = ((updatedBetween.getD d #[]).getD s.val #[]).getD e.val 0 := by
    intros d s e
    by_cases hd : d < n
    · exact betweenRankFn_σ_inv_from_cells σ updatedBetween h_ub_inv d hd s e
    · push_neg at hd
      have h : updatedBetween.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_ub_size]; exact hd),
            Option.getD_none]
      rw [h]; simp
  -- from-side σ-rank-closure.
  set compareFrom := comparePathsFrom vts
    (fun rd rs re => ((updatedBetween.getD rd #[]).getD rs #[]).getD re 0) with h_compareFrom_def
  have h_f_σ_closure :=
    from_assignList_σ_rank_closure σ (initializePaths G) h_state_σ_fixed
      vts hvts (fun rd rs re => ((updatedBetween.getD rd #[]).getD rs #[]).getD re 0)
      h_updatedBr_inv depth h_depth h_outer_len h_pathsToVertex_len h_inner_conn_len
  -- starts perm for from-side assignList.
  set assignList_f := assignRanks compareFrom
    (sortBy compareFrom ((initializePaths G).pathsOfLength.getD depth #[]).toList)
    with h_assignList_f_def
  have h_f_starts_perm : (assignList_f.map (·.1.startVertexIndex.val)).Perm (List.range n) := by
    have h_fst : assignList_f.map (·.1) = sortBy compareFrom
        ((initializePaths G).pathsOfLength.getD depth #[]).toList := by
      rw [h_assignList_f_def]; exact assignRanks_map_fst _ _
    have h_eq : assignList_f.map (·.1.startVertexIndex.val)
              = (sortBy compareFrom ((initializePaths G).pathsOfLength.getD depth #[]).toList).map
                  (·.startVertexIndex.val) := by
      rw [← h_fst, List.map_map]; rfl
    rw [h_eq]
    have h_perm : ((sortBy compareFrom
        ((initializePaths G).pathsOfLength.getD depth #[]).toList).map (·.startVertexIndex.val)).Perm
        (((initializePaths G).pathsOfLength.getD depth #[]).toList.map (·.startVertexIndex.val)) :=
      (sortBy_perm compareFrom _).map _
    rw [h_starts_eq] at h_perm
    exact h_perm
  -- Apply set_chain_σInvariant.
  have h_chain_f := set_chain_σInvariant σ cf h_cf_size h_cf_row h_cf_inv
    depth h_depth assignList_f h_f_starts_perm h_f_σ_closure
  obtain ⟨h_uf_size, h_uf_row, h_uf_inv⟩ := h_chain_f
  -- Combine into CalcRankingsInv.
  exact ⟨h_ub_size, h_uf_size, h_ub_row, h_uf_row, h_ub_cell, h_ub_inv, h_uf_inv⟩

/-- **Cell-level σ-invariance facts** for `calculatePathRankings`'s output. The deep
content. Proved via depth-foldl induction over `List.range n`; the inductive step uses
`set_chain_σInvariant` / `setBetween_chain_σInvariant` (with the σ-rank-closure lemmas
`from_assignList_σ_rank_closure` / `between_assignList_σ_rank_closure`) plus the
structural facts about `pathsAtDepth` and `allBetween` from `initializePaths G`. -/
private theorem calculatePathRankings_σ_cell_inv_facts
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    let rs := calculatePathRankings (initializePaths G) vts
    (∀ d : Nat, d < n → ∀ s : Fin n,
        (rs.fromRanks.getD d #[]).getD s.val 0
        = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
        ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
        = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  -- Coerce hvts to the .val form expected by helpers.
  have hvts' : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0 := hvts
  -- Unfold calculatePathRankings.
  unfold calculatePathRankings
  -- Reduce to a foldl-invariant statement.
  suffices h_inv :
      CalcRankingsInv σ
        ((List.range n).foldl
          (fun accumulated depth =>
            let (currentBetween, currentFrom) := accumulated
            let pathsAtDepth := ((initializePaths G).pathsOfLength.getD depth #[]).toList
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
            (updatedBetween, updatedFrom))
          ((Array.range n).map fun _ => (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat),
           (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat))) by
    obtain ⟨_, _, _, _, _, h_b_inv, h_f_inv⟩ := h_inv
    exact ⟨h_f_inv, h_b_inv⟩
  -- Foldl induction with body_preserves_inv.
  -- Initial CalcRankingsInv on (empty, empty).
  have h_init : CalcRankingsInv σ
      ((Array.range n).map fun _ => (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat),
       (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro d hd; simp [hd]
    · intro d hd; simp [hd]
    · intro d hd s hs; simp [hd, hs]
    · intro d hd s e
      -- All cells are 0 in the empty table.
      have h_get_d : ((((Array.range n).map fun _ =>
            (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat))).getD d #[]).size = n := by
        simp [hd]
      -- Both sides are getD ... 0 = 0.
      have h_lhs : (((((Array.range n).map fun _ =>
              (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat))).getD d #[]).getD s.val #[]).getD e.val 0 = 0 := by
        simp [hd]
      have h_rhs : (((((Array.range n).map fun _ =>
              (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat))).getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0 = 0 := by
        simp [hd]
      rw [h_lhs, h_rhs]
    · intro d hd s
      have h_lhs : ((((Array.range n).map fun _ =>
            (Array.range n).map fun _ : Nat => (0 : Nat))).getD d #[]).getD s.val 0 = 0 := by
        simp [hd]
      have h_rhs : ((((Array.range n).map fun _ =>
            (Array.range n).map fun _ : Nat => (0 : Nat))).getD d #[]).getD (σ⁻¹ s).val 0 = 0 := by
        simp [hd]
      rw [h_lhs, h_rhs]
  -- Foldl induction.
  generalize h_acc_eq :
    ((Array.range n).map fun _ => (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat),
     (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat)) = acc₀
  rw [h_acc_eq] at h_init
  -- Generalize over the list (List.range n) and the initial accumulator.
  suffices h_step : ∀ (l : List Nat) (acc₀ : Array (Array (Array Nat)) × Array (Array Nat)),
      (∀ d ∈ l, d < n) → CalcRankingsInv σ acc₀ →
      CalcRankingsInv σ (l.foldl (fun accumulated depth =>
        let (currentBetween, currentFrom) := accumulated
        let pathsAtDepth := ((initializePaths G).pathsOfLength.getD depth #[]).toList
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
        (updatedBetween, updatedFrom)) acc₀) by
    have h_l_lt : ∀ d ∈ List.range n, d < n := fun d hd => List.mem_range.mp hd
    exact h_step (List.range n) acc₀ h_l_lt h_init
  intro l
  induction l with
  | nil => intros _ _ h_inv; exact h_inv
  | cons x xs ih =>
    intros acc₀ h_l_lt h_inv
    rw [List.foldl_cons]
    apply ih
    · intros d h_d_in
      exact h_l_lt d (List.mem_cons_of_mem _ h_d_in)
    · -- Apply body_preserves_inv with depth = x.
      have h_x_lt : x < n := h_l_lt x List.mem_cons_self
      exact calculatePathRankings_body_preserves_inv G σ hσ vts hvts' acc₀ h_inv x h_x_lt

/-- **Combined σ-invariance** of `calculatePathRankings`'s output: the full
`RankState.σInvariant σ rs` for `rs := calculatePathRankings (initializePaths G) vts`.
Sizes from `calculatePathRankings_size_inv`; cell σ-inv from
`calculatePathRankings_σ_cell_inv_facts`. -/
theorem calculatePathRankings_σInvariant_combined
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    RankState.σInvariant σ (calculatePathRankings (initializePaths G) vts) := by
  have h_size := calculatePathRankings_size_inv (initializePaths G) vts
  obtain ⟨h_from_inv, h_between_inv⟩ :=
    calculatePathRankings_σ_cell_inv_facts G σ hσ vts hvts
  exact {
    fromRanks_size := calculatePathRankings_fromRanks_size _ _,
    betweenRanks_size := h_size.1,
    fromRanks_row_size := fun d hd => h_size.2.2.1 d hd,
    betweenRanks_row_size := fun d hd => h_size.2.2.2.1 d hd,
    betweenRanks_cell_size := fun d hd s hs => h_size.2.2.2.2 d s hd hs,
    fromRanks_inv := h_from_inv,
    betweenRanks_inv := h_between_inv,
  }

/-- The σ-invariance of `fromRanks` values: projection of `σInvariant_combined`. -/
theorem calculatePathRankings_fromRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (hd : d < n) (s : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    (rs.fromRanks.getD d #[]).getD s.val 0
    = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0 :=
  (calculatePathRankings_σInvariant_combined G σ hσ vts hvts).fromRanks_inv d hd s

/-- The σ-invariance of `betweenRanks` values: projection of `σInvariant_combined`. -/
theorem calculatePathRankings_betweenRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (hd : d < n) (s e : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
    = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0 :=
  (calculatePathRankings_σInvariant_combined G σ hσ vts hvts).betweenRanks_inv d hd s e

/-- The σ-invariance of `calculatePathRankings`'s output: a direct alias for
`calculatePathRankings_σInvariant_combined`. -/
theorem calculatePathRankings_σInvariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    RankState.σInvariant σ (calculatePathRankings (initializePaths G) vts) :=
  calculatePathRankings_σInvariant_combined G σ hσ vts hvts

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


end Graph
