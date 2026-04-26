import FullCorrectness.Equivariance.PathEquivarianceRelational

/-!
# Phase 6 Stage B-rel general σ (P6.A)
  (`FullCorrectness.Equivariance.PathEquivarianceGeneral`)

The σ ∈ Aut G version of Stage B-rel (`calculatePathRankings_σ_equivariant_relational`)
in `PathEquivarianceRelational.lean` requires `PathState.permute σ state = state`.
Phase 6's `run_swap_invariant_fwd` (σ ∉ Aut G branch) needs the general form, where
the second `calculatePathRankings` call runs on `PathState.permute σ state` (a
different state from the first call's `state`).

## Status

Foundational lemmas (`pathsOfLength_two_states_at_σ_slot`,
`pathsAtDepth_two_states_perm`) are landing here. The body-step lemma and final
assembly are pending and remain `sorry`-blocked.

## Proof structure (mirroring the σ ∈ Aut G version in `PathEquivarianceRelational`)

**Foundational geometric lemmas:**
  - `pathsOfLength_two_states_at_σ_slot` — array-level σ-shift between
    `state₁.pathsOfLength.getD d #[]` and `state₂ := PathState.permute σ state₁`.
    Mirrors `state_σ_fixed_pathsOfLength_at_σ_slot` (Aut version) but compares
    two distinct states. ✅ proved here.

  - `pathsAtDepth_two_states_perm` — `pathsAtDepth state₂ ~Perm
    (pathsAtDepth state₁).map (PathsFrom.permute σ)`. Mirrors `pathsAtDepth_map_f_perm`
    (Aut version) using `pathsOfLength_two_states_at_σ_slot` + `map_reindex_perm`.
    ✅ proved here.

  - `mem_pathsAtDepth_two_states_under_f` — Perm-corollary: for `p ∈ pathsAtDepth state₁`,
    `PathsFrom.permute σ p ∈ pathsAtDepth state₂`. Pending.

  - `allBetween_two_states_perm` — same chain as `allBetween_map_f_perm`. Pending.

  - `mem_allBetween_two_states_under_f` — Pending.

**Relational σ-rank-closure (mirrors Phase 1):**
  - `from_assignList_σ_rank_general` — Pending.
  - `between_assignList_σ_rank_general` — Pending.

**Body step + foldl induction + final assembly:**
  - `calculatePathRankings_body_preserves_general` — Pending.
  - `calculatePathRankings_σ_cell_general_facts` — Pending.
  - `calculatePathRankings_σ_equivariant_general` — top-level statement; `sorry` until
    the body-step closes.

## Top-level statement (P6.A target)
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## Foundational lemma 1 — pathsOfLength two-states slot identity

Given `state₂ := PathState.permute σ state₁`, slot `(σ s).val` of `state₂`'s
depth-`depth` array equals `PathsFrom.permute σ (state₁_arr[s.val])`. This is the
two-state generalization of `state_σ_fixed_pathsOfLength_at_σ_slot` (Aut version).

The σ-fixed version corresponds to `state₂ = state₁`; the general version exposes
the σ-shift between two distinct states. -/

private theorem pathsOfLength_two_states_at_σ_slot
    (σ : Equiv.Perm (Fin n)) (state₁ : PathState n)
    (depth : Nat) (h_depth : depth < state₁.pathsOfLength.size)
    (h_inner_size : (state₁.pathsOfLength.getD depth #[]).size = n)
    (s : Fin n)
    (h_σs_lt₂ :
      (σ s).val < ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).size)
    (h_s_lt₁ : s.val < (state₁.pathsOfLength.getD depth #[]).size) :
    ((PathState.permute σ state₁).pathsOfLength.getD depth #[])[(σ s).val]'h_σs_lt₂
      = PathsFrom.permute σ ((state₁.pathsOfLength.getD depth #[])[s.val]'h_s_lt₁) := by
  -- Handle n = 0 vacuously (Fin 0 is empty).
  by_cases hn : n = 0
  · subst hn; exact s.elim0
  -- For n ≥ 1, peel off n = k + 1 to unfold `PathState.permute`.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- The map identity (analogous to σ-fixedness, but pointing to a different state):
  -- the σ-permuted pathsOfLength equals the map of state₁'s pathsOfLength.
  have h_map_eq : state₁.pathsOfLength.map (fun pathsByStart =>
      (Array.range (k + 1)).map fun newStart =>
        PathsFrom.permute σ (pathsByStart.getD (permNat σ⁻¹ newStart)
          { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))
      = (PathState.permute σ state₁).pathsOfLength := rfl
  -- Helper: array equality projected at a fixed index. Avoids motive issues.
  have h_get_at : ∀ {α : Type} {M N : Array α} (h : M = N) (i : Nat)
      (h_M : i < M.size) (h_N : i < N.size), M[i]'h_M = N[i]'h_N := by
    intros _ M N h _ _ _; subst h; rfl
  -- Project h_map_eq at depth on both sides.
  have h_depth_map : depth < (state₁.pathsOfLength.map (fun pathsByStart =>
      (Array.range (k + 1)).map fun newStart =>
        PathsFrom.permute σ (pathsByStart.getD (permNat σ⁻¹ newStart)
          { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size := by
    rw [Array.size_map]; exact h_depth
  have h_depth_arr₂ : depth < (PathState.permute σ state₁).pathsOfLength.size := by
    rw [← h_map_eq]; exact h_depth_map
  have h_proj := h_get_at h_map_eq depth h_depth_map h_depth_arr₂
  -- Reduce `(state₁.pathsOfLength.map f₁)[depth] = f₁ (state₁.pathsOfLength[depth])`.
  rw [Array.getElem_map] at h_proj
  -- h_proj : f₁ (state₁.pathsOfLength[depth]) = (PathState.permute σ state₁).pathsOfLength[depth].
  -- Convert state₁.pathsOfLength[depth] to state₁.pathsOfLength.getD depth #[].
  have h_arr₁_get_elem : (state₁.pathsOfLength.getD depth #[])
                       = state₁.pathsOfLength[depth]'h_depth :=
    Array.getElem_eq_getD #[] |>.symm
  rw [← h_arr₁_get_elem] at h_proj
  -- Convert (PathState.permute σ state₁).pathsOfLength[depth] to ...getD depth #[].
  have h_arr₂_get_elem : ((PathState.permute σ state₁).pathsOfLength.getD depth #[])
                       = (PathState.permute σ state₁).pathsOfLength[depth]'h_depth_arr₂ :=
    Array.getElem_eq_getD #[] |>.symm
  rw [← h_arr₂_get_elem] at h_proj
  -- h_proj : f₁ (state₁.pathsOfLength.getD depth #[]) = (PathState.permute σ state₁).pathsOfLength.getD depth #[].
  set arr₁ := state₁.pathsOfLength.getD depth #[] with h_arr₁_def
  set arr₂ := (PathState.permute σ state₁).pathsOfLength.getD depth #[] with h_arr₂_def
  -- h_proj : f₁ arr₁ = arr₂.
  -- Goal: arr₂[(σ s).val] = PathsFrom.permute σ (arr₁[s.val]).
  -- Use h_proj to rewrite arr₂ ← f₁ arr₁ at the LHS.
  have h_σs_lt_kp1 : (σ s).val < k + 1 := (σ s).isLt
  have h_f₁_arr₁_size :
      ((Array.range (k + 1)).map (fun newStart =>
          PathsFrom.permute σ (arr₁.getD (permNat σ⁻¹ newStart)
            { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size = k + 1 := by
    simp [Array.size_map, Array.size_range]
  have h_σs_lt_f₁ : (σ s).val < ((Array.range (k + 1)).map (fun newStart =>
      PathsFrom.permute σ (arr₁.getD (permNat σ⁻¹ newStart)
        { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size := by
    rw [h_f₁_arr₁_size]; exact h_σs_lt_kp1
  have h_bridge : arr₂[(σ s).val]'h_σs_lt₂
      = ((Array.range (k + 1)).map (fun newStart =>
          PathsFrom.permute σ (arr₁.getD (permNat σ⁻¹ newStart)
            { depth := 0, startVertexIndex := 0, pathsToVertex := [] })))[(σ s).val]'h_σs_lt_f₁ :=
    h_get_at h_proj.symm (σ s).val h_σs_lt₂ h_σs_lt_f₁
  rw [h_bridge]
  rw [Array.getElem_map]
  simp only [Array.getElem_range]
  -- Goal: PathsFrom.permute σ (arr₁.getD (permNat σ⁻¹ (σ s).val) default)
  --     = PathsFrom.permute σ (arr₁[s.val]).
  congr 1
  -- arr₁.getD (permNat σ⁻¹ (σ s).val) default = arr₁[s.val].
  rw [show permNat σ⁻¹ (σ s).val = s.val from by
    rw [show (σ s).val = permNat σ s.val from (permNat_fin σ s).symm,
        permNat_inv_perm s.isLt]]
  exact (Array.getElem_eq_getD
    ({ depth := 0, startVertexIndex := 0, pathsToVertex := [] } : PathsFrom (k+1))).symm

/-! ## Foundational lemma 2 — pathsAtDepth Perm under two states

For `state₂ := PathState.permute σ state₁`, the depth-`depth` `pathsAtDepth` of
`state₂` is `Perm`-equivalent to `(pathsAtDepth state₁).map (PathsFrom.permute σ)`.

This is the two-state generalization of `pathsAtDepth_map_f_perm` (Aut version).
The proof uses `pathsOfLength_two_states_at_σ_slot` to identify slot `(σ⁻¹ i).val`
of arr₂ with `f(arr₁[i.val])`, then `map_reindex_perm` to rearrange. -/

private theorem pathsAtDepth_two_states_perm
    (σ : Equiv.Perm (Fin n)) (state₁ : PathState n)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state₁.pathsOfLength.getD depth #[]).toList.length = n) :
    let pathsAtDepth₁ := (state₁.pathsOfLength.getD depth #[]).toList
    let pathsAtDepth₂ :=
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList
    let f : PathsFrom n → PathsFrom n := PathsFrom.permute σ
    pathsAtDepth₂.Perm (pathsAtDepth₁.map f) := by
  -- Handle n = 0 vacuously.
  by_cases hn : n = 0
  · subst hn; exact absurd h_depth (Nat.not_lt_zero _)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro pathsAtDepth₁ pathsAtDepth₂ f
  -- arr₁ size = k+1.
  have h_inner₁_size : (state₁.pathsOfLength.getD depth #[]).size = k + 1 := by
    rw [← Array.length_toList]; exact h_outer_len
  -- depth < state₁.pathsOfLength.size.
  have h_depth₁_arr : depth < state₁.pathsOfLength.size := by
    by_contra h_not
    push_neg at h_not
    have h_arr_empty : state₁.pathsOfLength.getD depth #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_not, Option.getD_none]
    rw [h_arr_empty] at h_outer_len
    simp at h_outer_len
  -- arr₂ size = k+1 (via PathState.permute → Array.range).
  have h_inner₂_size :
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).size = k + 1 := by
    have h_depth₂_arr : depth < (PathState.permute σ state₁).pathsOfLength.size := by
      rw [PathState_permute_pathsOfLength_size]; exact h_depth₁_arr
    rw [show (PathState.permute σ state₁).pathsOfLength.getD depth #[]
          = (PathState.permute σ state₁).pathsOfLength[depth]'h_depth₂_arr
        from (Array.getElem_eq_getD #[]).symm]
    -- Unfold PathState.permute on the indexed slice.
    show ((state₁.pathsOfLength.map (fun pathsByStart =>
              (Array.range (k + 1)).map fun newStart =>
                PathsFrom.permute σ (pathsByStart.getD (permNat σ⁻¹ newStart)
                  { depth := 0, startVertexIndex := 0, pathsToVertex := [] })))[depth]'_).size
            = k + 1
    rw [Array.getElem_map]
    simp [Array.size_map, Array.size_range]
  have h_pathsAtDepth₁_len : pathsAtDepth₁.length = k + 1 := h_outer_len
  have h_pathsAtDepth₂_len : pathsAtDepth₂.length = k + 1 := by
    show ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList.length = k + 1
    rw [Array.length_toList]; exact h_inner₂_size
  let default_pf : PathsFrom (k + 1) :=
    { depth := 0, startVertexIndex := 0, pathsToVertex := [] }
  -- The σ-reindexing-after-f-mapping list of pathsAtDepth₁ equals pathsAtDepth₂.
  have h_reindex_eq :
      (List.finRange (k + 1)).map (fun i : Fin (k + 1) =>
        f (pathsAtDepth₁.getD (σ⁻¹ i).val default_pf))
      = pathsAtDepth₂ := by
    apply List.ext_getElem
    · simp [h_pathsAtDepth₂_len]
    intros j h₁ h₂
    have h_j_lt_kp1 : j < k + 1 := by
      simp only [List.length_map, List.length_finRange] at h₁; exact h₁
    rw [List.getElem_map, List.getElem_finRange]
    simp only [Fin.cast_mk]
    -- LHS: f (pathsAtDepth₁.getD (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val default_pf)
    have h_σ_inv_j_lt : (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val < pathsAtDepth₁.length := by
      rw [h_pathsAtDepth₁_len]; exact (σ⁻¹ ⟨j, h_j_lt_kp1⟩).isLt
    have h_getD₁_eq : pathsAtDepth₁.getD (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val default_pf
                   = pathsAtDepth₁[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_σ_inv_j_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_σ_inv_j_lt, Option.getD_some]
    rw [h_getD₁_eq]
    -- Convert pathsAtDepth₁[i] → arr₁[i] via getElem_toList.
    have h_arr₁_σ_inv_lt :
        (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val < (state₁.pathsOfLength.getD depth #[]).size := by
      rw [h_inner₁_size]; exact (σ⁻¹ ⟨j, h_j_lt_kp1⟩).isLt
    have h_arr₁_at_σ_inv :
        (state₁.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr₁_σ_inv_lt
        = pathsAtDepth₁[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_σ_inv_j_lt := by
      show (state₁.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr₁_σ_inv_lt
         = (state₁.pathsOfLength.getD depth #[]).toList[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'
              (by rw [Array.length_toList]; exact h_arr₁_σ_inv_lt)
      exact Array.getElem_toList (h := h_arr₁_σ_inv_lt)
    rw [← h_arr₁_at_σ_inv]
    -- Apply pathsOfLength_two_states_at_σ_slot at s := σ⁻¹ ⟨j, h_j_lt_kp1⟩.
    have h_arr₂_j_lt :
        j < ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).size := by
      rw [h_inner₂_size]; exact h_j_lt_kp1
    have h_σσ : σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩) = ⟨j, h_j_lt_kp1⟩ := by simp
    have h_arr₂_at_σσ :
        ((PathState.permute σ state₁).pathsOfLength.getD depth #[])[(σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩)).val]'
            (by rw [h_σσ]; exact h_arr₂_j_lt)
        = PathsFrom.permute σ
            ((state₁.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr₁_σ_inv_lt) :=
      pathsOfLength_two_states_at_σ_slot σ state₁ depth h_depth₁_arr h_inner₁_size
        (σ⁻¹ ⟨j, h_j_lt_kp1⟩) (by rw [h_σσ]; exact h_arr₂_j_lt) h_arr₁_σ_inv_lt
    -- Goal LHS form: PathsFrom.permute σ (arr₁[(σ⁻¹ ...).val]) — match h_arr₂_at_σσ.
    -- Unfold the let-bound `f` to make the rewrite fire.
    change PathsFrom.permute σ
            ((state₁.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr₁_σ_inv_lt)
       = pathsAtDepth₂[j]'h₂
    rw [← h_arr₂_at_σσ]
    -- Final: arr₂[(σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩)).val] = pathsAtDepth₂[j].
    -- Both equal `arr₂[j]` via `σ (σ⁻¹ x) = x` and `Array.getElem_toList`.
    set arr₂ := (PathState.permute σ state₁).pathsOfLength.getD depth #[] with h_arr₂_def
    have h_arr₂_index_eq :
        arr₂[(σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩)).val]'(by rw [h_σσ]; exact h_arr₂_j_lt)
          = arr₂[j]'h_arr₂_j_lt := by
      congr 1; rw [h_σσ]
    rw [h_arr₂_index_eq]
    -- arr₂[j] = arr₂.toList[j] = pathsAtDepth₂[j].
    show arr₂[j]'h_arr₂_j_lt = pathsAtDepth₂[j]'h₂
    exact Array.getElem_toList (h := h_arr₂_j_lt)
  -- Apply map_reindex_perm with σ := σ⁻¹.
  have h_perm := map_reindex_perm σ⁻¹ pathsAtDepth₁ h_pathsAtDepth₁_len f default_pf
  -- h_perm : ((List.finRange (k+1)).map (fun i => f (pathsAtDepth₁.getD (σ⁻¹ i).val default_pf))).Perm
  --          (pathsAtDepth₁.map f)
  rw [h_reindex_eq] at h_perm
  exact h_perm

/-! ## Foundational lemma 3 — membership corollary

Direct corollary of `pathsAtDepth_two_states_perm`: for `p ∈ pathsAtDepth state₁`,
`PathsFrom.permute σ p ∈ pathsAtDepth state₂` where `state₂ = PathState.permute σ state₁`. -/

private theorem mem_pathsAtDepth_two_states_under_f
    (σ : Equiv.Perm (Fin n)) (state₁ : PathState n)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state₁.pathsOfLength.getD depth #[]).toList.length = n)
    (p : PathsFrom n) (h_p_in : p ∈ (state₁.pathsOfLength.getD depth #[]).toList) :
    PathsFrom.permute σ p ∈
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList := by
  have h_perm := pathsAtDepth_two_states_perm σ state₁ depth h_depth h_outer_len
  have h_fp_in_map :
      PathsFrom.permute σ p ∈
        (state₁.pathsOfLength.getD depth #[]).toList.map (PathsFrom.permute σ) :=
    List.mem_map.mpr ⟨p, h_p_in, rfl⟩
  exact h_perm.symm.mem_iff.mp h_fp_in_map

/-! ## Foundational lemma 4 — allBetween Perm under two states

Generalization of `allBetween_map_f_perm`: when `state₂ = PathState.permute σ state₁`,
`allBetween state₂ ~Perm (allBetween state₁).map (PathsBetween.permute σ)`.

The proof mirrors `allBetween_map_f_perm`'s structure (reduce `allBetween` to
`flatMap (·.pathsToVertex)`, use `Perm.flatMap_left` + `Perm.flatMap_right` +
`PathsFrom_permute_pathsToVertex_perm`), with `pathsAtDepth_map_f_perm` replaced by
`pathsAtDepth_two_states_perm`. -/

private theorem allBetween_two_states_perm
    (σ : Equiv.Perm (Fin n)) (state₁ : PathState n)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state₁.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n) :
    let pathsAtDepth₁ := (state₁.pathsOfLength.getD depth #[]).toList
    let pathsAtDepth₂ :=
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList
    let allBetween₁ := pathsAtDepth₁.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let allBetween₂ := pathsAtDepth₂.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let f : PathsBetween n → PathsBetween n := PathsBetween.permute σ
    allBetween₂.Perm (allBetween₁.map f) := by
  intro pathsAtDepth₁ pathsAtDepth₂ allBetween₁ allBetween₂ f
  set g : PathsFrom n → PathsFrom n := PathsFrom.permute σ with hg_def
  -- Step 1: allBetween_i = pathsAtDepth_i.flatMap (·.pathsToVertex).
  have h_allBetween₁_eq : allBetween₁ = pathsAtDepth₁.flatMap (·.pathsToVertex) := by
    show pathsAtDepth₁.foldl (fun acc pf => acc ++ pf.pathsToVertex) [] = _
    rw [List.flatMap_eq_foldl]
  have h_allBetween₂_eq : allBetween₂ = pathsAtDepth₂.flatMap (·.pathsToVertex) := by
    show pathsAtDepth₂.foldl (fun acc pf => acc ++ pf.pathsToVertex) [] = _
    rw [List.flatMap_eq_foldl]
  -- Step 2: allBetween₁.map f = pathsAtDepth₁.flatMap (·.pathsToVertex.map f).
  have h_allBetween₁_map_eq :
      allBetween₁.map f = pathsAtDepth₁.flatMap (·.pathsToVertex.map f) := by
    rw [h_allBetween₁_eq, List.map_flatMap]
  -- Step 3: pathsAtDepth₁.flatMap (·.pathsToVertex.map f)
  --       ~Perm pathsAtDepth₁.flatMap (fun pf => (g pf).pathsToVertex).
  have h_step₁ :
      (pathsAtDepth₁.flatMap (·.pathsToVertex.map f)).Perm
        (pathsAtDepth₁.flatMap (fun pf => (g pf).pathsToVertex)) := by
    apply List.Perm.flatMap_left
    intro pf h_pf_in
    have h_pf_pTV_len : pf.pathsToVertex.length = n := h_pathsToVertex_len pf h_pf_in
    exact (PathsFrom_permute_pathsToVertex_perm σ pf h_pf_pTV_len).symm
  -- Step 4: pathsAtDepth₁.flatMap (g · .pathsToVertex)
  --       = (pathsAtDepth₁.map g).flatMap (·.pathsToVertex).
  have h_step₂ : pathsAtDepth₁.flatMap (fun pf => (g pf).pathsToVertex)
              = (pathsAtDepth₁.map g).flatMap (·.pathsToVertex) := by
    rw [List.flatMap_map]
  -- Step 5: pathsAtDepth₂ ~Perm pathsAtDepth₁.map g (by pathsAtDepth_two_states_perm).
  have h_pathsAtDepth_perm : pathsAtDepth₂.Perm (pathsAtDepth₁.map g) :=
    pathsAtDepth_two_states_perm σ state₁ depth h_depth h_outer_len
  -- Step 6: (pathsAtDepth₁.map g).flatMap (·.pathsToVertex)
  --       ~Perm pathsAtDepth₂.flatMap (·.pathsToVertex).
  have h_step₃ : ((pathsAtDepth₁.map g).flatMap (·.pathsToVertex)).Perm
                  (pathsAtDepth₂.flatMap (·.pathsToVertex)) :=
    (h_pathsAtDepth_perm.flatMap_right (·.pathsToVertex)).symm
  -- Combine: allBetween₁.map f ~Perm allBetween₂.
  have h_chain : (allBetween₁.map f).Perm allBetween₂ := by
    rw [h_allBetween₁_map_eq]
    refine h_step₁.trans (?_)
    rw [h_step₂]
    refine h_step₃.trans (?_)
    rw [← h_allBetween₂_eq]
  exact h_chain.symm

/-! ## Foundational lemma 5 — allBetween membership corollary

Direct corollary of `allBetween_two_states_perm`: for `q ∈ allBetween state₁`,
`PathsBetween.permute σ q ∈ allBetween state₂`. -/

private theorem mem_allBetween_two_states_under_f
    (σ : Equiv.Perm (Fin n)) (state₁ : PathState n)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state₁.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (q : PathsBetween n)
    (h_q_in : q ∈ ((state₁.pathsOfLength.getD depth #[]).toList.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [])) :
    PathsBetween.permute σ q ∈ (((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []) := by
  have h_perm := allBetween_two_states_perm σ state₁ depth h_depth h_outer_len
    h_pathsToVertex_len
  -- h_perm : allBetween₂.Perm (allBetween₁.map (PathsBetween.permute σ))
  have h_fq_in_map :
      PathsBetween.permute σ q ∈
        ((state₁.pathsOfLength.getD depth #[]).toList.foldl
          (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []).map
          (PathsBetween.permute σ) :=
    List.mem_map.mpr ⟨q, h_q_in, rfl⟩
  exact h_perm.symm.mem_iff.mp h_fq_in_map

/-! ## P6.A target — Stage B-rel general σ

`calculatePathRankings_σ_equivariant_general` — relational σ-equivariance of
`calculatePathRankings` for an *arbitrary* `σ : Equiv.Perm (Fin n)`. Pending the
build-up of the relational σ-rank-closure lemmas + body step + foldl induction. -/

theorem calculatePathRankings_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (_hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    let rs₁ := calculatePathRankings (initializePaths G) vts₁
    let rs₂ := calculatePathRankings (initializePaths (G.permute σ)) vts₂
    (∀ d : Nat, d < n → ∀ s : Fin n,
        (rs₂.fromRanks.getD d #[]).getD s.val 0
        = (rs₁.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
        ((rs₂.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
        = ((rs₁.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  sorry

end Graph
