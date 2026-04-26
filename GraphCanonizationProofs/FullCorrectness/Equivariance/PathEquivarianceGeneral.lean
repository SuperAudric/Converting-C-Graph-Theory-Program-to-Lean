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

/-! ## P6.A relational σ-rank-closure — `from_assignList_σ_rank_general`

Generalization of `from_assignList_σ_rank_rel` to drop `PathState.permute σ state = state`.
Compares `assignList₁` (sorted on `pathsAtDepth state₁`) with `assignList₂` (sorted on
`pathsAtDepth state₂` where `state₂ := PathState.permute σ state₁`).

The proof structure mirrors `from_assignList_σ_rank_rel` exactly, with the foundational
helpers `mem_pathsAtDepth_two_states_under_f` and `pathsAtDepth_two_states_perm` in
place of their σ-INV state counterparts. -/

theorem from_assignList_σ_rank_general
    (σ : Equiv.Perm (Fin n))
    (state₁ : PathState n)
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin n,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len₁ : (state₁.pathsOfLength.getD depth #[]).toList.length = n)
    (h_outer_len₂ :
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len₁ : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_pathsToVertex_len₂ :
      ∀ p ∈ ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len₁ : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n)
    (h_inner_len₂ :
      ∀ p ∈ ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth₁ := (state₁.pathsOfLength.getD depth #[]).toList
    let pathsAtDepth₂ :=
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList
    let cmp₁ := comparePathsFrom vts₁ br₁
    let cmp₂ := comparePathsFrom vts₂ br₂
    let assignList₁ := assignRanks cmp₁ (sortBy cmp₁ pathsAtDepth₁)
    let assignList₂ := assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth₂)
    ∀ item₁ ∈ assignList₁,
      ∃ item₂ ∈ assignList₂,
        item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
        ∧ item₂.2 = item₁.2 := by
  intro pathsAtDepth₁ pathsAtDepth₂ cmp₁ cmp₂ assignList₁ assignList₂ item₁ h_item₁_mem
  set f : PathsFrom n → PathsFrom n := PathsFrom.permute σ with hf_def
  -- Locate item₁ in assignList₁ at position k₁.
  obtain ⟨k₁, h_k₁_lt, h_assign_k₁⟩ := List.mem_iff_getElem.mp h_item₁_mem
  -- Length facts.
  have h_assign₁_len : assignList₁.length = pathsAtDepth₁.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₁ pathsAtDepth₁).length_eq
  have h_assign₂_len : assignList₂.length = pathsAtDepth₂.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₂ pathsAtDepth₂).length_eq
  have h_pathsAtDepth_len_eq : pathsAtDepth₁.length = pathsAtDepth₂.length := by
    rw [h_outer_len₁, h_outer_len₂]
  have h_k₁_lt_n₁ : k₁ < pathsAtDepth₁.length := h_assign₁_len ▸ h_k₁_lt
  have h_k₁_lt_n₂ : k₁ < pathsAtDepth₂.length := h_pathsAtDepth_len_eq ▸ h_k₁_lt_n₁
  have h_k₁_lt_sort₁ : k₁ < (sortBy cmp₁ pathsAtDepth₁).length := by
    rw [(sortBy_perm cmp₁ pathsAtDepth₁).length_eq]; exact h_k₁_lt_n₁
  have h_k₁_lt_sort₂ : k₁ < (sortBy cmp₂ pathsAtDepth₂).length := by
    rw [(sortBy_perm cmp₂ pathsAtDepth₂).length_eq]; exact h_k₁_lt_n₂
  -- p := item₁.1.
  set p := item₁.1 with hp_def
  have h_item₁_1_eq : p = (sortBy cmp₁ pathsAtDepth₁)[k₁]'h_k₁_lt_sort₁ := by
    rw [hp_def, ← h_assign_k₁]
    exact assignRanks_getElem_fst cmp₁ (sortBy cmp₁ pathsAtDepth₁) k₁ h_k₁_lt_sort₁
  -- p ∈ pathsAtDepth₁.
  have h_p_in_sort₁ : p ∈ sortBy cmp₁ pathsAtDepth₁ := by
    rw [h_item₁_1_eq]; exact List.getElem_mem _
  have h_p_in₁ : p ∈ pathsAtDepth₁ :=
    (sortBy_perm cmp₁ pathsAtDepth₁).mem_iff.mp h_p_in_sort₁
  -- q := f p ∈ pathsAtDepth₂ (via mem_pathsAtDepth_two_states_under_f).
  set q := f p with hq_def
  have h_q_in₂ : q ∈ pathsAtDepth₂ := by
    rw [hq_def, hf_def]
    exact mem_pathsAtDepth_two_states_under_f σ state₁ depth h_depth h_outer_len₁ p h_p_in₁
  -- q is in sortBy cmp₂ pathsAtDepth₂ at some position k₂.
  have h_q_in_sort₂ : q ∈ sortBy cmp₂ pathsAtDepth₂ :=
    (sortBy_perm cmp₂ pathsAtDepth₂).mem_iff.mpr h_q_in₂
  obtain ⟨k₂, h_k₂_lt_sort₂, h_q_at_k₂⟩ := List.mem_iff_getElem.mp h_q_in_sort₂
  have h_k₂_lt : k₂ < assignList₂.length := by
    rw [h_assign₂_len]
    exact (sortBy_perm cmp₂ pathsAtDepth₂).length_eq ▸ h_k₂_lt_sort₂
  -- item₂ := assignList₂[k₂].
  set item₂ := assignList₂[k₂]'h_k₂_lt with hitem₂_def
  -- item₂.1 = q.
  have h_item₂_1_eq : item₂.1 = q := by
    rw [hitem₂_def, assignRanks_getElem_fst cmp₂ (sortBy cmp₂ pathsAtDepth₂) k₂ h_k₂_lt_sort₂]
    exact h_q_at_k₂
  -- Total preorder + equivCompat for cmp₁ and cmp₂.
  obtain ⟨h_refl₁, h_antisym₁₁, h_antisym₂₁, h_trans₁⟩ :=
    comparePathsFrom_total_preorder (vc := n) vts₁ br₁
  obtain ⟨h_refl₂, h_antisym₁₂, h_antisym₂₂, h_trans₂⟩ :=
    comparePathsFrom_total_preorder (vc := n) vts₂ br₂
  -- Sortedness of sortBy outputs.
  have h_sort₁ := sortBy_pairwise cmp₁ h_antisym₂₁ h_trans₁ pathsAtDepth₁
  have h_sort₂ := sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ pathsAtDepth₂
  -- Relational compare hypothesis: ∀ a b ∈ pathsAtDepth₁, cmp₂ (f a) (f b) = cmp₁ a b.
  have h_resp : ∀ a ∈ pathsAtDepth₁, ∀ b ∈ pathsAtDepth₁, cmp₂ (f a) (f b) = cmp₁ a b := by
    intros a h_a b h_b
    rw [hf_def]
    have h_a_pTV_len : a.pathsToVertex.length = n := h_pathsToVertex_len₁ a h_a
    have h_b_pTV_len : b.pathsToVertex.length = n := h_pathsToVertex_len₁ b h_b
    have h_a_inner : ∀ q ∈ a.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n :=
      h_inner_len₁ a h_a
    have h_b_inner : ∀ q ∈ b.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n :=
      h_inner_len₁ b h_b
    exact comparePathsFrom_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel a b
      h_a_pTV_len h_b_pTV_len h_a_inner h_b_inner
  -- L_f := sortBy cmp₂ (pathsAtDepth₁.map f) = (sortBy cmp₁ pathsAtDepth₁).map f.
  have h_Lf_eq : sortBy cmp₂ (pathsAtDepth₁.map f)
               = (sortBy cmp₁ pathsAtDepth₁).map f := by
    apply sortBy_map_pointwise_relational f cmp₁ cmp₂ pathsAtDepth₁
    intros a h_a b h_b
    exact h_resp a h_a b h_b
  -- assignRanks cmp₂ (L₁.map f) = assignList₁.map (lift f).
  have h_assign_Lf_eq :
      assignRanks cmp₂ ((sortBy cmp₁ pathsAtDepth₁).map f)
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    apply assignRanks_map_relational cmp₁ cmp₂ f (sortBy cmp₁ pathsAtDepth₁)
    intros a h_a b h_b
    have h_a_in : a ∈ pathsAtDepth₁ := (sortBy_perm cmp₁ pathsAtDepth₁).mem_iff.mp h_a
    have h_b_in : b ∈ pathsAtDepth₁ := (sortBy_perm cmp₁ pathsAtDepth₁).mem_iff.mp h_b
    exact h_resp a h_a_in b h_b_in
  have h_assign_pathMapF_eq :
      assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth₁.map f))
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    rw [h_Lf_eq]; exact h_assign_Lf_eq
  -- pathsAtDepth₂.Perm (pathsAtDepth₁.map f) (via pathsAtDepth_two_states_perm).
  have h_perm_paths : pathsAtDepth₂.Perm (pathsAtDepth₁.map f) :=
    pathsAtDepth_two_states_perm σ state₁ depth h_depth h_outer_len₁
  -- sortBy outputs Perm-equivalent.
  have h_sort_perm : (sortBy cmp₂ pathsAtDepth₂).Perm (sortBy cmp₂ (pathsAtDepth₁.map f)) := by
    have h_p1 := sortBy_perm cmp₂ pathsAtDepth₂
    have h_p2 := sortBy_perm cmp₂ (pathsAtDepth₁.map f)
    exact h_p1.trans (h_perm_paths.trans h_p2.symm)
  have h_sort_Lf : (sortBy cmp₂ (pathsAtDepth₁.map f)).Pairwise (fun a b => cmp₂ a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ (pathsAtDepth₁.map f)
  have h_k₁_lt_Lf : k₁ < (sortBy cmp₂ (pathsAtDepth₁.map f)).length := by
    rw [(sortBy_perm cmp₂ (pathsAtDepth₁.map f)).length_eq, List.length_map]; exact h_k₁_lt_n₁
  have h_k₁_lt_assign₂ : k₁ < assignList₂.length := h_assign₂_len ▸ h_k₁_lt_n₂
  have h_k₁_lt_assignLf :
      k₁ < (assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth₁.map f))).length := by
    rw [assignRanks_length]; exact h_k₁_lt_Lf
  have h_rank_eq_at_k₁ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = ((assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth₁.map f)))[k₁]'h_k₁_lt_assignLf).2 :=
    assignRanks_rank_eq_of_sorted_perm cmp₂
      h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂ h_sort_perm h_sort₂ h_sort_Lf k₁
      h_k₁_lt_sort₂ h_k₁_lt_Lf
  -- Helper: lists equal at the same index give equal getElem (PathsFrom n × Nat version).
  have h_get_of_list_eq_pair : ∀ {L₁ L₂ : List (PathsFrom n × Nat)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_rank_at_k₁_via_map :
      ((assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth₁.map f)))[k₁]'h_k₁_lt_assignLf).2
        = item₁.2 := by
    have h_k₁_lt_assignList₁_map : k₁ < (assignList₁.map (fun e => (f e.1, e.2))).length := by
      rw [List.length_map, h_assign₁_len]; exact h_k₁_lt_n₁
    rw [h_get_of_list_eq_pair h_assign_pathMapF_eq k₁ h_k₁_lt_assignLf h_k₁_lt_assignList₁_map,
        List.getElem_map]
    show ((assignList₁[k₁]'(h_assign₁_len ▸ h_k₁_lt_n₁)).2 : Nat) = item₁.2
    rw [h_assign_k₁]
  have h_rank_at_k₁_eq : (assignList₂[k₁]'h_k₁_lt_assign₂).2 = item₁.2 := by
    rw [h_rank_eq_at_k₁]; exact h_rank_at_k₁_via_map
  -- Helper: lists equal at the same index give equal getElem (PathsFrom n version).
  have h_get_of_list_eq : ∀ {L₁ L₂ : List (PathsFrom n)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_Lf_k₁ : (sortBy cmp₂ (pathsAtDepth₁.map f))[k₁]'h_k₁_lt_Lf = q := by
    have h_k₁_lt_map : k₁ < ((sortBy cmp₁ pathsAtDepth₁).map f).length := by
      rw [List.length_map]; exact h_k₁_lt_sort₁
    rw [h_get_of_list_eq h_Lf_eq k₁ h_k₁_lt_Lf h_k₁_lt_map, List.getElem_map,
        ← h_item₁_1_eq, ← hq_def]
  have h_class_eq : cmp₂ ((sortBy cmp₂ (pathsAtDepth₁.map f))[k₁]'h_k₁_lt_Lf)
                       ((sortBy cmp₂ pathsAtDepth₂)[k₁]'h_k₁_lt_sort₂) = Ordering.eq :=
    sortedPerm_class_eq cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
      _ _ h_sort_perm.symm h_sort_Lf h_sort₂ k₁ h_k₁_lt_Lf h_k₁_lt_sort₂
  rw [h_Lf_k₁] at h_class_eq
  -- Use h_class_eq to show the rank at k₂ matches the rank at k₁ in assignList₂.
  have h_eq_symm : ∀ a b : PathsFrom n,
      comparePathsFrom vts₂ br₂ a b = Ordering.eq →
      comparePathsFrom vts₂ br₂ b a = Ordering.eq := by
    intros a b hab
    match h_ba : comparePathsFrom vts₂ br₂ b a with
    | .eq => rfl
    | .lt =>
      exfalso
      have h_gt : comparePathsFrom vts₂ br₂ a b = Ordering.gt := h_antisym₁₂ b a h_ba
      rw [h_gt] at hab; cases hab
    | .gt =>
      exfalso
      have h_lt : comparePathsFrom vts₂ br₂ a b = Ordering.lt := h_antisym₂₂ b a h_ba
      rw [h_lt] at hab; cases hab
  have h_rank_eq_k₁_k₂ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = (assignList₂[k₂]'h_k₂_lt).2 := by
    rcases Nat.lt_or_ge k₂ k₁ with h_lt | h_ge
    · -- k₂ < k₁.
      have h_le : k₂ ≤ k₁ := h_lt.le
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ pathsAtDepth₂)[k₂]'h_k₂_lt_sort₂)
                ((sortBy cmp₂ pathsAtDepth₂)[k₁]'h_k₁_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth₂))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth₂))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact (assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ pathsAtDepth₂) h_sort₂ k₂ k₁ h_le h_k₁_lt_sort₂ h_class_eq_low).symm
    · -- k₁ ≤ k₂.
      have h_le : k₁ ≤ k₂ := h_ge
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ pathsAtDepth₂)[k₁]'h_k₁_lt_sort₂)
                ((sortBy cmp₂ pathsAtDepth₂)[k₂]'h_k₂_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_eq_symm _ _ h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth₂))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth₂))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ pathsAtDepth₂) h_sort₂ k₁ k₂ h_le h_k₂_lt_sort₂ h_class_eq_low
  -- Now: (assignList₂[k₂]).2 = item₁.2.
  have h_item₂_2_eq : item₂.2 = item₁.2 := by
    rw [hitem₂_def, ← h_rank_eq_k₁_k₂]; exact h_rank_at_k₁_eq
  -- Construct the witness.
  refine ⟨item₂, ?_, ?_, h_item₂_2_eq⟩
  · -- item₂ ∈ assignList₂.
    rw [hitem₂_def]; exact List.getElem_mem _
  · -- item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val.
    rw [h_item₂_1_eq, hq_def, hf_def]
    by_cases hn : n = 0
    · subst hn; exact p.startVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.startVertexIndex).val = (σ item₁.1.startVertexIndex).val
      rw [hp_def]

/-! ## P6.A relational σ-rank-closure — `between_assignList_σ_rank_general`

Generalization of `between_assignList_σ_rank_rel` for the between-side. Mirrors
`from_assignList_σ_rank_general`'s adaptation (replacing single `pathsAtDepth`
with per-side `pathsAtDepth_i` and `allBetween_i`, and using the two-state
foundational helpers). -/

theorem between_assignList_σ_rank_general
    (σ : Equiv.Perm (Fin n))
    (state₁ : PathState n)
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin n,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len₁ : (state₁.pathsOfLength.getD depth #[]).toList.length = n)
    (h_outer_len₂ :
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len₁ : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_pathsToVertex_len₂ :
      ∀ p ∈ ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len₁ : ∀ p ∈ (state₁.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n)
    (h_inner_len₂ :
      ∀ p ∈ ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth₁ := (state₁.pathsOfLength.getD depth #[]).toList
    let pathsAtDepth₂ :=
      ((PathState.permute σ state₁).pathsOfLength.getD depth #[]).toList
    let allBetween₁ := pathsAtDepth₁.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let allBetween₂ := pathsAtDepth₂.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let cmp₁ := comparePathsBetween vts₁ br₁
    let cmp₂ := comparePathsBetween vts₂ br₂
    let assignList₁ := assignRanks cmp₁ (sortBy cmp₁ allBetween₁)
    let assignList₂ := assignRanks cmp₂ (sortBy cmp₂ allBetween₂)
    ∀ item₁ ∈ assignList₁,
      ∃ item₂ ∈ assignList₂,
        item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
        ∧ item₂.1.endVertexIndex.val = (σ item₁.1.endVertexIndex).val
        ∧ item₂.2 = item₁.2 := by
  intro pathsAtDepth₁ pathsAtDepth₂ allBetween₁ allBetween₂ cmp₁ cmp₂ assignList₁ assignList₂
        item₁ h_item₁_mem
  set f : PathsBetween n → PathsBetween n := PathsBetween.permute σ with hf_def
  obtain ⟨k₁, h_k₁_lt, h_assign_k₁⟩ := List.mem_iff_getElem.mp h_item₁_mem
  -- Length facts.
  have h_assign₁_len : assignList₁.length = allBetween₁.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₁ allBetween₁).length_eq
  have h_assign₂_len : assignList₂.length = allBetween₂.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₂ allBetween₂).length_eq
  have h_k₁_lt_n₁ : k₁ < allBetween₁.length := h_assign₁_len ▸ h_k₁_lt
  have h_k₁_lt_sort₁ : k₁ < (sortBy cmp₁ allBetween₁).length := by
    rw [(sortBy_perm cmp₁ allBetween₁).length_eq]; exact h_k₁_lt_n₁
  -- p := item₁.1.
  set p := item₁.1 with hp_def
  have h_item₁_1_eq : p = (sortBy cmp₁ allBetween₁)[k₁]'h_k₁_lt_sort₁ := by
    rw [hp_def, ← h_assign_k₁]
    exact assignRanks_getElem_fst cmp₁ (sortBy cmp₁ allBetween₁) k₁ h_k₁_lt_sort₁
  have h_p_in_sort₁ : p ∈ sortBy cmp₁ allBetween₁ := by
    rw [h_item₁_1_eq]; exact List.getElem_mem _
  have h_p_in₁ : p ∈ allBetween₁ :=
    (sortBy_perm cmp₁ allBetween₁).mem_iff.mp h_p_in_sort₁
  -- q := f p ∈ allBetween₂ (via mem_allBetween_two_states_under_f).
  set q := f p with hq_def
  have h_q_in₂ : q ∈ allBetween₂ := by
    rw [hq_def, hf_def]
    exact mem_allBetween_two_states_under_f σ state₁ depth h_depth h_outer_len₁
      h_pathsToVertex_len₁ p h_p_in₁
  -- q is in sortBy cmp₂ allBetween₂ at some position k₂.
  have h_q_in_sort₂ : q ∈ sortBy cmp₂ allBetween₂ :=
    (sortBy_perm cmp₂ allBetween₂).mem_iff.mpr h_q_in₂
  obtain ⟨k₂, h_k₂_lt_sort₂, h_q_at_k₂⟩ := List.mem_iff_getElem.mp h_q_in_sort₂
  have h_k₂_lt : k₂ < assignList₂.length := by
    rw [h_assign₂_len]
    exact (sortBy_perm cmp₂ allBetween₂).length_eq ▸ h_k₂_lt_sort₂
  set item₂ := assignList₂[k₂]'h_k₂_lt with hitem₂_def
  have h_item₂_1_eq : item₂.1 = q := by
    rw [hitem₂_def, assignRanks_getElem_fst cmp₂ (sortBy cmp₂ allBetween₂) k₂ h_k₂_lt_sort₂]
    exact h_q_at_k₂
  -- Total preorder + sortedness.
  obtain ⟨h_refl₁, h_antisym₁₁, h_antisym₂₁, h_trans₁⟩ :=
    comparePathsBetween_total_preorder (vc := n) vts₁ br₁
  obtain ⟨h_refl₂, h_antisym₁₂, h_antisym₂₂, h_trans₂⟩ :=
    comparePathsBetween_total_preorder (vc := n) vts₂ br₂
  have h_sort₁ := sortBy_pairwise cmp₁ h_antisym₂₁ h_trans₁ allBetween₁
  have h_sort₂ := sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ allBetween₂
  -- Inner-length conditions for elements of allBetween₁.
  have h_inner_q_in_allBetween₁ : ∀ q ∈ allBetween₁, q.depth > 0 → q.connectedSubPaths.length = n := by
    intros q h_q_in h_q_d
    obtain ⟨pf, h_pf_in, h_q_in_pf⟩ := (mem_allBetween_iff q pathsAtDepth₁).mp h_q_in
    exact h_inner_len₁ pf h_pf_in q h_q_in_pf h_q_d
  -- Relational compare: ∀ a b ∈ allBetween₁, cmp₂ (f a) (f b) = cmp₁ a b.
  have h_resp : ∀ a ∈ allBetween₁, ∀ b ∈ allBetween₁, cmp₂ (f a) (f b) = cmp₁ a b := by
    intros a h_a b h_b
    rw [hf_def]
    have h_a_inner : a.depth > 0 → a.connectedSubPaths.length = n := h_inner_q_in_allBetween₁ a h_a
    have h_b_inner : b.depth > 0 → b.connectedSubPaths.length = n := h_inner_q_in_allBetween₁ b h_b
    exact comparePathsBetween_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel a b
      h_a_inner h_b_inner
  -- L_f := sortBy cmp₂ (allBetween₁.map f) = (sortBy cmp₁ allBetween₁).map f.
  have h_Lf_eq : sortBy cmp₂ (allBetween₁.map f) = (sortBy cmp₁ allBetween₁).map f := by
    apply sortBy_map_pointwise_relational f cmp₁ cmp₂ allBetween₁
    intros a h_a b h_b
    exact h_resp a h_a b h_b
  -- assignRanks cmp₂ (L₁.map f) = assignList₁.map (lift f).
  have h_assign_Lf_eq :
      assignRanks cmp₂ ((sortBy cmp₁ allBetween₁).map f)
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    apply assignRanks_map_relational cmp₁ cmp₂ f (sortBy cmp₁ allBetween₁)
    intros a h_a b h_b
    have h_a_in : a ∈ allBetween₁ := (sortBy_perm cmp₁ allBetween₁).mem_iff.mp h_a
    have h_b_in : b ∈ allBetween₁ := (sortBy_perm cmp₁ allBetween₁).mem_iff.mp h_b
    exact h_resp a h_a_in b h_b_in
  have h_assign_pathMapF_eq :
      assignRanks cmp₂ (sortBy cmp₂ (allBetween₁.map f))
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    rw [h_Lf_eq]; exact h_assign_Lf_eq
  -- allBetween₂.Perm (allBetween₁.map f) (via allBetween_two_states_perm).
  have h_perm_allBetween : allBetween₂.Perm (allBetween₁.map f) :=
    allBetween_two_states_perm σ state₁ depth h_depth h_outer_len₁ h_pathsToVertex_len₁
  -- sortBy outputs Perm-equivalent.
  have h_sort_perm : (sortBy cmp₂ allBetween₂).Perm (sortBy cmp₂ (allBetween₁.map f)) := by
    have h_p1 := sortBy_perm cmp₂ allBetween₂
    have h_p2 := sortBy_perm cmp₂ (allBetween₁.map f)
    exact h_p1.trans (h_perm_allBetween.trans h_p2.symm)
  have h_sort_Lf : (sortBy cmp₂ (allBetween₁.map f)).Pairwise (fun a b => cmp₂ a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ (allBetween₁.map f)
  have h_k₁_lt_Lf : k₁ < (sortBy cmp₂ (allBetween₁.map f)).length := by
    rw [(sortBy_perm cmp₂ (allBetween₁.map f)).length_eq, List.length_map]; exact h_k₁_lt_n₁
  -- Length match: allBetween₂.length = allBetween₁.length via the Perm.
  have h_allBetween_len_eq : allBetween₂.length = allBetween₁.length := by
    rw [h_perm_allBetween.length_eq, List.length_map]
  have h_k₁_lt_n₂ : k₁ < allBetween₂.length := h_allBetween_len_eq ▸ h_k₁_lt_n₁
  have h_k₁_lt_sort₂ : k₁ < (sortBy cmp₂ allBetween₂).length := by
    rw [(sortBy_perm cmp₂ allBetween₂).length_eq]; exact h_k₁_lt_n₂
  have h_k₁_lt_assign₂ : k₁ < assignList₂.length := h_assign₂_len ▸ h_k₁_lt_n₂
  have h_k₁_lt_assignLf :
      k₁ < (assignRanks cmp₂ (sortBy cmp₂ (allBetween₁.map f))).length := by
    rw [assignRanks_length]; exact h_k₁_lt_Lf
  have h_rank_eq_at_k₁ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = ((assignRanks cmp₂ (sortBy cmp₂ (allBetween₁.map f)))[k₁]'h_k₁_lt_assignLf).2 :=
    assignRanks_rank_eq_of_sorted_perm cmp₂
      h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂ h_sort_perm h_sort₂ h_sort_Lf k₁
      h_k₁_lt_sort₂ h_k₁_lt_Lf
  have h_get_of_list_eq_pair : ∀ {L₁ L₂ : List (PathsBetween n × Nat)}
      (h_eq : L₁ = L₂) (i : Nat) (h₁ : i < L₁.length) (h₂ : i < L₂.length),
      L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_rank_at_k₁_via_map :
      ((assignRanks cmp₂ (sortBy cmp₂ (allBetween₁.map f)))[k₁]'h_k₁_lt_assignLf).2
        = item₁.2 := by
    have h_k₁_lt_assignList₁_map : k₁ < (assignList₁.map (fun e => (f e.1, e.2))).length := by
      rw [List.length_map, h_assign₁_len]; exact h_k₁_lt_n₁
    rw [h_get_of_list_eq_pair h_assign_pathMapF_eq k₁ h_k₁_lt_assignLf h_k₁_lt_assignList₁_map,
        List.getElem_map]
    show ((assignList₁[k₁]'(h_assign₁_len ▸ h_k₁_lt_n₁)).2 : Nat) = item₁.2
    rw [h_assign_k₁]
  have h_rank_at_k₁_eq : (assignList₂[k₁]'h_k₁_lt_assign₂).2 = item₁.2 := by
    rw [h_rank_eq_at_k₁]; exact h_rank_at_k₁_via_map
  -- L_f at k₁ = q.
  have h_get_of_list_eq : ∀ {L₁ L₂ : List (PathsBetween n)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_Lf_k₁ : (sortBy cmp₂ (allBetween₁.map f))[k₁]'h_k₁_lt_Lf = q := by
    have h_k₁_lt_map : k₁ < ((sortBy cmp₁ allBetween₁).map f).length := by
      rw [List.length_map]; exact h_k₁_lt_sort₁
    rw [h_get_of_list_eq h_Lf_eq k₁ h_k₁_lt_Lf h_k₁_lt_map, List.getElem_map,
        ← h_item₁_1_eq, ← hq_def]
  have h_class_eq : cmp₂ ((sortBy cmp₂ (allBetween₁.map f))[k₁]'h_k₁_lt_Lf)
                       ((sortBy cmp₂ allBetween₂)[k₁]'h_k₁_lt_sort₂) = Ordering.eq :=
    sortedPerm_class_eq cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
      _ _ h_sort_perm.symm h_sort_Lf h_sort₂ k₁ h_k₁_lt_Lf h_k₁_lt_sort₂
  rw [h_Lf_k₁] at h_class_eq
  have h_eq_symm : ∀ a b : PathsBetween n,
      comparePathsBetween vts₂ br₂ a b = Ordering.eq →
      comparePathsBetween vts₂ br₂ b a = Ordering.eq := by
    intros a b hab
    match h_ba : comparePathsBetween vts₂ br₂ b a with
    | .eq => rfl
    | .lt =>
      exfalso
      have h_gt : comparePathsBetween vts₂ br₂ a b = Ordering.gt := h_antisym₁₂ b a h_ba
      rw [h_gt] at hab; cases hab
    | .gt =>
      exfalso
      have h_lt : comparePathsBetween vts₂ br₂ a b = Ordering.lt := h_antisym₂₂ b a h_ba
      rw [h_lt] at hab; cases hab
  have h_rank_eq_k₁_k₂ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = (assignList₂[k₂]'h_k₂_lt).2 := by
    rcases Nat.lt_or_ge k₂ k₁ with h_lt | h_ge
    · have h_le : k₂ ≤ k₁ := h_lt.le
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ allBetween₂)[k₂]'h_k₂_lt_sort₂)
                ((sortBy cmp₂ allBetween₂)[k₁]'h_k₁_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween₂))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween₂))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact (assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ allBetween₂) h_sort₂ k₂ k₁ h_le h_k₁_lt_sort₂ h_class_eq_low).symm
    · have h_le : k₁ ≤ k₂ := h_ge
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ allBetween₂)[k₁]'h_k₁_lt_sort₂)
                ((sortBy cmp₂ allBetween₂)[k₂]'h_k₂_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_eq_symm _ _ h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween₂))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween₂))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ allBetween₂) h_sort₂ k₁ k₂ h_le h_k₂_lt_sort₂ h_class_eq_low
  have h_item₂_2_eq : item₂.2 = item₁.2 := by
    rw [hitem₂_def, ← h_rank_eq_k₁_k₂]; exact h_rank_at_k₁_eq
  refine ⟨item₂, ?_, ?_, ?_, h_item₂_2_eq⟩
  · rw [hitem₂_def]; exact List.getElem_mem _
  · rw [h_item₂_1_eq, hq_def, hf_def]
    by_cases hn : n = 0
    · subst hn; exact p.startVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.startVertexIndex).val = (σ item₁.1.startVertexIndex).val
      rw [hp_def]
  · rw [h_item₂_1_eq, hq_def, hf_def]
    by_cases hn : n = 0
    · subst hn; exact p.endVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.endVertexIndex).val = (σ item₁.1.endVertexIndex).val
      rw [hp_def]

/-! ## P6.A — Body step

The body of the depth-foldl in `calculatePathRankings` preserves `CalcRankingsRel σ`
when the two sides run on `initializePaths G` and `initializePaths (G.permute σ)`
respectively (no `σ ∈ Aut G` needed).

Generalization of `calculatePathRankings_body_preserves_rel` to the σ ∉ Aut G case.
The structure mirrors the σ ∈ Aut G version, but: (a) drops `h_state_σ_fixed`; (b) on
side 2, all `state.pathsOfLength`-related facts come from
`initializePaths_pathsAtDepth_structure` applied to `G.permute σ`; (c) the
σ-rank-closure lemmas are the *general* (two-state) variants. -/

/-- Reuse the existing `CalcRankingsRel` predicate from `PathEquivarianceRelational`. -/
private theorem calculatePathRankings_body_preserves_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (acc₁ acc₂ : Array (Array (Array Nat)) × Array (Array Nat))
    (h_rel : CalcRankingsRel σ acc₁ acc₂)
    (depth : Nat) (h_depth : depth < n) :
    let body₁ := fun (vts : Array VertexType)
        (accumulated : Array (Array (Array Nat)) × Array (Array Nat)) =>
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
      (updatedBetween, updatedFrom)
    let body₂ := fun (vts : Array VertexType)
        (accumulated : Array (Array (Array Nat)) × Array (Array Nat)) =>
      let (currentBetween, currentFrom) := accumulated
      let pathsAtDepth := ((initializePaths (G.permute σ)).pathsOfLength.getD depth #[]).toList
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
      (updatedBetween, updatedFrom)
    CalcRankingsRel σ (body₁ vts₁ acc₁) (body₂ vts₂ acc₂) := by
  obtain ⟨cb₁, cf₁⟩ := acc₁
  obtain ⟨cb₂, cf₂⟩ := acc₂
  obtain ⟨h_cb₁_size, h_cf₁_size, h_cb₁_row, h_cf₁_row, h_cb₁_cell,
          h_cb₂_size, h_cf₂_size, h_cb₂_row, h_cf₂_row, h_cb₂_cell,
          h_cb_rel, h_cf_rel⟩ := h_rel
  -- pathsAtDepth structure for both states (applied to G and G.permute σ).
  obtain ⟨h_outer_len₁, h_starts_eq₁, h_pathsToVertex_len₁, h_inner_conn_len₁⟩ :=
    initializePaths_pathsAtDepth_structure G h_depth
  obtain ⟨h_outer_len₂, h_starts_eq₂, h_pathsToVertex_len₂, h_inner_conn_len₂⟩ :=
    initializePaths_pathsAtDepth_structure (G.permute σ) h_depth
  obtain ⟨h_pairs_nodup₁, _h_pairs_complete₁⟩ :=
    initializePaths_allBetween_pairs_facts G h_depth
  obtain ⟨h_pairs_nodup₂, _h_pairs_complete₂⟩ :=
    initializePaths_allBetween_pairs_facts (G.permute σ) h_depth
  -- Stage A relation: initializePaths (G.permute σ) = PathState.permute σ (initializePaths G).
  have h_stageA : initializePaths (G.permute σ) = PathState.permute σ (initializePaths G) :=
    initializePaths_Aut_equivariant G σ
  -- σ-related betweenRankFn for current state (extended to all d via the out-of-bounds case).
  have h_br_rel : ∀ d : Nat, ∀ s e : Fin n,
      ((cb₂.getD d #[]).getD (σ s).val #[]).getD (σ e).val 0
      = ((cb₁.getD d #[]).getD s.val #[]).getD e.val 0 := by
    intros d s e
    by_cases hd : d < n
    · exact betweenRankFn_σ_rel_from_cells σ cb₁ cb₂ h_cb_rel d hd s e
    · push_neg at hd
      have h_lhs_empty : cb₂.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_cb₂_size]; exact hd),
            Option.getD_none]
      have h_rhs_empty : cb₁.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_cb₁_size]; exact hd),
            Option.getD_none]
      rw [h_lhs_empty, h_rhs_empty]; simp
  -- Apply between_assignList_σ_rank_general (note: state₁ = initializePaths G, state₂ via Stage A).
  -- The general lemma reads from state₂ := PathState.permute σ (initializePaths G).
  -- After applying h_stageA, this is the same as initializePaths (G.permute σ).
  have h_b_σ_rel := by
    have h := between_assignList_σ_rank_general σ (initializePaths G)
      vts₁ vts₂ hvts_rel
      (fun rd rs re => ((cb₁.getD rd #[]).getD rs #[]).getD re 0)
      (fun rd rs re => ((cb₂.getD rd #[]).getD rs #[]).getD re 0)
      h_br_rel depth h_depth h_outer_len₁
      (by rw [← h_stageA]; exact h_outer_len₂)
      h_pathsToVertex_len₁
      (by rw [← h_stageA]; exact h_pathsToVertex_len₂)
      h_inner_conn_len₁
      (by rw [← h_stageA]; exact h_inner_conn_len₂)
    -- Rewrite state₂ in `h`'s conclusion via h_stageA.
    rw [← h_stageA] at h
    exact h
  -- Names matching the body output structure.
  set compareBetween₁ := comparePathsBetween vts₁
    (fun rd rs re => ((cb₁.getD rd #[]).getD rs #[]).getD re 0) with h_compareBetween₁_def
  set compareBetween₂ := comparePathsBetween vts₂
    (fun rd rs re => ((cb₂.getD rd #[]).getD rs #[]).getD re 0) with h_compareBetween₂_def
  set allBetween₁ := ((initializePaths G).pathsOfLength.getD depth #[]).toList.foldl
    (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    with h_allBetween₁_def
  set allBetween₂ := ((initializePaths (G.permute σ)).pathsOfLength.getD depth #[]).toList.foldl
    (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    with h_allBetween₂_def
  set assignList_b₁ := assignRanks compareBetween₁ (sortBy compareBetween₁ allBetween₁)
    with h_assignList_b₁_def
  set assignList_b₂ := assignRanks compareBetween₂ (sortBy compareBetween₂ allBetween₂)
    with h_assignList_b₂_def
  -- Generic helper: any sortBy-derived assignList preserves nodup of (s,e) and completeness, on either state.
  have h_b_nodup_complete_general :
      ∀ (G' : AdjMatrix n) (cmp : PathsBetween n → PathsBetween n → Ordering),
      (((initializePaths G').pathsOfLength.getD depth #[]).toList.foldl
              (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex)
              []).map (fun pb : PathsBetween n => (pb.startVertexIndex.val, pb.endVertexIndex.val))
            |>.Nodup →
      (∀ s e : Fin n, ∃ q ∈ ((initializePaths G').pathsOfLength.getD depth #[]).toList.foldl
              (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [],
              q.startVertexIndex.val = s.val ∧ q.endVertexIndex.val = e.val) →
      ((assignRanks cmp (sortBy cmp (((initializePaths G').pathsOfLength.getD depth #[]).toList.foldl
            (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex)
            []))).map (fun item =>
          (item.1.startVertexIndex.val, item.1.endVertexIndex.val))).Nodup ∧
      (∀ s e : Fin n, ∃ item ∈ assignRanks cmp (sortBy cmp (((initializePaths G').pathsOfLength.getD depth #[]).toList.foldl
            (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex)
            [])),
          item.1.startVertexIndex.val = s.val ∧ item.1.endVertexIndex.val = e.val) := by
    intros G' cmp h_pairs_nodup h_pairs_complete
    set ab := ((initializePaths G').pathsOfLength.getD depth #[]).toList.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [] with h_ab_def
    set assignList := assignRanks cmp (sortBy cmp ab) with h_def
    refine ⟨?_, ?_⟩
    · have h_fst : assignList.map (·.1) = sortBy cmp ab := by
        rw [h_def]; exact assignRanks_map_fst _ _
      have h_eq : assignList.map (fun item =>
          (item.1.startVertexIndex.val, item.1.endVertexIndex.val))
                = (sortBy cmp ab).map (fun pb : PathsBetween n =>
                    (pb.startVertexIndex.val, pb.endVertexIndex.val)) := by
        rw [← h_fst, List.map_map]; rfl
      rw [h_eq]
      have h_perm : ((sortBy cmp ab).map (fun pb : PathsBetween n =>
          (pb.startVertexIndex.val, pb.endVertexIndex.val))).Perm
          (ab.map (fun pb : PathsBetween n =>
            (pb.startVertexIndex.val, pb.endVertexIndex.val))) :=
        (sortBy_perm cmp ab).map _
      exact h_perm.nodup_iff.mpr h_pairs_nodup
    · intros s e
      obtain ⟨q, h_q_in, h_q_start, h_q_end⟩ := h_pairs_complete s e
      have h_q_in_sort : q ∈ sortBy cmp ab :=
        (sortBy_perm cmp ab).mem_iff.mpr h_q_in
      have h_q_in_map : q ∈ assignList.map (·.1) := by
        rw [h_def, assignRanks_map_fst]; exact h_q_in_sort
      obtain ⟨item, h_item_in, h_item_eq⟩ := List.mem_map.mp h_q_in_map
      refine ⟨item, h_item_in, ?_, ?_⟩
      · rw [h_item_eq]; exact h_q_start
      · rw [h_item_eq]; exact h_q_end
  obtain ⟨h_b₁_nodup, h_b₁_complete⟩ :=
    h_b_nodup_complete_general G compareBetween₁ h_pairs_nodup₁ _h_pairs_complete₁
  obtain ⟨h_b₂_nodup, h_b₂_complete⟩ :=
    h_b_nodup_complete_general (G.permute σ) compareBetween₂ h_pairs_nodup₂ _h_pairs_complete₂
  -- Apply setBetween_chain_σRelated.
  have h_chain_b := setBetween_chain_σRelated σ cb₁ cb₂
    h_cb₁_size h_cb₂_size h_cb₁_row h_cb₂_row h_cb₁_cell h_cb₂_cell h_cb_rel
    depth h_depth assignList_b₁ assignList_b₂
    h_b₁_nodup h_b₂_nodup h_b₁_complete h_b₂_complete h_b_σ_rel
  obtain ⟨h_ub₁_size, h_ub₂_size, h_ub₁_row, h_ub₂_row, h_ub₁_cell, h_ub₂_cell, h_ub_rel⟩ :=
    h_chain_b
  -- updatedBetween for both sides.
  set updatedBetween₁ := assignList_b₁.foldl
    (fun (betweenAcc : Array (Array (Array Nat))) item =>
      let (pathBetween, rank) := item
      setBetween betweenAcc depth pathBetween.startVertexIndex.val
        pathBetween.endVertexIndex.val rank) cb₁ with h_updatedBetween₁_def
  set updatedBetween₂ := assignList_b₂.foldl
    (fun (betweenAcc : Array (Array (Array Nat))) item =>
      let (pathBetween, rank) := item
      setBetween betweenAcc depth pathBetween.startVertexIndex.val
        pathBetween.endVertexIndex.val rank) cb₂ with h_updatedBetween₂_def
  -- σ-related updatedBetweenFn (for the from-side step).
  have h_updatedBr_rel : ∀ d : Nat, ∀ s e : Fin n,
      ((updatedBetween₂.getD d #[]).getD (σ s).val #[]).getD (σ e).val 0
      = ((updatedBetween₁.getD d #[]).getD s.val #[]).getD e.val 0 := by
    intros d s e
    by_cases hd : d < n
    · exact betweenRankFn_σ_rel_from_cells σ updatedBetween₁ updatedBetween₂ h_ub_rel d hd s e
    · push_neg at hd
      have h_lhs_empty : updatedBetween₂.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_ub₂_size]; exact hd),
            Option.getD_none]
      have h_rhs_empty : updatedBetween₁.getD d #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [h_ub₁_size]; exact hd),
            Option.getD_none]
      rw [h_lhs_empty, h_rhs_empty]; simp
  -- Apply from_assignList_σ_rank_general.
  set compareFrom₁ := comparePathsFrom vts₁
    (fun rd rs re => ((updatedBetween₁.getD rd #[]).getD rs #[]).getD re 0) with h_compareFrom₁_def
  set compareFrom₂ := comparePathsFrom vts₂
    (fun rd rs re => ((updatedBetween₂.getD rd #[]).getD rs #[]).getD re 0) with h_compareFrom₂_def
  have h_f_σ_rel := by
    have h := from_assignList_σ_rank_general σ (initializePaths G)
      vts₁ vts₂ hvts_rel
      (fun rd rs re => ((updatedBetween₁.getD rd #[]).getD rs #[]).getD re 0)
      (fun rd rs re => ((updatedBetween₂.getD rd #[]).getD rs #[]).getD re 0)
      h_updatedBr_rel depth h_depth h_outer_len₁
      (by rw [← h_stageA]; exact h_outer_len₂)
      h_pathsToVertex_len₁
      (by rw [← h_stageA]; exact h_pathsToVertex_len₂)
      h_inner_conn_len₁
      (by rw [← h_stageA]; exact h_inner_conn_len₂)
    rw [← h_stageA] at h
    exact h
  -- Generic helper: any sortBy on pathsAtDepth gives starts permuted equal to range n.
  have h_f_starts_perm_general :
      ∀ (G' : AdjMatrix n) (cmp : PathsFrom n → PathsFrom n → Ordering),
      ((initializePaths G').pathsOfLength.getD depth #[]).toList.map
          (·.startVertexIndex.val) = List.range n →
      ((assignRanks cmp (sortBy cmp ((initializePaths G').pathsOfLength.getD depth #[]).toList)).map
          (·.1.startVertexIndex.val)).Perm (List.range n) := by
    intros G' cmp h_starts_eq
    set assignList := assignRanks cmp
      (sortBy cmp ((initializePaths G').pathsOfLength.getD depth #[]).toList) with h_def
    have h_fst : assignList.map (·.1) = sortBy cmp
        ((initializePaths G').pathsOfLength.getD depth #[]).toList := by
      rw [h_def]; exact assignRanks_map_fst _ _
    have h_eq : assignList.map (·.1.startVertexIndex.val)
              = (sortBy cmp ((initializePaths G').pathsOfLength.getD depth #[]).toList).map
                  (·.startVertexIndex.val) := by
      rw [← h_fst, List.map_map]; rfl
    rw [h_eq]
    have h_perm : ((sortBy cmp
        ((initializePaths G').pathsOfLength.getD depth #[]).toList).map (·.startVertexIndex.val)).Perm
        (((initializePaths G').pathsOfLength.getD depth #[]).toList.map (·.startVertexIndex.val)) :=
      (sortBy_perm cmp _).map _
    rw [h_starts_eq] at h_perm
    exact h_perm
  set assignList_f₁ := assignRanks compareFrom₁
    (sortBy compareFrom₁ ((initializePaths G).pathsOfLength.getD depth #[]).toList)
    with h_assignList_f₁_def
  set assignList_f₂ := assignRanks compareFrom₂
    (sortBy compareFrom₂ ((initializePaths (G.permute σ)).pathsOfLength.getD depth #[]).toList)
    with h_assignList_f₂_def
  have h_f₁_starts_perm := h_f_starts_perm_general G compareFrom₁ h_starts_eq₁
  have h_f₂_starts_perm := h_f_starts_perm_general (G.permute σ) compareFrom₂ h_starts_eq₂
  -- Apply set_chain_σRelated.
  have h_chain_f := set_chain_σRelated σ cf₁ cf₂
    h_cf₁_size h_cf₂_size h_cf₁_row h_cf₂_row h_cf_rel depth h_depth
    assignList_f₁ assignList_f₂ h_f₁_starts_perm h_f₂_starts_perm h_f_σ_rel
  obtain ⟨h_uf₁_size, h_uf₂_size, h_uf₁_row, h_uf₂_row, h_uf_rel⟩ := h_chain_f
  -- Combine into CalcRankingsRel.
  exact ⟨h_ub₁_size, h_uf₁_size, h_ub₁_row, h_uf₁_row, h_ub₁_cell,
         h_ub₂_size, h_uf₂_size, h_ub₂_row, h_uf₂_row, h_ub₂_cell,
         h_ub_rel, h_uf_rel⟩

/-! ## P6.A target — Stage B-rel general σ

`calculatePathRankings_σ_equivariant_general` — relational σ-equivariance of
`calculatePathRankings` for an *arbitrary* `σ : Equiv.Perm (Fin n)`. Pending the
build-up of the relational σ-rank-closure lemmas + body step + foldl induction. -/

/-- Cell-level σ-relatedness facts for `calculatePathRankings`'s output run on
σ-related typing arrays + Stage A-related path states. Generalization of
`calculatePathRankings_σ_cell_rel_facts` to drop `σ ∈ Aut G`. -/
private theorem calculatePathRankings_σ_cell_general_facts
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    let rs₁ := calculatePathRankings (initializePaths G) vts₁
    let rs₂ := calculatePathRankings (initializePaths (G.permute σ)) vts₂
    (∀ d : Nat, d < n → ∀ s : Fin n,
        (rs₂.fromRanks.getD d #[]).getD s.val 0
        = (rs₁.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
        ((rs₂.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
        = ((rs₁.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  -- Unfold calculatePathRankings.
  unfold calculatePathRankings
  -- Initial accumulator (zero tables).
  set acc₀ := (((Array.range n).map fun _ =>
                  (Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat)),
               ((Array.range n).map fun _ => (Array.range n).map fun _ : Nat => (0 : Nat)))
    with h_acc₀_def
  -- Initial CalcRankingsRel on (acc₀, acc₀).
  have h_init : CalcRankingsRel σ acc₀ acc₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_acc₀_def]
    · simp [h_acc₀_def]
    · intro d hd; simp [h_acc₀_def, hd]
    · intro d hd; simp [h_acc₀_def, hd]
    · intro d hd s hs; simp [h_acc₀_def, hd, hs]
    · simp [h_acc₀_def]
    · simp [h_acc₀_def]
    · intro d hd; simp [h_acc₀_def, hd]
    · intro d hd; simp [h_acc₀_def, hd]
    · intro d hd s hs; simp [h_acc₀_def, hd, hs]
    · intro d hd s e
      have h_lhs : (((acc₀.1).getD d #[]).getD s.val #[]).getD e.val 0 = 0 := by
        simp [h_acc₀_def, hd]
      have h_rhs : (((acc₀.1).getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0 = 0 := by
        simp [h_acc₀_def, hd]
      rw [h_lhs, h_rhs]
    · intro d hd s
      have h_lhs : ((acc₀.2).getD d #[]).getD s.val 0 = 0 := by
        simp [h_acc₀_def, hd]
      have h_rhs : ((acc₀.2).getD d #[]).getD (σ⁻¹ s).val 0 = 0 := by
        simp [h_acc₀_def, hd]
      rw [h_lhs, h_rhs]
  -- Foldl induction with parallel BUT-DIFFERENT bodies (body₁ on G; body₂ on G.permute σ).
  suffices h_step : ∀ (l : List Nat) (a₁ a₂ : Array (Array (Array Nat)) × Array (Array Nat)),
      (∀ d ∈ l, d < n) → CalcRankingsRel σ a₁ a₂ →
      CalcRankingsRel σ
        (l.foldl (fun acc d =>
          (fun depth => fun (vts : Array VertexType)
              (accumulated : Array (Array (Array Nat)) × Array (Array Nat)) =>
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
            (updatedBetween, updatedFrom)) d vts₁ acc) a₁)
        (l.foldl (fun acc d =>
          (fun depth => fun (vts : Array VertexType)
              (accumulated : Array (Array (Array Nat)) × Array (Array Nat)) =>
            let (currentBetween, currentFrom) := accumulated
            let pathsAtDepth := ((initializePaths (G.permute σ)).pathsOfLength.getD depth #[]).toList
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
            (updatedBetween, updatedFrom)) d vts₂ acc) a₂) by
    have h_l_lt : ∀ d ∈ List.range n, d < n := fun d hd => List.mem_range.mp hd
    have h_final := h_step (List.range n) acc₀ acc₀ h_l_lt h_init
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h_b_rel, h_f_rel⟩ := h_final
    exact ⟨h_f_rel, h_b_rel⟩
  intro l
  induction l with
  | nil => intros _ _ _ h_rel; exact h_rel
  | cons x xs ih =>
    intros a₁ a₂ h_l_lt h_rel
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · intros d h_d_in
      exact h_l_lt d (List.mem_cons_of_mem _ h_d_in)
    · -- Apply body_preserves_general with depth = x.
      have h_x_lt : x < n := h_l_lt x List.mem_cons_self
      exact calculatePathRankings_body_preserves_general G σ vts₁ vts₂ hvts_rel
        a₁ a₂ h_rel x h_x_lt

/-- **Stage B-rel general σ: relational σ-equivariance of `calculatePathRankings`**
without `σ ∈ Aut G`.

The two sides run on `initializePaths G` and `initializePaths (G.permute σ)` respectively
(connected via `initializePaths_Aut_equivariant`, which is fully general). The output
rank-cells are σ-related (i.e., shifted by σ⁻¹). -/
theorem calculatePathRankings_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    let rs₁ := calculatePathRankings (initializePaths G) vts₁
    let rs₂ := calculatePathRankings (initializePaths (G.permute σ)) vts₂
    (∀ d : Nat, d < n → ∀ s : Fin n,
        (rs₂.fromRanks.getD d #[]).getD s.val 0
        = (rs₁.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
        ((rs₂.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
        = ((rs₁.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) :=
  calculatePathRankings_σ_cell_general_facts G σ vts₁ vts₂ hvts_rel

end Graph
