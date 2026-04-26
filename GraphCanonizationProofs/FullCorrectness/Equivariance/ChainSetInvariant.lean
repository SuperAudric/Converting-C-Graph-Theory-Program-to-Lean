import FullCorrectness.Equivariance.PathsAtDepthStructure

/-!
# Chain σ-invariance lemmas (`FullCorrectness.Equivariance.ChainSetInvariant`)

The body of `calculatePathRankings` updates `currentBetween` and `currentFrom` via
chains of `setBetween` / `set!` operations driven by the assignList from `assignRanks`.
For σ-invariance preservation, we need:

- The chain preserves σ-invariance of cells **outside** the touched depth.
- For the touched depth, the new cells are σ-invariant when:
  - The currentBetween/currentFrom is already σ-invariant.
  - The assignList is σ-rank-closed (each entry's σ-conjugate is also in the assignList
    with the same rank).
  - The assignList has the right uniqueness structure (unique start vertices for `set!`,
    unique (start, end) pairs for `setBetween`).

The σ-rank-closure of the assignList comes from `assignRanks_map_of_cmp_respect`
(already proved): when `cmp` respects `f := PathsFrom.permute σ`, applying `f` to the
first components of the assignList preserves its multiset structure (proof TBD via the
`Perm`-related-sorted lemma).

This module exposes:
- `set_chain_σInvariant` (private) — 1D chain σ-invariance preservation for `fromRanks`
  updates.
- `setBetween_chain_σInvariant` (private) — 2D chain σ-invariance preservation for
  `betweenRanks` updates.
- Plus all supporting size-preservation and outside-target-unchanged helpers.
-/

namespace Graph

variable {n : Nat}

/-- The chain of `set!`s on `fromAcc` preserves the outer array size. -/
theorem set_chain_size_preserving
    (currentFrom : Array (Array Nat)) (depth : Nat)
    (assignList : List (PathsFrom n × Nat)) :
    (assignList.foldl
      (fun (fromAcc : Array (Array Nat)) item =>
        let (pathFrom, rank) := item
        let depthSlice := fromAcc.getD depth #[]
        fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom).size
      = currentFrom.size := by
  induction assignList generalizing currentFrom with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons]
    rw [ih]
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The chain of `set!`s on `fromAcc` preserves each row's size. -/
theorem set_chain_row_size_preserving
    (currentFrom : Array (Array Nat)) (depth : Nat)
    (assignList : List (PathsFrom n × Nat))
    (d : Nat) (h_orig : (currentFrom.getD d #[]).size = n) :
    ((assignList.foldl
      (fun (fromAcc : Array (Array Nat)) item =>
        let (pathFrom, rank) := item
        let depthSlice := fromAcc.getD depth #[]
        fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom).getD d #[]).size = n := by
  induction assignList generalizing currentFrom with
  | nil => exact h_orig
  | cons item l' ih =>
    rw [List.foldl_cons]
    obtain ⟨pathFrom, rank⟩ := item
    apply ih
    -- Need: ((currentFrom.set! depth (slice.set! ...)).getD d #[]).size = n
    by_cases h_eq : depth = d
    · subst h_eq
      by_cases h_in : depth < currentFrom.size
      · have h_eq_step : (currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)).getD depth #[]
              = (currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank := by
          rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_self_of_lt h_in, Option.getD_some]
        show ((currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)).getD depth #[]).size = n
        rw [h_eq_step]
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact h_orig
      · have h_no_change : currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)
              = currentFrom := by
          rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
        show ((currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)).getD depth #[]).size = n
        rw [h_no_change]
        exact h_orig
    · have h_no_change_d : (currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)).getD d #[]
            = currentFrom.getD d #[] := by
        rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_ne h_eq, ← Array.getD_eq_getD_getElem?]
      show ((currentFrom.set! depth ((currentFrom.getD depth #[]).set! pathFrom.startVertexIndex.val rank)).getD d #[]).size = n
      rw [h_no_change_d]
      exact h_orig

/-- **Sub-lemma `set_chain_σInvariant`**: the `set!` chain on `fromRanks` preserves
σ-invariance, given the σ-rank-closure of the assignList plus the assumption that the
start vertices form a permutation of `List.range n` (the realistic case in the algorithm:
each start vertex appears exactly once). -/
theorem set_chain_σInvariant
    (σ : Equiv.Perm (Fin n)) (currentFrom : Array (Array Nat))
    (h_size : currentFrom.size = n)
    (h_row_size : ∀ d : Nat, d < n → (currentFrom.getD d #[]).size = n)
    (h_curr_inv : ∀ d : Nat, d < n → ∀ s : Fin n,
      (currentFrom.getD d #[]).getD s.val 0
      = (currentFrom.getD d #[]).getD (σ⁻¹ s).val 0)
    (depth : Nat) (h_depth : depth < n)
    (assignList : List (PathsFrom n × Nat))
    (h_starts_perm : (assignList.map (·.1.startVertexIndex.val)).Perm (List.range n))
    (h_σ_closure : ∀ item ∈ assignList,
      ∃ item' ∈ assignList,
        item'.1.startVertexIndex.val = (σ item.1.startVertexIndex).val
        ∧ item'.2 = item.2) :
    let result := assignList.foldl
      (fun (fromAcc : Array (Array Nat)) item =>
        let (pathFrom, rank) := item
        let depthSlice := fromAcc.getD depth #[]
        fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom
    -- Sizes preserved.
    result.size = n ∧
    (∀ d : Nat, d < n → (result.getD d #[]).size = n) ∧
    -- σ-invariance preserved.
    (∀ d : Nat, d < n → ∀ s : Fin n,
      (result.getD d #[]).getD s.val 0
      = (result.getD d #[]).getD (σ⁻¹ s).val 0) := by
  -- Define the chain function on the slice.
  set chainFn := fun (fromAcc : Array (Array Nat)) (item : PathsFrom n × Nat) =>
    fromAcc.set! depth ((fromAcc.getD depth #[]).set! item.1.startVertexIndex.val item.2)
  -- Top-level size preservation.
  have h_result_size : (assignList.foldl chainFn currentFrom).size = n := by
    rw [set_chain_size_preserving currentFrom depth assignList]; exact h_size
  -- Row-size preservation.
  have h_result_row_size : ∀ d : Nat, d < n →
      ((assignList.foldl chainFn currentFrom).getD d #[]).size = n := by
    intro d hd
    exact set_chain_row_size_preserving currentFrom depth assignList d (h_row_size d hd)
  refine ⟨h_result_size, h_result_row_size, ?_⟩
  -- σ-invariance of cells.
  intro d hd s
  by_cases h_eq : d = depth
  · -- d = depth: use slice extraction + chain inversion.
    have hd_depth : depth < n := h_eq ▸ hd
    rw [h_eq]
    have h_depth_in : depth < currentFrom.size := h_size ▸ hd_depth
    rw [show assignList.foldl chainFn currentFrom = assignList.foldl
        (fun (fromAcc : Array (Array Nat)) item =>
          let (pathFrom, rank) := item
          let depthSlice := fromAcc.getD depth #[]
          fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) currentFrom from rfl]
    rw [inner_fold_slice_at_depth assignList currentFrom depth h_depth_in]
    -- Convert the foldl into a foldl on the mapped (Nat × Nat) list.
    rw [show assignList.foldl
            (fun (slice : Array Nat) (item : PathsFrom n × Nat) =>
              slice.set! item.1.startVertexIndex.val item.2)
            (currentFrom.getD depth #[])
          = (assignList.map (fun item : PathsFrom n × Nat =>
                (item.1.startVertexIndex.val, item.2))).foldl
            (fun (slice : Array Nat) (item : Nat × Nat) => slice.set! item.1 item.2)
            (currentFrom.getD depth #[]) from by
        rw [List.foldl_map]]
    set L_pairs := assignList.map (fun item : PathsFrom n × Nat =>
      (item.1.startVertexIndex.val, item.2)) with hL_pairs
    -- Nodup of the start values.
    have h_keys_eq : L_pairs.map (·.1) = assignList.map (·.1.startVertexIndex.val) := by
      rw [hL_pairs, List.map_map]; rfl
    have h_nodup : (L_pairs.map (·.1)).Nodup := by
      rw [h_keys_eq]
      exact h_starts_perm.nodup_iff.mpr List.nodup_range
    -- Existence of an entry with start = s.val:
    have h_s_in_range : s.val ∈ List.range n := List.mem_range.mpr s.isLt
    have h_s_in_starts : s.val ∈ assignList.map (·.1.startVertexIndex.val) :=
      h_starts_perm.symm.mem_iff.mp h_s_in_range
    obtain ⟨item_s, h_item_s_in, h_item_s_start⟩ := List.mem_map.mp h_s_in_starts
    -- Existence of an entry with start = (σ⁻¹ s).val:
    have h_σs_in_range : (σ⁻¹ s).val ∈ List.range n := List.mem_range.mpr (σ⁻¹ s).isLt
    have h_σs_in_starts : (σ⁻¹ s).val ∈ assignList.map (·.1.startVertexIndex.val) :=
      h_starts_perm.symm.mem_iff.mp h_σs_in_range
    obtain ⟨item_σs, h_item_σs_in, h_item_σs_start⟩ := List.mem_map.mp h_σs_in_starts
    -- Mapped pair targets.
    let target_s : Nat × Nat := (s.val, item_s.2)
    let target_σs : Nat × Nat := ((σ⁻¹ s).val, item_σs.2)
    have h_target_s_in : target_s ∈ L_pairs := by
      rw [hL_pairs]
      refine List.mem_map.mpr ⟨item_s, h_item_s_in, ?_⟩
      show (item_s.1.startVertexIndex.val, item_s.2) = (s.val, item_s.2)
      rw [h_item_s_start]
    have h_target_σs_in : target_σs ∈ L_pairs := by
      rw [hL_pairs]
      refine List.mem_map.mpr ⟨item_σs, h_item_σs_in, ?_⟩
      show (item_σs.1.startVertexIndex.val, item_σs.2) = ((σ⁻¹ s).val, item_σs.2)
      rw [h_item_σs_start]
    have h_slice_size : (currentFrom.getD depth #[]).size = n := h_row_size depth hd_depth
    have h_target_s_bound : target_s.1 < (currentFrom.getD depth #[]).size := by
      show s.val < (currentFrom.getD depth #[]).size
      rw [h_slice_size]; exact s.isLt
    have h_target_σs_bound : target_σs.1 < (currentFrom.getD depth #[]).size := by
      show (σ⁻¹ s).val < (currentFrom.getD depth #[]).size
      rw [h_slice_size]; exact (σ⁻¹ s).isLt
    -- Apply chain-at-target-nodup.
    have h_cell_s :
        Array.getD (List.foldl (fun (slice : Array Nat) (item : Nat × Nat) =>
            slice.set! item.1 item.2) (currentFrom.getD depth #[]) L_pairs) s.val 0
        = item_s.2 :=
      array_set_chain_at_target_nodup (currentFrom.getD depth #[]) L_pairs target_s 0
        h_target_s_in h_nodup h_target_s_bound
    have h_cell_σs :
        Array.getD (List.foldl (fun (slice : Array Nat) (item : Nat × Nat) =>
            slice.set! item.1 item.2) (currentFrom.getD depth #[]) L_pairs) (σ⁻¹ s).val 0
        = item_σs.2 :=
      array_set_chain_at_target_nodup (currentFrom.getD depth #[]) L_pairs target_σs 0
        h_target_σs_in h_nodup h_target_σs_bound
    show Array.getD (List.foldl _ (currentFrom.getD depth #[]) L_pairs) s.val 0
       = Array.getD (List.foldl _ (currentFrom.getD depth #[]) L_pairs) (σ⁻¹ s).val 0
    rw [h_cell_s, h_cell_σs]
    -- Now show item_s.2 = item_σs.2 via σ-closure.
    obtain ⟨item', h_item'_in, h_item'_start, h_item'_rank⟩ := h_σ_closure item_σs h_item_σs_in
    have h_σs_eq_fin : item_σs.1.startVertexIndex = σ⁻¹ s := by
      apply Fin.ext; exact h_item_σs_start
    rw [h_σs_eq_fin] at h_item'_start
    have h_σσ_eq : σ (σ⁻¹ s) = s := by simp
    rw [h_σσ_eq] at h_item'_start
    -- (item'.1.start.val, item'.2) ∈ L_pairs.
    have h_item'_pair_in : (item'.1.startVertexIndex.val, item'.2) ∈ L_pairs := by
      rw [hL_pairs]
      exact List.mem_map.mpr ⟨item', h_item'_in, rfl⟩
    rw [h_item'_start] at h_item'_pair_in
    -- Both (s.val, item'.2) and (s.val, item_s.2) are in L_pairs; Nodup keys ⟹ equal.
    have h_target_s_eq : target_s = (s.val, item_s.2) := rfl
    rw [h_target_s_eq] at h_target_s_in
    -- L_pairs has Nodup keys; if two pairs share the same .1, they must be the same pair.
    have h_unique_v : ∀ (L : List (Nat × Nat)) (k v₁ v₂ : Nat),
        (L.map (·.1)).Nodup → (k, v₁) ∈ L → (k, v₂) ∈ L → v₁ = v₂ := by
      intro L k v₁ v₂ hND h1 h2
      induction L with
      | nil => exact absurd h1 (List.not_mem_nil)
      | cons hd tl ih =>
        simp only [List.map_cons, List.nodup_cons] at hND
        obtain ⟨h_hd_not_in, h_tl_nd⟩ := hND
        rcases List.mem_cons.mp h1 with h1 | h1
        · rcases List.mem_cons.mp h2 with h2 | h2
          · have heq : (Prod.mk k v₁ : Nat × Nat) = (k, v₂) := h1.trans h2.symm
            exact (Prod.mk.injEq _ _ _ _).mp heq |>.2
          · have h_hd_eq : hd.1 = k := by rw [← h1]
            have : k ∈ tl.map (·.1) := List.mem_map.mpr ⟨(k, v₂), h2, rfl⟩
            exact absurd this (h_hd_eq ▸ h_hd_not_in)
        · rcases List.mem_cons.mp h2 with h2 | h2
          · have h_hd_eq : hd.1 = k := by rw [← h2]
            have : k ∈ tl.map (·.1) := List.mem_map.mpr ⟨(k, v₁), h1, rfl⟩
            exact absurd this (h_hd_eq ▸ h_hd_not_in)
          · exact ih h_tl_nd h1 h2
    have h_v_eq : item_s.2 = item'.2 := h_unique_v L_pairs s.val item_s.2 item'.2
      h_nodup h_target_s_in h_item'_pair_in
    rw [h_v_eq, h_item'_rank]
  · -- d ≠ depth: use inner_fold_other_depth_unchanged.
    have h_dep_ne_d : depth ≠ d := fun h => h_eq h.symm
    have h_lhs : (assignList.foldl chainFn currentFrom).getD d #[] = currentFrom.getD d #[] :=
      inner_fold_other_depth_unchanged assignList currentFrom depth d h_dep_ne_d
    rw [h_lhs]
    exact h_curr_inv d hd s

/-! ### 2D chain inversion (for setBetween chain)

For a chain of `ds.set! s (innerSlice.set! e r)` operations with Nodup `(s, e)` pairs,
the cell at `(s_target, e_target)` is determined by the unique entry whose `(s, e)` matches.
These mirror the 1D chain helpers in RankStateInvariants but with 2D keys. -/

/-- 2D chain "outside" lemma: if no step has `(s, e) = (s_target, e_target)`, the cell at
`(s_target, e_target)` is preserved. -/
private theorem nested_set_chain_outside_pair_unchanged
    {α : Type} (ds₀ : Array (Array α)) (l : List (Nat × Nat × α))
    (s_target e_target : Nat) (defaultV : α)
    (h : ∀ item ∈ l, ¬ (item.1 = s_target ∧ item.2.1 = e_target)) :
    ((l.foldl (fun (ds : Array (Array α)) item =>
        ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2)) ds₀).getD s_target #[]).getD e_target defaultV
      = (ds₀.getD s_target #[]).getD e_target defaultV := by
  induction l generalizing ds₀ with
  | nil => rfl
  | cons head l' ih =>
    rw [List.foldl_cons]
    have h_head : ¬ (head.1 = s_target ∧ head.2.1 = e_target) := h head List.mem_cons_self
    have h_tail : ∀ item ∈ l', ¬ (item.1 = s_target ∧ item.2.1 = e_target) :=
      fun item hi => h item (List.mem_cons_of_mem _ hi)
    rw [ih (ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2)) h_tail]
    -- Show one step preserves cell at (s_target, e_target).
    by_cases h_s : head.1 = s_target
    · have h_e_ne : head.2.1 ≠ e_target := fun h_e => h_head ⟨h_s, h_e⟩
      subst h_s
      -- Cell at (s_target, e_target) after one step:
      --   new ds[s_target] = (old ds[s_target]).set! head.2.1 head.2.2.
      -- Cell at e_target: head.2.1 ≠ e_target, so set! doesn't affect e_target.
      by_cases h_in_outer : head.1 < ds₀.size
      · -- head.1 = s_target (but we replaced s_target back to head.1 since they're equal).
        have h_step :
            (ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2)).getD head.1 #[]
            = (ds₀.getD head.1 #[]).set! head.2.1 head.2.2 := by
          rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_self_of_lt h_in_outer, Option.getD_some]
        rw [h_step]
        -- Now: ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2).getD e_target defaultV
        --    = (ds₀.getD head.1 #[]).getD e_target defaultV
        rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_ne h_e_ne, ← Array.getD_eq_getD_getElem?]
      · -- head.1 ≥ ds₀.size: set! is a no-op, so ds unchanged.
        have h_eq_ds : ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2) = ds₀ := by
          rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
        rw [h_eq_ds]
    · -- head.1 ≠ s_target: ds[s_target] unchanged.
      have h_eq_outer : (ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2)).getD s_target #[]
                      = ds₀.getD s_target #[] := by
        rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_ne h_s, ← Array.getD_eq_getD_getElem?]
      rw [h_eq_outer]

/-- 2D chain "at target" lemma: with `Nodup` `(s, e)` keys and `target ∈ l`, the cell at
`(target.1, target.2.1)` equals `target.2.2`. -/
theorem nested_set_chain_at_target_pair_nodup
    {α : Type} (ds₀ : Array (Array α)) (l : List (Nat × Nat × α))
    (target : Nat × Nat × α) (defaultV : α)
    (h_target_in : target ∈ l)
    (h_nodup : (l.map (fun item => (item.1, item.2.1))).Nodup)
    (h_target_outer_bound : target.1 < ds₀.size)
    (h_target_inner_bound : target.2.1 < (ds₀.getD target.1 #[]).size) :
    ((l.foldl (fun (ds : Array (Array α)) item =>
        ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2)) ds₀).getD target.1 #[]).getD target.2.1 defaultV
      = target.2.2 := by
  induction l generalizing ds₀ with
  | nil => exact absurd h_target_in (by simp)
  | cons head l' ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h_target_in with h_eq | h_in_tail
    · -- target = head.
      have h_others_ne : ∀ item ∈ l', ¬ (item.1 = target.1 ∧ item.2.1 = target.2.1) := by
        intro item h_in_item ⟨h_s_eq, h_e_eq⟩
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : (head.1, head.2.1) ∉ l'.map (fun item => (item.1, item.2.1)) :=
          (List.nodup_cons.mp h_nd').1
        rw [← h_eq] at h_head_not_in
        apply h_head_not_in
        exact List.mem_map.mpr ⟨item, h_in_item, by rw [h_s_eq, h_e_eq]⟩
      -- After head step: ds at (target.1, target.2.1) = target.2.2.
      have h_step_eq : ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2)
                     = ds₀.set! target.1 ((ds₀.getD target.1 #[]).set! target.2.1 target.2.2) := by
        rw [h_eq]
      rw [h_step_eq]
      rw [nested_set_chain_outside_pair_unchanged
            (ds₀.set! target.1 ((ds₀.getD target.1 #[]).set! target.2.1 target.2.2))
            l' target.1 target.2.1 defaultV h_others_ne]
      -- Now compute the cell value directly.
      have h_step_outer : (ds₀.set! target.1 ((ds₀.getD target.1 #[]).set! target.2.1 target.2.2)).getD target.1 #[]
                        = (ds₀.getD target.1 #[]).set! target.2.1 target.2.2 := by
        rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_self_of_lt h_target_outer_bound, Option.getD_some]
      rw [h_step_outer]
      rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds_self_of_lt h_target_inner_bound, Option.getD_some]
    · -- target ∈ l'. By Nodup, head's pair ≠ target's pair, so head doesn't affect cell.
      have h_pair_ne : (head.1, head.2.1) ≠ (target.1, target.2.1) := by
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : (head.1, head.2.1) ∉ l'.map (fun item => (item.1, item.2.1)) :=
          (List.nodup_cons.mp h_nd').1
        intro h_eq
        apply h_head_not_in
        rw [h_eq]
        exact List.mem_map.mpr ⟨target, h_in_tail, rfl⟩
      have h_nodup' : (l'.map (fun item => (item.1, item.2.1))).Nodup := by
        simp only [List.map_cons] at h_nodup
        exact (List.nodup_cons.mp h_nodup).2
      -- Apply IH on (ds₀.set! head.1 ...).
      set ds₀' := ds₀.set! head.1 ((ds₀.getD head.1 #[]).set! head.2.1 head.2.2) with hds₀'
      have h_outer_bound' : target.1 < ds₀'.size := by
        rw [hds₀']
        simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact h_target_outer_bound
      have h_inner_bound' : target.2.1 < (ds₀'.getD target.1 #[]).size := by
        -- Cell at target.1 may have been replaced or unchanged; either way size = original.
        by_cases h_s : head.1 = target.1
        · -- head.1 = target.1: ds₀'[target.1] = (ds₀[target.1]).set! ..., size preserved.
          by_cases h_in_outer : head.1 < ds₀.size
          · have h_step : ds₀'.getD target.1 #[]
                = (ds₀.getD head.1 #[]).set! head.2.1 head.2.2 := by
              rw [hds₀', ← h_s, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
                  Array.getElem?_setIfInBounds_self_of_lt h_in_outer, Option.getD_some]
            rw [h_step]
            simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
            -- (ds₀.getD head.1 #[]).size = (ds₀.getD target.1 #[]).size since head.1 = target.1.
            rw [h_s]; exact h_target_inner_bound
          · have h_no_change : ds₀' = ds₀ := by
              rw [hds₀', Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
            rw [h_no_change]; exact h_target_inner_bound
        · have h_no_change : ds₀'.getD target.1 #[] = ds₀.getD target.1 #[] := by
            rw [hds₀', Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
                Array.getElem?_setIfInBounds_ne h_s, ← Array.getD_eq_getD_getElem?]
          rw [h_no_change]; exact h_target_inner_bound
      exact ih ds₀' h_in_tail h_nodup' h_outer_bound' h_inner_bound'

/-- The setBetween chain preserves the outer array size. -/
theorem setBetween_chain_size_preserving
    (currentBetween : Array (Array (Array Nat))) (depth : Nat)
    (assignList : List (PathsBetween n × Nat)) :
    (assignList.foldl
      (fun (betweenAcc : Array (Array (Array Nat))) item =>
        let (pathBetween, rank) := item
        setBetween betweenAcc depth pathBetween.startVertexIndex.val
          pathBetween.endVertexIndex.val rank) currentBetween).size = currentBetween.size := by
  induction assignList generalizing currentBetween with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons]
    rw [ih]
    unfold setBetween
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The setBetween chain preserves each row's size. -/
theorem setBetween_chain_row_size_preserving
    (currentBetween : Array (Array (Array Nat))) (depth : Nat)
    (assignList : List (PathsBetween n × Nat))
    (d : Nat) (h_orig : (currentBetween.getD d #[]).size = n) :
    ((assignList.foldl
      (fun (betweenAcc : Array (Array (Array Nat))) item =>
        let (pathBetween, rank) := item
        setBetween betweenAcc depth pathBetween.startVertexIndex.val
          pathBetween.endVertexIndex.val rank) currentBetween).getD d #[]).size = n := by
  induction assignList generalizing currentBetween with
  | nil => exact h_orig
  | cons item l' ih =>
    rw [List.foldl_cons]
    obtain ⟨pathBetween, rank⟩ := item
    apply ih
    show ((setBetween currentBetween depth pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank).getD d #[]).size = n
    unfold setBetween
    by_cases h_eq : depth = d
    · subst h_eq
      by_cases h_in : depth < currentBetween.size
      · have h_eq_step : (currentBetween.set! depth
                ((currentBetween.getD depth #[]).set! pathBetween.startVertexIndex.val
                  (((currentBetween.getD depth #[]).getD pathBetween.startVertexIndex.val #[]).set!
                    pathBetween.endVertexIndex.val rank))).getD depth #[]
                = (currentBetween.getD depth #[]).set! pathBetween.startVertexIndex.val
                    (((currentBetween.getD depth #[]).getD pathBetween.startVertexIndex.val #[]).set!
                      pathBetween.endVertexIndex.val rank) := by
          rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_self_of_lt h_in, Option.getD_some]
        rw [h_eq_step]
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact h_orig
      · have h_no_change : currentBetween.set! depth
              ((currentBetween.getD depth #[]).set! pathBetween.startVertexIndex.val
                (((currentBetween.getD depth #[]).getD pathBetween.startVertexIndex.val #[]).set!
                  pathBetween.endVertexIndex.val rank))
              = currentBetween := by
          rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
        rw [h_no_change]
        exact h_orig
    · have h_no_change_d : (currentBetween.set! depth
            ((currentBetween.getD depth #[]).set! pathBetween.startVertexIndex.val
              (((currentBetween.getD depth #[]).getD pathBetween.startVertexIndex.val #[]).set!
                pathBetween.endVertexIndex.val rank))).getD d #[]
          = currentBetween.getD d #[] := by
        rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_ne h_eq, ← Array.getD_eq_getD_getElem?]
      rw [h_no_change_d]
      exact h_orig

/-- The setBetween chain preserves each (depth, start) cell's size. -/
theorem setBetween_chain_cell_size_preserving
    (currentBetween : Array (Array (Array Nat))) (depth : Nat)
    (assignList : List (PathsBetween n × Nat))
    (d : Nat) (s : Nat) (h_orig : ((currentBetween.getD d #[]).getD s #[]).size = n) :
    (((assignList.foldl
      (fun (betweenAcc : Array (Array (Array Nat))) item =>
        let (pathBetween, rank) := item
        setBetween betweenAcc depth pathBetween.startVertexIndex.val
          pathBetween.endVertexIndex.val rank) currentBetween).getD d #[]).getD s #[]).size = n := by
  induction assignList generalizing currentBetween with
  | nil => exact h_orig
  | cons item l' ih =>
    rw [List.foldl_cons]
    obtain ⟨pathBetween, rank⟩ := item
    apply ih
    -- After one setBetween step, ((.getD d #[]).getD s #[]).size = n.
    -- Cell-size preserved by setBetween regardless of d, s.
    have := setBetween_getD_getD_size currentBetween depth pathBetween.startVertexIndex.val
      pathBetween.endVertexIndex.val rank d s
    rw [this]
    exact h_orig

/-- **Sub-lemma `setBetween_chain_σInvariant`**: the `setBetween` chain on `betweenRanks`
preserves σ-invariance, given the σ-rank-closure of the assignList plus the assumption
that the (start, end) pairs in the assignList are all distinct (the realistic case in the
algorithm: each (start, end) pair appears exactly once in `allBetween`).

**Status**: signature stated with Perm-form hypotheses; proof TBD (analogous to
`set_chain_σInvariant` but with 2D chain inversion at the depth-slice level). The
structure mirrors `set_chain_σInvariant`: sizes by induction; σ-inv of cell `(d, s, e)`
splits on `d = depth`. For `d ≠ depth` use the `setBetween d ≠ depth` no-op; for
`d = depth` extract the depth-slice and invert the 2D chain (each `(s, e)` gets the rank
of the unique entry with `(start, end) = (s, e)`); apply σ-closure to bridge cells. -/
theorem setBetween_chain_σInvariant
    (σ : Equiv.Perm (Fin n)) (currentBetween : Array (Array (Array Nat)))
    (h_size : currentBetween.size = n)
    (h_row_size : ∀ d : Nat, d < n → (currentBetween.getD d #[]).size = n)
    (h_cell_size : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      ((currentBetween.getD d #[]).getD s #[]).size = n)
    (h_curr_inv : ∀ d : Nat, d < n → ∀ s e : Fin n,
      ((currentBetween.getD d #[]).getD s.val #[]).getD e.val 0
      = ((currentBetween.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0)
    (depth : Nat) (h_depth : depth < n)
    (assignList : List (PathsBetween n × Nat))
    (h_pairs_nodup : (assignList.map (fun item =>
        (item.1.startVertexIndex.val, item.1.endVertexIndex.val))).Nodup)
    (h_pairs_complete : ∀ s e : Fin n, ∃ item ∈ assignList,
        item.1.startVertexIndex.val = s.val ∧ item.1.endVertexIndex.val = e.val)
    (h_σ_closure : ∀ item ∈ assignList,
      ∃ item' ∈ assignList,
        item'.1.startVertexIndex.val = (σ item.1.startVertexIndex).val
        ∧ item'.1.endVertexIndex.val = (σ item.1.endVertexIndex).val
        ∧ item'.2 = item.2) :
    let result := assignList.foldl
      (fun (betweenAcc : Array (Array (Array Nat))) item =>
        let (pathBetween, rank) := item
        setBetween betweenAcc depth pathBetween.startVertexIndex.val
          pathBetween.endVertexIndex.val rank) currentBetween
    -- Sizes preserved.
    result.size = n ∧
    (∀ d : Nat, d < n → (result.getD d #[]).size = n) ∧
    (∀ d : Nat, d < n → ∀ s : Nat, s < n → ((result.getD d #[]).getD s #[]).size = n) ∧
    -- σ-invariance preserved.
    (∀ d : Nat, d < n → ∀ s e : Fin n,
      ((result.getD d #[]).getD s.val #[]).getD e.val 0
      = ((result.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  set chainFn := fun (betweenAcc : Array (Array (Array Nat))) (item : PathsBetween n × Nat) =>
    setBetween betweenAcc depth item.1.startVertexIndex.val item.1.endVertexIndex.val item.2
  -- Sizes preserved.
  have h_result_size : (assignList.foldl chainFn currentBetween).size = n := by
    rw [setBetween_chain_size_preserving currentBetween depth assignList]; exact h_size
  have h_result_row_size : ∀ d : Nat, d < n →
      ((assignList.foldl chainFn currentBetween).getD d #[]).size = n := by
    intro d hd
    exact setBetween_chain_row_size_preserving currentBetween depth assignList d (h_row_size d hd)
  have h_result_cell_size : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      (((assignList.foldl chainFn currentBetween).getD d #[]).getD s #[]).size = n := by
    intro d hd s hs
    exact setBetween_chain_cell_size_preserving currentBetween depth assignList d s
      (h_cell_size d hd s hs)
  refine ⟨h_result_size, h_result_row_size, h_result_cell_size, ?_⟩
  -- σ-invariance of cells.
  intro d hd s e
  by_cases h_eq : d = depth
  · -- d = depth: use 2D chain inversion.
    have hd_depth : depth < n := h_eq ▸ hd
    rw [h_eq]
    have h_depth_in : depth < currentBetween.size := h_size ▸ hd_depth
    rw [show assignList.foldl chainFn currentBetween = assignList.foldl
        (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc depth pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) currentBetween from rfl]
    rw [setBetween_fold_slice_at_depth assignList currentBetween depth h_depth_in]
    -- Convert the foldl into a foldl on the mapped (Nat × Nat × Nat) list.
    rw [show assignList.foldl
            (fun (ds : Array (Array Nat)) (item : PathsBetween n × Nat) =>
              let s := item.1.startVertexIndex.val
              let e := item.1.endVertexIndex.val
              ds.set! s ((ds.getD s #[]).set! e item.2))
            (currentBetween.getD depth #[])
          = (assignList.map (fun item : PathsBetween n × Nat =>
                (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2))).foldl
            (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
              ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
            (currentBetween.getD depth #[]) from by
        rw [List.foldl_map]]
    set L_triples := assignList.map (fun item : PathsBetween n × Nat =>
      (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2)) with hL_triples
    -- Nodup of (s, e) pairs.
    have h_keys_eq : L_triples.map (fun item => (item.1, item.2.1))
        = assignList.map (fun item =>
            (item.1.startVertexIndex.val, item.1.endVertexIndex.val)) := by
      rw [hL_triples, List.map_map]; rfl
    have h_nodup : (L_triples.map (fun item => (item.1, item.2.1))).Nodup := by
      rw [h_keys_eq]; exact h_pairs_nodup
    -- Pick out unique entries for (s, e) and (σ⁻¹ s, σ⁻¹ e).
    obtain ⟨item_se, h_item_se_in, h_item_se_start, h_item_se_end⟩ :=
      h_pairs_complete s e
    obtain ⟨item_σse, h_item_σse_in, h_item_σse_start, h_item_σse_end⟩ :=
      h_pairs_complete (σ⁻¹ s) (σ⁻¹ e)
    -- Mapped triple targets.
    let target_se : Nat × Nat × Nat := (s.val, e.val, item_se.2)
    let target_σse : Nat × Nat × Nat := ((σ⁻¹ s).val, (σ⁻¹ e).val, item_σse.2)
    have h_target_se_in : target_se ∈ L_triples := by
      rw [hL_triples]
      refine List.mem_map.mpr ⟨item_se, h_item_se_in, ?_⟩
      show (item_se.1.startVertexIndex.val, item_se.1.endVertexIndex.val, item_se.2) = (s.val, e.val, item_se.2)
      rw [h_item_se_start, h_item_se_end]
    have h_target_σse_in : target_σse ∈ L_triples := by
      rw [hL_triples]
      refine List.mem_map.mpr ⟨item_σse, h_item_σse_in, ?_⟩
      show (item_σse.1.startVertexIndex.val, item_σse.1.endVertexIndex.val, item_σse.2)
         = ((σ⁻¹ s).val, (σ⁻¹ e).val, item_σse.2)
      rw [h_item_σse_start, h_item_σse_end]
    have h_slice_size : (currentBetween.getD depth #[]).size = n := h_row_size depth hd_depth
    have h_target_se_outer_bound : target_se.1 < (currentBetween.getD depth #[]).size := by
      show s.val < (currentBetween.getD depth #[]).size
      rw [h_slice_size]; exact s.isLt
    have h_target_σse_outer_bound : target_σse.1 < (currentBetween.getD depth #[]).size := by
      show (σ⁻¹ s).val < (currentBetween.getD depth #[]).size
      rw [h_slice_size]; exact (σ⁻¹ s).isLt
    have h_inner_size : ((currentBetween.getD depth #[]).getD s.val #[]).size = n :=
      h_cell_size depth hd_depth s.val s.isLt
    have h_inner_size_σ : ((currentBetween.getD depth #[]).getD (σ⁻¹ s).val #[]).size = n :=
      h_cell_size depth hd_depth (σ⁻¹ s).val (σ⁻¹ s).isLt
    have h_target_se_inner_bound : target_se.2.1 < ((currentBetween.getD depth #[]).getD target_se.1 #[]).size := by
      show e.val < ((currentBetween.getD depth #[]).getD s.val #[]).size
      rw [h_inner_size]; exact e.isLt
    have h_target_σse_inner_bound : target_σse.2.1 < ((currentBetween.getD depth #[]).getD target_σse.1 #[]).size := by
      show (σ⁻¹ e).val < ((currentBetween.getD depth #[]).getD (σ⁻¹ s).val #[]).size
      rw [h_inner_size_σ]; exact (σ⁻¹ e).isLt
    -- Apply chain-at-target.
    have h_cell_se :
        Array.getD (Array.getD (List.foldl
          (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
            ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
          (currentBetween.getD depth #[]) L_triples) s.val #[]) e.val 0 = item_se.2 :=
      nested_set_chain_at_target_pair_nodup (currentBetween.getD depth #[]) L_triples target_se 0
        h_target_se_in h_nodup h_target_se_outer_bound h_target_se_inner_bound
    have h_cell_σse :
        Array.getD (Array.getD (List.foldl
          (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
            ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
          (currentBetween.getD depth #[]) L_triples) (σ⁻¹ s).val #[]) (σ⁻¹ e).val 0 = item_σse.2 :=
      nested_set_chain_at_target_pair_nodup (currentBetween.getD depth #[]) L_triples target_σse 0
        h_target_σse_in h_nodup h_target_σse_outer_bound h_target_σse_inner_bound
    show Array.getD (Array.getD (List.foldl _ (currentBetween.getD depth #[]) L_triples) s.val #[]) e.val 0
       = Array.getD (Array.getD (List.foldl _ (currentBetween.getD depth #[]) L_triples) (σ⁻¹ s).val #[]) (σ⁻¹ e).val 0
    rw [h_cell_se, h_cell_σse]
    -- Show item_se.2 = item_σse.2 via σ-closure.
    obtain ⟨item', h_item'_in, h_item'_start, h_item'_end, h_item'_rank⟩ :=
      h_σ_closure item_σse h_item_σse_in
    have h_σse_start_eq_fin : item_σse.1.startVertexIndex = σ⁻¹ s := by
      apply Fin.ext; exact h_item_σse_start
    have h_σse_end_eq_fin : item_σse.1.endVertexIndex = σ⁻¹ e := by
      apply Fin.ext; exact h_item_σse_end
    rw [h_σse_start_eq_fin] at h_item'_start
    rw [h_σse_end_eq_fin] at h_item'_end
    have h_σσ_s : σ (σ⁻¹ s) = s := by simp
    have h_σσ_e : σ (σ⁻¹ e) = e := by simp
    rw [h_σσ_s] at h_item'_start
    rw [h_σσ_e] at h_item'_end
    -- (item'.1.start.val, item'.1.end.val) = (s.val, e.val).
    have h_item'_pair_in : (item'.1.startVertexIndex.val, item'.1.endVertexIndex.val, item'.2) ∈ L_triples := by
      rw [hL_triples]
      exact List.mem_map.mpr ⟨item', h_item'_in, rfl⟩
    rw [h_item'_start, h_item'_end] at h_item'_pair_in
    -- Both (s.val, e.val, item'.2) and (s.val, e.val, item_se.2) are in L_triples.
    -- By Nodup of (s, e) pairs, ranks must be equal.
    have h_unique_v : ∀ (L : List (Nat × Nat × Nat)) (s' e' v₁ v₂ : Nat),
        (L.map (fun item => (item.1, item.2.1))).Nodup →
        (s', e', v₁) ∈ L → (s', e', v₂) ∈ L → v₁ = v₂ := by
      intro L s' e' v₁ v₂ hND h1 h2
      induction L with
      | nil => exact absurd h1 (List.not_mem_nil)
      | cons hd tl ih =>
        simp only [List.map_cons, List.nodup_cons] at hND
        obtain ⟨h_hd_not_in, h_tl_nd⟩ := hND
        rcases List.mem_cons.mp h1 with h1 | h1
        · rcases List.mem_cons.mp h2 with h2 | h2
          · have heq : (Prod.mk s' (Prod.mk e' v₁)) = (s', e', v₂) := h1.trans h2.symm
            have := (Prod.mk.injEq _ _ _ _).mp heq |>.2
            exact (Prod.mk.injEq _ _ _ _).mp this |>.2
          · have h_hd_eq : (hd.1, hd.2.1) = (s', e') := by rw [← h1]
            have : (s', e') ∈ tl.map (fun item => (item.1, item.2.1)) :=
              List.mem_map.mpr ⟨(s', e', v₂), h2, rfl⟩
            exact absurd this (h_hd_eq ▸ h_hd_not_in)
        · rcases List.mem_cons.mp h2 with h2 | h2
          · have h_hd_eq : (hd.1, hd.2.1) = (s', e') := by rw [← h2]
            have : (s', e') ∈ tl.map (fun item => (item.1, item.2.1)) :=
              List.mem_map.mpr ⟨(s', e', v₁), h1, rfl⟩
            exact absurd this (h_hd_eq ▸ h_hd_not_in)
          · exact ih h_tl_nd h1 h2
    have h_target_se_eq : target_se = (s.val, e.val, item_se.2) := rfl
    rw [h_target_se_eq] at h_target_se_in
    have h_v_eq : item_se.2 = item'.2 :=
      h_unique_v L_triples s.val e.val item_se.2 item'.2 h_nodup h_target_se_in h_item'_pair_in
    rw [h_v_eq, h_item'_rank]
  · -- d ≠ depth: use setBetween_fold_other_depth_unchanged.
    have h_dep_ne_d : depth ≠ d := fun h => h_eq h.symm
    have h_lhs : (assignList.foldl chainFn currentBetween).getD d #[] = currentBetween.getD d #[] :=
      setBetween_fold_other_depth_unchanged assignList currentBetween depth d h_dep_ne_d
    rw [h_lhs]
    exact h_curr_inv d hd s e


end Graph
