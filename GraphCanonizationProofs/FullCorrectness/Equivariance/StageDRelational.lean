import FullCorrectness.Equivariance.ConvergeLoopRelational
import FullCorrectness.Equivariance.LabelEdgesCharacterization
import FullCorrectness.Equivariance.RankStateInvariants
import Mathlib.Data.List.GetD

/-!
# Phase 3 — Stage D-rel: `labelEdgesAccordingToRankings` τ-equivariance under tie-freeness
  (`FullCorrectness.Equivariance.StageDRelational`)

The relational lift of Stage D specialized to all-distinct ranks (the post-`orderVertices`
invariant from §7). Statement:

  τ ∈ Aut G  ∧  rks₁, rks₂ τ-related (rks₂[w] = rks₁[τ⁻¹ w])  ∧  rks₁, rks₂ tie-free
  ⟹  labelEdgesAccordingToRankings rks₂ G = labelEdgesAccordingToRankings rks₁ G

## Why tie-freeness matters

`computeDenseRanks` uses `(rank, vertex-index)` lex order. Under τ-relabeling of the
rks array, the secondary `vertex-index` key gets τ-permuted, and in general the
canonical position assignment is no longer τ-equivariant. Tie-freeness collapses the
secondary key (no ties to break), so dense ranks are determined by primary rank alone,
and hence are τ-related cleanly.

## Proof structure

  1. **Phase 3.D** (`computeDenseRanks_perm_when_tieFree`): denseRanks values cover {0..n-1}.
  2. **Phase 3.C** (`computeDenseRanks_τ_shift_distinct`): under tie-freeness, denseRanks
     τ-shifts: `(computeDenseRanks rks₂)[w] = (computeDenseRanks rks₁)[τ⁻¹ w]`.
  3. **Phase 3.E** (`labelEdges_VtsInvariant_eq_distinct`): assemble using
     `labelEdges_fold_strong` and `labelEdges_terminal_rankMap_identity` from
     `LabelEdgesCharacterization`, plus 3.C and 3.D.
-/

namespace Graph

variable {n : Nat}

/-! ### Tie-freeness predicate -/

/-- A typing array has all-distinct values up to size n. This is the post-`orderVertices`
invariant from §7 (`orderVertices_n_distinct_ranks`). -/
def TieFree (rks : Array VertexType) (n : Nat) : Prop :=
  ∀ i j : Fin n, rks.getD i.val 0 = rks.getD j.val 0 → i = j

/-- τ-related tie-free arrays: their dense ranks (and hence the canonical sort order)
shift uniformly by τ. This is the relational form used by Stage D-rel. -/
private def τRelatedRks (τ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType) : Prop :=
  ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0

/-! ### Cmp on `(VertexType × Nat)`: lex on (primary rank, vertex-index) -/

/-- The comparison used by `computeDenseRanks`: lex on (primary rank, vertex-index). -/
private def pairCmp : (VertexType × Nat) → (VertexType × Nat) → Ordering :=
  fun pair1 pair2 => if pair1.1 != pair2.1 then compare pair1.1 pair2.1 else compare pair1.2 pair2.2

/-- `pairCmp` total preorder properties (used to invoke sortBy_pairwise/sortBy_eq_of_perm_strict). -/
private theorem pairCmp_refl (a : VertexType × Nat) : pairCmp a a = Ordering.eq := by
  unfold pairCmp
  simp

/-- Local helper: `pairCmp` evaluated when first components differ. -/
private theorem pairCmp_eval_ne_fst (a b : VertexType × Nat) (h_ne : a.1 ≠ b.1) :
    pairCmp a b = compare a.1 b.1 := by
  unfold pairCmp
  simp [h_ne, bne]

/-- Local helper: `pairCmp` evaluated when first components are equal. -/
private theorem pairCmp_eval_eq_fst (a b : VertexType × Nat) (h_eq : a.1 = b.1) :
    pairCmp a b = compare a.2 b.2 := by
  unfold pairCmp
  simp [h_eq, bne]

/-- `pairCmp a b ≠ .gt` is equivalent to lex order (a ≤ b). -/
private theorem pairCmp_le_iff (a b : VertexType × Nat) :
    pairCmp a b ≠ Ordering.gt ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  by_cases h_eq : a.1 = b.1
  · rw [pairCmp_eval_eq_fst a b h_eq]
    constructor
    · intro h
      right; refine ⟨h_eq, ?_⟩
      rcases Nat.lt_trichotomy a.2 b.2 with h₂ | h₂ | h₂
      · exact Nat.le_of_lt h₂
      · exact h₂.le
      · exact (h (Nat.compare_eq_gt.mpr h₂)).elim
    · rintro (h_lt | ⟨_, h_le⟩)
      · exact (Nat.lt_irrefl _ (h_eq ▸ h_lt)).elim
      · intro h_gt
        have h_a2_gt : a.2 > b.2 := Nat.compare_eq_gt.mp h_gt
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_a2_gt h_le)
  · rw [pairCmp_eval_ne_fst a b h_eq]
    constructor
    · intro h
      left
      rcases Nat.lt_trichotomy a.1 b.1 with h₁ | h₁ | h₁
      · exact h₁
      · exact (h_eq h₁).elim
      · exact (h (Nat.compare_eq_gt.mpr h₁)).elim
    · rintro (h_lt | ⟨h_e, _⟩)
      · intro h_gt
        have : a.1 > b.1 := Nat.compare_eq_gt.mp h_gt
        exact Nat.lt_irrefl _ (Nat.lt_trans h_lt this)
      · exact (h_eq h_e).elim

/-- `pairCmp a b = .gt` is equivalent to strict lex order (a > b). -/
private theorem pairCmp_gt_iff (a b : VertexType × Nat) :
    pairCmp a b = Ordering.gt ↔ a.1 > b.1 ∨ (a.1 = b.1 ∧ a.2 > b.2) := by
  by_cases h_eq : a.1 = b.1
  · rw [pairCmp_eval_eq_fst a b h_eq]
    constructor
    · intro h; right; exact ⟨h_eq, Nat.compare_eq_gt.mp h⟩
    · rintro (h_lt | ⟨_, h_gt⟩)
      · exact (Nat.lt_irrefl _ (h_eq ▸ h_lt)).elim
      · exact Nat.compare_eq_gt.mpr h_gt
  · rw [pairCmp_eval_ne_fst a b h_eq]
    constructor
    · intro h; left; exact Nat.compare_eq_gt.mp h
    · rintro (h_lt | ⟨h_e, _⟩)
      · exact Nat.compare_eq_gt.mpr h_lt
      · exact (h_eq h_e).elim

private theorem pairCmp_antisym₁ (a b : VertexType × Nat)
    (h : pairCmp a b = Ordering.lt) : pairCmp b a = Ordering.gt := by
  rw [pairCmp_gt_iff]
  by_cases h_eq : a.1 = b.1
  · rw [pairCmp_eval_eq_fst a b h_eq] at h
    have h_a2_lt : a.2 < b.2 := Nat.compare_eq_lt.mp h
    right; exact ⟨h_eq.symm, h_a2_lt⟩
  · rw [pairCmp_eval_ne_fst a b h_eq] at h
    have h_a1_lt : a.1 < b.1 := Nat.compare_eq_lt.mp h
    left; exact h_a1_lt

private theorem pairCmp_antisym₂ (a b : VertexType × Nat)
    (h : pairCmp a b = Ordering.gt) : pairCmp b a = Ordering.lt := by
  rcases (pairCmp_gt_iff a b).mp h with h_lt | ⟨h_e, h_gt⟩
  · have h_ne : b.1 ≠ a.1 := Nat.ne_of_lt h_lt
    rw [pairCmp_eval_ne_fst b a h_ne]
    exact Nat.compare_eq_lt.mpr h_lt
  · have h_e' : b.1 = a.1 := h_e.symm
    rw [pairCmp_eval_eq_fst b a h_e']
    exact Nat.compare_eq_lt.mpr h_gt

private theorem pairCmp_trans (a b c : VertexType × Nat)
    (hab : pairCmp a b ≠ Ordering.gt) (hbc : pairCmp b c ≠ Ordering.gt) :
    pairCmp a c ≠ Ordering.gt := by
  rw [pairCmp_le_iff] at hab hbc
  rw [pairCmp_le_iff]
  rcases hab with h_ab | ⟨h_ab_e, h_ab_le⟩
  · rcases hbc with h_bc | ⟨h_bc_e, h_bc_le⟩
    · -- a.1 < b.1, b.1 < c.1: a.1 < c.1.
      left; exact Nat.lt_trans h_ab h_bc
    · -- a.1 < b.1, b.1 = c.1: a.1 < c.1.
      left; rw [← h_bc_e]; exact h_ab
  · rcases hbc with h_bc | ⟨h_bc_e, h_bc_le⟩
    · -- a.1 = b.1, b.1 < c.1: a.1 < c.1.
      left; rw [h_ab_e]; exact h_bc
    · -- a.1 = b.1 = c.1, a.2 ≤ b.2, b.2 ≤ c.2.
      right
      exact ⟨h_ab_e.trans h_bc_e, Nat.le_trans h_ab_le h_bc_le⟩

/-- `pairCmp` is strict on pairs with distinct values: `a ≠ b → pairCmp a b ≠ .eq`. -/
private theorem pairCmp_strict (a b : VertexType × Nat) (h_ne : a ≠ b) :
    pairCmp a b ≠ Ordering.eq := by
  intro h_eq
  by_cases hf : a.1 = b.1
  · rw [pairCmp_eval_eq_fst a b hf] at h_eq
    have h_snd : a.2 = b.2 := Nat.compare_eq_eq.mp h_eq
    exact h_ne (Prod.ext hf h_snd)
  · rw [pairCmp_eval_ne_fst a b hf] at h_eq
    exact hf (Nat.compare_eq_eq.mp h_eq)

/-! ### Properties of the `pairs` list and its `sortBy` -/

/-- The pairs list used by `computeDenseRanks`. -/
private def pairsOf (n : Nat) (rks : Array VertexType) : List (VertexType × Nat) :=
  (List.range n).map (fun i => (rks.getD i 0, i))

private theorem pairsOf_length (n : Nat) (rks : Array VertexType) :
    (pairsOf n rks).length = n := by
  unfold pairsOf
  rw [List.length_map, List.length_range]

private theorem pairsOf_seconds (n : Nat) (rks : Array VertexType) :
    (pairsOf n rks).map (·.2) = List.range n := by
  unfold pairsOf
  rw [List.map_map]
  -- ((·.2) ∘ (fun i => (rks.getD i 0, i))) i = i, so the composed map is identity on range n.
  show List.map ((fun p : VertexType × Nat => p.2) ∘ fun i => (rks.getD i 0, i)) (List.range n) = List.range n
  conv_lhs =>
    arg 1
    ext i
    rw [show ((fun p : VertexType × Nat => p.2) ∘ fun i => (rks.getD i 0, i)) i = i from rfl]
  exact List.map_id _

/-- The sorted list `sortBy pairCmp (pairsOf n rks)` has length `n`. -/
private theorem sortedPairs_length (n : Nat) (rks : Array VertexType) :
    (sortBy pairCmp (pairsOf n rks)).length = n := by
  rw [(sortBy_perm pairCmp _).length_eq]
  exact pairsOf_length n rks

/-- Sorted pairs second components form a Perm of `List.range n`. -/
private theorem sortedPairs_seconds_perm (n : Nat) (rks : Array VertexType) :
    ((sortBy pairCmp (pairsOf n rks)).map (·.2)).Perm (List.range n) := by
  have h_perm : (sortBy pairCmp (pairsOf n rks)).Perm (pairsOf n rks) := sortBy_perm _ _
  have h_perm_map := h_perm.map (·.2)
  rw [pairsOf_seconds] at h_perm_map
  exact h_perm_map

/-- Sorted pairs second components are Nodup. -/
private theorem sortedPairs_seconds_nodup (n : Nat) (rks : Array VertexType) :
    ((sortBy pairCmp (pairsOf n rks)).map (·.2)).Nodup :=
  (sortedPairs_seconds_perm n rks).nodup_iff.mpr List.nodup_range

/-! ### Cell-wise lookup formula

The key reduction: `(computeDenseRanks rks).getD v 0` equals the position `pos` such that
`sorted[pos].2 = v`, when v < n. -/

/-- The set-chain target indices form a Nodup list: when written as
`sorted.map (·.2)` we have a permutation of `[0, n)`. -/
private theorem L_pairs_nodup_aux (n : Nat) (rks : Array VertexType) :
    ((((sortBy pairCmp (pairsOf n rks)).zipIdx).map
        (fun (pp : (VertexType × Nat) × Nat) => (pp.1.2, pp.2))).map
      (fun (p : Nat × Nat) => p.1)).Nodup := by
  rw [List.map_map]
  -- Goal: (sortBy ... .zipIdx.map ((·.1) ∘ (pp ↦ (pp.1.2, pp.2)))).Nodup. The composition is (pp ↦ pp.1.2).
  show ((sortBy pairCmp (pairsOf n rks)).zipIdx.map
        (fun pp : (VertexType × Nat) × Nat => pp.1.2)).Nodup
  -- (·.1.2) = (·.2) ∘ (·.1), so the map = sorted.zipIdx.map (·.1) |>.map (·.2) = sorted.map (·.2).
  rw [show (fun pp : (VertexType × Nat) × Nat => pp.1.2)
        = (fun p : VertexType × Nat => p.2) ∘ (fun p : (VertexType × Nat) × Nat => p.1) from rfl,
      ← List.map_map]
  rw [show (sortBy pairCmp (pairsOf n rks)).zipIdx.map (fun p : (VertexType × Nat) × Nat => p.1)
        = sortBy pairCmp (pairsOf n rks) by
        apply List.ext_getElem
        · rw [List.length_map, List.length_zipIdx]
        · intro i h₁ _
          rw [List.length_map, List.length_zipIdx] at h₁
          rw [List.getElem_map, List.getElem_zipIdx]]
  exact sortedPairs_seconds_nodup n rks

/-- Reformulation of `computeDenseRanks` as a `set!`-chain over a `(target, value)` pair list
built from `sorted.zipIdx`. -/
private theorem computeDenseRanks_eq_zipIdx_setChain (n : Nat) (rks : Array VertexType) :
    let sorted := sortBy pairCmp (pairsOf n rks)
    let L_pairs : List (Nat × Nat) :=
      sorted.zipIdx.map (fun pp => (pp.1.2, pp.2))
    let init : Array Nat := (Array.range n).map (fun _ => 0)
    computeDenseRanks n rks
      = L_pairs.foldl (fun (a : Array Nat) item => a.set! item.1 item.2) init := by
  show computeDenseRanks n rks = _
  unfold computeDenseRanks
  show (List.foldl
        (fun positionArray sortedIdx =>
          positionArray.set! ((sortBy pairCmp (pairsOf n rks)).getD sortedIdx (0, 0)).2 sortedIdx)
        ((Array.range n).map fun _ => 0)
        (List.range (sortBy pairCmp (pairsOf n rks)).length)) = _
  -- Convert outer foldl to use sorted.zipIdx via bijection: sortedIdx index ↔ (entry, sortedIdx).
  -- Note: sorted.zipIdx pairs each element with its index.
  show List.foldl
        (fun (positionArray : Array Nat) sortedIdx =>
          positionArray.set! ((sortBy pairCmp (pairsOf n rks)).getD sortedIdx (0, 0)).2 sortedIdx)
        ((Array.range n).map fun _ => 0)
        (List.range (sortBy pairCmp (pairsOf n rks)).length)
      = ((sortBy pairCmp (pairsOf n rks)).zipIdx.map (fun pp => (pp.1.2, pp.2))).foldl
          (fun (a : Array Nat) item => a.set! item.1 item.2)
          ((Array.range n).map fun _ => 0)
  -- Use foldl_pointwise_eq via index correspondence:
  -- LHS: foldl over List.range L.length with body (a, k) ↦ a.set! sorted.getD[k].2 k.
  -- RHS: foldl over (sorted.zipIdx).map (fun pp => (pp.1.2, pp.2)) with body (a, item) ↦ a.set! item.1 item.2.
  -- They match position-wise: for k < L.length, (sorted.zipIdx)[k] = (sorted[k], k), so map gives (sorted[k].2, k).
  -- And foldl on .map f = foldl on body composed with f.
  set sorted := sortBy pairCmp (pairsOf n rks) with h_sorted_def
  -- (sorted.zipIdx).map (fun pp => (pp.1.2, pp.2)) = (List.range sorted.length).map (fun k => (sorted.getD k (0,0)).2, k))
  -- by zipIdx_eq_zip_range_length and explicit calc.
  rw [show sorted.zipIdx.map (fun pp => (pp.1.2, pp.2))
        = (List.range sorted.length).map (fun k => ((sorted.getD k (0,0)).2, k)) from by
    apply List.ext_getElem
    · rw [List.length_map, List.length_zipIdx, List.length_map, List.length_range]
    · intro i h₁ h₂
      rw [List.length_map, List.length_zipIdx] at h₁
      rw [List.length_map, List.length_range] at h₂
      rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, List.getElem_range]
      simp only []
      show ((sorted[i]'h₁).2, 0 + i) = ((sorted.getD i (0, 0)).2, i)
      rw [Nat.zero_add, List.getD_eq_getElem _ _ h₁]]
  rw [List.foldl_map]

/-- **Per-position lookup**: `(computeDenseRanks rks).getD v 0 = pos` whenever `pos < n`,
`v < n`, and the sorted pair at position `pos` has second component `v`. -/
private theorem computeDenseRanks_getD_at_pos (n : Nat) (rks : Array VertexType)
    (v pos : Nat) (h_v_lt : v < n)
    (h_pos_lt_sorted : pos < (sortBy pairCmp (pairsOf n rks)).length)
    (h_eq : ((sortBy pairCmp (pairsOf n rks))[pos]'h_pos_lt_sorted).2 = v) :
    (computeDenseRanks n rks).getD v 0 = pos := by
  rw [computeDenseRanks_eq_zipIdx_setChain n rks]
  -- Apply array_set_chain_at_target_nodup with target = (v, pos).
  have h_nodup := L_pairs_nodup_aux n rks
  set sorted := sortBy pairCmp (pairsOf n rks) with h_sorted_def
  set L_pairs : List (Nat × Nat) :=
    sorted.zipIdx.map (fun pp => (pp.1.2, pp.2)) with h_L_pairs_def
  -- target ∈ L_pairs.
  have h_target_in : (v, pos) ∈ L_pairs := by
    rw [h_L_pairs_def]
    apply List.mem_map.mpr
    refine ⟨(sorted[pos]'h_pos_lt_sorted, pos), ?_, ?_⟩
    · -- (sorted[pos], pos) ∈ sorted.zipIdx.
      rw [List.mem_iff_getElem]
      refine ⟨pos, ?_, ?_⟩
      · rw [List.length_zipIdx]; exact h_pos_lt_sorted
      · rw [List.getElem_zipIdx]
        show (sorted[pos]'h_pos_lt_sorted, 0 + pos) = _
        rw [Nat.zero_add]
    · show ((sorted[pos]'h_pos_lt_sorted).2, pos) = (v, pos)
      rw [h_eq]
  have h_target_bound : v < ((Array.range n).map (fun _ : Nat => (0 : Nat))).size := by
    rw [Array.size_map, Array.size_range]
    exact h_v_lt
  exact array_set_chain_at_target_nodup
    ((Array.range n).map (fun _ : Nat => (0 : Nat)))
    L_pairs (v, pos) 0 h_target_in h_nodup h_target_bound

/-- **Injectivity of `computeDenseRanks` on Fin n.** Independent of tie-freeness:
denseRanks is always injective because two distinct vertices have distinct sort positions. -/
private theorem computeDenseRanks_inj (rks : Array VertexType) (u₁ u₂ : Fin n)
    (h_eq : (computeDenseRanks n rks).getD u₁.val 0 = (computeDenseRanks n rks).getD u₂.val 0) :
    u₁ = u₂ := by
  have h_sorted_length : (sortBy pairCmp (pairsOf n rks)).length = n := sortedPairs_length n rks
  -- Find sort position pos₁ for u₁ where sorted[pos₁].2 = u₁.val.
  have h_u₁_in_seconds : u₁.val ∈ (sortBy pairCmp (pairsOf n rks)).map (·.2) :=
    (sortedPairs_seconds_perm n rks).mem_iff.mpr (List.mem_range.mpr u₁.isLt)
  obtain ⟨entry₁, h_e₁_in, h_e₁_eq⟩ := List.mem_map.mp h_u₁_in_seconds
  obtain ⟨pos₁, h_p₁_lt, h_p₁_eq⟩ := List.mem_iff_getElem.mp h_e₁_in
  have h_p₁_lt_n : pos₁ < n := h_sorted_length ▸ h_p₁_lt
  have h_p₁_lt_sorted : pos₁ < (sortBy pairCmp (pairsOf n rks)).length := h_p₁_lt
  -- Similarly for u₂.
  have h_u₂_in_seconds : u₂.val ∈ (sortBy pairCmp (pairsOf n rks)).map (·.2) :=
    (sortedPairs_seconds_perm n rks).mem_iff.mpr (List.mem_range.mpr u₂.isLt)
  obtain ⟨entry₂, h_e₂_in, h_e₂_eq⟩ := List.mem_map.mp h_u₂_in_seconds
  obtain ⟨pos₂, h_p₂_lt, h_p₂_eq⟩ := List.mem_iff_getElem.mp h_e₂_in
  have h_p₂_lt_n : pos₂ < n := h_sorted_length ▸ h_p₂_lt
  have h_p₂_lt_sorted : pos₂ < (sortBy pairCmp (pairsOf n rks)).length := h_p₂_lt
  -- Apply computeDenseRanks_getD_at_pos.
  have h_dr1 : (computeDenseRanks n rks).getD u₁.val 0 = pos₁ := by
    apply computeDenseRanks_getD_at_pos n rks u₁.val pos₁ u₁.isLt h_p₁_lt_sorted
    rw [h_p₁_eq]; exact h_e₁_eq
  have h_dr2 : (computeDenseRanks n rks).getD u₂.val 0 = pos₂ := by
    apply computeDenseRanks_getD_at_pos n rks u₂.val pos₂ u₂.isLt h_p₂_lt_sorted
    rw [h_p₂_eq]; exact h_e₂_eq
  -- pos₁ = pos₂.
  have h_pos_eq : pos₁ = pos₂ := by rw [← h_dr1, ← h_dr2, h_eq]
  -- entry₁ = entry₂ via getElem at equal positions.
  have h_entry_eq : entry₁ = entry₂ := by
    rw [← h_p₁_eq, ← h_p₂_eq]
    congr 1
  -- u₁.val = entry₁.2 = entry₂.2 = u₂.val.
  apply Fin.ext
  rw [← h_e₁_eq, ← h_e₂_eq, h_entry_eq]

/-! ### Stage D-rel main theorems -/

/-- **Phase 3.D** Tie-free rks ⟹ each value in {0..n-1} is achieved by some vertex's
denseRanks. Foundational helper for using `labelEdges_terminal_rankMap_identity`. -/
theorem computeDenseRanks_perm_when_tieFree
    (rks : Array VertexType) (h_size : rks.size = n) (_h_distinct : TieFree rks n) :
    ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks).getD w.val 0 = k.val := by
  intro k
  have h_sorted_length : (sortBy pairCmp (pairsOf n rks)).length = n := sortedPairs_length n rks
  have h_k_lt_sorted : k.val < (sortBy pairCmp (pairsOf n rks)).length := by
    rw [h_sorted_length]; exact k.isLt
  -- Take w := sorted[k.val].2.
  set w_val : Nat := ((sortBy pairCmp (pairsOf n rks))[k.val]'h_k_lt_sorted).2 with h_w_val_def
  have h_w_in_seconds : w_val ∈ (sortBy pairCmp (pairsOf n rks)).map (·.2) := by
    rw [h_w_val_def]
    exact List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩
  have h_w_in_range : w_val ∈ List.range n :=
    (sortedPairs_seconds_perm n rks).mem_iff.mp h_w_in_seconds
  have h_w_lt : w_val < n := List.mem_range.mp h_w_in_range
  refine ⟨⟨w_val, h_w_lt⟩, ?_⟩
  exact computeDenseRanks_getD_at_pos n rks w_val k.val h_w_lt h_k_lt_sorted h_w_val_def.symm

/-! ### Lifting τ : Fin n → Fin n to Nat for the `pairs.map (rk, j) ↦ (rk, τ j)` action -/

/-- Lift τ : Equiv.Perm (Fin n) to a function on Nat; default to identity outside [0, n). -/
private def liftToNat (τ : Equiv.Perm (Fin n)) : Nat → Nat :=
  fun j => if h : j < n then (τ ⟨j, h⟩).val else j

/-- The lifted action on pairs: applies `liftToNat τ` to the second component. -/
private def pairLift (τ : Equiv.Perm (Fin n)) : (VertexType × Nat) → (VertexType × Nat) :=
  fun p => (p.1, liftToNat τ p.2)

private theorem liftToNat_in_range (τ : Equiv.Perm (Fin n)) (j : Nat) (h : j < n) :
    liftToNat τ j = (τ ⟨j, h⟩).val := by
  unfold liftToNat; simp [h]

/-- Mapping pairs₁ via `pairLift τ` produces a list with the same multiset as pairs₂. -/
private theorem pairsOf_τ_perm (τ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType)
    (h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    ((pairsOf n rks₁).map (pairLift τ)).Perm (pairsOf n rks₂) := by
  unfold pairsOf
  rw [List.map_map]
  -- LHS: (range n).map (fun i => (rks₁.getD i 0, liftToNat τ i)).
  -- RHS: (range n).map (fun i => (rks₂.getD i 0, i)).
  -- Both have the same multiset. Use `perm_of_nodup_nodup_toFinset_eq`.
  apply List.perm_of_nodup_nodup_toFinset_eq
  · -- LHS Nodup.
    apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
    intro i hi j hj h_eq
    have h_snd : liftToNat τ i = liftToNat τ j := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h_i_lt : i < n := List.mem_range.mp hi
    have h_j_lt : j < n := List.mem_range.mp hj
    rw [liftToNat_in_range τ i h_i_lt, liftToNat_in_range τ j h_j_lt] at h_snd
    have h_τ_eq : τ ⟨i, h_i_lt⟩ = τ ⟨j, h_j_lt⟩ := Fin.ext h_snd
    have h_eq' : (⟨i, h_i_lt⟩ : Fin n) = ⟨j, h_j_lt⟩ := τ.injective h_τ_eq
    exact (Fin.mk.injEq _ _ _ _).mp h_eq'
  · -- RHS Nodup.
    apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
    intro i _ j _ h_eq
    exact (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  · -- toFinset equality.
    ext p
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · -- LHS: ∃ i < n, ((pairLift τ) ∘ ...) i = p.
      rintro ⟨i, h_i_lt, h_eq⟩
      -- Take j := liftToNat τ i.
      have hτi_lt : liftToNat τ i < n := by
        rw [liftToNat_in_range τ i h_i_lt]; exact (τ ⟨i, h_i_lt⟩).isLt
      refine ⟨liftToNat τ i, hτi_lt, ?_⟩
      have h_lift_eq : liftToNat τ i = (τ ⟨i, h_i_lt⟩).val := liftToNat_in_range τ i h_i_lt
      have h_τ_inv_apply : τ⁻¹ ⟨liftToNat τ i, hτi_lt⟩ = ⟨i, h_i_lt⟩ := by
        have h_step : (⟨liftToNat τ i, hτi_lt⟩ : Fin n) = τ ⟨i, h_i_lt⟩ := by
          apply Fin.ext
          exact h_lift_eq
        rw [h_step]
        rw [Equiv.Perm.inv_def, τ.symm_apply_apply]
      have h_rks2_eq : rks₂.getD (liftToNat τ i) 0 = rks₁.getD i 0 := by
        have := h_rel ⟨liftToNat τ i, hτi_lt⟩
        rw [this, h_τ_inv_apply]
      show ((fun i' => (rks₂.getD i' 0, i')) (liftToNat τ i)) = p
      show (rks₂.getD (liftToNat τ i) 0, liftToNat τ i) = p
      rw [h_rks2_eq]
      show (rks₁.getD i 0, liftToNat τ i) = p
      have h_eq' : (rks₁.getD i 0, liftToNat τ i) = pairLift τ (rks₁.getD i 0, i) := by
        unfold pairLift; rfl
      rw [h_eq']
      show pairLift τ (rks₁.getD i 0, i) = p
      have h_pre : ((pairLift τ ∘ fun i => (rks₁.getD i 0, i))) i = pairLift τ (rks₁.getD i 0, i) := rfl
      rw [← h_pre]
      exact h_eq
    · -- RHS: ∃ j < n, (rks₂.getD j 0, j) = p.
      rintro ⟨j, h_j_lt, h_eq⟩
      -- Take i := (τ⁻¹ ⟨j, h_j_lt⟩).val.
      have hi_lt : (τ⁻¹ ⟨j, h_j_lt⟩).val < n := (τ⁻¹ ⟨j, h_j_lt⟩).isLt
      refine ⟨(τ⁻¹ ⟨j, h_j_lt⟩).val, hi_lt, ?_⟩
      have h_τ_apply : τ (τ⁻¹ ⟨j, h_j_lt⟩) = ⟨j, h_j_lt⟩ := τ.apply_symm_apply _
      have h_lift : liftToNat τ (τ⁻¹ ⟨j, h_j_lt⟩).val = j := by
        rw [liftToNat_in_range τ _ hi_lt]
        show (τ ⟨(τ⁻¹ ⟨j, h_j_lt⟩).val, hi_lt⟩).val = j
        have h_eq' : (⟨(τ⁻¹ ⟨j, h_j_lt⟩).val, hi_lt⟩ : Fin n) = τ⁻¹ ⟨j, h_j_lt⟩ := rfl
        rw [h_eq', h_τ_apply]
      have h_rks_eq : rks₁.getD (τ⁻¹ ⟨j, h_j_lt⟩).val 0 = rks₂.getD j 0 := (h_rel ⟨j, h_j_lt⟩).symm
      show ((pairLift τ ∘ fun i' => (rks₁.getD i' 0, i')) (τ⁻¹ ⟨j, h_j_lt⟩).val) = p
      show pairLift τ (rks₁.getD (τ⁻¹ ⟨j, h_j_lt⟩).val 0, (τ⁻¹ ⟨j, h_j_lt⟩).val) = p
      unfold pairLift
      show (rks₁.getD (τ⁻¹ ⟨j, h_j_lt⟩).val 0, liftToNat τ (τ⁻¹ ⟨j, h_j_lt⟩).val) = p
      rw [h_lift, h_rks_eq]
      exact h_eq

/-- Under tie-freeness of rks₁, the cmp respects the pairLift τ map on `pairsOf n rks₁`. -/
private theorem pairCmp_resp_lift_under_tieFree
    (τ : Equiv.Perm (Fin n)) (rks₁ : Array VertexType) (h_distinct₁ : TieFree rks₁ n) :
    ∀ a ∈ pairsOf n rks₁, ∀ b ∈ pairsOf n rks₁,
      pairCmp (pairLift τ a) (pairLift τ b) = pairCmp a b := by
  intro a h_a b h_b
  unfold pairsOf at h_a h_b
  obtain ⟨i, h_i_in, h_a_eq⟩ := List.mem_map.mp h_a
  obtain ⟨j, h_j_in, h_b_eq⟩ := List.mem_map.mp h_b
  have h_i_lt : i < n := List.mem_range.mp h_i_in
  have h_j_lt : j < n := List.mem_range.mp h_j_in
  rw [← h_a_eq, ← h_b_eq]
  -- Goal: pairCmp (pairLift τ (rks₁.getD i 0, i)) (pairLift τ (rks₁.getD j 0, j))
  --       = pairCmp (rks₁.getD i 0, i) (rks₁.getD j 0, j).
  -- Both sides have the same first component for the if-condition; only second components differ.
  show pairCmp (rks₁.getD i 0, liftToNat τ i) (rks₁.getD j 0, liftToNat τ j)
       = pairCmp (rks₁.getD i 0, i) (rks₁.getD j 0, j)
  by_cases hf : rks₁.getD i 0 = rks₁.getD j 0
  · -- Same first component. By tie-freeness, i = j.
    have h_ij : (⟨i, h_i_lt⟩ : Fin n) = ⟨j, h_j_lt⟩ := h_distinct₁ ⟨i, h_i_lt⟩ ⟨j, h_j_lt⟩ hf
    have h_ij_nat : i = j := (Fin.mk.injEq _ _ _ _).mp h_ij
    subst h_ij_nat
    -- LHS = pairCmp (rk, lift i) (rk, lift i) = .eq (refl). RHS = pairCmp (rk, i) (rk, i) = .eq.
    rw [pairCmp_refl, pairCmp_refl]
  · -- Different first components.
    have h_ne : (rks₁.getD i 0, liftToNat τ i).1 ≠ (rks₁.getD j 0, liftToNat τ j).1 := hf
    have h_ne' : (rks₁.getD i 0, i).1 ≠ (rks₁.getD j 0, j).1 := hf
    rw [pairCmp_eval_ne_fst _ _ h_ne, pairCmp_eval_ne_fst _ _ h_ne']

/-- **Phase 3.C** τ-shift lemma: for τ-related tie-free rks₁, rks₂, the denseRanks
shift τ-equivariantly. -/
theorem computeDenseRanks_τ_shift_distinct
    (τ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType)
    (_h_size₁ : rks₁.size = n) (_h_size₂ : rks₂.size = n)
    (h_distinct₁ : TieFree rks₁ n) (_h_distinct₂ : TieFree rks₂ n)
    (h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (computeDenseRanks n rks₂).getD w.val 0 = (computeDenseRanks n rks₁).getD (τ⁻¹ w).val 0 := by
  intro w
  -- Step 1: sortBy pairCmp pairs₂ = (sortBy pairCmp pairs₁).map (pairLift τ).
  have h_sortBy_eq_pairs2 : sortBy pairCmp (pairsOf n rks₂)
      = (sortBy pairCmp (pairsOf n rks₁)).map (pairLift τ) := by
    have h_resp := pairCmp_resp_lift_under_tieFree τ rks₁ h_distinct₁
    have h_sortBy_map :
        sortBy pairCmp ((pairsOf n rks₁).map (pairLift τ))
          = (sortBy pairCmp (pairsOf n rks₁)).map (pairLift τ) :=
      sortBy_map_pointwise_relational (pairLift τ) pairCmp pairCmp (pairsOf n rks₁) h_resp
    have h_perm := pairsOf_τ_perm τ rks₁ rks₂ h_rel
    have h_strict : ∀ a ∈ pairsOf n rks₂, ∀ b ∈ pairsOf n rks₂, a ≠ b → pairCmp a b ≠ Ordering.eq :=
      fun a _ b _ h_ne => pairCmp_strict a b h_ne
    have h_sortBy_eq : sortBy pairCmp (pairsOf n rks₂) = sortBy pairCmp ((pairsOf n rks₁).map (pairLift τ)) :=
      sortBy_eq_of_perm_strict pairCmp pairCmp_antisym₁ pairCmp_antisym₂ pairCmp_trans
        h_perm.symm h_strict
    exact h_sortBy_eq.trans h_sortBy_map
  -- Step 2: identify denseRanks output via cell-wise lookup formula.
  have h_τinv_w_lt : (τ⁻¹ w).val < n := (τ⁻¹ w).isLt
  have h_w_lt : w.val < n := w.isLt
  have h_sorted₁_length : (sortBy pairCmp (pairsOf n rks₁)).length = n := sortedPairs_length n rks₁
  have h_sorted₂_length : (sortBy pairCmp (pairsOf n rks₂)).length = n := sortedPairs_length n rks₂
  -- Find pos in sorted₁ where (·.2) = (τ⁻¹ w).val.
  have h_τinv_w_in : (τ⁻¹ w).val ∈ (sortBy pairCmp (pairsOf n rks₁)).map (·.2) := by
    rw [(sortedPairs_seconds_perm n rks₁).mem_iff]
    exact List.mem_range.mpr h_τinv_w_lt
  obtain ⟨entry₁, h_entry₁_in, h_entry₁_snd⟩ := List.mem_map.mp h_τinv_w_in
  obtain ⟨pos, h_pos_lt, h_pos_eq⟩ := List.mem_iff_getElem.mp h_entry₁_in
  -- pos < n and pos < sorted_i.length for both.
  have h_pos_lt_sorted₁ : pos < (sortBy pairCmp (pairsOf n rks₁)).length := h_pos_lt
  have h_pos_lt_n : pos < n := by rw [← h_sorted₁_length]; exact h_pos_lt_sorted₁
  have h_pos_lt_sorted₂ : pos < (sortBy pairCmp (pairsOf n rks₂)).length := by
    rw [h_sorted₂_length]; exact h_pos_lt_n
  -- (computeDenseRanks rks₁)[(τ⁻¹ w).val] = pos.
  have h_dr1 : (computeDenseRanks n rks₁).getD (τ⁻¹ w).val 0 = pos := by
    apply computeDenseRanks_getD_at_pos n rks₁ (τ⁻¹ w).val pos h_τinv_w_lt h_pos_lt_sorted₁
    rw [h_pos_eq]; exact h_entry₁_snd
  -- (computeDenseRanks rks₂)[w.val] = pos as well.
  have h_dr2 : (computeDenseRanks n rks₂).getD w.val 0 = pos := by
    apply computeDenseRanks_getD_at_pos n rks₂ w.val pos h_w_lt h_pos_lt_sorted₂
    -- (sortBy pairCmp pairs₂)[pos] = (sortBy pairCmp pairs₁).map (pairLift τ))[pos]
    --                              = pairLift τ ((sortBy pairCmp pairs₁)[pos]).
    -- Then read .2 to get liftToNat τ entry₁.2 = liftToNat τ (τ⁻¹ w).val = w.val.
    have h_sorted₂_at_pos :
        (sortBy pairCmp (pairsOf n rks₂))[pos]'h_pos_lt_sorted₂
          = pairLift τ entry₁ := by
      -- Use heterogeneous index transport via h_sortBy_eq_pairs2.
      have h_pos_lt_mapped : pos < ((sortBy pairCmp (pairsOf n rks₁)).map (pairLift τ)).length := by
        rw [List.length_map]; exact h_pos_lt_sorted₁
      have h_eq_sorted : (sortBy pairCmp (pairsOf n rks₂))[pos]'h_pos_lt_sorted₂
            = ((sortBy pairCmp (pairsOf n rks₁)).map (pairLift τ))[pos]'h_pos_lt_mapped := by
        congr! 1
      rw [h_eq_sorted, List.getElem_map, h_pos_eq]
    rw [h_sorted₂_at_pos]
    show liftToNat τ entry₁.2 = w.val
    rw [h_entry₁_snd]
    rw [liftToNat_in_range τ (τ⁻¹ w).val h_τinv_w_lt]
    -- Need: (τ ⟨(τ⁻¹ w).val, h_τinv_w_lt⟩).val = w.val.
    have h_eq' : (⟨(τ⁻¹ w).val, h_τinv_w_lt⟩ : Fin n) = τ⁻¹ w := rfl
    rw [h_eq', Equiv.Perm.inv_def, τ.apply_symm_apply]
  rw [h_dr1, h_dr2]

/-! ### Stage D-rel assembly -/

/-- **Stage D-rel under tie-freeness.** Given τ ∈ Aut G and two τ-related tie-free
typing arrays `rks₁, rks₂`, `labelEdgesAccordingToRankings` produces equal canonical
matrices.

**Proof:**
  1. By `labelEdges_fold_strong` on side 1 (with σ := id, rankMap_0 := denseRanks rks₁),
     get σ_1 with output_1 = G.permute σ_1 and output_1.rankMap = denseRanks rks₁ ∘ σ_1⁻¹.
  2. Similarly on side 2 with σ := τ (using `τ ∈ Aut G ⟹ G = G.permute τ`),
     and rankMap_0 := denseRanks rks₁ (using Phase 3.C: denseRanks rks₂ = denseRanks rks₁ ∘ τ⁻¹).
     Get σ_2 with output_2 = G.permute σ_2 and output_2.rankMap = denseRanks rks₁ ∘ σ_2⁻¹.
  3. Both terminal rankMaps are identity (by `labelEdges_terminal_rankMap_identity` with Phase 3.D).
  4. So `denseRanks rks₁ ∘ σ_1⁻¹ = denseRanks rks₁ ∘ σ_2⁻¹` pointwise.
  5. By tie-freeness (injectivity of denseRanks rks₁), σ_1 = σ_2.
  6. Hence output_1 = output_2. ∎ -/
theorem labelEdges_VtsInvariant_eq_distinct
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ AdjMatrix.Aut G)
    (rks₁ rks₂ : Array VertexType)
    (h_size₁ : rks₁.size = n) (h_size₂ : rks₂.size = n)
    (h_distinct₁ : TieFree rks₁ n) (h_distinct₂ : TieFree rks₂ n)
    (h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    labelEdgesAccordingToRankings rks₂ G = labelEdgesAccordingToRankings rks₁ G := by
  -- Unfold both sides to expose the foldl over List.finRange n.
  show ((List.finRange n).foldl (labelEdgesStep n (List.finRange n)) (G, computeDenseRanks n rks₂)).1
       = ((List.finRange n).foldl (labelEdgesStep n (List.finRange n)) (G, computeDenseRanks n rks₁)).1
  -- Helper sizes.
  have h_dr1_size : (computeDenseRanks n rks₁).size = n := computeDenseRanks_size n rks₁
  have h_dr2_size : (computeDenseRanks n rks₂).size = n := computeDenseRanks_size n rks₂
  -- Phase 3.D: denseRanks rks₁ achieves each k ∈ Fin n.
  have h_dr1_perm : ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks₁).getD w.val 0 = k.val :=
    computeDenseRanks_perm_when_tieFree rks₁ h_size₁ h_distinct₁
  -- Phase 3.D for rks₂.
  have h_dr2_perm : ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks₂).getD w.val 0 = k.val :=
    computeDenseRanks_perm_when_tieFree rks₂ h_size₂ h_distinct₂
  -- Phase 3.C: denseRanks rks₂ shifts τ-equivariantly.
  have h_dr_shift : ∀ w : Fin n,
      (computeDenseRanks n rks₂).getD w.val 0 = (computeDenseRanks n rks₁).getD (τ⁻¹ w).val 0 :=
    computeDenseRanks_τ_shift_distinct τ rks₁ rks₂ h_size₁ h_size₂ h_distinct₁ h_distinct₂ h_rel
  -- τ ∈ Aut G ⟹ G.permute τ = G.
  have hG_τ : G.permute τ = G := hτ
  -- Side 1: apply labelEdges_fold_strong with σ := 1 (identity).
  obtain ⟨σ_1, h_out1_graph, h_out1_size, h_out1_rankMap⟩ :=
    labelEdges_fold_strong G (computeDenseRanks n rks₁) h_dr1_size (List.finRange n)
      (G, computeDenseRanks n rks₁) (1 : Equiv.Perm (Fin n))
      (by show G = G.permute 1; rw [AdjMatrix.permute_one])
      h_dr1_size
      (fun v => by show _ = _; rfl)
  -- Side 2: apply labelEdges_fold_strong with σ := τ, rankMap_0 := denseRanks rks₁.
  obtain ⟨σ_2, h_out2_graph, h_out2_size, h_out2_rankMap⟩ :=
    labelEdges_fold_strong G (computeDenseRanks n rks₁) h_dr1_size (List.finRange n)
      (G, computeDenseRanks n rks₂) τ
      (by show G = G.permute τ; rw [hG_τ])
      h_dr2_size
      h_dr_shift
  -- Apply terminal_rankMap_identity to both sides, with rankMap_0 = denseRanks rks_i.
  -- For side 1, multiset = h_dr1_perm (rks₁).
  have h_term1 : ∀ v : Fin n,
      ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
        (G, computeDenseRanks n rks₁)).2.getD v.val 0 = v.val :=
    labelEdges_terminal_rankMap_identity G (computeDenseRanks n rks₁) h_dr1_size h_dr1_perm
  have h_term2 : ∀ v : Fin n,
      ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
        (G, computeDenseRanks n rks₂)).2.getD v.val 0 = v.val :=
    labelEdges_terminal_rankMap_identity G (computeDenseRanks n rks₂) h_dr2_size h_dr2_perm
  -- Combine: denseRanks rks₁ ∘ σ_1⁻¹ = denseRanks rks₁ ∘ σ_2⁻¹ pointwise.
  have h_combined : ∀ v : Fin n,
      (computeDenseRanks n rks₁).getD (σ_1⁻¹ v).val 0
        = (computeDenseRanks n rks₁).getD (σ_2⁻¹ v).val 0 := by
    intro v
    rw [← h_out1_rankMap v, h_term1 v, ← h_term2 v, h_out2_rankMap v]
  -- By injectivity of denseRanks rks₁ (computeDenseRanks_inj), σ_1⁻¹ v = σ_2⁻¹ v.
  have h_inv_eq : ∀ v : Fin n, σ_1⁻¹ v = σ_2⁻¹ v := fun v =>
    computeDenseRanks_inj rks₁ (σ_1⁻¹ v) (σ_2⁻¹ v) (h_combined v)
  -- Hence σ_1 = σ_2.
  have h_σ_eq : σ_1 = σ_2 := by
    have h_inv_eq' : σ_1⁻¹ = σ_2⁻¹ := Equiv.ext h_inv_eq
    -- σ_1 = (σ_1⁻¹)⁻¹ = (σ_2⁻¹)⁻¹ = σ_2.
    have := congrArg (·⁻¹) h_inv_eq'
    simp at this
    exact this
  -- Conclude: output_1.1 = G.permute σ_1 = G.permute σ_2 = output_2.1.
  rw [h_out2_graph, h_out1_graph, h_σ_eq]

/-! ### Stage D-rel general σ (no Aut hypothesis)

Generalization of `labelEdges_VtsInvariant_eq_distinct` (Phase 3.E) that drops the
`τ ∈ Aut G` hypothesis. Compares `labelEdgesAccordingToRankings` on **two different
graphs** `G` and `G.permute σ`, with `σ`-related rks. The proof is structurally
identical to Phase 3.E, except we don't need to collapse `G.permute σ = G`.

Used by Phase 6 (`Main.lean::run_swap_invariant_fwd`) for the σ ∉ Aut G branch. -/
theorem labelEdges_two_graphs_σ_related
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType)
    (h_size₁ : rks₁.size = n) (h_size₂ : rks₂.size = n)
    (h_distinct₁ : TieFree rks₁ n) (h_distinct₂ : TieFree rks₂ n)
    (h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (σ⁻¹ w).val 0) :
    labelEdgesAccordingToRankings rks₂ (G.permute σ) = labelEdgesAccordingToRankings rks₁ G := by
  show ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
          (G.permute σ, computeDenseRanks n rks₂)).1
       = ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
          (G, computeDenseRanks n rks₁)).1
  have h_dr1_size : (computeDenseRanks n rks₁).size = n := computeDenseRanks_size n rks₁
  have h_dr2_size : (computeDenseRanks n rks₂).size = n := computeDenseRanks_size n rks₂
  have h_dr1_perm : ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks₁).getD w.val 0 = k.val :=
    computeDenseRanks_perm_when_tieFree rks₁ h_size₁ h_distinct₁
  have h_dr2_perm : ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks₂).getD w.val 0 = k.val :=
    computeDenseRanks_perm_when_tieFree rks₂ h_size₂ h_distinct₂
  have h_dr_shift : ∀ w : Fin n,
      (computeDenseRanks n rks₂).getD w.val 0 = (computeDenseRanks n rks₁).getD (σ⁻¹ w).val 0 :=
    computeDenseRanks_τ_shift_distinct σ rks₁ rks₂ h_size₁ h_size₂ h_distinct₁ h_distinct₂ h_rel
  -- Side 1: starting graph G = G.permute 1.
  obtain ⟨σ_1, h_out1_graph, h_out1_size, h_out1_rankMap⟩ :=
    labelEdges_fold_strong G (computeDenseRanks n rks₁) h_dr1_size (List.finRange n)
      (G, computeDenseRanks n rks₁) (1 : Equiv.Perm (Fin n))
      (by show G = G.permute 1; rw [AdjMatrix.permute_one])
      h_dr1_size
      (fun v => by show _ = _; rfl)
  -- Side 2: starting graph G.permute σ — this is exactly acc.1 directly, no Aut needed.
  obtain ⟨σ_2, h_out2_graph, h_out2_size, h_out2_rankMap⟩ :=
    labelEdges_fold_strong G (computeDenseRanks n rks₁) h_dr1_size (List.finRange n)
      (G.permute σ, computeDenseRanks n rks₂) σ
      (by show G.permute σ = G.permute σ; rfl)
      h_dr2_size
      h_dr_shift
  -- Both terminal rankMaps are identity.
  have h_term1 : ∀ v : Fin n,
      ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
        (G, computeDenseRanks n rks₁)).2.getD v.val 0 = v.val :=
    labelEdges_terminal_rankMap_identity G (computeDenseRanks n rks₁) h_dr1_size h_dr1_perm
  have h_term2 : ∀ v : Fin n,
      ((List.finRange n).foldl (labelEdgesStep n (List.finRange n))
        (G.permute σ, computeDenseRanks n rks₂)).2.getD v.val 0 = v.val :=
    labelEdges_terminal_rankMap_identity (G.permute σ) (computeDenseRanks n rks₂) h_dr2_size h_dr2_perm
  -- denseRanks rks₁ ∘ σ_1⁻¹ = denseRanks rks₁ ∘ σ_2⁻¹ pointwise.
  have h_combined : ∀ v : Fin n,
      (computeDenseRanks n rks₁).getD (σ_1⁻¹ v).val 0
        = (computeDenseRanks n rks₁).getD (σ_2⁻¹ v).val 0 := by
    intro v
    rw [← h_out1_rankMap v, h_term1 v, ← h_term2 v, h_out2_rankMap v]
  -- By injectivity of denseRanks rks₁, σ_1⁻¹ v = σ_2⁻¹ v.
  have h_inv_eq : ∀ v : Fin n, σ_1⁻¹ v = σ_2⁻¹ v := fun v =>
    computeDenseRanks_inj rks₁ (σ_1⁻¹ v) (σ_2⁻¹ v) (h_combined v)
  have h_σ_eq : σ_1 = σ_2 := by
    have h_inv_eq' : σ_1⁻¹ = σ_2⁻¹ := Equiv.ext h_inv_eq
    have := congrArg (·⁻¹) h_inv_eq'
    simp at this
    exact this
  -- Conclude: output_2.1 = G.permute σ_2 = G.permute σ_1 = output_1.1.
  rw [h_out2_graph, h_out1_graph, h_σ_eq]

end Graph
