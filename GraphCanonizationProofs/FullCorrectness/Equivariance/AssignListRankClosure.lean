import FullCorrectness.Equivariance.ChainSetInvariant

/-!
# σ-rank-closure of `assignList` (`FullCorrectness.Equivariance.AssignListRankClosure`)

The σ-rank-closure of the `assignList` produced by `assignRanks ∘ sortBy`: when
`pathsAtDepth` is permutation-closed under `f := PathsFrom.permute σ` (which holds
when `state` is σ-fixed), and `cmp` is σ-equivariant + identifies σ-related entries
(`comparePathsFrom_σ_self_eq`), then for each `(p, r)` in the assignList, the σ-permuted
pair `(f p, r)` is also in the list.

This module exposes:
- `comparePathSegments_σ_self_eq` / `comparePathsBetween_σ_self_eq` /
  `comparePathsFrom_σ_self_eq` — comparing an element to its σ-permuted self under
  σ-invariant `vts` and `br` returns `.eq`.
- `comparePathsFrom_total_preorder` — total-preorder properties of `comparePathsFrom`.
- `state_σ_fixed_pathsOfLength_at_σ_slot` (private) — array-level reading of
  σ-fixedness for a `PathState`.
- `from_assignList_σ_rank_closure` (private) — the from-side σ-rank-closure (used
  by `set_chain_σInvariant` in the body of `calculatePathRankings`).
- `between_assignList_σ_rank_closure` (private) — the between-side σ-rank-closure
  (used by `setBetween_chain_σInvariant`).
-/

namespace Graph

variable {n : Nat}

/-- Generic OILC "self-under-f" lemma: if `cmp x (f x) = .eq` for all `x ∈ L`, and `cmp`
respects `f` pointwise, then `orderInsensitiveListCmp cmp L (L.map f) = .eq`. -/
private theorem orderInsensitiveListCmp_self_under_f_eq {α : Type}
    (cmp : α → α → Ordering) (f : α → α) (L : List α)
    (h_resp : ∀ a ∈ L, ∀ b ∈ L, cmp (f a) (f b) = cmp a b)
    (h_eq : ∀ x ∈ L, cmp x (f x) = .eq) :
    orderInsensitiveListCmp cmp L (L.map f) = .eq := by
  unfold orderInsensitiveListCmp
  simp only [List.length_map, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [sortBy_map_pointwise f cmp L h_resp]
  -- Now: (sortBy cmp L).zip ((sortBy cmp L).map f) is a list of (a, f a).
  rw [show (sortBy cmp L).zip ((sortBy cmp L).map f)
        = (sortBy cmp L).map (fun a => (a, f a)) by
      rw [List.zip_map_right]
      apply List.ext_getElem (by simp)
      intros j h₁ h₂
      simp [List.getElem_zip, List.getElem_map]]
  rw [List.foldl_map]
  -- The foldl over `(a, f a)` pairs: each cmp a (f a) = .eq, so accumulator stays .eq.
  -- For all a ∈ sortBy cmp L: a ∈ L (since sortBy is a Perm).
  have h_eq_sorted : ∀ a ∈ sortBy cmp L, cmp a (f a) = .eq := fun a ha =>
    h_eq a ((sortBy_perm cmp L).mem_iff.mp ha)
  -- foldl with all .eq cmps preserves .eq.
  have h_foldl_eq : ∀ (M : List α), (∀ a ∈ M, cmp a (f a) = .eq) →
      M.foldl (fun currentOrder a =>
        if (currentOrder != Ordering.eq) = true then currentOrder else cmp a (f a))
        Ordering.eq = Ordering.eq := by
    intro M
    induction M with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro h_M
      rw [List.foldl_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [h_M hd List.mem_cons_self]
      apply ih
      intros a ha
      exact h_M a (List.mem_cons_of_mem _ ha)
  exact h_foldl_eq (sortBy cmp L) h_eq_sorted

/-- σ-self-equality for `comparePathSegments`: comparing a segment to its σ-permuted
self gives `.eq` under σ-invariant `vts` and `br`. -/
theorem comparePathSegments_σ_self_eq
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p : PathSegment vc) :
    comparePathSegments vts br p (PathSegment.permute σ p) = Ordering.eq := by
  cases p with
  | bottom v =>
    show compare (vts.getD v.val 0) (vts.getD (σ v).val 0) = Ordering.eq
    rw [hvts v]
    exact compare_eq_iff_eq.mpr rfl
  | inner pe pd ps pend =>
    show (let xRank := br pd ps.val pend.val
          let yRank := br pd (σ ps).val (σ pend).val
          if xRank != yRank then compare yRank xRank
          else if pe != pe then compare pe pe else .eq) = .eq
    rw [hbr pd ps pend]
    simp

/-- σ-self-equality for `comparePathsBetween`: comparing a `PathsBetween` to its
σ-permuted self gives `.eq` under σ-invariant `vts`/`br` and length normalization. -/
theorem comparePathsBetween_σ_self_eq
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p : PathsBetween vc)
    (h_len : p.depth > 0 → p.connectedSubPaths.length = vc) :
    comparePathsBetween vts br p (PathsBetween.permute σ p) = Ordering.eq := by
  match vc, σ, p, h_len with
  | 0, _, p, _ => exact p.endVertexIndex.elim0
  | k + 1, σ, p, h_len =>
    -- End-vertex types: σ-inv vts gives equality.
    show (if vts.getD p.endVertexIndex.val 0 != vts.getD (σ p.endVertexIndex).val 0 then
            compare (vts.getD p.endVertexIndex.val 0) (vts.getD (σ p.endVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 p.connectedSubPaths (PathsBetween.permute σ p).connectedSubPaths) = .eq
    rw [hvts p.endVertexIndex]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    -- OILC of p.connectedSubPaths and (PB.permute σ p).connectedSubPaths.
    -- (PB.permute σ p).connectedSubPaths is Perm of p.connectedSubPaths.map (PS.permute σ).
    have h_perm := PathsBetween_permute_connectedSubPaths_perm σ p h_len
    obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
      comparePathSegments_total_preorder (vc := k+1) vts br
    rw [orderInsensitiveListCmp_perm (comparePathSegments vts br)
          h_refl h_antisym₁ h_antisym₂ h_trans
          (comparePathSegments_equivCompat vts br) _ _ _ _ List.Perm.rfl h_perm]
    -- Now: orderInsensitiveListCmp cmp p.connectedSubPaths (p.connectedSubPaths.map (PS.permute σ)) = .eq
    apply orderInsensitiveListCmp_self_under_f_eq (comparePathSegments vts br)
      (PathSegment.permute σ) p.connectedSubPaths
    · intro a _ b _
      exact comparePathSegments_σ_equivariant σ vts hvts br hbr a b
    · intro x _
      exact comparePathSegments_σ_self_eq σ vts hvts br hbr x

/-- σ-self-equality for `comparePathsFrom`: comparing a `PathsFrom` to its σ-permuted
self gives `.eq` under σ-invariant `vts`/`br` and length normalization. -/
theorem comparePathsFrom_σ_self_eq
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p : PathsFrom vc)
    (h_len : p.pathsToVertex.length = vc)
    (h_inner_len : ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc) :
    comparePathsFrom vts br p (PathsFrom.permute σ p) = Ordering.eq := by
  match vc, σ, p, h_len, h_inner_len with
  | 0, _, p, _, _ => exact p.startVertexIndex.elim0
  | k + 1, σ, p, h_len, h_inner_len =>
    show (if vts.getD p.startVertexIndex.val 0 != vts.getD (σ p.startVertexIndex).val 0 then
            compare (vts.getD p.startVertexIndex.val 0) (vts.getD (σ p.startVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 p.pathsToVertex (PathsFrom.permute σ p).pathsToVertex) = .eq
    rw [hvts p.startVertexIndex]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have h_perm := PathsFrom_permute_pathsToVertex_perm σ p h_len
    obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
      comparePathsBetween_total_preorder (vc := k+1) vts br
    rw [orderInsensitiveListCmp_perm (comparePathsBetween vts br)
          h_refl h_antisym₁ h_antisym₂ h_trans
          (comparePathsBetween_equivCompat vts br) _ _ _ _ List.Perm.rfl h_perm]
    -- orderInsensitiveListCmp cmp p.pathsToVertex (p.pathsToVertex.map (PB.permute σ)) = .eq
    apply orderInsensitiveListCmp_self_under_f_eq (comparePathsBetween vts br)
      (PathsBetween.permute σ) p.pathsToVertex
    · intro a ha b hb
      have ha_len : a.depth > 0 → a.connectedSubPaths.length = k + 1 := h_inner_len a ha
      have hb_len : b.depth > 0 → b.connectedSubPaths.length = k + 1 := h_inner_len b hb
      exact comparePathsBetween_σ_equivariant σ vts hvts br hbr a b ha_len hb_len
    · intro x hx
      exact comparePathsBetween_σ_self_eq σ vts hvts br hbr x (h_inner_len x hx)

/-! ### σ-rank-closure of the assignList

Goal: when `pathsAtDepth` is permutation-closed under `f := PathsFrom.permute σ` (which
holds when `state` is σ-fixed), and `cmp` is σ-equivariant + identifies σ-related entries
(`comparePathsFrom_σ_self_eq`), then for each `(p, r)` in the assignList, the σ-permuted
pair `(f p, r)` is also in the list.

Proof strategy:
- `f p ∈ pathsAtDepth` (witnessed by σ-fixedness: `f p` is the entry at slot `σ p.start`).
- By `assignRanks_map_of_cmp_respect`: `assignRanks cmp (sortBy cmp (Y.map f))
  = (assignRanks cmp (sortBy cmp Y)).map (fun (x, r) => (f x, r))`.
- By `sortBy_map_pointwise`: LHS = `assignRanks cmp ((sortBy cmp Y).map f)`.
- For `Y.Perm (Y.map f)` (which σ-fixedness gives) AND assignRanks-Perm-preservation, the
  multisets of `assignList` and `assignList.map (lift f)` coincide.
- Hence `(f p, r) ∈ assignList`.

The key missing piece is **assignRanks-Perm-preservation**: `Y.Perm Y' →
assignRanks cmp (sortBy cmp Y).Perm assignRanks cmp (sortBy cmp Y')`. This holds because
sortBy outputs differ only in tie-breaking (Pairwise + Perm-equivalent), and assignRanks
gives same rank to .eq-class members.

The structural sub-lemma needed is `assignRanks_rank_eq_within_eq_class`: in a sorted list
(Pairwise non-gt), two elements with `cmp a b = .eq` get the same rank. -/

/-- For a σ-fixed `state`, slot `(σ s).val` of the depth-`depth` array equals the
σ-permuted image of slot `s.val`. This is the array-level reading of σ-fixedness. -/
theorem state_σ_fixed_pathsOfLength_at_σ_slot
    {n : Nat} (σ : Equiv.Perm (Fin n))
    (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (depth : Nat) (h_depth : depth < state.pathsOfLength.size)
    (h_inner_size : (state.pathsOfLength.getD depth #[]).size = n)
    (s : Fin n)
    (h_σs_lt : (σ s).val < (state.pathsOfLength.getD depth #[]).size)
    (h_s_lt : s.val < (state.pathsOfLength.getD depth #[]).size) :
    (state.pathsOfLength.getD depth #[])[(σ s).val]'h_σs_lt
      = PathsFrom.permute σ ((state.pathsOfLength.getD depth #[])[s.val]'h_s_lt) := by
  -- Handle n = 0 vacuously (Fin 0 is empty).
  by_cases hn : n = 0
  · subst hn; exact s.elim0
  -- For n ≥ 1, peel off n = k + 1 to unfold `PathState.permute`.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- σ-fixedness gives the map identity.
  have h_map_eq : state.pathsOfLength.map (fun pathsByStart =>
      (Array.range (k + 1)).map fun newStart =>
        PathsFrom.permute σ (pathsByStart.getD (permNat σ⁻¹ newStart)
          { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))
      = state.pathsOfLength :=
    congrArg PathState.pathsOfLength h_state_σ_fixed
  -- Helper: array equality projected at a fixed index. Avoids motive issues.
  have h_get_at : ∀ {α : Type} {M N : Array α} (h : M = N) (i : Nat)
      (h_M : i < M.size) (h_N : i < N.size), M[i]'h_M = N[i]'h_N := by
    intros _ M N h _ _ _; subst h; rfl
  -- Project h_map_eq at depth.
  have h_depth_map : depth < (state.pathsOfLength.map (fun pathsByStart =>
      (Array.range (k + 1)).map fun newStart =>
        PathsFrom.permute σ (pathsByStart.getD (permNat σ⁻¹ newStart)
          { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size := by
    rw [Array.size_map]; exact h_depth
  have h_proj := h_get_at h_map_eq depth h_depth_map h_depth
  -- (state.pathsOfLength.map f₁)[depth] = f₁ (state.pathsOfLength[depth]).
  rw [Array.getElem_map] at h_proj
  -- h_proj : f₁ (state.pathsOfLength[depth]'h_depth) = state.pathsOfLength[depth]'h_depth.
  -- Convert state.pathsOfLength[depth] to state.pathsOfLength.getD depth #[].
  have h_arr_get_elem : (state.pathsOfLength.getD depth #[])
                      = state.pathsOfLength[depth]'h_depth :=
    Array.getElem_eq_getD #[] |>.symm
  -- Substitute back: f₁ (state.pathsOfLength.getD depth #[]) = state.pathsOfLength.getD depth #[].
  rw [← h_arr_get_elem] at h_proj
  -- h_proj : f₁ arr = arr  (where arr := state.pathsOfLength.getD depth #[]).
  -- Now: goal is arr[(σ s).val]'h_σs_lt = PathsFrom.permute σ (arr[s.val]'h_s_lt).
  -- Rewrite arr ← f₁ arr using h_proj.symm at the LHS.
  set arr := state.pathsOfLength.getD depth #[] with h_arr_def
  have h_σs_lt_kp1 : (σ s).val < k + 1 := (σ s).isLt
  -- (f₁ arr).size = k+1.
  have h_f₁_arr_size : ((Array.range (k + 1)).map (fun newStart =>
      PathsFrom.permute σ (arr.getD (permNat σ⁻¹ newStart)
        { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size = k + 1 := by
    simp [Array.size_map, Array.size_range]
  have h_σs_lt_f₁ : (σ s).val < ((Array.range (k + 1)).map (fun newStart =>
      PathsFrom.permute σ (arr.getD (permNat σ⁻¹ newStart)
        { depth := 0, startVertexIndex := 0, pathsToVertex := [] }))).size := by
    rw [h_f₁_arr_size]; exact h_σs_lt_kp1
  -- Bridge arr[(σ s).val] to (f₁ arr)[(σ s).val] using h_proj.
  have h_bridge : arr[(σ s).val]'h_σs_lt
      = ((Array.range (k + 1)).map (fun newStart =>
          PathsFrom.permute σ (arr.getD (permNat σ⁻¹ newStart)
            { depth := 0, startVertexIndex := 0, pathsToVertex := [] })))[(σ s).val]'h_σs_lt_f₁ :=
    h_get_at h_proj.symm (σ s).val h_σs_lt h_σs_lt_f₁
  rw [h_bridge]
  -- (f₁ arr)[(σ s).val] = PathsFrom.permute σ (arr.getD (permNat σ⁻¹ (σ s).val) ⟨...⟩).
  rw [Array.getElem_map]
  simp only [Array.getElem_range]
  -- Goal: PathsFrom.permute σ (arr.getD (permNat σ⁻¹ (σ s).val) dflt)
  --     = PathsFrom.permute σ (arr[s.val]'h_s_lt).
  congr 1
  -- arr.getD (permNat σ⁻¹ (σ s).val) dflt = arr[s.val]'h_s_lt.
  rw [show permNat σ⁻¹ (σ s).val = s.val from by
    rw [show (σ s).val = permNat σ s.val from (permNat_fin σ s).symm,
        permNat_inv_perm s.isLt]]
  exact (Array.getElem_eq_getD
    ({ depth := 0, startVertexIndex := 0, pathsToVertex := [] } : PathsFrom (k+1))).symm

/-- comparePathsFrom satisfies the total-preorder properties. Lifted by hand from
`comparePathsBetween_total_preorder` and the now-public `orderInsensitiveListCmp_*`
helpers. -/
theorem comparePathsFrom_total_preorder
    {vc : Nat} (vts : Array VertexType) (br : Nat → Nat → Nat → Nat) :
    (∀ a : PathsFrom vc, comparePathsFrom vts br a a = Ordering.eq) ∧
    (∀ a b : PathsFrom vc, comparePathsFrom vts br a b = Ordering.lt →
                            comparePathsFrom vts br b a = Ordering.gt) ∧
    (∀ a b : PathsFrom vc, comparePathsFrom vts br a b = Ordering.gt →
                            comparePathsFrom vts br b a = Ordering.lt) ∧
    (∀ a b c : PathsFrom vc, comparePathsFrom vts br a b ≠ Ordering.gt →
                              comparePathsFrom vts br b c ≠ Ordering.gt →
                              comparePathsFrom vts br a c ≠ Ordering.gt) := by
  obtain ⟨h_pb_refl, h_pb_anti₁, h_pb_anti₂, h_pb_trans⟩ :=
    comparePathsBetween_total_preorder (vc := vc) vts br
  have h_pb_compat := comparePathsBetween_equivCompat (vc := vc) vts br
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Refl.
    intro a
    show (let xStartType := vts.getD a.startVertexIndex.val 0
          let yStartType := vts.getD a.startVertexIndex.val 0
          if xStartType != yStartType then compare xStartType yStartType
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 a.pathsToVertex a.pathsToVertex) = Ordering.eq
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact orderInsensitiveListCmp_refl _ _ (fun s _ => h_pb_refl s)
  · -- Antisym₁: .lt → .gt.
    intros a b h_lt
    show (let yStartType := vts.getD b.startVertexIndex.val 0
          let xStartType := vts.getD a.startVertexIndex.val 0
          if yStartType != xStartType then compare yStartType xStartType
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 b.pathsToVertex a.pathsToVertex) = Ordering.gt
    have h_lt' : (let xStartType := vts.getD a.startVertexIndex.val 0
                  let yStartType := vts.getD b.startVertexIndex.val 0
                  if xStartType != yStartType then compare xStartType yStartType
                  else orderInsensitiveListCmp (comparePathsBetween vts br)
                         a.pathsToVertex b.pathsToVertex) = Ordering.lt := h_lt
    by_cases h_eq : vts.getD a.startVertexIndex.val 0 = vts.getD b.startVertexIndex.val 0
    · have h_bne_xy : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.startVertexIndex.val 0)
      have h_bne_yx : (vts.getD b.startVertexIndex.val 0 != vts.getD a.startVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.startVertexIndex.val 0)
      simp only [h_bne_xy, Bool.false_eq_true, ↓reduceIte] at h_lt'
      simp only [h_bne_yx, Bool.false_eq_true, ↓reduceIte]
      exact orderInsensitiveListCmp_swap_lt _ h_pb_anti₁ h_pb_anti₂ _ _ h_lt'
    · have h_bne_xy : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_eq
      simp only [h_bne_xy, ↓reduceIte] at h_lt'
      have h_xy_lt : (vts.getD a.startVertexIndex.val 0 : Nat) < vts.getD b.startVertexIndex.val 0 :=
        Nat.compare_eq_lt.mp h_lt'
      have h_yx_ne : vts.getD b.startVertexIndex.val 0 ≠ vts.getD a.startVertexIndex.val 0 := Ne.symm h_eq
      have h_bne_yx : (vts.getD b.startVertexIndex.val 0 != vts.getD a.startVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_yx_ne
      simp only [h_bne_yx, ↓reduceIte]
      exact Nat.compare_eq_gt.mpr h_xy_lt
  · -- Antisym₂: .gt → .lt.
    intros a b h_gt
    show (let yStartType := vts.getD b.startVertexIndex.val 0
          let xStartType := vts.getD a.startVertexIndex.val 0
          if yStartType != xStartType then compare yStartType xStartType
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 b.pathsToVertex a.pathsToVertex) = Ordering.lt
    have h_gt' : (let xStartType := vts.getD a.startVertexIndex.val 0
                  let yStartType := vts.getD b.startVertexIndex.val 0
                  if xStartType != yStartType then compare xStartType yStartType
                  else orderInsensitiveListCmp (comparePathsBetween vts br)
                         a.pathsToVertex b.pathsToVertex) = Ordering.gt := h_gt
    by_cases h_eq : vts.getD a.startVertexIndex.val 0 = vts.getD b.startVertexIndex.val 0
    · have h_bne_xy : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.startVertexIndex.val 0)
      have h_bne_yx : (vts.getD b.startVertexIndex.val 0 != vts.getD a.startVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.startVertexIndex.val 0)
      simp only [h_bne_xy, Bool.false_eq_true, ↓reduceIte] at h_gt'
      simp only [h_bne_yx, Bool.false_eq_true, ↓reduceIte]
      exact orderInsensitiveListCmp_swap_gt _ h_pb_anti₁ h_pb_anti₂ _ _ h_gt'
    · have h_bne_xy : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_eq
      simp only [h_bne_xy, ↓reduceIte] at h_gt'
      have h_xy_gt : (vts.getD a.startVertexIndex.val 0 : Nat) > vts.getD b.startVertexIndex.val 0 :=
        Nat.compare_eq_gt.mp h_gt'
      have h_yx_ne : vts.getD b.startVertexIndex.val 0 ≠ vts.getD a.startVertexIndex.val 0 := Ne.symm h_eq
      have h_bne_yx : (vts.getD b.startVertexIndex.val 0 != vts.getD a.startVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_yx_ne
      simp only [h_bne_yx, ↓reduceIte]
      exact Nat.compare_eq_lt.mpr h_xy_gt
  · -- Transitivity.
    intros a b c h_ab h_bc
    show (let xStartType := vts.getD a.startVertexIndex.val 0
          let zStartType := vts.getD c.startVertexIndex.val 0
          if xStartType != zStartType then compare xStartType zStartType
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 a.pathsToVertex c.pathsToVertex) ≠ Ordering.gt
    have h_ab' : (let xStartType := vts.getD a.startVertexIndex.val 0
                  let yStartType := vts.getD b.startVertexIndex.val 0
                  if xStartType != yStartType then compare xStartType yStartType
                  else orderInsensitiveListCmp (comparePathsBetween vts br)
                         a.pathsToVertex b.pathsToVertex) ≠ Ordering.gt := h_ab
    have h_bc' : (let yStartType := vts.getD b.startVertexIndex.val 0
                  let zStartType := vts.getD c.startVertexIndex.val 0
                  if yStartType != zStartType then compare yStartType zStartType
                  else orderInsensitiveListCmp (comparePathsBetween vts br)
                         b.pathsToVertex c.pathsToVertex) ≠ Ordering.gt := h_bc
    by_cases h_ab_eq : vts.getD a.startVertexIndex.val 0 = vts.getD b.startVertexIndex.val 0
    · by_cases h_bc_eq : vts.getD b.startVertexIndex.val 0 = vts.getD c.startVertexIndex.val 0
      · have h_ac_eq : vts.getD a.startVertexIndex.val 0 = vts.getD c.startVertexIndex.val 0 :=
          h_ab_eq.trans h_bc_eq
        have h_bne_ab : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = false := by
          rw [h_ab_eq]; exact bne_self_eq_false _
        have h_bne_bc : (vts.getD b.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = false := by
          rw [h_bc_eq]; exact bne_self_eq_false _
        have h_bne_ac : (vts.getD a.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = false := by
          rw [h_ac_eq]; exact bne_self_eq_false _
        simp only [h_bne_ab, Bool.false_eq_true, ↓reduceIte] at h_ab'
        simp only [h_bne_bc, Bool.false_eq_true, ↓reduceIte] at h_bc'
        simp only [h_bne_ac, Bool.false_eq_true, ↓reduceIte]
        exact orderInsensitiveListCmp_trans _ h_pb_anti₁ h_pb_trans h_pb_compat _ _ _ h_ab' h_bc'
      · have h_bne_bc : (vts.getD b.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_bc_eq
        simp only [h_bne_bc, ↓reduceIte] at h_bc'
        have h_bc_lt : compare (vts.getD b.startVertexIndex.val 0) (vts.getD c.startVertexIndex.val 0) = Ordering.lt := by
          rcases Nat.lt_trichotomy (vts.getD b.startVertexIndex.val 0) (vts.getD c.startVertexIndex.val 0) with h_lt | h_eq' | h_gt
          · exact Nat.compare_eq_lt.mpr h_lt
          · exact absurd h_eq' h_bc_eq
          · exact absurd (Nat.compare_eq_gt.mpr h_gt) h_bc'
        have h_ac_ne : vts.getD a.startVertexIndex.val 0 ≠ vts.getD c.startVertexIndex.val 0 := by
          rw [h_ab_eq]; exact h_bc_eq
        have h_bne_ac : (vts.getD a.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_ac_ne
        simp only [h_bne_ac, ↓reduceIte]
        rw [h_ab_eq]
        rw [h_bc_lt]
        intro h; cases h
    · by_cases h_bc_eq : vts.getD b.startVertexIndex.val 0 = vts.getD c.startVertexIndex.val 0
      · have h_bne_ab : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_ab_eq
        simp only [h_bne_ab, ↓reduceIte] at h_ab'
        have h_ab_lt : compare (vts.getD a.startVertexIndex.val 0) (vts.getD b.startVertexIndex.val 0) = Ordering.lt := by
          rcases Nat.lt_trichotomy (vts.getD a.startVertexIndex.val 0) (vts.getD b.startVertexIndex.val 0) with h_lt | h_eq' | h_gt
          · exact Nat.compare_eq_lt.mpr h_lt
          · exact absurd h_eq' h_ab_eq
          · exact absurd (Nat.compare_eq_gt.mpr h_gt) h_ab'
        have h_ac_ne : vts.getD a.startVertexIndex.val 0 ≠ vts.getD c.startVertexIndex.val 0 := by
          rw [← h_bc_eq]; exact h_ab_eq
        have h_bne_ac : (vts.getD a.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_ac_ne
        simp only [h_bne_ac, ↓reduceIte]
        rw [← h_bc_eq]
        rw [h_ab_lt]
        intro h; cases h
      · have h_bne_ab : (vts.getD a.startVertexIndex.val 0 != vts.getD b.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_ab_eq
        have h_bne_bc : (vts.getD b.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_bc_eq
        simp only [h_bne_ab, ↓reduceIte] at h_ab'
        simp only [h_bne_bc, ↓reduceIte] at h_bc'
        have h_ab_lt : (vts.getD a.startVertexIndex.val 0 : Nat) < vts.getD b.startVertexIndex.val 0 := by
          rcases Nat.lt_trichotomy (vts.getD a.startVertexIndex.val 0) (vts.getD b.startVertexIndex.val 0) with h_lt | h_eq' | h_gt
          · exact h_lt
          · exact absurd h_eq' h_ab_eq
          · exact absurd (Nat.compare_eq_gt.mpr h_gt) h_ab'
        have h_bc_lt : (vts.getD b.startVertexIndex.val 0 : Nat) < vts.getD c.startVertexIndex.val 0 := by
          rcases Nat.lt_trichotomy (vts.getD b.startVertexIndex.val 0) (vts.getD c.startVertexIndex.val 0) with h_lt | h_eq' | h_gt
          · exact h_lt
          · exact absurd h_eq' h_bc_eq
          · exact absurd (Nat.compare_eq_gt.mpr h_gt) h_bc'
        have h_ac_lt_nat : (vts.getD a.startVertexIndex.val 0 : Nat) < vts.getD c.startVertexIndex.val 0 :=
          lt_trans h_ab_lt h_bc_lt
        have h_ac_ne : vts.getD a.startVertexIndex.val 0 ≠ vts.getD c.startVertexIndex.val 0 :=
          Nat.ne_of_lt h_ac_lt_nat
        have h_bne_ac : (vts.getD a.startVertexIndex.val 0 != vts.getD c.startVertexIndex.val 0) = true :=
          bne_iff_ne.mpr h_ac_ne
        simp only [h_bne_ac, ↓reduceIte]
        rw [Nat.compare_eq_lt.mpr h_ac_lt_nat]
        intro h; cases h

/-- **σ-rank-closure of the from-side assignList**: for σ-fixed `state` and
σ-invariant `vts`/`br`, the assignList from `assignRanks cmp (sortBy cmp pathsAtDepth)` is
σ-rank-closed: each `(p, r)` has a matching `(f p, r)` in the list. -/
theorem from_assignList_σ_rank_closure
    {n : Nat} (σ : Equiv.Perm (Fin n))
    (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin n, br d (σ s).val (σ e).val = br d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let cmp := comparePathsFrom vts br
    let assignList := assignRanks cmp (sortBy cmp pathsAtDepth)
    ∀ item ∈ assignList,
      ∃ item' ∈ assignList,
        item'.1.startVertexIndex.val = (σ item.1.startVertexIndex).val
        ∧ item'.2 = item.2 := by
  intro pathsAtDepth cmp assignList item h_item_mem
  -- Setup notation.
  set f : PathsFrom n → PathsFrom n := PathsFrom.permute σ with hf_def
  -- Inner-array size = n via toList.length.
  have h_inner_size : (state.pathsOfLength.getD depth #[]).size = n := by
    rw [← Array.length_toList]; exact h_outer_len
  -- depth < state.pathsOfLength.size, derived from h_outer_len = n > 0 (so depth slot is in-range)
  -- when n > 0; for n = 0, the goal is vacuous since pathsAtDepth = [] makes assignList = [].
  -- We reason by cases on `n` only when needed; here we extract via classical reasoning.
  have h_depth_arr : depth < state.pathsOfLength.size := by
    by_contra h_not
    push_neg at h_not
    have : state.pathsOfLength.getD depth #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_not, Option.getD_none]
    rw [this] at h_outer_len
    simp at h_outer_len
    omega
  -- Decompose item ∈ assignList: item is at some position k in assignList.
  obtain ⟨k, h_k_lt, h_assign_k⟩ := List.mem_iff_getElem.mp h_item_mem
  -- Length of assignList = length of sortBy.
  have h_assign_len : assignList.length = (sortBy cmp pathsAtDepth).length :=
    assignRanks_length cmp _
  have h_sort_len_eq : (sortBy cmp pathsAtDepth).length = pathsAtDepth.length :=
    (sortBy_perm cmp pathsAtDepth).length_eq
  have h_sort_len : (sortBy cmp pathsAtDepth).length = n := by
    rw [h_sort_len_eq]; exact h_outer_len
  have h_assign_len_n : assignList.length = n := by rw [h_assign_len]; exact h_sort_len
  have h_k_lt_sort : k < (sortBy cmp pathsAtDepth).length := by
    rw [← h_assign_len]; exact h_k_lt
  have h_k_lt_n : k < n := by rw [← h_sort_len]; exact h_k_lt_sort
  -- item.1 = sortedY[k].
  have h_item1_eq : item.1 = (sortBy cmp pathsAtDepth)[k]'h_k_lt_sort := by
    have h_fst_eq : (assignList[k]'h_k_lt).1
                  = (sortBy cmp pathsAtDepth)[k]'h_k_lt_sort :=
      assignRanks_getElem_fst cmp (sortBy cmp pathsAtDepth) k h_k_lt_sort
    rw [← h_assign_k]; exact h_fst_eq
  -- item.2 = (assignList[k]).2.
  have h_item2_eq : item.2 = (assignList[k]'h_k_lt).2 := by
    rw [← h_assign_k]
  -- Set p := item.1 = sortedY[k].
  set p := item.1 with hp_def
  -- p ∈ pathsAtDepth (via sortBy_perm).
  have h_p_in_sort : p ∈ sortBy cmp pathsAtDepth := by
    rw [h_item1_eq]; exact List.getElem_mem _
  have h_p_in : p ∈ pathsAtDepth := (sortBy_perm cmp pathsAtDepth).mem_iff.mp h_p_in_sort
  -- Get a position s_p for p in pathsAtDepth.
  obtain ⟨s_p, hs_p_lt, hs_p_eq⟩ := List.mem_iff_getElem.mp h_p_in
  have hs_p_lt_n : s_p < n := by rw [← h_outer_len]; exact hs_p_lt
  -- Convert s_p to a Fin n.
  set s_fin : Fin n := ⟨s_p, hs_p_lt_n⟩ with hs_fin_def
  -- arr := state.pathsOfLength.getD depth #[]; pathsAtDepth = arr.toList.
  have h_pathsAtDepth_def : pathsAtDepth = (state.pathsOfLength.getD depth #[]).toList := rfl
  have h_arr_size := h_inner_size
  have h_s_p_lt_arr : s_p < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_arr_size]; exact hs_p_lt_n
  have h_σs_lt_arr : (σ s_fin).val < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_arr_size]; exact (σ s_fin).isLt
  -- The σ-fixedness implication: arr[(σ s_fin).val] = f arr[s_fin.val] = f p.
  have h_q_at_σs : (state.pathsOfLength.getD depth #[])[(σ s_fin).val]'h_σs_lt_arr = f p := by
    have h_eq := state_σ_fixed_pathsOfLength_at_σ_slot σ state h_state_σ_fixed depth
                  h_depth_arr h_inner_size s_fin h_σs_lt_arr h_s_p_lt_arr
    rw [h_eq]
    -- arr[s_fin.val] = arr[s_p] (def-eq) = pathsAtDepth[s_p] (Array.getElem_toList) = p (hs_p_eq).
    have h_arr_eq_p : (state.pathsOfLength.getD depth #[])[s_fin.val]'h_s_p_lt_arr = p := by
      show (state.pathsOfLength.getD depth #[])[s_p]'h_s_p_lt_arr = p
      rw [show (state.pathsOfLength.getD depth #[])[s_p]'h_s_p_lt_arr
            = (state.pathsOfLength.getD depth #[]).toList[s_p]'(by
                rw [Array.length_toList]; exact h_s_p_lt_arr)
          from (Array.getElem_toList (h := h_s_p_lt_arr)).symm]
      exact hs_p_eq
    rw [h_arr_eq_p]
  -- Define q := f p, located at position (σ s_fin).val in pathsAtDepth.
  set q : PathsFrom n := f p with hq_def
  have h_q_in : q ∈ pathsAtDepth := by
    rw [h_pathsAtDepth_def, ← h_q_at_σs]
    exact Array.getElem_mem_toList _
  -- q ∈ sortBy cmp pathsAtDepth.
  have h_q_in_sort : q ∈ sortBy cmp pathsAtDepth :=
    (sortBy_perm cmp pathsAtDepth).mem_iff.mpr h_q_in
  -- Get position k' for q in sortedY.
  obtain ⟨k', h_k'_lt_sort, hk'_eq⟩ := List.mem_iff_getElem.mp h_q_in_sort
  have h_k'_lt : k' < assignList.length := by rw [h_assign_len]; exact h_k'_lt_sort
  -- cmp p q = .eq via comparePathsFrom_σ_self_eq.
  have h_p_pathsToVertex_len : p.pathsToVertex.length = n := h_pathsToVertex_len p h_p_in
  have h_p_inner_len : ∀ q' ∈ p.pathsToVertex, q'.depth > 0 → q'.connectedSubPaths.length = n :=
    h_inner_len p h_p_in
  have h_cmp_pq : cmp p q = Ordering.eq := by
    rw [hq_def, hf_def]
    exact comparePathsFrom_σ_self_eq σ vts hvts br hbr p h_p_pathsToVertex_len h_p_inner_len
  -- Now use assignRanks_rank_eq_within_eq_class.
  -- Get total preorder of cmp.
  obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
    comparePathsFrom_total_preorder (vc := n) vts br
  -- sortBy is sorted (Pairwise non-gt).
  have h_sorted : (sortBy cmp pathsAtDepth).Pairwise (fun a b => cmp a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp h_antisym₂ h_trans pathsAtDepth
  -- cmp sortedY[k] sortedY[k'] = .eq (from cmp p q = .eq).
  have h_sortk_eq_p : (sortBy cmp pathsAtDepth)[k]'h_k_lt_sort = p := h_item1_eq.symm
  have h_sortk'_eq_q : (sortBy cmp pathsAtDepth)[k']'h_k'_lt_sort = q := hk'_eq
  have h_cmp_at : cmp ((sortBy cmp pathsAtDepth)[k]'h_k_lt_sort)
                      ((sortBy cmp pathsAtDepth)[k']'h_k'_lt_sort) = Ordering.eq := by
    rw [h_sortk_eq_p, h_sortk'_eq_q]; exact h_cmp_pq
  -- eq is symmetric (derived from antisym).
  have h_eq_symm : ∀ a b : PathsFrom n, cmp a b = .eq → cmp b a = .eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      exfalso
      have h_gt : comparePathsFrom vts br a b = .gt := h_antisym₁ b a h_ba
      have h_eq : comparePathsFrom vts br a b = .eq := hab
      rw [h_gt] at h_eq; cases h_eq
    | .gt =>
      exfalso
      have h_lt : comparePathsFrom vts br a b = .lt := h_antisym₂ b a h_ba
      have h_eq : comparePathsFrom vts br a b = .eq := hab
      rw [h_lt] at h_eq; cases h_eq
  -- Apply assignRanks_rank_eq_within_eq_class with i = min(k, k'), j = max(k, k').
  have h_b_k : k < (assignRanks cmp (sortBy cmp pathsAtDepth)).length := by
    rw [assignRanks_length]; exact h_k_lt_sort
  have h_b_k' : k' < (assignRanks cmp (sortBy cmp pathsAtDepth)).length := by
    rw [assignRanks_length]; exact h_k'_lt_sort
  have h_rank_eq :
      ((assignRanks cmp (sortBy cmp pathsAtDepth))[k]'h_b_k).2
        = ((assignRanks cmp (sortBy cmp pathsAtDepth))[k']'h_b_k').2 := by
    rcases Nat.lt_or_ge k' k with h_lt | h_ge
    · -- k' < k: swap.
      have h_le_swap : k' ≤ k := Nat.le_of_lt h_lt
      have h_cmp_swap : cmp ((sortBy cmp pathsAtDepth)[k']'h_k'_lt_sort)
                            ((sortBy cmp pathsAtDepth)[k]'h_k_lt_sort) = Ordering.eq :=
        h_eq_symm _ _ h_cmp_at
      exact (assignRanks_rank_eq_within_eq_class cmp h_refl h_antisym₁ h_antisym₂ h_trans
        (sortBy cmp pathsAtDepth) h_sorted k' k h_le_swap h_k_lt_sort h_cmp_swap).symm
    · -- k ≤ k': direct.
      exact assignRanks_rank_eq_within_eq_class cmp h_refl h_antisym₁ h_antisym₂ h_trans
        (sortBy cmp pathsAtDepth) h_sorted k k' h_ge h_k'_lt_sort h_cmp_at
  -- Construct item' = assignList[k']. It has q as first component and rank = item.2.
  refine ⟨assignList[k']'h_k'_lt, List.getElem_mem _, ?_, ?_⟩
  · -- (assignList[k']).1 = sortedY[k'] = q. q.startVertexIndex.val = (σ p.startVertexIndex).val.
    have h_assign_k'_fst : (assignList[k']'h_k'_lt).1
                         = (sortBy cmp pathsAtDepth)[k']'h_k'_lt_sort :=
      assignRanks_getElem_fst cmp (sortBy cmp pathsAtDepth) k' h_k'_lt_sort
    rw [h_assign_k'_fst, h_sortk'_eq_q, hq_def, hf_def]
    -- (PathsFrom.permute σ p).startVertexIndex = σ p.startVertexIndex (for n ≥ 1).
    -- For n = 0, p.startVertexIndex.elim0 makes the goal trivial.
    by_cases hn : n = 0
    · subst hn; exact p.startVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.startVertexIndex).val = (σ p.startVertexIndex).val
      rfl
  · -- (assignList[k']).2 = item.2.
    rw [h_item2_eq]; exact h_rank_eq.symm

/-- For a list `L`, `L.foldl (acc, x => acc ++ f x) []` flattens to a `flatMap`-style
collection: `q ∈ result ↔ ∃ x ∈ L, q ∈ f x`. -/
private theorem mem_foldl_append_init_nil {α β : Type} (f : β → List α) (q : α) :
    ∀ (L : List β) (init : List α),
      q ∈ L.foldl (fun acc x => acc ++ f x) init ↔
        q ∈ init ∨ ∃ x ∈ L, q ∈ f x := by
  intro L
  induction L with
  | nil =>
    intro init
    simp [List.foldl]
  | cons hd tl ih =>
    intro init
    rw [List.foldl_cons]
    rw [ih (init ++ f hd)]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro ((h_init | h_hd) | ⟨x, h_in, h_q⟩)
      · exact Or.inl h_init
      · exact Or.inr ⟨hd, Or.inl rfl, h_hd⟩
      · exact Or.inr ⟨x, Or.inr h_in, h_q⟩
    · rintro (h_init | ⟨x, (h_eq | h_in), h_q⟩)
      · exact Or.inl (Or.inl h_init)
      · subst h_eq; exact Or.inl (Or.inr h_q)
      · exact Or.inr ⟨x, h_in, h_q⟩

/-- Specialization for the algorithm's `allBetween` foldl. -/
theorem mem_allBetween_iff {n : Nat} (q : PathsBetween n)
    (pathsAtDepth : List (PathsFrom n)) :
    q ∈ pathsAtDepth.foldl
        (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [] ↔
      ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex := by
  rw [mem_foldl_append_init_nil (fun pf : PathsFrom n => pf.pathsToVertex) q pathsAtDepth []]
  simp

/-- **σ-rank-closure of the between-side assignList**: for σ-fixed `state` and
σ-invariant `vts`/`br`, the assignList from `assignRanks cmp (sortBy cmp allBetween)` is
σ-rank-closed: each `(q, r)` has a matching `(f q, r)` in the list. -/
theorem between_assignList_σ_rank_closure
    {n : Nat} (σ : Equiv.Perm (Fin n))
    (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin n, br d (σ s).val (σ e).val = br d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let allBetween := pathsAtDepth.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let cmp := comparePathsBetween vts br
    let assignList := assignRanks cmp (sortBy cmp allBetween)
    ∀ item ∈ assignList,
      ∃ item' ∈ assignList,
        item'.1.startVertexIndex.val = (σ item.1.startVertexIndex).val
        ∧ item'.1.endVertexIndex.val = (σ item.1.endVertexIndex).val
        ∧ item'.2 = item.2 := by
  intro pathsAtDepth allBetween cmp assignList item h_item_mem
  set f : PathsBetween n → PathsBetween n := PathsBetween.permute σ with hf_def
  -- Inner-array size = n via toList.length.
  have h_inner_size : (state.pathsOfLength.getD depth #[]).size = n := by
    rw [← Array.length_toList]; exact h_outer_len
  have h_depth_arr : depth < state.pathsOfLength.size := by
    by_contra h_not
    push_neg at h_not
    have : state.pathsOfLength.getD depth #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_not, Option.getD_none]
    rw [this] at h_outer_len
    simp at h_outer_len
    omega
  -- Decompose item ∈ assignList: at some position k.
  obtain ⟨k, h_k_lt, h_assign_k⟩ := List.mem_iff_getElem.mp h_item_mem
  have h_assign_len : assignList.length = (sortBy cmp allBetween).length :=
    assignRanks_length cmp _
  have h_k_lt_sort : k < (sortBy cmp allBetween).length := by
    rw [← h_assign_len]; exact h_k_lt
  have h_item1_eq : item.1 = (sortBy cmp allBetween)[k]'h_k_lt_sort := by
    have h_fst_eq : (assignList[k]'h_k_lt).1
                  = (sortBy cmp allBetween)[k]'h_k_lt_sort :=
      assignRanks_getElem_fst cmp (sortBy cmp allBetween) k h_k_lt_sort
    rw [← h_assign_k]; exact h_fst_eq
  have h_item2_eq : item.2 = (assignList[k]'h_k_lt).2 := by rw [← h_assign_k]
  set q := item.1 with hq_def
  -- q ∈ allBetween via sortBy_perm.
  have h_q_in_sort : q ∈ sortBy cmp allBetween := by
    rw [h_item1_eq]; exact List.getElem_mem _
  have h_q_in : q ∈ allBetween :=
    (sortBy_perm cmp allBetween).mem_iff.mp h_q_in_sort
  -- q ∈ allBetween ⟹ ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex.
  obtain ⟨pf, h_pf_in, h_q_in_pf⟩ := (mem_allBetween_iff q pathsAtDepth).mp h_q_in
  -- pf is at some slot s_pf : Fin n in pathsAtDepth.
  obtain ⟨s_pf, hs_pf_lt, hs_pf_eq⟩ := List.mem_iff_getElem.mp h_pf_in
  have hs_pf_lt_n : s_pf < n := by rw [← h_outer_len]; exact hs_pf_lt
  set s_fin : Fin n := ⟨s_pf, hs_pf_lt_n⟩
  have h_s_pf_lt_arr : s_pf < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_inner_size]; exact hs_pf_lt_n
  have h_σs_lt_arr : (σ s_fin).val < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_inner_size]; exact (σ s_fin).isLt
  -- σ-fixedness: pathsAtDepth[σ s_fin] = PathsFrom.permute σ pf.
  have h_pf_at_σs_eq :
      (state.pathsOfLength.getD depth #[])[(σ s_fin).val]'h_σs_lt_arr
        = PathsFrom.permute σ pf := by
    have h_eq := state_σ_fixed_pathsOfLength_at_σ_slot σ state h_state_σ_fixed depth
                  h_depth_arr h_inner_size s_fin h_σs_lt_arr h_s_pf_lt_arr
    rw [h_eq]
    have h_arr_eq_p : (state.pathsOfLength.getD depth #[])[s_fin.val]'h_s_pf_lt_arr = pf := by
      show (state.pathsOfLength.getD depth #[])[s_pf]'h_s_pf_lt_arr = pf
      rw [show (state.pathsOfLength.getD depth #[])[s_pf]'h_s_pf_lt_arr
            = (state.pathsOfLength.getD depth #[]).toList[s_pf]'(by
                rw [Array.length_toList]; exact h_s_pf_lt_arr)
          from (Array.getElem_toList (h := h_s_pf_lt_arr)).symm]
      exact hs_pf_eq
    rw [h_arr_eq_p]
  -- pf' := PathsFrom.permute σ pf, located at slot σ s_fin in pathsAtDepth.
  set pf' : PathsFrom n := PathsFrom.permute σ pf with hpf'_def
  have h_pf'_in : pf' ∈ pathsAtDepth := by
    show pf' ∈ (state.pathsOfLength.getD depth #[]).toList
    rw [← h_pf_at_σs_eq]
    exact Array.getElem_mem_toList _
  -- q ∈ pf.pathsToVertex ⟹ f q ∈ pf.pathsToVertex.map f.
  have h_fq_in_map : f q ∈ pf.pathsToVertex.map f := List.mem_map.mpr ⟨q, h_q_in_pf, rfl⟩
  -- pf'.pathsToVertex.Perm (pf.pathsToVertex.map f) via PathsFrom_permute_pathsToVertex_perm.
  have h_pf_pathsToVertex_len : pf.pathsToVertex.length = n := h_pathsToVertex_len pf h_pf_in
  have h_perm : pf'.pathsToVertex.Perm (pf.pathsToVertex.map f) :=
    PathsFrom_permute_pathsToVertex_perm σ pf h_pf_pathsToVertex_len
  -- f q ∈ pf'.pathsToVertex.
  have h_fq_in_pf' : f q ∈ pf'.pathsToVertex := h_perm.symm.mem_iff.mp h_fq_in_map
  -- f q ∈ allBetween (via the foldl-flatten lemma).
  have h_fq_in_all : f q ∈ allBetween := by
    show f q ∈ pathsAtDepth.foldl _ []
    exact (mem_allBetween_iff (f q) pathsAtDepth).mpr ⟨pf', h_pf'_in, h_fq_in_pf'⟩
  -- f q ∈ sortBy cmp allBetween, at some position k'.
  have h_fq_in_sort : f q ∈ sortBy cmp allBetween :=
    (sortBy_perm cmp allBetween).mem_iff.mpr h_fq_in_all
  obtain ⟨k', h_k'_lt_sort, hk'_eq⟩ := List.mem_iff_getElem.mp h_fq_in_sort
  have h_k'_lt : k' < assignList.length := by rw [h_assign_len]; exact h_k'_lt_sort
  -- cmp q (f q) = .eq via comparePathsBetween_σ_self_eq.
  have h_q_inner_len : q.depth > 0 → q.connectedSubPaths.length = n :=
    h_inner_len pf h_pf_in q h_q_in_pf
  have h_cmp_qfq : cmp q (f q) = Ordering.eq := by
    rw [hf_def]
    exact comparePathsBetween_σ_self_eq σ vts hvts br hbr q h_q_inner_len
  -- Get total preorder of cmp.
  obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
    comparePathsBetween_total_preorder (vc := n) vts br
  have h_sorted : (sortBy cmp allBetween).Pairwise (fun a b => cmp a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp h_antisym₂ h_trans allBetween
  have h_sortk_eq_q : (sortBy cmp allBetween)[k]'h_k_lt_sort = q := h_item1_eq.symm
  have h_sortk'_eq_fq : (sortBy cmp allBetween)[k']'h_k'_lt_sort = f q := hk'_eq
  have h_cmp_at : cmp ((sortBy cmp allBetween)[k]'h_k_lt_sort)
                      ((sortBy cmp allBetween)[k']'h_k'_lt_sort) = Ordering.eq := by
    rw [h_sortk_eq_q, h_sortk'_eq_fq]; exact h_cmp_qfq
  have h_eq_symm : ∀ a b : PathsBetween n, cmp a b = .eq → cmp b a = .eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      exfalso
      have h_gt : comparePathsBetween vts br a b = .gt := h_antisym₁ b a h_ba
      have h_eq : comparePathsBetween vts br a b = .eq := hab
      rw [h_gt] at h_eq; cases h_eq
    | .gt =>
      exfalso
      have h_lt : comparePathsBetween vts br a b = .lt := h_antisym₂ b a h_ba
      have h_eq : comparePathsBetween vts br a b = .eq := hab
      rw [h_lt] at h_eq; cases h_eq
  have h_b_k : k < (assignRanks cmp (sortBy cmp allBetween)).length := by
    rw [assignRanks_length]; exact h_k_lt_sort
  have h_b_k' : k' < (assignRanks cmp (sortBy cmp allBetween)).length := by
    rw [assignRanks_length]; exact h_k'_lt_sort
  have h_rank_eq :
      ((assignRanks cmp (sortBy cmp allBetween))[k]'h_b_k).2
        = ((assignRanks cmp (sortBy cmp allBetween))[k']'h_b_k').2 := by
    rcases Nat.lt_or_ge k' k with h_lt | h_ge
    · have h_le_swap : k' ≤ k := Nat.le_of_lt h_lt
      have h_cmp_swap : cmp ((sortBy cmp allBetween)[k']'h_k'_lt_sort)
                            ((sortBy cmp allBetween)[k]'h_k_lt_sort) = Ordering.eq :=
        h_eq_symm _ _ h_cmp_at
      exact (assignRanks_rank_eq_within_eq_class cmp h_refl h_antisym₁ h_antisym₂ h_trans
        (sortBy cmp allBetween) h_sorted k' k h_le_swap h_k_lt_sort h_cmp_swap).symm
    · exact assignRanks_rank_eq_within_eq_class cmp h_refl h_antisym₁ h_antisym₂ h_trans
        (sortBy cmp allBetween) h_sorted k k' h_ge h_k'_lt_sort h_cmp_at
  -- Construct item' = assignList[k']: first component is f q.
  refine ⟨assignList[k']'h_k'_lt, List.getElem_mem _, ?_, ?_, ?_⟩
  · -- (assignList[k']).1.startVertexIndex.val = (σ q.startVertexIndex).val.
    have h_assign_k'_fst : (assignList[k']'h_k'_lt).1
                         = (sortBy cmp allBetween)[k']'h_k'_lt_sort :=
      assignRanks_getElem_fst cmp (sortBy cmp allBetween) k' h_k'_lt_sort
    rw [h_assign_k'_fst, h_sortk'_eq_fq, hf_def]
    by_cases hn : n = 0
    · subst hn; exact q.startVertexIndex.elim0
    · obtain ⟨k_pos, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ q.startVertexIndex).val = (σ q.startVertexIndex).val
      rfl
  · -- (assignList[k']).1.endVertexIndex.val = (σ q.endVertexIndex).val.
    have h_assign_k'_fst : (assignList[k']'h_k'_lt).1
                         = (sortBy cmp allBetween)[k']'h_k'_lt_sort :=
      assignRanks_getElem_fst cmp (sortBy cmp allBetween) k' h_k'_lt_sort
    rw [h_assign_k'_fst, h_sortk'_eq_fq, hf_def]
    by_cases hn : n = 0
    · subst hn; exact q.endVertexIndex.elim0
    · obtain ⟨k_pos, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ q.endVertexIndex).val = (σ q.endVertexIndex).val
      rfl
  · -- (assignList[k']).2 = item.2.
    rw [h_item2_eq]; exact h_rank_eq.symm


end Graph
