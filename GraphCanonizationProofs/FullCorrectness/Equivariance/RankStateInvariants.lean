import FullCorrectness.Equivariance.Actions

/-!
# Size invariants and `RankState.σInvariant`  (`FullCorrectness.Equivariance.RankStateInvariants`)

Proves the size-shape facts for `calculatePathRankings`'s output and defines the
`RankState.σInvariant` predicate (a σ-invariance certificate for a `RankState`).

The key deliverables are:
- `calculatePathRankings_fromRanks_size` — `fromRanks` has size `vc`.
- `calculatePathRankings_size_inv` — full `vc × vc × vc` / `vc × vc` shape facts.
- `RankState.σInvariant` — packages size + value σ-invariance into one structure.
- `RankState.σInvariant.permute_eq_self` — extensionality: σInvariant → permute σ rs = rs.
-/

namespace Graph

variable {n : Nat}

/-! ## §3 Stage B — `calculatePathRankings` equivariance -/

/-- The `fromRanks` table produced by `calculatePathRankings` has size `vc`. Follows from
`set!`-size-preservation through the outer fold; the initial table is built as
`(Array.range vc).map ...` of size `vc`. -/
theorem calculatePathRankings_fromRanks_size {vc : Nat} (state : PathState vc)
    (vts : Array VertexType) :
    (calculatePathRankings state vts).fromRanks.size = vc := by
  unfold calculatePathRankings
  -- The fold's `.2` (`fromRanks`-in-progress) starts with size `vc` and is updated only
  -- by `set!`, which preserves size. We prove this via a generic foldl-invariant.
  suffices haux : ∀ (l : List Nat)
      (start : Array (Array (Array Nat)) × Array (Array Nat)),
      start.2.size = vc →
      (l.foldl (fun accumulated depth =>
          let (currentBetween, currentFrom) := accumulated
          let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
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
          (updatedBetween, updatedFrom)) start).2.size = vc by
    apply haux
    simp
  intro l
  induction l with
  | nil => intros _ h; exact h
  | cons x xs ih =>
    intros start hstart
    rw [List.foldl_cons]
    apply ih
    obtain ⟨b, f⟩ := start
    simp only [] at hstart ⊢
    -- Inner fold over `assignRanks ...` applies `set!` (size-preserving).
    suffices h_inner : ∀ (l' : List ((PathsFrom vc) × Nat)) (acc : Array (Array Nat)),
        acc.size = vc →
        (l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
          let (pathFrom, rank) := item
          let depthSlice := fromAcc.getD x #[]
          fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).size = vc by
      apply h_inner _ _ hstart
    intro l' acc hacc
    induction l' generalizing acc with
    | nil => exact hacc
    | cons y ys ih_inner =>
      rw [List.foldl_cons]
      apply ih_inner
      obtain ⟨pathFrom, rank⟩ := y
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hacc]

/-! ### Size invariants for `calculatePathRankings`'s output

The `calculatePathRankings_σInvariant` (below) needs five size facts: `betweenRanks` has
shape `vc × vc × vc` and `fromRanks` has shape `vc × vc`. We prove these via small
size-preservation lemmas about `set!`/`setBetween` and a foldl invariant. -/

/-- `set!` at the same in-bounds index reads back the inserted value (for `getD`). -/
private theorem Array_set!_getD_self {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (h : i < xs.size) : (xs.set! i v).getD i d = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

/-- `set!` at a different index leaves the `getD` reading unchanged. -/
private theorem Array_set!_getD_ne {α : Type} (xs : Array α) (i j : Nat) (v d : α)
    (h : i ≠ j) : (xs.set! i v).getD j d = xs.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

/-- Out-of-bounds `set!` is a no-op. -/
private theorem Array_set!_eq_self_of_size_le {α : Type} (xs : Array α) (i : Nat) (v : α)
    (h : xs.size ≤ i) : xs.set! i v = xs := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le h]

/-- `setBetween` preserves `betweenTable`'s outer size. -/
private theorem setBetween_size (b : Array (Array (Array Nat))) (d s e r : Nat) :
    (setBetween b d s e r).size = b.size := by
  unfold setBetween
  simp [Array.set!_eq_setIfInBounds]

/-- `setBetween` preserves the size of every depth-row. -/
private theorem setBetween_getD_size (b : Array (Array (Array Nat))) (d s e r d' : Nat) :
    ((setBetween b d s e r).getD d' #[]).size = (b.getD d' #[]).size := by
  unfold setBetween
  by_cases h_eq : d = d'
  · subst h_eq
    by_cases h_in : d < b.size
    · rw [Array_set!_getD_self _ _ _ _ h_in]
      simp [Array.set!_eq_setIfInBounds]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_eq]

/-- `setBetween` preserves the size of every (depth, start)-cell. -/
theorem setBetween_getD_getD_size (b : Array (Array (Array Nat)))
    (d s e r d' s' : Nat) :
    (((setBetween b d s e r).getD d' #[]).getD s' #[]).size
    = ((b.getD d' #[]).getD s' #[]).size := by
  unfold setBetween
  by_cases h_d_eq : d = d'
  · subst h_d_eq
    by_cases h_d_in : d < b.size
    · rw [Array_set!_getD_self _ _ _ _ h_d_in]
      -- Inside: `depthSlice.set! s (startSlice.set! e r)`. Recurse on s vs s'.
      by_cases h_s_eq : s = s'
      · subst h_s_eq
        by_cases h_s_in : s < (b.getD d #[]).size
        · rw [Array_set!_getD_self _ _ _ _ h_s_in]
          simp [Array.set!_eq_setIfInBounds]
        · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
      · rw [Array_set!_getD_ne _ _ _ _ _ h_s_eq]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_d_eq]

/-- The from-side update preserves the size of every depth-row. -/
private theorem from_set_getD_size (f : Array (Array Nat)) (d s : Nat) (rank : Nat) (d' : Nat) :
    ((f.set! d ((f.getD d #[]).set! s rank)).getD d' #[]).size = (f.getD d' #[]).size := by
  by_cases h_eq : d = d'
  · subst h_eq
    by_cases h_in : d < f.size
    · rw [Array_set!_getD_self _ _ _ _ h_in]
      simp [Array.set!_eq_setIfInBounds]
    · rw [Array_set!_eq_self_of_size_le _ _ _ (by omega)]
  · rw [Array_set!_getD_ne _ _ _ _ _ h_eq]

/-! ### Chain helpers: `set!`-chain inversion

These chain helpers express how a foldl over `set!`-style updates evolves: the value at a
target position is determined by the (unique, by `Nodup`) entry whose first component
equals that position; positions outside the chain are unchanged. They are shared between
`Invariants.lean` (used by tiebreak content) and `PathEquivariance.lean` (used by σ-inv). -/

/-- Foldl `set!`-chain leaves untouched positions unchanged: if no entry in `l` has its
first component equal to `i`, the position-`i` value of the result equals the input. -/
theorem array_set_chain_outside_unchanged
    {α : Type} (arr₀ : Array α) (l : List (Nat × α)) (i : Nat) (defaultV : α)
    (h : ∀ item ∈ l, item.1 ≠ i) :
    (l.foldl (fun a item => a.set! item.1 item.2) arr₀).getD i defaultV
      = arr₀.getD i defaultV := by
  induction l generalizing arr₀ with
  | nil => rfl
  | cons head l' ih =>
    rw [List.foldl_cons]
    have h_head_ne : head.1 ≠ i := h head List.mem_cons_self
    have h_tail : ∀ item ∈ l', item.1 ≠ i := fun item h_in => h item (List.mem_cons_of_mem _ h_in)
    rw [ih (arr₀.set! head.1 head.2) h_tail]
    simp only [Array.getD_eq_getD_getElem?,
               Array.set!_eq_setIfInBounds,
               Array.getElem?_setIfInBounds_ne h_head_ne]

/-- Foldl `set!`-chain at the target index gives the target value, when the chain
indices are `Nodup` (the target's index appears only at the target's position). -/
theorem array_set_chain_at_target_nodup
    {α : Type} (arr₀ : Array α) (l : List (Nat × α)) (target : Nat × α) (defaultV : α)
    (h_target_in : target ∈ l)
    (h_nodup : (l.map (·.1)).Nodup)
    (h_target_bound : target.1 < arr₀.size) :
    (l.foldl (fun a item => a.set! item.1 item.2) arr₀).getD target.1 defaultV
      = target.2 := by
  induction l generalizing arr₀ with
  | nil => exact absurd h_target_in (by simp)
  | cons head l' ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h_target_in with h_eq | h_in_tail
    · have h_others_ne : ∀ item ∈ l', item.1 ≠ target.1 := by
        intro item h_in_item
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : head.1 ∉ l'.map (·.1) := (List.nodup_cons.mp h_nd').1
        rw [← h_eq] at h_head_not_in
        intro h_eq_idx
        exact h_head_not_in (h_eq_idx ▸ List.mem_map.mpr ⟨item, h_in_item, rfl⟩)
      have h_step_eq : arr₀.set! head.1 head.2 = arr₀.set! target.1 target.2 := by
        rw [h_eq]
      rw [h_step_eq]
      rw [array_set_chain_outside_unchanged (arr₀.set! target.1 target.2) l' target.1 defaultV h_others_ne]
      simp only [Array.getD_eq_getD_getElem?,
                 Array.set!_eq_setIfInBounds,
                 Array.getElem?_setIfInBounds_self_of_lt h_target_bound,
                 Option.getD_some]
    · have h_head_ne : head.1 ≠ target.1 := by
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : head.1 ∉ l'.map (·.1) := (List.nodup_cons.mp h_nd').1
        intro h_eq_idx
        exact h_head_not_in (h_eq_idx ▸ List.mem_map.mpr ⟨target, h_in_tail, rfl⟩)
      have h_nodup' : (l'.map (·.1)).Nodup := by
        simp only [List.map_cons] at h_nodup
        exact (List.nodup_cons.mp h_nodup).2
      have h_bound' : target.1 < (arr₀.set! head.1 head.2).size := by
        simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h_target_bound
      exact ih (arr₀.set! head.1 head.2) h_in_tail h_nodup' h_bound'

/-- Strip the outer `fromAcc.set! depth` wrapper from the inner fold: the slice at
position `depth` after the fold equals folding `slice.set! ... ...` directly on the
initial slice. -/
theorem inner_fold_slice_at_depth {n : Nat}
    (l : List (PathsFrom n × Nat)) (fromAcc₀ : Array (Array Nat)) (depth : Nat)
    (h_depth_in : depth < fromAcc₀.size) :
    (l.foldl (fun (fromAcc : Array (Array Nat)) item =>
      let (pathFrom, rank) := item
      let depthSlice := fromAcc.getD depth #[]
      fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) fromAcc₀).getD depth #[]
    = l.foldl (fun slice item =>
        slice.set! item.1.startVertexIndex.val item.2) (fromAcc₀.getD depth #[]) := by
  induction l generalizing fromAcc₀ with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons, List.foldl_cons]
    set fromAcc' := fromAcc₀.set! depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2) with hfromAcc'
    have h_depth_in' : depth < fromAcc'.size := by
      rw [hfromAcc']
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact h_depth_in
    have h_slice_eq : fromAcc'.getD depth #[]
                    = (fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2 := by
      rw [hfromAcc']
      rw [show fromAcc₀.set! depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2)
            = fromAcc₀.setIfInBounds depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2) from rfl]
      simp only [Array.getD_eq_getD_getElem?,
                 Array.getElem?_setIfInBounds_self_of_lt h_depth_in,
                 Option.getD_some]
    rw [ih fromAcc' h_depth_in', h_slice_eq]

/-- Inner fold (within `calculatePathRankings`) only writes to slot `depth`, so positions
`target ≠ depth` are preserved. -/
theorem inner_fold_other_depth_unchanged
    (l : List (PathsFrom n × Nat)) (fromAcc₀ : Array (Array Nat))
    (depth target : Nat) (h_ne : depth ≠ target) :
    (l.foldl (fun (fromAcc : Array (Array Nat)) item =>
      let (pathFrom, rank) := item
      let depthSlice := fromAcc.getD depth #[]
      fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) fromAcc₀).getD target #[]
    = fromAcc₀.getD target #[] := by
  induction l generalizing fromAcc₀ with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons]
    rw [ih]
    show (fromAcc₀.set! depth
            ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2)).getD target #[]
       = fromAcc₀.getD target #[]
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
               Array.getElem?_setIfInBounds_ne h_ne]

/-- Strip the outer `setBetween` wrapper from the setBetween-chain fold: the depth-slice
of the result equals folding `slice.set! start (inner.set! end r)` directly on the initial
depth-slice. The 3D analog of `inner_fold_slice_at_depth`. -/
theorem setBetween_fold_slice_at_depth {n : Nat}
    (l : List (PathsBetween n × Nat)) (betweenAcc₀ : Array (Array (Array Nat)))
    (depth : Nat) (h_depth_in : depth < betweenAcc₀.size) :
    (l.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
      let (pathBetween, rank) := item
      setBetween betweenAcc depth pathBetween.startVertexIndex.val
        pathBetween.endVertexIndex.val rank) betweenAcc₀).getD depth #[]
    = l.foldl (fun (ds : Array (Array Nat)) item =>
        let s := item.1.startVertexIndex.val
        let e := item.1.endVertexIndex.val
        ds.set! s ((ds.getD s #[]).set! e item.2)) (betweenAcc₀.getD depth #[]) := by
  induction l generalizing betweenAcc₀ with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons, List.foldl_cons]
    set betweenAcc' := setBetween betweenAcc₀ depth item.1.startVertexIndex.val
        item.1.endVertexIndex.val item.2 with hbetweenAcc'
    have h_depth_in' : depth < betweenAcc'.size := by
      rw [hbetweenAcc']
      unfold setBetween
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact h_depth_in
    have h_slice_eq : betweenAcc'.getD depth #[]
        = (betweenAcc₀.getD depth #[]).set! item.1.startVertexIndex.val
            (((betweenAcc₀.getD depth #[]).getD item.1.startVertexIndex.val #[]).set!
                item.1.endVertexIndex.val item.2) := by
      rw [hbetweenAcc']
      unfold setBetween
      simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
                 Array.getElem?_setIfInBounds_self_of_lt h_depth_in, Option.getD_some]
    rw [ih betweenAcc' h_depth_in', h_slice_eq]

/-- The setBetween chain only writes to outer index `depth`, so other depths are
preserved. The 3D analog of `inner_fold_other_depth_unchanged`. -/
theorem setBetween_fold_other_depth_unchanged {n : Nat}
    (l : List (PathsBetween n × Nat)) (betweenAcc₀ : Array (Array (Array Nat)))
    (depth target : Nat) (h_ne : depth ≠ target) :
    (l.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
      let (pathBetween, rank) := item
      setBetween betweenAcc depth pathBetween.startVertexIndex.val
        pathBetween.endVertexIndex.val rank) betweenAcc₀).getD target #[]
    = betweenAcc₀.getD target #[] := by
  induction l generalizing betweenAcc₀ with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons]
    rw [ih]
    show (setBetween betweenAcc₀ depth item.1.startVertexIndex.val
            item.1.endVertexIndex.val item.2).getD target #[]
       = betweenAcc₀.getD target #[]
    unfold setBetween
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
               Array.getElem?_setIfInBounds_ne h_ne]

/-! ### `RankState.σInvariant` and extensionality

The structural content of `RankState.permute σ rs = rs` decomposes into (a) size constraints
ensuring `rs`'s tables are shape `n × n × n` / `n × n` and (b) σ-invariance of the cell
values. We package this as `RankState.σInvariant`, prove the extensionality direction
(`σInvariant → permute σ rs = rs`), and reduce the main theorem to the σInvariance of
`calculatePathRankings (initializePaths G) vts`. The latter is the deep content — it
requires σ-equivariance of the entire `calculatePathRankings` pipeline (compare → sort →
assignRanks → fold). -/

/-- The structural σ-invariance of a `RankState` w.r.t. a permutation `σ`. -/
structure RankState.σInvariant {n : Nat} (σ : Equiv.Perm (Fin n)) (rs : RankState) : Prop where
  fromRanks_size      : rs.fromRanks.size = n
  betweenRanks_size   : rs.betweenRanks.size = n
  fromRanks_row_size  : ∀ d : Nat, d < n → (rs.fromRanks.getD d #[]).size = n
  betweenRanks_row_size : ∀ d : Nat, d < n → (rs.betweenRanks.getD d #[]).size = n
  betweenRanks_cell_size : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
    ((rs.betweenRanks.getD d #[]).getD s #[]).size = n
  /-- σ-invariance of `fromRanks` values: σ⁻¹-shifted start positions hold the same rank. -/
  fromRanks_inv : ∀ d : Nat, d < n → ∀ s : Fin n,
    (rs.fromRanks.getD d #[]).getD s.val 0
    = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0
  /-- σ-invariance of `betweenRanks` values: σ⁻¹-shifted (start, end) hold the same rank. -/
  betweenRanks_inv : ∀ d : Nat, d < n → ∀ s e : Fin n,
    ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
    = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0

/-- Extensionality: the structural σ-invariance is exactly what `RankState.permute σ rs = rs`
requires. -/
theorem RankState.σInvariant.permute_eq_self
    {σ : Equiv.Perm (Fin n)} {rs : RankState} (h : RankState.σInvariant σ rs) :
    RankState.permute σ rs = rs := by
  -- Apply mk.injEq via show on the unfolded `permute` form.
  show ({ betweenRanks := _, fromRanks := _ } : RankState) = rs
  refine RankState.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · -- betweenRanks equality.
    refine Array.ext ?_ fun d hd₁ hd₂ => ?_
    · simp [h.betweenRanks_size, h.fromRanks_size]
    have hd : d < n := by simpa [h.fromRanks_size] using hd₁
    rw [Array.getElem_map, Array.getElem_range]
    -- Convert RHS `rs.betweenRanks[d]` to `rs.betweenRanks.getD d #[]` BEFORE the inner
    -- Array.ext, so the inner bound `hs₂` doesn't carry a dependency on the unsubstituted
    -- `[d]` term (which would block subsequent rewrites with motive type-mismatch).
    rw [show rs.betweenRanks[d]'hd₂ = rs.betweenRanks.getD d #[] from Array.getElem_eq_getD _]
    refine Array.ext ?_ fun s hs₁ hs₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.betweenRanks_row_size d hd).symm
    have hs : s < n := by simpa using hs₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show (rs.betweenRanks.getD d #[])[s]'hs₂ = (rs.betweenRanks.getD d #[]).getD s #[] from
        Array.getElem_eq_getD _]
    refine Array.ext ?_ fun e he₁ he₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.betweenRanks_cell_size d hd s hs).symm
    have he : e < n := by simpa using he₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show ((rs.betweenRanks.getD d #[]).getD s #[])[e]'he₂
          = ((rs.betweenRanks.getD d #[]).getD s #[]).getD e 0 from Array.getElem_eq_getD _]
    rw [show permNat σ⁻¹ s = (σ⁻¹ ⟨s, hs⟩).val from permNat_of_lt hs,
        show permNat σ⁻¹ e = (σ⁻¹ ⟨e, he⟩).val from permNat_of_lt he]
    exact (h.betweenRanks_inv d hd ⟨s, hs⟩ ⟨e, he⟩).symm
  · -- fromRanks equality. Same pattern as above without the third level.
    refine Array.ext ?_ fun d hd₁ hd₂ => ?_
    · simp [h.fromRanks_size]
    have hd : d < n := by simpa [h.fromRanks_size] using hd₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show rs.fromRanks[d]'hd₂ = rs.fromRanks.getD d #[] from Array.getElem_eq_getD _]
    refine Array.ext ?_ fun s hs₁ hs₂ => ?_
    · simp only [Array.size_map, Array.size_range]
      exact (h.fromRanks_row_size d hd).symm
    have hs : s < n := by simpa using hs₁
    rw [Array.getElem_map, Array.getElem_range]
    rw [show (rs.fromRanks.getD d #[])[s]'hs₂ = (rs.fromRanks.getD d #[]).getD s 0 from
        Array.getElem_eq_getD _]
    rw [show permNat σ⁻¹ s = (σ⁻¹ ⟨s, hs⟩).val from permNat_of_lt hs]
    exact (h.fromRanks_inv d hd ⟨s, hs⟩).symm

/-- The five size facts about `calculatePathRankings`'s output: `betweenRanks` and
`fromRanks` have shapes `vc × vc × vc` and `vc × vc`. Proved via a single foldl invariant
on the algorithm body, using the `setBetween`/`set!` size-preservation lemmas above. -/
theorem calculatePathRankings_size_inv {vc : Nat} (state : PathState vc)
    (vts : Array VertexType) :
    let rs := calculatePathRankings state vts
    rs.betweenRanks.size = vc ∧
    rs.fromRanks.size = vc ∧
    (∀ d : Nat, d < vc → (rs.fromRanks.getD d #[]).size = vc) ∧
    (∀ d : Nat, d < vc → (rs.betweenRanks.getD d #[]).size = vc) ∧
    (∀ d s : Nat, d < vc → s < vc →
      ((rs.betweenRanks.getD d #[]).getD s #[]).size = vc) := by
  unfold calculatePathRankings
  -- Define a combined size invariant on the foldl accumulator (b, f).
  suffices haux : ∀ (l : List Nat)
      (start : Array (Array (Array Nat)) × Array (Array Nat)),
      (start.1.size = vc ∧ start.2.size = vc ∧
       (∀ d : Nat, d < vc → (start.2.getD d #[]).size = vc) ∧
       (∀ d : Nat, d < vc → (start.1.getD d #[]).size = vc) ∧
       (∀ d s : Nat, d < vc → s < vc → ((start.1.getD d #[]).getD s #[]).size = vc)) →
      let acc := l.foldl (fun accumulated depth =>
          let (currentBetween, currentFrom) := accumulated
          let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
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
          (updatedBetween, updatedFrom)) start
      acc.1.size = vc ∧ acc.2.size = vc ∧
      (∀ d : Nat, d < vc → (acc.2.getD d #[]).size = vc) ∧
      (∀ d : Nat, d < vc → (acc.1.getD d #[]).size = vc) ∧
      (∀ d s : Nat, d < vc → s < vc → ((acc.1.getD d #[]).getD s #[]).size = vc) by
    -- Apply with the empty initial accumulator.
    have h_init : (((Array.range vc).map fun _ => (Array.range vc).map fun _ =>
                    (Array.range vc).map fun _ : Nat => (0 : Nat)).size = vc ∧
                   ((Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).size = vc ∧
                   (∀ d : Nat, d < vc → (((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).size = vc) ∧
                   (∀ d : Nat, d < vc → (((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).size = vc) ∧
                   (∀ d s : Nat, d < vc → s < vc → ((((Array.range vc).map fun _ =>
                     (Array.range vc).map fun _ => (Array.range vc).map fun _ : Nat => (0 : Nat)).getD d #[]).getD s #[]).size = vc)) := by
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro d hd
        simp [hd]
      · intro d hd
        simp [hd]
      · intro d s hd hs
        simp [hd, hs]
    exact haux _ _ h_init
  -- Foldl invariant proof.
  intro l
  induction l with
  | nil => intros _ h; exact h
  | cons x xs ih =>
    intros start hstart
    rw [List.foldl_cons]
    apply ih
    obtain ⟨b, f⟩ := start
    obtain ⟨h_b_size, h_f_size, h_f_row, h_b_row, h_b_cell⟩ := hstart
    simp only [] at h_b_size h_f_size h_f_row h_b_row h_b_cell ⊢
    -- Inner fold over assignRanks updates `b` via `setBetween` — preserves between sizes.
    -- We state the inner-b lemma without an outer `let acc'` so that `exact`/`apply`
    -- unifies the universal variable `l'` with the specific assignRanks-output list in
    -- the goal.
    suffices h_inner_b : ∀ (l' : List ((PathsBetween vc) × Nat))
        (acc : Array (Array (Array Nat))),
        acc.size = vc → (∀ d : Nat, d < vc → (acc.getD d #[]).size = vc) →
        (∀ d s : Nat, d < vc → s < vc → ((acc.getD d #[]).getD s #[]).size = vc) →
        (l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc x pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) acc).size = vc ∧
        (∀ d : Nat, d < vc → ((l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc x pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) acc).getD d #[]).size = vc) ∧
        (∀ d s : Nat, d < vc → s < vc →
          (((l'.foldl (fun (betweenAcc : Array (Array (Array Nat))) item =>
            let (pathBetween, rank) := item
            setBetween betweenAcc x pathBetween.startVertexIndex.val
              pathBetween.endVertexIndex.val rank) acc).getD d #[]).getD s #[]).size = vc) by
      suffices h_inner_f : ∀ (l' : List ((PathsFrom vc) × Nat)) (acc : Array (Array Nat)),
          acc.size = vc → (∀ d : Nat, d < vc → (acc.getD d #[]).size = vc) →
          (l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
            let (pathFrom, rank) := item
            let depthSlice := fromAcc.getD x #[]
            fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).size = vc ∧
          (∀ d : Nat, d < vc → ((l'.foldl (fun (fromAcc : Array (Array Nat)) item =>
            let (pathFrom, rank) := item
            let depthSlice := fromAcc.getD x #[]
            fromAcc.set! x (depthSlice.set! pathFrom.startVertexIndex.val rank)) acc).getD d #[]).size = vc) by
        exact ⟨(h_inner_b _ b h_b_size h_b_row h_b_cell).1,
               (h_inner_f _ f h_f_size h_f_row).1,
               (h_inner_f _ f h_f_size h_f_row).2,
               (h_inner_b _ b h_b_size h_b_row h_b_cell).2.1,
               (h_inner_b _ b h_b_size h_b_row h_b_cell).2.2⟩
      -- Prove h_inner_f.
      intro l' acc h_size h_row
      induction l' generalizing acc with
      | nil => exact ⟨h_size, h_row⟩
      | cons y ys ih_inner =>
        rw [List.foldl_cons]
        obtain ⟨pathFrom, rank⟩ := y
        apply ih_inner
        · simp [Array.set!_eq_setIfInBounds, h_size]
        · intro d hd
          rw [from_set_getD_size]
          exact h_row d hd
    -- Prove h_inner_b.
    intro l' acc h_size h_row h_cell
    induction l' generalizing acc with
    | nil => exact ⟨h_size, h_row, h_cell⟩
    | cons y ys ih_inner =>
      rw [List.foldl_cons]
      obtain ⟨pathBetween, rank⟩ := y
      apply ih_inner
      · rw [setBetween_size]; exact h_size
      · intro d hd; rw [setBetween_getD_size]; exact h_row d hd
      · intro d s hd hs; rw [setBetween_getD_getD_size]; exact h_cell d s hd hs


end Graph
