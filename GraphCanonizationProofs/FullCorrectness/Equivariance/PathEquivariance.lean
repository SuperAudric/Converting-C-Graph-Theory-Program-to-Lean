import FullCorrectness.Equivariance.ComparePathSegments
import FullCorrectness.Equivariance.RankStateInvariants
import FullCorrectness.Equivariance.StageA

/-!
# σ-equivariance of path comparisons and Stage B  (`FullCorrectness.Equivariance.PathEquivariance`)

Proves that `comparePathSegments`, `comparePathsBetween`, `comparePathsFrom` are
σ-equivariant under σ-invariant typing/rank functions, and that `PathsBetween`/`PathsFrom`
permute actions produce `List.Perm`-related outputs.

Assembles Stage B: `calculatePathRankings_Aut_equivariant` follows from
`calculatePathRankings_RankState_invariant` (which needs the two `_inv` sorry'd lemmas
below) composed with Stage A + `σ ∈ Aut G`.

## Sorry status
- `calculatePathRankings_fromRanks_inv` : `sorry` — deep fold-level σ-invariance; requires
  foldl induction on the depth loop plus σ-equivariance of sortBy + assignRanks.
- `calculatePathRankings_betweenRanks_inv` : `sorry` — companion to the above; proved by
  shared foldl induction.
-/

namespace Graph

variable {n : Nat}

-- `comparePathSegments_equivCompat` was moved to `Equivariance.ComparePathSegments`
-- so it can be used by `comparePathsBetween_total_preorder` (the .eq-bilateral compat
-- lemma is needed by the `_trans` lifter on `orderInsensitiveListCmp`).

/-- `orderInsensitiveListCmp` is invariant under `map`-ping both lists by an
`f` that preserves the comparison. This handles the depth=0 branch of
`PathsBetween.permute` (where `connectedSubPaths` is just `.map (PathSegment.permute σ)`). -/
theorem orderInsensitiveListCmp_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (L₁ L₂ : List α) :
    orderInsensitiveListCmp cmp (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp L₁ L₂ := by
  unfold orderInsensitiveListCmp
  simp only [List.length_map]
  by_cases hLen : L₁.length = L₂.length
  · simp only [hLen]
    rw [sortBy_map f cmp h L₁, sortBy_map f cmp h L₂]
    -- Convert the zip-of-maps into a map-of-zip, then push the map through `foldl` and
    -- collapse `cmp (f x) (f y)` to `cmp x y` via `h`.
    rw [show ((sortBy cmp L₁).map f).zip ((sortBy cmp L₂).map f)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map (fun (x, y) => (f x, f y)) by
        rw [List.zip_map_right, List.zip_map_left, List.map_map]
        congr]
    rw [List.foldl_map]
    -- The two foldl functions agree pointwise (by h); rewrite by function equality.
    have hfn : (fun (x : Ordering) (y : α × α) =>
                  if (x != Ordering.eq) = true then x
                  else cmp ((fun (p : α × α) => (f p.1, f p.2)) y).1
                            ((fun (p : α × α) => (f p.1, f p.2)) y).2)
             = (fun (currentOrder : Ordering) (x : α × α) =>
                  if (currentOrder != Ordering.eq) = true then currentOrder
                  else cmp x.1 x.2) := by
      funext x y
      simp [h y.1 y.2]
    rw [hfn]
  · simp [hLen]

/-- Pointwise variant of `insertSorted_map`: only requires `cmp (f a) (f b) = cmp a b`
for `b ∈ L`. -/
private theorem insertSorted_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (a : α) (L : List α) (h : ∀ b ∈ L, cmp (f a) (f b) = cmp a b) :
    insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    show insertSorted cmp (f a) (f b :: L.map f) = (insertSorted cmp a (b :: L)).map f
    show (if cmp (f a) (f b) != .gt then f a :: f b :: L.map f
          else f b :: insertSorted cmp (f a) (L.map f))
       = (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).map f
    rw [h b (List.mem_cons_self)]
    by_cases hc : cmp a b != .gt
    · simp [hc]
    · simp [hc, ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- Pointwise variant of `sortBy_map`: only requires `cmp (f a) (f b) = cmp a b` for
`a, b ∈ L`. -/
private theorem sortBy_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (L : List α) (h : ∀ a ∈ L, ∀ b ∈ L, cmp (f a) (f b) = cmp a b) :
    sortBy cmp (L.map f) = (sortBy cmp L).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show insertSorted cmp (f a) (sortBy cmp (L.map f))
       = (insertSorted cmp a (sortBy cmp L)).map f
    have h_L : ∀ x ∈ L, ∀ y ∈ L, cmp (f x) (f y) = cmp x y := fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [ih h_L]
    have h_a : ∀ b ∈ sortBy cmp L, cmp (f a) (f b) = cmp a b := fun b hb =>
      h a (List.mem_cons_self) b
        (List.mem_cons_of_mem _ ((sortBy_perm cmp L).mem_iff.mp hb))
    exact insertSorted_map_pointwise f cmp a (sortBy cmp L) h_a

/-- Pointwise `foldl` congruence: if `f` and `g` agree on all `(acc, a)` pairs where
`a ∈ L`, then their folds agree. -/
private theorem foldl_congr_mem {α β : Type} {f g : β → α → β} {L : List α} {init : β}
    (h : ∀ acc : β, ∀ a ∈ L, f acc a = g acc a) :
    L.foldl f init = L.foldl g init := by
  induction L generalizing init with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldl_cons, List.foldl_cons, h init a List.mem_cons_self]
    apply ih
    intros acc b hb
    exact h acc b (List.mem_cons_of_mem _ hb)

/-- Pointwise variant of `orderInsensitiveListCmp_map`: only requires `cmp (f a) (f b) = cmp a b`
for `a, b ∈ L₁ ++ L₂`. This is what's needed for `comparePathsFrom_σ_equivariant` where
the inner `comparePathsBetween_σ_equivariant` only applies to elements satisfying per-element
length conditions. -/
theorem orderInsensitiveListCmp_map_pointwise {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (L₁ L₂ : List α)
    (h : ∀ a ∈ L₁ ++ L₂, ∀ b ∈ L₁ ++ L₂, cmp (f a) (f b) = cmp a b) :
    orderInsensitiveListCmp cmp (L₁.map f) (L₂.map f) = orderInsensitiveListCmp cmp L₁ L₂ := by
  -- Decompose h into per-list and cross-list conditions.
  have h₁ : ∀ a ∈ L₁, ∀ b ∈ L₁, cmp (f a) (f b) = cmp a b := fun a ha b hb =>
    h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have h₂ : ∀ a ∈ L₂, ∀ b ∈ L₂, cmp (f a) (f b) = cmp a b := fun a ha b hb =>
    h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  unfold orderInsensitiveListCmp
  simp only [List.length_map]
  by_cases hLen : L₁.length = L₂.length
  · simp only [hLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [sortBy_map_pointwise f cmp L₁ h₁, sortBy_map_pointwise f cmp L₂ h₂]
    rw [show ((sortBy cmp L₁).map f).zip ((sortBy cmp L₂).map f)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map (fun (x, y) => (f x, f y)) by
        rw [List.zip_map_right, List.zip_map_left, List.map_map]
        congr]
    rw [List.foldl_map]
    -- Apply pointwise foldl_congr: only need cmp respect for pairs in the zip.
    apply foldl_congr_mem
    intros acc p hp
    have hp_left' : p.1 ∈ L₁ := (sortBy_perm cmp L₁).mem_iff.mp (List.of_mem_zip hp).1
    have hp_right' : p.2 ∈ L₂ := (sortBy_perm cmp L₂).mem_iff.mp (List.of_mem_zip hp).2
    have h_p : cmp (f p.1) (f p.2) = cmp p.1 p.2 :=
      h p.1 (List.mem_append_left _ hp_left') p.2 (List.mem_append_right _ hp_right')
    simp [h_p]
  · simp [hLen]

/-- `comparePathSegments` is σ-equivariant when both the typing array and the
`betweenRanks` function are σ-invariant. -/
theorem comparePathSegments_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p q : PathSegment vc) :
    comparePathSegments vts br (PathSegment.permute σ p) (PathSegment.permute σ q)
    = comparePathSegments vts br p q := by
  cases p with
  | bottom xVI =>
    cases q with
    | bottom yVI =>
      -- LHS: compare (vts.getD (σ xVI).val 0) (vts.getD (σ yVI).val 0)
      -- RHS: compare (vts.getD xVI.val 0) (vts.getD yVI.val 0)
      -- σ-invariance of vts gives equality at each position.
      show compare (vts.getD (σ xVI).val 0) (vts.getD (σ yVI).val 0)
         = compare (vts.getD xVI.val 0) (vts.getD yVI.val 0)
      rw [hvts xVI, hvts yVI]
    | inner _ _ _ _ =>
      -- Mixed bottom/inner hits the panic branch; both sides equal.
      rfl
  | inner xe xd xs xend =>
    cases q with
    | bottom _ =>
      rfl
    | inner ye yd ys yend =>
      -- LHS compares inner segments with `(σ xs, σ xend)` and `(σ ys, σ yend)` endpoints.
      -- σ-invariance of `br` gives the same `xRank`/`yRank` values as in the RHS.
      show (let xRank := br xd (σ xs).val (σ xend).val
            let yRank := br yd (σ ys).val (σ yend).val
            if xRank != yRank then compare yRank xRank
            else if xe != ye then compare ye xe else .eq)
        = (let xRank := br xd xs.val xend.val
           let yRank := br yd ys.val yend.val
           if xRank != yRank then compare yRank xRank
           else if xe != ye then compare ye xe else .eq)
      rw [hbr xd xs xend, hbr yd ys yend]

/-! ### `PathsBetween` / `PathsFrom` permute → multiset Perm

When `PathsBetween.permute σ` (depth>0 branch) reindexes `connectedSubPaths` via `σ⁻¹`
on positions, the result is a `Perm` of `connectedSubPaths.map (PathSegment.permute σ)`
by `Equiv.Perm.ofFn_comp_perm`. Same for `PathsFrom.permute σ`'s `pathsToVertex`. -/

/-- General reindex-perm lemma: if `L : List α` has length `n` and `σ : Equiv.Perm (Fin n)`,
then the list obtained by σ-reindexing `L.map act` is a `Perm` of `L.map act`. This captures
the depth>0 branch of `PathsBetween.permute`/`PathsFrom.permute` in a σ-agnostic way. -/
private theorem map_reindex_perm {α : Type} {n : Nat}
    (σ : Equiv.Perm (Fin n)) (L : List α) (h_len : L.length = n)
    (act : α → α) (def_val : α) :
    ((List.finRange n).map fun i : Fin n => act (L.getD (σ i).val def_val)).Perm
      (L.map act) := by
  -- Rewrite getD to getElem using h_len and (σ i).isLt.
  have h_eq : (List.finRange n).map (fun i : Fin n => act (L.getD (σ i).val def_val))
            = (List.finRange n).map (fun i : Fin n =>
                act (L[(σ i).val]'(h_len ▸ (σ i).isLt))) := by
    apply List.map_congr_left
    intro i _
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h_len ▸ (σ i).isLt),
        Option.getD_some]
  rw [h_eq]
  -- Convert to List.ofFn and apply Equiv.Perm.ofFn_comp_perm.
  rw [← List.ofFn_eq_map]
  -- Now: List.ofFn (fun i => act L[(σ i).val]'_) ~ L.map act.
  -- View as List.ofFn (f ∘ σ) where f i := act L[i.val]'_.
  rw [show (fun i : Fin n => act (L[(σ i).val]'(h_len ▸ (σ i).isLt)))
        = (fun i : Fin n => act (L[i.val]'(h_len ▸ i.isLt))) ∘ σ from by
      funext i; rfl]
  refine (Equiv.Perm.ofFn_comp_perm σ _).trans ?_
  -- Goal: List.ofFn (fun i => act L[i.val]'_) ~ L.map act.
  rw [List.ofFn_eq_map]
  -- Now: (finRange n).map (fun i : Fin n => act L[i.val]'_) ~ L.map act.
  -- Prove element-wise equality.
  apply List.Perm.of_eq
  apply List.ext_getElem
  · simp [h_len]
  intros j h₁ h₂
  simp [List.getElem_map, List.getElem_finRange]

/-- For `n = k + 1` and `p.connectedSubPaths` of length `k+1` (or depth = 0), the
permuted `connectedSubPaths` is a `Perm` of the σ-mapped original. -/
theorem PathsBetween_permute_connectedSubPaths_perm
    {vc : Nat} (σ : Equiv.Perm (Fin vc)) (p : PathsBetween vc)
    (h_len : p.depth > 0 → p.connectedSubPaths.length = vc) :
    (p.permute σ).connectedSubPaths.Perm (p.connectedSubPaths.map (PathSegment.permute σ)) := by
  match vc, σ, p, h_len with
  | 0, _, p, _ =>
    -- PathSegment 0 is uninhabited, so p.connectedSubPaths must be [].
    show p.connectedSubPaths.Perm (p.connectedSubPaths.map _)
    cases h_cs : p.connectedSubPaths with
    | nil => simp
    | cons a _ =>
      cases a with
      | bottom v => exact v.elim0
      | inner _ _ s _ => exact s.elim0
  | k + 1, σ, p, h_len =>
    by_cases hd : p.depth = 0
    · -- d = 0 case: directly equal (no reindexing).
      have h_eq : (PathsBetween.permute σ p).connectedSubPaths
                = p.connectedSubPaths.map (PathSegment.permute σ) := by
        show (if p.depth = 0 then p.connectedSubPaths.map (PathSegment.permute σ) else _) = _
        rw [if_pos hd]
      rw [h_eq]
    · -- d > 0: reindexed. Use map_reindex_perm with σ := σ⁻¹.
      have h_len' : p.connectedSubPaths.length = k + 1 := h_len (Nat.pos_of_ne_zero hd)
      have h_eq : (PathsBetween.permute σ p).connectedSubPaths
                = (List.finRange (k+1)).map fun i : Fin (k+1) =>
                    PathSegment.permute σ
                      (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (PathSegment.bottom 0)) := by
        show (if p.depth = 0 then _ else _) = _
        rw [if_neg hd]
      rw [h_eq]
      -- Replace `permNat σ⁻¹ i.val` with `(σ⁻¹ i).val` to match `map_reindex_perm`.
      have h_rw : (fun i : Fin (k+1) =>
          PathSegment.permute σ (p.connectedSubPaths.getD (permNat σ⁻¹ i.val) (PathSegment.bottom 0)))
        = (fun i : Fin (k+1) =>
          PathSegment.permute σ (p.connectedSubPaths.getD (σ⁻¹ i).val (PathSegment.bottom 0))) := by
        funext i
        rw [permNat_of_lt i.isLt]
      rw [h_rw]
      exact map_reindex_perm σ⁻¹ p.connectedSubPaths h_len'
        (PathSegment.permute σ) (PathSegment.bottom 0)

/-- Analogous Perm helper for `PathsFrom.permute`'s `pathsToVertex`. -/
theorem PathsFrom_permute_pathsToVertex_perm
    {vc : Nat} (σ : Equiv.Perm (Fin vc)) (p : PathsFrom vc)
    (h_len : p.pathsToVertex.length = vc) :
    (p.permute σ).pathsToVertex.Perm (p.pathsToVertex.map (PathsBetween.permute σ)) := by
  match vc, σ, p, h_len with
  | 0, _, p, h_len =>
    -- For n=0, PathsFrom.permute is identity. We need p.pathsToVertex = [].
    -- Actually, since pathsToVertex : List (PathsBetween 0) and PathsBetween has fields
    -- startVertexIndex endVertexIndex : Fin 0 (uninhabited), pathsToVertex can only be [].
    show p.pathsToVertex.Perm (p.pathsToVertex.map _)
    cases h_pv : p.pathsToVertex with
    | nil => simp
    | cons a _ => exact a.startVertexIndex.elim0
  | k + 1, σ, p, h_len =>
    -- PathsFrom.permute's pathsToVertex is always reindexed (no depth branching).
    have h_eq : (PathsFrom.permute σ p).pathsToVertex
              = (List.finRange (k+1)).map fun i : Fin (k+1) =>
                  PathsBetween.permute σ
                    (p.pathsToVertex.getD (permNat σ⁻¹ i.val)
                      { depth := 0, startVertexIndex := 0, endVertexIndex := 0,
                        connectedSubPaths := [] }) := rfl
    rw [h_eq]
    have h_rw : (fun i : Fin (k+1) =>
        PathsBetween.permute σ
          (p.pathsToVertex.getD (permNat σ⁻¹ i.val)
            ({ depth := 0, startVertexIndex := 0, endVertexIndex := 0,
               connectedSubPaths := [] } : PathsBetween (k+1))))
      = (fun i : Fin (k+1) =>
        PathsBetween.permute σ
          (p.pathsToVertex.getD (σ⁻¹ i).val
            ({ depth := 0, startVertexIndex := 0, endVertexIndex := 0,
               connectedSubPaths := [] } : PathsBetween (k+1)))) := by
      funext i
      rw [permNat_of_lt i.isLt]
    rw [h_rw]
    exact map_reindex_perm σ⁻¹ p.pathsToVertex h_len
      (PathsBetween.permute σ)
      { depth := 0, startVertexIndex := 0, endVertexIndex := 0, connectedSubPaths := [] }

/-- `comparePathsBetween` is σ-equivariant under σ-invariant `vts`/`br` and `connectedSubPaths`-
length normalization (which holds in `initializePaths G` for `depth>0`). -/
theorem comparePathsBetween_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p₁ p₂ : PathsBetween vc)
    (h_len₁ : p₁.depth > 0 → p₁.connectedSubPaths.length = vc)
    (h_len₂ : p₂.depth > 0 → p₂.connectedSubPaths.length = vc) :
    comparePathsBetween vts br (p₁.permute σ) (p₂.permute σ)
    = comparePathsBetween vts br p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂ with
  | 0, _, _, _, _, _ =>
    -- For n = 0, `PathsBetween.permute` is the identity definitionally.
    rfl
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂ =>
    -- Unfold comparePathsBetween + PathsBetween.permute (succ branch).
    show (if vts.getD (σ p₁.endVertexIndex).val 0 != vts.getD (σ p₂.endVertexIndex).val 0 then
            compare (vts.getD (σ p₁.endVertexIndex).val 0) (vts.getD (σ p₂.endVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 (PathsBetween.permute σ p₁).connectedSubPaths
                 (PathsBetween.permute σ p₂).connectedSubPaths)
       = (if vts.getD p₁.endVertexIndex.val 0 != vts.getD p₂.endVertexIndex.val 0 then
            compare (vts.getD p₁.endVertexIndex.val 0) (vts.getD p₂.endVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 p₁.connectedSubPaths p₂.connectedSubPaths)
    rw [hvts p₁.endVertexIndex, hvts p₂.endVertexIndex]
    split
    · rfl
    · -- else branch: orderInsensitiveListCmp on connectedSubPaths.
      have h_perm₁ := PathsBetween_permute_connectedSubPaths_perm σ p₁ h_len₁
      have h_perm₂ := PathsBetween_permute_connectedSubPaths_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathSegments_total_preorder (vc := k+1) vts br
      rw [orderInsensitiveListCmp_perm (comparePathSegments vts br)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathSegments_equivCompat vts br) _ _ _ _ h_perm₁ h_perm₂]
      exact orderInsensitiveListCmp_map (PathSegment.permute σ) (comparePathSegments vts br)
            (fun a b => comparePathSegments_σ_equivariant σ vts hvts br hbr a b)
            p₁.connectedSubPaths p₂.connectedSubPaths

/-- `comparePathsBetween` respects equivalence bilaterally (the EquivCompat condition
needed for `orderInsensitiveListCmp_perm` at the `comparePathsFrom` level).
The proof mirrors `comparePathsBetween_total_preorder`: case on whether the
end-vertex-types match, then use `orderInsensitiveListCmp_equivCompat` for the
equal-prefix branch (with `comparePathSegments_equivCompat` as the inner `h_compat`). -/
theorem comparePathsBetween_equivCompat
    {vc : Nat} (vts : Array VertexType) (br : Nat → Nat → Nat → Nat)
    (p₁ p₂ : PathsBetween vc)
    (h : comparePathsBetween vts br p₁ p₂ = Ordering.eq)
    (r : PathsBetween vc) :
    comparePathsBetween vts br p₁ r = comparePathsBetween vts br p₂ r ∧
    comparePathsBetween vts br r p₁ = comparePathsBetween vts br r p₂ := by
  have h_seg_compat := comparePathSegments_equivCompat (vc := vc) vts br
  have h' : (let xEndType := vts.getD p₁.endVertexIndex.val 0
             let yEndType := vts.getD p₂.endVertexIndex.val 0
             if xEndType != yEndType then compare xEndType yEndType
             else orderInsensitiveListCmp (comparePathSegments vts br)
                    p₁.connectedSubPaths p₂.connectedSubPaths) = Ordering.eq := h
  by_cases h_endTy_eq : vts.getD p₁.endVertexIndex.val 0 = vts.getD p₂.endVertexIndex.val 0
  · have h_bne_eq : (vts.getD p₁.endVertexIndex.val 0 != vts.getD p₂.endVertexIndex.val 0) = false := by
      rw [h_endTy_eq]; exact bne_self_eq_false (a := vts.getD p₂.endVertexIndex.val 0)
    simp only [h_bne_eq, Bool.false_eq_true, ↓reduceIte] at h'
    obtain ⟨h_inner_left, h_inner_right⟩ := orderInsensitiveListCmp_equivCompat
      (comparePathSegments vts br) h_seg_compat
      p₁.connectedSubPaths p₂.connectedSubPaths h' r.connectedSubPaths
    refine ⟨?_, ?_⟩
    · show (let xEndType := vts.getD p₁.endVertexIndex.val 0
            let rEndType := vts.getD r.endVertexIndex.val 0
            if xEndType != rEndType then compare xEndType rEndType
            else orderInsensitiveListCmp (comparePathSegments vts br)
                   p₁.connectedSubPaths r.connectedSubPaths)
         = (let yEndType := vts.getD p₂.endVertexIndex.val 0
            let rEndType := vts.getD r.endVertexIndex.val 0
            if yEndType != rEndType then compare yEndType rEndType
            else orderInsensitiveListCmp (comparePathSegments vts br)
                   p₂.connectedSubPaths r.connectedSubPaths)
      rw [h_endTy_eq, h_inner_left]
    · show (let rEndType := vts.getD r.endVertexIndex.val 0
            let xEndType := vts.getD p₁.endVertexIndex.val 0
            if rEndType != xEndType then compare rEndType xEndType
            else orderInsensitiveListCmp (comparePathSegments vts br)
                   r.connectedSubPaths p₁.connectedSubPaths)
         = (let rEndType := vts.getD r.endVertexIndex.val 0
            let yEndType := vts.getD p₂.endVertexIndex.val 0
            if rEndType != yEndType then compare rEndType yEndType
            else orderInsensitiveListCmp (comparePathSegments vts br)
                   r.connectedSubPaths p₂.connectedSubPaths)
      rw [h_endTy_eq, h_inner_right]
  · have h_bne_ne : (vts.getD p₁.endVertexIndex.val 0 != vts.getD p₂.endVertexIndex.val 0) = true :=
      bne_iff_ne.mpr h_endTy_eq
    simp only [h_bne_ne, ↓reduceIte] at h'
    exact absurd (compare_eq_iff_eq.mp h') h_endTy_eq

/-- `comparePathsFrom` is σ-equivariant under σ-invariant `vts`/`br` and `pathsToVertex`-
length normalization (which holds in `initializePaths G`). -/
theorem comparePathsFrom_σ_equivariant
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts : Array VertexType)
    (hvts : ∀ v : Fin vc, vts.getD (σ v).val 0 = vts.getD v.val 0)
    (br : Nat → Nat → Nat → Nat)
    (hbr : ∀ d : Nat, ∀ s e : Fin vc, br d (σ s).val (σ e).val = br d s.val e.val)
    (p₁ p₂ : PathsFrom vc)
    (h_len₁ : p₁.pathsToVertex.length = vc)
    (h_len₂ : p₂.pathsToVertex.length = vc)
    (h_inner_len₁ : ∀ q ∈ p₁.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc)
    (h_inner_len₂ : ∀ q ∈ p₂.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc) :
    comparePathsFrom vts br (p₁.permute σ) (p₂.permute σ)
    = comparePathsFrom vts br p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ with
  | 0, _, _, _, _, _, _, _ =>
    rfl
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ =>
    show (if vts.getD (σ p₁.startVertexIndex).val 0 != vts.getD (σ p₂.startVertexIndex).val 0 then
            compare (vts.getD (σ p₁.startVertexIndex).val 0) (vts.getD (σ p₂.startVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 (PathsFrom.permute σ p₁).pathsToVertex
                 (PathsFrom.permute σ p₂).pathsToVertex)
       = (if vts.getD p₁.startVertexIndex.val 0 != vts.getD p₂.startVertexIndex.val 0 then
            compare (vts.getD p₁.startVertexIndex.val 0) (vts.getD p₂.startVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts br)
                 p₁.pathsToVertex p₂.pathsToVertex)
    rw [hvts p₁.startVertexIndex, hvts p₂.startVertexIndex]
    split
    · rfl
    · have h_perm₁ := PathsFrom_permute_pathsToVertex_perm σ p₁ h_len₁
      have h_perm₂ := PathsFrom_permute_pathsToVertex_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathsBetween_total_preorder (vc := k+1) vts br
      rw [orderInsensitiveListCmp_perm (comparePathsBetween vts br)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathsBetween_equivCompat vts br) _ _ _ _ h_perm₁ h_perm₂]
      -- Apply pointwise map lemma: comparePathsBetween_σ_equivariant for each pair in the
      -- combined list, using per-element h_inner_len conditions.
      apply orderInsensitiveListCmp_map_pointwise (PathsBetween.permute σ)
        (comparePathsBetween vts br) p₁.pathsToVertex p₂.pathsToVertex
      intro p hp q hq
      have hp_len : p.depth > 0 → p.connectedSubPaths.length = k + 1 := fun hp_d =>
        match List.mem_append.mp hp with
        | Or.inl hp_in => h_inner_len₁ p hp_in hp_d
        | Or.inr hp_in => h_inner_len₂ p hp_in hp_d
      have hq_len : q.depth > 0 → q.connectedSubPaths.length = k + 1 := fun hq_d =>
        match List.mem_append.mp hq with
        | Or.inl hq_in => h_inner_len₁ q hq_in hq_d
        | Or.inr hq_in => h_inner_len₂ q hq_in hq_d
      exact comparePathsBetween_σ_equivariant σ vts hvts br hbr p q hp_len hq_len

/-! ### Plan for `calculatePathRankings_fromRanks_inv` and `_betweenRanks_inv`

**Strategy**: Foldl invariant on the depth loop (mirroring `calculatePathRankings_size_inv`).
Track σ-invariance of cell values across both `betweenRanks` and `fromRanks` simultaneously
(the body updates both in tandem).

**Proof tree**:
```
calculatePathRankings_σInvariant_combined  (deep helper, foldl invariant)
  ├── init_σ_invariant         (trivial: all zeros)
  └── body_preserves_σ_inv     (the deep step; uses Aut G + σ-inv vts)
        │
        ├── betweenRankFn σ-invariant from cell-σ-inv of currentBetween
        ├── compareBetween σ-equivariant  (via comparePathsBetween_σ_equivariant ✅)
        ├── pathsAtDepth σ-permuted by σ  (via Stage A: initializePaths_Aut_equivariant ✅)
        ├── allBetween σ-permuted  (concat over PathsFrom_permute_pathsToVertex_perm ✅)
        ├── assignList σ-equivariantly permuted with rank-preservation
        │     ├── sortBy with σ-equivariant cmp  (sortBy_map_pointwise ✅)
        │     └── assignRanks rank-preservation across σ-Perm-related sorted lists
        ├── setBetween chain over σ-Perm assignList preserves σ-inv of currentBetween
        ├── updatedBetweenFn σ-invariant (analogous to step 1)
        ├── compareFrom σ-equivariant  (via comparePathsFrom_σ_equivariant ✅)
        └── set! chain (for fromRanks) over σ-Perm assignList preserves σ-inv
```

**Sub-lemmas needed** (some new, some existing):
- `betweenRankFn_σ_inv_from_cells` — small: cell-σ-inv → function-σ-inv.
- `pathsAtDepth_initializePaths_σInv` — small: corollary of Stage A.
- `assignRanks_σ_equivariant_perm` — generic; rank preservation across σ-related sorted lists.
- `setBetween_chain_σInvariant`, `set!_chain_σInvariant` — chain preserves σ-inv.
- `body_preserves_σ_inv` — wraps the substeps above.
- `calculatePathRankings_σInvariant_combined` — foldl invariant.

Both target theorems then follow by extracting the corresponding cell-level fact. -/

/-- **Helper 1 (small)**: cell-level σ-invariance of a 3D table lifts to a σ-invariant
function (the natural betweenRankFn projection). -/
theorem betweenRankFn_σ_inv_from_cells
    (σ : Equiv.Perm (Fin n)) (b : Array (Array (Array Nat)))
    (h_cell : ∀ d : Nat, d < n → ∀ s e : Fin n,
      ((b.getD d #[]).getD s.val #[]).getD e.val 0
      = ((b.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) :
    ∀ d : Nat, d < n → ∀ s e : Fin n,
      (fun rankDepth rankStart rankEnd =>
          ((b.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0)
        d (σ s).val (σ e).val
      = (fun rankDepth rankStart rankEnd =>
          ((b.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0)
        d s.val e.val := by
  intro d hd s e
  -- Apply h_cell at (d, σ s, σ e); the σ⁻¹ (σ x) terms simplify to x.
  have h := h_cell d hd (σ s) (σ e)
  have h_inv_s : σ⁻¹ (σ s) = s := by simp
  have h_inv_e : σ⁻¹ (σ e) = e := by simp
  rw [h_inv_s, h_inv_e] at h
  show ((b.getD d #[]).getD (σ s).val #[]).getD (σ e).val 0
     = ((b.getD d #[]).getD s.val #[]).getD e.val 0
  exact h

/-- **Helper 2 (small)**: for σ ∈ Aut G, `initializePaths G` is fixed by `PathState.permute σ`.
Direct corollary of `initializePaths_Aut_equivariant`. -/
theorem initializePaths_σInv_via_Aut
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G) :
    initializePaths G = PathState.permute σ (initializePaths G) := by
  have hG : G.permute σ = G := hσ
  have h_stageA := initializePaths_Aut_equivariant G σ
  rw [hG] at h_stageA
  exact h_stageA

/-! ### Chain σ-invariance lemmas

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
`Perm`-related-sorted lemma). -/

/-- **Sub-lemma `set!_chain_σInvariant`** (TODO): the `set!` chain on `fromRanks`
preserves σ-invariance, given the σ-rank-closure of the assignList.

**Status**: stated; proof sketched; deep details TBD via chain-inversion infrastructure. -/
private theorem set_chain_σInvariant
    (σ : Equiv.Perm (Fin n)) (currentFrom : Array (Array Nat))
    (h_size : currentFrom.size = n)
    (h_row_size : ∀ d : Nat, d < n → (currentFrom.getD d #[]).size = n)
    (h_curr_inv : ∀ d : Nat, d < n → ∀ s : Fin n,
      (currentFrom.getD d #[]).getD s.val 0
      = (currentFrom.getD d #[]).getD (σ⁻¹ s).val 0)
    (depth : Nat) (h_depth : depth < n)
    (assignList : List (PathsFrom n × Nat))
    (h_unique_starts : ∀ s : Fin n, ∃! item ∈ assignList, item.1.startVertexIndex.val = s.val)
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
  sorry

/-- **Sub-lemma `setBetween_chain_σInvariant`** (TODO): the `setBetween` chain on
`betweenRanks` preserves σ-invariance, given the σ-rank-closure of the assignList.

**Status**: stated; proof sketched; deep details TBD. -/
private theorem setBetween_chain_σInvariant
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
    (h_unique_pairs : ∀ s e : Fin n, ∃! item ∈ assignList,
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
  sorry

/-- The σ-invariance of `fromRanks` values in `calculatePathRankings`'s output.
Part of the deep Stage B content; requires foldl induction on the depth loop combined with
σ-equivariance of the compare/sort/rank assignment at each step. -/
theorem calculatePathRankings_fromRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (_hd : d < n) (s : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    (rs.fromRanks.getD d #[]).getD s.val 0
    = (rs.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0 := by
  sorry

/-- The σ-invariance of `betweenRanks` values in `calculatePathRankings`'s output.
Companion to `calculatePathRankings_fromRanks_inv`; the two are proved by a shared foldl
induction (sharing the same σ-invariance bookkeeping across the `betweenRanks`/`fromRanks`
pair, since each step updates both in tandem). -/
theorem calculatePathRankings_betweenRanks_inv
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (_hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0)
    (d : Nat) (_hd : d < n) (s e : Fin n) :
    let rs := calculatePathRankings (initializePaths G) vts
    ((rs.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
    = ((rs.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0 := by
  sorry

/-- The σ-invariance of `calculatePathRankings`'s output, given σ ∈ Aut G and σ-invariant
typing. Sizes are discharged by `calculatePathRankings_size_inv` (proved); the value
invariance comes from the two `_inv` theorems above. -/
theorem calculatePathRankings_σInvariant
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts : Array VertexType)
    (hvts : ∀ v : Fin n, vts.getD (σ v) 0 = vts.getD v 0) :
    RankState.σInvariant σ (calculatePathRankings (initializePaths G) vts) where
  fromRanks_size := calculatePathRankings_fromRanks_size _ _
  betweenRanks_size := (calculatePathRankings_size_inv (initializePaths G) vts).1
  fromRanks_row_size := fun d hd =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.1 d hd
  betweenRanks_row_size := fun d hd =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.2.1 d hd
  betweenRanks_cell_size := fun d hd s hs =>
    (calculatePathRankings_size_inv (initializePaths G) vts).2.2.2.2 d s hd hs
  fromRanks_inv := calculatePathRankings_fromRanks_inv G σ hσ vts hvts
  betweenRanks_inv := calculatePathRankings_betweenRanks_inv G σ hσ vts hvts

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
