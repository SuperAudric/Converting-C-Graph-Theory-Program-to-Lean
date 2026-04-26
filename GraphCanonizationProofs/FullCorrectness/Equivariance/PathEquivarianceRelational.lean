import FullCorrectness.Equivariance.PathEquivariance

/-!
# Stage B σ-equivariance — relational form  (`FullCorrectness.Equivariance.PathEquivarianceRelational`)

The fixed-point form of Stage B (in `PathEquivariance.lean`) says:

  σ ∈ Aut G  ∧  vts σ-INVARIANT  ⟹  `RankState.permute σ rs = rs`

But `runFrom_VtsInvariant_eq` (in `Tiebreak.lean`) needs the *relational* form:

  σ ∈ Aut G, ANY vts:
  `calculatePathRankings (initializePaths G) (σ · vts)
     = RankState.permute σ (calculatePathRankings (initializePaths G) vts)`

These are not the same. The fixed-point form is the diagonal special case
`vts₁ = vts₂ = vts`; the relational form covers two arbitrary σ-related typing arrays.

## Plan

The strategy mirrors the proof of `calculatePathRankings_σInvariant` but tracks a
*relation* between two parallel computations rather than σ-invariance of one. The
overall structure is a foldl induction over depths with a relational invariant.

The cascade of supporting lemmas to lift:

1. **Compare-function relational equivariance** (here, this file):
   - `comparePathSegments_σ_relational` : LHS uses `(σ·vts, σ·br)` on `(σ·p, σ·q)`,
     RHS uses `(vts, br)` on `(p, q)`. No σ-INV hypothesis on `vts` or `br`.
   - `comparePathsBetween_σ_relational`, `comparePathsFrom_σ_relational` similar.
2. **Chain σ-equivariance** (planned; analogous to `setBetween_chain_σInvariant`
   and `set_chain_σInvariant` but relational).
3. **assignList σ-equivariance** (planned; analogous to
   `from_assignList_σ_rank_closure` / `between_assignList_σ_rank_closure` but
   relational).
4. **Body step** (planned): the body of `calculatePathRankings`'s depth foldl
   transports the relational invariant.
5. **Stage B-rel** (planned): foldl induction giving the final relational equality.

This file currently stops at step 1 — the foundational compare lemmas.

## σ-action on `vts` and `br`

We do NOT introduce dedicated `σ · vts` / `σ · br` definitions, since those would
require additional lemmas about how they project to `getD`. Instead we use the
**hypothesis-form** action: a relational hypothesis like

  `∀ v, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0`

precisely captures `vts₂ = σ · vts₁` at the `getD` level we need. This matches the
hypothesis form used in `Tiebreak.lean`'s `runFrom_VtsInvariant_eq` (via
`VtsInvariant`-style relations between two arrays).
-/

namespace Graph

variable {n : Nat}

/-! ### Relational compare equivariance

These are the relational analogues of `comparePathSegments_σ_equivariant`,
`comparePathsBetween_σ_equivariant`, and `comparePathsFrom_σ_equivariant`. The
fixed-point lemmas are recovered as the diagonal special case `vts₁ = vts₂` and
`br₁ = br₂` (under which the relational hypotheses collapse to σ-INV). -/

/-- `comparePathSegments` is σ-equivariant under σ-related typing/rank functions.
This is a strict generalization of `comparePathSegments_σ_equivariant`: when
`vts₁ = vts₂ = vts` and `br₁ = br₂ = br`, the relational hypotheses collapse to
the σ-INV hypotheses of the fixed-point form. -/
theorem comparePathSegments_σ_relational
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin vc, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin vc,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (p q : PathSegment vc) :
    comparePathSegments vts₂ br₂ (PathSegment.permute σ p) (PathSegment.permute σ q)
    = comparePathSegments vts₁ br₁ p q := by
  cases p with
  | bottom xVI =>
    cases q with
    | bottom yVI =>
      show compare (vts₂.getD (σ xVI).val 0) (vts₂.getD (σ yVI).val 0)
         = compare (vts₁.getD xVI.val 0) (vts₁.getD yVI.val 0)
      rw [hvts_rel xVI, hvts_rel yVI]
    | inner _ _ _ _ =>
      rfl
  | inner xe xd xs xend =>
    cases q with
    | bottom _ =>
      rfl
    | inner ye yd ys yend =>
      show (let xRank := br₂ xd (σ xs).val (σ xend).val
            let yRank := br₂ yd (σ ys).val (σ yend).val
            if xRank != yRank then compare yRank xRank
            else if xe != ye then compare ye xe else .eq)
        = (let xRank := br₁ xd xs.val xend.val
           let yRank := br₁ yd ys.val yend.val
           if xRank != yRank then compare yRank xRank
           else if xe != ye then compare ye xe else .eq)
      rw [hbr_rel xd xs xend, hbr_rel yd ys yend]

/-! ### Relational `sortBy` / `orderInsensitiveListCmp` machinery

The fixed-point form's `sortBy_map_pointwise` / `orderInsensitiveListCmp_map_pointwise`
use a single `cmp`. The relational form switches `cmp` when going through the σ-image:
sorting `L.map f` by `cmp₂` equals (sorting `L` by `cmp₁`) mapped by `f`, when
`cmp₂ (f a) (f b) = cmp₁ a b` pointwise. -/

/-- Pointwise relational `insertSorted_map`: only requires the relational
`cmp₂ (f a) (f b) = cmp₁ a b` hypothesis pointwise on `b ∈ L`. -/
private theorem insertSorted_map_pointwise_relational {α : Type}
    (f : α → α) (cmp₁ cmp₂ : α → α → Ordering)
    (a : α) (L : List α)
    (h : ∀ b ∈ L, cmp₂ (f a) (f b) = cmp₁ a b) :
    insertSorted cmp₂ (f a) (L.map f) = (insertSorted cmp₁ a L).map f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    show insertSorted cmp₂ (f a) (f b :: L.map f) = (insertSorted cmp₁ a (b :: L)).map f
    show (if cmp₂ (f a) (f b) != .gt then f a :: f b :: L.map f
          else f b :: insertSorted cmp₂ (f a) (L.map f))
       = (if cmp₁ a b != .gt then a :: b :: L else b :: insertSorted cmp₁ a L).map f
    rw [h b List.mem_cons_self]
    by_cases hc : cmp₁ a b != .gt
    · simp [hc]
    · simp [hc, ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- Pointwise relational `sortBy_map`: only requires the relational
`cmp₂ (f a) (f b) = cmp₁ a b` hypothesis pointwise on `a, b ∈ L`. -/
theorem sortBy_map_pointwise_relational {α : Type}
    (f : α → α) (cmp₁ cmp₂ : α → α → Ordering)
    (L : List α)
    (h : ∀ a ∈ L, ∀ b ∈ L, cmp₂ (f a) (f b) = cmp₁ a b) :
    sortBy cmp₂ (L.map f) = (sortBy cmp₁ L).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show insertSorted cmp₂ (f a) (sortBy cmp₂ (L.map f))
       = (insertSorted cmp₁ a (sortBy cmp₁ L)).map f
    have h_L : ∀ x ∈ L, ∀ y ∈ L, cmp₂ (f x) (f y) = cmp₁ x y := fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [ih h_L]
    have h_a : ∀ b ∈ sortBy cmp₁ L, cmp₂ (f a) (f b) = cmp₁ a b := fun b hb =>
      h a List.mem_cons_self b
        (List.mem_cons_of_mem _ ((sortBy_perm cmp₁ L).mem_iff.mp hb))
    exact insertSorted_map_pointwise_relational f cmp₁ cmp₂ a (sortBy cmp₁ L) h_a

/-- Pointwise relational `orderInsensitiveListCmp_map`: when
`cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L₁ ++ L₂`, then mapping both lists by `f`
swaps the comparison function from `cmp₁` to `cmp₂`. This is the key step lifting
σ-relational compare equivariance from `PathSegment` to `PathsBetween`/`PathsFrom`. -/
theorem orderInsensitiveListCmp_map_pointwise_relational {α : Type}
    (f : α → α) (cmp₁ cmp₂ : α → α → Ordering)
    (L₁ L₂ : List α)
    (h : ∀ a ∈ L₁ ++ L₂, ∀ b ∈ L₁ ++ L₂, cmp₂ (f a) (f b) = cmp₁ a b) :
    orderInsensitiveListCmp cmp₂ (L₁.map f) (L₂.map f)
    = orderInsensitiveListCmp cmp₁ L₁ L₂ := by
  -- Decompose h into per-list and cross-list conditions.
  have h₁ : ∀ a ∈ L₁, ∀ b ∈ L₁, cmp₂ (f a) (f b) = cmp₁ a b := fun a ha b hb =>
    h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have h₂ : ∀ a ∈ L₂, ∀ b ∈ L₂, cmp₂ (f a) (f b) = cmp₁ a b := fun a ha b hb =>
    h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  unfold orderInsensitiveListCmp
  simp only [List.length_map]
  by_cases hLen : L₁.length = L₂.length
  · simp only [hLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [sortBy_map_pointwise_relational f cmp₁ cmp₂ L₁ h₁,
        sortBy_map_pointwise_relational f cmp₁ cmp₂ L₂ h₂]
    rw [show ((sortBy cmp₁ L₁).map f).zip ((sortBy cmp₁ L₂).map f)
          = ((sortBy cmp₁ L₁).zip (sortBy cmp₁ L₂)).map (fun (x, y) => (f x, f y)) by
        rw [List.zip_map_right, List.zip_map_left, List.map_map]
        congr]
    rw [List.foldl_map]
    -- Apply pointwise foldl_congr: only need cmp₂ (f x) (f y) = cmp₁ x y for pairs in
    -- the zip.
    have h_foldl : ∀ (M : List (α × α)) (init : Ordering),
        (∀ p ∈ M, cmp₂ (f p.1) (f p.2) = cmp₁ p.1 p.2) →
        M.foldl (fun (currentOrder : Ordering) (p : α × α) =>
                   if (currentOrder != Ordering.eq) = true then currentOrder
                   else cmp₂ (f p.1) (f p.2)) init
          = M.foldl (fun (currentOrder : Ordering) (p : α × α) =>
                       if (currentOrder != Ordering.eq) = true then currentOrder
                       else cmp₁ p.1 p.2) init := by
      intro M
      induction M with
      | nil => intros _ _; rfl
      | cons p M ih =>
        intros init h_M
        rw [List.foldl_cons, List.foldl_cons]
        rw [show (if (init != Ordering.eq) = true then init else cmp₂ (f p.1) (f p.2))
              = (if (init != Ordering.eq) = true then init else cmp₁ p.1 p.2) by
            split_ifs <;> simp [h_M p List.mem_cons_self]]
        apply ih
        intros q hq
        exact h_M q (List.mem_cons_of_mem _ hq)
    apply h_foldl
    intros p hp
    have hp_left' : p.1 ∈ L₁ := (sortBy_perm cmp₁ L₁).mem_iff.mp (List.of_mem_zip hp).1
    have hp_right' : p.2 ∈ L₂ := (sortBy_perm cmp₁ L₂).mem_iff.mp (List.of_mem_zip hp).2
    exact h p.1 (List.mem_append_left _ hp_left') p.2 (List.mem_append_right _ hp_right')
  · simp [hLen]

/-- `comparePathsBetween` is σ-equivariant under σ-related typing/rank functions.
This is a strict generalization of `comparePathsBetween_σ_equivariant`: when
`vts₁ = vts₂` and `br₁ = br₂` the relational hypotheses collapse to σ-INV. -/
theorem comparePathsBetween_σ_relational
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin vc, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin vc,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (p₁ p₂ : PathsBetween vc)
    (h_len₁ : p₁.depth > 0 → p₁.connectedSubPaths.length = vc)
    (h_len₂ : p₂.depth > 0 → p₂.connectedSubPaths.length = vc) :
    comparePathsBetween vts₂ br₂ (p₁.permute σ) (p₂.permute σ)
    = comparePathsBetween vts₁ br₁ p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂ with
  | 0, _, p₁', _, _, _ =>
    -- `PathsBetween 0` is uninhabited (`endVertexIndex : Fin 0`), so the case is vacuous.
    exact p₁'.endVertexIndex.elim0
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂ =>
    -- Unfold both sides.
    show (if vts₂.getD (σ p₁.endVertexIndex).val 0 != vts₂.getD (σ p₂.endVertexIndex).val 0 then
            compare (vts₂.getD (σ p₁.endVertexIndex).val 0) (vts₂.getD (σ p₂.endVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathSegments vts₂ br₂)
                 (PathsBetween.permute σ p₁).connectedSubPaths
                 (PathsBetween.permute σ p₂).connectedSubPaths)
       = (if vts₁.getD p₁.endVertexIndex.val 0 != vts₁.getD p₂.endVertexIndex.val 0 then
            compare (vts₁.getD p₁.endVertexIndex.val 0) (vts₁.getD p₂.endVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathSegments vts₁ br₁)
                 p₁.connectedSubPaths p₂.connectedSubPaths)
    rw [hvts_rel p₁.endVertexIndex, hvts_rel p₂.endVertexIndex]
    split
    · rfl
    · -- else branch: OILC over connectedSubPaths.
      have h_perm₁ := PathsBetween_permute_connectedSubPaths_perm σ p₁ h_len₁
      have h_perm₂ := PathsBetween_permute_connectedSubPaths_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathSegments_total_preorder (vc := k+1) vts₂ br₂
      rw [orderInsensitiveListCmp_perm (comparePathSegments vts₂ br₂)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathSegments_equivCompat vts₂ br₂) _ _ _ _ h_perm₁ h_perm₂]
      -- Now both sides have OILC over `(L.map f) (L'.map f)`, with cmp₂ vs. cmp₁;
      -- discharge via `orderInsensitiveListCmp_map_pointwise_relational`.
      apply orderInsensitiveListCmp_map_pointwise_relational
        (PathSegment.permute σ) (comparePathSegments vts₁ br₁) (comparePathSegments vts₂ br₂)
        p₁.connectedSubPaths p₂.connectedSubPaths
      intros a _ b _
      exact comparePathSegments_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel a b

/-- `comparePathsFrom` is σ-equivariant under σ-related typing/rank functions.
This is a strict generalization of `comparePathsFrom_σ_equivariant`. -/
theorem comparePathsFrom_σ_relational
    {vc : Nat} (σ : Equiv.Perm (Fin vc))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin vc, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin vc,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (p₁ p₂ : PathsFrom vc)
    (h_len₁ : p₁.pathsToVertex.length = vc)
    (h_len₂ : p₂.pathsToVertex.length = vc)
    (h_inner_len₁ : ∀ q ∈ p₁.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc)
    (h_inner_len₂ : ∀ q ∈ p₂.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = vc) :
    comparePathsFrom vts₂ br₂ (p₁.permute σ) (p₂.permute σ)
    = comparePathsFrom vts₁ br₁ p₁ p₂ := by
  match vc, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ with
  | 0, _, p₁', _, _, _, _, _ =>
    -- `PathsFrom 0` is uninhabited (`startVertexIndex : Fin 0`), so the case is vacuous.
    exact p₁'.startVertexIndex.elim0
  | k + 1, σ, p₁, p₂, h_len₁, h_len₂, h_inner_len₁, h_inner_len₂ =>
    show (if vts₂.getD (σ p₁.startVertexIndex).val 0 != vts₂.getD (σ p₂.startVertexIndex).val 0 then
            compare (vts₂.getD (σ p₁.startVertexIndex).val 0) (vts₂.getD (σ p₂.startVertexIndex).val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts₂ br₂)
                 (PathsFrom.permute σ p₁).pathsToVertex
                 (PathsFrom.permute σ p₂).pathsToVertex)
       = (if vts₁.getD p₁.startVertexIndex.val 0 != vts₁.getD p₂.startVertexIndex.val 0 then
            compare (vts₁.getD p₁.startVertexIndex.val 0) (vts₁.getD p₂.startVertexIndex.val 0)
          else orderInsensitiveListCmp (comparePathsBetween vts₁ br₁)
                 p₁.pathsToVertex p₂.pathsToVertex)
    rw [hvts_rel p₁.startVertexIndex, hvts_rel p₂.startVertexIndex]
    split
    · rfl
    · have h_perm₁ := PathsFrom_permute_pathsToVertex_perm σ p₁ h_len₁
      have h_perm₂ := PathsFrom_permute_pathsToVertex_perm σ p₂ h_len₂
      obtain ⟨h_refl, h_antisym₁, h_antisym₂, h_trans⟩ :=
        comparePathsBetween_total_preorder (vc := k+1) vts₂ br₂
      rw [orderInsensitiveListCmp_perm (comparePathsBetween vts₂ br₂)
            h_refl h_antisym₁ h_antisym₂ h_trans
            (comparePathsBetween_equivCompat vts₂ br₂) _ _ _ _ h_perm₁ h_perm₂]
      apply orderInsensitiveListCmp_map_pointwise_relational
        (PathsBetween.permute σ) (comparePathsBetween vts₁ br₁) (comparePathsBetween vts₂ br₂)
        p₁.pathsToVertex p₂.pathsToVertex
      intros p hp q hq
      have hp_len : p.depth > 0 → p.connectedSubPaths.length = k + 1 := fun hp_d =>
        match List.mem_append.mp hp with
        | Or.inl hp_in => h_inner_len₁ p hp_in hp_d
        | Or.inr hp_in => h_inner_len₂ p hp_in hp_d
      have hq_len : q.depth > 0 → q.connectedSubPaths.length = k + 1 := fun hq_d =>
        match List.mem_append.mp hq with
        | Or.inl hq_in => h_inner_len₁ q hq_in hq_d
        | Or.inr hq_in => h_inner_len₂ q hq_in hq_d
      exact comparePathsBetween_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel p q hp_len hq_len

end Graph
