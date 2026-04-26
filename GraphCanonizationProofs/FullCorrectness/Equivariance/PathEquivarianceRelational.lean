import FullCorrectness.Equivariance.PathEquivariance
import FullCorrectness.Equivariance.ChainSetInvariant

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

/-! ### Relational chain σ-equivariance

These are the relational analogues of `set_chain_σInvariant` /
`setBetween_chain_σInvariant`. The fixed-point lemmas are recovered as the diagonal
special case `cf₁ = cf₂` (resp. `cb₁ = cb₂`) and `assignList₁ = assignList₂`. -/

/-- Generic helper: in a list of `(Nat × Nat)` pairs with `Nodup` keys, two entries
sharing the same key have the same value. -/
private theorem nodup_keys_unique_value
    (L : List (Nat × Nat)) (k v₁ v₂ : Nat)
    (hND : (L.map (·.1)).Nodup)
    (h1 : (k, v₁) ∈ L) (h2 : (k, v₂) ∈ L) : v₁ = v₂ := by
  induction L with
  | nil => exact absurd h1 List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hND
    obtain ⟨h_hd_not_in, h_tl_nd⟩ := hND
    rcases List.mem_cons.mp h1 with h1 | h1
    · rcases List.mem_cons.mp h2 with h2 | h2
      · exact (Prod.mk.injEq _ _ _ _).mp (h1.trans h2.symm) |>.2
      · have h_hd_eq : hd.1 = k := by rw [← h1]
        exact absurd (List.mem_map.mpr ⟨(k, v₂), h2, rfl⟩)
          (h_hd_eq ▸ h_hd_not_in)
    · rcases List.mem_cons.mp h2 with h2 | h2
      · have h_hd_eq : hd.1 = k := by rw [← h2]
        exact absurd (List.mem_map.mpr ⟨(k, v₁), h1, rfl⟩)
          (h_hd_eq ▸ h_hd_not_in)
      · exact ih h_tl_nd h1 h2

/-- Generic helper: in a list of `(Nat × Nat × Nat)` triples with `Nodup` `(s, e)`-keys,
two entries sharing the same `(s, e)` have the same value. -/
private theorem nodup_pair_keys_unique_value
    (L : List (Nat × Nat × Nat)) (s' e' v₁ v₂ : Nat)
    (hND : (L.map (fun item => (item.1, item.2.1))).Nodup)
    (h1 : (s', e', v₁) ∈ L) (h2 : (s', e', v₂) ∈ L) : v₁ = v₂ := by
  induction L with
  | nil => exact absurd h1 List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hND
    obtain ⟨h_hd_not_in, h_tl_nd⟩ := hND
    rcases List.mem_cons.mp h1 with h1 | h1
    · rcases List.mem_cons.mp h2 with h2 | h2
      · have heq : (Prod.mk s' (Prod.mk e' v₁)) = (s', e', v₂) := h1.trans h2.symm
        exact (Prod.mk.injEq _ _ _ _).mp ((Prod.mk.injEq _ _ _ _).mp heq |>.2) |>.2
      · have h_hd_eq : (hd.1, hd.2.1) = (s', e') := by rw [← h1]
        exact absurd (List.mem_map.mpr ⟨(s', e', v₂), h2, rfl⟩)
          (h_hd_eq ▸ h_hd_not_in)
    · rcases List.mem_cons.mp h2 with h2 | h2
      · have h_hd_eq : (hd.1, hd.2.1) = (s', e') := by rw [← h2]
        exact absurd (List.mem_map.mpr ⟨(s', e', v₁), h1, rfl⟩)
          (h_hd_eq ▸ h_hd_not_in)
      · exact ih h_tl_nd h1 h2

/-- The chain of `set!`s on `fromAcc` preserves σ-relatedness when both inputs are
σ-related and the assignLists are σ-related (each item in `al₁` has a corresponding
σ-image in `al₂`). The fixed-point form `set_chain_σInvariant` is recovered with
`cf₁ = cf₂` and `al₁ = al₂` (with σ-rank-closure as `h_σ_rel`). -/
theorem set_chain_σRelated
    (σ : Equiv.Perm (Fin n))
    (cf₁ cf₂ : Array (Array Nat))
    (h_size₁ : cf₁.size = n) (h_size₂ : cf₂.size = n)
    (h_row_size₁ : ∀ d : Nat, d < n → (cf₁.getD d #[]).size = n)
    (h_row_size₂ : ∀ d : Nat, d < n → (cf₂.getD d #[]).size = n)
    (h_curr_rel : ∀ d : Nat, d < n → ∀ s : Fin n,
      (cf₂.getD d #[]).getD s.val 0
      = (cf₁.getD d #[]).getD (σ⁻¹ s).val 0)
    (depth : Nat) (h_depth : depth < n)
    (al₁ al₂ : List (PathsFrom n × Nat))
    (h_starts_perm₁ : (al₁.map (·.1.startVertexIndex.val)).Perm (List.range n))
    (h_starts_perm₂ : (al₂.map (·.1.startVertexIndex.val)).Perm (List.range n))
    (h_σ_rel : ∀ item₁ ∈ al₁, ∃ item₂ ∈ al₂,
      item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
      ∧ item₂.2 = item₁.2) :
    let chainStep := fun (fromAcc : Array (Array Nat)) (item : PathsFrom n × Nat) =>
      fromAcc.set! depth ((fromAcc.getD depth #[]).set! item.1.startVertexIndex.val item.2)
    let result₁ := al₁.foldl chainStep cf₁
    let result₂ := al₂.foldl chainStep cf₂
    result₁.size = n ∧ result₂.size = n ∧
    (∀ d : Nat, d < n → (result₁.getD d #[]).size = n) ∧
    (∀ d : Nat, d < n → (result₂.getD d #[]).size = n) ∧
    (∀ d : Nat, d < n → ∀ s : Fin n,
      (result₂.getD d #[]).getD s.val 0
      = (result₁.getD d #[]).getD (σ⁻¹ s).val 0) := by
  set chainStep := fun (fromAcc : Array (Array Nat)) (item : PathsFrom n × Nat) =>
    fromAcc.set! depth ((fromAcc.getD depth #[]).set! item.1.startVertexIndex.val item.2) with h_chainStep
  -- Sizes preserved.
  have h_result₁_size : (al₁.foldl chainStep cf₁).size = n := by
    rw [h_chainStep, set_chain_size_preserving cf₁ depth al₁]; exact h_size₁
  have h_result₂_size : (al₂.foldl chainStep cf₂).size = n := by
    rw [h_chainStep, set_chain_size_preserving cf₂ depth al₂]; exact h_size₂
  have h_result₁_row : ∀ d : Nat, d < n → ((al₁.foldl chainStep cf₁).getD d #[]).size = n := by
    intro d hd
    rw [h_chainStep]
    exact set_chain_row_size_preserving cf₁ depth al₁ d (h_row_size₁ d hd)
  have h_result₂_row : ∀ d : Nat, d < n → ((al₂.foldl chainStep cf₂).getD d #[]).size = n := by
    intro d hd
    rw [h_chainStep]
    exact set_chain_row_size_preserving cf₂ depth al₂ d (h_row_size₂ d hd)
  refine ⟨h_result₁_size, h_result₂_size, h_result₁_row, h_result₂_row, ?_⟩
  -- σ-relatedness of cells.
  intro d hd s
  by_cases h_eq : d = depth
  · -- d = depth: extract the depth-slice on both sides.
    have hd_depth : depth < n := h_eq ▸ hd
    rw [h_eq]
    have h_depth_in₁ : depth < cf₁.size := h_size₁ ▸ hd_depth
    have h_depth_in₂ : depth < cf₂.size := h_size₂ ▸ hd_depth
    -- Convert both LHS and RHS to a foldl on `(Nat × Nat)` pairs.
    rw [show al₂.foldl chainStep cf₂ = al₂.foldl
        (fun (fromAcc : Array (Array Nat)) item =>
          let (pathFrom, rank) := item
          let depthSlice := fromAcc.getD depth #[]
          fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) cf₂ from rfl]
    rw [show al₁.foldl chainStep cf₁ = al₁.foldl
        (fun (fromAcc : Array (Array Nat)) item =>
          let (pathFrom, rank) := item
          let depthSlice := fromAcc.getD depth #[]
          fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) cf₁ from rfl]
    rw [inner_fold_slice_at_depth al₂ cf₂ depth h_depth_in₂]
    rw [inner_fold_slice_at_depth al₁ cf₁ depth h_depth_in₁]
    rw [show al₂.foldl
            (fun (slice : Array Nat) (item : PathsFrom n × Nat) =>
              slice.set! item.1.startVertexIndex.val item.2)
            (cf₂.getD depth #[])
          = (al₂.map (fun item : PathsFrom n × Nat =>
                (item.1.startVertexIndex.val, item.2))).foldl
            (fun (slice : Array Nat) (item : Nat × Nat) => slice.set! item.1 item.2)
            (cf₂.getD depth #[]) from by rw [List.foldl_map]]
    rw [show al₁.foldl
            (fun (slice : Array Nat) (item : PathsFrom n × Nat) =>
              slice.set! item.1.startVertexIndex.val item.2)
            (cf₁.getD depth #[])
          = (al₁.map (fun item : PathsFrom n × Nat =>
                (item.1.startVertexIndex.val, item.2))).foldl
            (fun (slice : Array Nat) (item : Nat × Nat) => slice.set! item.1 item.2)
            (cf₁.getD depth #[]) from by rw [List.foldl_map]]
    set L₁ := al₁.map (fun item : PathsFrom n × Nat => (item.1.startVertexIndex.val, item.2))
      with hL₁_def
    set L₂ := al₂.map (fun item : PathsFrom n × Nat => (item.1.startVertexIndex.val, item.2))
      with hL₂_def
    -- Nodup of the start values.
    have h_keys_eq₁ : L₁.map (·.1) = al₁.map (·.1.startVertexIndex.val) := by
      rw [hL₁_def, List.map_map]; rfl
    have h_keys_eq₂ : L₂.map (·.1) = al₂.map (·.1.startVertexIndex.val) := by
      rw [hL₂_def, List.map_map]; rfl
    have h_nodup₁ : (L₁.map (·.1)).Nodup := by
      rw [h_keys_eq₁]; exact h_starts_perm₁.nodup_iff.mpr List.nodup_range
    have h_nodup₂ : (L₂.map (·.1)).Nodup := by
      rw [h_keys_eq₂]; exact h_starts_perm₂.nodup_iff.mpr List.nodup_range
    -- LHS: find unique entry in al₂ with start = s.val (via h_starts_perm₂).
    have h_s_in_starts₂ : s.val ∈ al₂.map (·.1.startVertexIndex.val) :=
      h_starts_perm₂.symm.mem_iff.mp (List.mem_range.mpr s.isLt)
    obtain ⟨item_s₂, h_item_s₂_in, h_item_s₂_start⟩ := List.mem_map.mp h_s_in_starts₂
    -- RHS: find unique entry in al₁ with start = (σ⁻¹ s).val (via h_starts_perm₁).
    have h_σs_in_starts₁ : (σ⁻¹ s).val ∈ al₁.map (·.1.startVertexIndex.val) :=
      h_starts_perm₁.symm.mem_iff.mp (List.mem_range.mpr (σ⁻¹ s).isLt)
    obtain ⟨item_σs₁, h_item_σs₁_in, h_item_σs₁_start⟩ := List.mem_map.mp h_σs_in_starts₁
    -- Pair targets.
    have h_target_s₂_in : (s.val, item_s₂.2) ∈ L₂ := by
      rw [hL₂_def]
      refine List.mem_map.mpr ⟨item_s₂, h_item_s₂_in, ?_⟩
      show (item_s₂.1.startVertexIndex.val, item_s₂.2) = (s.val, item_s₂.2)
      rw [h_item_s₂_start]
    have h_target_σs₁_in : ((σ⁻¹ s).val, item_σs₁.2) ∈ L₁ := by
      rw [hL₁_def]
      refine List.mem_map.mpr ⟨item_σs₁, h_item_σs₁_in, ?_⟩
      show (item_σs₁.1.startVertexIndex.val, item_σs₁.2) = ((σ⁻¹ s).val, item_σs₁.2)
      rw [h_item_σs₁_start]
    have h_slice_size₁ : (cf₁.getD depth #[]).size = n := h_row_size₁ depth hd_depth
    have h_slice_size₂ : (cf₂.getD depth #[]).size = n := h_row_size₂ depth hd_depth
    have h_target_s₂_bound : s.val < (cf₂.getD depth #[]).size := by
      rw [h_slice_size₂]; exact s.isLt
    have h_target_σs₁_bound : (σ⁻¹ s).val < (cf₁.getD depth #[]).size := by
      rw [h_slice_size₁]; exact (σ⁻¹ s).isLt
    -- Apply chain-at-target-nodup.
    have h_cell_s₂ :
        Array.getD (List.foldl (fun (slice : Array Nat) (item : Nat × Nat) =>
            slice.set! item.1 item.2) (cf₂.getD depth #[]) L₂) s.val 0
        = item_s₂.2 :=
      array_set_chain_at_target_nodup (cf₂.getD depth #[]) L₂ (s.val, item_s₂.2) 0
        h_target_s₂_in h_nodup₂ h_target_s₂_bound
    have h_cell_σs₁ :
        Array.getD (List.foldl (fun (slice : Array Nat) (item : Nat × Nat) =>
            slice.set! item.1 item.2) (cf₁.getD depth #[]) L₁) (σ⁻¹ s).val 0
        = item_σs₁.2 :=
      array_set_chain_at_target_nodup (cf₁.getD depth #[]) L₁ ((σ⁻¹ s).val, item_σs₁.2) 0
        h_target_σs₁_in h_nodup₁ h_target_σs₁_bound
    show Array.getD (List.foldl _ (cf₂.getD depth #[]) L₂) s.val 0
       = Array.getD (List.foldl _ (cf₁.getD depth #[]) L₁) (σ⁻¹ s).val 0
    rw [h_cell_s₂, h_cell_σs₁]
    -- Need: item_s₂.2 = item_σs₁.2. Use h_σ_rel applied to item_σs₁.
    obtain ⟨item₂', h_item₂'_in, h_item₂'_start, h_item₂'_rank⟩ := h_σ_rel item_σs₁ h_item_σs₁_in
    -- item_σs₁.startVertexIndex.val = (σ⁻¹ s).val ⟹ item_σs₁.startVertexIndex = σ⁻¹ s.
    have h_σs_eq_fin : item_σs₁.1.startVertexIndex = σ⁻¹ s := by
      apply Fin.ext; exact h_item_σs₁_start
    rw [h_σs_eq_fin] at h_item₂'_start
    have h_σσ : σ (σ⁻¹ s) = s := by simp
    rw [h_σσ] at h_item₂'_start
    -- (item₂'.startVertexIndex.val, item₂'.2) = (s.val, item₂'.2) ∈ L₂.
    have h_item₂'_pair_in : (item₂'.1.startVertexIndex.val, item₂'.2) ∈ L₂ := by
      rw [hL₂_def]
      exact List.mem_map.mpr ⟨item₂', h_item₂'_in, rfl⟩
    rw [h_item₂'_start] at h_item₂'_pair_in
    -- Both (s.val, item_s₂.2) and (s.val, item₂'.2) are in L₂; Nodup keys ⟹ ranks equal.
    have h_v_eq : item_s₂.2 = item₂'.2 :=
      nodup_keys_unique_value L₂ s.val item_s₂.2 item₂'.2 h_nodup₂ h_target_s₂_in h_item₂'_pair_in
    rw [h_v_eq, h_item₂'_rank]
  · -- d ≠ depth: cells unchanged on both sides.
    have h_dep_ne_d : depth ≠ d := fun h => h_eq h.symm
    have h_lhs : (al₂.foldl chainStep cf₂).getD d #[] = cf₂.getD d #[] :=
      inner_fold_other_depth_unchanged al₂ cf₂ depth d h_dep_ne_d
    have h_rhs : (al₁.foldl chainStep cf₁).getD d #[] = cf₁.getD d #[] :=
      inner_fold_other_depth_unchanged al₁ cf₁ depth d h_dep_ne_d
    rw [h_lhs, h_rhs]
    exact h_curr_rel d hd s

/-- The 2D chain (`setBetween` chain) preserves σ-relatedness when both inputs are
σ-related and the assignLists are σ-related (each item in `al₁` has a corresponding
σ-image in `al₂` with σ-shifted (s, e) coords and same rank). The fixed-point form
`setBetween_chain_σInvariant` is recovered with `cb₁ = cb₂` and `al₁ = al₂`. -/
theorem setBetween_chain_σRelated
    (σ : Equiv.Perm (Fin n))
    (cb₁ cb₂ : Array (Array (Array Nat)))
    (h_size₁ : cb₁.size = n) (h_size₂ : cb₂.size = n)
    (h_row_size₁ : ∀ d : Nat, d < n → (cb₁.getD d #[]).size = n)
    (h_row_size₂ : ∀ d : Nat, d < n → (cb₂.getD d #[]).size = n)
    (h_cell_size₁ : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      ((cb₁.getD d #[]).getD s #[]).size = n)
    (h_cell_size₂ : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      ((cb₂.getD d #[]).getD s #[]).size = n)
    (h_curr_rel : ∀ d : Nat, d < n → ∀ s e : Fin n,
      ((cb₂.getD d #[]).getD s.val #[]).getD e.val 0
      = ((cb₁.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0)
    (depth : Nat) (h_depth : depth < n)
    (al₁ al₂ : List (PathsBetween n × Nat))
    (h_pairs_nodup₁ : (al₁.map (fun item =>
        (item.1.startVertexIndex.val, item.1.endVertexIndex.val))).Nodup)
    (h_pairs_nodup₂ : (al₂.map (fun item =>
        (item.1.startVertexIndex.val, item.1.endVertexIndex.val))).Nodup)
    (h_pairs_complete₁ : ∀ s e : Fin n, ∃ item ∈ al₁,
        item.1.startVertexIndex.val = s.val ∧ item.1.endVertexIndex.val = e.val)
    (h_pairs_complete₂ : ∀ s e : Fin n, ∃ item ∈ al₂,
        item.1.startVertexIndex.val = s.val ∧ item.1.endVertexIndex.val = e.val)
    (h_σ_rel : ∀ item₁ ∈ al₁, ∃ item₂ ∈ al₂,
      item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
      ∧ item₂.1.endVertexIndex.val = (σ item₁.1.endVertexIndex).val
      ∧ item₂.2 = item₁.2) :
    let chainStep := fun (betweenAcc : Array (Array (Array Nat))) (item : PathsBetween n × Nat) =>
      setBetween betweenAcc depth item.1.startVertexIndex.val item.1.endVertexIndex.val item.2
    let result₁ := al₁.foldl chainStep cb₁
    let result₂ := al₂.foldl chainStep cb₂
    result₁.size = n ∧ result₂.size = n ∧
    (∀ d : Nat, d < n → (result₁.getD d #[]).size = n) ∧
    (∀ d : Nat, d < n → (result₂.getD d #[]).size = n) ∧
    (∀ d : Nat, d < n → ∀ s : Nat, s < n → ((result₁.getD d #[]).getD s #[]).size = n) ∧
    (∀ d : Nat, d < n → ∀ s : Nat, s < n → ((result₂.getD d #[]).getD s #[]).size = n) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
      ((result₂.getD d #[]).getD s.val #[]).getD e.val 0
      = ((result₁.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  set chainStep := fun (betweenAcc : Array (Array (Array Nat))) (item : PathsBetween n × Nat) =>
    setBetween betweenAcc depth item.1.startVertexIndex.val item.1.endVertexIndex.val item.2
    with h_chainStep
  -- Sizes preserved.
  have h_result₁_size : (al₁.foldl chainStep cb₁).size = n := by
    rw [h_chainStep, setBetween_chain_size_preserving cb₁ depth al₁]; exact h_size₁
  have h_result₂_size : (al₂.foldl chainStep cb₂).size = n := by
    rw [h_chainStep, setBetween_chain_size_preserving cb₂ depth al₂]; exact h_size₂
  have h_result₁_row : ∀ d : Nat, d < n → ((al₁.foldl chainStep cb₁).getD d #[]).size = n := by
    intro d hd
    rw [h_chainStep]
    exact setBetween_chain_row_size_preserving cb₁ depth al₁ d (h_row_size₁ d hd)
  have h_result₂_row : ∀ d : Nat, d < n → ((al₂.foldl chainStep cb₂).getD d #[]).size = n := by
    intro d hd
    rw [h_chainStep]
    exact setBetween_chain_row_size_preserving cb₂ depth al₂ d (h_row_size₂ d hd)
  have h_result₁_cell : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      (((al₁.foldl chainStep cb₁).getD d #[]).getD s #[]).size = n := by
    intro d hd s hs
    rw [h_chainStep]
    exact setBetween_chain_cell_size_preserving cb₁ depth al₁ d s (h_cell_size₁ d hd s hs)
  have h_result₂_cell : ∀ d : Nat, d < n → ∀ s : Nat, s < n →
      (((al₂.foldl chainStep cb₂).getD d #[]).getD s #[]).size = n := by
    intro d hd s hs
    rw [h_chainStep]
    exact setBetween_chain_cell_size_preserving cb₂ depth al₂ d s (h_cell_size₂ d hd s hs)
  refine ⟨h_result₁_size, h_result₂_size, h_result₁_row, h_result₂_row,
          h_result₁_cell, h_result₂_cell, ?_⟩
  -- σ-relatedness of cells.
  intro d hd s e
  by_cases h_eq : d = depth
  · -- d = depth: 2D chain inversion on both sides.
    have hd_depth : depth < n := h_eq ▸ hd
    rw [h_eq]
    have h_depth_in₁ : depth < cb₁.size := h_size₁ ▸ hd_depth
    have h_depth_in₂ : depth < cb₂.size := h_size₂ ▸ hd_depth
    rw [show al₂.foldl chainStep cb₂ = al₂.foldl
        (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc depth pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) cb₂ from rfl]
    rw [show al₁.foldl chainStep cb₁ = al₁.foldl
        (fun (betweenAcc : Array (Array (Array Nat))) item =>
          let (pathBetween, rank) := item
          setBetween betweenAcc depth pathBetween.startVertexIndex.val
            pathBetween.endVertexIndex.val rank) cb₁ from rfl]
    rw [setBetween_fold_slice_at_depth al₂ cb₂ depth h_depth_in₂]
    rw [setBetween_fold_slice_at_depth al₁ cb₁ depth h_depth_in₁]
    rw [show al₂.foldl
            (fun (ds : Array (Array Nat)) (item : PathsBetween n × Nat) =>
              let s := item.1.startVertexIndex.val
              let e := item.1.endVertexIndex.val
              ds.set! s ((ds.getD s #[]).set! e item.2))
            (cb₂.getD depth #[])
          = (al₂.map (fun item : PathsBetween n × Nat =>
                (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2))).foldl
            (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
              ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
            (cb₂.getD depth #[]) from by rw [List.foldl_map]]
    rw [show al₁.foldl
            (fun (ds : Array (Array Nat)) (item : PathsBetween n × Nat) =>
              let s := item.1.startVertexIndex.val
              let e := item.1.endVertexIndex.val
              ds.set! s ((ds.getD s #[]).set! e item.2))
            (cb₁.getD depth #[])
          = (al₁.map (fun item : PathsBetween n × Nat =>
                (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2))).foldl
            (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
              ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
            (cb₁.getD depth #[]) from by rw [List.foldl_map]]
    set L₁ := al₁.map (fun item : PathsBetween n × Nat =>
      (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2)) with hL₁_def
    set L₂ := al₂.map (fun item : PathsBetween n × Nat =>
      (item.1.startVertexIndex.val, item.1.endVertexIndex.val, item.2)) with hL₂_def
    -- Nodup of (s, e) pairs in both.
    have h_keys_eq₁ : L₁.map (fun item => (item.1, item.2.1))
        = al₁.map (fun item => (item.1.startVertexIndex.val, item.1.endVertexIndex.val)) := by
      rw [hL₁_def, List.map_map]; rfl
    have h_keys_eq₂ : L₂.map (fun item => (item.1, item.2.1))
        = al₂.map (fun item => (item.1.startVertexIndex.val, item.1.endVertexIndex.val)) := by
      rw [hL₂_def, List.map_map]; rfl
    have h_nodup₁ : (L₁.map (fun item => (item.1, item.2.1))).Nodup := by
      rw [h_keys_eq₁]; exact h_pairs_nodup₁
    have h_nodup₂ : (L₂.map (fun item => (item.1, item.2.1))).Nodup := by
      rw [h_keys_eq₂]; exact h_pairs_nodup₂
    -- LHS: find unique entry in al₂ at (s, e).
    obtain ⟨item_se₂, h_item_se₂_in, h_item_se₂_start, h_item_se₂_end⟩ :=
      h_pairs_complete₂ s e
    -- RHS: find unique entry in al₁ at (σ⁻¹ s, σ⁻¹ e).
    obtain ⟨item_σse₁, h_item_σse₁_in, h_item_σse₁_start, h_item_σse₁_end⟩ :=
      h_pairs_complete₁ (σ⁻¹ s) (σ⁻¹ e)
    -- Triple targets.
    have h_target_se₂_in : (s.val, e.val, item_se₂.2) ∈ L₂ := by
      rw [hL₂_def]
      refine List.mem_map.mpr ⟨item_se₂, h_item_se₂_in, ?_⟩
      show (item_se₂.1.startVertexIndex.val, item_se₂.1.endVertexIndex.val, item_se₂.2)
         = (s.val, e.val, item_se₂.2)
      rw [h_item_se₂_start, h_item_se₂_end]
    have h_target_σse₁_in : ((σ⁻¹ s).val, (σ⁻¹ e).val, item_σse₁.2) ∈ L₁ := by
      rw [hL₁_def]
      refine List.mem_map.mpr ⟨item_σse₁, h_item_σse₁_in, ?_⟩
      show (item_σse₁.1.startVertexIndex.val, item_σse₁.1.endVertexIndex.val, item_σse₁.2)
         = ((σ⁻¹ s).val, (σ⁻¹ e).val, item_σse₁.2)
      rw [h_item_σse₁_start, h_item_σse₁_end]
    have h_slice_size₁ : (cb₁.getD depth #[]).size = n := h_row_size₁ depth hd_depth
    have h_slice_size₂ : (cb₂.getD depth #[]).size = n := h_row_size₂ depth hd_depth
    have h_inner_size_s₂ : ((cb₂.getD depth #[]).getD s.val #[]).size = n :=
      h_cell_size₂ depth hd_depth s.val s.isLt
    have h_inner_size_σs₁ : ((cb₁.getD depth #[]).getD (σ⁻¹ s).val #[]).size = n :=
      h_cell_size₁ depth hd_depth (σ⁻¹ s).val (σ⁻¹ s).isLt
    have h_target_se₂_outer_bound : s.val < (cb₂.getD depth #[]).size := by
      rw [h_slice_size₂]; exact s.isLt
    have h_target_σse₁_outer_bound : (σ⁻¹ s).val < (cb₁.getD depth #[]).size := by
      rw [h_slice_size₁]; exact (σ⁻¹ s).isLt
    have h_target_se₂_inner_bound : e.val < ((cb₂.getD depth #[]).getD s.val #[]).size := by
      rw [h_inner_size_s₂]; exact e.isLt
    have h_target_σse₁_inner_bound : (σ⁻¹ e).val < ((cb₁.getD depth #[]).getD (σ⁻¹ s).val #[]).size := by
      rw [h_inner_size_σs₁]; exact (σ⁻¹ e).isLt
    -- Apply chain-at-target on both.
    have h_cell_se₂ :
        Array.getD (Array.getD (List.foldl
          (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
            ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
          (cb₂.getD depth #[]) L₂) s.val #[]) e.val 0 = item_se₂.2 :=
      nested_set_chain_at_target_pair_nodup (cb₂.getD depth #[]) L₂ (s.val, e.val, item_se₂.2) 0
        h_target_se₂_in h_nodup₂ h_target_se₂_outer_bound h_target_se₂_inner_bound
    have h_cell_σse₁ :
        Array.getD (Array.getD (List.foldl
          (fun (ds : Array (Array Nat)) (item : Nat × Nat × Nat) =>
            ds.set! item.1 ((ds.getD item.1 #[]).set! item.2.1 item.2.2))
          (cb₁.getD depth #[]) L₁) (σ⁻¹ s).val #[]) (σ⁻¹ e).val 0 = item_σse₁.2 :=
      nested_set_chain_at_target_pair_nodup (cb₁.getD depth #[]) L₁
        ((σ⁻¹ s).val, (σ⁻¹ e).val, item_σse₁.2) 0
        h_target_σse₁_in h_nodup₁ h_target_σse₁_outer_bound h_target_σse₁_inner_bound
    show Array.getD (Array.getD (List.foldl _ (cb₂.getD depth #[]) L₂) s.val #[]) e.val 0
       = Array.getD (Array.getD (List.foldl _ (cb₁.getD depth #[]) L₁) (σ⁻¹ s).val #[]) (σ⁻¹ e).val 0
    rw [h_cell_se₂, h_cell_σse₁]
    -- Need: item_se₂.2 = item_σse₁.2. Use h_σ_rel applied to item_σse₁.
    obtain ⟨item₂', h_item₂'_in, h_item₂'_start, h_item₂'_end, h_item₂'_rank⟩ :=
      h_σ_rel item_σse₁ h_item_σse₁_in
    have h_σse_start_eq : item_σse₁.1.startVertexIndex = σ⁻¹ s := by
      apply Fin.ext; exact h_item_σse₁_start
    have h_σse_end_eq : item_σse₁.1.endVertexIndex = σ⁻¹ e := by
      apply Fin.ext; exact h_item_σse₁_end
    rw [h_σse_start_eq] at h_item₂'_start
    rw [h_σse_end_eq] at h_item₂'_end
    have h_σσ_s : σ (σ⁻¹ s) = s := by simp
    have h_σσ_e : σ (σ⁻¹ e) = e := by simp
    rw [h_σσ_s] at h_item₂'_start
    rw [h_σσ_e] at h_item₂'_end
    -- (item₂'.start.val, item₂'.end.val, item₂'.2) ∈ L₂.
    have h_item₂'_pair_in :
        (item₂'.1.startVertexIndex.val, item₂'.1.endVertexIndex.val, item₂'.2) ∈ L₂ := by
      rw [hL₂_def]
      exact List.mem_map.mpr ⟨item₂', h_item₂'_in, rfl⟩
    rw [h_item₂'_start, h_item₂'_end] at h_item₂'_pair_in
    -- Both (s.val, e.val, item_se₂.2) and (s.val, e.val, item₂'.2) ∈ L₂; Nodup keys ⟹ equal.
    have h_v_eq : item_se₂.2 = item₂'.2 :=
      nodup_pair_keys_unique_value L₂ s.val e.val item_se₂.2 item₂'.2 h_nodup₂
        h_target_se₂_in h_item₂'_pair_in
    rw [h_v_eq, h_item₂'_rank]
  · -- d ≠ depth: cells unchanged on both sides.
    have h_dep_ne_d : depth ≠ d := fun h => h_eq h.symm
    have h_lhs : (al₂.foldl chainStep cb₂).getD d #[] = cb₂.getD d #[] :=
      setBetween_fold_other_depth_unchanged al₂ cb₂ depth d h_dep_ne_d
    have h_rhs : (al₁.foldl chainStep cb₁).getD d #[] = cb₁.getD d #[] :=
      setBetween_fold_other_depth_unchanged al₁ cb₁ depth d h_dep_ne_d
    rw [h_lhs, h_rhs]
    exact h_curr_rel d hd s e

/-! ### Relational σ-rank-closure of `assignList`

The σ-rank-closure relational property: for σ-related `(vts₁, br₁)` and `(vts₂, br₂)`
and σ-fixed `state`, each item₁ in `assignList₁` has a corresponding σ-image item₂ in
`assignList₂` with the same rank.

**Strategy.** By `sortBy_map_pointwise_relational` and `assignRanks_map_relational`:

  `assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f))
    = (assignRanks cmp₁ (sortBy cmp₁ pathsAtDepth)).map (lift f)
    = (assignList₁).map (lift f)`

By state σ-fixedness, `pathsAtDepth.Perm (pathsAtDepth.map f)`, so `assignList₂` and
`(assignList₁).map (lift f)` are computed from `assignRanks cmp₂` of two `Perm`-equivalent
sorted lists. The (element, rank) multisets are equal — the rank of each element is
determined by its `cmp₂`-class position, independent of intra-class tie-breaking.

**Status: closed.** The position-by-position rank equality across two sorted
Perm-equivalent inputs is provided by `assignRanks_rank_eq_of_sorted_perm` (in
`ComparisonSort.lean`). The cross-list rank match for `q` (at position k₂ in `assignList₂`)
is then established via `assignRanks_rank_eq_within_eq_class` applied to `q` and
`(sortBy cmp₂ pathsAtDepth)[k₁]` (which lie in the same `cmp₂`-class by
`sortedPerm_class_eq`). -/

/-- The σ-image `f p := PathsFrom.permute σ p` of any element of `pathsAtDepth` (under
σ-fixed state) is itself in `pathsAtDepth`. This is the structural witness used in both
the σ-INV `from_assignList_σ_rank_closure` and its relational analogue below. -/
private theorem mem_pathsAtDepth_under_f
    (σ : Equiv.Perm (Fin n)) (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (p : PathsFrom n) (h_p_in : p ∈ (state.pathsOfLength.getD depth #[]).toList) :
    PathsFrom.permute σ p ∈ (state.pathsOfLength.getD depth #[]).toList := by
  -- Inner-array size = n via toList.length.
  have h_inner_size : (state.pathsOfLength.getD depth #[]).size = n := by
    rw [← Array.length_toList]; exact h_outer_len
  -- Locate p at some position in pathsAtDepth.
  obtain ⟨s_p, hs_p_lt, hs_p_eq⟩ := List.mem_iff_getElem.mp h_p_in
  have hs_p_lt_n : s_p < n := by rw [← h_outer_len]; exact hs_p_lt
  set s_fin : Fin n := ⟨s_p, hs_p_lt_n⟩
  -- The state's depth slice exists (depth < state.pathsOfLength.size).
  have h_depth_arr : depth < state.pathsOfLength.size := by
    by_contra h_not
    push_neg at h_not
    have h_arr_empty : state.pathsOfLength.getD depth #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_not, Option.getD_none]
    rw [h_arr_empty] at h_outer_len
    simp at h_outer_len
    omega
  have h_s_p_lt_arr : s_p < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_inner_size]; exact hs_p_lt_n
  have h_σs_lt_arr : (σ s_fin).val < (state.pathsOfLength.getD depth #[]).size := by
    rw [h_inner_size]; exact (σ s_fin).isLt
  -- (σ s_fin)-slot of state.pathsOfLength = f p.
  have h_q_at_σs : (state.pathsOfLength.getD depth #[])[(σ s_fin).val]'h_σs_lt_arr
                 = PathsFrom.permute σ p := by
    have h_eq := state_σ_fixed_pathsOfLength_at_σ_slot σ state h_state_σ_fixed depth
                  h_depth_arr h_inner_size s_fin h_σs_lt_arr h_s_p_lt_arr
    rw [h_eq]
    have h_arr_eq_p : (state.pathsOfLength.getD depth #[])[s_fin.val]'h_s_p_lt_arr = p := by
      show (state.pathsOfLength.getD depth #[])[s_p]'h_s_p_lt_arr = p
      rw [show (state.pathsOfLength.getD depth #[])[s_p]'h_s_p_lt_arr
            = (state.pathsOfLength.getD depth #[]).toList[s_p]'(by
                rw [Array.length_toList]; exact h_s_p_lt_arr)
          from (Array.getElem_toList (h := h_s_p_lt_arr)).symm]
      exact hs_p_eq
    rw [h_arr_eq_p]
  rw [← h_q_at_σs]
  exact Array.getElem_mem_toList _

/-- σ-action invariance of `pathsAtDepth.map f` (`Perm` version): when state is σ-fixed,
`pathsAtDepth` and `pathsAtDepth.map f` are `Perm`-equivalent.

**Proof.** By σ-fixedness, `f(arr[(σ⁻¹ i).val]) = arr[i.val]` for the underlying array
`arr := state.pathsOfLength.getD depth #[]`. Therefore the σ⁻¹-reindexed `f`-mapping of
`pathsAtDepth` equals `pathsAtDepth` itself. The `map_reindex_perm` lemma then gives the
Perm with `pathsAtDepth.map f`. -/
private theorem pathsAtDepth_map_f_perm
    (σ : Equiv.Perm (Fin n)) (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let f : PathsFrom n → PathsFrom n := PathsFrom.permute σ
    pathsAtDepth.Perm (pathsAtDepth.map f) := by
  -- Handle n = 0 vacuously.
  by_cases hn : n = 0
  · subst hn; exact absurd h_depth (Nat.not_lt_zero _)
  -- For n ≥ 1, peel off n = k + 1 to inhabit `Fin n`.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro pathsAtDepth f
  -- Inner-array size = k+1 via toList.length.
  have h_inner_size : (state.pathsOfLength.getD depth #[]).size = k + 1 := by
    rw [← Array.length_toList]; exact h_outer_len
  -- depth < state.pathsOfLength.size (so the arr is meaningful).
  have h_depth_arr : depth < state.pathsOfLength.size := by
    by_contra h_not
    push_neg at h_not
    have h_arr_empty : state.pathsOfLength.getD depth #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h_not, Option.getD_none]
    rw [h_arr_empty] at h_outer_len
    simp at h_outer_len
  -- Default for getD lookups (n = k + 1 inhabits Fin n via 0).
  let default_pf : PathsFrom (k + 1) :=
    { depth := 0, startVertexIndex := 0, pathsToVertex := [] }
  have h_pathsAtDepth_len : pathsAtDepth.length = k + 1 := h_outer_len
  -- The σ-reindexing-after-f-mapping list equals pathsAtDepth.
  have h_reindex_eq :
      (List.finRange (k + 1)).map (fun i : Fin (k + 1) =>
        f (pathsAtDepth.getD (σ⁻¹ i).val default_pf))
      = pathsAtDepth := by
    apply List.ext_getElem
    · simp [h_pathsAtDepth_len]
    intros j h₁ h₂
    have h_j_lt_kp1 : j < k + 1 := by
      simp only [List.length_map, List.length_finRange] at h₁; exact h₁
    rw [List.getElem_map, List.getElem_finRange]
    simp only [Fin.cast_mk]
    -- After normalization, LHS is `f (pathsAtDepth.getD (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val default_pf)`.
    have h_σ_inv_j_lt : (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val < pathsAtDepth.length := by
      rw [h_pathsAtDepth_len]; exact (σ⁻¹ ⟨j, h_j_lt_kp1⟩).isLt
    have h_getD_eq : pathsAtDepth.getD (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val default_pf
                   = pathsAtDepth[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_σ_inv_j_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_σ_inv_j_lt, Option.getD_some]
    rw [h_getD_eq]
    -- Convert pathsAtDepth[i] to arr[i] via getElem_toList.
    have h_arr_σ_inv_lt : (σ⁻¹ ⟨j, h_j_lt_kp1⟩).val < (state.pathsOfLength.getD depth #[]).size := by
      rw [h_inner_size]; exact (σ⁻¹ ⟨j, h_j_lt_kp1⟩).isLt
    have h_arr_j_lt : j < (state.pathsOfLength.getD depth #[]).size := by
      rw [h_inner_size]; exact h_j_lt_kp1
    have h_arr_at_σ_inv :
        (state.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr_σ_inv_lt
        = pathsAtDepth[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_σ_inv_j_lt := by
      show (state.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr_σ_inv_lt
         = (state.pathsOfLength.getD depth #[]).toList[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'
              (by rw [Array.length_toList]; exact h_arr_σ_inv_lt)
      exact Array.getElem_toList (h := h_arr_σ_inv_lt)
    rw [← h_arr_at_σ_inv]
    -- Apply σ-fixedness at s_fin := σ⁻¹ ⟨j, h_j_lt_kp1⟩.
    have h_σ_fix := state_σ_fixed_pathsOfLength_at_σ_slot σ state h_state_σ_fixed depth
      h_depth_arr h_inner_size (σ⁻¹ ⟨j, h_j_lt_kp1⟩)
      (by rw [h_inner_size]; exact (σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩)).isLt)
      h_arr_σ_inv_lt
    have h_σσ : σ (σ⁻¹ ⟨j, h_j_lt_kp1⟩) = ⟨j, h_j_lt_kp1⟩ := by simp
    rw [h_σσ] at h_σ_fix
    -- `f` is `let`-bound to `PathsFrom.permute σ`; align with `show`.
    show PathsFrom.permute σ
            ((state.pathsOfLength.getD depth #[])[(σ⁻¹ ⟨j, h_j_lt_kp1⟩).val]'h_arr_σ_inv_lt)
        = pathsAtDepth[j]'h₂
    rw [← h_σ_fix]
    -- Goal: arr[j] = pathsAtDepth[j].
    show (state.pathsOfLength.getD depth #[])[j]'h_arr_j_lt
       = (state.pathsOfLength.getD depth #[]).toList[j]'
            (by rw [Array.length_toList]; exact h_arr_j_lt)
    exact Array.getElem_toList (h := h_arr_j_lt)
  -- Apply map_reindex_perm with σ := σ⁻¹.
  have h_perm := map_reindex_perm σ⁻¹ pathsAtDepth h_pathsAtDepth_len f default_pf
  -- h_perm : ((List.finRange (k+1)).map (fun i => f (pathsAtDepth.getD (σ⁻¹ i).val default_pf))).Perm
  --          (pathsAtDepth.map f)
  -- Rewrite LHS via h_reindex_eq.
  rw [h_reindex_eq] at h_perm
  exact h_perm

/-- **Relational σ-rank-closure for the from-side assignList**.

For σ-related typing/rank pairs `(vts₁, br₁)` and `(vts₂, br₂)` and σ-fixed `state`,
each item in `assignList₁` has a corresponding σ-image (with σ-shifted start and same
rank) in `assignList₂`.

**Proof structure.** For item₁ = (p, r) at position k₁ in `sortBy cmp₁ pathsAtDepth`,
set q := f p (which is in pathsAtDepth by state σ-fixedness). Find q's position k₂ in
`sortBy cmp₂ pathsAtDepth`. Show:
- The rank at position k₁ in assignList₂ equals r (via `sortBy_map_pointwise_relational` +
  `assignRanks_map_relational` + Perm-invariance via `assignRanks_rank_eq_of_sorted_perm`).
- The rank at k₂ equals the rank at k₁ via `assignRanks_rank_eq_within_eq_class` (since
  `cmp₂ q L₂[k₁] = .eq` by `sortedPerm_class_eq`).

Hence item₂ := assignList₂[k₂] has first comp q (with σ-shifted start) and rank r. -/
theorem from_assignList_σ_rank_rel
    (σ : Equiv.Perm (Fin n))
    (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin n,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let cmp₁ := comparePathsFrom vts₁ br₁
    let cmp₂ := comparePathsFrom vts₂ br₂
    let assignList₁ := assignRanks cmp₁ (sortBy cmp₁ pathsAtDepth)
    let assignList₂ := assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth)
    ∀ item₁ ∈ assignList₁,
      ∃ item₂ ∈ assignList₂,
        item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
        ∧ item₂.2 = item₁.2 := by
  intro pathsAtDepth cmp₁ cmp₂ assignList₁ assignList₂ item₁ h_item₁_mem
  set f : PathsFrom n → PathsFrom n := PathsFrom.permute σ with hf_def
  -- Locate item₁ in assignList₁ at position k₁.
  obtain ⟨k₁, h_k₁_lt, h_assign_k₁⟩ := List.mem_iff_getElem.mp h_item₁_mem
  -- Length facts.
  have h_assign₁_len : assignList₁.length = pathsAtDepth.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₁ pathsAtDepth).length_eq
  have h_assign₂_len : assignList₂.length = pathsAtDepth.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₂ pathsAtDepth).length_eq
  have h_k₁_lt_n : k₁ < pathsAtDepth.length := h_assign₁_len ▸ h_k₁_lt
  have h_k₁_lt_sort₁ : k₁ < (sortBy cmp₁ pathsAtDepth).length := by
    rw [(sortBy_perm cmp₁ pathsAtDepth).length_eq]; exact h_k₁_lt_n
  have h_k₁_lt_sort₂ : k₁ < (sortBy cmp₂ pathsAtDepth).length := by
    rw [(sortBy_perm cmp₂ pathsAtDepth).length_eq]; exact h_k₁_lt_n
  -- p := item₁.1.
  set p := item₁.1 with hp_def
  have h_item₁_1_eq : p = (sortBy cmp₁ pathsAtDepth)[k₁]'h_k₁_lt_sort₁ := by
    rw [hp_def, ← h_assign_k₁]
    exact assignRanks_getElem_fst cmp₁ (sortBy cmp₁ pathsAtDepth) k₁ h_k₁_lt_sort₁
  -- p ∈ pathsAtDepth.
  have h_p_in_sort₁ : p ∈ sortBy cmp₁ pathsAtDepth := by
    rw [h_item₁_1_eq]; exact List.getElem_mem _
  have h_p_in : p ∈ pathsAtDepth :=
    (sortBy_perm cmp₁ pathsAtDepth).mem_iff.mp h_p_in_sort₁
  -- q := f p ∈ pathsAtDepth.
  set q := f p with hq_def
  have h_q_in : q ∈ pathsAtDepth := by
    rw [hq_def, hf_def]; exact mem_pathsAtDepth_under_f σ state h_state_σ_fixed depth h_depth
      h_outer_len p h_p_in
  -- q is in sortBy cmp₂ pathsAtDepth at some position k₂.
  have h_q_in_sort₂ : q ∈ sortBy cmp₂ pathsAtDepth :=
    (sortBy_perm cmp₂ pathsAtDepth).mem_iff.mpr h_q_in
  obtain ⟨k₂, h_k₂_lt_sort₂, h_q_at_k₂⟩ := List.mem_iff_getElem.mp h_q_in_sort₂
  have h_k₂_lt : k₂ < assignList₂.length := by
    rw [h_assign₂_len]
    exact (sortBy_perm cmp₂ pathsAtDepth).length_eq ▸ h_k₂_lt_sort₂
  -- item₂ := assignList₂[k₂].
  set item₂ := assignList₂[k₂]'h_k₂_lt with hitem₂_def
  -- item₂.1 = q.
  have h_item₂_1_eq : item₂.1 = q := by
    rw [hitem₂_def, assignRanks_getElem_fst cmp₂ (sortBy cmp₂ pathsAtDepth) k₂ h_k₂_lt_sort₂]
    exact h_q_at_k₂
  -- Total preorder + equivCompat for cmp₁ and cmp₂ (used by sortedPerm_class_eq, etc.).
  obtain ⟨h_refl₁, h_antisym₁₁, h_antisym₂₁, h_trans₁⟩ :=
    comparePathsFrom_total_preorder (vc := n) vts₁ br₁
  obtain ⟨h_refl₂, h_antisym₁₂, h_antisym₂₂, h_trans₂⟩ :=
    comparePathsFrom_total_preorder (vc := n) vts₂ br₂
  -- Sortedness of sortBy outputs.
  have h_sort₁ := sortBy_pairwise cmp₁ h_antisym₂₁ h_trans₁ pathsAtDepth
  have h_sort₂ := sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ pathsAtDepth
  -- Relational compare hypothesis: ∀ a b ∈ pathsAtDepth, cmp₂ (f a) (f b) = cmp₁ a b.
  have h_resp : ∀ a ∈ pathsAtDepth, ∀ b ∈ pathsAtDepth, cmp₂ (f a) (f b) = cmp₁ a b := by
    intros a h_a b h_b
    rw [hf_def]
    -- Apply comparePathsFrom_σ_relational.
    have h_a_pTV_len : a.pathsToVertex.length = n := h_pathsToVertex_len a h_a
    have h_b_pTV_len : b.pathsToVertex.length = n := h_pathsToVertex_len b h_b
    have h_a_inner : ∀ q ∈ a.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n :=
      h_inner_len a h_a
    have h_b_inner : ∀ q ∈ b.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n :=
      h_inner_len b h_b
    exact comparePathsFrom_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel a b
      h_a_pTV_len h_b_pTV_len h_a_inner h_b_inner
  -- L_f := sortBy cmp₂ (pathsAtDepth.map f) = (sortBy cmp₁ pathsAtDepth).map f.
  have h_Lf_eq : sortBy cmp₂ (pathsAtDepth.map f)
               = (sortBy cmp₁ pathsAtDepth).map f := by
    apply sortBy_map_pointwise_relational f cmp₁ cmp₂ pathsAtDepth
    intros a h_a b h_b
    exact h_resp a h_a b h_b
  -- assignRanks cmp₂ (L₁.map f) = assignList₁.map (lift f).
  have h_assign_Lf_eq :
      assignRanks cmp₂ ((sortBy cmp₁ pathsAtDepth).map f)
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    apply assignRanks_map_relational cmp₁ cmp₂ f (sortBy cmp₁ pathsAtDepth)
    intros a h_a b h_b
    -- a, b ∈ sortBy cmp₁ pathsAtDepth → a, b ∈ pathsAtDepth.
    have h_a_in : a ∈ pathsAtDepth := (sortBy_perm cmp₁ pathsAtDepth).mem_iff.mp h_a
    have h_b_in : b ∈ pathsAtDepth := (sortBy_perm cmp₁ pathsAtDepth).mem_iff.mp h_b
    exact h_resp a h_a_in b h_b_in
  -- Therefore: assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f)) = assignList₁.map (lift f).
  have h_assign_pathMapF_eq :
      assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f))
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    rw [h_Lf_eq]; exact h_assign_Lf_eq
  -- pathsAtDepth.Perm (pathsAtDepth.map f).
  have h_perm_paths : pathsAtDepth.Perm (pathsAtDepth.map f) :=
    pathsAtDepth_map_f_perm σ state h_state_σ_fixed depth h_depth h_outer_len
  -- sortBy outputs Perm-equivalent.
  have h_sort_perm : (sortBy cmp₂ pathsAtDepth).Perm (sortBy cmp₂ (pathsAtDepth.map f)) := by
    have h_p1 := sortBy_perm cmp₂ pathsAtDepth
    have h_p2 := sortBy_perm cmp₂ (pathsAtDepth.map f)
    exact h_p1.trans (h_perm_paths.trans h_p2.symm)
  have h_sort_Lf : (sortBy cmp₂ (pathsAtDepth.map f)).Pairwise (fun a b => cmp₂ a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ (pathsAtDepth.map f)
  -- Rank at position k₁ in assignList₂ = rank at position k₁ in assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f)).
  have h_k₁_lt_Lf : k₁ < (sortBy cmp₂ (pathsAtDepth.map f)).length := by
    rw [(sortBy_perm cmp₂ (pathsAtDepth.map f)).length_eq, List.length_map]; exact h_k₁_lt_n
  have h_k₁_lt_assign₂ : k₁ < assignList₂.length := h_assign₂_len ▸ h_k₁_lt_n
  have h_k₁_lt_assignLf :
      k₁ < (assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f))).length := by
    rw [assignRanks_length]; exact h_k₁_lt_Lf
  have h_rank_eq_at_k₁ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = ((assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f)))[k₁]'h_k₁_lt_assignLf).2 :=
    assignRanks_rank_eq_of_sorted_perm cmp₂
      h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂ h_sort_perm h_sort₂ h_sort_Lf k₁
      h_k₁_lt_sort₂ h_k₁_lt_Lf
  -- Rank at k₁ in assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f)) = item₁.2 = r.
  -- Helper: lists equal at the same index give equal getElem (PathsFrom n × Nat version).
  have h_get_of_list_eq_pair : ∀ {L₁ L₂ : List (PathsFrom n × Nat)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_rank_at_k₁_via_map :
      ((assignRanks cmp₂ (sortBy cmp₂ (pathsAtDepth.map f)))[k₁]'h_k₁_lt_assignLf).2
        = item₁.2 := by
    have h_k₁_lt_assignList₁_map : k₁ < (assignList₁.map (fun e => (f e.1, e.2))).length := by
      rw [List.length_map, h_assign₁_len]; exact h_k₁_lt_n
    rw [h_get_of_list_eq_pair h_assign_pathMapF_eq k₁ h_k₁_lt_assignLf h_k₁_lt_assignList₁_map,
        List.getElem_map]
    show ((assignList₁[k₁]'(h_assign₁_len ▸ h_k₁_lt_n)).2 : Nat) = item₁.2
    rw [h_assign_k₁]
  have h_rank_at_k₁_eq : (assignList₂[k₁]'h_k₁_lt_assign₂).2 = item₁.2 := by
    rw [h_rank_eq_at_k₁]; exact h_rank_at_k₁_via_map
  -- Now relate rank at k₂ to rank at k₁ within assignList₂.
  -- Helper: lists equal at the same index give equal getElem.
  have h_get_of_list_eq : ∀ {L₁ L₂ : List (PathsFrom n)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_Lf_k₁ : (sortBy cmp₂ (pathsAtDepth.map f))[k₁]'h_k₁_lt_Lf = q := by
    have h_k₁_lt_map : k₁ < ((sortBy cmp₁ pathsAtDepth).map f).length := by
      rw [List.length_map]; exact h_k₁_lt_sort₁
    rw [h_get_of_list_eq h_Lf_eq k₁ h_k₁_lt_Lf h_k₁_lt_map, List.getElem_map,
        ← h_item₁_1_eq, ← hq_def]
  have h_class_eq : cmp₂ ((sortBy cmp₂ (pathsAtDepth.map f))[k₁]'h_k₁_lt_Lf)
                       ((sortBy cmp₂ pathsAtDepth)[k₁]'h_k₁_lt_sort₂) = Ordering.eq :=
    sortedPerm_class_eq cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
      _ _ h_sort_perm.symm h_sort_Lf h_sort₂ k₁ h_k₁_lt_Lf h_k₁_lt_sort₂
  rw [h_Lf_k₁] at h_class_eq
  -- h_class_eq : cmp₂ q (sortBy cmp₂ pathsAtDepth)[k₁] = .eq.
  -- In sortBy cmp₂ pathsAtDepth: q is at position k₂, [k₁] is at position k₁.
  -- We want: rank at k₁ = rank at k₂ in assignList₂.
  -- Case k₁ ≤ k₂: cmp₂ [k₁] [k₂] = cmp₂ [k₁] q = sym (h_class_eq).
  -- Case k₂ < k₁: cmp₂ [k₂] [k₁] = cmp₂ q [k₁] = h_class_eq.
  -- In both, apply assignRanks_rank_eq_within_eq_class with i ≤ j.
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
  have h_k₁_lt_n_full : k₁ < pathsAtDepth.length := h_k₁_lt_n
  have h_k₂_lt_n_full : k₂ < pathsAtDepth.length := by
    rw [← (sortBy_perm cmp₂ pathsAtDepth).length_eq]; exact h_k₂_lt_sort₂
  have h_rank_eq_k₁_k₂ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = (assignList₂[k₂]'h_k₂_lt).2 := by
    rcases Nat.lt_or_ge k₂ k₁ with h_lt | h_ge
    · -- k₂ < k₁.
      have h_le : k₂ ≤ k₁ := h_lt.le
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ pathsAtDepth)[k₂]'h_k₂_lt_sort₂)
                ((sortBy cmp₂ pathsAtDepth)[k₁]'h_k₁_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact (assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ pathsAtDepth) h_sort₂ k₂ k₁ h_le h_k₁_lt_sort₂ h_class_eq_low).symm
    · -- k₁ ≤ k₂.
      have h_le : k₁ ≤ k₂ := h_ge
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ pathsAtDepth)[k₁]'h_k₁_lt_sort₂)
                ((sortBy cmp₂ pathsAtDepth)[k₂]'h_k₂_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_eq_symm _ _ h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ pathsAtDepth))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ pathsAtDepth) h_sort₂ k₁ k₂ h_le h_k₂_lt_sort₂ h_class_eq_low
  -- Now: (assignList₂[k₂]).2 = item₁.2.
  have h_item₂_2_eq : item₂.2 = item₁.2 := by
    rw [hitem₂_def, ← h_rank_eq_k₁_k₂]; exact h_rank_at_k₁_eq
  -- Construct the witness.
  refine ⟨item₂, ?_, ?_, h_item₂_2_eq⟩
  · -- item₂ ∈ assignList₂.
    rw [hitem₂_def]; exact List.getElem_mem _
  · -- item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val.
    rw [h_item₂_1_eq, hq_def, hf_def]
    -- (PathsFrom.permute σ p).startVertexIndex = σ p.startVertexIndex (for n ≥ 1).
    by_cases hn : n = 0
    · subst hn; exact p.startVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.startVertexIndex).val = (σ item₁.1.startVertexIndex).val
      rw [hp_def]

/-- Auxiliary: f := PathsBetween.permute σ preserves membership in `allBetween` (for
σ-fixed state). The argument mirrors `mem_pathsAtDepth_under_f`: if q ∈ allBetween via
some pf ∈ pathsAtDepth, then f q ∈ (PathsFrom.permute σ pf).pathsToVertex (positionally
re-indexed under σ⁻¹), and PathsFrom.permute σ pf ∈ pathsAtDepth (state σ-fixed). -/
private theorem mem_allBetween_under_f
    (σ : Equiv.Perm (Fin n)) (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (q : PathsBetween n)
    (h_q_in : q ∈ ((state.pathsOfLength.getD depth #[]).toList.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) [])) :
    PathsBetween.permute σ q ∈ ((state.pathsOfLength.getD depth #[]).toList.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []) := by
  set pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList with h_pathsAtDepth_def
  -- Decompose: q ∈ allBetween ⟹ ∃ pf ∈ pathsAtDepth, q ∈ pf.pathsToVertex.
  obtain ⟨pf, h_pf_in, h_q_in_pf⟩ := (mem_allBetween_iff q pathsAtDepth).mp h_q_in
  -- pf' := PathsFrom.permute σ pf is in pathsAtDepth (via state σ-fixedness).
  have h_pf'_in : PathsFrom.permute σ pf ∈ pathsAtDepth :=
    mem_pathsAtDepth_under_f σ state h_state_σ_fixed depth h_depth h_outer_len pf h_pf_in
  -- f q ∈ (PathsFrom.permute σ pf).pathsToVertex (via the Perm relation).
  set f : PathsBetween n → PathsBetween n := PathsBetween.permute σ with hf_def
  have h_pf_pTV_len : pf.pathsToVertex.length = n := h_pathsToVertex_len pf h_pf_in
  have h_perm : (PathsFrom.permute σ pf).pathsToVertex.Perm (pf.pathsToVertex.map f) :=
    PathsFrom_permute_pathsToVertex_perm σ pf h_pf_pTV_len
  have h_fq_in_map : f q ∈ pf.pathsToVertex.map f :=
    List.mem_map.mpr ⟨q, h_q_in_pf, rfl⟩
  have h_fq_in_pf' : f q ∈ (PathsFrom.permute σ pf).pathsToVertex :=
    h_perm.symm.mem_iff.mp h_fq_in_map
  -- f q ∈ allBetween via pf'.
  exact (mem_allBetween_iff (f q) pathsAtDepth).mpr ⟨_, h_pf'_in, h_fq_in_pf'⟩

/-- σ-action on `allBetween` is a Perm (analogous to `pathsAtDepth_map_f_perm`).

For σ-fixed state, `allBetween.map (PathsBetween.permute σ)` is a permutation of
`allBetween`. The proof unwinds allBetween = pathsAtDepth.flatMap (·.pathsToVertex) and
chains:
1. `allBetween.map f = pathsAtDepth.flatMap (·.pathsToVertex.map f)` (List.map_flatMap).
2. `pf.pathsToVertex.map f ~Perm (PathsFrom.permute σ pf).pathsToVertex` (PathsFrom_permute_pathsToVertex_perm.symm).
3. `pathsAtDepth.Perm (pathsAtDepth.map (PathsFrom.permute σ))` (pathsAtDepth_map_f_perm).

Combined via `Perm.flatMap_left` and `List.flatMap_map`. -/
private theorem allBetween_map_f_perm
    (σ : Equiv.Perm (Fin n)) (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let allBetween := pathsAtDepth.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let f : PathsBetween n → PathsBetween n := PathsBetween.permute σ
    allBetween.Perm (allBetween.map f) := by
  intro pathsAtDepth allBetween f
  set g : PathsFrom n → PathsFrom n := PathsFrom.permute σ with hg_def
  -- Step 1: allBetween = pathsAtDepth.flatMap (·.pathsToVertex).
  have h_allBetween_eq : allBetween = pathsAtDepth.flatMap (·.pathsToVertex) := by
    show pathsAtDepth.foldl (fun acc pf => acc ++ pf.pathsToVertex) [] = _
    rw [List.flatMap_eq_foldl]
  -- Step 2: allBetween.map f = pathsAtDepth.flatMap (·.pathsToVertex.map f).
  have h_allBetween_map_eq : allBetween.map f = pathsAtDepth.flatMap (·.pathsToVertex.map f) := by
    rw [h_allBetween_eq, List.map_flatMap]
  -- Step 3: pathsAtDepth.flatMap (·.pathsToVertex.map f)
  --       ~Perm pathsAtDepth.flatMap ((g ·).pathsToVertex) (Perm.flatMap_left + element-wise Perm).
  have h_step₁ :
      (pathsAtDepth.flatMap (·.pathsToVertex.map f)).Perm
        (pathsAtDepth.flatMap (fun pf => (g pf).pathsToVertex)) := by
    apply List.Perm.flatMap_left
    intro pf h_pf_in
    have h_pf_pTV_len : pf.pathsToVertex.length = n := h_pathsToVertex_len pf h_pf_in
    -- (PathsFrom.permute σ pf).pathsToVertex.Perm (pf.pathsToVertex.map f).
    -- We want: pf.pathsToVertex.map f ~Perm (PathsFrom.permute σ pf).pathsToVertex.
    exact (PathsFrom_permute_pathsToVertex_perm σ pf h_pf_pTV_len).symm
  -- Step 4: pathsAtDepth.flatMap (g · .pathsToVertex) = (pathsAtDepth.map g).flatMap (·.pathsToVertex).
  have h_step₂ : pathsAtDepth.flatMap (fun pf => (g pf).pathsToVertex)
              = (pathsAtDepth.map g).flatMap (·.pathsToVertex) := by
    rw [List.flatMap_map]
  -- Step 5: (pathsAtDepth.map g).flatMap (·.pathsToVertex)
  --       ~Perm pathsAtDepth.flatMap (·.pathsToVertex) (Perm.flatMap_left applied to the input list Perm).
  have h_pathsAtDepth_perm :
      pathsAtDepth.Perm (pathsAtDepth.map g) :=
    pathsAtDepth_map_f_perm σ state h_state_σ_fixed depth h_depth h_outer_len
  have h_step₃ : ((pathsAtDepth.map g).flatMap (·.pathsToVertex)).Perm
                  (pathsAtDepth.flatMap (·.pathsToVertex)) := by
    exact (h_pathsAtDepth_perm.flatMap_right (·.pathsToVertex)).symm
  -- Combine: allBetween.map f ~Perm allBetween.
  have h_chain : (allBetween.map f).Perm allBetween := by
    rw [h_allBetween_map_eq]
    refine h_step₁.trans (?_)
    rw [h_step₂]
    refine h_step₃.trans (?_)
    rw [← h_allBetween_eq]
  exact h_chain.symm

/-- **Relational σ-rank-closure for the between-side assignList**.

The proof structure mirrors `from_assignList_σ_rank_rel` exactly, with `pathsAtDepth`
replaced by `allBetween` and `comparePathsFrom` by `comparePathsBetween`. The key
auxiliary lemmas are `mem_allBetween_under_f` (q ∈ allBetween ⟹ f q ∈ allBetween) and
`allBetween_map_f_perm` (allBetween Perm-equivalent to its f-image). -/
theorem between_assignList_σ_rank_rel
    (σ : Equiv.Perm (Fin n))
    (state : PathState n)
    (h_state_σ_fixed : PathState.permute σ state = state)
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (br₁ br₂ : Nat → Nat → Nat → Nat)
    (hbr_rel : ∀ d : Nat, ∀ s e : Fin n,
      br₂ d (σ s).val (σ e).val = br₁ d s.val e.val)
    (depth : Nat) (h_depth : depth < n)
    (h_outer_len : (state.pathsOfLength.getD depth #[]).toList.length = n)
    (h_pathsToVertex_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        p.pathsToVertex.length = n)
    (h_inner_len : ∀ p ∈ (state.pathsOfLength.getD depth #[]).toList,
        ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n) :
    let pathsAtDepth := (state.pathsOfLength.getD depth #[]).toList
    let allBetween := pathsAtDepth.foldl
      (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
    let cmp₁ := comparePathsBetween vts₁ br₁
    let cmp₂ := comparePathsBetween vts₂ br₂
    let assignList₁ := assignRanks cmp₁ (sortBy cmp₁ allBetween)
    let assignList₂ := assignRanks cmp₂ (sortBy cmp₂ allBetween)
    ∀ item₁ ∈ assignList₁,
      ∃ item₂ ∈ assignList₂,
        item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val
        ∧ item₂.1.endVertexIndex.val = (σ item₁.1.endVertexIndex).val
        ∧ item₂.2 = item₁.2 := by
  intro pathsAtDepth allBetween cmp₁ cmp₂ assignList₁ assignList₂ item₁ h_item₁_mem
  set f : PathsBetween n → PathsBetween n := PathsBetween.permute σ with hf_def
  obtain ⟨k₁, h_k₁_lt, h_assign_k₁⟩ := List.mem_iff_getElem.mp h_item₁_mem
  -- Length facts.
  have h_assign₁_len : assignList₁.length = allBetween.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₁ allBetween).length_eq
  have h_assign₂_len : assignList₂.length = allBetween.length := by
    rw [assignRanks_length]; exact (sortBy_perm cmp₂ allBetween).length_eq
  have h_k₁_lt_n : k₁ < allBetween.length := h_assign₁_len ▸ h_k₁_lt
  have h_k₁_lt_sort₁ : k₁ < (sortBy cmp₁ allBetween).length := by
    rw [(sortBy_perm cmp₁ allBetween).length_eq]; exact h_k₁_lt_n
  have h_k₁_lt_sort₂ : k₁ < (sortBy cmp₂ allBetween).length := by
    rw [(sortBy_perm cmp₂ allBetween).length_eq]; exact h_k₁_lt_n
  -- p := item₁.1.
  set p := item₁.1 with hp_def
  have h_item₁_1_eq : p = (sortBy cmp₁ allBetween)[k₁]'h_k₁_lt_sort₁ := by
    rw [hp_def, ← h_assign_k₁]
    exact assignRanks_getElem_fst cmp₁ (sortBy cmp₁ allBetween) k₁ h_k₁_lt_sort₁
  have h_p_in_sort₁ : p ∈ sortBy cmp₁ allBetween := by
    rw [h_item₁_1_eq]; exact List.getElem_mem _
  have h_p_in : p ∈ allBetween :=
    (sortBy_perm cmp₁ allBetween).mem_iff.mp h_p_in_sort₁
  -- q := f p ∈ allBetween (via mem_allBetween_under_f).
  set q := f p with hq_def
  have h_q_in : q ∈ allBetween := by
    rw [hq_def, hf_def]
    exact mem_allBetween_under_f σ state h_state_σ_fixed depth h_depth h_outer_len
      h_pathsToVertex_len p h_p_in
  -- q is in sortBy cmp₂ allBetween at some position k₂.
  have h_q_in_sort₂ : q ∈ sortBy cmp₂ allBetween :=
    (sortBy_perm cmp₂ allBetween).mem_iff.mpr h_q_in
  obtain ⟨k₂, h_k₂_lt_sort₂, h_q_at_k₂⟩ := List.mem_iff_getElem.mp h_q_in_sort₂
  have h_k₂_lt : k₂ < assignList₂.length := by
    rw [h_assign₂_len]
    exact (sortBy_perm cmp₂ allBetween).length_eq ▸ h_k₂_lt_sort₂
  set item₂ := assignList₂[k₂]'h_k₂_lt with hitem₂_def
  have h_item₂_1_eq : item₂.1 = q := by
    rw [hitem₂_def, assignRanks_getElem_fst cmp₂ (sortBy cmp₂ allBetween) k₂ h_k₂_lt_sort₂]
    exact h_q_at_k₂
  -- Total preorder + sortedness.
  obtain ⟨h_refl₁, h_antisym₁₁, h_antisym₂₁, h_trans₁⟩ :=
    comparePathsBetween_total_preorder (vc := n) vts₁ br₁
  obtain ⟨h_refl₂, h_antisym₁₂, h_antisym₂₂, h_trans₂⟩ :=
    comparePathsBetween_total_preorder (vc := n) vts₂ br₂
  have h_sort₁ := sortBy_pairwise cmp₁ h_antisym₂₁ h_trans₁ allBetween
  have h_sort₂ := sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ allBetween
  -- Inner-length conditions for elements of allBetween (needed for comparePathsBetween_σ_relational).
  have h_inner_q_in_allBetween : ∀ q ∈ allBetween, q.depth > 0 → q.connectedSubPaths.length = n := by
    intros q h_q_in h_q_d
    obtain ⟨pf, h_pf_in, h_q_in_pf⟩ := (mem_allBetween_iff q pathsAtDepth).mp h_q_in
    exact h_inner_len pf h_pf_in q h_q_in_pf h_q_d
  -- Relational compare: ∀ a b ∈ allBetween, cmp₂ (f a) (f b) = cmp₁ a b.
  have h_resp : ∀ a ∈ allBetween, ∀ b ∈ allBetween, cmp₂ (f a) (f b) = cmp₁ a b := by
    intros a h_a b h_b
    rw [hf_def]
    have h_a_inner : a.depth > 0 → a.connectedSubPaths.length = n := h_inner_q_in_allBetween a h_a
    have h_b_inner : b.depth > 0 → b.connectedSubPaths.length = n := h_inner_q_in_allBetween b h_b
    exact comparePathsBetween_σ_relational σ vts₁ vts₂ hvts_rel br₁ br₂ hbr_rel a b
      h_a_inner h_b_inner
  -- L_f := sortBy cmp₂ (allBetween.map f) = (sortBy cmp₁ allBetween).map f.
  have h_Lf_eq : sortBy cmp₂ (allBetween.map f) = (sortBy cmp₁ allBetween).map f := by
    apply sortBy_map_pointwise_relational f cmp₁ cmp₂ allBetween
    intros a h_a b h_b
    exact h_resp a h_a b h_b
  -- assignRanks cmp₂ (L₁.map f) = assignList₁.map (lift f).
  have h_assign_Lf_eq :
      assignRanks cmp₂ ((sortBy cmp₁ allBetween).map f)
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    apply assignRanks_map_relational cmp₁ cmp₂ f (sortBy cmp₁ allBetween)
    intros a h_a b h_b
    have h_a_in : a ∈ allBetween := (sortBy_perm cmp₁ allBetween).mem_iff.mp h_a
    have h_b_in : b ∈ allBetween := (sortBy_perm cmp₁ allBetween).mem_iff.mp h_b
    exact h_resp a h_a_in b h_b_in
  have h_assign_pathMapF_eq :
      assignRanks cmp₂ (sortBy cmp₂ (allBetween.map f))
        = assignList₁.map (fun e => (f e.1, e.2)) := by
    rw [h_Lf_eq]; exact h_assign_Lf_eq
  -- allBetween.Perm (allBetween.map f) (via allBetween_map_f_perm).
  have h_perm_allBetween : allBetween.Perm (allBetween.map f) :=
    allBetween_map_f_perm σ state h_state_σ_fixed depth h_depth h_outer_len
      h_pathsToVertex_len
  -- sortBy outputs Perm-equivalent.
  have h_sort_perm : (sortBy cmp₂ allBetween).Perm (sortBy cmp₂ (allBetween.map f)) := by
    have h_p1 := sortBy_perm cmp₂ allBetween
    have h_p2 := sortBy_perm cmp₂ (allBetween.map f)
    exact h_p1.trans (h_perm_allBetween.trans h_p2.symm)
  have h_sort_Lf : (sortBy cmp₂ (allBetween.map f)).Pairwise (fun a b => cmp₂ a b ≠ Ordering.gt) :=
    sortBy_pairwise cmp₂ h_antisym₂₂ h_trans₂ (allBetween.map f)
  have h_k₁_lt_Lf : k₁ < (sortBy cmp₂ (allBetween.map f)).length := by
    rw [(sortBy_perm cmp₂ (allBetween.map f)).length_eq, List.length_map]; exact h_k₁_lt_n
  have h_k₁_lt_assign₂ : k₁ < assignList₂.length := h_assign₂_len ▸ h_k₁_lt_n
  have h_k₁_lt_assignLf :
      k₁ < (assignRanks cmp₂ (sortBy cmp₂ (allBetween.map f))).length := by
    rw [assignRanks_length]; exact h_k₁_lt_Lf
  have h_rank_eq_at_k₁ :
      (assignList₂[k₁]'h_k₁_lt_assign₂).2
      = ((assignRanks cmp₂ (sortBy cmp₂ (allBetween.map f)))[k₁]'h_k₁_lt_assignLf).2 :=
    assignRanks_rank_eq_of_sorted_perm cmp₂
      h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂ h_sort_perm h_sort₂ h_sort_Lf k₁
      h_k₁_lt_sort₂ h_k₁_lt_Lf
  have h_get_of_list_eq_pair : ∀ {L₁ L₂ : List (PathsBetween n × Nat)}
      (h_eq : L₁ = L₂) (i : Nat) (h₁ : i < L₁.length) (h₂ : i < L₂.length),
      L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_rank_at_k₁_via_map :
      ((assignRanks cmp₂ (sortBy cmp₂ (allBetween.map f)))[k₁]'h_k₁_lt_assignLf).2
        = item₁.2 := by
    have h_k₁_lt_assignList₁_map : k₁ < (assignList₁.map (fun e => (f e.1, e.2))).length := by
      rw [List.length_map, h_assign₁_len]; exact h_k₁_lt_n
    rw [h_get_of_list_eq_pair h_assign_pathMapF_eq k₁ h_k₁_lt_assignLf h_k₁_lt_assignList₁_map,
        List.getElem_map]
    show ((assignList₁[k₁]'(h_assign₁_len ▸ h_k₁_lt_n)).2 : Nat) = item₁.2
    rw [h_assign_k₁]
  have h_rank_at_k₁_eq : (assignList₂[k₁]'h_k₁_lt_assign₂).2 = item₁.2 := by
    rw [h_rank_eq_at_k₁]; exact h_rank_at_k₁_via_map
  -- L_f at k₁ = q.
  have h_get_of_list_eq : ∀ {L₁ L₂ : List (PathsBetween n)} (h_eq : L₁ = L₂) (i : Nat)
      (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i]'h₁ = L₂[i]'h₂ := by
    intros _ _ h_eq _ _ _
    subst h_eq; rfl
  have h_Lf_k₁ : (sortBy cmp₂ (allBetween.map f))[k₁]'h_k₁_lt_Lf = q := by
    have h_k₁_lt_map : k₁ < ((sortBy cmp₁ allBetween).map f).length := by
      rw [List.length_map]; exact h_k₁_lt_sort₁
    rw [h_get_of_list_eq h_Lf_eq k₁ h_k₁_lt_Lf h_k₁_lt_map, List.getElem_map,
        ← h_item₁_1_eq, ← hq_def]
  have h_class_eq : cmp₂ ((sortBy cmp₂ (allBetween.map f))[k₁]'h_k₁_lt_Lf)
                       ((sortBy cmp₂ allBetween)[k₁]'h_k₁_lt_sort₂) = Ordering.eq :=
    sortedPerm_class_eq cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
      _ _ h_sort_perm.symm h_sort_Lf h_sort₂ k₁ h_k₁_lt_Lf h_k₁_lt_sort₂
  rw [h_Lf_k₁] at h_class_eq
  -- h_class_eq : cmp₂ q (sortBy cmp₂ allBetween)[k₁] = .eq.
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
          cmp₂ ((sortBy cmp₂ allBetween)[k₂]'h_k₂_lt_sort₂)
                ((sortBy cmp₂ allBetween)[k₁]'h_k₁_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact (assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ allBetween) h_sort₂ k₂ k₁ h_le h_k₁_lt_sort₂ h_class_eq_low).symm
    · have h_le : k₁ ≤ k₂ := h_ge
      have h_class_eq_low :
          cmp₂ ((sortBy cmp₂ allBetween)[k₁]'h_k₁_lt_sort₂)
                ((sortBy cmp₂ allBetween)[k₂]'h_k₂_lt_sort₂) = Ordering.eq := by
        rw [h_q_at_k₂]; exact h_eq_symm _ _ h_class_eq
      have h_assign_at_k₁ :
          (assignList₂[k₁]'h_k₁_lt_assign₂).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween))[k₁]'(by
                rw [assignRanks_length]; exact h_k₁_lt_sort₂)).2 := rfl
      have h_assign_at_k₂ :
          (assignList₂[k₂]'h_k₂_lt).2
          = ((assignRanks cmp₂ (sortBy cmp₂ allBetween))[k₂]'(by
                rw [assignRanks_length]; exact h_k₂_lt_sort₂)).2 := rfl
      rw [h_assign_at_k₁, h_assign_at_k₂]
      exact assignRanks_rank_eq_within_eq_class cmp₂ h_refl₂ h_antisym₁₂ h_antisym₂₂ h_trans₂
        (sortBy cmp₂ allBetween) h_sort₂ k₁ k₂ h_le h_k₂_lt_sort₂ h_class_eq_low
  have h_item₂_2_eq : item₂.2 = item₁.2 := by
    rw [hitem₂_def, ← h_rank_eq_k₁_k₂]; exact h_rank_at_k₁_eq
  refine ⟨item₂, ?_, ?_, ?_, h_item₂_2_eq⟩
  · rw [hitem₂_def]; exact List.getElem_mem _
  · -- item₂.1.startVertexIndex.val = (σ item₁.1.startVertexIndex).val.
    rw [h_item₂_1_eq, hq_def, hf_def]
    by_cases hn : n = 0
    · subst hn; exact p.startVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.startVertexIndex).val = (σ item₁.1.startVertexIndex).val
      rw [hp_def]
  · -- item₂.1.endVertexIndex.val = (σ item₁.1.endVertexIndex).val.
    rw [h_item₂_1_eq, hq_def, hf_def]
    by_cases hn : n = 0
    · subst hn; exact p.endVertexIndex.elim0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show (σ p.endVertexIndex).val = (σ item₁.1.endVertexIndex).val
      rw [hp_def]

end Graph
