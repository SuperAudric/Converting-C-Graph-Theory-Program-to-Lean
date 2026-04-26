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

## Progress status (2026-04-25)
Foundational sub-lemmas for the deep proof are in place:
- ✅ `betweenRankFn_σ_inv_from_cells` — cell-σ-inv → fn-σ-inv.
- ✅ `initializePaths_σInv_via_Aut` — Stage A applied for σ ∈ Aut G.
- ✅ `assignRanks_map_of_cmp_respect` (in `ComparisonSort`) — assignRanks commutes with `map f`
  when cmp respects f.
- ✅ `set_chain_σInvariant` — set! chain on fromRanks preserves σ-cell-invariance, given
  σ-rank-closure + permutation of starts.
- ✅ `setBetween_chain_σInvariant` — setBetween chain on betweenRanks preserves σ-cell-
  invariance, given σ-rank-closure + Nodup of (start, end) pairs.
- ✅ `comparePathSegments_σ_self_eq` — `cmp p (PS.permute σ p) = .eq` under σ-inv vts/br.
- ✅ `comparePathsBetween_σ_self_eq` — `cmp p (PB.permute σ p) = .eq` under σ-inv vts/br.
- ✅ `comparePathsFrom_σ_self_eq` — `cmp p (PF.permute σ p) = .eq` under σ-inv vts/br.

Remaining for `calculatePathRankings_fromRanks_inv` / `_betweenRanks_inv`:
- σ-rank-closure of assignList: derive from `_σ_self_eq` (cmp p (f p) = .eq) — σ-related
  elements get the same rank in `assignRanks`. The σ-self-eq lemmas above provide the key
  ingredient: cmp identifies p with its σ-permuted self, so they're in the same cmp-class.
- Body preservation: combines chain σ-inv + σ-rank-closure + σ-equivariance of compare/sort
  for one depth iteration.
- Foldl invariant on the depth loop (carrying σ-cell-invariance of currentBetween/currentFrom).
- Cell-level extraction from the foldl invariant.
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

/-- The chain of `set!`s on `fromAcc` preserves the outer array size. -/
private theorem set_chain_size_preserving
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
private theorem set_chain_row_size_preserving
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
private theorem set_chain_σInvariant
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
private theorem nested_set_chain_at_target_pair_nodup
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
private theorem setBetween_chain_size_preserving
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
private theorem setBetween_chain_row_size_preserving
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
private theorem setBetween_chain_cell_size_preserving
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

/-! ### σ-self-equality of compare functions

Under σ-invariant `vts` and `br`, comparing an element to its σ-permuted self yields `.eq`.
This is a key step toward σ-rank-closure of the assignList: σ-related elements in
`pathsAtDepth` get the same rank, enabling the σ-closure hypothesis of the chain σ-inv
lemmas. The proofs cascade up through PathSegment → PathsBetween → PathsFrom. -/

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
private theorem state_σ_fixed_pathsOfLength_at_σ_slot
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
private theorem from_assignList_σ_rank_closure
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

/-- **σ-rank-closure of the between-side assignList** (TODO): analog of the from-side
σ-rank-closure for the `allBetween` list (the concat of all `pathsToVertex`). -/
private theorem between_assignList_σ_rank_closure
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
