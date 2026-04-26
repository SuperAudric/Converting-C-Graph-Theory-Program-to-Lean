import FullCorrectness.Equivariance.Actions

/-!
# Generic sort / comparison list lemmas  (`FullCorrectness.Equivariance.ComparisonSort`)

Abstract lemmas about `insertSorted`, `sortBy`, `orderInsensitiveListCmp`, and
`foldl` that are used by the path-comparison equivariance proofs but do not mention
any path data types directly.

## Key lemmas

- `insertSorted_map` / `sortBy_map` — `f`-map commutes with sort when `f` preserves `cmp`.
- `perm_insertSorted` / `sortBy_perm` — sort produces a `List.Perm` of its input.
- `sortedPerm_class_eq` — **KEY**: for sorted `Perm`-related lists, position-`i` elements
  are in the same `cmp`-equivalence class.
- `sortBy_pairwise` — `sortBy` output is pairwise `≠ .gt`.
- `foldl_pointwise_eq` — generic pointwise-equal foldl equality helper.
- `orderInsensitiveListCmp_perm` — `orderInsensitiveListCmp` is `Perm`-invariant given
  a compatible total preorder.
- `assignRanks_length` / `assignRanks_map_fst` / `assignRanks_getElem_fst` — structural
  characterizations of `assignRanks`'s output: same length as input, first components
  reproduce the input list.
- `assignRanks_rank_lt_length` — every rank is `< L.length`. Combined with the above,
  bounds the values produced by `convergeOnce` (each vertex gets a `getFrom` value, which
  is a rank from `assignRanks` on a length-`n` input list).
- `assignRanks_image_dense` — the rank set is downward-closed: any `k ≤ entry.2` for an
  entry in the output also has a witness in the output. Combined with `_rank_lt_length`,
  the rank set is `{0, 1, ..., max_rank}` — exactly the density needed for the prefix
  typing invariant.
-/

namespace Graph

variable {n : Nat}

/-! ### σ-equivariance of the comparison functions

`calculatePathRankings_value_invariant` needs the three compare functions to be σ-equivariant
on σ-invariant inputs. We prove `comparePathSegments` fully here; the stronger `PathsBetween`/
`PathsFrom` versions also require `sortBy`'s `map`-respect lemma (proved below), and for
the depth-positive `PathsBetween` case `orderInsensitiveListCmp`'s permutation-invariance
(left for follow-up work). -/

/-- `insertSorted` respects `map` when `f` preserves the comparison: inserting `f a` into
a `f`-mapped sorted list equals `f`-mapping the result of inserting `a` into the original
sorted list. -/
private theorem insertSorted_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (a : α) (L : List α) :
    insertSorted cmp (f a) (L.map f) = (insertSorted cmp a L).map f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    show insertSorted cmp (f a) (f b :: L.map f) = (insertSorted cmp a (b :: L)).map f
    show (if cmp (f a) (f b) != .gt then f a :: f b :: L.map f
          else f b :: insertSorted cmp (f a) (L.map f))
       = (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).map f
    rw [h a b]
    by_cases hc : cmp a b != .gt
    · simp [hc]
    · simp [hc, ih]

/-- `sortBy` respects `map` when `f` preserves the comparison. The σ-equivariance form
(below) instantiates `f := PathSegment.permute σ` and the σ-equivariance of
`comparePathSegments`. -/
theorem sortBy_map {α : Type} (f : α → α) (cmp : α → α → Ordering)
    (h : ∀ a b : α, cmp (f a) (f b) = cmp a b) (L : List α) :
    sortBy cmp (L.map f) = (sortBy cmp L).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show insertSorted cmp (f a) (sortBy cmp (L.map f))
       = (insertSorted cmp a (sortBy cmp L)).map f
    rw [ih, insertSorted_map f cmp h]

/-- `insertSorted` produces a permutation of `a :: L` (regardless of `cmp`). -/
theorem perm_insertSorted {α : Type} (cmp : α → α → Ordering) (a : α) (L : List α) :
    (insertSorted cmp a L).Perm (a :: L) := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons b L ih =>
    show (if cmp a b != .gt then a :: b :: L else b :: insertSorted cmp a L).Perm (a :: b :: L)
    by_cases h : cmp a b != .gt
    · simp [h]
    · simp [h]
      exact (List.Perm.cons b ih).trans (List.Perm.swap a b L)

/-- `sortBy` produces a permutation of its input (regardless of `cmp`). -/
theorem sortBy_perm {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (sortBy cmp L).Perm L := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons a L ih =>
    show (insertSorted cmp a (sortBy cmp L)).Perm (a :: L)
    exact (perm_insertSorted cmp a (sortBy cmp L)).trans (List.Perm.cons a ih)

/-- The head case of `sortedPerm_class_eq`: heads of sorted permuted lists are in the same
class. Proved here cleanly using `Perm`-membership + sortedness + reflexivity + antisymmetry.

For the general position-`i` case, the same reasoning applies after "decomposing" both
lists, but the tail-decomposition isn't a `Perm` (only "class-Perm"), which is the
difficulty in the general lemma. -/
private theorem sorted_perm_head_class_eq {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (a : α) (M : List α) (b : α) (M' : List α)
    (h_perm : (a :: M).Perm (b :: M'))
    (h_sort : (a :: M).Pairwise (fun x y => cmp x y ≠ Ordering.gt))
    (h_sort' : (b :: M').Pairwise (fun x y => cmp x y ≠ Ordering.gt)) :
    cmp a b = Ordering.eq := by
  -- Membership transfer via Perm.
  have ha_in : a ∈ b :: M' := h_perm.mem_iff.mp List.mem_cons_self
  have hb_in : b ∈ a :: M := h_perm.symm.mem_iff.mp List.mem_cons_self
  -- cmp a b ≠ .gt: either b = a (refl) or b ∈ M (sortedness of a :: M).
  have h_ab : cmp a b ≠ Ordering.gt := by
    rcases List.mem_cons.mp hb_in with hb_eq | hb_in_tail
    · subst hb_eq; rw [h_refl]; intro h; cases h
    · exact List.rel_of_pairwise_cons h_sort hb_in_tail
  -- cmp b a ≠ .gt: similarly.
  have h_ba : cmp b a ≠ Ordering.gt := by
    rcases List.mem_cons.mp ha_in with ha_eq | ha_in_tail
    · subst ha_eq; rw [h_refl]; intro h; cases h
    · exact List.rel_of_pairwise_cons h_sort' ha_in_tail
  -- Conclude cmp a b = .eq via case analysis + antisym.
  match h_cmp : cmp a b with
  | .eq => rfl
  | .lt =>
    have : cmp b a = Ordering.gt := h_antisym _ _ h_cmp
    exact absurd this h_ba
  | .gt => exact absurd h_cmp h_ab

/-- For sorted `M`, `M'` with `M.Perm M'`, at every position the elements are in the same
`cmp`-equivalence class. This is the **KEY LEMMA** behind `orderInsensitiveListCmp_perm`.

Intuition: in a sorted list, equivalence classes occupy contiguous blocks. Two sorted
permutations of the same multiset have the same block structure (same classes in the same
order, with the same sizes), hence agree class-wise at every position. Within each block
(within-class permutation), `cmp` gives `.eq`.

The proof is a counting argument. Set `x := M[i]`. Two facts about a sorted `L`:
- `count(cmp · x = .lt, L) ≤ i`: by sortedness, only the first `i` positions can hold
  elements strictly less than `x`.
- `count(cmp · x ≠ .gt, L) ≥ i + 1`: positions `0..i` all hold elements `≤ x`.
Both counts transfer to `M'` via `List.Perm.countP_eq`. In sorted `M'`, "lt-positions"
form a left prefix and "≠-gt-positions" form a left prefix. The bounds force position
`i` of `M'` to be sandwiched: not in the lt prefix (since `i ≥ lt_count`) but in the
≠-gt prefix (since `i < ngt_count`). Hence `cmp M'[i] x` is neither `.lt` nor `.gt`,
so it is `.eq`. Symmetry gives `cmp M[i] M'[i] = .eq`.

The proof uses four hypotheses on `cmp`: reflexivity, both directions of antisymmetry,
and `≤`-transitivity. These are the ingredients of a total preorder, which is what
`comparePathSegments`/etc. behave like on the algorithm's actual lists. -/
private theorem sortedPerm_class_eq {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (M M' : List α) (h_perm : M.Perm M')
    (h_sort_M : M.Pairwise (fun a b => cmp a b ≠ Ordering.gt))
    (h_sort_M' : M'.Pairwise (fun a b => cmp a b ≠ Ordering.gt))
    (i : Nat) (h_i : i < M.length) (h_i' : i < M'.length) :
    cmp (M[i]'h_i) (M'[i]'h_i') = Ordering.eq := by
  -- Helper 0: symmetry of `.eq` (derived from antisym₁ + antisym₂).
  have h_eq_symm : ∀ a b, cmp a b = Ordering.eq → cmp b a = Ordering.eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      have h1 := h_antisym₁ b a h_ba
      rw [hab] at h1
      exact Ordering.noConfusion h1
    | .gt =>
      have h1 := h_antisym₂ b a h_ba
      rw [hab] at h1
      exact Ordering.noConfusion h1
  -- Helper 1: `≤`-then-`<` gives `<`.
  have h_le_lt : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c = Ordering.lt → cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hbc' : cmp b c ≠ Ordering.gt := by rw [hbc]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab hbc'
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca' : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      exact (h_trans c a b h_ca' hab) (h_antisym₁ b c hbc)
  -- Helper 2: `<`-then-`≤` gives `<`.
  have h_lt_le : ∀ a b c, cmp a b = Ordering.lt → cmp b c ≠ Ordering.gt → cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hab' : cmp a b ≠ Ordering.gt := by rw [hab]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab' hbc
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca' : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      exact (h_trans b c a hbc h_ca') (h_antisym₁ a b hab)
  -- 1. Reference element `x := M[i]`.
  set x := M[i]'h_i with hx_def
  -- 2. `lt_count M x ≤ i`. Split `M = take i ++ drop i`; the drop part contributes 0.
  have h_lt_count_M : M.countP (fun y => decide (cmp y x = Ordering.lt)) ≤ i := by
    rw [show M = M.take i ++ M.drop i from (List.take_append_drop i M).symm,
        List.countP_append]
    have h_drop_zero : (M.drop i).countP (fun y => decide (cmp y x = Ordering.lt)) = 0 := by
      rw [List.countP_eq_zero]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      have hk_lt' : k < M.length - i := by simpa using hk_lt
      have hi_k : i + k < M.length := by omega
      simp only [decide_eq_true_eq]
      have h_index : (M.drop i)[k]'hk_lt = M[i + k]'hi_k :=
        (List.getElem_drop' (by omega)).symm
      rw [show y = M[i + k]'hi_k by rw [← hk_eq]; exact h_index]
      intro h_eq_lt
      by_cases h_k : k = 0
      · subst h_k
        -- h_eq_lt : cmp M[i + 0] x = Ordering.lt; reduce via def-eq.
        have h_eq_lt' : cmp (M[i]'h_i) (M[i]'h_i) = Ordering.lt := h_eq_lt
        rw [h_refl] at h_eq_lt'
        exact Ordering.noConfusion h_eq_lt'
      · have hi_lt_ik : i < i + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero h_k)
        have h_sort : cmp (M[i]'h_i) (M[i + k]'hi_k) ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M) i (i + k) h_i hi_k hi_lt_ik
        exact h_sort (h_antisym₁ _ _ h_eq_lt)
    rw [h_drop_zero, Nat.add_zero]
    refine Nat.le_trans List.countP_le_length ?_
    rw [List.length_take]; exact Nat.min_le_left _ _
  -- 3. `not_gt_count M x ≥ i + 1`. The take (i+1) part hits `i+1` because every element satisfies.
  have h_ngt_count_M : i + 1 ≤ M.countP (fun y => decide (cmp y x ≠ Ordering.gt)) := by
    rw [show M = M.take (i+1) ++ M.drop (i+1) from (List.take_append_drop (i+1) M).symm,
        List.countP_append]
    have h_take_eq : (M.take (i+1)).countP (fun y => decide (cmp y x ≠ Ordering.gt))
                  = (M.take (i+1)).length := by
      rw [List.countP_eq_length]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      simp only [decide_eq_true_eq]
      rw [List.getElem_take] at hk_eq
      rw [List.length_take] at hk_lt
      have hk_lt_succ : k < i + 1 := (lt_min_iff.mp hk_lt).1
      have hk_le_i : k ≤ i := Nat.le_of_lt_succ hk_lt_succ
      have hk_M : k < M.length := (lt_min_iff.mp hk_lt).2
      rw [← hk_eq]
      by_cases h_k : k = i
      · subst h_k
        rw [hx_def, h_refl]
        intro hh; cases hh
      · have hk_lt_i : k < i := lt_of_le_of_ne hk_le_i h_k
        exact (List.pairwise_iff_getElem.mp h_sort_M) k i hk_M h_i hk_lt_i
    have h_take_len : (M.take (i+1)).length = i + 1 := by
      rw [List.length_take]; omega
    rw [h_take_eq, h_take_len]
    omega
  -- 4. Perm transfer: counts on `M'` inherit the same bounds.
  have h_lt_count_M' : M'.countP (fun y => decide (cmp y x = Ordering.lt)) ≤ i := by
    rw [← h_perm.countP_eq]; exact h_lt_count_M
  have h_ngt_count_M' : i + 1 ≤ M'.countP (fun y => decide (cmp y x ≠ Ordering.gt)) := by
    rw [← h_perm.countP_eq]; exact h_ngt_count_M
  -- 5. `cmp M'[i] x ≠ .lt`. Otherwise, by `h_le_lt`, all positions ≤ `i` have `cmp · x = .lt`,
  -- forcing `lt_count M' x ≥ i + 1` — contradicting (4).
  have h_not_lt : cmp (M'[i]'h_i') x ≠ Ordering.lt := by
    intro h_lt_val
    have h_count_take_M' : (M'.take (i+1)).countP (fun y => decide (cmp y x = Ordering.lt))
                         = (M'.take (i+1)).length := by
      rw [List.countP_eq_length]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      simp only [decide_eq_true_eq]
      rw [List.getElem_take] at hk_eq
      rw [List.length_take] at hk_lt
      have hk_lt_succ : k < i + 1 := (lt_min_iff.mp hk_lt).1
      have hk_le_i : k ≤ i := Nat.le_of_lt_succ hk_lt_succ
      have hk_M' : k < M'.length := (lt_min_iff.mp hk_lt).2
      rw [← hk_eq]
      by_cases h_k : k = i
      · subst h_k; exact h_lt_val
      · have hk_lt_i : k < i := lt_of_le_of_ne hk_le_i h_k
        have h_sort : cmp (M'[k]'hk_M') (M'[i]'h_i') ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M') k i hk_M' h_i' hk_lt_i
        exact h_le_lt _ _ _ h_sort h_lt_val
    have h_take_len_M' : (M'.take (i+1)).length = i + 1 := by
      rw [List.length_take]; omega
    have h_count_full :
        i + 1 ≤ M'.countP (fun y => decide (cmp y x = Ordering.lt)) := by
      rw [show M' = M'.take (i+1) ++ M'.drop (i+1) from (List.take_append_drop (i+1) M').symm,
          List.countP_append, h_count_take_M', h_take_len_M']
      omega
    omega
  -- 6. `cmp M'[i] x ≠ .gt`. Otherwise, by `h_lt_le` (after antisym), all positions ≥ `i`
  -- have `cmp · x = .gt`, forcing `ngt_count M' x ≤ i` — contradicting (4).
  have h_not_gt : cmp (M'[i]'h_i') x ≠ Ordering.gt := by
    intro h_gt_val
    have h_drop_zero : (M'.drop i).countP (fun y => decide (cmp y x ≠ Ordering.gt)) = 0 := by
      rw [List.countP_eq_zero]
      intros y hy
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hy
      have hk_lt' : k < M'.length - i := by simpa using hk_lt
      have hi_k : i + k < M'.length := by omega
      simp only [decide_eq_true_eq, ne_eq, Decidable.not_not]
      have h_index : (M'.drop i)[k]'hk_lt = M'[i + k]'hi_k :=
        (List.getElem_drop' (by omega)).symm
      rw [show y = M'[i + k]'hi_k by rw [← hk_eq]; exact h_index]
      by_cases h_k : k = 0
      · subst h_k
        show cmp (M'[i]'h_i') x = Ordering.gt
        exact h_gt_val
      · have hi_lt_ik : i < i + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero h_k)
        have h_sort : cmp (M'[i]'h_i') (M'[i + k]'hi_k) ≠ Ordering.gt :=
          (List.pairwise_iff_getElem.mp h_sort_M') i (i + k) h_i' hi_k hi_lt_ik
        have h_x_M'i : cmp x (M'[i]'h_i') = Ordering.lt := h_antisym₂ _ _ h_gt_val
        have h_x_M'ik : cmp x (M'[i + k]'hi_k) = Ordering.lt := h_lt_le _ _ _ h_x_M'i h_sort
        exact h_antisym₁ _ _ h_x_M'ik
    have h_take_le_i : (M'.take i).length ≤ i := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    have h_count_take_le : (M'.take i).countP (fun y => decide (cmp y x ≠ Ordering.gt))
                         ≤ i :=
      List.countP_le_length.trans h_take_le_i
    have h_total : M'.countP (fun y => decide (cmp y x ≠ Ordering.gt)) ≤ i := by
      rw [show M' = M'.take i ++ M'.drop i from (List.take_append_drop i M').symm,
          List.countP_append, h_drop_zero, Nat.add_zero]
      exact h_count_take_le
    omega
  -- 7. Conclude `cmp M'[i] x = .eq` (the only remaining case), then symmetrize.
  have h_M'i_eq_x : cmp (M'[i]'h_i') x = Ordering.eq := by
    match h : cmp (M'[i]'h_i') x with
    | .eq => rfl
    | .lt => exact (h_not_lt h).elim
    | .gt => exact (h_not_gt h).elim
  exact h_eq_symm _ _ h_M'i_eq_x

/-- `insertSorted` preserves `Pairwise`-sortedness when `cmp` admits the swap-on-`.gt`
direction of antisymmetry and `≤`-transitivity. Inserts `a` into a sorted `L` in the
unique left-most position where `cmp a · ≠ .gt` holds; positions before are unchanged
(IH), at position `a` we use sortedness + transitivity to extend to the tail, and at
positions after we use that the tail is sorted (IH) and `cmp ·_head a ≠ .gt` follows
from `cmp a head = .gt → cmp head a = .lt`. -/
private theorem insertSorted_pairwise {α : Type} (cmp : α → α → Ordering)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt) :
    ∀ (L : List α) (a : α), L.Pairwise (fun x y => cmp x y ≠ Ordering.gt) →
      (insertSorted cmp a L).Pairwise (fun x y => cmp x y ≠ Ordering.gt) := by
  intro L
  induction L with
  | nil =>
    intros a _
    show ([a] : List α).Pairwise _
    exact List.Pairwise.cons (by intros _ hy; cases hy) List.Pairwise.nil
  | cons b L ih =>
    intros a hL
    show (if cmp a b != Ordering.gt then a :: b :: L else b :: insertSorted cmp a L).Pairwise _
    by_cases hab : cmp a b != Ordering.gt
    · -- insert at front: a :: b :: L is sorted because cmp a b ≠ .gt + transitivity to L.
      simp only [hab]
      have hab' : cmp a b ≠ Ordering.gt := by
        intro h; rw [h] at hab; simp at hab
      apply List.Pairwise.cons
      · intros y hy
        rcases List.mem_cons.mp hy with rfl | hy_in
        · exact hab'
        · have hby : cmp b y ≠ Ordering.gt := List.rel_of_pairwise_cons hL hy_in
          exact h_trans _ _ _ hab' hby
      · exact hL
    · -- insert later: b :: insertSorted cmp a L. b ≤ everything in (a :: L) by sortedness
      -- (for L) + antisym₂ (for a, since cmp a b = .gt → cmp b a = .lt ≠ .gt).
      simp only [hab]
      have hab_gt : cmp a b = Ordering.gt := by
        match h_eq : cmp a b with
        | .lt => exfalso; rw [h_eq] at hab; simp at hab
        | .eq => exfalso; rw [h_eq] at hab; simp at hab
        | .gt => rfl
      have hL_tail : L.Pairwise (fun x y => cmp x y ≠ Ordering.gt) :=
        (List.pairwise_cons.mp hL).2
      have hL_head : ∀ y ∈ L, cmp b y ≠ Ordering.gt :=
        (List.pairwise_cons.mp hL).1
      apply List.Pairwise.cons
      · intros y hy
        have hy_perm : y ∈ a :: L := (perm_insertSorted cmp a L).mem_iff.mp hy
        rcases List.mem_cons.mp hy_perm with hy_eq | hy_in
        · rw [hy_eq]
          have h_ba : cmp b a = Ordering.lt := h_antisym₂ _ _ hab_gt
          rw [h_ba]; intro h; cases h
        · exact hL_head y hy_in
      · exact ih a hL_tail

/-- `sortBy cmp L` produces a `Pairwise`-sorted list. Insertion sort, by induction on `L`
applying `insertSorted_pairwise` at each step. -/
theorem sortBy_pairwise {α : Type} (cmp : α → α → Ordering)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (L : List α) :
    (sortBy cmp L).Pairwise (fun a b => cmp a b ≠ Ordering.gt) := by
  induction L with
  | nil =>
    show (([] : List α)).Pairwise _
    exact List.Pairwise.nil
  | cons a L ih =>
    show (insertSorted cmp a (sortBy cmp L)).Pairwise _
    exact insertSorted_pairwise cmp h_antisym₂ h_trans (sortBy cmp L) a ih

/-- Pointwise `foldl` equality: if `L.length = L'.length` and `f acc (L[i]) = f acc (L'[i])`
at every position `i` and every `acc`, then the folds on `L` and `L'` give the same result. -/
theorem foldl_pointwise_eq {α β : Type} (f : β → α → β) (L L' : List α) (init : β)
    (h_len : L.length = L'.length)
    (h_pt : ∀ acc : β, ∀ i : Nat, ∀ (h₁ : i < L.length) (h₂ : i < L'.length),
            f acc (L[i]'h₁) = f acc (L'[i]'h₂)) :
    L.foldl f init = L'.foldl f init := by
  induction L generalizing L' init with
  | nil => match L' with
    | [] => rfl
    | _ :: _ => simp at h_len
  | cons a L ih =>
    match L' with
    | [] => simp at h_len
    | a' :: L' =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [show f init a = f init a' from h_pt init 0 (by simp) (by simp)]
      apply ih
      · simpa using h_len
      · intros acc i h₁ h₂
        exact h_pt acc (i + 1) (by simp; exact h₁) (by simp; exact h₂)

/-- `orderInsensitiveListCmp` is invariant under permutations of its inputs when `cmp`
respects equivalence classes bilaterally (`h_compat`: both left and right).

**Proof.** Lengths agree by `Perm`. `sortBy cmp L₁` and `sortBy cmp L₁'` are both sorted
(`sortBy_pairwise`) and `Perm` (`sortBy_perm`-twice + transitivity). By
`sortedPerm_class_eq`, they agree position-wise on `cmp`-class. Under bilateral `h_compat`,
fold values against the corresponding position of the other sorted list agree pointwise,
so `foldl_pointwise_eq` gives the same result. -/
theorem orderInsensitiveListCmp_perm {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (h_compat : ∀ a b, cmp a b = Ordering.eq → ∀ c, cmp a c = cmp b c ∧ cmp c a = cmp c b)
    (L₁ L₁' L₂ L₂' : List α) (h₁ : L₁.Perm L₁') (h₂ : L₂.Perm L₂') :
    orderInsensitiveListCmp cmp L₁ L₂ = orderInsensitiveListCmp cmp L₁' L₂' := by
  unfold orderInsensitiveListCmp
  have hL₁ : L₁.length = L₁'.length := h₁.length_eq
  have hL₂ : L₂.length = L₂'.length := h₂.length_eq
  by_cases hLen : L₁.length = L₂.length
  · have hLen' : L₁'.length = L₂'.length := hL₁.symm.trans (hLen.trans hL₂)
    simp only [hLen, hLen', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    -- sortBy outputs are Perm-related + sorted.
    have hM₁ : (sortBy cmp L₁).Perm (sortBy cmp L₁') :=
      ((sortBy_perm cmp L₁).trans h₁).trans (sortBy_perm cmp L₁').symm
    have hM₂ : (sortBy cmp L₂).Perm (sortBy cmp L₂') :=
      ((sortBy_perm cmp L₂).trans h₂).trans (sortBy_perm cmp L₂').symm
    have hSort₁ := sortBy_pairwise cmp h_antisym₂ h_trans L₁
    have hSort₁' := sortBy_pairwise cmp h_antisym₂ h_trans L₁'
    have hSort₂ := sortBy_pairwise cmp h_antisym₂ h_trans L₂
    have hSort₂' := sortBy_pairwise cmp h_antisym₂ h_trans L₂'
    -- Pointwise class agreement.
    have h_class₁ : ∀ i (hi₁ : i < (sortBy cmp L₁).length) (hi₁' : i < (sortBy cmp L₁').length),
        cmp ((sortBy cmp L₁)[i]'hi₁) ((sortBy cmp L₁')[i]'hi₁') = Ordering.eq :=
      fun i hi₁ hi₁' =>
        sortedPerm_class_eq cmp h_refl h_antisym₁ h_antisym₂ h_trans
          _ _ hM₁ hSort₁ hSort₁' i hi₁ hi₁'
    have h_class₂ : ∀ i (hi₂ : i < (sortBy cmp L₂).length) (hi₂' : i < (sortBy cmp L₂').length),
        cmp ((sortBy cmp L₂)[i]'hi₂) ((sortBy cmp L₂')[i]'hi₂') = Ordering.eq :=
      fun i hi₂ hi₂' =>
        sortedPerm_class_eq cmp h_refl h_antisym₁ h_antisym₂ h_trans
          _ _ hM₂ hSort₂ hSort₂' i hi₂ hi₂'
    -- Length equality on zip.
    have h_zip_len : ((sortBy cmp L₁).zip (sortBy cmp L₂)).length
                  = ((sortBy cmp L₁').zip (sortBy cmp L₂')).length := by
      rw [List.length_zip, List.length_zip, hM₁.length_eq, hM₂.length_eq]
    -- Apply foldl_pointwise_eq.
    apply foldl_pointwise_eq _ _ _ _ h_zip_len
    intros acc i h_i₁ h_i₂
    -- Translate zip indices to sortBy positions.
    have h_sort₁_len : i < (sortBy cmp L₁).length := by
      have := h_i₁; rw [List.length_zip] at this; omega
    have h_sort₂_len : i < (sortBy cmp L₂).length := by
      have := h_i₁; rw [List.length_zip] at this; omega
    have h_sort₁'_len : i < (sortBy cmp L₁').length := by
      have := h_i₂; rw [List.length_zip] at this; omega
    have h_sort₂'_len : i < (sortBy cmp L₂').length := by
      have := h_i₂; rw [List.length_zip] at this; omega
    -- Compute cmp values at each position via bilateral h_compat.
    have h_eq_cmp :
        cmp ((sortBy cmp L₁)[i]'h_sort₁_len) ((sortBy cmp L₂)[i]'h_sort₂_len)
      = cmp ((sortBy cmp L₁')[i]'h_sort₁'_len) ((sortBy cmp L₂')[i]'h_sort₂'_len) := by
      -- Bridge through (sortBy L₁')[i] (sortBy L₂)[i] using left compat for L₁/L₁'.
      rw [(h_compat _ _ (h_class₁ i h_sort₁_len h_sort₁'_len) _).1]
      -- Now need cmp (sortBy L₁')[i] (sortBy L₂)[i] = cmp (sortBy L₁')[i] (sortBy L₂')[i].
      -- Use right compat for L₂/L₂'.
      exact (h_compat _ _ (h_class₂ i h_sort₂_len h_sort₂'_len) _).2
    -- The foldl step value at index i.
    show (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder else cmp x.1 x.2) acc
          ((sortBy cmp L₁).zip (sortBy cmp L₂))[i]
       = (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder else cmp x.1 x.2) acc
          ((sortBy cmp L₁').zip (sortBy cmp L₂'))[i]
    rw [List.getElem_zip, List.getElem_zip]
    simp [h_eq_cmp]
  · have hLen' : ¬ L₁'.length = L₂'.length := fun h => hLen (hL₁.trans (h.trans hL₂.symm))
    have h_len_lt : (L₁.length < L₂.length) = (L₁'.length < L₂'.length) := by
      rw [hL₁, hL₂]
    simp [hLen, hLen', h_len_lt]

/-! ## `assignRanks` properties

`assignRanks` produces the dense-rank list. These structural lemmas characterize its
behavior independently of the specific cmp / list:

- `assignRanks_length` — `(assignRanks cmp L).length = L.length`
- `assignRanks_get_fst` — element at position `i` is `L[i]`
- `assignRanks_first_rank` — first element gets rank 0
- `assignRanks_rank_lt_length` — every rank is `< L.length` (for non-empty L)

These power both `convergeLoop_preserves_prefix` (where we need ranks bounded by `n`) and
`calculatePathRankings_*_inv` (where same-class elements need same ranks).
-/

/-- The step function of `assignRanks`'s foldl, factored out to dodge the
`let (revList, lastEntry) := pair` desugaring quirk that prevents direct rewriting. -/
private def assignRanksStep {α : Type} (cmp : α → α → Ordering)
    (pair : List (α × Nat) × Option (α × Nat)) (item : α)
    : List (α × Nat) × Option (α × Nat) :=
  let (revList, lastEntry) := pair
  let rank : Nat :=
    match lastEntry with
    | none                      => 0
    | some (prevItem, prevRank) => if cmp prevItem item == .eq then prevRank else prevRank + 1
  ((item, rank) :: revList, some (item, rank))

private theorem assignRanks_eq_foldl {α : Type} (cmp : α → α → Ordering) (L : List α) :
    assignRanks cmp L = (L.foldl (assignRanksStep cmp) ([], none)).1.reverse := rfl

/-- The step's first component grows by exactly one. -/
private theorem assignRanksStep_fst_length {α : Type} (cmp : α → α → Ordering)
    (revList : List (α × Nat)) (lastEntry : Option (α × Nat)) (item : α) :
    (assignRanksStep cmp (revList, lastEntry) item).1.length = revList.length + 1 := by
  unfold assignRanksStep
  simp

/-- The step prepends `item` to the first-component projection. -/
private theorem assignRanksStep_fst_map_fst {α : Type} (cmp : α → α → Ordering)
    (revList : List (α × Nat)) (lastEntry : Option (α × Nat)) (item : α) :
    (assignRanksStep cmp (revList, lastEntry) item).1.map (·.1)
      = item :: revList.map (·.1) := by
  unfold assignRanksStep
  simp

/-- Length-preserving auxiliary: foldl invariant for the `assignRanks` step. -/
private theorem assignRanks_aux_length {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (revList₀ : List (α × Nat)) (lastEntry₀ : Option (α × Nat)),
      (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1.length
        = revList₀.length + L.length := by
  intro L
  induction L with
  | nil => intros; simp
  | cons a L ih =>
    intros revList₀ lastEntry₀
    rw [List.foldl_cons]
    -- After one step, the new state's revList has size revList₀.length + 1.
    -- IH on (L, new state) gives length = (revList₀.length + 1) + L.length.
    set newState := assignRanksStep cmp (revList₀, lastEntry₀) a with h_newState
    rcases h_pair : newState with ⟨newRev, newLast⟩
    have h_newRev_len : newRev.length = revList₀.length + 1 := by
      rw [show newRev = newState.1 from by rw [h_pair]]
      rw [h_newState]; exact assignRanksStep_fst_length _ _ _ _
    rw [ih newRev newLast, h_newRev_len]
    simp; omega

/-- `assignRanks cmp L` has the same length as `L`. -/
theorem assignRanks_length {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (assignRanks cmp L).length = L.length := by
  rw [assignRanks_eq_foldl, List.length_reverse]
  simpa using assignRanks_aux_length cmp L [] none

/-- Element-preservation auxiliary: foldl invariant for the first-component projection. -/
private theorem assignRanks_aux_map_fst {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (revList₀ : List (α × Nat)) (lastEntry₀ : Option (α × Nat)),
      ((L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1).map (·.1)
        = L.reverse ++ revList₀.map (·.1) := by
  intro L
  induction L with
  | nil => intros; simp
  | cons a L ih =>
    intros revList₀ lastEntry₀
    rw [List.foldl_cons]
    set newState := assignRanksStep cmp (revList₀, lastEntry₀) a with h_newState
    rcases h_pair : newState with ⟨newRev, newLast⟩
    have h_newRev_map : newRev.map (·.1) = a :: revList₀.map (·.1) := by
      rw [show newRev = newState.1 from by rw [h_pair]]
      rw [h_newState]; exact assignRanksStep_fst_map_fst _ _ _ _
    rw [ih newRev newLast, h_newRev_map]
    simp [List.reverse_cons]

/-- The elements of `assignRanks cmp L` (first components) reproduce `L` in order. -/
theorem assignRanks_map_fst {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (assignRanks cmp L).map (·.1) = L := by
  rw [assignRanks_eq_foldl, List.map_reverse, assignRanks_aux_map_fst cmp L [] none]
  simp

theorem assignRanks_getElem_fst {α : Type} (cmp : α → α → Ordering) (L : List α)
    (i : Nat) (h : i < L.length) :
    ((assignRanks cmp L)[i]'(by rw [assignRanks_length]; exact h)).1 = L[i]'h := by
  have h_map := assignRanks_map_fst cmp L
  have hi_arl : i < (assignRanks cmp L).length := by rw [assignRanks_length]; exact h
  -- Use congrArg on getElem? to bridge the two sides.
  have hi_map : i < ((assignRanks cmp L).map (·.1)).length := by
    rw [List.length_map]; exact hi_arl
  have h_via_map : ((assignRanks cmp L).map (·.1))[i]'hi_map = L[i]'h := by
    have hh := congrArg (fun M => M[i]?) h_map
    simp only at hh
    rw [List.getElem?_eq_getElem hi_map, List.getElem?_eq_getElem h] at hh
    exact Option.some.inj hh
  rw [List.getElem_map] at h_via_map
  exact h_via_map

/-! ### `assignRanks` commutes with `map f` when `f` respects `cmp`

For `f : α → α` such that `cmp (f a) (f b) = cmp a b`:
- `assignRanksStep` commutes with the f-mapping of state.
- Lifted through `foldl`, this gives that `assignRanks cmp (L.map f)` equals the f-image
  of `assignRanks cmp L` (componentwise on first coordinates, ranks unchanged).

Foundational for the σ-equivariance pipeline of `calculatePathRankings`. -/

/-- Single-step commutation: applying `f` to all first components of the state and to the
new item commutes with `assignRanksStep`, given `cmp` respects `f`. -/
private theorem assignRanksStep_commutes_with_f_map {α : Type} (cmp : α → α → Ordering)
    (f : α → α) (h_respect : ∀ a b : α, cmp (f a) (f b) = cmp a b)
    (rev : List (α × Nat)) (lastE : Option (α × Nat)) (a : α) :
    assignRanksStep cmp (rev.map (fun e => (f e.1, e.2)),
                         lastE.map (fun e => (f e.1, e.2))) (f a)
    = ((assignRanksStep cmp (rev, lastE) a).1.map (fun e => (f e.1, e.2)),
       (assignRanksStep cmp (rev, lastE) a).2.map (fun e => (f e.1, e.2))) := by
  unfold assignRanksStep
  cases lastE with
  | none => simp
  | some prev =>
    rcases prev with ⟨p1, p2⟩
    simp only [Option.map_some]
    -- New rank: cmp (f p1) (f a) → cmp p1 a by h_respect.
    rw [h_respect p1 a]
    simp [List.map_cons]

/-- Lifted foldl commutation: foldl on the f-mapped list with the f-mapped initial state
gives the f-mapped foldl on the original list. -/
private theorem assignRanks_foldl_map_f {α : Type} (cmp : α → α → Ordering) (f : α → α)
    (h_respect : ∀ a b : α, cmp (f a) (f b) = cmp a b) :
    ∀ (L : List α) (rev : List (α × Nat)) (lastE : Option (α × Nat)),
      (L.map f).foldl (assignRanksStep cmp)
        (rev.map (fun e => (f e.1, e.2)), lastE.map (fun e => (f e.1, e.2)))
      = ((L.foldl (assignRanksStep cmp) (rev, lastE)).1.map (fun e => (f e.1, e.2)),
         (L.foldl (assignRanksStep cmp) (rev, lastE)).2.map (fun e => (f e.1, e.2))) := by
  intro L
  induction L with
  | nil => intros; simp
  | cons a L ih =>
    intros rev lastE
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    rw [assignRanksStep_commutes_with_f_map cmp f h_respect rev lastE a]
    apply ih

/-- **Main commutation**: `assignRanks cmp` distributes over `List.map f` when `f` respects
`cmp`. The first components of the result are f-mapped; ranks are unchanged. -/
theorem assignRanks_map_of_cmp_respect {α : Type} (cmp : α → α → Ordering) (f : α → α)
    (h_respect : ∀ a b : α, cmp (f a) (f b) = cmp a b) (L : List α) :
    assignRanks cmp (L.map f) = (assignRanks cmp L).map (fun e => (f e.1, e.2)) := by
  rw [assignRanks_eq_foldl, assignRanks_eq_foldl]
  have h := assignRanks_foldl_map_f cmp f h_respect L [] none
  simp only [List.map_nil, Option.map_none] at h
  have h_fst : ((L.map f).foldl (assignRanksStep cmp) ([], none)).1
             = ((L.foldl (assignRanksStep cmp) ([], none)).1).map (fun e => (f e.1, e.2)) :=
    congrArg Prod.fst h
  rw [h_fst, List.map_reverse]

/-! ### Relational `assignRanks_map`

`assignRanks_map_of_cmp_respect` (above) requires a *single* `cmp` with
`cmp (f a) (f b) = cmp a b`. The relational form replaces this with the relational
hypothesis `cmp₂ (f a) (f b) = cmp₁ a b` connecting *two different* comparison functions.
This is the form needed by Stage B-rel (in `PathEquivarianceRelational.lean`), where
`cmp₁` uses `vts₁`/`br₁` and `cmp₂` uses the σ-permuted `vts₂`/`br₂`. The fixed-point
form is recovered as the diagonal `cmp₁ = cmp₂`.

Implementation note: the proof structure mirrors the fixed-point version through three
lemmas (single-step commutation → foldl-lifted commutation → top-level), but the foldl
lemma carries a *pointwise* hypothesis on the elements of the (already-processed) prefix
because the `lastEntry` first component is one of those elements. -/

/-- Single-step commutation in the relational form. The membership condition on `b`
captures the invariant that `lastE`'s first component is always a previously-processed
element. -/
private theorem assignRanksStep_commutes_relational {α : Type}
    (cmp₁ cmp₂ : α → α → Ordering) (f : α → α)
    (rev : List (α × Nat)) (lastE : Option (α × Nat)) (a : α)
    (h_resp_a : ∀ b : α, (∃ p, lastE = some p ∧ p.1 = b) → cmp₂ (f b) (f a) = cmp₁ b a) :
    assignRanksStep cmp₂ (rev.map (fun e => (f e.1, e.2)),
                          lastE.map (fun e => (f e.1, e.2))) (f a)
    = ((assignRanksStep cmp₁ (rev, lastE) a).1.map (fun e => (f e.1, e.2)),
       (assignRanksStep cmp₁ (rev, lastE) a).2.map (fun e => (f e.1, e.2))) := by
  unfold assignRanksStep
  cases lastE with
  | none => simp
  | some prev =>
    rcases prev with ⟨p1, p2⟩
    simp only [Option.map_some]
    rw [h_resp_a p1 ⟨(p1, p2), rfl, rfl⟩]
    simp [List.map_cons]

/-- Foldl-lifted relational commutation. The hypothesis quantifies over `b` that's either
in `lastE`'s first-component slot or in the remaining list `L`. -/
private theorem assignRanks_foldl_map_f_relational {α : Type}
    (cmp₁ cmp₂ : α → α → Ordering) (f : α → α) :
    ∀ (L : List α) (rev : List (α × Nat)) (lastE : Option (α × Nat)),
      (∀ a ∈ L, ∀ b : α, (∃ p, lastE = some p ∧ p.1 = b) ∨ b ∈ L →
        cmp₂ (f b) (f a) = cmp₁ b a) →
      (L.map f).foldl (assignRanksStep cmp₂)
        (rev.map (fun e => (f e.1, e.2)), lastE.map (fun e => (f e.1, e.2)))
      = ((L.foldl (assignRanksStep cmp₁) (rev, lastE)).1.map (fun e => (f e.1, e.2)),
         (L.foldl (assignRanksStep cmp₁) (rev, lastE)).2.map (fun e => (f e.1, e.2))) := by
  intro L
  induction L with
  | nil => intros; simp
  | cons a L ih =>
    intros rev lastE h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    rw [assignRanksStep_commutes_relational cmp₁ cmp₂ f rev lastE a
      (fun b hb => h a List.mem_cons_self b (Or.inl hb))]
    apply ih
    intros a' h_a'_in b h_b
    cases h_b with
    | inl h_b_lastE =>
      obtain ⟨p, hp_eq, hp_b⟩ := h_b_lastE
      have h_step_lastE_p1 : p.1 = a := by
        unfold assignRanksStep at hp_eq
        cases lastE with
        | none =>
          simp at hp_eq
          rw [← hp_eq]
        | some prev =>
          rcases prev with ⟨pp1, pp2⟩
          simp only [Option.some.injEq] at hp_eq
          rw [← hp_eq]
      have h_b_eq_a : b = a := h_step_lastE_p1 ▸ hp_b.symm
      apply h a' (List.mem_cons_of_mem _ h_a'_in) b
      exact Or.inr (h_b_eq_a ▸ List.mem_cons_self)
    | inr h_b_in =>
      apply h a' (List.mem_cons_of_mem _ h_a'_in) b
      exact Or.inr (List.mem_cons_of_mem _ h_b_in)

/-- **Main relational commutation**: `assignRanks cmp₂ ∘ map f = (assignRanks cmp₁) ∘ ·.map (lift f)`
when `cmp₂ (f a) (f b) = cmp₁ a b` for `a, b ∈ L`. The fixed-point form
`assignRanks_map_of_cmp_respect` is the diagonal special case `cmp₁ = cmp₂`. -/
theorem assignRanks_map_relational {α : Type}
    (cmp₁ cmp₂ : α → α → Ordering) (f : α → α) (L : List α)
    (h_resp : ∀ a ∈ L, ∀ b ∈ L, cmp₂ (f a) (f b) = cmp₁ a b) :
    assignRanks cmp₂ (L.map f) = (assignRanks cmp₁ L).map (fun e => (f e.1, e.2)) := by
  rw [assignRanks_eq_foldl, assignRanks_eq_foldl]
  have h := assignRanks_foldl_map_f_relational cmp₁ cmp₂ f L [] none ?_
  · simp only [List.map_nil, Option.map_none] at h
    have h_fst : ((L.map f).foldl (assignRanksStep cmp₂) ([], none)).1
               = ((L.foldl (assignRanksStep cmp₁) ([], none)).1).map (fun e => (f e.1, e.2)) :=
      congrArg Prod.fst h
    rw [h_fst, List.map_reverse]
  · intros a' h_a'_in b h_b
    cases h_b with
    | inl h_b_lastE =>
      obtain ⟨_, h_eq, _⟩ := h_b_lastE
      cases h_eq
    | inr h_b_in =>
      exact h_resp b h_b_in a' h_a'_in

/-! ### Rank bound: every rank is `< L.length`

Useful for `convergeLoop_preserves_prefix`: ranks from `assignRanks` end up as values
in the typing array, so bounding them by the input length bounds the prefix-typing
witness `m`. -/

/-- A single `assignRanksStep` from a state bounded by `k` produces a state bounded by
`k + 1`, both for the new revList and the new lastEntry. -/
private theorem assignRanksStep_rank_le {α : Type} (cmp : α → α → Ordering)
    (revList : List (α × Nat)) (lastEntry : Option (α × Nat)) (item : α) (k : Nat)
    (h_rev : ∀ e ∈ revList, e.2 ≤ k)
    (h_last : ∀ e, lastEntry = some e → e.2 ≤ k) :
    (∀ e ∈ (assignRanksStep cmp (revList, lastEntry) item).1, e.2 ≤ k + 1) ∧
    (∀ e, (assignRanksStep cmp (revList, lastEntry) item).2 = some e → e.2 ≤ k + 1) := by
  unfold assignRanksStep
  refine ⟨?_, ?_⟩
  · -- New revList = (item, rank) :: revList₀.
    intro e he
    cases lastEntry with
    | none =>
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · show (0 : Nat) ≤ k + 1; omega
      · exact (h_rev e he).trans (Nat.le_succ k)
    | some prev =>
      rcases prev with ⟨p1, p2⟩
      simp only [List.mem_cons] at he
      have hp2 : p2 ≤ k := h_last (p1, p2) rfl
      rcases he with rfl | he
      · -- e = (item, rank) where rank = p2 or p2 + 1.
        show (if cmp p1 item == Ordering.eq then p2 else p2 + 1) ≤ k + 1
        split_ifs <;> omega
      · exact (h_rev e he).trans (Nat.le_succ k)
  · -- New lastEntry = some (item, rank).
    intro e he
    cases lastEntry with
    | none =>
      simp only [Option.some.injEq] at he
      rw [← he]
      show (0 : Nat) ≤ k + 1; omega
    | some prev =>
      rcases prev with ⟨p1, p2⟩
      have hp2 : p2 ≤ k := h_last (p1, p2) rfl
      simp only [Option.some.injEq] at he
      rw [← he]
      show (if cmp p1 item == Ordering.eq then p2 else p2 + 1) ≤ k + 1
      split_ifs <;> omega

/-- Auxiliary: foldl preserves the rank bound, growing it by `L.length` each call. -/
private theorem assignRanks_aux_rank_le {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (revList₀ : List (α × Nat)) (lastEntry₀ : Option (α × Nat)) (k : Nat),
      (∀ entry ∈ revList₀, entry.2 ≤ k) →
      (∀ entry, lastEntry₀ = some entry → entry.2 ≤ k) →
      ∀ entry ∈ (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1,
        entry.2 ≤ k + L.length := by
  intro L
  induction L with
  | nil =>
    intros revList₀ _ k h_rev _ entry h_in
    simpa using h_rev entry h_in
  | cons a L ih =>
    intros revList₀ lastEntry₀ k h_rev h_last
    rw [List.foldl_cons]
    -- After one step, bound is k + 1.
    have h_step := assignRanksStep_rank_le cmp revList₀ lastEntry₀ a k h_rev h_last
    -- Reify the step result as (newRev, newLast).
    set newRev := (assignRanksStep cmp (revList₀, lastEntry₀) a).1
    set newLast := (assignRanksStep cmp (revList₀, lastEntry₀) a).2
    intro entry h_in
    have := ih newRev newLast (k + 1) h_step.1 h_step.2 entry h_in
    show entry.2 ≤ k + (L.length + 1)
    omega

/-! ### Image density: ranks form a downward-closed set

For any entry in `assignRanks cmp L`, every smaller rank also appears. Hence the rank
set is `{0, 1, ..., max_rank}`. This is the missing density property needed by
`getFrom_image_isPrefix_for_initializePaths` (which feeds `convergeLoop_preserves_prefix`). -/

/-- A single `assignRanksStep` preserves the joint invariant:
- (P') the revList is downward-closed: every entry's rank has all predecessors
  represented in the revList;
- (P2) the lastEntry's pair is in the revList. -/
private theorem assignRanksStep_density_invariant {α : Type} (cmp : α → α → Ordering)
    (revList : List (α × Nat)) (lastEntry : Option (α × Nat)) (item : α)
    (h_P' : ∀ entry ∈ revList, ∀ k ≤ entry.2, ∃ entry' ∈ revList, entry'.2 = k)
    (h_P2 : ∀ x, lastEntry = some x → x ∈ revList) :
    let new := assignRanksStep cmp (revList, lastEntry) item
    (∀ entry ∈ new.1, ∀ k ≤ entry.2, ∃ entry' ∈ new.1, entry'.2 = k) ∧
    (∀ x, new.2 = some x → x ∈ new.1) := by
  refine ⟨?_, ?_⟩
  · -- Preserve P'.
    intro entry h_in k hk
    unfold assignRanksStep at h_in
    cases lastEntry with
    | none =>
      simp only [List.mem_cons] at h_in
      rcases h_in with rfl | h_old
      · -- entry = (item, 0). k ≤ 0 → k = 0. Witness: (item, 0).
        have hk0 : k = 0 := by simp at hk; exact hk
        refine ⟨(item, 0), ?_, hk0.symm⟩
        unfold assignRanksStep; simp [List.mem_cons]
      · -- entry was in old revList. Apply h_P'.
        obtain ⟨e', he'_in, he'_eq⟩ := h_P' entry h_old k hk
        refine ⟨e', ?_, he'_eq⟩
        unfold assignRanksStep; simp [List.mem_cons]; right; exact he'_in
    | some prev =>
      rcases prev with ⟨p1, p2⟩
      have hp_in : (p1, p2) ∈ revList := h_P2 (p1, p2) rfl
      simp only [List.mem_cons] at h_in
      obtain h_eq | h_old := h_in
      · -- entry = (item, new_rank). new_rank = p2 (cmp eq) or p2 + 1.
        rw [h_eq] at hk
        by_cases h_cmp : (cmp p1 item == Ordering.eq) = true
        · -- new_rank = p2.
          simp [h_cmp] at hk  -- hk : k ≤ p2
          obtain ⟨e', he'_in, he'_eq⟩ := h_P' (p1, p2) hp_in k hk
          refine ⟨e', ?_, he'_eq⟩
          unfold assignRanksStep; simp [h_cmp, List.mem_cons]; right; exact he'_in
        · -- new_rank = p2 + 1.
          simp [h_cmp] at hk  -- hk : k ≤ p2 + 1
          by_cases h_k_le_p2 : k ≤ p2
          · obtain ⟨e', he'_in, he'_eq⟩ := h_P' (p1, p2) hp_in k h_k_le_p2
            refine ⟨e', ?_, he'_eq⟩
            unfold assignRanksStep; simp [h_cmp, List.mem_cons]; right; exact he'_in
          · -- ¬ (k ≤ p2), so k > p2, combined with k ≤ p2 + 1: k = p2 + 1.
            have h_k_eq : k = p2 + 1 := by omega
            refine ⟨(item, p2 + 1), ?_, h_k_eq.symm⟩
            unfold assignRanksStep; simp [h_cmp, List.mem_cons]
      · -- entry was in old revList. Apply h_P'.
        obtain ⟨e', he'_in, he'_eq⟩ := h_P' entry h_old k hk
        refine ⟨e', ?_, he'_eq⟩
        unfold assignRanksStep
        by_cases h_cmp_dec : (cmp p1 item == Ordering.eq) = true
        · simp [h_cmp_dec, List.mem_cons]; right; exact he'_in
        · simp [h_cmp_dec, List.mem_cons]; right; exact he'_in
  · -- Preserve P2.
    intro x hx
    unfold assignRanksStep at hx ⊢
    cases lastEntry with
    | none =>
      simp only [Option.some.injEq] at hx
      subst hx
      simp [List.mem_cons]
    | some prev =>
      simp only [Option.some.injEq] at hx
      subst hx
      simp [List.mem_cons]

/-- Foldl-level density invariant: maintained through the whole `assignRanks` foldl. -/
private theorem assignRanks_aux_density {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (revList₀ : List (α × Nat)) (lastEntry₀ : Option (α × Nat)),
      (∀ entry ∈ revList₀, ∀ k ≤ entry.2, ∃ entry' ∈ revList₀, entry'.2 = k) →
      (∀ x, lastEntry₀ = some x → x ∈ revList₀) →
      (∀ entry ∈ (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1,
        ∀ k ≤ entry.2,
          ∃ entry' ∈ (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1, entry'.2 = k) ∧
      (∀ x, (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).2 = some x →
        x ∈ (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1) := by
  intro L
  induction L with
  | nil => intros; exact ⟨‹_›, ‹_›⟩
  | cons a L ih =>
    intros revList₀ lastEntry₀ h_P' h_P2
    rw [List.foldl_cons]
    -- After one step: state = assignRanksStep cmp (revList₀, lastEntry₀) a.
    -- Apply step lemma to get new (P', P2), then apply IH.
    have h_step := assignRanksStep_density_invariant cmp revList₀ lastEntry₀ a h_P' h_P2
    -- Reify the step result for IH application.
    set newState := assignRanksStep cmp (revList₀, lastEntry₀) a with h_newState
    rcases h_pair : newState with ⟨newRev, newLast⟩
    have h_new_P' : ∀ entry ∈ newRev, ∀ k ≤ entry.2, ∃ entry' ∈ newRev, entry'.2 = k := by
      intro entry h_in k hk
      have h_in' : entry ∈ newState.1 := by rw [h_pair]; exact h_in
      rw [h_newState] at h_in'
      obtain ⟨e', he'_in, he'_eq⟩ := h_step.1 entry h_in' k hk
      have he'_in' : e' ∈ newState.1 := by rw [h_newState]; exact he'_in
      rw [h_pair] at he'_in'
      exact ⟨e', he'_in', he'_eq⟩
    have h_new_P2 : ∀ x, newLast = some x → x ∈ newRev := by
      intro x hx
      have hx' : newState.2 = some x := by rw [h_pair]; exact hx
      rw [h_newState] at hx'
      have := h_step.2 x hx'
      have h_in_state : x ∈ newState.1 := by rw [h_newState]; exact this
      rw [h_pair] at h_in_state
      exact h_in_state
    exact ih newRev newLast h_new_P' h_new_P2

/-- The image of `assignRanks cmp L` is downward-closed: for any entry, all smaller ranks
appear. Combined with `assignRanks_rank_lt_length`, the rank set is `{0, ..., max_rank}`. -/
theorem assignRanks_image_dense {α : Type} (cmp : α → α → Ordering) (L : List α)
    (entry : α × Nat) (h_in : entry ∈ assignRanks cmp L) :
    ∀ k ≤ entry.2, ∃ entry' ∈ assignRanks cmp L, entry'.2 = k := by
  intros k hk
  have h_initP' : ∀ e ∈ ([] : List (α × Nat)), ∀ k' ≤ e.2,
      ∃ e' ∈ ([] : List (α × Nat)), e'.2 = k' := fun _ he _ _ => by simp at he
  have h_initP2 : ∀ x, (none : Option (α × Nat)) = some x → x ∈ ([] : List (α × Nat)) :=
    fun _ h => by cases h
  have h_aux := assignRanks_aux_density cmp L [] none h_initP' h_initP2
  rw [assignRanks_eq_foldl, List.mem_reverse] at h_in
  obtain ⟨entry', he'_in, he'_eq⟩ := h_aux.1 entry h_in k hk
  refine ⟨entry', ?_, he'_eq⟩
  rw [assignRanks_eq_foldl, List.mem_reverse]
  exact he'_in

/-- Every rank in `assignRanks cmp L` is `< L.length`. (Vacuous for empty `L`.) -/
theorem assignRanks_rank_lt_length {α : Type} (cmp : α → α → Ordering) (L : List α) :
    ∀ entry ∈ assignRanks cmp L, entry.2 < L.length := by
  intro entry h_entry
  rcases L with _ | ⟨a, L'⟩
  · simp [assignRanks_eq_foldl] at h_entry
  · -- Non-empty L: handle the first step manually so we get bound 0 instead of 1.
    rw [assignRanks_eq_foldl, List.mem_reverse, List.foldl_cons] at h_entry
    -- After processing `a`: state = ([(a, 0)], some (a, 0)). Then aux on L' with k = 0.
    have h_first : assignRanksStep cmp ([], none) a = ([(a, 0)], some (a, 0)) := by
      unfold assignRanksStep; rfl
    rw [h_first] at h_entry
    have h_rev : ∀ e ∈ [(a, 0)], e.2 ≤ 0 := by
      intros e he; simp only [List.mem_singleton] at he; rw [he]
    have h_last : ∀ e, some (a, 0) = some e → e.2 ≤ 0 := by
      intros e he; simp only [Option.some.injEq] at he; rw [← he]
    have := assignRanks_aux_rank_le cmp L' [(a, 0)] (some (a, 0)) 0 h_rev h_last entry h_entry
    show entry.2 < L'.length + 1
    omega

/-! ### Per-position rank bounds (`assignRanks` ranks at position `k` ≤ `k`)

Used by `Invariants.lean`'s Phase 3 to bound the new typing values for unique-typed
vertices. The key fact: in the dense ranking, position `k` of the sorted list gets a
rank ≤ k (strictly less only when consecutive items collapse into the same class). -/

/-- **P3.B aux** lastEntry's rank tracks step count: after processing `L`, the lastEntry
(if any) has rank `≤ prev_rank + L.length` (where `prev_rank` is the input lastEntry's
rank, or `L.length - 1` if input lastEntry is `none`). -/
private theorem assignRanksFoldl_lastEntry_rank_le {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (initRev : List (α × Nat)) (initLast : Option (α × Nat)),
      ∀ e, (L.foldl (assignRanksStep cmp) (initRev, initLast)).2 = some e →
        e.2 ≤ initLast.elim (L.length - 1) (fun prev => prev.2 + L.length) := by
  intro L
  induction L with
  | nil =>
    intros initRev initLast e he
    rw [List.foldl_nil] at he
    cases hlast : initLast with
    | none =>
      rw [hlast] at he
      exact absurd he (by simp)
    | some prev =>
      rw [hlast] at he
      simp only [Option.some.injEq] at he
      simp only [Option.elim_some, List.length_nil, Nat.add_zero]
      rw [← he]
  | cons a L' ih =>
    intros initRev initLast e he
    rw [List.foldl_cons] at he
    -- After step a: state' = (newRev, newLast) with newLast = some (a, r_a) where
    -- r_a depends on initLast.
    set state' := assignRanksStep cmp (initRev, initLast) a with hstate'
    -- Identify state'.2.
    have h_state'_2 : ∃ r, state'.2 = some (a, r) ∧
        r ≤ initLast.elim 0 (fun prev => prev.2 + 1) := by
      cases hlast : initLast with
      | none =>
        refine ⟨0, ?_, by simp⟩
        rw [hstate', hlast]
        unfold assignRanksStep
        rfl
      | some prev =>
        refine ⟨if cmp prev.1 a == .eq then prev.2 else prev.2 + 1, ?_, ?_⟩
        · rw [hstate', hlast]
          unfold assignRanksStep
          rfl
        · simp only [Option.elim_some]
          split_ifs <;> omega
    obtain ⟨r, h_state'_2_eq, h_r⟩ := h_state'_2
    -- Apply ih on L' from state'.
    have h_ih := ih state'.1 state'.2 e he
    rw [h_state'_2_eq] at h_ih
    simp only [Option.elim_some] at h_ih
    -- h_ih : e.2 ≤ r + L'.length.
    cases hlast : initLast with
    | none =>
      have h_r_eq : r = 0 := by
        have := h_r
        simp [hlast] at this
        omega
      simp only [Option.elim_none]
      rw [h_r_eq] at h_ih
      simp only [Nat.zero_add] at h_ih
      -- h_ih : e.2 ≤ L'.length.
      show e.2 ≤ (List.length L' + 1) - 1
      omega
    | some prev =>
      have h_r' : r ≤ prev.2 + 1 := by
        have := h_r
        simp [hlast] at this
        exact this
      simp only [Option.elim_some]
      show e.2 ≤ prev.2 + (List.length L' + 1)
      omega

/-- **P3.B aux** Decomposition for `assignRanks` on `snoc`: the result is the result on
the prefix appended with one entry whose rank is bounded by the prefix length. -/
private theorem assignRanks_snoc_decompose {α : Type} (cmp : α → α → Ordering)
    (L : List α) (a : α) :
    ∃ r_a : Nat, assignRanks cmp (L ++ [a]) = assignRanks cmp L ++ [(a, r_a)] ∧
      r_a ≤ L.length := by
  rw [assignRanks_eq_foldl, assignRanks_eq_foldl, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  -- Destructure the state explicitly.
  rcases h_pair : L.foldl (assignRanksStep cmp) ([], none) with ⟨rev, lastE⟩
  -- assignRanksStep cmp (rev, lastE) a now reduces concretely.
  cases hlast : lastE with
  | none =>
    refine ⟨0, ?_, by omega⟩
    show ((a, 0) :: rev).reverse = rev.reverse ++ [(a, 0)]
    rw [List.reverse_cons]
  | some prev =>
    rcases prev with ⟨p1, p2⟩
    refine ⟨if cmp p1 a == .eq then p2 else p2 + 1, ?_, ?_⟩
    · show ((a, if cmp p1 a == .eq then p2 else p2 + 1) :: rev).reverse
          = rev.reverse ++ [(a, if cmp p1 a == .eq then p2 else p2 + 1)]
      rw [List.reverse_cons]
    · -- Bound via aux lemma.
      have h_aux := assignRanksFoldl_lastEntry_rank_le cmp L [] none (p1, p2)
      have h_st_eq : (L.foldl (assignRanksStep cmp) ([], none)).2 = some (p1, p2) := by
        rw [h_pair]; exact hlast
      have h_p2 := h_aux h_st_eq
      simp at h_p2
      -- h_p2 : p2 ≤ L.length - 1.
      have h_L_pos : 0 < L.length := by
        by_contra h_zero
        have : L = [] := by
          cases L with
          | nil => rfl
          | cons _ _ => simp at h_zero
        rw [this] at h_pair
        simp at h_pair
        rw [← h_pair.2] at hlast
        exact absurd hlast (by simp)
      split_ifs <;> omega

/-- **P3.C aux** Sharper snoc decomposition: gives the exact formula for the new rank
in terms of the lastEntry of the partial fold. -/
private theorem assignRanks_snoc_decompose_strict {α : Type} (cmp : α → α → Ordering)
    (L : List α) (a : α) (rev : List (α × Nat)) (lastL : Option (α × Nat))
    (h_pair : L.foldl (assignRanksStep cmp) ([], none) = (rev, lastL)) :
    assignRanks cmp (L ++ [a]) =
      assignRanks cmp L ++
      [(a, lastL.elim 0 (fun prev => if cmp prev.1 a == .eq then prev.2 else prev.2 + 1))] := by
  rw [assignRanks_eq_foldl, assignRanks_eq_foldl, List.foldl_append,
      List.foldl_cons, List.foldl_nil, h_pair]
  cases hlast : lastL with
  | none =>
    show ((a, 0) :: rev).reverse = rev.reverse ++ [(a, 0)]
    rw [List.reverse_cons]
  | some prev =>
    rcases prev with ⟨p1, p2⟩
    show ((a, if cmp p1 a == .eq then p2 else p2 + 1) :: rev).reverse
         = rev.reverse ++ [(a, if cmp p1 a == .eq then p2 else p2 + 1)]
    rw [List.reverse_cons]

/-- For non-empty `L`, the foldl's `lastEntry` has first component `L.getLast`. -/
private theorem assignRanks_foldl_lastEntry_fst {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (h : L ≠ []),
      ∃ r, (L.foldl (assignRanksStep cmp) ([], none)).2 = some (L.getLast h, r) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton L' a _ =>
    intro _
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases h_pair : L'.foldl (assignRanksStep cmp) ([], none) with ⟨rev, lastE⟩
    cases hlast : lastE with
    | none =>
      refine ⟨0, ?_⟩
      show (assignRanksStep cmp (rev, none) a).2 = some ((L' ++ [a]).getLast _, 0)
      rw [show (L' ++ [a]).getLast (by simp) = a from List.getLast_append_singleton L']
      rfl
    | some prev =>
      rcases prev with ⟨p1, p2⟩
      refine ⟨if cmp p1 a == .eq then p2 else p2 + 1, ?_⟩
      show (assignRanksStep cmp (rev, some (p1, p2)) a).2 = some ((L' ++ [a]).getLast _, _)
      rw [show (L' ++ [a]).getLast (by simp) = a from List.getLast_append_singleton L']
      rfl

/-- **P3.B** Rank at position `k` in `assignRanks cmp L` is `≤ k`. -/
theorem assignRanks_rank_le_pos {α : Type} (cmp : α → α → Ordering) (L : List α)
    (k : Nat) (hk : k < L.length) :
    ((assignRanks cmp L)[k]'(by rw [assignRanks_length]; exact hk)).2 ≤ k := by
  induction L using List.reverseRecOn generalizing k with
  | nil => simp at hk
  | append_singleton L' a ih =>
    obtain ⟨r_a, h_decomp, h_r_a⟩ := assignRanks_snoc_decompose cmp L' a
    have h_len_lhs : (assignRanks cmp L').length = L'.length := assignRanks_length cmp L'
    have h_k_lt : k < L'.length + 1 := by
      have := hk; simp [List.length_append] at this; omega
    have h_k_lt_full : k < (assignRanks cmp (L' ++ [a])).length := by
      rw [assignRanks_length]; exact hk
    rcases Nat.lt_or_ge k L'.length with h_k_lt_L' | h_k_ge_L'
    · -- k < L'.length: position k is in `assignRanks cmp L'`.
      have h_assign_get : (assignRanks cmp (L' ++ [a]))[k]'h_k_lt_full =
          (assignRanks cmp L' ++ [(a, r_a)])[k]'(by simp [h_len_lhs]; omega) := by
        congr 1
      rw [h_assign_get]
      have h_lt_lhs : k < (assignRanks cmp L').length := by rw [h_len_lhs]; exact h_k_lt_L'
      rw [List.getElem_append_left h_lt_lhs]
      exact ih k h_k_lt_L'
    · -- k = L'.length: position k is the appended entry.
      have h_k_eq : k = L'.length := by omega
      have h_assign_get : (assignRanks cmp (L' ++ [a]))[k]'h_k_lt_full =
          (assignRanks cmp L' ++ [(a, r_a)])[k]'(by simp [h_len_lhs]; omega) := by
        congr 1
      rw [h_assign_get]
      have h_k_eq_len : k = (assignRanks cmp L').length := by rw [h_len_lhs]; exact h_k_eq
      rw [List.getElem_append_right (by rw [← h_k_eq_len])]
      simp [h_k_eq_len]
      omega

/-! ### Rank monotonicity

`assignRanks` produces ranks that are non-decreasing along the output list. This is
because each `assignRanksStep` either keeps the rank (when `cmp prev item == .eq`) or
increments it by exactly one. The proof tracks the joint invariant:
- the foldl's `revList` is pairwise non-increasing (head has the largest rank);
- the `lastEntry` equals the head of `revList` (so it tracks the most recent rank).

After reversing, the output `assignRanks cmp L` is pairwise non-decreasing in rank. -/

/-- One step of `assignRanksStep` preserves: revList head matches lastEntry, AND revList
is pairwise non-increasing in rank from head to tail. -/
private theorem assignRanksStep_preserves_invariant {α : Type} (cmp : α → α → Ordering)
    (revList : List (α × Nat)) (lastEntry : Option (α × Nat)) (item : α)
    (h_pw : revList.Pairwise (fun a b => b.2 ≤ a.2))
    (h_head : revList.head? = lastEntry) :
    (assignRanksStep cmp (revList, lastEntry) item).1.Pairwise (fun a b => b.2 ≤ a.2) ∧
    (assignRanksStep cmp (revList, lastEntry) item).1.head?
      = (assignRanksStep cmp (revList, lastEntry) item).2 := by
  unfold assignRanksStep
  cases lastEntry with
  | none =>
    -- lastEntry = none ⟹ revList = [] (since head? = none).
    have h_rev_empty : revList = [] := by
      cases revList with
      | nil => rfl
      | cons => simp at h_head
    subst h_rev_empty
    refine ⟨?_, ?_⟩
    · exact List.pairwise_singleton _ _
    · simp
  | some prev =>
    -- revList = head :: tail. h_head says head = prev.
    rcases revList with _ | ⟨head, tail⟩
    · simp at h_head
    · simp only [List.head?_cons, Option.some.injEq] at h_head
      -- h_head : head = prev
      rcases prev with ⟨p1, p2⟩
      have h_head_eq : head = (p1, p2) := h_head
      subst h_head_eq
      refine ⟨?_, ?_⟩
      · -- ((item, new_rank) :: (p1, p2) :: tail).Pairwise.
        apply List.Pairwise.cons _ h_pw
        intro b hb
        rcases List.mem_cons.mp hb with h_eq | h_in
        · subst h_eq
          show (p1, p2).2 ≤ (if cmp p1 item == Ordering.eq then p2 else p2 + 1)
          split_ifs <;> omega
        · -- b ∈ tail; b.2 ≤ p2 by IH.
          have h_tail_le : ∀ x ∈ tail, x.2 ≤ p2 :=
            (List.pairwise_cons.mp h_pw).1
          have hb_le : b.2 ≤ p2 := h_tail_le b h_in
          show b.2 ≤ (if cmp p1 item == Ordering.eq then p2 else p2 + 1)
          split_ifs <;> omega
      · simp

/-- The joint invariant lifted through `foldl`. -/
private theorem assignRanks_foldl_invariant {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α) (revList₀ : List (α × Nat)) (lastEntry₀ : Option (α × Nat)),
      revList₀.Pairwise (fun a b => b.2 ≤ a.2) →
      revList₀.head? = lastEntry₀ →
      (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1.Pairwise
        (fun a b => b.2 ≤ a.2) ∧
      (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).1.head?
        = (L.foldl (assignRanksStep cmp) (revList₀, lastEntry₀)).2 := by
  intro L
  induction L with
  | nil => intros; exact ⟨‹_›, ‹_›⟩
  | cons a L ih =>
    intros revList₀ lastEntry₀ h_pw h_head
    rw [List.foldl_cons]
    obtain ⟨h_pw', h_head'⟩ :=
      assignRanksStep_preserves_invariant cmp revList₀ lastEntry₀ a h_pw h_head
    set newState := assignRanksStep cmp (revList₀, lastEntry₀) a
    exact ih newState.1 newState.2 h_pw' h_head'

/-- **Pairwise rank ordering**: `assignRanks cmp L` has ranks non-decreasing along the list. -/
theorem assignRanks_pairwise_rank_le {α : Type} (cmp : α → α → Ordering) (L : List α) :
    (assignRanks cmp L).Pairwise (fun a b => a.2 ≤ b.2) := by
  rw [assignRanks_eq_foldl]
  have h_inv :=
    (assignRanks_foldl_invariant cmp L [] none List.Pairwise.nil rfl).1
  exact List.pairwise_reverse.mpr h_inv

/-- **Rank monotonicity**: rank at position `i` is `≤` rank at position `j` for `i ≤ j`. -/
theorem assignRanks_rank_monotone {α : Type} (cmp : α → α → Ordering) (L : List α)
    (i j : Nat) (hi : i ≤ j) (hj : j < L.length) :
    ((assignRanks cmp L)[i]'(by rw [assignRanks_length]; omega)).2
      ≤ ((assignRanks cmp L)[j]'(by rw [assignRanks_length]; exact hj)).2 := by
  have h_pw := assignRanks_pairwise_rank_le cmp L
  have hi' : i < (assignRanks cmp L).length := by rw [assignRanks_length]; omega
  have hj' : j < (assignRanks cmp L).length := by rw [assignRanks_length]; exact hj
  rcases Nat.lt_or_eq_of_le hi with h_lt | h_eq
  · exact List.pairwise_iff_getElem.mp h_pw i j hi' hj' h_lt
  · -- i = j; ranks equal.
    subst h_eq
    exact Nat.le_refl _

/-- **P3.C aux** (combined with lastEntry tracking): Strong invariant via reverseRecOn
induction. For lists where consecutive cmps differ for `i + 1 < L.length`, the rank at
every position equals the position, AND the foldl's lastEntry has rank `L.length - 1`
(for non-empty L). -/
private theorem assignRanks_strong_invariant {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List α),
      (∀ i (h : i + 1 < L.length),
        cmp (L[i]'(Nat.lt_of_succ_lt h)) (L[i+1]'h) ≠ .eq) →
      (∀ k (hk : k < L.length),
        ((assignRanks cmp L)[k]'(by rw [assignRanks_length]; exact hk)).2 = k) ∧
      (∀ (h_ne : L ≠ []), ∃ a,
        (L.foldl (assignRanksStep cmp) ([], none)).2 = some (a, L.length - 1)) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨?_, ?_⟩
    · intros _ hk; simp at hk
    · intros h; exact absurd rfl h
  | append_singleton L' a ih =>
    intro h_distinct
    -- Restrict h_distinct to L'.
    have h_distinct_L' : ∀ i (h : i + 1 < L'.length),
        cmp (L'[i]'(Nat.lt_of_succ_lt h)) (L'[i+1]'h) ≠ .eq := by
      intro i hi
      have h_in_L : i + 1 < (L' ++ [a]).length := by simp; omega
      have h_orig := h_distinct i h_in_L
      have h_get_i : (L' ++ [a])[i]'(Nat.lt_of_succ_lt h_in_L) = L'[i]'(Nat.lt_of_succ_lt hi) := by
        rw [List.getElem_append_left (Nat.lt_of_succ_lt hi)]
      have h_get_i1 : (L' ++ [a])[i+1]'h_in_L = L'[i+1]'hi := by
        rw [List.getElem_append_left hi]
      rw [h_get_i, h_get_i1] at h_orig
      exact h_orig
    obtain ⟨ih_rank, ih_lastEntry⟩ := ih h_distinct_L'
    -- Key info: the snoc decomposition.
    rcases h_pair : L'.foldl (assignRanksStep cmp) ([], none) with ⟨rev, lastE⟩
    have h_decomp_strict := assignRanks_snoc_decompose_strict cmp L' a rev lastE h_pair
    have h_len_lhs : (assignRanks cmp L').length = L'.length := assignRanks_length cmp L'
    refine ⟨?_, ?_⟩
    · -- Rank at every position k of assignRanks (L' ++ [a]) = k.
      intros k hk
      have h_k_lt_full : k < (assignRanks cmp (L' ++ [a])).length := by
        rw [assignRanks_length]; exact hk
      have h_assign_get : (assignRanks cmp (L' ++ [a]))[k]'h_k_lt_full =
          (assignRanks cmp L' ++ [(a, lastE.elim 0 (fun prev =>
            if cmp prev.1 a == .eq then prev.2 else prev.2 + 1))])[k]'(by
              simp [h_len_lhs]
              have := hk; simp [List.length_append] at this; omega) := by
        congr 1
      rw [h_assign_get]
      rcases Nat.lt_or_ge k L'.length with h_k_lt_L' | h_k_ge_L'
      · -- k < L'.length: use ih_rank.
        have h_lt_lhs : k < (assignRanks cmp L').length := by rw [h_len_lhs]; exact h_k_lt_L'
        rw [List.getElem_append_left h_lt_lhs]
        exact ih_rank k h_k_lt_L'
      · -- k = L'.length: appended entry, rank = lastE.elim 0 (...).
        have h_k_eq : k = L'.length := by
          have := hk; simp [List.length_append] at this; omega
        have h_k_eq_len : k = (assignRanks cmp L').length := by rw [h_len_lhs]; exact h_k_eq
        rw [List.getElem_append_right (by rw [← h_k_eq_len])]
        simp [h_k_eq_len]
        -- Goal: lastE.elim 0 (...) = L'.length.
        cases hlast : lastE with
        | none =>
          -- lastE = none ⟹ L' = [].
          have h_L'_empty : L' = [] := by
            by_contra h_L'_ne
            obtain ⟨a', h_some⟩ := ih_lastEntry h_L'_ne
            rw [h_pair] at h_some
            simp at h_some
            rw [hlast] at h_some
            exact absurd h_some (by simp)
          subst h_L'_empty
          rfl
        | some prev =>
          -- L' ≠ []. Use ih_lastEntry to get prev's rank = L'.length - 1.
          rcases prev with ⟨p1, p2⟩
          have h_L'_ne : L' ≠ [] := by
            intro h_L'_eq
            rw [h_L'_eq] at h_pair
            simp at h_pair
            rw [← h_pair.2] at hlast
            exact absurd hlast (by simp)
          obtain ⟨a', h_some⟩ := ih_lastEntry h_L'_ne
          rw [h_pair] at h_some
          simp at h_some
          rw [hlast] at h_some
          -- h_some : some (a', L'.length - 1) = some (p1, p2)
          simp only [Option.some.injEq, Prod.mk.injEq] at h_some
          obtain ⟨h_a'_eq_p1, h_p2_eq⟩ := h_some
          -- p1 = L'.getLast h_L'_ne (from assignRanks_foldl_lastEntry_fst).
          obtain ⟨_, h_fst⟩ := assignRanks_foldl_lastEntry_fst cmp L' h_L'_ne
          rw [h_pair] at h_fst
          simp at h_fst
          rw [hlast] at h_fst
          simp only [Option.some.injEq, Prod.mk.injEq] at h_fst
          have h_p1_eq : p1 = L'.getLast h_L'_ne := h_fst.1
          -- cmp p1 a ≠ .eq follows from h_distinct.
          have h_cmp_ne : cmp p1 a ≠ .eq := by
            have h_lt : L'.length - 1 + 1 < (L' ++ [a]).length := by
              simp; have := List.length_pos_iff.mpr h_L'_ne; omega
            have h_h_distinct := h_distinct (L'.length - 1) h_lt
            -- (L' ++ [a])[L'.length - 1] = L'[L'.length - 1] = L'.getLast = p1.
            have h_get_pre : (L' ++ [a])[L'.length - 1]'(by simp; omega) =
                L'[L'.length - 1]'(by have := List.length_pos_iff.mpr h_L'_ne; omega) := by
              rw [List.getElem_append_left]
            have h_get_post : (L' ++ [a])[L'.length - 1 + 1]'h_lt = a := by
              have h_pos := List.length_pos_iff.mpr h_L'_ne
              have h_at_len : (L' ++ [a])[L'.length]'(by simp) = a := by
                rw [List.getElem_append_right (Nat.le_refl _)]
                simp
              have h_idx_cast : (L' ++ [a])[L'.length - 1 + 1]'h_lt
                              = (L' ++ [a])[L'.length]'(by simp) := by
                congr 1; omega
              rw [h_idx_cast]; exact h_at_len
            rw [h_get_pre, h_get_post] at h_h_distinct
            -- L'[L'.length - 1] = L'.getLast = p1.
            have h_getLast_eq : L'[L'.length - 1]'(by
                have := List.length_pos_iff.mpr h_L'_ne; omega) = L'.getLast h_L'_ne := by
              rw [List.getLast_eq_getElem]
            rw [h_getLast_eq, ← h_p1_eq] at h_h_distinct
            exact h_h_distinct
          -- Now compute the rank.
          simp only [Option.elim_some]
          split_ifs with h_eq
          · exact absurd h_eq h_cmp_ne
          · rw [h_p2_eq]
            have := List.length_pos_iff.mpr h_L'_ne
            simp [h_len_lhs]
            omega
    · -- lastEntry of foldl (L' ++ [a]) has rank L'.length = (L' ++ [a]).length - 1.
      intros _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, h_pair]
      cases hlast : lastE with
      | none =>
        refine ⟨a, ?_⟩
        show (assignRanksStep cmp (rev, none) a).2 = some (a, (L' ++ [a]).length - 1)
        unfold assignRanksStep
        simp
        -- Need: 0 = (L' ++ [a]).length - 1.
        -- From hlast (lastE = none) and h_pair: L' = [].
        have h_L'_empty : L' = [] := by
          by_contra h_L'_ne
          obtain ⟨a', h_some⟩ := ih_lastEntry h_L'_ne
          rw [h_pair] at h_some
          simp at h_some
          rw [hlast] at h_some
          exact absurd h_some (by simp)
        simp [h_L'_empty]
      | some prev =>
        rcases prev with ⟨p1, p2⟩
        refine ⟨a, ?_⟩
        show (assignRanksStep cmp (rev, some (p1, p2)) a).2 = some (a, (L' ++ [a]).length - 1)
        -- L' must be non-empty (else lastE = none).
        have h_L'_ne : L' ≠ [] := by
          intro h_L'_eq
          rw [h_L'_eq] at h_pair
          simp at h_pair
          rw [← h_pair.2] at hlast
          exact absurd hlast (by simp)
        have h_pos := List.length_pos_iff.mpr h_L'_ne
        -- p2 = L'.length - 1 (from ih_lastEntry).
        obtain ⟨a', h_some⟩ := ih_lastEntry h_L'_ne
        rw [h_pair] at h_some
        simp at h_some
        rw [hlast] at h_some
        simp only [Option.some.injEq, Prod.mk.injEq] at h_some
        have h_p2_eq : p2 = L'.length - 1 := h_some.2
        -- p1 = L'.getLast h_L'_ne (from assignRanks_foldl_lastEntry_fst).
        obtain ⟨_, h_fst⟩ := assignRanks_foldl_lastEntry_fst cmp L' h_L'_ne
        rw [h_pair] at h_fst
        simp at h_fst
        rw [hlast] at h_fst
        simp only [Option.some.injEq, Prod.mk.injEq] at h_fst
        have h_p1_eq : p1 = L'.getLast h_L'_ne := h_fst.1
        -- cmp p1 a ≠ .eq (from h_distinct, similar to the rank conjunct).
        have h_cmp_ne : cmp p1 a ≠ .eq := by
          have h_lt : L'.length - 1 + 1 < (L' ++ [a]).length := by
            simp; omega
          have h_h_distinct := h_distinct (L'.length - 1) h_lt
          have h_get_pre : (L' ++ [a])[L'.length - 1]'(by simp; omega) =
              L'[L'.length - 1]'(by omega) := by
            rw [List.getElem_append_left]
          have h_get_post : (L' ++ [a])[L'.length - 1 + 1]'h_lt = a := by
            have h_at_len : (L' ++ [a])[L'.length]'(by simp) = a := by
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp
            have h_idx_cast : (L' ++ [a])[L'.length - 1 + 1]'h_lt
                            = (L' ++ [a])[L'.length]'(by simp) := by
              congr 1; omega
            rw [h_idx_cast]; exact h_at_len
          rw [h_get_pre, h_get_post] at h_h_distinct
          have h_getLast_eq : L'[L'.length - 1]'(by omega) = L'.getLast h_L'_ne := by
            rw [List.getLast_eq_getElem]
          rw [h_getLast_eq, ← h_p1_eq] at h_h_distinct
          exact h_h_distinct
        -- Now compute the lastEntry's rank.
        unfold assignRanksStep
        simp only []
        -- Goal: ((a, if cmp p1 a == .eq then p2 else p2 + 1) :: rev, some (a, ...)).2 = some (a, ...).
        congr 1
        simp only [Prod.mk.injEq, true_and]
        split_ifs with h_eq
        · simp at h_eq; exact absurd h_eq h_cmp_ne
        · -- Goal: p2 + 1 = (L' ++ [a]).length - 1.
          rw [h_p2_eq]
          simp
          omega

/-- **P3.C** Rank at position `k` in `assignRanks cmp L` equals `k`, when consecutive
cmps differ throughout `L`. -/
theorem assignRanks_rank_eq_pos_when_distinct {α : Type} (cmp : α → α → Ordering)
    (L : List α)
    (h_distinct : ∀ i (h : i + 1 < L.length),
      cmp (L[i]'(Nat.lt_of_succ_lt h)) (L[i+1]'h) ≠ .eq)
    (k : Nat) (hk : k < L.length) :
    ((assignRanks cmp L)[k]'(by rw [assignRanks_length]; exact hk)).2 = k :=
  (assignRanks_strong_invariant cmp L h_distinct).1 k hk

/-- **Append-preservation**: rank at position `k` in `assignRanks cmp (A ++ B)` equals
the rank at position `k` in `assignRanks cmp A` (for `k < A.length`). Proved via
right-snoc induction on `B` using `assignRanks_snoc_decompose`. -/
theorem assignRanks_rank_eq_of_prefix {α : Type} (cmp : α → α → Ordering)
    (A B : List α) (k : Nat) (hk : k < A.length) :
    ((assignRanks cmp (A ++ B))[k]'(by
        rw [assignRanks_length, List.length_append]; omega)).2
      = ((assignRanks cmp A)[k]'(by rw [assignRanks_length]; exact hk)).2 := by
  induction B using List.reverseRecOn with
  | nil =>
    -- A ++ [] reduces to A. Show that the two getElem's agree by congruence.
    simp
  | append_singleton B' b ih =>
    -- A ++ (B' ++ [b]) = (A ++ B') ++ [b]. By snoc_decompose, the rank at k < A.length
    -- in assignRanks ((A ++ B') ++ [b]) = (assignRanks (A ++ B') ++ [(b, _)])[k]
    -- = (assignRanks (A ++ B'))[k].2 (by getElem_append_left, since k < A++B'.length).
    obtain ⟨r_b, h_decomp, _⟩ := assignRanks_snoc_decompose cmp (A ++ B') b
    have h_assign_AB'_len : (assignRanks cmp (A ++ B')).length = (A ++ B').length :=
      assignRanks_length _ _
    have h_k_lt_AB' : k < (A ++ B').length := by
      simp [List.length_append]; omega
    have h_k_lt_assign_AB' : k < (assignRanks cmp (A ++ B')).length := by
      rw [h_assign_AB'_len]; exact h_k_lt_AB'
    have h_k_lt_full : k < (assignRanks cmp (A ++ B' ++ [b])).length := by
      rw [assignRanks_length]; simp [List.length_append]; omega
    have h_assoc : A ++ (B' ++ [b]) = (A ++ B') ++ [b] := by simp
    have h_get_eq : (assignRanks cmp (A ++ (B' ++ [b])))[k]'(by
            rw [assignRanks_length, List.length_append, List.length_append]; omega)
        = (assignRanks cmp ((A ++ B') ++ [b]))[k]'h_k_lt_full := by
      congr 1
      rw [h_assoc]
    rw [h_get_eq]
    have h_get_eq2 : (assignRanks cmp ((A ++ B') ++ [b]))[k]'h_k_lt_full
        = (assignRanks cmp (A ++ B') ++ [(b, r_b)])[k]'(by
            rw [List.length_append, h_assign_AB'_len, List.length_singleton]; omega) := by
      congr 1
    rw [h_get_eq2, List.getElem_append_left h_k_lt_assign_AB']
    exact ih

/-- **P3.C-prefix**: rank at position `k` (for `k < q`) in `assignRanks cmp L` equals `k`,
provided consecutive cmps differ throughout the prefix `L.take q` (with `q ≤ L.length`).
Combines `assignRanks_rank_eq_of_prefix` with `assignRanks_rank_eq_pos_when_distinct`
applied to the prefix. -/
theorem assignRanks_rank_eq_pos_when_distinct_prefix {α : Type} (cmp : α → α → Ordering)
    (L : List α) (q : Nat) (hq : q ≤ L.length)
    (h_distinct : ∀ i (h : i + 1 < q),
      cmp (L[i]'(Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt h) hq))
          (L[i+1]'(Nat.lt_of_lt_of_le h hq)) ≠ .eq)
    (k : Nat) (hk : k < q) :
    ((assignRanks cmp L)[k]'(by
        rw [assignRanks_length]; exact Nat.lt_of_lt_of_le hk hq)).2 = k := by
  have h_take_len : (L.take q).length = q := by
    rw [List.length_take]; omega
  have hk_take : k < (L.take q).length := by rw [h_take_len]; exact hk
  -- Distinctness on L.take q follows from distinctness of L's prefix.
  have h_distinct_take : ∀ i (h : i + 1 < (L.take q).length),
      cmp ((L.take q)[i]'(Nat.lt_of_succ_lt h)) ((L.take q)[i+1]'h) ≠ .eq := by
    intro i h
    have h_i_lt_q : i + 1 < q := by rw [h_take_len] at h; exact h
    have h_i_eq : (L.take q)[i]'(Nat.lt_of_succ_lt h)
                = L[i]'(Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt h_i_lt_q) hq) := by
      rw [List.getElem_take]
    have h_i1_eq : (L.take q)[i+1]'h
                 = L[i+1]'(Nat.lt_of_lt_of_le h_i_lt_q hq) := by
      rw [List.getElem_take]
    rw [h_i_eq, h_i1_eq]
    exact h_distinct i h_i_lt_q
  -- Step: use `assignRanks_rank_eq_of_prefix` with A = L.take q, B = L.drop q, then
  -- rewrite via `take_append_drop` to bridge.
  have h_pref := assignRanks_rank_eq_of_prefix cmp (L.take q) (L.drop q) k hk_take
  simp only [List.take_append_drop] at h_pref
  rw [h_pref]
  exact assignRanks_rank_eq_pos_when_distinct cmp (L.take q) h_distinct_take k hk_take

/-! ### Rank equality across `.eq` transitions (TODO)

The dual of `assignRanks_rank_eq_pos_when_distinct`: when `cmp L[i] L[i+1] = .eq`, the
ranks at positions `i` and `i+1` are equal.

**Proof strategy**: use `assignRanks_rank_eq_of_prefix` to reduce to `L.take (i+2)`, then
use `assignRanks_snoc_decompose_strict` on `L.take (i+2) = L.take (i+1) ++ [L[i+1]]`. The
foldl's `lastEntry` after processing `L.take (i+1)` carries the rank at position `i` of
the assignList, with first component `L[i]`. The snoc-decompose's new rank for `L[i+1]`
becomes `if cmp L[i] L[i+1] = .eq then rank_at_i else rank_at_i + 1`, which is `rank_at_i`
by `h_eq`. -/

/-- **Rank equality across `.eq` transition**: if `cmp L[i] L[i+1] = .eq` and
`i+1 < L.length`, then ranks at positions `i` and `i+1` in `assignRanks cmp L` are equal. -/
theorem assignRanks_rank_eq_at_succ_when_cmp_eq {α : Type} (cmp : α → α → Ordering)
    (L : List α) (i : Nat) (hi : i + 1 < L.length)
    (h_eq : cmp (L[i]'(Nat.lt_of_succ_lt hi)) (L[i+1]'hi) = .eq) :
    ((assignRanks cmp L)[i]'(by rw [assignRanks_length]; omega)).2
      = ((assignRanks cmp L)[i+1]'(by rw [assignRanks_length]; exact hi)).2 := by
  -- Step 1: reduce to assignRanks (L.take (i+2)) using prefix lemma.
  have hi_take_len : (L.take (i+2)).length = i + 2 := by
    rw [List.length_take]; omega
  have hi_lt_take : i < (L.take (i+2)).length := by rw [hi_take_len]; omega
  have hi1_lt_take : i + 1 < (L.take (i+2)).length := by rw [hi_take_len]; omega
  have h_pref_i := assignRanks_rank_eq_of_prefix cmp (L.take (i+2)) (L.drop (i+2)) i hi_lt_take
  have h_pref_i1 :=
    assignRanks_rank_eq_of_prefix cmp (L.take (i+2)) (L.drop (i+2)) (i+1) hi1_lt_take
  simp only [List.take_append_drop] at h_pref_i h_pref_i1
  rw [h_pref_i, h_pref_i1]
  -- Step 2: rewrite L.take (i+2) = L.take (i+1) ++ [L[i+1]].
  have h_take_eq : L.take (i+2) = L.take (i+1) ++ [L[i+1]'hi] :=
    (List.take_concat_get' L (i+1) hi).symm
  -- Step 3: extract foldl pair for L.take (i+1).
  have hA_len : (L.take (i+1)).length = i + 1 := by
    rw [List.length_take]; omega
  rcases h_pair : (L.take (i+1)).foldl (assignRanksStep cmp) ([], none) with ⟨rev, lastE⟩
  -- Identify lastE = some (L[i], r_last).
  have h_A_ne : L.take (i+1) ≠ [] := by
    intro h_nil; rw [h_nil] at hA_len; simp at hA_len
  obtain ⟨r_last, h_lastE_some⟩ := assignRanks_foldl_lastEntry_fst cmp (L.take (i+1)) h_A_ne
  rw [h_pair] at h_lastE_some
  simp only at h_lastE_some
  -- (L.take (i+1)).getLast = L[i].
  have hi_lt_A : i < (L.take (i+1)).length := by rw [hA_len]; omega
  have h_getLast_eq : (L.take (i+1)).getLast h_A_ne = L[i]'(Nat.lt_of_succ_lt hi) := by
    rw [List.getLast_eq_getElem]
    have h_eq_idx : (L.take (i+1))[(L.take (i+1)).length - 1]'(by
        have h_pos : 0 < (L.take (i+1)).length := List.length_pos_iff.mpr h_A_ne
        omega) = (L.take (i+1))[i]'hi_lt_A := by
      congr 1; rw [hA_len]; omega
    rw [h_eq_idx, List.getElem_take]
  rw [h_getLast_eq] at h_lastE_some
  -- Step 4: characterize (assignRanks cmp (L.take (i+1)))[i].2 = r_last via foldl invariant.
  have h_assign_A_eq_rev : assignRanks cmp (L.take (i+1)) = rev.reverse := by
    rw [assignRanks_eq_foldl, h_pair]
  have h_assign_A_len : (assignRanks cmp (L.take (i+1))).length = i + 1 := by
    rw [assignRanks_length]; exact hA_len
  have h_rev_len : rev.length = i + 1 := by
    rw [← List.length_reverse, ← h_assign_A_eq_rev, h_assign_A_len]
  have h_rev_ne : rev ≠ [] := by
    intro h_rev_eq; rw [h_rev_eq] at h_rev_len; simp at h_rev_len
  have h_inv := assignRanks_foldl_invariant cmp (L.take (i+1)) [] none List.Pairwise.nil rfl
  rw [h_pair] at h_inv
  simp only at h_inv
  have h_rev_head_eq_lastE : rev.head? = lastE := h_inv.2
  -- rev.head h_rev_ne = (L[i], r_last) via head? equation.
  have h_head?_eq : rev.head? = some (L[i]'(Nat.lt_of_succ_lt hi), r_last) := by
    rw [h_rev_head_eq_lastE, h_lastE_some]
  have h_head_some : rev.head? = some (rev.head h_rev_ne) := List.head?_eq_some_head h_rev_ne
  rw [h_head_some] at h_head?_eq
  have h_rev_head_eq : rev.head h_rev_ne = (L[i]'(Nat.lt_of_succ_lt hi), r_last) :=
    Option.some.inj h_head?_eq
  -- Step 5: snoc decomposition gives the list-level equation.
  have h_decomp :=
    assignRanks_snoc_decompose_strict cmp (L.take (i+1)) (L[i+1]'hi) rev lastE h_pair
  have h_r' : lastE.elim 0 (fun prev =>
        if cmp prev.1 (L[i+1]'hi) == .eq then prev.2 else prev.2 + 1) = r_last := by
    rw [h_lastE_some]
    simp only [Option.elim_some]
    rw [h_eq]
    rfl
  -- The combined list-level equation, expressed in terms of rev.reverse to avoid
  -- a later dependent rewrite of `assignRanks cmp (L.take (i+1))`.
  have h_assignL2_eq : assignRanks cmp (L.take (i+2))
      = rev.reverse ++ [(L[i+1]'hi, r_last)] := by
    rw [h_take_eq, h_decomp, h_r', h_assign_A_eq_rev]
  -- Step 6: factor through a helper to bypass dependent-rewriting issues.
  -- The helper takes a list `M` equal to the concrete (rev.reverse-based) form.
  suffices h_compute : ∀ (M : List (α × Nat))
      (_h_M_eq : M = rev.reverse ++ [(L[i+1]'hi, r_last)])
      (h_b1 : i < M.length) (h_b2 : i + 1 < M.length),
      (M[i]'h_b1).2 = r_last ∧ (M[i+1]'h_b2).2 = r_last by
    obtain ⟨hl, hr⟩ := h_compute (assignRanks cmp (L.take (i+2))) h_assignL2_eq _ _
    rw [hl, hr]
  intros M h_M_eq h_b1 h_b2
  subst h_M_eq
  -- M = rev.reverse ++ [(L[i+1], r_last)]
  have h_rev_rev_len : rev.reverse.length = i + 1 := by
    rw [List.length_reverse]; exact h_rev_len
  have h_i_lt_rev_rev : i < rev.reverse.length := by rw [h_rev_rev_len]; omega
  have h_rev_rev_le : rev.reverse.length ≤ i + 1 := by rw [h_rev_rev_len]
  -- Convert h_rev_head_eq to use rev[0] form.
  rw [List.head_eq_getElem_zero h_rev_ne] at h_rev_head_eq
  -- h_rev_head_eq : rev[0]'_ = (L[i], r_last)
  refine ⟨?_, ?_⟩
  · -- (rev.reverse ++ [(L[i+1], r_last)])[i].2 = r_last
    rw [List.getElem_append_left h_i_lt_rev_rev, List.getElem_reverse]
    -- Goal: (rev[rev.length - 1 - i]).2 = r_last, where rev.length - 1 - i = 0.
    have h_idx_zero : rev.length - 1 - i = 0 := by rw [h_rev_len]; omega
    have h_rev0_lt : 0 < rev.length := by rw [h_rev_len]; omega
    have h_idx_lt : rev.length - 1 - i < rev.length := by rw [h_idx_zero]; exact h_rev0_lt
    have h_idx_get : rev[rev.length - 1 - i]'h_idx_lt = rev[0]'h_rev0_lt := by
      congr 1
    rw [h_idx_get, h_rev_head_eq]
  · -- (rev.reverse ++ [(L[i+1], r_last)])[i+1].2 = r_last
    rw [List.getElem_append_right h_rev_rev_le]
    simp [h_rev_rev_len]

/-! ### Rank equality within an `.eq`-class

Given a total preorder `cmp` and a sorted list (Pairwise `≠ .gt`), if two positions
`i ≤ j` satisfy `cmp L[i] L[j] = .eq`, then by sortedness + transitivity each
consecutive `cmp L[k] L[k+1]` for `k ∈ [i, j-1]` must also be `.eq`. Chain
`assignRanks_rank_eq_at_succ_when_cmp_eq` to conclude equal ranks. -/

/-- **Rank equality within an `.eq`-class**: for a sorted list `L` under a total
preorder `cmp`, if `cmp L[i] L[j] = .eq` and `i ≤ j`, the assigned ranks agree. -/
theorem assignRanks_rank_eq_within_eq_class {α : Type} (cmp : α → α → Ordering)
    (h_refl : ∀ a, cmp a a = Ordering.eq)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (L : List α)
    (h_sorted : L.Pairwise (fun a b => cmp a b ≠ Ordering.gt))
    (i j : Nat) (hij : i ≤ j) (hj : j < L.length)
    (h_eq : cmp (L[i]'(Nat.lt_of_le_of_lt hij hj)) (L[j]'hj) = Ordering.eq) :
    ((assignRanks cmp L)[i]'(by rw [assignRanks_length]; omega)).2
      = ((assignRanks cmp L)[j]'(by rw [assignRanks_length]; exact hj)).2 := by
  -- Helper: `.eq` is symmetric.
  have h_eq_symm : ∀ a b, cmp a b = Ordering.eq → cmp b a = Ordering.eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      have := h_antisym₁ b a h_ba
      rw [hab] at this; cases this
    | .gt =>
      have := h_antisym₂ b a h_ba
      rw [hab] at this; cases this
  -- Helper: `cmp a b ≠ .gt → cmp b c = .lt → cmp a c = .lt`.
  have h_le_lt : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c = Ordering.lt →
      cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hbc' : cmp b c ≠ Ordering.gt := by rw [hbc]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab hbc'
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca_le : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      have h_cb_le : cmp c b ≠ Ordering.gt := h_trans c a b h_ca_le hab
      have h_cb_gt : cmp c b = Ordering.gt := h_antisym₁ b c hbc
      exact h_cb_le h_cb_gt
  -- Helper: `cmp a b = .lt → cmp b c ≠ .gt → cmp a c = .lt`.
  have h_lt_le : ∀ a b c, cmp a b = Ordering.lt → cmp b c ≠ Ordering.gt →
      cmp a c = Ordering.lt := by
    intros a b c hab hbc
    have hab' : cmp a b ≠ Ordering.gt := by rw [hab]; intro h; cases h
    have h_ac_le : cmp a c ≠ Ordering.gt := h_trans a b c hab' hbc
    match h_ac : cmp a c with
    | .lt => rfl
    | .gt => exact (h_ac_le h_ac).elim
    | .eq =>
      exfalso
      have h_ca : cmp c a = Ordering.eq := h_eq_symm _ _ h_ac
      have h_ca_le : cmp c a ≠ Ordering.gt := by rw [h_ca]; intro h; cases h
      have h_ba_gt : cmp b a = Ordering.gt := h_antisym₁ a b hab
      have h_ba_le : cmp b a ≠ Ordering.gt := h_trans b c a hbc h_ca_le
      exact h_ba_le h_ba_gt
  -- Pairwise-iff-getElem: any two indexed elements with `i' < j'` satisfy `cmp ≠ .gt`.
  have h_pw := List.pairwise_iff_getElem.mp h_sorted
  -- Sortedness gives `cmp L[i'] L[j'] ≠ .gt` for all `i' ≤ j'`.
  have h_sorted_le : ∀ (i' j' : Nat) (hi' : i' < L.length) (hj' : j' < L.length),
      i' ≤ j' → cmp (L[i']'hi') (L[j']'hj') ≠ Ordering.gt := by
    intros i' j' hi' hj' hij'
    rcases Nat.lt_or_eq_of_le hij' with h_lt | h_eq_idx
    · exact h_pw i' j' hi' hj' h_lt
    · subst h_eq_idx
      rw [h_refl]; intro h; cases h
  -- Show all consecutive cmps in [i, j-1] are `.eq`.
  have h_chain : ∀ (k : Nat) (hk : i ≤ k) (hk_succ : k + 1 ≤ j),
      cmp (L[k]'(by have := hj; omega)) (L[k+1]'(by have := hj; omega)) = Ordering.eq := by
    intros k hk hk_succ
    have hk_lt : k < L.length := by omega
    have hk1_lt : k + 1 < L.length := by omega
    have hi_lt : i < L.length := Nat.lt_of_le_of_lt hij hj
    have h_kk1_le : cmp (L[k]'hk_lt) (L[k+1]'hk1_lt) ≠ Ordering.gt :=
      h_pw k (k+1) hk_lt hk1_lt (Nat.lt_succ_self k)
    match h_cmp : cmp (L[k]'hk_lt) (L[k+1]'hk1_lt) with
    | .eq => rfl
    | .gt => exact (h_kk1_le h_cmp).elim
    | .lt =>
      exfalso
      -- cmp L[i] L[k] ≤ + cmp L[k] L[k+1] = lt → cmp L[i] L[k+1] = lt.
      have h_ik_le := h_sorted_le i k hi_lt hk_lt hk
      have h_ik1_lt : cmp (L[i]'hi_lt) (L[k+1]'hk1_lt) = Ordering.lt :=
        h_le_lt _ _ _ h_ik_le h_cmp
      -- cmp L[i] L[k+1] = lt + cmp L[k+1] L[j] ≤ → cmp L[i] L[j] = lt.
      have h_k1j_le := h_sorted_le (k+1) j hk1_lt hj hk_succ
      have h_ij_lt : cmp (L[i]'hi_lt) (L[j]'hj) = Ordering.lt :=
        h_lt_le _ _ _ h_ik1_lt h_k1j_le
      rw [h_ij_lt] at h_eq; cases h_eq
  -- Chain `assignRanks_rank_eq_at_succ_when_cmp_eq` via a generic statement that
  -- pre-computes the bound proof from the `i + m ≤ j` hypothesis.
  have h_step : ∀ (m : Nat) (hm : i + m ≤ j),
      ∀ (h_b : i + m < (assignRanks cmp L).length),
      ((assignRanks cmp L)[i]'(by rw [assignRanks_length]; omega)).2
        = ((assignRanks cmp L)[i+m]'h_b).2 := by
    intro m
    induction m with
    | zero => intros _ _; rfl
    | succ m ih =>
      intro h_m_le h_b_succ
      have h_m_le' : i + m ≤ j := Nat.le_of_succ_le h_m_le
      have h_im1_lt : i + m + 1 < L.length := by
        rw [assignRanks_length] at h_b_succ; exact h_b_succ
      have h_im_lt : i + m < L.length := Nat.lt_of_succ_lt h_im1_lt
      have h_b_m : i + m < (assignRanks cmp L).length := by
        rw [assignRanks_length]; exact h_im_lt
      have h_im_le_k : i ≤ i + m := Nat.le_add_right i m
      have h_cmp_eq :
          cmp (L[i+m]'h_im_lt) (L[(i+m)+1]'h_im1_lt) = Ordering.eq :=
        h_chain (i+m) h_im_le_k h_m_le
      have h_succ_step :
          ((assignRanks cmp L)[i+m]'h_b_m).2
            = ((assignRanks cmp L)[i+m+1]'(by
                rw [assignRanks_length]; exact h_im1_lt)).2 :=
        assignRanks_rank_eq_at_succ_when_cmp_eq cmp L (i+m) h_im1_lt h_cmp_eq
      rw [ih h_m_le' h_b_m, h_succ_step]
      rfl
  -- Extract the result at `m = j - i`, then convert `i + (j - i) = j`.
  have h_b_at_jmi : i + (j - i) < (assignRanks cmp L).length := by
    rw [assignRanks_length]; omega
  have h_at_j_minus_i := h_step (j - i) (by omega) h_b_at_jmi
  -- Convert via proof-irrelevant index equation.
  suffices h_get_eq : ∀ (k : Nat) (_h_k_eq : k = j) (h_b : k < (assignRanks cmp L).length),
      ((assignRanks cmp L)[k]'h_b).2
        = ((assignRanks cmp L)[j]'(by rw [assignRanks_length]; exact hj)).2 by
    rw [h_at_j_minus_i]
    exact h_get_eq (i + (j - i)) (by omega) _
  intros k h_k_eq h_b
  subst h_k_eq
  rfl

end Graph
