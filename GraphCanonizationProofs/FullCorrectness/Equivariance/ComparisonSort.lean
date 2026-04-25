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
private theorem sortBy_pairwise {α : Type} (cmp : α → α → Ordering)
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
private theorem foldl_pointwise_eq {α β : Type} (f : β → α → β) (L L' : List α) (init : β)
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

end Graph
