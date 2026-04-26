import FullCorrectness.Equivariance.StageDRelational
import FullCorrectness.Equivariance.BreakTieRelational
import FullCorrectness.Invariants
import FullCorrectness.Tiebreak

/-!
# Phase 5 — `runFrom_VtsInvariant_eq` via joint induction
  (`FullCorrectness.Equivariance.RunFromRelational`)

The single load-bearing reduction needed by §6 (and also by §8's `(⟹)` direction).

## Diagnostic: the existing statement is too strong

The current statement (in `Tiebreak.lean`) is:

```
τ ∈ Aut G → arr₁, arr₂ τ-related → runFrom s arr₁ G = runFrom s arr₂ G
```

**This is not true unconditionally**. Concrete counterexample:
  - G = path 0–1–2 (edges 0-1, 1-2).
  - τ = swap(0, 2) ∈ Aut G.
  - rks₁ = [0, 5, 5], rks₂ = [5, 5, 0] (τ-related: rks₂[w] = rks₁[τ⁻¹ w] for all w).
  - labelEdges rks₁ G = path 0–1–2.
  - labelEdges rks₂ G = the graph with edges {0–2, 1–2}.

The canonical matrices differ. So `runFrom n rks_i G` (i.e., the `s = n` case where the
foldl is empty) gives unequal outputs.

## Root cause: tie-breaking by vertex-index isn't τ-equivariant

`computeDenseRanks` sorts pairs `(rank, vertex-index)` lex. When two vertices have the
same rank, the secondary `vertex-index` key breaks the tie. Under τ-relabeling:
  - In rks₁ = [0, 5, 5], the tied vertices are {1, 2} (in original index order).
  - In rks₂ = [5, 5, 0], the tied vertices are {0, 1} (in original index order).
  - These tie classes are NOT τ-images of each other in the *index-order* sense, even
    though their rank-pairs are.

The vertex-index secondary key is a function of the labeling, not the graph structure,
so it's not τ-equivariant. Tie-freeness (every vertex gets a unique rank) collapses the
secondary key — then there are no ties to break, and labelEdges produces the same
canonical form for τ-related rks.

## No bug in the original algorithm

The algorithm is correct. The flow is:

  1. `run zeros G = labelEdges (orderVertices (initializePaths G) zeros) G`.
  2. `orderVertices` runs `n` iterations of `convergeLoop + breakTie`.
  3. `orderVertices_n_distinct_ranks` (proved in `Invariants.lean`) shows the output
     ranks are all-distinct (tie-free) when starting from a prefix typing like `zeros`.
  4. `labelEdges` is then called on tie-free input — exactly the case where it's
     τ-equivariant.

So the algorithm is fine; only the *lemma statement* `runFrom_VtsInvariant_eq` is too
broad. It needs an additional hypothesis that the algorithmic context always provides.

## Tie-freeness is the right hypothesis

Not sortedness — distinct-valuedness. After breakTieAt + further iterations, the ranks
become distinct, and labelEdges' canonical form depends only on the rank order (not on
vertex-index tie-breaking).

## Plan for Phase 5

### Step 1: Strengthen `runFrom_VtsInvariant_eq`'s signature

Add a hypothesis stating the input `arr` plus the remaining `runFrom` iterations
together produce tie-free output. The cleanest formulation uses the existing
`IsPrefixTyping` predicate from `Invariants.lean`:

```lean
theorem runFrom_VtsInvariant_eq
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ G.Aut)
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    -- NEW HYPOTHESIS: arr is a prefix typing (so that runFrom's iterations produce tie-free output).
    (h_prefix : IsPrefixTyping arr₁)
    : runFrom s arr₁ G = runFrom s arr₂ G
```

(The prefix property of `arr₂` follows from `arr₁`'s + the τ-relation: τ is a
bijection on `Fin n`, so `arr₂`'s value set equals `arr₁`'s.)

### Step 2: Prove a runFrom-tie-freeness lemma

Adapt `orderVertices_n_distinct_ranks` to runFrom's "skip first `s` outer iterations"
form. Specifically:

```
runFrom_foldl_distinct_ranks:
  IsPrefixTyping arr → ∀ s, the foldl orderedRanks output is tie-free.
```

For `s = 0` this is exactly `orderVertices_n_distinct_ranks`. For `s > 0`, we'd need a
stronger argument: the input arr already satisfies prefix-uniqueness up to `s`, so the
remaining iterations only need to break ties at values `≥ s`.

In practice, `tiebreak_choice_independent` only calls `runFrom (s + 1)` with arr =
`breakTieAt vts t₀ v_i` after `vts` has been canonicalized up through targetPosition
`s`. So the input always satisfies the prefix invariant up to `s`.

### Step 3: Joint induction

Prove `P₁(m) := runFrom_VtsInvariant_eq` and `P₂(m) := tiebreak_choice_independent`
together by induction on `m = n - s`:

  - **Base (m = 0):** runFrom n arr G = labelEdges arr G.
    Apply Phase 3 (`labelEdges_VtsInvariant_eq_distinct`) using tie-freeness from Step 2
    + the τ-relatedness hypothesis.

  - **Step (m = k+1):** Unfold one foldl iteration: convergeLoop + breakTie at start.
    1. Convergence step: by Phase 2 (`convergeLoop_VtsInvariant_eq`), τ-relatedness preserved.
    2. breakTie step: choices may diverge. Bridge:
       - keep₁ ∈ typeClass(converged₁, start), keep₂ ∈ typeClass(converged₂, start).
       - τ⁻¹ keep₂ ∈ typeClass(converged₁, start) (same orbit).
       - By IH P₂(k), runFrom (s+1) (breakTieAt converged₁ start keep₁) G
                     = runFrom (s+1) (breakTieAt converged₁ start (τ⁻¹ keep₂)) G.
       - By Phase 4 (`breakTieAt_τ_related`), breakTieAt converged₂ start keep₂ is
         τ-related to breakTieAt converged₁ start (τ⁻¹ keep₂).
       - By IH P₁(k), runFrom (s+1) on these gives equal results.
       - Compose to get the original goal.

### Step 4: Update call sites

  - `tiebreak_choice_independent`: add the IsPrefixTyping hypothesis (or derive it
    internally — its caller, `orderVertices_prefix_invariant`'s induction step, has the
    invariant).
  - `Main.run_isomorphic_eq_new`: thread `IsPrefixTyping.replicate_zero` through.

### Step 5: Phase 3 dependency

Phase 3 (`labelEdges_VtsInvariant_eq_distinct`) currently has a sorry on the cell-wise
characterization of `labelEdgesAccordingToRankings`. Phase 5's base case depends on
this being closed. The plan for Phase 3 is documented in
`Equivariance/StageDRelational.lean` — it requires showing that for tie-free rks,
`labelEdgesAccordingToRankings rks G = G.permute (rankPerm rks)`, which in turn
requires a structural induction on the `swapVertexLabels` fold.

## Estimate

  - Strengthen `runFrom_VtsInvariant_eq` signature + propagate to call sites: ~50 lines.
  - `runFrom_foldl_distinct_ranks` lemma: ~150 lines.
  - Joint induction (P₁ + P₂): ~250 lines.
  - Phase 3 closure (cell-wise characterization): ~300 lines.

**Total: ~750 lines of new Lean code.**

## Risks / open questions

  1. The `IsPrefixTyping arr` hypothesis may be too strong for `tiebreak_choice_independent`'s
     own caller. We may need a weaker form (e.g., "values 0..s-1 are uniquely held").
     The existing `orderVertices_prefix_invariant_strong` in `Invariants.lean` provides
     a more nuanced invariant; aligning with it may be cleaner.

  2. The base case `m = 0` requires Phase 3's deep characterization. Phase 3's sorry
     is the only blocker.

  3. The joint induction's IH form needs care. The IH for `P₂` at level k uses arr =
     converged₁'s `breakTieAt`, not the original arr — so the prefix-typing hypothesis
     on converged₁'s breakTieAt must follow from converged₁ being a (post-convergeLoop)
     prefix typing, which Invariants.lean's `convergeLoop_preserves_prefix` provides.

## Status

This file documents the approach. The next concrete steps:

  (a) Modify `Tiebreak.lean::runFrom_VtsInvariant_eq` signature to add `IsPrefixTyping`.
  (b) Modify `Tiebreak.lean::tiebreak_choice_independent` similarly.
  (c) Adapt `Main.lean::run_isomorphic_eq_new` to thread the hypothesis.
  (d) Implement `runFrom_foldl_distinct_ranks` + the joint induction.
  (e) Close Phase 3 (separate work).

The signature change in (a) breaks no external callers since the lemma is a sorry; the
internal callers (`tiebreak_choice_independent`) are within the same file and easily
updated.
-/

namespace Graph

variable {n : Nat}

/-! ### Foldl-step helper (already established): one convergeLoop preserves τ-relatedness -/

/-- One `convergeLoop` step on τ-related typings preserves τ-relatedness. Direct
restatement of `convergeLoop_VtsInvariant_eq` for use within the foldl induction.

Note: this applies to every iteration of `runFrom`'s outer foldl, regardless of
tie-freeness assumptions. It's the "easy" half of the inductive step. -/
theorem convergeLoop_step_τ_preserved
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ AdjMatrix.Aut G)
    (vts₁ vts₂ : Array VertexType)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0) :
    let converged₁ := convergeLoop (initializePaths G) vts₁ n
    let converged₂ := convergeLoop (initializePaths G) vts₂ n
    converged₁.size = n ∧ converged₂.size = n ∧
    (∀ w : Fin n, converged₂.getD w.val 0 = converged₁.getD (τ⁻¹ w).val 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [convergeLoop_size_preserving]; exact h_size₁
  · rw [convergeLoop_size_preserving]; exact h_size₂
  · exact convergeLoop_VtsInvariant_eq G τ hτ vts₁ vts₂ n h_size₁ h_size₂ h_rel

/-! ### Strengthened theorem statement

The existing `runFrom_VtsInvariant_eq` in `Tiebreak.lean` is too strongly stated.
We introduce a properly-hypothesized version here as a separate theorem, with
`IsPrefixTyping` added. The original sorry in `Tiebreak.lean` remains pending the
signature surgery; this strengthened version is the lemma that downstream callers
should use. -/

/-- The prefix-typing property transfers from arr₁ to arr₂ across τ-relatedness. -/
theorem IsPrefixTyping_τ_transfer
    (τ : Equiv.Perm (Fin n))
    (arr₁ arr₂ : Array VertexType)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (h_prefix₁ : @IsPrefixTyping n arr₁) :
    @IsPrefixTyping n arr₂ := by
  obtain ⟨m, h_lt, h_witness⟩ := h_prefix₁
  refine ⟨m, ?_, ?_⟩
  · intro v
    rw [h_rel v]
    exact h_lt (τ⁻¹ v)
  · intro k hk
    obtain ⟨v, hv⟩ := h_witness k hk
    refine ⟨τ v, ?_⟩
    rw [h_rel (τ v)]
    have h_inv : τ⁻¹ (τ v) = v := by simp
    rw [h_inv]
    exact hv

/-- The lower-uniqueness property transfers from arr₁ to arr₂ across τ-relatedness. -/
theorem UniquelyHeldBelow_τ_transfer
    (τ : Equiv.Perm (Fin n))
    (arr₁ arr₂ : Array VertexType)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (q : Nat)
    (h_unique₁ : @UniquelyHeldBelow n arr₁ q) :
    @UniquelyHeldBelow n arr₂ q := by
  intro k
  obtain ⟨v, hv_eq, hv_unique⟩ := h_unique₁ k
  refine ⟨τ v, ?_, ?_⟩
  · -- arr₂[(τ v).val] = arr₁[(τ⁻¹ (τ v)).val] = arr₁[v.val] = k.val.
    show arr₂.getD (τ v).val 0 = k.val
    rw [h_rel (τ v)]
    have h_inv : τ⁻¹ (τ v) = v := by simp
    rw [h_inv]
    exact hv_eq
  · -- Uniqueness: any w with arr₂[w] = k.val must equal τ v.
    intro w hw
    -- arr₂[w.val] = arr₁[(τ⁻¹ w).val] = k.val. By uniqueness of v in arr₁: τ⁻¹ w = v.
    rw [h_rel w] at hw
    have h_τinv_w_eq : τ⁻¹ w = v := hv_unique (τ⁻¹ w) hw
    -- So w = τ v.
    have : τ (τ⁻¹ w) = τ v := by rw [h_τinv_w_eq]
    simpa using this

/-! ### Helpers: runFrom unfolding and tie-freeness from invariants -/

/-- `runFrom n arr G = labelEdgesAccordingToRankings arr G`. The empty foldl reduces
to the identity on the typing array, then labelEdges runs on it. -/
private theorem runFrom_at_n (G : AdjMatrix n) (arr : Array VertexType) :
    runFrom n arr G = labelEdgesAccordingToRankings arr G := by
  unfold runFrom
  simp [List.range_zero]

/-- `runFrom s arr G = runFrom (s+1) (after-one-step arr) G`, where one step is
`convergeLoop`-then-`breakTie` at target `s`. The outer foldl in `runFrom s` decomposes
into the first iteration (target `s + 0 = s`) followed by the remaining iterations
(targets `s+1, …, n-1`), which is exactly `runFrom (s+1)`. -/
private theorem runFrom_succ (G : AdjMatrix n) (arr : Array VertexType) (s : Nat) (hs : s < n) :
    runFrom s arr G
      = runFrom (s + 1) ((breakTie (convergeLoop (initializePaths G) arr n) s).1) G := by
  -- Define the body at each base target.
  let body (t : Nat) := fun (currentTypes : Array VertexType) (targetPosition : Nat) =>
    (breakTie (convergeLoop (initializePaths G) currentTypes n) (t + targetPosition)).1
  -- The orderedRanks computed by runFrom s arr G is (List.range (n-s)).foldl (body s) arr.
  show labelEdgesAccordingToRankings ((List.range (n - s)).foldl (body s) arr) G
       = labelEdgesAccordingToRankings
            ((List.range (n - (s + 1))).foldl (body (s + 1))
              ((breakTie (convergeLoop (initializePaths G) arr n) s).1)) G
  -- Reduce to: orderedRanks are equal.
  congr 1
  -- Peel the first iteration of LHS via List.range_add.
  have h_diff : n - s = 1 + (n - (s + 1)) := by omega
  rw [h_diff, List.range_add]
  rw [List.foldl_append]
  -- Inner foldl (List.range 1 = [0]) reduces to one step.
  have h_step : (List.range 1).foldl (body s) arr
        = (breakTie (convergeLoop (initializePaths G) arr n) s).1 := by
    show ((List.range 1).foldl (body s) arr) = _
    rw [show List.range 1 = [0] from by decide]
    show body s arr 0 = _
    show (breakTie (convergeLoop (initializePaths G) arr n) (s + 0)).1 = _
    rw [Nat.add_zero]
  rw [h_step]
  -- LHS now: ((List.range (n-(s+1))).map (1 + ·)).foldl (body s) (arr_step).
  -- RHS:    (List.range (n-(s+1))).foldl (body (s+1)) (arr_step).
  -- The map shifts targets by +1.
  rw [List.foldl_map]
  -- Bodies match: body s curr (1 + tp) = body (s+1) curr tp (since s + (1+tp) = (s+1) + tp).
  congr 1
  funext currentTypes targetPosition
  show body s currentTypes (1 + targetPosition) = body (s + 1) currentTypes targetPosition
  show (breakTie (convergeLoop (initializePaths G) currentTypes n) (s + (1 + targetPosition))).1
       = (breakTie (convergeLoop (initializePaths G) currentTypes n) (s + 1 + targetPosition)).1
  rw [show s + (1 + targetPosition) = s + 1 + targetPosition from by omega]

/-- `UniquelyHeldBelow arr n` (with `arr.size = n`) implies `TieFree arr n`. By the
uniqueness of each value in {0..n-1}, equal values force equal vertices. The
`IsPrefixTyping` hypothesis isn't strictly needed for this implication. -/
private theorem UniquelyHeldBelow_n_implies_TieFree
    (arr : Array VertexType) (_h_size : arr.size = n)
    (h_unique : @UniquelyHeldBelow n arr n) :
    TieFree arr n := by
  intro i j h_eq
  -- arr[i.val] = arr[j.val] = k, with k < n (we'll get this from h_unique).
  -- For i, j ∈ Fin n, take k_i := ⟨arr[i.val], _⟩. By h_unique, the witness for k_i is unique.
  -- Both i and j are witnesses (their arr values equal); so i = j.
  -- We need arr[i.val] < n. This is provided by the uniqueness hypothesis: for any k ∈ Fin n,
  -- the unique witness has arr[witness] = k.val. Conversely, every value held by some
  -- v ∈ Fin n must be in {0..n-1} via the bijective correspondence.
  -- Direct argument: n values in {0..n-1} are uniquely held, and arr.size = n, so ALL values
  -- in arr are in {0..n-1}. (Pigeonhole: n distinct values within {0..n-1}, n vertices.)
  -- For brevity, we show TieFree directly using uniqueness on Fin n indexed values.
  by_contra h_ne
  -- i ≠ j with arr[i.val] = arr[j.val] = some value k.
  -- Strategy: derive contradiction by finding a value k < n where two distinct vertices both witness it.
  -- We use h_unique on k = ⟨_, h_lt⟩ where h_lt is established by exhaustion via finite Fintype.
  -- A cleaner route: extract the bijection directly.
  -- Use Finite.injective_iff_surjective on f : Fin n → Fin n (defined when arr values < n).
  -- For now, derive via uniqueness + value bounds.
  have h_arr_val_lt_n : ∀ v : Fin n, arr.getD v.val 0 < n := by
    -- For each v, the value k := arr[v.val]. We claim k < n.
    -- If k ≥ n: by h_unique on k' = arr[v.val] ... but h_unique only applies for k' : Fin n.
    -- We need a separate argument using the bijection. Since n values 0..n-1 are uniquely held,
    -- and there are exactly n vertices, the n witnesses for k ∈ Fin n cover Fin n. So every
    -- vertex IS a witness for some k < n, hence its value is < n.
    intro v
    -- The map (k : Fin n) ↦ (h_unique k).choose : Fin n → Fin n is injective (different ks give
    -- different vs by uniqueness clause). For finite sets, injective ⟹ surjective. So v is in
    -- the image, i.e., ∃ k, (h_unique k).choose = v. Then arr[v.val] = k.val < n.
    let f : Fin n → Fin n := fun k => (h_unique k).choose
    have h_f_inj : Function.Injective f := by
      intro k₁ k₂ h_f_eq
      have h₁ : arr.getD (f k₁).val 0 = k₁.val := (h_unique k₁).choose_spec.1
      have h₂ : arr.getD (f k₂).val 0 = k₂.val := (h_unique k₂).choose_spec.1
      rw [h_f_eq] at h₁
      apply Fin.ext
      rw [← h₁, h₂]
    have h_f_surj : Function.Surjective f := Finite.injective_iff_surjective.mp h_f_inj
    obtain ⟨k, h_k_eq⟩ := h_f_surj v
    have h_arr_eq_k : arr.getD v.val 0 = k.val := h_k_eq ▸ (h_unique k).choose_spec.1
    rw [h_arr_eq_k]
    exact k.isLt
  -- arr[i.val] < n. So arr[i.val] = k.val for some k : Fin n.
  set k_val := arr.getD i.val 0 with h_k_def
  have h_k_lt : k_val < n := h_arr_val_lt_n i
  let k_fin : Fin n := ⟨k_val, h_k_lt⟩
  -- Both i and j are witnesses for k_fin in h_unique.
  obtain ⟨v_k, hv_k_eq, hv_k_unique⟩ := h_unique k_fin
  have h_i_witness : arr.getD i.val 0 = k_fin.val := rfl
  have h_j_witness : arr.getD j.val 0 = k_fin.val := h_eq.symm ▸ h_i_witness
  have h_i_eq_v : i = v_k := hv_k_unique i h_i_witness
  have h_j_eq_v : j = v_k := hv_k_unique j h_j_witness
  exact h_ne (h_i_eq_v.trans h_j_eq_v.symm)

/-! ### `breakTieCount` is τ-invariant -/

/-- For τ-related arrays of size `n`, the count of any target value is the same.
The multiset of values is preserved by τ-relabeling (τ is a bijection on Fin n). -/
private theorem breakTieCount_τ_invariant
    (τ : Equiv.Perm (Fin n))
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (t : VertexType) :
    breakTieCount arr₁ t = breakTieCount arr₂ t := by
  -- Reduce both counts to Finset.card via Array.foldl_eq_foldl_finRange_get.
  -- Strategy: translate breakTieCount to a Finset.card and use τ-bijection on Fin n.
  -- breakTieCount arr t = (Finset.univ.filter (fun w : Fin n => arr.getD w.val 0 = t)).card.
  -- For τ-related arr₁, arr₂: the filter sets are images of each other under τ.
  -- Hence equal cardinality.
  have h_count_eq_card : ∀ (arr : Array VertexType), arr.size = n →
      breakTieCount arr t
        = (Finset.univ.filter (fun w : Fin n => arr.getD w.val 0 = t)).card := by
    -- Standard Array.foldl-to-Finset.card translation. Leave as a separate utility lemma
    -- (a few intermediate steps: Array.foldl_toList → countP-style induction → Finset.card via
    -- Fin n bijection).
    sorry
  rw [h_count_eq_card arr₁ h_size₁, h_count_eq_card arr₂ h_size₂]
  -- Bijection: w ↦ τ w maps arr₁-filter to arr₂-filter.
  apply Finset.card_bij (fun (w : Fin n) (_ : w ∈ Finset.univ.filter
        (fun w : Fin n => arr₁.getD w.val 0 = t)) => τ w)
  · -- Membership: arr₁[w] = t → arr₂[τ w] = t.
    intro w h_w_in
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_w_in ⊢
    rw [h_rel (τ w)]
    have h_inv_eq : τ⁻¹ (τ w) = w := by simp
    rw [h_inv_eq]
    exact h_w_in
  · -- Injective: τ w₁ = τ w₂ → w₁ = w₂.
    intro w₁ _ w₂ _ h_eq
    exact τ.injective h_eq
  · -- Surjective: for u in arr₂-filter, take w := τ⁻¹ u.
    intro u h_u_in
    refine ⟨τ⁻¹ u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_u_in ⊢
      have h_τ_inv_apply : τ (τ⁻¹ u) = u := by simp
      rw [h_rel u] at h_u_in
      exact h_u_in
    · simp

/-! ### Strengthened theorem proof

**Strengthened** `runFrom_VtsInvariant_eq`: τ-related typings with prefix typing
+ lower-uniqueness produce equal canonical matrices. The `IsPrefixTyping arr₁` +
`UniquelyHeldBelow arr₁ s` hypotheses precisely capture the algorithmic state after `s`
outer iterations: values 0..s-1 are uniquely held. Then the remaining `n - s` foldl
iterations extend uniqueness to all of `{0..n-1}`, producing tie-free output where
Phase 3.E (`labelEdges_VtsInvariant_eq_distinct`) applies. -/

theorem runFrom_VtsInvariant_eq_strong
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ AdjMatrix.Aut G)
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (h_prefix : @IsPrefixTyping n arr₁)
    (h_unique : @UniquelyHeldBelow n arr₁ s)
    (hs : s ≤ n) :
    runFrom s arr₁ G = runFrom s arr₂ G := by
  -- Induct on m := n - s.
  -- Induct on m := n - s. Generalize over s, arr₁, arr₂ so the IH at m-1 applies at any s'.
  suffices h : ∀ (m s : Nat) (arr₁ arr₂ : Array VertexType),
      n - s = m →
      arr₁.size = n → arr₂.size = n →
      (∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0) →
      @IsPrefixTyping n arr₁ →
      @UniquelyHeldBelow n arr₁ s →
      s ≤ n →
      runFrom s arr₁ G = runFrom s arr₂ G by
    exact h (n - s) s arr₁ arr₂ rfl h_size₁ h_size₂ h_rel h_prefix h_unique hs
  clear h_size₁ h_size₂ h_rel h_prefix h_unique hs arr₁ arr₂ s
  intro m
  induction m with
  | zero =>
    intro s arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    -- Base: n - s = 0 ⟹ s = n.
    have hsn : s = n := by omega
    -- Don't subst; just upgrade UniquelyHeldBelow at s to UniquelyHeldBelow at n.
    have h_unique_n : @UniquelyHeldBelow n arr₁ n := hsn ▸ h_unique
    -- arr₁ tie-free.
    have h_tf₁ : TieFree arr₁ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₁ h_size₁ h_unique_n
    -- arr₂ via τ-transfer.
    have h_unique₂ : @UniquelyHeldBelow n arr₂ n :=
      UniquelyHeldBelow_τ_transfer τ arr₁ arr₂ h_rel n h_unique_n
    have h_tf₂ : TieFree arr₂ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₂ h_size₂ h_unique₂
    -- runFrom n arr_i G = labelEdges arr_i G; apply Phase 3.E.
    rw [hsn, runFrom_at_n, runFrom_at_n]
    -- Phase 3.E: produces equality of labelEdges results.
    exact (labelEdges_VtsInvariant_eq_distinct G τ hτ arr₁ arr₂ h_size₁ h_size₂ h_tf₁ h_tf₂ h_rel).symm
  | succ m ih =>
    intro s arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    -- s < n.
    have hs_lt : s < n := by omega
    -- Step 1: Unfold one iteration on both sides.
    rw [runFrom_succ G arr₁ s hs_lt, runFrom_succ G arr₂ s hs_lt]
    -- Step 2: Compute conv_i and arr_i' on both sides.
    set conv₁ := convergeLoop (initializePaths G) arr₁ n with h_conv₁_def
    set conv₂ := convergeLoop (initializePaths G) arr₂ n with h_conv₂_def
    set arr₁' := (breakTie conv₁ s).1 with h_arr₁'_def
    set arr₂' := (breakTie conv₂ s).1 with h_arr₂'_def
    -- Step 3: τ-relatedness of conv_i (Phase 2).
    have ⟨h_conv₁_size, h_conv₂_size, h_conv_rel⟩ :=
      convergeLoop_step_τ_preserved G τ hτ arr₁ arr₂ h_size₁ h_size₂ h_rel
    -- Step 4: Hypothesis preservation through convergeLoop.
    have h_conv₁_prefix : @IsPrefixTyping n conv₁ :=
      convergeLoop_preserves_prefix G arr₁ n h_size₁ h_prefix
    have h_conv₁_both : @IsPrefixTyping n conv₁ ∧ @UniquelyHeldBelow n conv₁ s :=
      convergeLoop_preserves_lower_uniqueness G arr₁ s (Nat.le_of_lt hs_lt) n h_size₁ h_prefix h_unique
    have h_conv₁_unique : @UniquelyHeldBelow n conv₁ s := h_conv₁_both.2
    -- Step 5: Hypothesis preservation through breakTie.
    have ⟨h_arr₁'_prefix, h_arr₁'_unique⟩ :=
      breakTie_step_preserves_uniqueness conv₁ s hs_lt h_conv₁_size h_conv₁_prefix h_conv₁_unique
    have h_arr₁'_size : arr₁'.size = n := by
      rw [h_arr₁'_def, breakTie_size]; exact h_conv₁_size
    have h_arr₂'_size : arr₂'.size = n := by
      rw [h_arr₂'_def, breakTie_size]; exact h_conv₂_size
    -- Step 6: hs+1 ≤ n.
    have hs1 : s + 1 ≤ n := hs_lt
    -- Step 7: m = n - (s+1).
    have h_m_def' : n - (s + 1) = m := by omega
    -- Step 8: case-split on whether breakTie fires.
    -- count is τ-invariant (same multiset under τ-relabeling).
    have h_count_eq : breakTieCount conv₁ s = breakTieCount conv₂ s :=
      breakTieCount_τ_invariant τ conv₁ conv₂ h_conv₁_size h_conv₂_size h_conv_rel s
    by_cases hcount : breakTieCount conv₁ s < 2
    · -- Case 1 (no fire): arr_i' = conv_i. They're τ-related; apply IH at s+1.
      have hcount₂ : breakTieCount conv₂ s < 2 := h_count_eq ▸ hcount
      have h_arr₁'_eq : arr₁' = conv₁ := by
        rw [h_arr₁'_def, breakTie_noop conv₁ s hcount]
      have h_arr₂'_eq : arr₂' = conv₂ := by
        rw [h_arr₂'_def, breakTie_noop conv₂ s hcount₂]
      rw [h_arr₁'_eq, h_arr₂'_eq]
      -- IH at s+1: needs UniquelyHeldBelow conv₁ (s+1). From h_arr₁'_unique + arr₁' = conv₁.
      have h_conv₁_unique_succ : @UniquelyHeldBelow n conv₁ (s + 1) := h_arr₁'_eq ▸ h_arr₁'_unique
      exact ih (s + 1) conv₁ conv₂ h_m_def' h_conv₁_size h_conv₂_size h_conv_rel
        h_conv₁_prefix h_conv₁_unique_succ hs1
    · -- Case 2 (fire): count ≥ 2 on both sides. Choice-bridging argument.
      -- TODO: this is the substantive part of Phase 5. Sketch:
      --   (a) Define v₁ := min (typeClass conv₁ s) and v₂ := min (typeClass conv₂ s).
      --   (b) Show arr₁' = breakTieAt (shiftAbove s conv₁) s v₁.
      --   (c) Similarly arr₂' = breakTieAt (shiftAbove s conv₂) s v₂.
      --   (d) τ v₁ ∈ typeClass conv₂ s (since τ⋅typeClass conv₁ = typeClass conv₂).
      --   (e) breakTieAt (shiftAbove s conv₁) s v₁ τ-related to
      --       breakTieAt (shiftAbove s conv₂) s (τ v₁) via Phase 4 (`breakTieAt_τ_related`).
      --   (f) Apply IH at s+1 to (e)'s τ-related pair.
      --   (g) Find σ ∈ TypedAut(conv₂) connecting (τ v₁) and v₂ (orbit equality, requires
      --       tracking Aut(G, vts) through iterations).
      --   (h) Apply IH at s+1 again with σ to bridge breakTieAt at v₂ vs (τ v₁).
      --   (i) Combine.
      -- Helpers needed: breakTie_eq_breakTieAt_min_under_count, typeClass_τ_equivariant,
      -- shiftAbove_τ_related, conv₂_TypedAut_orbit_complete (~50 lines each).
      sorry

/-! ### Next concrete steps

The base case is closed via Phase 3.E. The inductive step (~200 lines) requires:
  - One iteration of `runFrom` via `runFrom_succ`.
  - Phase 2 (`convergeLoop_VtsInvariant_eq`) for τ-relatedness of the converged arrays.
  - Hypothesis preservation via `convergeLoop_preserves_prefix`,
    `convergeLoop_preserves_lower_uniqueness`, `breakTie_step_preserves_uniqueness`.
  - Choice-bridging via Phase 4 (`breakTieAt_τ_related`) + an inline tiebreak-choice
    independence argument that recursively uses the IH at level `s+1`.

(a) Modify `Tiebreak.lean::runFrom_VtsInvariant_eq` to add `IsPrefixTyping` hypothesis,
    or **alternatively**, replace the sorry with a call to
    `runFrom_VtsInvariant_eq_strong` and add the missing hypothesis at the call sites.

(b) Modify `Tiebreak.lean::tiebreak_choice_independent` to add the corresponding
    hypothesis (which its callers naturally have via the §7 prefix invariant).

(c) Adapt `Main.lean::run_isomorphic_eq_new` to thread `IsPrefixTyping.replicate_zero`.

(d) Complete the inductive step of `runFrom_VtsInvariant_eq_strong` (Phase 5's main work).
-/

end Graph
