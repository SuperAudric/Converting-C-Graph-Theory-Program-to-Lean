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

/-- For arrays of size `n`, the `toList` is the `List.finRange n`-indexed map of `getD`
values. This is the bridge between Array.foldl-style counts and the Fin-indexed list
form used in countP/Perm arguments. -/
private theorem Array.toList_eq_finRange_map (arr : Array VertexType) (h_size : arr.size = n) :
    arr.toList = (List.finRange n).map (fun w : Fin n => arr.getD w.val 0) := by
  apply List.ext_getElem
  · simp [h_size]
  · intro i hi₁ _hi₂
    have hi_arr : i < arr.size := by
      rw [Array.length_toList] at hi₁; exact hi₁
    rw [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    simp [Array.getElem_eq_getD (h := hi_arr) 0]

/-- For τ-related arrays of size `n`, the count of any target value is the same.
The multiset of values is preserved by τ-relabeling (τ is a bijection on Fin n).

Proof strategy: show `arr₂.toList ~ arr₁.toList` (List.Perm) via the τ-relabeling of
indices, then apply `List.Perm.countP_eq`. -/
private theorem breakTieCount_τ_invariant
    (τ : Equiv.Perm (Fin n))
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (t : VertexType) :
    breakTieCount arr₁ t = breakTieCount arr₂ t := by
  -- arr₂.toList ~ arr₁.toList via τ-permutation of indices in finRange.
  have h_perm : List.Perm arr₂.toList arr₁.toList := by
    rw [Array.toList_eq_finRange_map arr₁ h_size₁,
        Array.toList_eq_finRange_map arr₂ h_size₂]
    -- (fun w => arr₂[w]) = (fun w => arr₁[w]) ∘ (τ⁻¹ : Fin n → Fin n) by h_rel.
    have h_funext : (fun w : Fin n => arr₂.getD w.val 0)
        = (fun w : Fin n => arr₁.getD w.val 0) ∘ (τ⁻¹ : Equiv.Perm (Fin n)) := by
      funext w; exact h_rel w
    rw [h_funext, ← List.map_map]
    -- (List.finRange n).map τ⁻¹ ~ List.finRange n  ⟹  apply List.Perm.map.
    exact (Equiv.Perm.map_finRange_perm τ⁻¹).map _
  rw [breakTieCount_eq_countP, breakTieCount_eq_countP]
  exact (h_perm.countP_eq _).symm

/-! ### typeClass under τ-relation -/

/-- The τ-image of `typeClass arr₁ t` equals `typeClass arr₂ t` when `arr₁, arr₂` are
τ-related. This is the orbit-equivariance of the type class set under the τ-action
on `Fin n`. -/
private theorem typeClass_τ_image_eq
    (τ : Equiv.Perm (Fin n))
    (arr₁ arr₂ : Array VertexType)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (t : VertexType) :
    @typeClass n arr₂ t = τ '' @typeClass n arr₁ t := by
  ext w
  constructor
  · -- w ∈ typeClass arr₂ t  ⟹  τ⁻¹ w ∈ typeClass arr₁ t  ∧  τ (τ⁻¹ w) = w.
    intro hw
    refine ⟨τ⁻¹ w, ?_, ?_⟩
    · show arr₁.getD (τ⁻¹ w).val 0 = t
      rw [← h_rel w]; exact hw
    · simp
  · -- ∃ v ∈ typeClass arr₁ t, τ v = w  ⟹  w ∈ typeClass arr₂ t.
    rintro ⟨v, hv, hτv⟩
    show arr₂.getD w.val 0 = t
    rw [h_rel w, ← hτv]
    have h_inv : τ⁻¹ (τ v) = v := by simp
    rw [h_inv]; exact hv

/-- When `breakTieCount arr t ≥ 2`, the smallest-index target-valued vertex exists as
a `Fin n` (given `arr.size = n`). This packages `Nat.find` on the predicate. -/
private theorem breakTie_min_witness
    (arr : Array VertexType) (h_size : arr.size = n) (t : VertexType)
    (hcount : 2 ≤ breakTieCount arr t) :
    ∃ v_star : Fin n,
      arr.getD v_star.val 0 = t ∧
      (∀ i : Fin n, i.val < v_star.val → arr.getD i.val 0 ≠ t) := by
  classical
  -- The set of target-valued indices is non-empty (count ≥ 2 ≥ 1).
  have h_pos : 0 < breakTieCount arr t := by omega
  rw [breakTieCount_eq_countP] at h_pos
  -- countP > 0 ⟹ ∃ x ∈ arr.toList, x = t.
  rw [List.countP_pos_iff] at h_pos
  obtain ⟨x, hx_mem, hx_eq⟩ := h_pos
  -- Convert: ∃ idx < arr.size, arr.toList[idx] = t.
  have hx_eq' : x = t := by simpa using hx_eq
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hx_mem
  have h_ex : ∃ i, i < arr.size ∧ arr.getD i 0 = t := by
    refine ⟨idx, ?_, ?_⟩
    · simpa using hidx_lt
    · have hi_arr : idx < arr.size := by simpa using hidx_lt
      have h1 : arr.getD idx 0 = arr[idx]'hi_arr :=
        (Array.getElem_eq_getD (h := hi_arr) 0).symm
      have h2 : arr[idx]'hi_arr = arr.toList[idx]'hidx_lt :=
        (Array.getElem_toList hi_arr).symm
      rw [h1, h2, hidx_eq]; exact hx_eq'
  set v := Nat.find h_ex with h_v_def
  have hv_spec : v < arr.size ∧ arr.getD v 0 = t := Nat.find_spec h_ex
  have hv_min_raw : ∀ i, i < v → ¬ (i < arr.size ∧ arr.getD i 0 = t) :=
    fun i hi => Nat.find_min h_ex hi
  have hv_lt_n : v < n := h_size ▸ hv_spec.1
  refine ⟨⟨v, hv_lt_n⟩, hv_spec.2, ?_⟩
  intro i hi h_eq
  -- i.val < v but arr.getD i.val 0 = t — violates Nat.find minimality.
  have h_i_in_size : i.val < arr.size := h_size ▸ i.isLt
  exact hv_min_raw i.val hi ⟨h_i_in_size, h_eq⟩

/-- The min-index target-valued vertex (when count ≥ 2) is in `typeClass arr t`. -/
private theorem breakTie_min_witness_in_typeClass
    (arr : Array VertexType) (h_size : arr.size = n) (t : VertexType)
    (hcount : 2 ≤ breakTieCount arr t) :
    ∃ v_star : Fin n,
      v_star ∈ @typeClass n arr t ∧
      (∀ i : Fin n, i.val < v_star.val → arr.getD i.val 0 ≠ t) := by
  obtain ⟨v_star, hv_val, hv_min⟩ := breakTie_min_witness arr h_size t hcount
  exact ⟨v_star, hv_val, hv_min⟩

/-! ### Strengthened theorem proof

**Strengthened** `runFrom_VtsInvariant_eq`: τ-related typings with prefix typing
+ lower-uniqueness produce equal canonical matrices. The `IsPrefixTyping arr₁` +
`UniquelyHeldBelow arr₁ s` hypotheses precisely capture the algorithmic state after `s`
outer iterations: values 0..s-1 are uniquely held. Then the remaining `n - s` foldl
iterations extend uniqueness to all of `{0..n-1}`, producing tie-free output where
Phase 3.E (`labelEdges_VtsInvariant_eq_distinct`) applies. -/
/-! ### Orbit-completeness invariant

The strong theorem requires an orbit-completeness hypothesis at iteration boundaries:
for every post-iters intermediate array `mid`, vertices in the convergeLoop output of `mid`
that share a value are in the same `TypedAut`-orbit. This is the canonizer-correctness
invariant — proving its preservation through algorithm iterations is the deep half of
canonizer correctness; here we treat it as a hypothesis discharged at the call site
(Phase 6 / `Main.lean`). -/

/-- Orbit-completeness: for `mid` an intermediate algorithm state, vertices with equal
values in `convergeLoop(initializePaths G) mid n` are in the same `TypedAut`-orbit
of that converged array.

Discharged at the call site by canonizer-correctness reasoning. -/
def OrbitCompleteAfterConv (G : AdjMatrix n) : Prop :=
  ∀ (mid : Array VertexType), mid.size = n →
    ∀ v₁ v₂ : Fin n,
      (convergeLoop (initializePaths G) mid n).getD v₁.val 0 =
      (convergeLoop (initializePaths G) mid n).getD v₂.val 0 →
      ∃ σ ∈ G.TypedAut (convergeLoop (initializePaths G) mid n), σ v₁ = v₂

theorem runFrom_VtsInvariant_eq_strong
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ AdjMatrix.Aut G)
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (h_prefix : @IsPrefixTyping n arr₁)
    (h_unique : @UniquelyHeldBelow n arr₁ s)
    (hs : s ≤ n)
    (hOrbit : OrbitCompleteAfterConv (n := n) G) :
    runFrom s arr₁ G = runFrom s arr₂ G := by
  -- Induct on m := n - s. Generalize over s, τ, arr₁, arr₂ so the IH applies at level s+1
  -- with a possibly different τ' (built by composing τ with an orbit-bridging σ).
  suffices h : ∀ (m s : Nat) (τ' : Equiv.Perm (Fin n)) (_hτ' : τ' ∈ AdjMatrix.Aut G)
      (arr₁ arr₂ : Array VertexType),
      n - s = m →
      arr₁.size = n → arr₂.size = n →
      (∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ'⁻¹ w).val 0) →
      @IsPrefixTyping n arr₁ →
      @UniquelyHeldBelow n arr₁ s →
      s ≤ n →
      runFrom s arr₁ G = runFrom s arr₂ G by
    exact h (n - s) s τ hτ arr₁ arr₂ rfl h_size₁ h_size₂ h_rel h_prefix h_unique hs
  clear h_size₁ h_size₂ h_rel h_prefix h_unique hs arr₁ arr₂ s τ hτ
  intro m
  induction m with
  | zero =>
    intro s τ hτ arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    -- Base: n - s = 0 ⟹ s = n.
    have hsn : s = n := by omega
    have h_unique_n : @UniquelyHeldBelow n arr₁ n := hsn ▸ h_unique
    have h_tf₁ : TieFree arr₁ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₁ h_size₁ h_unique_n
    have h_unique₂ : @UniquelyHeldBelow n arr₂ n :=
      UniquelyHeldBelow_τ_transfer τ arr₁ arr₂ h_rel n h_unique_n
    have h_tf₂ : TieFree arr₂ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₂ h_size₂ h_unique₂
    rw [hsn, runFrom_at_n, runFrom_at_n]
    exact (labelEdges_VtsInvariant_eq_distinct G τ hτ arr₁ arr₂ h_size₁ h_size₂ h_tf₁ h_tf₂ h_rel).symm
  | succ m ih =>
    intro s τ hτ arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    have hs_lt : s < n := by omega
    rw [runFrom_succ G arr₁ s hs_lt, runFrom_succ G arr₂ s hs_lt]
    set conv₁ := convergeLoop (initializePaths G) arr₁ n with h_conv₁_def
    set conv₂ := convergeLoop (initializePaths G) arr₂ n with h_conv₂_def
    set arr₁' := (breakTie conv₁ s).1 with h_arr₁'_def
    set arr₂' := (breakTie conv₂ s).1 with h_arr₂'_def
    have ⟨h_conv₁_size, h_conv₂_size, h_conv_rel⟩ :=
      convergeLoop_step_τ_preserved G τ hτ arr₁ arr₂ h_size₁ h_size₂ h_rel
    have h_conv₁_prefix : @IsPrefixTyping n conv₁ :=
      convergeLoop_preserves_prefix G arr₁ n h_size₁ h_prefix
    have h_conv₁_both : @IsPrefixTyping n conv₁ ∧ @UniquelyHeldBelow n conv₁ s :=
      convergeLoop_preserves_lower_uniqueness G arr₁ s (Nat.le_of_lt hs_lt) n h_size₁ h_prefix h_unique
    have h_conv₁_unique : @UniquelyHeldBelow n conv₁ s := h_conv₁_both.2
    have ⟨h_arr₁'_prefix, h_arr₁'_unique⟩ :=
      breakTie_step_preserves_uniqueness conv₁ s hs_lt h_conv₁_size h_conv₁_prefix h_conv₁_unique
    have h_arr₁'_size : arr₁'.size = n := by
      rw [h_arr₁'_def, breakTie_size]; exact h_conv₁_size
    have h_arr₂'_size : arr₂'.size = n := by
      rw [h_arr₂'_def, breakTie_size]; exact h_conv₂_size
    have hs1 : s + 1 ≤ n := hs_lt
    have h_m_def' : n - (s + 1) = m := by omega
    have h_count_eq : breakTieCount conv₁ s = breakTieCount conv₂ s :=
      breakTieCount_τ_invariant τ conv₁ conv₂ h_conv₁_size h_conv₂_size h_conv_rel s
    by_cases hcount : breakTieCount conv₁ s < 2
    · -- Case 1 (no fire): arr_i' = conv_i. τ-related; apply IH at s+1 with τ' := τ.
      have hcount₂ : breakTieCount conv₂ s < 2 := h_count_eq ▸ hcount
      have h_arr₁'_eq : arr₁' = conv₁ := by
        rw [h_arr₁'_def, breakTie_noop conv₁ s hcount]
      have h_arr₂'_eq : arr₂' = conv₂ := by
        rw [h_arr₂'_def, breakTie_noop conv₂ s hcount₂]
      rw [h_arr₁'_eq, h_arr₂'_eq]
      have h_conv₁_unique_succ : @UniquelyHeldBelow n conv₁ (s + 1) := h_arr₁'_eq ▸ h_arr₁'_unique
      exact ih (s + 1) τ hτ conv₁ conv₂ h_m_def' h_conv₁_size h_conv₂_size h_conv_rel
        h_conv₁_prefix h_conv₁_unique_succ hs1
    · -- Case 2 (fire): count ≥ 2 on both sides. Choice-bridging via orbit-completeness.
      have hcount2 : 2 ≤ breakTieCount conv₁ s := by omega
      have hcount2_b : 2 ≤ breakTieCount conv₂ s := h_count_eq ▸ hcount2
      -- Step 1: extract min-witnesses v₁, v₂ in respective typeClasses at value s.
      obtain ⟨v₁, hv₁_val, hv₁_min⟩ :=
        breakTie_min_witness conv₁ h_conv₁_size s hcount2
      obtain ⟨v₂, hv₂_val, hv₂_min⟩ :=
        breakTie_min_witness conv₂ h_conv₂_size s hcount2_b
      -- Step 2: τ v₁ ∈ typeClass conv₂ s (typeClass τ-image equality).
      have hτv₁_in : conv₂.getD (τ v₁).val 0 = s := by
        have := typeClass_τ_image_eq τ conv₁ conv₂ h_conv_rel s
        have h_in : τ v₁ ∈ @typeClass n conv₂ s := by
          rw [this]; exact ⟨v₁, hv₁_val, rfl⟩
        exact h_in
      -- Step 3: orbit-completeness ⟹ ∃ σ ∈ TypedAut conv₂ with σ (τ v₁) = v₂.
      have hτv₁_v₂_same : conv₂.getD (τ v₁).val 0 = conv₂.getD v₂.val 0 := by
        rw [hτv₁_in, hv₂_val]
      obtain ⟨σ, hσ_TypedAut, hσ_apply⟩ :=
        hOrbit arr₂ h_size₂ (τ v₁) v₂ hτv₁_v₂_same
      -- Step 4: στ := σ * τ ∈ Aut G; (στ)⁻¹ w = τ⁻¹ (σ⁻¹ w).
      have hσ_Aut : σ ∈ AdjMatrix.Aut G := AdjMatrix.TypedAut_le_Aut G conv₂ hσ_TypedAut
      have hσ_INV : VtsInvariant σ conv₂ := hσ_TypedAut.2
      let στ := σ * τ
      have hστ_Aut : στ ∈ AdjMatrix.Aut G := Subgroup.mul_mem _ hσ_Aut hτ
      -- Step 5: arr₂'[w] = arr₁'[(στ)⁻¹ w] for all w (case analysis on conv₂[w]).
      have h_στ_rel : ∀ w : Fin n, arr₂'.getD w.val 0 = arr₁'.getD (στ⁻¹ w).val 0 := by
        intro w
        -- (στ)⁻¹ w = τ⁻¹ (σ⁻¹ w).
        have h_inv_apply : στ⁻¹ w = τ⁻¹ (σ⁻¹ w) := by
          show (σ * τ)⁻¹ w = τ⁻¹ (σ⁻¹ w)
          simp [mul_inv_rev]
        rw [h_inv_apply]
        -- Let u := σ⁻¹ w (so w = σ u). conv₂[w] = conv₂[σ u] = conv₂[u] (since σ ∈ TypedAut).
        set u := σ⁻¹ w with h_u_def
        have h_w_eq_σu : w = σ u := by simp [h_u_def]
        have h_conv₂_w_eq_u : conv₂.getD w.val 0 = conv₂.getD u.val 0 := by
          have := hσ_INV u
          rw [show σ u = w from h_w_eq_σu.symm] at this
          exact this
        -- Bridge to conv₁ via h_conv_rel: conv₁[τ⁻¹ u] = conv₂[u] (note: roles reversed).
        have h_conv_link : conv₁.getD (τ⁻¹ u).val 0 = conv₂.getD u.val 0 := by
          rw [h_conv_rel u]
        -- Case analysis on conv₂[w] = conv₂[u] = conv₁[τ⁻¹ u].
        rcases lt_trichotomy (conv₂.getD w.val 0) s with h_lt | h_eq | h_gt
        · -- conv₂[w] < s ⟹ both arr_i' = conv_i (below).
          rw [breakTie_getD_below conv₂ s h_lt]
          have h_below₁ : conv₁.getD (τ⁻¹ u).val 0 < s := by
            rw [h_conv_link, ← h_conv₂_w_eq_u]; exact h_lt
          rw [breakTie_getD_below conv₁ s h_below₁]
          rw [h_conv_link, ← h_conv₂_w_eq_u]
        · -- conv₂[w] = s ⟹ both in typeClass; differ by min-keep.
          have h_w_in : conv₂.getD w.val 0 = s := h_eq
          have h_u_in : conv₂.getD u.val 0 = s := h_conv₂_w_eq_u ▸ h_eq
          have h_τinv_u_in : conv₁.getD (τ⁻¹ u).val 0 = s := h_conv_link.trans h_u_in
          -- arr₂'[w]: if w = v₂ then s else s+1.
          -- arr₁'[τ⁻¹ u]: if τ⁻¹ u = v₁ then s else s+1.
          -- σ (τ v₁) = v₂; w = σ u; so w = v₂ ⟺ σ u = σ (τ v₁) ⟺ u = τ v₁ ⟺ τ⁻¹ u = v₁.
          have h_iff : w = v₂ ↔ τ⁻¹ u = v₁ := by
            constructor
            · intro hw
              have : σ u = σ (τ v₁) := by
                rw [← h_w_eq_σu, hw, ← hσ_apply]
              have hu_eq : u = τ v₁ := σ.injective this
              have : τ⁻¹ u = τ⁻¹ (τ v₁) := by rw [hu_eq]
              simpa using this
            · intro h_inv_eq
              have hu_eq : u = τ v₁ := by
                have : τ (τ⁻¹ u) = τ v₁ := by rw [h_inv_eq]
                simpa using this
              rw [h_w_eq_σu, hu_eq, hσ_apply]
          -- Now case analysis on whether w = v₂.
          have hv₂_size : v₂.val < conv₂.size := h_conv₂_size.symm ▸ v₂.isLt
          have hv₁_size : v₁.val < conv₁.size := h_conv₁_size.symm ▸ v₁.isLt
          have hv₁_min_idx : ∀ i, i < v₁.val → conv₁.getD i 0 ≠ s := by
            intro i hi h_i_eq
            -- i < v₁.val with conv₁[i] = s; build Fin n witness.
            have hi_lt_n : i < n := by
              have hv₁_lt_n : v₁.val < n := v₁.isLt
              omega
            exact hv₁_min ⟨i, hi_lt_n⟩ hi h_i_eq
          have hv₂_min_idx : ∀ i, i < v₂.val → conv₂.getD i 0 ≠ s := by
            intro i hi h_i_eq
            have hi_lt_n : i < n := by
              have hv₂_lt_n : v₂.val < n := v₂.isLt
              omega
            exact hv₂_min ⟨i, hi_lt_n⟩ hi h_i_eq
          by_cases hw_v₂ : w = v₂
          · -- w = v₂: arr₂'[v₂] = s (kept).
            have h_arr₂'_v₂ : arr₂'.getD v₂.val 0 = s := by
              show (breakTie conv₂ s).1.getD v₂.val 0 = s
              exact breakTie_getD_at_min conv₂ s hv₂_size hv₂_val hv₂_min_idx
            have h_τinv_u_v₁ : τ⁻¹ u = v₁ := h_iff.mp hw_v₂
            have h_arr₁'_v₁ : arr₁'.getD (τ⁻¹ u).val 0 = s := by
              rw [h_τinv_u_v₁]
              show (breakTie conv₁ s).1.getD v₁.val 0 = s
              exact breakTie_getD_at_min conv₁ s hv₁_size hv₁_val hv₁_min_idx
            rw [hw_v₂, h_arr₂'_v₂, h_arr₁'_v₁]
          · -- w ≠ v₂ but w ∈ typeClass: arr₂'[w] = s+1 (promoted).
            have hw_size : w.val < conv₂.size := h_conv₂_size.symm ▸ w.isLt
            have h_arr₂'_w : arr₂'.getD w.val 0 = s + 1 := by
              show (breakTie conv₂ s).1.getD w.val 0 = s + 1
              exact breakTie_getD_at_other conv₂ s hv₂_size hv₂_val hv₂_min_idx
                hw_size h_w_in (fun heq => hw_v₂ (Fin.ext heq))
            have h_τinv_u_ne_v₁ : τ⁻¹ u ≠ v₁ := fun heq => hw_v₂ (h_iff.mpr heq)
            have h_τinv_u_size : (τ⁻¹ u).val < conv₁.size := h_conv₁_size.symm ▸ (τ⁻¹ u).isLt
            have h_arr₁'_τinv_u : arr₁'.getD (τ⁻¹ u).val 0 = s + 1 := by
              show (breakTie conv₁ s).1.getD (τ⁻¹ u).val 0 = s + 1
              exact breakTie_getD_at_other conv₁ s hv₁_size hv₁_val hv₁_min_idx
                h_τinv_u_size h_τinv_u_in (fun heq => h_τinv_u_ne_v₁ (Fin.ext heq))
            rw [h_arr₂'_w, h_arr₁'_τinv_u]
        · -- conv₂[w] > s ⟹ both arr_i' = conv_i + 1 (above), since count ≥ 2.
          rw [breakTie_getD_above conv₂ s hcount2_b h_gt]
          have h_above₁ : conv₁.getD (τ⁻¹ u).val 0 > s := by
            rw [h_conv_link, ← h_conv₂_w_eq_u]; exact h_gt
          rw [breakTie_getD_above conv₁ s hcount2 h_above₁]
          rw [h_conv_link, ← h_conv₂_w_eq_u]
      -- Step 6: apply IH at s+1 with τ' := στ.
      exact ih (s + 1) στ hστ_Aut arr₁' arr₂' h_m_def' h_arr₁'_size h_arr₂'_size
        h_στ_rel h_arr₁'_prefix h_arr₁'_unique hs1

/-! ### Lemmas previously sketched in `Tiebreak.lean`

The original `runFrom_VtsInvariant_eq` and `tiebreak_choice_independent` in `Tiebreak.lean`
were stated as `sorry` pending §3 closure. With the strong theorem available, they're now
provable here as direct wrappers — the strong theorem supplies the τ-relational equivariance,
and the §6 choice-independence lemma reduces to a single `breakTieAt_VtsInvariant_eq` step
to construct the τ-relation from the orbit hypothesis. Both lemmas inherit
`OrbitCompleteAfterConv G` as the canonizer-correctness hypothesis.

These replace the corresponding declarations in `Tiebreak.lean`. -/

/-- Pipeline τ-equivariance for `runFrom`. The original `Tiebreak.lean` stated a too-broad
form (no prefix/uniqueness/orbit hypotheses); the corrected form is supplied here by
direct application of `runFrom_VtsInvariant_eq_strong`.

Replaces the `Tiebreak.lean` sorry. -/
theorem runFrom_VtsInvariant_eq
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ AdjMatrix.Aut G)
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (h_prefix : @IsPrefixTyping n arr₁)
    (h_unique : @UniquelyHeldBelow n arr₁ s)
    (hs : s ≤ n)
    (hOrbit : OrbitCompleteAfterConv (n := n) G) :
    runFrom s arr₁ G = runFrom s arr₂ G :=
  runFrom_VtsInvariant_eq_strong G s τ hτ arr₁ arr₂ h_size₁ h_size₂ h_rel
    h_prefix h_unique hs hOrbit

/-- §6 Tiebreak choice-independence. For `vts` an Aut(G)-invariant typing and `v₁, v₂`
in the same `TypedAut(G, vts)`-orbit (`hconn`), running the rest of the pipeline from
`breakTieAt vts t₀ v_i` yields the same canonical matrix.

The proof reduces to `runFrom_VtsInvariant_eq` (above) by constructing the τ-relation
between `breakTieAt vts t₀ v₁` and `breakTieAt vts t₀ v₂` via `breakTieAt_VtsInvariant_eq`
applied to the τ provided by `hconn`. -/
theorem tiebreak_choice_independent
    (G : AdjMatrix n) (start : Nat) (vts : Array VertexType) (t₀ : VertexType)
    (v₁ v₂ : Fin n)
    (hsize : vts.size = n)
    (_hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (_hv₁ : v₁ ∈ @typeClass n vts t₀) (_hv₂ : v₂ ∈ @typeClass n vts t₀)
    (hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂)
    (h_prefix : @IsPrefixTyping n (breakTieAt vts t₀ v₁))
    (h_unique : @UniquelyHeldBelow n (breakTieAt vts t₀ v₁) (start + 1))
    (hs : start + 1 ≤ n)
    (hOrbit : OrbitCompleteAfterConv (n := n) G) :
    runFrom (start + 1) (breakTieAt vts t₀ v₁) G =
    runFrom (start + 1) (breakTieAt vts t₀ v₂) G := by
  obtain ⟨τ, hτ, hτv⟩ := hconn
  have hτG : G.permute τ = G := hτ.1
  have hτAut : τ ∈ G.Aut := hτG
  have hτvts : VtsInvariant τ vts := hτ.2
  have h_relabel : ∀ w : Fin n,
      (breakTieAt vts t₀ v₂).getD w.val 0 =
        (breakTieAt vts t₀ v₁).getD (τ⁻¹ w).val 0 := by
    intro w
    rw [show v₂ = τ v₁ from hτv.symm]
    exact breakTieAt_VtsInvariant_eq vts t₀ τ v₁ hsize hτvts w
  have h_size₁ : (breakTieAt vts t₀ v₁).size = n := by
    rw [breakTieAt_size]; exact hsize
  have h_size₂ : (breakTieAt vts t₀ v₂).size = n := by
    rw [breakTieAt_size]; exact hsize
  exact runFrom_VtsInvariant_eq G (start + 1) τ hτAut
            (breakTieAt vts t₀ v₁) (breakTieAt vts t₀ v₂)
            h_size₁ h_size₂ h_relabel h_prefix h_unique hs hOrbit

/-! ### Status (Phase 5 closed modulo `OrbitCompleteAfterConv`)

`runFrom_VtsInvariant_eq_strong` is closed via:
  - **Base** (s = n): Phase 3.E (`labelEdges_VtsInvariant_eq_distinct`).
  - **Inductive step Case 1** (no fire): IH at s+1 with the same τ.
  - **Inductive step Case 2** (fire): IH at s+1 with `στ := σ * τ`, where σ is supplied
    by the orbit-completeness hypothesis and bridges τ⋅min(typeClass conv₁ s) to
    min(typeClass conv₂ s).

The single open obligation is **`OrbitCompleteAfterConv G`** — the canonizer-correctness
invariant: vertices with equal values in any post-`convergeLoop` array share a single
`TypedAut`-orbit. This is dischargable at the call site (Phase 6 / `Main.lean`), where
the original σ ∈ Aut G connecting G and H supplies the orbit bridge.

### Next steps

(a) Replace `Tiebreak.lean::runFrom_VtsInvariant_eq`'s sorry with a call to
    `runFrom_VtsInvariant_eq_strong`, adding `IsPrefixTyping` + `UniquelyHeldBelow` +
    `OrbitCompleteAfterConv` hypotheses (provided at the Tiebreak call site by `Main.lean`).

(b) Phase 6 (`Main.lean::run_isomorphic_eq_new`) discharges
    `OrbitCompleteAfterConv` via the σ ∈ Aut G threading. Specifically: for `arr₂`
    obtained by σ-permuting some prior array, every vertex pair sharing a value in
    convergeLoop(arr₂) has a TypedAut-bridge constructible from σ and the algorithm's
    structure.
-/

end Graph
