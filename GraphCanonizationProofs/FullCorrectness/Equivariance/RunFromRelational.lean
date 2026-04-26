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

/-- **Strengthened** `runFrom_VtsInvariant_eq`: τ-related typings with prefix typing
+ lower-uniqueness produce equal canonical matrices.

The `IsPrefixTyping arr₁` + `UniquelyHeldBelow arr₁ s` hypotheses precisely capture
the algorithmic state after `s` outer iterations: values 0..s-1 are uniquely held, and
all values are in some prefix `{0..m-1}`. Then the remaining `n - s` foldl iterations
(at targets s, s+1, ..., n-1) extend uniqueness to all of `{0..n-1}`, producing
tie-free output where Phase 3's `labelEdges_VtsInvariant_eq_distinct` applies.

**Proof status: stated only; full closure pending Phase 3 + joint induction.**

The plan (recorded in this file's header):
  - Joint induction on `m = n - s` together with `tiebreak_choice_independent_strong`.
  - Base case (m = 0): `UniquelyHeldBelow arr s` with `s = n` is exactly tie-freeness;
    apply Phase 3 directly.
  - Step (m > 0): unfold one foldl iteration; use Phase 2 (Stage C-rel) + Phase 4 + IH.
    The hypothesis updates via `convergeLoop_preserves_lower_uniqueness` +
    `breakTie_step_preserves_uniqueness`. -/
theorem runFrom_VtsInvariant_eq_strong
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (_hτ : τ ∈ AdjMatrix.Aut G)
    (arr₁ arr₂ : Array VertexType)
    (_h_size₁ : arr₁.size = n) (_h_size₂ : arr₂.size = n)
    (_h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0)
    (_h_prefix : @IsPrefixTyping n arr₁)
    (_h_unique : @UniquelyHeldBelow n arr₁ s)
    (_hs : s ≤ n) :
    runFrom s arr₁ G = runFrom s arr₂ G := by
  -- TODO Phase 5: implement the joint induction outlined in the file docstring.
  -- The hypothesis transfer to arr₂ is via IsPrefixTyping_τ_transfer +
  -- UniquelyHeldBelow_τ_transfer (proved above).
  sorry

/-! ### Next concrete steps

(a) Modify `Tiebreak.lean::runFrom_VtsInvariant_eq` to add `IsPrefixTyping` hypothesis,
    or **alternatively**, replace the sorry with a call to
    `runFrom_VtsInvariant_eq_strong` and add the missing hypothesis at the call sites.

(b) Modify `Tiebreak.lean::tiebreak_choice_independent` to add the corresponding
    hypothesis (which its callers naturally have via the §7 prefix invariant).

(c) Adapt `Main.lean::run_isomorphic_eq_new` to thread `IsPrefixTyping.replicate_zero`.

(d) Prove `runFrom_VtsInvariant_eq_strong` via joint induction (Phase 5's main work).

(e) Close Phase 3 (separate work).
-/

end Graph
