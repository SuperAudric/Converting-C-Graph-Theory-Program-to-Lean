import FullCorrectness.Equivariance.StageDRelational
import FullCorrectness.Equivariance.BreakTieRelational
import FullCorrectness.Tiebreak

/-!
# Phase 5 — `runFrom_VtsInvariant_eq` via joint induction
  (`FullCorrectness.Equivariance.RunFromRelational`)

The single load-bearing reduction needed by §6: τ-related typings going through `runFrom`
produce equal canonical matrices.

## Important caveat: tie-freeness at the base case

The statement of `runFrom_VtsInvariant_eq` (in `Tiebreak.lean`) is:

```
τ ∈ Aut G → arr₁, arr₂ τ-related → runFrom s arr₁ G = runFrom s arr₂ G
```

This is **not** unconditionally true. For `s = n`, the foldl is empty and the result is
`labelEdgesAccordingToRankings arr_i G`. When `arr_i` has ties, `computeDenseRanks`'s
secondary `vertex-index` key breaks ties non-equivariantly under τ, so the canonical
matrices can differ.

**Concrete counterexample** (showing the claim is too strong):
  - G = path graph 0–1–2 (edges 0-1, 1-2).
  - τ = swap(0, 2) ∈ Aut G.
  - rks₁ = [0, 5, 5], rks₂ = [5, 5, 0].
  - τ-related: rks₂[w] = rks₁[τ⁻¹ w] for all w. ✓
  - labelEdges rks₁ G = path 0–1–2.
  - labelEdges rks₂ G = graph with edges {0-2, 1-2} (NOT a path 0-1-2).

So `runFrom n rks₁ G ≠ runFrom n rks₂ G` for this τ-related pair.

## The right form of the lemma

The lemma is provable when one of these additional hypotheses holds:

  (A) `arr_i` already has values in 0..start-1 distinct (prefix tie-free up to start).
  (B) `arr_i` is the output of a sufficiently-many-iterated convergeLoop+breakTie chain
      that the final orderedRanks (after the foldl) is tie-free.
  (C) `arr_i` has all values distinct (fully tie-free).

In the algorithmic context (§6's `tiebreak_choice_independent` and §8's
`run_isomorphic_eq_new`), the inputs to `runFrom` always satisfy a variant of (A) by
the prefix invariant from §7 (`orderVertices_prefix_invariant`).

## Proof structure (under hypothesis A or B)

Joint induction on `m = n - start`, sharing IH for both:

  - **P₁ (k):** `runFrom_VtsInvariant_eq` at `n - start = k`.
  - **P₂ (k):** `tiebreak_choice_independent` at `n - start = k`.

**Base case (k = 0):** runFrom n arr G = labelEdges arr G. Use Phase 3
(`labelEdges_VtsInvariant_eq_distinct`) under tie-freeness inherited from the prefix
invariant + extra hypothesis.

**Inductive step (k > 0):** Unfold one iteration of the foldl:
  - `convergeLoop` step: by Phase 2 (Stage C-rel), τ-related → τ-related.
  - `breakTie` step: choices may diverge; bridge via Phase 4 (`breakTieAt_τ_related`)
    + IH P₂ (k-1) (orbit-equivalence of tiebreak choices).

## Status: structural skeleton + helpers only

Closing `runFrom_VtsInvariant_eq` properly requires either:
  1. Adding the missing hypothesis to its statement in `Tiebreak.lean` (and propagating
     to all call sites — which, for the canonizer pipeline, hold by the prefix invariant).
  2. Relying on a more sophisticated invariant about the algorithm's reachable states.

This file provides the helper that handles the **τ-foldl-step** (one
convergeLoop+breakTie iteration on τ-related inputs), which is the inductive content
shared between Phases 5 and 6. The main `runFrom_VtsInvariant_eq` proof remains a
sorry pending hypothesis adjustment.
-/

namespace Graph

variable {n : Nat}

/-! ### One foldl iteration: τ-equivariance up to tiebreak choice -/

/-- One `convergeLoop` step on τ-related typings preserves τ-relatedness. Direct
restatement of `convergeLoop_VtsInvariant_eq` for use within the foldl induction. -/
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
  · -- size of converged₁ = n.
    induction n generalizing vts₁ with
    | zero => exact h_size₁
    | succ k ih =>
      -- convergeLoop init vts (k+1).size = vts.size by induction.
      -- Use convergeOnce_size_preserving repeatedly.
      have h_iter : ∀ (vts : Array VertexType) (h : vts.size = k + 1) (fuel : Nat),
          (convergeLoop (initializePaths G) vts fuel).size = k + 1 := by
        intro vts h fuel
        induction fuel generalizing vts with
        | zero => exact h
        | succ j ih_j =>
          change (if (convergeOnce (initializePaths G) vts).2
                  then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 j
                  else (convergeOnce (initializePaths G) vts).1).size = k + 1
          have h_co_size : (convergeOnce (initializePaths G) vts).1.size = k + 1 := by
            rw [convergeOnce_size_preserving]; exact h
          split
          · exact ih_j _ h_co_size
          · exact h_co_size
      exact h_iter vts₁ h_size₁ (k + 1)
  · -- size of converged₂ = n. Same argument.
    induction n generalizing vts₂ with
    | zero => exact h_size₂
    | succ k _ =>
      have h_iter : ∀ (vts : Array VertexType) (h : vts.size = k + 1) (fuel : Nat),
          (convergeLoop (initializePaths G) vts fuel).size = k + 1 := by
        intro vts h fuel
        induction fuel generalizing vts with
        | zero => exact h
        | succ j ih_j =>
          change (if (convergeOnce (initializePaths G) vts).2
                  then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 j
                  else (convergeOnce (initializePaths G) vts).1).size = k + 1
          have h_co_size : (convergeOnce (initializePaths G) vts).1.size = k + 1 := by
            rw [convergeOnce_size_preserving]; exact h
          split
          · exact ih_j _ h_co_size
          · exact h_co_size
      exact h_iter vts₂ h_size₂ (k + 1)
  · -- τ-relatedness preserved (Phase 2 directly).
    exact convergeLoop_VtsInvariant_eq G τ hτ vts₁ vts₂ n h_size₁ h_size₂ h_rel

/-! ### `runFrom_VtsInvariant_eq`: pending hypothesis adjustment

The existing `runFrom_VtsInvariant_eq` in `Tiebreak.lean` requires an additional
tie-freeness or prefix-invariant hypothesis (see file docstring). Closing it under the
current statement is **not possible** because of the tie-breaking issue.

The pragmatic resolution would be to:
  1. Modify `Tiebreak.lean`'s `runFrom_VtsInvariant_eq` to add a hypothesis like
     `tieFree (final orderedRanks)` or `prefixUnique (input arr) start`.
  2. Update `tiebreak_choice_independent` to provide this hypothesis from its caller's
     context (which always has the prefix invariant by §7).
  3. Update the call site in `Main.lean`'s `run_isomorphic_eq_new` similarly.

This file does not perform that surgery — modifying the existing theorem signatures
would ripple through `Tiebreak.lean` and `Main.lean`. Instead, the foldl-step helper
above is provided as the building block, and `runFrom_VtsInvariant_eq` remains the open
sorry it has been throughout the project.
-/

end Graph
