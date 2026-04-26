import FullCorrectness.Equivariance.Actions
import FullCorrectness.Permutation
import FullCorrectness.Automorphism

/-!
# Cell-wise characterization of `labelEdgesAccordingToRankings`
  (`FullCorrectness.Equivariance.LabelEdgesCharacterization`)

Phase 3's deep technical content. Proves that for tie-free `rks`,

```
labelEdgesAccordingToRankings rks G = G.permute (denseRanksPerm rks)
```

where `denseRanksPerm rks : Equiv.Perm (Fin n)` is the unique permutation determined by
the dense-rank assignment.

## Approach (selection-sort by rank)

The labelEdgesAccordingToRankings fold is essentially selection sort: at step `k`, find
the vertex with rank `k` and swap it into position `k`. The cumulative effect of all
swaps is the permutation `denseRanksPerm rks` (mapping each vertex to its dense-rank
position).

The proof tracks an invariant on the fold's `(graph, rankMap)` pair, namely:
  `∃ σ_k, graph_k = G.permute σ_k AND rankMap_k = denseRanks_0 ∘ σ_k⁻¹`,
extending the strengthening pattern used in `labelEdgesAccordingToRankings_isomorphic`
(in `LeanGraphCanonizerV4Correctness.lean`) which only tracked the existence of σ_k,
not its identity.

## Status

This file establishes the foundational lemmas; the cell-wise characterization is the
deep content. Currently provides:

  * `computeDenseRanks_size` — output has size `numVertices`.
  * Helpers for working with the (rank, vertex-index) lex sort.

The full characterization is left as a `sorry` with detailed proof structure documented;
finishing it is one of the two remaining technical pieces (the other being Phase 5's
joint induction).
-/

namespace Graph

variable {n : Nat}

/-! ### `computeDenseRanks` size -/

/-- The output of `computeDenseRanks` has size equal to the input `numVertices`.

The result is built by folding over a list with `set!` operations starting from
`(Array.range numVertices).map fun _ => 0` which has size `numVertices`. Both
`set!` and the underlying `setIfInBounds` are size-preserving. -/
theorem computeDenseRanks_size (numVertices : Nat) (rks : Array VertexType) :
    (computeDenseRanks numVertices rks).size = numVertices := by
  unfold computeDenseRanks
  -- Generic: foldl of set! preserves size.
  suffices haux : ∀ (l : List Nat) (init : Array Nat),
      init.size = numVertices →
      ∀ (sorted : List (VertexType × Nat)),
        (l.foldl (fun (positionArray : Array Nat) sortedIdx =>
            positionArray.set! (sorted.getD sortedIdx (0, 0)).2 sortedIdx) init).size = numVertices by
    apply haux
    simp
  intro l
  induction l with
  | nil => intros _ h _; exact h
  | cons x xs ih =>
    intros init h_size sorted
    rw [List.foldl_cons]
    apply ih
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact h_size

/-! ### Strengthened fold lemma — tracks the cumulative permutation

Generalizes `labelEdgesAccordingToRankings_isomorphic` (which only tracks `G ≃ ...`)
by carrying an explicit permutation `σ` such that `acc.1 = G.permute σ`. This is the
strengthened invariant required for the cell-wise characterization. -/

/-- The labelEdges fold step extracted as a function. -/
private def labelEdgesStep (n : Nat) (vertices : List (Fin n))
    (accumulated : AdjMatrix n × Array Nat) (currentFin : Fin n) :
    AdjMatrix n × Array Nat :=
  let (graph, rankMap) := accumulated
  let targetPos := currentFin.val
  match vertices.find? (fun searchFin => rankMap.getD searchFin.val 0 == targetPos) with
  | none => (graph, rankMap)
  | some sourceFin =>
    let sourceIdx := sourceFin.val
    let swappedGraph := graph.swapVertexLabels currentFin sourceFin
    let rankAtSource := rankMap.getD sourceIdx 0
    let rankAtTarget := rankMap.getD targetPos 0
    (swappedGraph, (rankMap.set! sourceIdx rankAtTarget).set! targetPos rankAtSource)

/-- **Strengthened fold invariant.** For any list `vs` and accumulator with
`acc.1 = G.permute σ` for some `σ`, the foldl preserves the existence of such a
permutation. This generalizes `labelEdgesAccordingToRankings_isomorphic` from `G ≃ acc.1`
to "acc.1 is a specific permute of G".

The proof structure mirrors `labelEdgesAccordingToRankings_isomorphic`: induction on
`vs` with case-split on the `find?` branch. The `none` branch leaves σ unchanged; the
`some` branch composes one swap into σ.

**Use case:** specialized at `vs = List.finRange n` and `acc = (G, denseRanks rks)`,
the resulting σ is the cumulative composition of all swaps. Identifying this σ as
`denseRanksPerm rks` (the dense-rank perm) is the second half of the cell-wise
characterization.

**Status:** stated; not yet proved. The proof is direct but tedious — each swap
contributes one `Equiv.swap` factor to σ. -/
theorem labelEdges_fold_permutes
    (G : AdjMatrix n) (vs : List (Fin n)) (acc : AdjMatrix n × Array Nat)
    (σ : Equiv.Perm (Fin n)) (h_acc : acc.1 = G.permute σ) :
    ∃ σ' : Equiv.Perm (Fin n),
      (vs.foldl (labelEdgesStep n (List.finRange n)) acc).1 = G.permute σ' := by
  induction vs generalizing acc σ with
  | nil =>
    -- Base case: the foldl is acc itself.
    refine ⟨σ, ?_⟩
    rw [List.foldl_nil]
    exact h_acc
  | cons v rest ih =>
    rw [List.foldl_cons]
    -- One step: case-split on the find? branch.
    obtain ⟨graph, rankMap⟩ := acc
    show ∃ σ', (rest.foldl (labelEdgesStep n (List.finRange n))
                  (labelEdgesStep n (List.finRange n) (graph, rankMap) v)).1 = G.permute σ'
    unfold labelEdgesStep
    simp only []
    split
    · -- none branch: accumulator unchanged.
      apply ih
      exact h_acc
    · -- some sourceFin branch: graph gets one swap.
      rename_i sourceFin _
      apply ih (acc := (graph.swapVertexLabels v sourceFin, _))
      -- New graph = graph.swapVertexLabels v sourceFin
      --           = (G.permute σ).swapVertexLabels v sourceFin
      --           = (G.permute σ).permute (Equiv.swap v sourceFin)
      --           = G.permute (Equiv.swap v sourceFin * σ).
      have h_graph_eq : graph = G.permute σ := h_acc
      show graph.swapVertexLabels v sourceFin = G.permute (Equiv.swap v sourceFin * σ)
      rw [swapVertexLabels_eq_permute, h_graph_eq, ← AdjMatrix.permute_mul]

/-! ### Cell-wise characterization (the deep content) — STUB

The lemma below would state and (eventually) prove:

```
labelEdges_eq_permute_denseRanks:
  for tie-free `rks` (with `rks.size = n`),
  `labelEdgesAccordingToRankings rks G = G.permute (denseRanksPerm rks)`
```

where `denseRanksPerm rks` is the permutation induced by `computeDenseRanks rks`. This
is the foundation Phase 3 (and through it, Phase 5) needs.

**Proof structure** (~200 lines of Lean):

  1. Show `computeDenseRanks_lt_n_when_tieFree`: under tie-freeness, all output values
     are in `[0, n)`. (Sort positions are in this range; `set!` writes them at vertex
     indices.)

  2. Show `computeDenseRanks_injective_when_tieFree`: the output is injective on
     `Fin n` (different vertices get different positions, since their lex pairs are
     distinct under tie-freeness).

  3. Define `denseRanksPerm rks : Equiv.Perm (Fin n)` from the bijective dense-rank
     map. (Uses `Function.Injective.bijOn_image_iff` or similar Mathlib infrastructure.)

  4. **Fold induction.** State the invariant on the `labelEdgesAccordingToRankings`
     fold parameterized by a list `vs : List (Fin n)`:

     ```
     invariant: ∃ σ : Equiv.Perm (Fin n),
       (foldl ... acc).1 = acc.1.permute σ AND
       (foldl ... acc).2 = (acc.2 viewed via σ⁻¹)
     ```

     (Strengthens `labelEdgesAccordingToRankings_isomorphic` to track the specific σ.)

  5. At `vs = List.finRange n` and `acc = (G, denseRanks)`, the cumulative σ from the
     fold equals `denseRanksPerm rks` (under tie-freeness, by the selection-sort
     characterization).

  6. Combine: `labelEdgesAccordingToRankings rks G = G.permute (denseRanksPerm rks)`.

The proof is mechanically tractable but tedious. Each iteration of the fold's
`some sourceFin` branch composes one swap into σ; the `none` branch leaves σ unchanged.
Tracking σ through the foldl with a `genrelize` + `induction` pattern (as in
`labelEdgesAccordingToRankings_isomorphic`) is direct.
-/

/-- **Cell-wise characterization of labelEdges (under tie-freeness)** — STATED ONLY.

For tie-free `rks` (each vertex has a distinct rank value), `labelEdgesAccordingToRankings`
applied to `(rks, G)` produces `G.permute σ` for a specific `σ` — namely the permutation
that places each vertex at its dense-rank position.

The closing of this characterization is the main technical work for Phase 3. With it,
Phase 3's `labelEdges_VtsInvariant_eq_distinct` follows by ~50 lines of algebra
(τ-shifted denseRanks + `τ ∈ Aut G ⟹ G.permute τ = G`).

**Proof status:** stated; deep content pending. -/
theorem labelEdges_adj_eq_at_canonical_position
    (G : AdjMatrix n) (rks : Array VertexType) (h_size : rks.size = n)
    (h_distinct : ∀ i j : Fin n, rks.getD i.val 0 = rks.getD j.val 0 → i = j)
    (i j : Fin n) :
    ∃ φ : Fin n → Fin n,
      Function.Bijective φ ∧
      (labelEdgesAccordingToRankings rks G).adj i j = G.adj (φ i) (φ j) := by
  -- TODO: implement the cell-wise characterization. φ is `vertexAtRank rks` (inverse of
  -- the dense-rank map). The proof goes through the fold induction outlined above.
  sorry

end Graph
