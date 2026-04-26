import FullCorrectness.Equivariance.ConvergeLoopRelational

/-!
# Phase 3 — Stage D-rel: `labelEdgesAccordingToRankings` τ-equivariance under tie-freeness
  (`FullCorrectness.Equivariance.StageDRelational`)

The relational lift of Stage D specialized to all-distinct ranks (the post-`orderVertices`
invariant from §7). Statement:

  τ ∈ Aut G  ∧  rks₁, rks₂ τ-related (rks₂[w] = rks₁[τ⁻¹ w])  ∧  rks₁, rks₂ tie-free
  ⟹  labelEdgesAccordingToRankings rks₂ G = labelEdgesAccordingToRankings rks₁ G

## Why tie-freeness matters

`computeDenseRanks` uses `(rank, vertex-index)` lex order. Under τ-relabeling of the
rks array, the secondary `vertex-index` key gets τ-permuted, and in general the
canonical position assignment is no longer τ-equivariant. Tie-freeness collapses the
secondary key (no ties to break), so dense ranks are determined by primary rank alone,
and hence are τ-related cleanly.

## Proof strategy (cell-wise characterization)

The deep content is: under tie-freeness, `labelEdgesAccordingToRankings rks G` equals
`G.permute (rankPerm rks)`, where `rankPerm rks : Equiv.Perm (Fin n)` is the permutation
sending each vertex `v` to its dense-rank position. The swap-based fold computes this
permutation incrementally via a sequence of selection-sort swaps.

Once this characterization is in place, Stage D-rel follows easily:
- For τ-related tie-free `rks₁, rks₂`: `rankPerm rks₂ = rankPerm rks₁ ∘ τ⁻¹`.
- `G.permute (rankPerm rks₁ ∘ τ⁻¹) = (G.permute τ⁻¹).permute (rankPerm rks₁)
                                    = G.permute (rankPerm rks₁)` (since τ⁻¹ ∈ Aut G).
- So `labelEdges rks₂ G = labelEdges rks₁ G`. ∎

The cell-wise characterization is captured by the lemma
`labelEdges_eq_permute_via_denseRanks` below; its proof is by induction on the swap
fold, maintaining the invariant `(graph_k, rankMap_k) = (G.permute σ_k, rankMap_0 ∘ σ_k⁻¹)`
where `σ_k` is the composition of swaps performed up to step `k`.

**Status: structural skeleton only.** The deep `labelEdges_eq_permute_via_denseRanks`
lemma is left as a single `sorry` site, with the proof plan documented above. The Stage
D-rel theorem `labelEdges_VtsInvariant_eq_distinct` is fully derivable from this
characterization and is provided here as a black box for Phase 5.
-/

namespace Graph

variable {n : Nat}

/-! ### Tie-freeness predicate -/

/-- A typing array has all-distinct values up to size n. This is the post-`orderVertices`
invariant from §7 (`orderVertices_n_distinct_ranks`). -/
def TieFree (rks : Array VertexType) (n : Nat) : Prop :=
  ∀ i j : Fin n, rks.getD i.val 0 = rks.getD j.val 0 → i = j

/-- τ-related tie-free arrays: their dense ranks (and hence the canonical sort order)
shift uniformly by τ. This is the relational form used by Stage D-rel. -/
private def τRelatedRks (τ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType) : Prop :=
  ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0

/-! ### Stage D-rel: the main theorem (proof deferred to a single deep characterization) -/

/-- **Stage D-rel under tie-freeness.** Given τ ∈ Aut G and two τ-related tie-free
typing arrays `rks₁, rks₂`, `labelEdgesAccordingToRankings` produces equal canonical
matrices.

**Proof skeleton:**

  1. Show that for tie-free `rks`, `labelEdgesAccordingToRankings rks G = G.permute (rankPerm rks)`,
     where `rankPerm rks : Equiv.Perm (Fin n)` is the dense-rank permutation. This is
     the deep technical content; see `labelEdges_eq_permute_via_denseRanks` below.

  2. Show `rankPerm rks₂ = rankPerm rks₁ ∘ τ⁻¹` for τ-related tie-free `rks₁, rks₂`.

  3. Conclude `G.permute (rankPerm rks₂) = (G.permute τ⁻¹).permute (rankPerm rks₁)
                                         = G.permute (rankPerm rks₁)` (using τ⁻¹ ∈ Aut G).

The current implementation defers the entire proof through one `sorry` on the
characterization; the structure above is documentation. Phase 5 uses this theorem as a
black box. -/
theorem labelEdges_VtsInvariant_eq_distinct
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (_hτ : τ ∈ AdjMatrix.Aut G)
    (rks₁ rks₂ : Array VertexType)
    (_h_size₁ : rks₁.size = n) (_h_size₂ : rks₂.size = n)
    (_h_distinct₁ : TieFree rks₁ n) (_h_distinct₂ : TieFree rks₂ n)
    (_h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    labelEdgesAccordingToRankings rks₂ G = labelEdgesAccordingToRankings rks₁ G := by
  -- TODO Phase 3 deep characterization: see file docstring for the proof plan.
  -- The structural skeleton is in place; the cell-wise lemma
  -- `labelEdges_eq_permute_via_denseRanks` is the missing technical content.
  sorry

end Graph
