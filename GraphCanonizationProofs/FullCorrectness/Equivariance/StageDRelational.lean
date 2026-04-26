import FullCorrectness.Equivariance.ConvergeLoopRelational
import FullCorrectness.Equivariance.LabelEdgesCharacterization

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

/-! ### Stage D-rel: the main theorem

With `LabelEdgesCharacterization`'s closed lemmas (`labelEdges_fold_strong` and
`labelEdges_terminal_rankMap_identity`), Stage D-rel reduces to two remaining facts:

  (P3.C) `computeDenseRanks_τ_shift_distinct`: for τ-related tie-free rks₁, rks₂,
         `computeDenseRanks rks₂ = computeDenseRanks rks₁ ∘ τ⁻¹` (in `getD` form).

  (P3.A') `computeDenseRanks_perm_when_tieFree`: for tie-free rks, the denseRanks
         output values are exactly `{0, 1, ..., n-1}` each appearing once (i.e.,
         the multiset condition needed by `labelEdges_terminal_rankMap_identity`).

These are the remaining sub-sorries. Both are arithmetic facts about computeDenseRanks
and the lex sort; their proofs are mechanical but tedious. -/

/-- **(P3.A')** Tie-free rks ⟹ each value in {0..n-1} is achieved by some vertex's
denseRanks. Foundational helper for using `labelEdges_terminal_rankMap_identity`. -/
theorem computeDenseRanks_perm_when_tieFree
    (rks : Array VertexType) (h_size : rks.size = n) (h_distinct : TieFree rks n) :
    ∀ k : Fin n, ∃ w : Fin n, (computeDenseRanks n rks).getD w.val 0 = k.val := by
  -- TODO P3.A': structural fact about computeDenseRanks under tie-freeness.
  -- The pairs list = [(rks[0], 0), ..., (rks[n-1], n-1)], all with distinct rks.
  -- The lex sort is determined by rks alone (no ties). The fold writes sortedIdx
  -- to position pairs[sortedIdx].2 = original vertex. So denseRanks output values
  -- are {0, ..., n-1} as a permutation.
  sorry

/-- **(P3.C)** τ-shift lemma: for τ-related tie-free rks₁, rks₂, the denseRanks
shift τ-equivariantly. -/
theorem computeDenseRanks_τ_shift_distinct
    (τ : Equiv.Perm (Fin n))
    (rks₁ rks₂ : Array VertexType)
    (h_size₁ : rks₁.size = n) (h_size₂ : rks₂.size = n)
    (h_distinct₁ : TieFree rks₁ n) (h_distinct₂ : TieFree rks₂ n)
    (h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (computeDenseRanks n rks₂).getD w.val 0 = (computeDenseRanks n rks₁).getD (τ⁻¹ w).val 0 := by
  -- TODO P3.C: the dense-rank position of w under rks₂ equals the dense-rank position
  -- of τ⁻¹ w under rks₁. Under tie-freeness, denseRanks rks[v] = #{u | rks[u] < rks[v]}.
  -- Apply this characterization + change of variables.
  sorry

/-- **Stage D-rel under tie-freeness.** Given τ ∈ Aut G and two τ-related tie-free
typing arrays `rks₁, rks₂`, `labelEdgesAccordingToRankings` produces equal canonical
matrices.

**Proof:**
  1. By `labelEdges_fold_strong` on side 1 (with σ := id, rankMap_0 := denseRanks rks₁),
     get σ_1 with output_1 = G.permute σ_1 and output_1.rankMap = denseRanks rks₁ ∘ σ_1⁻¹.
  2. Similarly on side 2 with σ := τ (using `τ ∈ Aut G ⟹ G = G.permute τ`),
     and rankMap_0 := denseRanks rks₁ (using P3.C: denseRanks rks₂ = denseRanks rks₁ ∘ τ⁻¹).
     Get σ_2 with output_2 = G.permute σ_2 and output_2.rankMap = denseRanks rks₁ ∘ σ_2⁻¹.
  3. Both terminal rankMaps are identity (by `labelEdges_terminal_rankMap_identity` with P3.A').
  4. So `denseRanks rks₁ ∘ σ_1⁻¹ = denseRanks rks₁ ∘ σ_2⁻¹` pointwise.
  5. By tie-freeness (injectivity of denseRanks rks₁), σ_1 = σ_2.
  6. Hence output_1 = output_2. ∎

The proof is fully closed once P3.A' and P3.C are filled in. -/
theorem labelEdges_VtsInvariant_eq_distinct
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (_hτ : τ ∈ AdjMatrix.Aut G)
    (rks₁ rks₂ : Array VertexType)
    (_h_size₁ : rks₁.size = n) (_h_size₂ : rks₂.size = n)
    (_h_distinct₁ : TieFree rks₁ n) (_h_distinct₂ : TieFree rks₂ n)
    (_h_rel : ∀ w : Fin n, rks₂.getD w.val 0 = rks₁.getD (τ⁻¹ w).val 0) :
    labelEdgesAccordingToRankings rks₂ G = labelEdgesAccordingToRankings rks₁ G := by
  -- TODO Phase 3.E: assemble the proof using `labelEdges_fold_strong` (closed),
  -- `labelEdges_terminal_rankMap_identity` (closed), `computeDenseRanks_perm_when_tieFree`
  -- (P3.A', stub), `computeDenseRanks_τ_shift_distinct` (P3.C, stub), and the algebra.
  sorry

end Graph
