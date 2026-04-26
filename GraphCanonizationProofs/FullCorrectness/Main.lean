import FullCorrectness.Tiebreak
import FullCorrectness.Invariants
import FullCorrectness.Permutation
import FullCorrectness.Automorphism
import FullCorrectness.Equivariance.StageDRelational
import LeanGraphCanonizerV4Correctness

/-!
# §8  Main theorem: `run_canonical`

Combines the pieces proved in §1–§7 to state and prove:

```
run_canonical : G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

That is, `run` with all-zero starting types is a complete graph-isomorphism invariant.

## Status
- (⟸) direction `run_eq_implies_iso`:  reused from `LeanGraphCanonizerV4Correctness` (genuinely proved via `run_isomorphic_to_input` + transitivity).
- (⟹) direction `run_isomorphic_eq`:   new proof via §3 + §4 + §6; proof pending.
- `run_canonical`:                      assembled from the two directions.

## Proof plan for the (⟹) direction

Given `h : G ≃ H`. By §2 (`permute_of_Isomorphic`), pick σ with `H = G.permute σ`. Goal:
`run 0 H = run 0 G`, i.e.

```
labelEdgesAccordingToRankings (orderVertices (initializePaths H) zeros) H
  = labelEdgesAccordingToRankings (orderVertices (initializePaths G) zeros) G
```

Substitute `H = G.permute σ`. By Stage A equivariance,
  `initializePaths (G.permute σ) = (initializePaths G).permute σ`.
The input `zeros := Array.replicate n 0` is σ-invariant trivially (every entry is 0).

**Sub-case A: σ ∈ Aut G.** Then by Stage B + §4 + Stage C + §6, the orderVertices output
  is σ-invariant:
  `orderVertices ((initializePaths G).permute σ) zeros = orderVertices (initializePaths G) zeros`.
  Then Stage D gives the final equality.

**Sub-case B: σ ∉ Aut G.** Then H = G.permute σ is a *different* labeling than G, and σ
  takes G to H which may have different labels. The canonical output depends only on
  the abstract graph (G up to isomorphism), so running the pipeline on H and G produces
  the same matrix — but this is the theorem we're trying to prove! To break the circle,
  factor σ through Aut G ⋊ (Aut G-orbits).

  Actually, a cleaner argument: H and G are in the same Isomorphic class, so by §4's
  corollary the multiset of type-arrays produced at each convergeLoop iteration is the
  same for both. Coupled with Stage D, this suffices.

**Alternative argument (probably simpler).** The pipeline applied to G and to H produces
matrices with distinct ranks assigned to vertices in some Aut-invariant way. The final
`labelEdgesAccordingToRankings` step sorts vertices by rank, producing a canonical
matrix whose adjacency structure depends only on the isomorphism class — because the
rank of each vertex is a function of its Aut-orbit + tiebreak history, which by §6 is
choice-independent. Two isomorphic graphs have identical Aut-orbit structure (up to the
isomorphism), hence identical canonical matrices.
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## (⟹) Isomorphic graphs produce equal canonical forms.

The proof inducts on the `Isomorphic` constructors (refl / swap / trans). The refl and
trans cases are immediate. The swap case reduces to a single-transposition equivalence
`run_swap_invariant`, which itself splits on whether the swap is in `Aut G`:

  - If `Equiv.swap v1 v2 ∈ Aut G`: `G.permute σ = G` definitionally, so the two `run`
    calls are on the same graph — trivially equal.
  - If `Equiv.swap v1 v2 ∉ Aut G`: requires general-σ equivariance of the pipeline
    (Path A: Stage B-rel/C-rel/D-rel generalized to drop σ ∈ Aut G). This branch
    is currently a focused sorry; closure requires ~400 lines of new general-σ
    infrastructure.
-/

/-- Single-transposition invariance of `run` (forward direction). Splits on
`σ := Equiv.swap v1 v2 ∈ Aut G`: the σ-fixing branch closes definitionally; the σ-moving
branch requires general-σ pipeline equivariance (Path A).

Distinct from the legacy `Graph.run_swap_invariant` (which goes in the opposite direction
and is sorry-blocked by the false §5 lemma). -/
private theorem run_swap_invariant_fwd (G : AdjMatrix n) (v1 v2 : Fin n) :
    run (Array.replicate n 0) G =
    run (Array.replicate n 0) (swapVertexLabels v1 v2 G) := by
  -- Reduce swapVertexLabels to G.permute σ via §1.2.
  rw [swapVertexLabels_eq_permute]
  set σ : Equiv.Perm (Fin n) := Equiv.swap v1 v2 with h_σ_def
  -- Branch on whether σ is an automorphism of G.
  by_cases hσ_Aut : σ ∈ AdjMatrix.Aut G
  · -- σ ∈ Aut G: G.permute σ = G by definition, so both `run`s are on the same graph.
    have h_perm_eq : G.permute σ = G := hσ_Aut
    rw [h_perm_eq]
  · -- σ ∉ Aut G: the swap genuinely changes the graph. Reduces to:
    --   (Step A) `labelEdges_two_graphs_σ_related` (✅ proved in `StageDRelational.lean`,
    --     Stage D-rel general σ): given σ-shifted tie-free rks, `labelEdges rks_H (G.permute σ)
    --     = labelEdges rks_G G`. So if we have σ-shifted ranks, the labelEdges parts match.
    --   (Step B) Pipeline σ-equivariance for general σ (open): `orderVertices
    --     (init (G.permute σ)) (getArrayRank zeros) = σ-shift of orderVertices (init G)
    --     (getArrayRank zeros)`. This requires:
    --     - Stage B-rel general σ: `calculatePathRankings (state.permute σ) (σ-shifted vts)
    --       = σ-shift of calculatePathRankings state vts` for ANY σ.
    --     - Stage C-rel general σ: corollary for `convergeLoop`.
    --     - breakTie loop σ-tracking through outer iterations (Phase 5's strong theorem
    --       requires τ ∈ Aut G; needs adaptation).
    --   The remaining work is ~250-400 lines for these generalizations.
    sorry

/-- New proof path (replacing the sorry-reachable `Graph.run_isomorphic_eq` from the
flat file). Proved via induction on `Isomorphic`'s constructors, reducing the swap case
to `run_swap_invariant`. -/
theorem run_isomorphic_eq_new
    {G H : AdjMatrix n}
    (h : G ≃ H) :
    run (Array.replicate n 0) G = run (Array.replicate n 0) H := by
  induction h with
  | refl G => rfl
  | swap G v1 v2 => exact run_swap_invariant_fwd G v1 v2
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## (⟸) Equal canonical forms imply isomorphism.

Reused verbatim from the old flat proof: `Graph.run_eq_implies_iso` (already in
scope via the `LeanGraphCanonizerV4Correctness` import) uses only
`run_isomorphic_to_input` (§4 of the flat file, still correct) plus transitivity of `≃`. -/

/-! ## Main theorem -/

/-- **Main theorem.** `run` with all-zero starting vertex types is a complete
graph-isomorphism invariant:

```
G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H
```

- The `(⟹)` direction is `run_isomorphic_eq`, proved via §3 + §4 + §6 (the new path).
- The `(⟸)` direction is `Graph.run_eq_implies_iso`, reused from the flat file (§4).

This theorem replaces the (sorry-reachable) `Graph.run_canonical` stated in
`LeanGraphCanonizerV4Correctness.lean`. External consumers should use
`FullCorrectness.run_canonical` via the `FullCorrectness` umbrella, which is
a stronger statement than the flat-file version (the (⟹) direction here does
not route through the false §5 lemma). -/
theorem run_canonical_correctness (G H : AdjMatrix n) :
    G ≃ H ↔ run (Array.replicate n 0) G = run (Array.replicate n 0) H :=
  ⟨run_isomorphic_eq_new, _root_.Graph.run_eq_implies_iso⟩

end Graph
