import FullCorrectness.Equivariance.RunFromRelational

/-!
# Phase 6 — `run_isomorphic_eq_new` (notes on the proof path)
  (`FullCorrectness.Equivariance.MainRelationalNotes`)

The `(⟹)` direction of `run_canonical`, currently a sorry in `Main.lean`. Given
`h : G ≃ H`, by §2 obtain σ with `H = G.permute σ`. Goal:
`run 0 G = run 0 H`.

## What's needed (beyond the existing Phase 1–5 lifts)

Phase 1's Stage B-rel is stated for **σ ∈ Aut G**. Phase 2's Stage C-rel similarly. To
prove `run_isomorphic_eq_new`, the pipeline must be σ-equivariant for an *arbitrary*
σ : Equiv.Perm (Fin n) (because in general `G ≃ H` gives a σ that takes G to H, not σ
that fixes G).

The needed generalization:

  * **Stage A (already general):** `initializePaths (G.permute σ) = (initializePaths G).permute σ`
    holds for ANY σ. ✓ (No change needed; this is `initializePaths_Aut_equivariant`'s
    actually-general form.)

  * **Stage B-rel-fully-general:**
    ```
    calculatePathRankings ((initializePaths G).permute σ) (σ · vts)
      = RankState.permute σ (calculatePathRankings (initializePaths G) vts)
    ```
    for any σ. The σ ∈ Aut G version is closed (`calculatePathRankings_Aut_equivariant`
    in `PathEquivariance.lean`); the general version requires a re-derivation that does
    not rely on `PathState.permute σ (initializePaths G) = initializePaths G` (which
    only holds for σ ∈ Aut G).

  * **Stage C-rel-fully-general:** convergeLoop on a permuted state + shifted vts gives
    the σ-permuted output. Direct corollary of the generalized Stage B.

  * **Stage D (already trivially-general for matched G):** `labelEdgesAccordingToRankings vts H = labelEdgesAccordingToRankings vts G`
    for σ ∈ Aut G (since `G.permute σ = G`). The general version where `G ≠ H = G.permute σ`
    requires the same cell-wise characterization of `labelEdgesAccordingToRankings` from
    Phase 3, applied across two different graphs related by σ.

## Why `zeros` simplifies things

The input `zeros := Array.replicate n 0` is **trivially σ-invariant for any σ**:
`(σ · zeros).getD w 0 = zeros.getD (σ⁻¹ w) 0 = 0 = zeros.getD w 0`.

So the σ-shifted vts is just `zeros` again. This means we don't need the full
relational form — we just need:

  * `calculatePathRankings ((initializePaths G).permute σ) zeros
       = RankState.permute σ (calculatePathRankings (initializePaths G) zeros)`

for any σ.

## Proof sketch under the generalized stages

  1. By §2: H = G.permute σ for some σ.
  2. `initializePaths H = (initializePaths G).permute σ` (Stage A, general).
  3. `convergeLoop (initializePaths H) zeros n = (convergeLoop (initializePaths G) zeros n) shifted by σ`
     (Stage C, general, with zeros σ-invariant).
  4. After the full breakTie loop, the orderedRanks for H is the σ-shift of the
     orderedRanks for G — modulo the tiebreak choices (handled via §6 / Phase 5's
     `tiebreak_choice_independent`).
  5. `labelEdges orderedRanks_H H = labelEdges (σ-shifted orderedRanks_G) (G.permute σ)
       = labelEdges orderedRanks_G G` (by the cell-wise characterization +
     `(G.permute σ) at adj (σ_OrderedRanks⁻¹ i) (σ_OrderedRanks⁻¹ j) = G.adj (...) (...)`).

Step 5 is essentially Stage D-rel where the τ does NOT need to be in Aut G — instead
it's the σ from the isomorphism, which takes G to H.

## Status

This file documents the proof plan; no new lemmas are landed here. Phase 6's actual
closure requires:

  1. The Phase 3 deep characterization (cell-wise form of `labelEdgesAccordingToRankings`).
  2. Generalizing Phase 1's Stage B-rel to drop the σ ∈ Aut G hypothesis.
  3. Generalizing Phase 2's Stage C-rel similarly.
  4. Assembling in `Main.lean`'s `run_isomorphic_eq_new` proof body.

Estimated additional ~400-600 lines of Lean for the generalized stages, plus the
Phase 3 characterization itself (~300 lines).

The original sorry in `Main.lean` line 70 remains in place pending this work.
-/

namespace Graph

variable {n : Nat}

/-- A trivial fact used in Phase 6's argument: `Array.replicate n 0` is invariant under
any permutation σ of indices. -/
theorem zeros_σ_invariant (σ : Equiv.Perm (Fin n)) :
    ∀ w : Fin n, (Array.replicate n (0 : VertexType)).getD w.val 0
                = (Array.replicate n (0 : VertexType)).getD (σ⁻¹ w).val 0 := by
  intro w
  simp [w.isLt]

end Graph
