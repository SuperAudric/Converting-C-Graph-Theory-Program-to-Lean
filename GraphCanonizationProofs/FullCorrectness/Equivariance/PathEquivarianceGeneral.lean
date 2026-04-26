import FullCorrectness.Equivariance.PathEquivarianceRelational

/-!
# Phase 6 Stage B-rel general σ (P6.A)
  (`FullCorrectness.Equivariance.PathEquivarianceGeneral`)

The σ ∈ Aut G version of Stage B-rel (`calculatePathRankings_σ_equivariant_relational`)
in `PathEquivarianceRelational.lean` requires `PathState.permute σ state = state`.
Phase 6's `run_swap_invariant_fwd` (σ ∉ Aut G branch) needs the general form, where
the second `calculatePathRankings` call runs on `PathState.permute σ state` (a
different state from the first call's `state`).

## Status

This file declares the **target signatures** for the general-σ relational stages.
All proofs are currently `sorry`-blocked. Implementation is the substantive content
of P6.A (~150-200 lines of Lean).

The signatures are designed so that the σ ∈ Aut G existing proofs are recovered as
the special case `state₂ = state₁` (i.e., `PathState.permute σ state = state`).

## Foundational lemma signatures

  - `pathsAtDepth_two_states_perm` 🟦 — `pathsAtDepth state₂` is a Perm of
    `(pathsAtDepth state₁).map (PathsFrom.permute σ)` whenever
    `state₂ = PathState.permute σ state₁`. (Direct from `PathState.permute`'s
    definition: it maps each PathsFrom through `PathsFrom.permute σ`, then re-indexes
    by σ⁻¹. Hence the resulting list, viewed as a multiset, equals
    `(pathsAtDepth state₁).map (PathsFrom.permute σ)`.)

  - `allBetween_two_states_perm` 🟦 — corollary via `flatMap`.

  - `mem_allBetween_two_states_under_f` 🟦 — pointwise version: if
    `q ∈ allBetween state₁` then `PathsBetween.permute σ q ∈ allBetween state₂`.

  - `between_assignList_σ_rank_general` 🟦 — generalizes
    `between_assignList_σ_rank_rel` to two states.

  - `from_assignList_σ_rank_general` 🟦 — generalizes `from_assignList_σ_rank_rel`.

  - `calculatePathRankings_body_preserves_general` 🟦 — body-step lemma.

  - `calculatePathRankings_σ_cell_general_facts` 🟦 — foldl induction.

  - `calculatePathRankings_σ_equivariant_general` 🟦 — final assembly.

## Top-level statement (P6.A target)
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-- **Stage B-rel general σ (P6.A target)**: relational σ-equivariance of
`calculatePathRankings` for an *arbitrary* `σ : Equiv.Perm (Fin n)` — no `σ ∈ Aut G`
hypothesis.

Compared to `calculatePathRankings_σ_equivariant_relational` (σ ∈ Aut G), the second
`calculatePathRankings` call runs on `initializePaths (G.permute σ) =
PathState.permute σ (initializePaths G)` (via `initializePaths_Aut_equivariant`,
which is fully general despite its name). This is genuinely a different state when
σ ∉ Aut G; the σ ∈ Aut G case collapses both sides to `initializePaths G`. -/
theorem calculatePathRankings_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (_hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    let rs₁ := calculatePathRankings (initializePaths G) vts₁
    let rs₂ := calculatePathRankings (initializePaths (G.permute σ)) vts₂
    (∀ d : Nat, d < n → ∀ s : Fin n,
        (rs₂.fromRanks.getD d #[]).getD s.val 0
        = (rs₁.fromRanks.getD d #[]).getD (σ⁻¹ s).val 0) ∧
    (∀ d : Nat, d < n → ∀ s e : Fin n,
        ((rs₂.betweenRanks.getD d #[]).getD s.val #[]).getD e.val 0
        = ((rs₁.betweenRanks.getD d #[]).getD (σ⁻¹ s).val #[]).getD (σ⁻¹ e).val 0) := by
  sorry

end Graph
