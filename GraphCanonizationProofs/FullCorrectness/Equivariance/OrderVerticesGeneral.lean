import FullCorrectness.Equivariance.ConvergeLoopGeneral
import FullCorrectness.Equivariance.RunFromRelational

/-!
# Phase 6 orderVertices σ-equivariance general σ (P6.C)
  (`FullCorrectness.Equivariance.OrderVerticesGeneral`)

The `orderVertices` outer foldl iterates `convergeLoop ∘ breakTie` over `0..n-1`.
For Phase 6, we need the σ-equivariance of the entire output for general σ.

Built atop:
  - P6.B (`convergeLoop_σ_equivariant_general`)
  - P6.U (`orderVertices_size_eq`, `getArrayRank_zeros_eq_zeros`) [✅ closed]
  - Phase 5 (`runFrom_VtsInvariant_eq_strong`) — the structurally-similar form
    requires σ ∈ Aut G; here we need a generalization tracking through the
    σ ∉ Aut G case.

## Status

`sorry`-blocked pending P6.B and the orbit-bridging argument adapted for general σ.

## Top-level statement
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-- **P6.C target — `orderVertices` σ-equivariance for general σ**.

The outer foldl over `0..n-1` of the `convergeLoop ∘ breakTie` body, applied to
σ-related inputs, gives σ-shifted outputs. For the Phase 6 application,
`vts₁ = vts₂ = Array.replicate n 0` (trivially σ-INV), but the lemma is stated
relationally for clarity.

Proof structure (following `runFrom_VtsInvariant_eq_strong` from Phase 5):
  - Outer induction on `m := n - s`, generalizing over σ.
  - Base case (s = n): empty foldl returns input vts; σ-shift relation given.
  - Inductive step Case 1 (`breakTieCount conv₁ s < 2`): `breakTie_noop` gives
    `arr_i' = conv_i`; IH at s+1 with same σ.
  - Inductive step Case 2 (`breakTieCount conv₁ s ≥ 2`): orbit-bridging argument.
    For Phase 6's specific case (σ a single transposition, vts = zeros), the
    orbit-completeness hypothesis (`OrbitCompleteAfterConv`) needs a general-σ
    form `OrbitCompleteAfterConv_general G σ`.

Estimated 80–150 lines if leveraging Phase 5's helpers; potentially less if the
orbit hypothesis can be discharged inline for the Phase 6 swap case. -/
theorem orderVertices_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (_h_size₁ : vts₁.size = n) (_h_size₂ : vts₂.size = n)
    (_hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    ∀ w : Fin n,
      (orderVertices (initializePaths (G.permute σ)) vts₂).getD w.val 0
      = (orderVertices (initializePaths G) vts₁).getD (σ⁻¹ w).val 0 := by
  sorry

/-- Specialization to the all-zeros input used by `run_swap_invariant_fwd`. -/
theorem orderVertices_σ_equivariant_general_zeros
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) :
    ∀ w : Fin n,
      (orderVertices (initializePaths (G.permute σ)) (Array.replicate n 0)).getD w.val 0
      = (orderVertices (initializePaths G) (Array.replicate n 0)).getD (σ⁻¹ w).val 0 := by
  apply orderVertices_σ_equivariant_general
  · exact Array.size_replicate
  · exact Array.size_replicate
  · -- zeros σ-invariance: every entry of `Array.replicate n 0` is 0.
    intro v
    simp [(σ v).isLt, v.isLt]

end Graph
