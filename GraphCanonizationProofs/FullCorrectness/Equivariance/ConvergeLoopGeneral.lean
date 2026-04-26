import FullCorrectness.Equivariance.PathEquivarianceGeneral
import FullCorrectness.Equivariance.ConvergeLoopRelational

/-!
# Phase 6 Stage C-rel general σ (P6.B)
  (`FullCorrectness.Equivariance.ConvergeLoopGeneral`)

Generalizes `convergeOnce_VtsInvariant_eq` and `convergeLoop_VtsInvariant_eq` from
`ConvergeLoopRelational.lean` to drop the `σ ∈ Aut G` hypothesis. Direct corollary
of P6.A (`calculatePathRankings_σ_equivariant_general`).

## Status

`sorry`-blocked pending P6.A.

## Statement
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-- **P6.B target — `convergeOnce` σ-equivariance for general σ**.

Direct corollary of P6.A's general Stage B-rel. The `convergeOnce_writeback`
characterization gives `(convergeOnce state vts).1.getD w 0 = rs.getFrom (n-1) w` where
`rs = calculatePathRankings state vts`; combining with P6.A's σ-shift on
`fromRanks` gives the result. -/
theorem convergeOnce_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (_h_size₁ : vts₁.size = n) (_h_size₂ : vts₂.size = n)
    (_hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) :
    ∀ w : Fin n,
      (convergeOnce (initializePaths (G.permute σ)) vts₂).1.getD w.val 0
      = (convergeOnce (initializePaths G) vts₁).1.getD (σ⁻¹ w).val 0 := by
  sorry

/-- **P6.B target — `convergeLoop` σ-equivariance for general σ**.

Fuel induction on `convergeLoop`, using `convergeOnce_σ_equivariant_general` per step.
Mirrors the proof of `convergeLoop_VtsInvariant_eq` but with a different "second
graph" (`G.permute σ` instead of `G`).

Note: `convergeOnce` produces a `(updated, changed)` pair. Need to also show that
the `changed` flag is the same on both sides (since the loop branches on it). This
follows from the σ-shift relation and the size/prefix invariants. -/
theorem convergeLoop_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (_h_size₁ : vts₁.size = n) (_h_size₂ : vts₂.size = n)
    (_hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0)
    (_fuel : Nat) :
    ∀ w : Fin n,
      (convergeLoop (initializePaths (G.permute σ)) vts₂ _fuel).getD w.val 0
      = (convergeLoop (initializePaths G) vts₁ _fuel).getD (σ⁻¹ w).val 0 := by
  sorry

end Graph
