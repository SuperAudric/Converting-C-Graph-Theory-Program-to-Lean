import FullCorrectness.Equivariance.PathEquivarianceGeneral
import FullCorrectness.Equivariance.ConvergeLoopRelational

/-!
# Phase 6 Stage C-rel general σ (P6.B)
  (`FullCorrectness.Equivariance.ConvergeLoopGeneral`)

Generalizes `convergeOnce_VtsInvariant_eq` and `convergeLoop_VtsInvariant_eq` from
`ConvergeLoopRelational.lean` to drop the `σ ∈ Aut G` hypothesis. Direct corollary
of P6.A (`calculatePathRankings_σ_equivariant_general`) via `convergeOnce_writeback`.

The two sides run on `initializePaths G` and `initializePaths (G.permute σ)` respectively;
their outputs are σ-related (i.e., shifted by σ⁻¹).

## Status

✅ closed.
-/

namespace Graph

variable {n : Nat}

/-- Relational analogue of `calculatePathRankings_getFrom_VtsInvariant_eq` for general σ.
The two computations run on different states (`initializePaths G` vs
`initializePaths (G.permute σ)`); the `getFrom (n-1)` values on side 2 are σ-shifts of
those on side 1. -/
private theorem calculatePathRankings_getFrom_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0) (w : Fin n) :
    (calculatePathRankings (initializePaths (G.permute σ)) vts₂).getFrom (n - 1) w.val =
      (calculatePathRankings (initializePaths G) vts₁).getFrom (n - 1) (σ⁻¹ w).val := by
  cases n with
  | zero => exact w.elim0
  | succ k =>
    have hd : k + 1 - 1 < k + 1 := by omega
    obtain ⟨h_from_rel, _⟩ :=
      calculatePathRankings_σ_equivariant_general G σ vts₁ vts₂ hvts_rel
    show (((calculatePathRankings (initializePaths (G.permute σ)) vts₂).fromRanks.getD (k + 1 - 1) #[]).getD w.val 0)
       = (((calculatePathRankings (initializePaths G) vts₁).fromRanks.getD (k + 1 - 1) #[]).getD (σ⁻¹ w).val 0)
    exact h_from_rel (k + 1 - 1) hd w

/-- **P6.B — `convergeOnce` σ-equivariance for general σ**.

Direct corollary of P6.A's general Stage B-rel: the value at slot `w` in
`convergeOnce` on `(initializePaths (G.permute σ), vts₂)` equals the value at slot
`σ⁻¹ w` in `convergeOnce` on `(initializePaths G, vts₁)`. -/
theorem convergeOnce_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (σ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (convergeOnce (initializePaths (G.permute σ)) vts₂).1.getD w.val 0
      = (convergeOnce (initializePaths G) vts₁).1.getD (σ⁻¹ w).val 0 := by
  intro w
  -- Reformulate h_rel into Stage B-rel-general's form (vts₂[(σ v)] = vts₁[v]).
  have hvts_rel : ∀ v : Fin n, vts₂.getD (σ v).val 0 = vts₁.getD v.val 0 := by
    intro v
    have h := h_rel (σ v)
    have h_inv : σ⁻¹ (σ v) = v := by simp
    rw [h_inv] at h
    exact h
  have hw_size : w.val < vts₂.size := h_size₂ ▸ w.isLt
  have hσw_size : (σ⁻¹ w).val < vts₁.size := h_size₁ ▸ (σ⁻¹ w).isLt
  rw [convergeOnce_writeback (initializePaths (G.permute σ)) vts₂ w.val hw_size w.isLt,
      convergeOnce_writeback (initializePaths G) vts₁ (σ⁻¹ w).val hσw_size (σ⁻¹ w).isLt]
  exact calculatePathRankings_getFrom_σ_equivariant_general G σ vts₁ vts₂ hvts_rel w

/-- **P6.B — `convergeLoop` σ-equivariance for general σ**.

Fuel induction using `convergeOnce_σ_equivariant_general` per step. The two sides may
take their `if changed` branches asymmetrically; we collapse this via
`convergeLoop_succ_eq_loop_of_once` (which holds for any state independently).

Mirrors `convergeLoop_VtsInvariant_eq`'s proof structure. -/
theorem convergeLoop_σ_equivariant_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType) (fuel : Nat)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (σ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (convergeLoop (initializePaths (G.permute σ)) vts₂ fuel).getD w.val 0
      = (convergeLoop (initializePaths G) vts₁ fuel).getD (σ⁻¹ w).val 0 := by
  induction fuel generalizing vts₁ vts₂ with
  | zero =>
    intro w
    show vts₂.getD w.val 0 = vts₁.getD (σ⁻¹ w).val 0
    exact h_rel w
  | succ k ih =>
    intro w
    rw [convergeLoop_succ_eq_loop_of_once (initializePaths G) vts₁ k,
        convergeLoop_succ_eq_loop_of_once (initializePaths (G.permute σ)) vts₂ k]
    -- Both sides now loop k times on (convergeOnce ...).1, which is σ-related.
    have hStep_size₁ : (convergeOnce (initializePaths G) vts₁).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₁
    have hStep_size₂ : (convergeOnce (initializePaths (G.permute σ)) vts₂).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₂
    have hStep := convergeOnce_σ_equivariant_general G σ vts₁ vts₂ h_size₁ h_size₂ h_rel
    exact ih (convergeOnce (initializePaths G) vts₁).1
              (convergeOnce (initializePaths (G.permute σ)) vts₂).1
              hStep_size₁ hStep_size₂ hStep w

end Graph
