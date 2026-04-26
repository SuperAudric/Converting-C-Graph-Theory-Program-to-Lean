import FullCorrectness.Equivariance.PathEquivarianceRelational
import FullCorrectness.Equivariance.ConvergeLoop

/-!
# Stage C-rel — `convergeOnce`/`convergeLoop` τ-equivariance  (`FullCorrectness.Equivariance.ConvergeLoopRelational`)

Lifts the `convergeOnce_Aut_invariant` / `convergeLoop_Aut_invariant` σ-invariance
results to the relational form needed by `runFrom_VtsInvariant_eq`:

  τ ∈ Aut G, arr₁, arr₂ τ-related ⟹ convergeOnce/convergeLoop on arr₂ matches
  convergeOnce/convergeLoop on arr₁ at τ⁻¹-shifted positions.

The σ-INV form is recovered as the diagonal special case `arr₁ = arr₂`. The proof
threads through `convergeOnce_writeback` and Phase 1's
`calculatePathRankings_σ_equivariant_relational`.
-/

namespace Graph

variable {n : Nat}

/-! ### Helpers: `convergeOnce`/`convergeLoop` fixed-point behavior

These technical lemmas ride on the structure of `convergeOnce` and `convergeLoop` to
let the relational induction collapse the case where the `changed` flag differs between
the two parallel computations. They are NOT relational themselves — they hold for any
single computation. -/

/-- The fold body of `convergeOnce` preserves the invariant: if the flag is `false`, the
type array is unchanged from the input. -/
private theorem convergeOnce_fold_unchanged_when_not_flag (rs : RankState) (vc : Nat)
    (vts : Array VertexType) :
    ∀ (l : List Nat) (start : Array VertexType × Bool),
      (start.2 = false → start.1 = vts) →
      (l.foldl (fun (pair : Array VertexType × Bool) (vertexIdx : Nat) =>
          let (typeArray, changed) := pair
          let newRank := rs.getFrom (vc - 1) vertexIdx
          if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
          else (typeArray, changed)) start).2 = false →
        (l.foldl (fun (pair : Array VertexType × Bool) (vertexIdx : Nat) =>
            let (typeArray, changed) := pair
            let newRank := rs.getFrom (vc - 1) vertexIdx
            if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
            else (typeArray, changed)) start).1 = vts
  | [], start, h_init, h_flag => h_init h_flag
  | x :: xs, start, h_init, h_flag => by
      rw [List.foldl_cons] at h_flag ⊢
      apply convergeOnce_fold_unchanged_when_not_flag rs vc vts xs _ ?_ h_flag
      -- New invariant: post-step flag = false → post-step array = vts.
      intro h_step_flag
      obtain ⟨arr, b⟩ := start
      simp only [] at h_step_flag ⊢
      by_cases h_cond : (rs.getFrom (vc - 1) x != arr.getD x 0) = true
      · rw [if_pos h_cond] at h_step_flag ⊢
        exact absurd h_step_flag (by simp)
      · rw [if_neg h_cond] at h_step_flag ⊢
        exact h_init h_step_flag

/-- If `convergeOnce`'s flag is `false`, the output array equals the input array. -/
theorem convergeOnce_unchanged_when_not_flag {vc : Nat}
    (state : PathState vc) (vts : Array VertexType) :
    (convergeOnce state vts).2 = false → (convergeOnce state vts).1 = vts := by
  intro h_flag
  unfold convergeOnce at h_flag ⊢
  apply convergeOnce_fold_unchanged_when_not_flag _ vc vts (List.range vc) (vts, false) _ h_flag
  intro _; rfl

/-- If `convergeOnce`'s flag is `false`, then `convergeLoop` is the identity at every
fuel level (the loop has reached a fixed point at `vts`). -/
theorem convergeLoop_unchanged_fixedpoint {vc : Nat}
    (state : PathState vc) (vts : Array VertexType) (fuel : Nat) :
    (convergeOnce state vts).2 = false → convergeLoop state vts fuel = vts := by
  intro h_flag
  induction fuel with
  | zero => rfl
  | succ k _ =>
    -- convergeLoop state vts (k+1) = if .2 then convergeLoop state .1 k else .1.
    -- Given .2 = false, take else branch giving .1 = vts (by Helper 1).
    change (if (convergeOnce state vts).2
            then convergeLoop state (convergeOnce state vts).1 k
            else (convergeOnce state vts).1) = vts
    rw [if_neg (by rw [h_flag]; decide)]
    exact convergeOnce_unchanged_when_not_flag state vts h_flag

/-- Universal lemma: `convergeLoop state vts (k+1)` always equals
`convergeLoop state (convergeOnce state vts).1 k`, regardless of the flag. The proof
case-splits on the flag and uses `convergeLoop_unchanged_fixedpoint` in the false case. -/
theorem convergeLoop_succ_eq_loop_of_once {vc : Nat}
    (state : PathState vc) (vts : Array VertexType) (k : Nat) :
    convergeLoop state vts (k + 1) = convergeLoop state (convergeOnce state vts).1 k := by
  change (if (convergeOnce state vts).2
          then convergeLoop state (convergeOnce state vts).1 k
          else (convergeOnce state vts).1)
        = convergeLoop state (convergeOnce state vts).1 k
  by_cases h_flag : (convergeOnce state vts).2 = true
  · rw [if_pos h_flag]
  · have h_false : (convergeOnce state vts).2 = false := by
      cases h : (convergeOnce state vts).2
      · rfl
      · exact absurd h h_flag
    rw [if_neg (by rw [h_false]; decide)]
    -- Need: (convergeOnce state vts).1 = convergeLoop state (convergeOnce state vts).1 k.
    rw [convergeOnce_unchanged_when_not_flag state vts h_false]
    exact (convergeLoop_unchanged_fixedpoint state vts k h_false).symm

/-! ### `getFrom` τ-relatedness from Stage B-rel -/

/-- Relational analogue of `calculatePathRankings_getFrom_invariant`: for σ-related
typing arrays, the `getFrom (n-1)` values on the second computation equal the values on
the first computation at σ⁻¹-shifted positions. -/
theorem calculatePathRankings_getFrom_VtsInvariant_eq
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ AdjMatrix.Aut G)
    (vts₁ vts₂ : Array VertexType)
    (hvts_rel : ∀ v : Fin n, vts₂.getD (σ v) 0 = vts₁.getD v 0) (w : Fin n) :
    (calculatePathRankings (initializePaths G) vts₂).getFrom (n - 1) w.val =
      (calculatePathRankings (initializePaths G) vts₁).getFrom (n - 1) (σ⁻¹ w).val := by
  cases n with
  | zero => exact w.elim0
  | succ k =>
    have hd : k + 1 - 1 < k + 1 := by omega
    obtain ⟨h_from_rel, _⟩ :=
      calculatePathRankings_σ_equivariant_relational G σ hσ vts₁ vts₂ hvts_rel
    show (((calculatePathRankings (initializePaths G) vts₂).fromRanks.getD (k + 1 - 1) #[]).getD w.val 0)
       = (((calculatePathRankings (initializePaths G) vts₁).fromRanks.getD (k + 1 - 1) #[]).getD (σ⁻¹ w).val 0)
    exact h_from_rel (k + 1 - 1) hd w

/-! ### Stage C-rel: `convergeOnce` and `convergeLoop` τ-equivariance -/

/-- One `convergeOnce` step on τ-related typing arrays produces τ-related outputs:
the value at slot `w` in the output on `vts₂` equals the value at slot `τ⁻¹ w` in the
output on `vts₁`. Relational analogue of `convergeOnce_Aut_invariant`. -/
theorem convergeOnce_VtsInvariant_eq
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ AdjMatrix.Aut G)
    (vts₁ vts₂ : Array VertexType)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (convergeOnce (initializePaths G) vts₂).1.getD w.val 0
      = (convergeOnce (initializePaths G) vts₁).1.getD (τ⁻¹ w).val 0 := by
  intro w
  -- Reformulate h_rel into Stage B-rel's form (vts₂[(τ v)] = vts₁[v]).
  have hvts_rel : ∀ v : Fin n, vts₂.getD (τ v) 0 = vts₁.getD v 0 := by
    intro v
    have h := h_rel (τ v)
    have h_inv : τ⁻¹ (τ v) = v := by simp
    rw [h_inv] at h
    exact h
  have hw_size : w.val < vts₂.size := h_size₂ ▸ w.isLt
  have hτw_size : (τ⁻¹ w).val < vts₁.size := h_size₁ ▸ (τ⁻¹ w).isLt
  rw [convergeOnce_writeback (initializePaths G) vts₂ w.val hw_size w.isLt,
      convergeOnce_writeback (initializePaths G) vts₁ (τ⁻¹ w).val hτw_size (τ⁻¹ w).isLt]
  exact calculatePathRankings_getFrom_VtsInvariant_eq G τ hτ vts₁ vts₂ hvts_rel w

/-- The full `convergeLoop` preserves τ-relatedness: starting from τ-related arrays, the
output is τ-related at every fuel level. Relational analogue of
`convergeLoop_Aut_invariant`. -/
theorem convergeLoop_VtsInvariant_eq
    (G : AdjMatrix n) (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ AdjMatrix.Aut G)
    (vts₁ vts₂ : Array VertexType) (fuel : Nat)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (convergeLoop (initializePaths G) vts₂ fuel).getD w.val 0
      = (convergeLoop (initializePaths G) vts₁ fuel).getD (τ⁻¹ w).val 0 := by
  induction fuel generalizing vts₁ vts₂ with
  | zero =>
    intro w
    show vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0
    exact h_rel w
  | succ k ih =>
    intro w
    -- Use convergeLoop_succ_eq_loop_of_once on both sides to collapse the if-flag asymmetry.
    rw [convergeLoop_succ_eq_loop_of_once (initializePaths G) vts₁ k,
        convergeLoop_succ_eq_loop_of_once (initializePaths G) vts₂ k]
    -- Now both sides loop k times on (convergeOnce ...).1, which is τ-related.
    have hStep_size₁ : (convergeOnce (initializePaths G) vts₁).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₁
    have hStep_size₂ : (convergeOnce (initializePaths G) vts₂).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₂
    have hStep := convergeOnce_VtsInvariant_eq G τ hτ vts₁ vts₂ h_size₁ h_size₂ h_rel
    exact ih (convergeOnce (initializePaths G) vts₁).1
              (convergeOnce (initializePaths G) vts₂).1
              hStep_size₁ hStep_size₂ hStep w

end Graph
