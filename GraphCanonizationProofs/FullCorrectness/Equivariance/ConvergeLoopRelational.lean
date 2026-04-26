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
  -- Cases on n: n = 0 is impossible (w : Fin 0); n ≥ 1 via Phase 1's cell-rel facts.
  cases n with
  | zero => exact w.elim0
  | succ k =>
    have hd : k + 1 - 1 < k + 1 := by omega
    obtain ⟨h_from_rel, _⟩ :=
      calculatePathRankings_σ_equivariant_relational G σ hσ vts₁ vts₂ hvts_rel
    -- Apply h_from_rel at d = k, s = w.
    show (calculatePathRankings (initializePaths G) vts₂).fromRanks.getD (k + 1 - 1) #[] |>.getD w.val 0
       = (calculatePathRankings (initializePaths G) vts₁).fromRanks.getD (k + 1 - 1) #[] |>.getD (σ⁻¹ w).val 0
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
  -- The τ-related-form-of-h_rel needed by Stage B-rel: vts₂[(τ v)] = vts₁[v].
  -- Substitute w ← τ v in h_rel: vts₂[(τ v).val] = vts₁[(τ⁻¹ (τ v)).val] = vts₁[v.val].
  have hvts_rel : ∀ v : Fin n, vts₂.getD (τ v) 0 = vts₁.getD v 0 := by
    intro v
    have h := h_rel (τ v)
    have h_inv : τ⁻¹ (τ v) = v := by simp
    rw [h_inv] at h
    exact h
  -- Bound facts.
  have hw_size : w.val < vts₂.size := h_size₂ ▸ w.isLt
  have hτw_size : (τ⁻¹ w).val < vts₁.size := h_size₁ ▸ (τ⁻¹ w).isLt
  -- Apply convergeOnce_writeback on both sides.
  rw [convergeOnce_writeback (initializePaths G) vts₂ w.val hw_size w.isLt,
      convergeOnce_writeback (initializePaths G) vts₁ (τ⁻¹ w).val hτw_size (τ⁻¹ w).isLt]
  -- Goal: (calculatePathRankings (init G) vts₂).getFrom (n-1) w.val
  --     = (calculatePathRankings (init G) vts₁).getFrom (n-1) (τ⁻¹ w).val
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
    have hStep := convergeOnce_VtsInvariant_eq G τ hτ vts₁ vts₂ h_size₁ h_size₂ h_rel
    have hStep_size₁ : (convergeOnce (initializePaths G) vts₁).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₁
    have hStep_size₂ : (convergeOnce (initializePaths G) vts₂).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size₂
    intro w
    -- One step: output is `if changed then loop k on (.1) else .1`.
    -- The two `.changed` flags may differ between vts₁ and vts₂. We need to handle all 4 cases.
    -- Crucially, the post-step typing arrays are τ-related; if the loop continues on either
    -- side, fuel is identical, and the output is determined by the typing arrays.
    -- However, the algorithm's actual control flow uses the changed flag — we need to show
    -- that the changed flags are aligned modulo τ. Simpler: factor out the if into a single
    -- expression depending only on the typing array, using the fact that even when the flag
    -- says "no change," recursing one more time on the unchanged array gives the same answer.
    --
    -- Approach: rather than reason about the flag, we directly show
    --   convergeLoop init vts (k+1) = convergeLoop init (convergeOnce vts).1 k  (when changed)
    --                              = (convergeOnce vts).1                         (otherwise)
    -- And on either branch, the IH plus τ-relatedness of the post-step arrays gives the
    -- desired equality.
    --
    -- BUT: the flag `changed` may differ between vts₁ and vts₂ in a way that breaks
    -- naive case-splitting. We unblock this by re-reading the spec: actually when the
    -- flag is `false`, we have `(convergeOnce vts).1 = vts` (no change), and so applying
    -- `convergeLoop _ _ k` to the unchanged array would leave it as-is (induction shows
    -- the loop output equals input when `convergeOnce` is the identity). So we can in
    -- fact treat the result as `convergeLoop init (convergeOnce vts).1 k` uniformly.
    -- This is the key observation that makes the relational lift work.
    --
    -- Concretely: we need a small lemma stating that the two formulations agree.
    set co₁ := convergeOnce (initializePaths G) vts₁ with h_co₁
    set co₂ := convergeOnce (initializePaths G) vts₂ with h_co₂
    -- Apply IH to (co₁.1, co₂.1) using hStep_size₁, hStep_size₂, hStep.
    have h_loopRel := ih co₁.1 co₂.1 hStep_size₁ hStep_size₂ hStep
    -- The convergeLoop unfolds at succ k as: if co.2 then convergeLoop init co.1 k else co.1.
    -- For both branches, we want the τ-related conclusion to hold.
    -- Reformulate convergeLoop as `convergeLoop init co.1 k` in the false case via
    -- `convergeLoop_unchanged_eq_input`-style lemma. But we don't have that lemma yet.
    -- Alternative: show that `convergeLoop init vts (k+1) = convergeLoop init co.1 k`
    -- always, regardless of the flag, by case-splitting on the flag and using that
    -- when the flag is false, `co.1 = vts`.
    have h_left_eq : convergeLoop (initializePaths G) vts₂ (k + 1) =
        convergeLoop (initializePaths G) co₂.1 k := by
      change (if co₂.2 then convergeLoop (initializePaths G) co₂.1 k else co₂.1)
              = convergeLoop (initializePaths G) co₂.1 k
      split
      · rfl
      · -- co₂.2 = false ⟹ co₂.1 = vts₂.
        rename_i h_changed
        have h_unchanged : co₂.1 = vts₂ :=
          convergeOnce_unchanged_when_not_flag _ _ h_changed
        rw [h_unchanged]
        -- Need: vts₂ = convergeLoop init vts₂ k. Inductively this holds because each
        -- step is the identity on vts₂ (since `convergeOnce init vts₂` doesn't change).
        exact (convergeLoop_unchanged_fixedpoint _ _ k h_changed).symm
    have h_right_eq : convergeLoop (initializePaths G) vts₁ (k + 1) =
        convergeLoop (initializePaths G) co₁.1 k := by
      change (if co₁.2 then convergeLoop (initializePaths G) co₁.1 k else co₁.1)
              = convergeLoop (initializePaths G) co₁.1 k
      split
      · rfl
      · rename_i h_changed
        have h_unchanged : co₁.1 = vts₁ :=
          convergeOnce_unchanged_when_not_flag _ _ h_changed
        rw [h_unchanged]
        exact (convergeLoop_unchanged_fixedpoint _ _ k h_changed).symm
    rw [h_left_eq, h_right_eq]
    exact h_loopRel w

end Graph
