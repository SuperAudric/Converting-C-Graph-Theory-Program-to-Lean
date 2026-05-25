import FullCorrectness.Tiebreak

/-!
# Phase 4 — `breakTieAt` / `shiftAbove` τ-related preservation helpers
  (`FullCorrectness.Equivariance.BreakTieRelational`)

Two τ-related typing arrays `vts₁`, `vts₂` (with `vts₂[w] = vts₁[τ⁻¹ w]`) are preserved
under `shiftAbove t` and `breakTieAt t keep`/`breakTieAt t (τ keep)` respectively. The
`shiftAbove` lemma is a direct pointwise check; `breakTieAt_τ_related` generalizes the
existing `breakTieAt_VtsInvariant_eq` (which used a single `vts`) to the relational form.

These helpers are used by Phase 5 to show that running τ-related typings through a single
`convergeLoop`/`breakTie` round of `runFrom` yields τ-related outputs again, when the
tiebreak choices are themselves τ-related.

**Critical observation.** `breakTie` itself is **not** in general τ-equivariant — its
"smallest index" choice depends on `Fin` ordering, which τ does not respect. So we collect
helpers for the parts that *do* preserve τ-relatedness, namely `shiftAbove` and
`breakTieAt` (the latter parameterized by an explicit `keep` index, where the τ-image
`τ keep` plays the symmetric role).
-/

namespace Graph

variable {n : Nat}

/-! ### `shiftAbove` τ-relational equivariance

`shiftAbove t vts` shifts every value `> t` up by 1 (preserving values `≤ t`). It depends
on the typing array only through pointwise comparison of values to `t`, so τ-related
inputs produce τ-related outputs. -/

/-- `shiftAbove` preserves τ-relatedness pointwise. For τ-related `vts₁, vts₂`:
`(shiftAbove t vts₂)[w] = (shiftAbove t vts₁)[τ⁻¹ w]`. -/
theorem shiftAbove_VtsInvariant_eq
    (t : VertexType) (τ : Equiv.Perm (Fin n))
    (vts₁ vts₂ : Array VertexType)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0) :
    ∀ w : Fin n,
      (shiftAbove t vts₂).getD w.val 0 = (shiftAbove t vts₁).getD (τ⁻¹ w).val 0 := by
  intro w
  -- shiftAbove is determined entirely by `vts.getD j 0` (pointwise comparison to t).
  by_cases h_lt : vts₂.getD w.val 0 ≤ t
  · -- vts₂[w] ≤ t: vts₁[τ⁻¹ w] ≤ t too (via h_rel).
    have h_lt' : vts₁.getD (τ⁻¹ w).val 0 ≤ t := by rw [← h_rel w]; exact h_lt
    rw [shiftAbove_getD_below t vts₂ h_lt, shiftAbove_getD_below t vts₁ h_lt']
    exact h_rel w
  · -- vts₂[w] > t: vts₁[τ⁻¹ w] > t too.
    push_neg at h_lt
    have h_gt' : vts₁.getD (τ⁻¹ w).val 0 > t := by rw [← h_rel w]; exact h_lt
    rw [shiftAbove_getD_above t vts₂ h_lt, shiftAbove_getD_above t vts₁ h_gt']
    rw [h_rel w]

/-- `shiftAbove` preserves array size. -/
theorem shiftAbove_VtsInvariant_size_eq (t : VertexType) (vts : Array VertexType)
    (h_size : vts.size = n) : (shiftAbove t vts).size = n := by
  rw [shiftAbove_size]; exact h_size

/-! ### `breakTieAt` τ-relational equivariance

The relational generalization of `breakTieAt_VtsInvariant_eq`. Compared to the
single-array version, this takes two τ-related typing arrays and asserts that running
`breakTieAt vts₁ t₀ keep` and `breakTieAt vts₂ t₀ (τ keep)` produces τ-related outputs.

The proof structure mirrors `breakTieAt_VtsInvariant_eq`'s case analysis on whether
`w` is in the target class `typeClass t₀` and whether `w = τ keep`. -/

/-- For τ-related `vts₁, vts₂` and any `keep`, the outputs of `breakTieAt vts₁ t₀ keep`
and `breakTieAt vts₂ t₀ (τ keep)` are τ-related: at every position `w`,

  `(breakTieAt vts₂ t₀ (τ keep))[w] = (breakTieAt vts₁ t₀ keep)[τ⁻¹ w]`.

This is the relational generalization of `breakTieAt_VtsInvariant_eq` (which is the case
`vts₁ = vts₂ = vts` with `VtsInvariant τ vts`). -/
theorem breakTieAt_τ_related
    (vts₁ vts₂ : Array VertexType) (t₀ : VertexType)
    (τ : Equiv.Perm (Fin n)) (keep : Fin n)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0) (w : Fin n) :
    (breakTieAt vts₂ t₀ (τ keep)).getD w.val 0 =
      (breakTieAt vts₁ t₀ keep).getD (τ⁻¹ w).val 0 := by
  by_cases hw : vts₂.getD w.val 0 = t₀
  · -- w ∈ typeClass t₀ in vts₂
    have hτw : vts₁.getD (τ⁻¹ w).val 0 = t₀ := by rw [← h_rel w]; exact hw
    by_cases h_eq : w = τ keep
    · -- w = τ keep → τ⁻¹ w = keep
      subst h_eq
      have h_inv_keep : τ⁻¹ (τ keep) = keep := by simp
      rw [breakTieAt_getD_keep, h_inv_keep, breakTieAt_getD_keep]
      have h := h_rel (τ keep)
      rw [h_inv_keep] at h
      exact h
    · -- w ≠ τ keep, so τ⁻¹ w ≠ keep.
      have h_neq : τ⁻¹ w ≠ keep := by
        intro h
        apply h_eq
        have : τ (τ⁻¹ w) = τ keep := by rw [h]
        simpa using this
      rw [breakTieAt_getD_promoted vts₂ t₀ (τ keep) h_size₂ hw h_eq,
          breakTieAt_getD_promoted vts₁ t₀ keep h_size₁ hτw h_neq]
  · -- w ∉ typeClass t₀ in vts₂
    have hτw : vts₁.getD (τ⁻¹ w).val 0 ≠ t₀ := by rw [← h_rel w]; exact hw
    rw [breakTieAt_getD_of_ne vts₂ t₀ (τ keep) hw,
        breakTieAt_getD_of_ne vts₁ t₀ keep hτw]
    exact h_rel w

/-- `breakTieAt` preserves array size, which threads through Phase 5's induction so
size hypotheses stay valid as `breakTieAt`/`convergeLoop` alternate. -/
theorem breakTieAt_size_eq (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n)
    (h_size : vts.size = n) : (breakTieAt vts t₀ keep).size = n := by
  rw [breakTieAt_size]; exact h_size

end Graph
