/-
# Route A, Phase 1 — the `hspan` assembly (level-set points in the plane, part 1: the Q-level assembly)

**What this module builds.** Piece (i) of the `hspan` discharge (recovery doc §8 ITEM B, "Remaining in A2"): turn the
landed conic count (`ScratchConicCount.exists_both_nonzero_solution`) into **three explicit non-collinear points of the
`Q`-level set** `{v : Q v = c}` inside the plane `W = span{a,b}` — the geometric input `hspan_of_two_indep`
(`ScratchSpanDim2Span`) needs. The `u`-transport (`Z(u) = u_W − L_c`, placing these in the isotropic set of a vertex) is
the next sub-step (Stage 3, a separate lemma); this module is the `Q`-level assembly it stands on.

**The construction.** For an orthogonal anisotropic pair `a, b` (`Q a ≠ 0`, `Q b ≠ 0`, `polar Q a b = 0`), the plane
form is diagonal: `Q (x•a + y•b) = x²·Q a + y²·Q b` (`map_ortho_comb`). A both-coordinate-nonzero solution `(x₀,y₀)` to
`Q a·x² + Q b·y² = c` (from the count, `q ≥ 7`) gives the three points `x₀•a+y₀•b`, `(−x₀)•a+y₀•b`, `x₀•a+(−y₀)•b`,
all at level `c` (squares), with differences `(−2x₀)•a`, `(−2y₀)•b` — linearly independent (scalar multiples of the
independent `a, b`; `2x₀, 2y₀ ≠ 0`).

Reuses `ScratchConicCount` (`exists_both_nonzero_solution`), `PairForm`/`GoodAnchorNonvacuity`
(`pairForm_apply`, `linearIndependent_of_pairForm_ne_zero`). Axiom-clean `[propext, Classical.choice, Quot.sound]`,
`lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConicCount
import ChainDescent.GoodAnchorNonvacuity
import ChainDescent.ScratchSpanDim2Span

namespace ChainDescent.ConicSpan

open QuadraticMap LinearMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- **The plane form is diagonal.** For an orthogonal pair (`polar Q a b = 0`),
`Q (x • a + y • b) = x² · Q a + y² · Q b` (the cross term `x·y·polar Q a b` vanishes). -/
theorem map_ortho_comb {a b : V} (hab : QuadraticMap.polar Q a b = 0) (x y : K) :
    Q (x • a + y • b) = x ^ 2 * Q a + y ^ 2 * Q b := by
  have hm := QuadraticMap.map_add (⇑Q) (x • a) (y • b)
  rw [QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, hab] at hm
  simp only [smul_eq_mul, mul_zero, add_zero] at hm
  rw [hm]; ring

/-- **Scaling preserves pair-independence.** If `![a, b]` is linearly independent and `s, t ≠ 0`, then
`![s • a, t • b]` is linearly independent. -/
theorem indep_smul_pair {a b : V} (hab_indep : LinearIndependent K ![a, b]) {s t : K}
    (hs : s ≠ 0) (ht : t ≠ 0) : LinearIndependent K ![s • a, t • b] := by
  rw [LinearIndependent.pair_iff]
  intro p q hpq
  rw [smul_smul, smul_smul] at hpq
  rw [LinearIndependent.pair_iff] at hab_indep
  obtain ⟨h1, h2⟩ := hab_indep (p * s) (q * t) hpq
  exact ⟨(mul_eq_zero.mp h1).resolve_right hs, (mul_eq_zero.mp h2).resolve_right ht⟩

/-- **★ Three non-collinear points of the plane `Q`-level set.** For an orthogonal anisotropic pair `a, b`, level
`c ≠ 0`, and `q = |K| ≥ 7`, the level set `{v : Q v = c}` inside `W = span{a,b}` contains three points with linearly
independent difference vectors — exactly the input `hspan_of_two_indep` needs. Built from the both-nonzero conic
solution `(x₀,y₀)` and the three points `(±x₀,±y₀)` (in `a,b`-coordinates). -/
theorem exists_three_indep_levelset {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] {c : K} (hc : c ≠ 0) (hq : 7 ≤ Fintype.card K) :
    ∃ v₀ v₁ v₂ : V, Q v₀ = c ∧ Q v₁ = c ∧ Q v₂ = c ∧
      v₀ ∈ Submodule.span K ({a, b} : Set V) ∧
      v₁ ∈ Submodule.span K ({a, b} : Set V) ∧
      v₂ ∈ Submodule.span K ({a, b} : Set V) ∧
      LinearIndependent K ![v₁ - v₀, v₂ - v₀] := by
  obtain ⟨x₀, y₀, hsol, hx₀, hy₀⟩ := ConicCount.exists_both_nonzero_solution hF hQa hQb hc hq
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hba : QuadraticMap.polar Q b a = 0 := by rw [QuadraticMap.polar_comm]; exact hab
  have hma : a ∈ Submodule.span K ({a, b} : Set V) := Submodule.subset_span (by simp)
  have hmb : b ∈ Submodule.span K ({a, b} : Set V) := Submodule.subset_span (by simp)
  have hmem : ∀ x y : K, x • a + y • b ∈ Submodule.span K ({a, b} : Set V) := fun x y =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ hma) (Submodule.smul_mem _ _ hmb)
  have hab_indep : LinearIndependent K ![a, b] := by
    apply ChainDescent.linearIndependent_of_pairForm_ne_zero
    rw [pairForm_apply, hba]
    simp only [mul_zero, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
      hQa) hQb
  refine ⟨x₀ • a + y₀ • b, (-x₀) • a + y₀ • b, x₀ • a + (-y₀) • b, ?_, ?_, ?_,
    hmem _ _, hmem _ _, hmem _ _, ?_⟩
  · rw [map_ortho_comb hab]; linear_combination hsol
  · rw [map_ortho_comb hab]; linear_combination hsol
  · rw [map_ortho_comb hab]; linear_combination hsol
  · have e1 : ((-x₀) • a + y₀ • b) - (x₀ • a + y₀ • b) = (-(2 * x₀)) • a := by module
    have e2 : (x₀ • a + (-y₀) • b) - (x₀ • a + y₀ • b) = (-(2 * y₀)) • b := by module
    rw [e1, e2]
    exact indep_smul_pair hab_indep (neg_ne_zero.mpr (mul_ne_zero h2 hx₀))
      (neg_ne_zero.mpr (mul_ne_zero h2 hy₀))

/-- **★ The `hspan` transport capstone (generic `c ≠ 0` case).** For an orthogonal anisotropic pair `a, b` and a vertex
`u` split as `u = u_W + u_⊥` (with `u_W ∈ W = span{a,b}`, `u_⊥ ∈ Wᗮ`), if the complement datum is anisotropic
(`Q u_⊥ ≠ 0`, so the level `c = −Q u_⊥ ≠ 0` — the non-singleton case) and `q ≥ 7`, then `u`'s isotropic set
`Z(u) = {w ∈ W : Q(u − w) = 0}` **affinely spans** `W` — the `hspan` hypothesis of `exactGram_of_sameWProfile`.

Mechanism: the orthogonal split (`map_sub_split`) gives the level identity `Q(u − w) = Q(u_W − w) + Q u_⊥` for `w ∈ W`,
so `Z(u) = u_W − L_c` (the level set `{v ∈ W : Q v = c}` translated by `u_W`). The three non-collinear points of `L_c`
(`exists_three_indep_levelset`) transport to three non-collinear points of `Z(u)`, and `hspan_of_two_indep` closes.
(The singleton case `Q u_⊥ = 0` — `Z(u)` a single point — is handled separately: recovery doc §8 ITEM B "(ii)".) -/
theorem hspan_of_conic [FiniteDimensional K V]
    {a b : V} (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    {u u_W u_perp : V} (hdecomp : u = u_W + u_perp)
    (hu_W : u_W ∈ Submodule.span K ({a, b} : Set V))
    (hu_perp : u_perp ∈ BilinForm.orthogonal Q.polarBilin (Submodule.span K ({a, b} : Set V)))
    (hcp : Q u_perp ≠ 0) :
    ∃ w₀ : V, w₀ ∈ Submodule.span K ({a, b} : Set V) ∧ Q (u - w₀) = 0 ∧
      Submodule.span K ((fun w => w - w₀) ''
        {w : V | w ∈ Submodule.span K ({a, b} : Set V) ∧ Q (u - w) = 0})
        = Submodule.span K ({a, b} : Set V) := by
  have hc : -Q u_perp ≠ 0 := neg_ne_zero.mpr hcp
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  -- The level identity `Q(u − w) = Q(u_W − w) + Q u_⊥` for `w ∈ W` (orthogonal split).
  have hlevel : ∀ w ∈ Submodule.span K ({a, b} : Set V), Q (u - w) = Q (u_W - w) + Q u_perp := by
    intro w hw
    have h := ChainDescent.ComplementFactor.map_sub_split (Q := Q)
      (W := Submodule.span K ({a, b} : Set V)) hu_W hw hu_perp (Submodule.zero_mem _)
    rw [add_zero, sub_zero, ← hdecomp] at h
    exact h
  obtain ⟨v₀, v₁, v₂, hv0, hv1, hv2, hm0, hm1, hm2, hindep⟩ :=
    exists_three_indep_levelset hQa hQb hab hF hc hq
  -- Transport: `w_j := u_W − v_j ∈ Z(u)` (`Q(u − w_j) = Q v_j + Q u_⊥ = c + Q u_⊥ = 0`).
  have hzero : ∀ v : V, Q v = -Q u_perp → v ∈ Submodule.span K ({a, b} : Set V) →
      Q (u - (u_W - v)) = 0 := by
    intro v hv hvm
    rw [hlevel _ (Submodule.sub_mem _ hu_W hvm)]
    have he : u_W - (u_W - v) = v := by abel
    rw [he, hv]; ring
  have hz0 := hzero v₀ hv0 hm0
  have hz1 := hzero v₁ hv1 hm1
  have hz2 := hzero v₂ hv2 hm2
  have hab_indep : LinearIndependent K ![a, b] := by
    apply ChainDescent.linearIndependent_of_pairForm_ne_zero
    have hba : QuadraticMap.polar Q b a = 0 := by rw [QuadraticMap.polar_comm]; exact hab
    rw [pairForm_apply, hba]; simp only [mul_zero, sub_zero]
    exact mul_ne_zero (mul_ne_zero (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
      hQa) hQb
  have hfr : Module.finrank K (Submodule.span K ({a, b} : Set V)) = 2 := by
    have hrange : (Set.range ![a, b]) = ({a, b} : Set V) := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]; ext x; simp [or_comm]
    rw [← hrange, finrank_span_eq_card hab_indep]; simp
  have hwindep : LinearIndependent K ![(u_W - v₁) - (u_W - v₀), (u_W - v₂) - (u_W - v₀)] := by
    have e1 : (u_W - v₁) - (u_W - v₀) = (-1 : K) • (v₁ - v₀) := by rw [neg_one_smul]; abel
    have e2 : (u_W - v₂) - (u_W - v₀) = (-1 : K) • (v₂ - v₀) := by rw [neg_one_smul]; abel
    rw [e1, e2]
    exact indep_smul_pair hindep (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  exact ⟨u_W - v₀, Submodule.sub_mem _ hu_W hm0, hz0,
    ChainDescent.SpanDim2Span.hspan_of_two_indep hfr
      (Submodule.sub_mem _ hu_W hm0) (Submodule.sub_mem _ hu_W hm1) (Submodule.sub_mem _ hu_W hm2)
      hz0 hz1 hz2 hwindep⟩

end ChainDescent.ConicSpan
