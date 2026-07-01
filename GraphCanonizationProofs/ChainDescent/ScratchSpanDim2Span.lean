/-
# Route A, Phase 1 — discharging `hspan` (part 1: the combinatorial bridge)

**What this module builds.** The recovery core `exactGram_of_sameWProfile` (`ScratchSpanDim2Geom`) carries the
hypothesis `hspan` — the isotropic set `Z = {w ∈ W : Q(u − w) = 0}` **affinely spans** the plane `W` (anchored:
`span K (Z − w₀) = W`). This module discharges the **form-independent half**: `hspan` follows from the concrete geometric
fact "`Z` contains three non-collinear points" (two linearly independent difference vectors). Reducing `hspan` to that is
the clean base — the remaining content is a pure **binary-conic cardinality fact** (see below), isolated here.

**The bridge (`hspan_of_two_indep`).** In a 2-dimensional `W`, if `w₀, w₁, w₂ ∈ Z` with `w₁ − w₀`, `w₂ − w₀` linearly
independent, then the anchored span `span K (Z − w₀)` is all of `W`: the two independent difference vectors already span
the 2-dim `W`, and they lie in `Z − w₀`. Pure linear algebra — no quadratic form structure.

**What remains (the conic count — scoped, the Gauss half).** `hspan` now reduces to: `Z` has three non-collinear points.
Via the orthogonal split `Q(u−w) = Q_W(u_W−w) + Q(u⊥)` (`ScratchComplementFactor.map_add_split`), `Z` is a translate of
the level set `L_c = {v ∈ W : Q_W(v) = c}`, `c = −Q(u⊥)`. The exact count (`card_quadForm_eq` + `gaussSum_sq`:
`gaussSum² = χ(-1)·q`) gives `|L_c| = q − ε` (`ε = ±1`) for `c ≠ 0`, `2q − 1` for `c = 0` hyperbolic, `1` for `c = 0`
anisotropic (the singleton exception). With "a line meets `L_c` in ≤ 2 points" (`c ≠ 0`: a nondeg conic contains no
line), `|L_c| ≥ 3` (⟺ `q ≥ 4`) gives three non-collinear points ⟹ this bridge ⟹ `hspan`. So the residual is the exact
binary-conic count + the small-`q` tail — a bounded Gauss build, cleanly isolated.

Pure linear algebra (no Gauss, no Witt). Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in
`build.sh`.
-/
import ChainDescent.ScratchComplementFactor

namespace ChainDescent.SpanDim2Span

open QuadraticMap

set_option linter.unusedVariables false

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

/-- **★ The combinatorial bridge — `hspan` from three non-collinear isotropic points.** In a 2-dimensional plane `W`, if
`w₀, w₁, w₂` all lie in the isotropic set `Z = {w ∈ W : Q(u − w) = 0}` and the difference vectors `w₁ − w₀`, `w₂ − w₀`
are linearly independent, then `Z − w₀` spans `W` — i.e. the `hspan` hypothesis of `exactGram_of_sameWProfile` holds. The
two independent differences already span the 2-dim `W`, and both lie in `Z − w₀`. -/
theorem hspan_of_two_indep {W : Submodule K V} (hWdim : Module.finrank K W = 2)
    {u w₀ w₁ w₂ : V}
    (h₀ : w₀ ∈ W) (h₁ : w₁ ∈ W) (h₂ : w₂ ∈ W)
    (hz₀ : Q (u - w₀) = 0) (hz₁ : Q (u - w₁) = 0) (hz₂ : Q (u - w₂) = 0)
    (hindep : LinearIndependent K ![w₁ - w₀, w₂ - w₀]) :
    Submodule.span K ((fun w => w - w₀) '' {w : V | w ∈ W ∧ Q (u - w) = 0}) = W := by
  set Z : Set V := {w : V | w ∈ W ∧ Q (u - w) = 0} with hZ
  set G : Set V := (fun w => w - w₀) '' Z with hG
  -- the two independent differences lie in `G`.
  have hmem₁ : w₁ - w₀ ∈ G := ⟨w₁, ⟨h₁, hz₁⟩, rfl⟩
  have hmem₂ : w₂ - w₀ ∈ G := ⟨w₂, ⟨h₂, hz₂⟩, rfl⟩
  have hpair : ({w₁ - w₀, w₂ - w₀} : Set V) ⊆ G := by
    intro x hx; rcases hx with hx | hx <;> (rw [hx]; assumption)
  -- `span G ≤ W` (every generator is a difference of `W`-elements).
  have hGW : Submodule.span K G ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨w, ⟨hwW, _⟩, rfl⟩
    exact W.sub_mem hwW h₀
  -- `finrank (span {w₁-w₀, w₂-w₀}) = 2`.
  have hrange : (Set.range ![w₁ - w₀, w₂ - w₀]) = {w₁ - w₀, w₂ - w₀} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]; ext x; simp [or_comm]
  have hfr : Module.finrank K (Submodule.span K ({w₁ - w₀, w₂ - w₀} : Set V)) = 2 := by
    rw [← hrange, finrank_span_eq_card hindep]; simp
  -- squeeze: `span {..} ≤ span G ≤ W`, finranks `2 ≤ finrank (span G) ≤ 2`.
  have hle₁ : Submodule.span K ({w₁ - w₀, w₂ - w₀} : Set V) ≤ Submodule.span K G :=
    Submodule.span_mono hpair
  have hle₂ : Module.finrank K (Submodule.span K G) ≤ Module.finrank K W :=
    Submodule.finrank_mono hGW
  have hle₃ : Module.finrank K (Submodule.span K ({w₁ - w₀, w₂ - w₀} : Set V))
      ≤ Module.finrank K (Submodule.span K G) := Submodule.finrank_mono hle₁
  rw [hfr] at hle₃
  rw [hWdim] at hle₂
  -- `finrank (span G) = 2 = finrank W`, and `span G ≤ W` ⟹ equal.
  exact Submodule.eq_of_le_of_finrank_le hGW (by rw [hWdim]; omega)

end ChainDescent.SpanDim2Span
