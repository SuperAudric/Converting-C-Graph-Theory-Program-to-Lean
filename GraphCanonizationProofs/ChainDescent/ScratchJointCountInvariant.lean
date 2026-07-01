/-
# Route A, the iterated/profile observable — soundness of the seal's `jointIsoCountK` (the free half)

**What this module builds.** The route-A reduction scaffold (`ScratchSpanDim2Recovery.obsEq_iff_stabOrbit`) is parametric
in an observable `obs : V → β` and needs two inputs: `ObsInvariant` (soundness — same orbit ⟹ same `obs`, FREE) and
`WallKernelFor obs` (the open recovery). The re-scope (recovery doc §8 ITEM B "INCREMENT 2") fixed the observable as the
seal's own **joint isotropy count `jointIsoCountK`** — a *single* count is only `χ(det)`-valued, so route A uses the
**profile over sub-configs** `S' ⊆ S₀` (the `ZProfileSeparatesK`-style observable), iterated. This module discharges the
FREE half **concretely** for that observable: a base-fixing **similitude** preserves `jointIsoCountK`, so the sub-config
profile is `Stab(S₀)`-invariant.

**The content.**
* `isoClassK_similitude` / `_symm` — a similitude `g` (`Q∘g = μ·Q`, `μ ≠ 0`) preserves the isotropy class
  (`isoClassK Q (g w) = isoClassK Q w`): `g w = 0 ⟺ w = 0` (linear equiv) and `Q(g w) = 0 ⟺ Q w = 0` (`μ ≠ 0`).
* `jointIsoCountK_similitude_fix` — if `g` fixes `S` pointwise, `jointIsoCountK Q (g u) S = jointIsoCountK Q u S`
  (bijection `z ↦ g z`: `g z − g u = g(z − u)` and `g z − t = g(z − t)` for `t ∈ S`, both class-preserved).
* `jointCountProfile` + `obsInvariant_jointCountProfile` — the sub-config-profile observable
  `u ↦ (S' ↦ if S' ⊆ S₀ then jointIsoCountK Q u S' else 0)` is `ObsInvariant … Q ↑S₀`. So route A at the span-dim-2 base
  reduces (via `obsEq_iff_stabOrbit`) to `WallKernelFor (this profile)` — the single remaining open (crackable, `d`-flat)
  content; the seal's landed `jointIsoCountK_ne_of_chiSep_pair` is the per-round separation lever.

Reuses `FieldGeneric` (`isoClassK`, `jointIsoCountK`) + `ScratchSpanDim2Recovery` (`ObsInvariant`, `Similitude`). The
geometric model `V = Fin d → K`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.FieldGeneric
import ChainDescent.ScratchSpanDim2Recovery

namespace ChainDescent.JointCountInvariant

open QuadraticMap ChainDescent.OrbitBaseCase ChainDescent.SpanDim2Recovery

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)}

/-- **A similitude preserves the isotropy class.** `isoClassK Q (g w) = isoClassK Q w`: `g` is a linear equiv so
`g w = 0 ⟺ w = 0`, and `Q (g w) = μ · Q w` with `μ ≠ 0` gives `Q (g w) = 0 ⟺ Q w = 0`. -/
theorem isoClassK_similitude (g : Similitude Q) (w : Fin d → K) :
    isoClassK Q (g.toLinearEquiv w) = isoClassK Q w := by
  unfold isoClassK
  by_cases hw0 : w = 0
  · subst hw0; simp
  · have hgw0 : g.toLinearEquiv w ≠ 0 := fun h =>
      hw0 (g.toLinearEquiv.injective (by rw [h, map_zero]))
    rw [if_neg hw0, if_neg hgw0]
    by_cases hqw : Q w = 0
    · rw [if_pos hqw, if_pos (by rw [g.map, hqw, mul_zero])]
    · rw [if_neg hqw, if_neg (by rw [g.map]; exact mul_ne_zero g.mult_ne hqw)]

/-- **The inverse form.** `isoClassK Q (g⁻¹ w) = isoClassK Q w` (apply `isoClassK_similitude` at `g⁻¹ w`). -/
theorem isoClassK_similitude_symm (g : Similitude Q) (w : Fin d → K) :
    isoClassK Q (g.toLinearEquiv.symm w) = isoClassK Q w := by
  have h := isoClassK_similitude g (g.toLinearEquiv.symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

open scoped Classical in
/-- **★ Soundness — a base-fixing similitude preserves the joint isotropy count.** If `g` fixes every point of `S`,
then `jointIsoCountK Q (g u) S = jointIsoCountK Q u S`. Bijection `z ↦ g z`: `z ≠ u ⟺ g z ≠ g u` (injective),
`g z − g u = g (z − u)` and `g z − t = g (z − t)` for `t ∈ S` (as `g t = t`), and `g` preserves the isotropy class. -/
theorem jointIsoCountK_similitude_fix (g : Similitude Q) {S : Finset (Fin d → K)}
    (hfix : ∀ t ∈ S, g.toLinearEquiv t = t) (u : Fin d → K) :
    jointIsoCountK Q (g.toLinearEquiv u) S = jointIsoCountK Q u S := by
  unfold jointIsoCountK
  have hfix' : ∀ t ∈ S, g.toLinearEquiv.symm t = t := fun t ht => by
    conv_lhs => rw [← hfix t ht]
    exact g.toLinearEquiv.symm_apply_apply t
  refine Finset.card_bij' (fun z _ => g.toLinearEquiv.symm z) (fun z _ => g.toLinearEquiv z)
    ?_ ?_ ?_ ?_
  · -- i : (gu)-set → u-set,  z ↦ g⁻¹ z
    rintro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hzu, hzu2, hzS⟩ := hz
    refine ⟨fun h => hzu (by rw [← h, LinearEquiv.apply_symm_apply]), ?_, fun t ht => ?_⟩
    · have he : g.toLinearEquiv.symm z - u
          = g.toLinearEquiv.symm (z - g.toLinearEquiv u) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]
      rw [he, isoClassK_similitude_symm]; exact hzu2
    · have he : g.toLinearEquiv.symm z - t = g.toLinearEquiv.symm (z - t) := by
        rw [map_sub, hfix' t ht]
      rw [he, isoClassK_similitude_symm]; exact hzS t ht
  · -- j : u-set → (gu)-set,  z ↦ g z
    rintro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hzu, hzu2, hzS⟩ := hz
    refine ⟨fun h => hzu (g.toLinearEquiv.injective h), ?_, fun t ht => ?_⟩
    · rw [← map_sub, isoClassK_similitude]; exact hzu2
    · rw [← hfix t ht, ← map_sub, isoClassK_similitude]; exact hzS t ht
  · rintro z _; exact g.toLinearEquiv.apply_symm_apply z
  · rintro z _; exact g.toLinearEquiv.symm_apply_apply z

open scoped Classical in
/-- **The sub-config joint-count profile observable.** `u ↦ (S' ↦ jointIsoCountK Q u S')` over sub-configs `S' ⊆ S₀`
(junk `0` off the sub-config lattice). This is the observable route A separates on at the span-dim-2 base `S₀` — the
`ZProfileSeparatesK`-style profile (richer than a single `χ(det)`-valued count). -/
noncomputable def jointCountProfile (Q : QuadraticForm K (Fin d → K)) (S₀ : Finset (Fin d → K))
    (u : Fin d → K) : Finset (Fin d → K) → ℕ :=
  fun S' => if S' ⊆ S₀ then jointIsoCountK Q u S' else 0

open scoped Classical in
/-- **★ `ObsInvariant` for the joint-count profile.** The sub-config joint-count profile is `Stab(S₀)`-invariant: a
similitude fixing `S₀` pointwise fixes every sub-config `S' ⊆ S₀` pointwise, so preserves each `jointIsoCountK`
(`jointIsoCountK_similitude_fix`). Discharges the FREE half of `obsEq_iff_stabOrbit` for the concrete seal observable,
reducing route A at a span-dim-2 base `S₀` to `WallKernelFor (jointCountProfile Q S₀ ·) Q ↑S₀`. -/
theorem obsInvariant_jointCountProfile (S₀ : Finset (Fin d → K)) :
    ObsInvariant (jointCountProfile Q S₀) Q (↑S₀ : Set (Fin d → K)) := by
  intro g hfix u
  funext S'
  unfold jointCountProfile
  by_cases hS' : S' ⊆ S₀
  · rw [if_pos hS', if_pos hS']
    exact jointIsoCountK_similitude_fix g
      (fun t ht => hfix t (by exact_mod_cast hS' ht)) u
  · rw [if_neg hS', if_neg hS']

end ChainDescent.JointCountInvariant
