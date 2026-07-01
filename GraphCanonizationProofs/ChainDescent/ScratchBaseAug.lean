/-
# Route A, Step B — the base-augmentation reduction (II-easy): `IsoSetEq ⟹ SameExactGram`

**What this module builds.** Step B of the route-A plan (recovery doc §9.5): the FREE half of the (II) seam. Define the
**base-augmentation observable** `IsoSetEq Q W u u'` = "`u, u'` have the same isotropic set in the plane `W`" (the
zero-pattern of `isoClass(·−w)` over `W`, which is what `Obs_aug` delivers once `C^∞` pins `W` — Step C). This module
discharges `IsoSetEq ⟹ SameExactGram Q {a,b} u u'` for **both** branches, reusing the landed (I)-geometry — *no counting*:

* **Generic branch** (`Q u_⊥ ≠ 0`, so `Z(u)` spans): `sameExactGram_of_isoSetEq_generic` — feed the `.mp` direction of
  `IsoSetEq` (= the one-directional `hprof`) and the `hspan` from `hspan_of_conic` into `exactGram_of_sameWProfile`.
* **Singleton branch** (`Q u_⊥ = 0` on an **anisotropic plane**, so `Z(u) = {u_W}`): the (ii)-glue
  `eq_wComp_of_isotropic_of_anisotropic` (`Z(u) = {u_W}` via the level identity + anisotropy) makes the `W`-components
  **match** (`u_W = u'_W`) from `IsoSetEq` alone, then `exactGram_of_isotropic_complement` closes it —
  `sameExactGram_of_isoSetEq_singleton_anis` (the match is *derived*, not carried).

So Step B banks `WallKernelFor IsoSetEq` on both branches; the only remaining route-A content is Step C ("C^∞ pins `W`",
the observable ⟹ `IsoSetEq` direction — where the counting lives). A `c=0`-hyperbolic sub-case (`Q u_⊥ = 0` on a
*hyperbolic* plane, where `Z` still spans) folds into the generic branch and is noted for later.

Reuses `ScratchConicSpan` (`hspan_of_conic`, `exactGram_of_isotropic_complement`, `ComplementFactor.map_sub_split`),
`ScratchSpanDim2Geom` (`exactGram_of_sameWProfile`), `ScratchWallKernel` (`SameExactGram`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConicSpan
import ChainDescent.ScratchSpanDim2Geom
import ChainDescent.ScratchWallKernel

namespace ChainDescent.BaseAug

open QuadraticMap LinearMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- **The base-augmentation observable (II-easy).** `IsoSetEq Q W u u'` = `u, u'` have the same isotropic set in the
plane `W`. This is what the augmented single-round observable `Obs_aug(u) = (isoClass(u−w))_{w∈W}` delivers once `C^∞`
pins `W` (Step C); here we discharge the FREE consequence `IsoSetEq ⟹ SameExactGram`. -/
def IsoSetEq (Q : QuadraticForm K V) (W : Submodule K V) (u u' : V) : Prop :=
  ∀ w ∈ W, (Q (u - w) = 0 ↔ Q (u' - w) = 0)

/-- Package the three-equality Gram conclusion as `Wall.SameExactGram` over `{a, b}`. -/
theorem sameExactGram_of_triple {a b u u' : V}
    (h : Q u = Q u' ∧ QuadraticMap.polar Q u a = QuadraticMap.polar Q u' a
      ∧ QuadraticMap.polar Q u b = QuadraticMap.polar Q u' b) :
    ChainDescent.Wall.SameExactGram Q ({a, b} : Set V) u u' := by
  refine ⟨h.1, ?_⟩
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact h.2.1
  · exact h.2.2

/-- **★ Step B (generic branch) — `IsoSetEq ⟹ SameExactGram`, via (I).** For a span-dim-2 anisotropic base at the
generic level (`Q u_⊥ ≠ 0`, so `Z(u)` spans), isotropy-set agreement `IsoSetEq` yields the same exact Gram to `{a,b}`.
`exactGram_of_sameWProfile` fed by the `.mp` direction of `IsoSetEq` (the one-directional `hprof`) + the `hspan` from
`hspan_of_conic`. No counting — the base-augmentation "easy" half. -/
theorem sameExactGram_of_isoSetEq_generic [FiniteDimensional K V] {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    {u u' u_W u_perp : V} (hdecomp : u = u_W + u_perp)
    (hu_W : u_W ∈ Submodule.span K ({a, b} : Set V))
    (hu_perp : u_perp ∈ BilinForm.orthogonal Q.polarBilin (Submodule.span K ({a, b} : Set V)))
    (hcp : Q u_perp ≠ 0)
    (hobs : IsoSetEq Q (Submodule.span K ({a, b} : Set V)) u u') :
    ChainDescent.Wall.SameExactGram Q ({a, b} : Set V) u u' := by
  obtain ⟨w₀, hw₀, hw₀0, hspan⟩ :=
    ChainDescent.ConicSpan.hspan_of_conic hQa hQb hab hF hq hdecomp hu_W hu_perp hcp
  exact sameExactGram_of_triple
    (ChainDescent.SpanDim2Geom.exactGram_of_sameWProfile
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      (fun w hw => (hobs w hw).mp) hw₀ hw₀0 hspan)

/-- **(ii)-glue — the singleton characterization.** If the plane `W` is anisotropic (`∀ v∈W, Q v = 0 → v = 0`) and `u`'s
complement component is isotropic (`Q u_⊥ = 0`), then the only `w∈W` with `Q(u−w)=0` is `u_W` — i.e. `Z(u) = {u_W}`.
Via the level identity `Q(u−w) = Q(u_W−w) + Q u_⊥ = Q(u_W−w)`, anisotropy forces `u_W − w = 0`. -/
theorem eq_wComp_of_isotropic_of_anisotropic {a b u u_W u_perp : V}
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0)
    (hu : u = u_W + u_perp) (hu_W : u_W ∈ Submodule.span K ({a, b} : Set V))
    (hu_perp : u_perp ∈ BilinForm.orthogonal Q.polarBilin (Submodule.span K ({a, b} : Set V)))
    (hiso : Q u_perp = 0) {w : V} (hw : w ∈ Submodule.span K ({a, b} : Set V))
    (hwz : Q (u - w) = 0) : w = u_W := by
  have hlevel : Q (u - w) = Q (u_W - w) := by
    have h := ChainDescent.ComplementFactor.map_sub_split (Q := Q)
      (W := Submodule.span K ({a, b} : Set V)) hu_W hw hu_perp (Submodule.zero_mem _)
    rw [add_zero, sub_zero, hiso, add_zero] at h
    rw [hu]; exact h
  have hz : Q (u_W - w) = 0 := by rw [← hlevel]; exact hwz
  have := hanis (u_W - w) (Submodule.sub_mem _ hu_W hw) hz
  exact (sub_eq_zero.mp this).symm

/-- **★ Step B (singleton branch) — `IsoSetEq ⟹ SameExactGram` on an anisotropic plane.** In the singleton locus
(`Q u_⊥ = Q u'_⊥ = 0`) on an **anisotropic** plane `W`, `IsoSetEq` alone forces the `W`-components to match
(`u_W = u'_W`, via `eq_wComp_of_isotropic_of_anisotropic`: `u_W ∈ Z(u) = Z(u') = {u'_W}`), after which
`exactGram_of_isotropic_complement` closes it. The match is **derived** from the observable, not carried — so the
singleton branch is fully closed (modulo the plane-anisotropy hypothesis that *characterizes* this branch). -/
theorem sameExactGram_of_isoSetEq_singleton_anis {a b : V}
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0)
    {u u' u_W u'_W u_perp u'_perp : V}
    (hu : u = u_W + u_perp) (hu' : u' = u'_W + u'_perp)
    (hu_W : u_W ∈ Submodule.span K ({a, b} : Set V))
    (hu'_W : u'_W ∈ Submodule.span K ({a, b} : Set V))
    (hu_perp : u_perp ∈ BilinForm.orthogonal Q.polarBilin (Submodule.span K ({a, b} : Set V)))
    (hu'_perp : u'_perp ∈ BilinForm.orthogonal Q.polarBilin (Submodule.span K ({a, b} : Set V)))
    (hiso : Q u_perp = 0) (hiso' : Q u'_perp = 0)
    (hobs : IsoSetEq Q (Submodule.span K ({a, b} : Set V)) u u') :
    ChainDescent.Wall.SameExactGram Q ({a, b} : Set V) u u' := by
  have huu : u - u_W = u_perp := by rw [hu]; abel
  have hz : Q (u - u_W) = 0 := by rw [huu]; exact hiso
  have hz' : Q (u' - u_W) = 0 := (hobs u_W hu_W).mp hz
  have hWeq : u_W = u'_W :=
    eq_wComp_of_isotropic_of_anisotropic hanis hu' hu'_W hu'_perp hiso' hu_W hz'
  exact sameExactGram_of_triple
    (ChainDescent.ConicSpan.exactGram_of_isotropic_complement hu hu' hu_W hu'_W hu_perp hu'_perp
      hiso hiso' hWeq)

end ChainDescent.BaseAug
