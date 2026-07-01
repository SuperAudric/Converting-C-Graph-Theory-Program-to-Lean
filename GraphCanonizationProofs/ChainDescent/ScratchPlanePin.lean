/-
# Route A, Step C — first steps: the `zSet` observable resolves cells to orbits (modulo "C^∞ pins W")

**What this module builds (scoping + first steps of Step C, recovery doc §9.5).** Step C must show the actual 1-WL
observable refines `IsoSetEq` ("C^∞ pins the plane `W`"). This module takes the observable to be the **isotropic set
itself** `zSet(u) = {w ∈ W : Q(u−w)=0}` — the zero-pattern of `Obs_aug` — and proves that *for this observable* route A
closes on an **anisotropic plane**, reducing everything to the single open statement "1-WL-stable refines `zSet`".

* `zSet` + `zSet_eq_iff_isoSetEq` — `zSet(u)=zSet(u') ⟺ IsoSetEq` (definitional).
* `zSet_invariant` (`ObsInvariant`) — a `{a,b}`-fixing similitude fixes `W` pointwise (`stab_fixes_span`) and preserves
  `Q(·)=0`, so it preserves `zSet`. **Soundness, free.**
* `wallKernel_zSet_anisotropic` — on an anisotropic plane, `WallKernelFor zSet` from **Step B** (both branches: generic
  via `sameExactGram_of_isoSetEq_generic`, singleton via `_singleton_anis`; the "one side generic" case symmetrised).
* `zSetEq_iff_stabOrbit_anisotropic` — the scaffold `obsEq_iff_stabOrbit` instantiated at `zSet`: **`zSet u = zSet u' ↔
  StabOrbit`**, i.e. `bᵢ = 1` *for the `zSet` observable*. So the cell-vs-orbit gap is now entirely: does 1-WL compute
  (refine to) `zSet`? = **"C^∞ pins W"**, the open counting crux (Step C proper).

The remaining open content, precisely isolated: `zSet` is `Stab`-invariant but not a-priori 1-WL-computable at
`{0,a,b}` — the plane points must be pinned by the iteration. That is the `d`-independent plane-pinning count (§9.5 Step
C), NOT built here. Reuses `ScratchBaseAug` (Step B), `ScratchConicSpan` (`exists_orthogonal_decomp`), `ScratchBranchDepth`
(`stab_fixes_span`), `ScratchSpanDim2Recovery` (the scaffold). Axiom-clean `[propext, Classical.choice, Quot.sound]`,
`lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchBaseAug
import ChainDescent.ScratchBranchDepth
import ChainDescent.ScratchSpanDim2Recovery

namespace ChainDescent.PlanePin

open QuadraticMap LinearMap ChainDescent.OrbitBaseCase ChainDescent.Wall
  ChainDescent.BaseAug ChainDescent.SpanDim2Recovery

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **The `zSet` observable.** `zSet Q W u = {w ∈ W : Q(u − w) = 0}` — `u`'s isotropic set in the plane `W`. Its
equality relation is exactly `IsoSetEq`, and it is `Stab`-invariant; the observable route A separates on. -/
def zSet (Q : QuadraticForm K V) (W : Submodule K V) (u : V) : Set V :=
  {w | w ∈ W ∧ Q (u - w) = 0}

/-- `zSet u = zSet u' ⟺ IsoSetEq` — the observable's equality IS same-isotropic-set-in-`W`. -/
theorem zSet_eq_iff_isoSetEq {W : Submodule K V} {u u' : V} :
    zSet Q W u = zSet Q W u' ↔ IsoSetEq Q W u u' := by
  constructor
  · intro h w hw
    constructor
    · intro hu
      have hm : w ∈ zSet Q W u := ⟨hw, hu⟩
      rw [h] at hm; exact hm.2
    · intro hu'
      have hm : w ∈ zSet Q W u' := ⟨hw, hu'⟩
      rw [← h] at hm; exact hm.2
  · intro h
    ext w
    simp only [zSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hw, hu⟩; exact ⟨hw, (h w hw).mp hu⟩
    · rintro ⟨hw, hu'⟩; exact ⟨hw, (h w hw).mpr hu'⟩

/-- **Soundness — `zSet` is `Stab({a,b})`-invariant.** A `{a,b}`-fixing similitude `g` fixes all of `W = span{a,b}`
pointwise (`stab_fixes_span`), so for `w ∈ W`, `Q(g u − w) = Q(g(u − w)) = μ·Q(u − w)` — zero iff `Q(u−w)=0`. Hence
`zSet(g u) = zSet(u)`. This is `ObsInvariant` for `zSet`. -/
theorem zSet_invariant {a b : V} :
    ObsInvariant (zSet Q (Submodule.span K ({a, b} : Set V))) Q (↑({a, b} : Set V)) := by
  intro g hfix u
  have hfix' : ∀ s ∈ ({a, b} : Set V), g.toLinearEquiv s = s := by
    intro s hs; exact hfix s hs
  ext w
  simp only [zSet, Set.mem_setOf_eq]
  refine and_congr_right (fun hwW => ?_)
  have hgw : g.toLinearEquiv w = w := ChainDescent.BranchDepth.stab_fixes_span hfix' hwW
  have key : Q (g.toLinearEquiv u - w) = g.mult * Q (u - w) := by
    conv_lhs => rw [← hgw]
    rw [← map_sub, g.map]
  rw [key]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left g.mult_ne
  · intro h; rw [h, mul_zero]

/-- `IsoSetEq` is symmetric. -/
theorem isoSetEq_symm {W : Submodule K V} {u u' : V} (h : IsoSetEq Q W u u') : IsoSetEq Q W u' u :=
  fun w hw => (h w hw).symm

/-- `SameExactGram` is symmetric. -/
theorem sameExactGram_symm {S : Set V} {u u' : V} (h : SameExactGram Q S u u') :
    SameExactGram Q S u' u :=
  ⟨h.1.symm, fun s hs => (h.2 s hs).symm⟩

/-- **★ `WallKernelFor zSet` on an anisotropic plane (Step B composed).** For a span-dim-2 anisotropic base `{a,b}` whose
plane `W` is anisotropic, `zSet u = zSet u' ⟹ SameExactGram` for **every** pair — the two branches of Step B cover all
cases: if either vertex is generic (`Q ·_⊥ ≠ 0`) use `sameExactGram_of_isoSetEq_generic` (symmetrising if it is `u'`);
if both are singleton (`Q ·_⊥ = 0`) use `_singleton_anis` (the plane being anisotropic supplies its hypothesis). No
counting. -/
theorem wallKernel_zSet_anisotropic [FiniteDimensional K V] {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0) :
    WallKernelFor (fun u u' => zSet Q (Submodule.span K ({a, b} : Set V)) u
        = zSet Q (Submodule.span K ({a, b} : Set V)) u') Q (↑({a, b} : Set V)) := by
  intro u u' hz
  have hobs : IsoSetEq Q (Submodule.span K ({a, b} : Set V)) u u' :=
    zSet_eq_iff_isoSetEq.mp hz
  obtain ⟨u_W, u_perp, hu, hu_W, hu_perp⟩ := ChainDescent.ConicSpan.exists_orthogonal_decomp hQa hQb hab u
  obtain ⟨u'_W, u'_perp, hu', hu'_W, hu'_perp⟩ :=
    ChainDescent.ConicSpan.exists_orthogonal_decomp hQa hQb hab u'
  by_cases hup : Q u_perp = 0
  · by_cases hup' : Q u'_perp = 0
    · exact sameExactGram_of_isoSetEq_singleton_anis hanis hu hu' hu_W hu'_W hu_perp hu'_perp
        hup hup' hobs
    · exact sameExactGram_symm (sameExactGram_of_isoSetEq_generic hQa hQb hab hF hq hu' hu'_W
        hu'_perp hup' (isoSetEq_symm hobs))
  · exact sameExactGram_of_isoSetEq_generic hQa hQb hab hF hq hu hu_W hu_perp hup hobs

/-- **★ Route A closes for the `zSet` observable (anisotropic plane) — the cell-vs-orbit gap isolated.** The scaffold
`obsEq_iff_stabOrbit` at `obs = zSet`: **`zSet u = zSet u' ↔ StabOrbit Q {a,b} u u'`** — the `zSet`-cells ARE the
`Stab`-orbits (`bᵢ = 1`), given the carried Witt extension. **So the entire remaining route-A content is the single
statement "1-WL-stable at `{0,a,b}` refines `zSet`" (= C^∞ pins `W`)** — the `d`-independent plane-pinning count
(recovery doc §9.5 Step C), the open crux. -/
theorem zSetEq_iff_stabOrbit_anisotropic [FiniteDimensional K V] {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0)
    (hWitt : WittExtendsToOrbit Q (↑({a, b} : Set V))) {u u' : V} :
    zSet Q (Submodule.span K ({a, b} : Set V)) u = zSet Q (Submodule.span K ({a, b} : Set V)) u'
      ↔ StabOrbit Q (↑({a, b} : Set V)) u u' :=
  obsEq_iff_stabOrbit zSet_invariant (wallKernel_zSet_anisotropic hQa hQb hab hF hq hanis) hWitt

end ChainDescent.PlanePin
