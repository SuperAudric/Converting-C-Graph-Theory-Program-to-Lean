/-
# Route A, Step C — the 1-WL-computability wiring ("`C^∞` pins `W`" ⟹ `bᵢ=1`, and its reduction to `PlanePinnable`)

**What this module builds (recovery doc §9.7, item (2)).** The pinning closure `PlanePinnable` (`ScratchPlanePinInduction`)
says the `χ`-profiles over reachable anchors separate the plane. The **wiring** turns that into the actual descent
statement — the 1-WL-stable colouring `C^∞` (after individualising the base) refines `zSet`, hence `bᵢ=1`. This module
lands the wiring on a **minimal, explicit 1-WL interface**, so the standard-WL content is named (not hand-waved) and the
genuinely-open residual is surfaced (not buried).

**§Core (abstract `V`) — the payoff: "`C` pins `W`" ⟹ `bᵢ=1`.**
* `IsColorSingleton C w` — `w` is the unique vertex of its `C`-colour (individualised / pinned).
* `ReadsSingletonIsotropy C Q` — the minimal 1-WL property: `C` reflects the isotropy indicator `Q(·−w)=0` to any
  colour-**singleton** `w`. (A theorem in any real 1-WL framework: if `w` is the unique vertex of its colour, the count of
  `z` with `C z = C w ∧ Q(u−z)=0` is `1`/`0` per `Q(u−w)=0`, so `C u` determines it. Encoded as an interface field — this
  is "what 1-WL does", not new math.)
* `PinsPlane C W := ∀ w∈W, IsColorSingleton C w` — "`C^∞` pins the plane".
* **`refines_zSet_of_pinsPlane`** — `ReadsSingletonIsotropy` + `PinsPlane` ⟹ `C` refines `zSet`.
* **`stabOrbit_of_colorEq`** — composed with `ScratchPlanePin.zSetEq_iff_stabOrbit_anisotropic`: WL-colour equality ⟹ same
  `Stab`-orbit (the *hard* "cells ⊆ orbits" direction). **`colorEq_iff_stabOrbit`** adds soundness (any `Stab`-invariant
  `C` has orbit ⟹ same colour, via `ObsInvariant`) to give the full **`C u = C u' ↔ StabOrbit`** = `bᵢ=1` for the WL
  colouring. This is the wiring's deliverable: *once `C` pins the plane, the WL cells ARE the orbits.*

**§Bridge (`V = Fin d → K`) — reduce "`C` pins `W`" to `PlanePinnable` + two named obligations.**
* `ReadsSingletonCounts C Q` — the count analogue of `ReadsSingletonIsotropy`: `C` reflects `jointIsoCountK(·,{t,t₀})` to
  colour-singleton anchors `t,t₀` (again standard 1-WL). Its contrapositive turns a count difference into a colour
  difference.
* `SeparatesPlaneFromComplement C W` — **the genuinely-open residual**, now named: plane points get a different `C`-colour
  from every non-plane vertex. This is NOT free (WL is coarser than orbits — the plane's orbit-rigidity does not make its
  points colour-singletons vs the complement) and is needed at *every* level of the induction (an anchor must be a *global*
  singleton to be read). It is the honest remaining WL-dimension content of the wiring.
* **`colorSingleton_of_mem_pinIter`** — the induction on the closure level: base `{0,a,b}` are singletons (individualised,
  `hbaseIndiv`); a freshly-pinned `w` is a singleton because it is `SeparatedBy` (already-singleton, by IH) anchors from
  every other plane point (`plane_count_sep` ⟹ count difference ⟹ colour difference), and from the complement
  (`SeparatesPlaneFromComplement`). **`pinsPlane_of_planePinnable`** packages it: `PlanePinnable` + the two interfaces +
  residual + base-individualisation ⟹ `PinsPlane`. Chaining with the Core gives `bᵢ=1` end-to-end.

Reuses `ScratchPlanePin` (`zSet`, `zSetEq_iff_stabOrbit_anisotropic`), `ScratchPlanePinInduction` (`pinIter`/`PlanePinnable`
/`SeparatedBy`), `ScratchPlaneSep` (`plane_count_sep`), `ScratchSpanDim2Recovery` (`ObsInvariant`/`stabOrbit_imp_obsEq`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchPlanePin
import ChainDescent.ScratchPlanePinInduction

namespace ChainDescent.WLWiring

set_option linter.unusedSectionVars false

/-- `w` is a colour-singleton under `C`: the unique vertex of its colour (individualised / pinned). -/
def IsColorSingleton {V γ : Type*} (C : V → γ) (w : V) : Prop := ∀ x, C x = C w → x = w

/-! ### §Core — abstract `V`: "`C` pins the plane" ⟹ `bᵢ=1`. -/

section Core

open QuadraticMap ChainDescent.OrbitBaseCase ChainDescent.Wall ChainDescent.PlanePin
  ChainDescent.SpanDim2Recovery

variable {K V γ : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **The minimal 1-WL property the wiring needs.** A refinement colouring `C` reflects the isotropy indicator
`Q(·−w)=0` to any colour-**singleton** `w`: if `w` is the unique vertex of its colour then `C u` determines whether
`Q(u−w)=0`. Standard 1-WL (a count against a singleton colour-class is `1`/`0`); carried as an interface field. -/
structure ReadsSingletonIsotropy (C : V → γ) (Q : QuadraticForm K V) : Prop where
  reads : ∀ w : V, IsColorSingleton C w →
    ∀ u u' : V, C u = C u' → (Q (u - w) = 0 ↔ Q (u' - w) = 0)

/-- **`C` pins the plane `W`:** every plane point is a colour-singleton. This is "`C^∞` pins `W`" (Insight 4). -/
def PinsPlane (C : V → γ) (W : Submodule K V) : Prop := ∀ w ∈ W, IsColorSingleton C w

/-- **★ `ReadsSingletonIsotropy` + `PinsPlane` ⟹ `C` refines `zSet`.** For each plane point `w` (a colour-singleton by
`hpins`), `C u = C u'` forces `Q(u−w)=0 ↔ Q(u'−w)=0`, so the isotropic sets in `W` coincide. -/
theorem refines_zSet_of_pinsPlane {C : V → γ} (hC : ReadsSingletonIsotropy C Q)
    {W : Submodule K V} (hpins : PinsPlane C W) {u u' : V} (h : C u = C u') :
    zSet Q W u = zSet Q W u' := by
  ext w
  simp only [zSet, Set.mem_setOf_eq]
  exact and_congr_right (fun hwW => hC.reads w (hpins w hwW) u u' h)

/-- **★ THE WIRING PAYOFF — WL-colour equality ⟹ same `Stab`-orbit (the hard "cells ⊆ orbits" direction).** Once `C`
pins the plane and reads singletons, `C u = C u'` implies `u, u'` are in the same `Stab({a,b})`-orbit — via
`refines_zSet_of_pinsPlane` then `zSetEq_iff_stabOrbit_anisotropic`. This is exactly `bᵢ=1`'s hard half for the actual
WL colouring. -/
theorem stabOrbit_of_colorEq [FiniteDimensional K V] {C : V → γ} {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0)
    (hWitt : WittExtendsToOrbit Q (↑({a, b} : Set V)))
    (hC : ReadsSingletonIsotropy C Q)
    (hpins : PinsPlane C (Submodule.span K ({a, b} : Set V)))
    {u u' : V} (h : C u = C u') :
    StabOrbit Q (↑({a, b} : Set V)) u u' :=
  (zSetEq_iff_stabOrbit_anisotropic hQa hQb hab hF hq hanis hWitt).mp
    (refines_zSet_of_pinsPlane hC hpins h)

/-- **★ Full `bᵢ=1` for the WL colouring.** Adding soundness — a `Stab`-invariant `C` gives orbit ⟹ same colour
(`stabOrbit_imp_obsEq`, `C` as an observable) — upgrades the payoff to an **iff**: `C u = C u' ↔ StabOrbit`. So the WL
cells coincide *exactly* with the `Stab`-orbits: `bᵢ = 1`. -/
theorem colorEq_iff_stabOrbit [FiniteDimensional K V] {C : V → γ} {a b : V}
    (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) (hab : QuadraticMap.polar Q a b = 0)
    (hF : ringChar K ≠ 2) [Invertible (2 : K)] (hq : 7 ≤ Fintype.card K)
    (hanis : ∀ v ∈ Submodule.span K ({a, b} : Set V), Q v = 0 → v = 0)
    (hWitt : WittExtendsToOrbit Q (↑({a, b} : Set V)))
    (hinv : ObsInvariant C Q (↑({a, b} : Set V)))
    (hC : ReadsSingletonIsotropy C Q)
    (hpins : PinsPlane C (Submodule.span K ({a, b} : Set V)))
    {u u' : V} :
    C u = C u' ↔ StabOrbit Q (↑({a, b} : Set V)) u u' :=
  ⟨stabOrbit_of_colorEq hQa hQb hab hF hq hanis hWitt hC hpins,
    fun h => stabOrbit_imp_obsEq hinv h⟩

end Core

/-! ### §Bridge — `V = Fin d → K`: reduce "`C` pins `W`" to `PlanePinnable` + two named obligations. -/

section Bridge

open QuadraticMap ChainDescent.PlanePinInduction ChainDescent.PlaneSep

variable {K γ : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-- **The count analogue of `ReadsSingletonIsotropy`.** `C` reflects the joint isotropy count against colour-**singleton**
anchors `t, t₀`: `C u = C u'` ⟹ `jointIsoCountK Q u {t,t₀} = jointIsoCountK Q u' {t,t₀}`. Standard 1-WL (a joint count
against singleton colour-classes is a function of the refined colour); carried as an interface field. Contrapositive: a
count difference forces a colour difference. -/
structure ReadsSingletonCounts (C : (Fin d → K) → γ) (Q : QuadraticForm K (Fin d → K)) : Prop where
  reads : ∀ t t₀ : Fin d → K, IsColorSingleton C t → IsColorSingleton C t₀ →
    ∀ u u' : Fin d → K, C u = C u' → jointIsoCountK Q u {t, t₀} = jointIsoCountK Q u' {t, t₀}

/-- **The genuinely-open residual, named.** Plane points get a different `C`-colour from every non-plane vertex. This is
the honest remaining WL-dimension content: orbit-rigidity of the plane does NOT make its points colour-singletons versus
the complement (WL is coarser than orbits), yet a *global* singleton is what both the induction (an anchor must be read)
and the payoff (`refines_zSet`) require. -/
def SeparatesPlaneFromComplement (C : (Fin d → K) → γ) (W : Set (Fin d → K)) : Prop :=
  ∀ w ∈ W, ∀ x, x ∉ W → C x ≠ C w

/-- `pinIter ⊆ W` (the closure never leaves the plane), given the seed is inside `W`. -/
theorem pinIter_subset_W {Q : QuadraticForm K (Fin d → K)} {W : Set (Fin d → K)} {a b : Fin d → K}
    (hseedW : seed a b ⊆ W) : ∀ n, pinIter Q W a b n ⊆ W := by
  intro n
  induction n with
  | zero => exact hseedW
  | succ k ih =>
      intro x hx
      simp only [pinIter, pinStep, Set.mem_union, Set.mem_setOf_eq] at hx
      rcases hx with hk | hfresh
      · exact ih hk
      · exact hfresh.1

/-- **★ The induction — every pinned point is a colour-singleton.** By induction on the closure level `n`: the seed
`{0,a,b}` are singletons (individualised, `hbaseIndiv`); a freshly-pinned `w` is a singleton because any `x` with the same
colour must equal `w` — if `x ∉ W`, the residual `SeparatesPlaneFromComplement` forbids `C x = C w`; if `x ∈ W` and `x ≠ w`,
`w` is `SeparatedBy` (IH-singleton) anchors from `x`, so `plane_count_sep` gives a joint-count difference and
`ReadsSingletonCounts` a colour difference — contradiction. -/
theorem colorSingleton_of_mem_pinIter {Q : QuadraticForm K (Fin d → K)} [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    {C : (Fin d → K) → γ} {W : Set (Fin d → K)} {a b : Fin d → K}
    (hReadC : ReadsSingletonCounts C Q)
    (hcompl : SeparatesPlaneFromComplement C W)
    (hbaseIndiv : ∀ w ∈ seed a b, IsColorSingleton C w) :
    ∀ n, ∀ w ∈ pinIter Q W a b n, IsColorSingleton C w := by
  intro n
  induction n with
  | zero => exact hbaseIndiv
  | succ k ih =>
      intro w hw
      simp only [pinIter, pinStep, Set.mem_union, Set.mem_setOf_eq] at hw
      rcases hw with hk | hfresh
      · exact ih w hk
      · -- w ∈ W, separated (by pinIter k anchors) from every other point of W
        obtain ⟨hwW, hsep⟩ := hfresh
        intro x hcx
        by_cases hxW : x ∈ W
        · by_contra hxw
          -- x ∈ W, x ≠ w: use the separation certificate
          obtain ⟨t, htP, t₀, ht₀P, ⟨hIw, hIx, hQw, hQx⟩, hchi⟩ := hsep x hxW hxw
          have hcount : jointIsoCountK Q w {t, t₀} ≠ jointIsoCountK Q x {t, t₀} :=
            plane_count_sep Q hF hcardK hd hψ vb hv hw w x t t₀ hIw hIx hQw hQx hchi
          exact hcount (hReadC.reads t t₀ (ih t htP) (ih t₀ ht₀P) w x hcx.symm)
        · exact absurd hcx (hcompl w hwW x hxW)

/-- **★ Reduce "`C` pins `W`" to `PlanePinnable` + the two interfaces + the residual.** If the pinning closure reaches all
of `W` (`PlanePinnable`), `C` reads singleton counts, plane points are colour-separated from the complement, and the base
is individualised, then every plane point is a colour-singleton — `C` pins `W`. Chaining with the Core (`colorEq_iff_stabOrbit`)
gives `bᵢ=1` end-to-end. -/
theorem pinsPlane_of_planePinnable {Q : QuadraticForm K (Fin d → K)} [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    {C : (Fin d → K) → γ} {W : Set (Fin d → K)} {a b : Fin d → K}
    (hReadC : ReadsSingletonCounts C Q)
    (hcompl : SeparatesPlaneFromComplement C W)
    (hbaseIndiv : ∀ w ∈ seed a b, IsColorSingleton C w)
    (hpin : PlanePinnable Q W a b) :
    ∀ w ∈ W, IsColorSingleton C w := by
  intro w hwW
  obtain ⟨n, hn⟩ := hpin w hwW
  exact colorSingleton_of_mem_pinIter hF hcardK hd hψ vb hv hw hReadC hcompl hbaseIndiv n w hn

end Bridge

end ChainDescent.WLWiring
