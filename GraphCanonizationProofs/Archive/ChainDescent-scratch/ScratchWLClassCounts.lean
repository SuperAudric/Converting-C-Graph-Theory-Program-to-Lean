/-
# Route A, Step C — the CORRECT observable: iterated 1-WL by colour-CLASS counts (replaces the refuted `PlanePinnable`)

**Why this module exists — a probe-driven correction (2026-07-02).** The Route α line
(`ChiProfileSeparatesPlane` → `PlanePinnable`) tried to reach `bᵢ=1` by **pinning the plane points** via `χ(pairForm)`
profiles to *pinned singleton anchors*. A probe (`scratchpad/pin_probe.py`) shows this **STALLS**: the singleton-anchor
closure pins only the 3-point base for every `q ≥ 5`, and plane-internal 1-WL stalls at 4 colour classes. So
`PlanePinnable` (via the singleton `PinClosure`) is **FALSE for `q ≥ 5`** — plane-point pinning is the wrong mechanism.

What actually delivers `bᵢ=1` (`recovery_depth_probe.py`, confirmed 2026-07-02): **ambient 1-WL refining by counts to
colour CLASSES** recovers the exact-Gram orbits in `r*∈{3,4}` rounds, flat in `d`. This matches the standing note in
`ScratchWallKernel` ("`WallKernel`/single-round is refuted at a bounded base; the crack is the *iterated* observable").
The missing power is **class counts** (count `z` in each evolving colour class), not counts to a few fixed singletons.

This module lands the correct observable and slots it into the existing `WallKernelFor Obs` abstraction:

* `iso3` — the 3-valued isotropy relation over abstract `V` (self / isotropic / anisotropic) = what 1-WL sees.
* `classCount C Q u c k` — `#{z : C z = c ∧ iso3 Q (u−z) = k}`: the 1-WL neighbourhood count of colour `c` at relation
  `k`. `SameClassCounts C Q` — the induced "equal class-count profile" relation, a graph-refinement **invariant**
  (`sameClassCounts_of_stabOrbit`, soundness FREE via `iso3` similitude-invariance).
* `IsWLStable C Q` — `C` is 1-WL-stable/equitable (equal colour ⟹ equal class-count profile), the fixpoint property of
  the stable colouring `C^∞`. Carried (a property of the actual WL colouring).
* **`ClassCountsSeparateGram C Q S`** — the CORRECT open predicate (the frontier): the class-count profile separates the
  exact Gram to `S`. This is `WallKernelFor (SameClassCounts C Q) Q S` — the *iterated* instance `ScratchWallKernel` asked
  for. **TRUE** (probe: cells = orbits), *replacing* the false `PlanePinnable`.
* **`wallKernel_of_wlStable`** / **`colorEq_iff_stabOrbit`** — the reduction: `IsWLStable` + `ClassCountsSeparateGram`
  (+ `ObsInvariant C` + Witt) ⟹ **`C u = C u' ↔ StabOrbit`, `bᵢ=1`** for the WL colouring, via the scaffold
  `obsEq_iff_stabOrbit`.

**Net:** `bᵢ=1` now reduces to the single honest predicate `ClassCountsSeparateGram` on the **correct (class-count)
mechanism** — probe-true, unlike the plane-pinning target. Proving it is the WL-dimension frontier (the seal's
per-anchor + union assembly, now against colour classes rather than singleton anchors).

Reuses `ScratchWallKernel` (`WallKernelFor`/`SameExactGram`/`WittExtendsToOrbit`), `ScratchSpanDim2Recovery`
(`ObsInvariant`/`obsEq_iff_stabOrbit`), `ScratchOrbitBaseCase` (`Similitude`/`StabOrbit`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchWallKernel
import ChainDescent.ScratchSpanDim2Recovery

namespace ChainDescent.WLClassCounts

open QuadraticMap ChainDescent.Wall ChainDescent.OrbitBaseCase ChainDescent.SpanDim2Recovery

set_option linter.unusedSectionVars false

variable {K V γ : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [DecidableEq γ]
  {Q : QuadraticForm K V}

/-- **The 3-valued isotropy relation over `V`** (what 1-WL sees on the forms graph): `0` (self, `v=0`), `1` (isotropic,
`Q v = 0`, `v≠0`), `2` (anisotropic). The abstract-`V` analogue of `isoClassK`. -/
noncomputable def iso3 (Q : QuadraticForm K V) (v : V) : Fin 3 :=
  if v = 0 then 0 else if Q v = 0 then 1 else 2

/-- A similitude preserves `iso3` (it fixes `0`, and scales `Q` by a nonzero multiplier so preserves `Q(·)=0`). -/
theorem iso3_similitude (g : Similitude Q) (v : V) : iso3 Q (g.toLinearEquiv v) = iso3 Q v := by
  unfold iso3
  have hz : g.toLinearEquiv v = 0 ↔ v = 0 := by
    rw [map_eq_zero_iff _ (g.toLinearEquiv.injective)]
  have hq : Q (g.toLinearEquiv v) = 0 ↔ Q v = 0 := by
    rw [g.map]; exact mul_eq_zero.trans (or_iff_right g.mult_ne)
  by_cases h0 : v = 0
  · simp [h0]
  · rw [if_neg h0, if_neg (fun h => h0 (hz.mp h))]
    by_cases hqv : Q v = 0
    · rw [if_pos hqv, if_pos (hq.mpr hqv)]
    · rw [if_neg hqv, if_neg (fun h => hqv (hq.mp h))]

open scoped Classical in
/-- **The 1-WL neighbourhood count of colour `c` at relation `k`:** `#{z : C z = c ∧ iso3 Q (u − z) = k}`. Counting `z`
against a whole colour *class* (`C z = c`) — the power the singleton-anchor closure lacked. -/
noncomputable def classCount (C : V → γ) (Q : QuadraticForm K V) (u : V) (c : γ) (k : Fin 3) : ℕ :=
  (Finset.univ.filter (fun z => C z = c ∧ iso3 Q (u - z) = k)).card

/-- **The class-count profile relation.** `u, u'` have equal 1-WL class-count profiles. A graph-refinement invariant
(`sameClassCounts_of_stabOrbit`); the *iterated* observable `ScratchWallKernel` calls for. -/
def SameClassCounts (C : V → γ) (Q : QuadraticForm K V) (u u' : V) : Prop :=
  ∀ c k, classCount C Q u c k = classCount C Q u' c k

/-- **`C` is 1-WL-stable (equitable).** Equal colour ⟹ equal class-count profile — the fixpoint property of the stable
colouring `C^∞`. Carried as a property of the actual WL colouring (like the seal carries Witt). -/
def IsWLStable (C : V → γ) (Q : QuadraticForm K V) : Prop :=
  ∀ u u', C u = C u' → SameClassCounts C Q u u'

/-- **★ THE CORRECT OPEN PREDICATE (the frontier) — the class-count profile separates the exact Gram.** This is
`WallKernelFor (SameClassCounts C Q) Q S` — the *iterated / colour-class* instance of the wall kernel. **TRUE** (probe:
`recovery_depth_probe` gives cells = orbits at a span-dim-2 base in `r*∈{3,4}` rounds), *replacing* the FALSE
singleton-anchor `PlanePinnable`. Proving it is the WL-dimension frontier — the seal's per-anchor + union assembly, now
run against colour classes. -/
def ClassCountsSeparateGram (C : V → γ) (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ u u', SameClassCounts C Q u u' → SameExactGram Q S u u'

/-- `ClassCountsSeparateGram` is literally `WallKernelFor` for the class-count observable — the intended instance. -/
theorem wallKernelFor_sameClassCounts {C : V → γ} {S : Set V} (h : ClassCountsSeparateGram C Q S) :
    WallKernelFor (SameClassCounts C Q) Q S := h

/-- **★ Stable `C` + class-count separation ⟹ the colour-equality wall kernel.** `C u = C u'` ⟹ (`IsWLStable`) equal
class-count profile ⟹ (`ClassCountsSeparateGram`) equal exact Gram. -/
theorem wallKernel_of_wlStable {C : V → γ} {S : Set V} (hstable : IsWLStable C Q)
    (hsep : ClassCountsSeparateGram C Q S) :
    WallKernelFor (fun u u' => C u = C u') Q S :=
  fun u u' h => hsep u u' (hstable u u' h)

/-- **★ `bᵢ=1` for the 1-WL-stable colouring — the corrected wiring capstone.** With `C` refinement-invariant
(`ObsInvariant`), 1-WL-stable, its class-count profile separating the exact Gram, and the carried Witt extension, the WL
colour cells coincide *exactly* with the `Stab(S)`-orbits: **`C u = C u' ↔ StabOrbit`**, i.e. `bᵢ=1` — via the scaffold
`obsEq_iff_stabOrbit`. The open content is now the single predicate `ClassCountsSeparateGram` (probe-true), on the
correct colour-class mechanism. -/
theorem colorEq_iff_stabOrbit {C : V → γ} {S : Set V} (hinv : ObsInvariant C Q S)
    (hstable : IsWLStable C Q) (hsep : ClassCountsSeparateGram C Q S) (hWitt : WittExtendsToOrbit Q S)
    {u u' : V} :
    C u = C u' ↔ StabOrbit Q S u u' :=
  obsEq_iff_stabOrbit hinv (wallKernel_of_wlStable hstable hsep) hWitt

/-- **Soundness (FREE) — `SameClassCounts` is a graph invariant.** If `C` is `Stab(S)`-invariant, orbit-related vertices
have equal class-count profiles (a base-fixing similitude permutes `V`, preserving `iso3` and the colouring). So the
class-count cells are always unions of orbits — the easy half; confirms the observable is orbit-sound. -/
theorem sameClassCounts_of_stabOrbit {C : V → γ} {S : Set V} (hinv : ObsInvariant C Q S)
    {u u' : V} (h : StabOrbit Q S u u') : SameClassCounts C Q u u' := by
  obtain ⟨g, hfix, hgu⟩ := h
  intro c k
  -- reindex the count over z ↦ g z (a bijection of V)
  rw [← hgu]
  unfold classCount
  rw [← Finset.card_map (g.toLinearEquiv.toEquiv.toEmbedding)]
  congr 1
  ext z
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_toEmbedding, LinearEquiv.coe_toEquiv]
  constructor
  · rintro ⟨w, ⟨hCw, hkw⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hinv g hfix w]; exact hCw
    · rw [← map_sub, iso3_similitude]; exact hkw
  · rintro ⟨hCz, hkz⟩
    exact ⟨g.toLinearEquiv.symm z, ⟨by rw [← hinv g hfix, LinearEquiv.apply_symm_apply]; exact hCz,
      by rw [← iso3_similitude g, map_sub, LinearEquiv.apply_symm_apply]; exact hkz⟩,
      LinearEquiv.apply_symm_apply _ _⟩

end ChainDescent.WLClassCounts
