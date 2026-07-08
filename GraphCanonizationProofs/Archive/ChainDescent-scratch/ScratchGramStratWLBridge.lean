/-
# Route A, Step C — Piece 2: the WL bridge `SameClassCounts → SameGramStratCounts`

**What this module builds (recovery doc §9.7, Piece 2).** Piece 1 proved the round-3 *gram-stratified* observable resolves
cells to orbits (`SameGramStratCounts ↔ StabOrbit`, modulo the Witt citation). Piece 2 connects it to the observable the
*canonizer actually computes* — the 1-WL colour-class counts (`SameClassCounts`, `ScratchWLClassCounts`). The bridge:

  **`sameGramStratCounts_of_sameClassCounts`** — if the colouring `C` **refines `gramK`** (`ColorRefinesGramK`: equal
  colour ⟹ equal exact Gram to `{a,b}`), then `SameClassCounts C Q u u' → SameGramStratCounts Q a b u u'`.

**Why the refinement hypothesis is the right (and necessary) residual.** With a trivial colouring `SameClassCounts`
sees only the isotropy degree, far coarser than the gram-strat count, so *some* fineness hypothesis on `C` is
unavoidable. `ColorRefinesGramK` is exactly it: `{z : gramK z = g}` is then a union of colour classes, so
`gramStratCount u g = ∑_{c a g-colour} (classCount u c 0 + classCount u c 1)` (isotropy `Q(u−z)=0 ⟺ iso3∈{0,1}`), a
`u`-independent sum of class-counts — equal for `u,u'` under `SameClassCounts`. `ColorRefinesGramK` holds for the stable
colouring `C∞ = orbits` (orbits refine gramK, by soundness), and is *weaker* than the goal `C∞ = orbits`; it is the clean
WL-dimension residual (the canonizer's colouring separating exact Gram to the individualized base).

**Capstone `colorEq_iff_stabOrbit_wittOnly`**: composing with Piece 1's `gramCountsEq_iff_stabOrbit_wittOnly`, the WL
colour cells coincide with the `Stab({a,b})`-orbits (`bᵢ=1`) modulo `{ColorRefinesGramK, IsWLStable, ObsInvariant,
RefinedWittExtends}` — the Gauss content fully discharged, `hψ` constructed. (Even ambient dimension; the odd case awaits
an extension of the closed form `isoConeSum_eval_even`.)

Reuses `ScratchGramStratCount` (`gramStratCount`), `ScratchWLClassCounts` (`classCount`/`SameClassCounts`/`iso3`/
`IsWLStable`), `ScratchGramStratConeSep` (Piece 1 capstone), `ScratchSpanDim2Recovery` (`ObsInvariant`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratConeSep
import ChainDescent.ScratchWLClassCounts

namespace ChainDescent.GramStrat

open QuadraticMap ChainDescent.WLClassCounts ChainDescent.OrbitBaseCase ChainDescent.SpanDim2Recovery

set_option linter.unusedSectionVars false

variable {K V γ : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [DecidableEq γ]
  {Q : QuadraticForm K V}

/-- **The colouring refines the exact Gram to `{a,b}`** — equal colour forces equal `gramK`. The (necessary) fineness
hypothesis of the WL bridge; holds for the stable colouring `C∞ = orbits` and is weaker than `C∞ = orbits`. -/
def ColorRefinesGramK (C : V → γ) (Q : QuadraticForm K V) (a b : V) : Prop :=
  ∀ z z' : V, C z = C z' → gramK Q a b z = gramK Q a b z'

/-- **Piece 2 — the WL bridge.** If `C` refines `gramK`, equal 1-WL class-count profiles give equal gram-stratified
count profiles. -/
theorem sameGramStratCounts_of_sameClassCounts {C : V → γ} {a b : V}
    (hrefine : ColorRefinesGramK C Q a b) {u u' : V} (h : SameClassCounts C Q u u') :
    SameGramStratCounts Q a b u u' := by
  classical
  -- Q(w−z)=0 ⟺ iso3(w−z) ∈ {0,1}
  have hiso : ∀ (w z : V), Q (w - z) = 0 ↔ (iso3 Q (w - z) = 0 ∨ iso3 Q (w - z) = 1) := by
    intro w z
    rcases eq_or_ne (w - z) 0 with h0 | h0
    · rw [h0]; simp [iso3]
    · rcases eq_or_ne (Q (w - z)) 0 with hq | hq <;> simp [iso3, h0, hq]
  -- card of the isotropic-to-w part of a colour class = classCount·0 + classCount·1
  have hsplit : ∀ (w : V) (c : γ),
      (Finset.univ.filter (fun z => C z = c ∧ Q (w - z) = 0)).card
        = classCount C Q w c 0 + classCount C Q w c 1 := by
    intro w c
    unfold classCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hiso w z]; tauto
    · rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [Finset.mem_filter] at hz1 hz2
      exact absurd (hz1.2.2.symm.trans hz2.2.2) (by decide)
  intro g
  set G := (Finset.univ.filter (fun z => gramK Q a b z = g)).image C with hG
  -- gramK z = g ⟺ C z ∈ G
  have hequiv : ∀ z : V, gramK Q a b z = g ↔ C z ∈ G := by
    intro z
    constructor
    · intro hz
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩
    · intro hz
      obtain ⟨z', hz', hCz'⟩ := Finset.mem_image.mp hz
      rw [hrefine z z' hCz'.symm]
      exact (Finset.mem_filter.mp hz').2
  have hrw : ∀ w : V, gramStratCount Q a b w g
      = ∑ c ∈ G, (classCount C Q w c 0 + classCount C Q w c 1) := by
    intro w
    unfold gramStratCount
    rw [Finset.filter_congr (fun z _ => by rw [hequiv z] : ∀ z ∈ Finset.univ,
      (gramK Q a b z = g ∧ Q (w - z) = 0) ↔ (C z ∈ G ∧ Q (w - z) = 0))]
    rw [Finset.card_eq_sum_card_fiberwise
      (fun z hz => (Finset.mem_filter.mp hz).2.1 : ∀ z ∈ _, C z ∈ G)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.filter_filter]
    rw [Finset.filter_congr (fun z _ => by
      constructor
      · rintro ⟨⟨_, hQ⟩, hCc⟩; exact ⟨hCc, hQ⟩
      · rintro ⟨hCc, hQ⟩; exact ⟨⟨by rw [hCc]; exact hc, hQ⟩, hCc⟩ :
        ∀ z ∈ Finset.univ, ((C z ∈ G ∧ Q (w - z) = 0) ∧ C z = c) ↔ (C z = c ∧ Q (w - z) = 0))]
    exact hsplit w c
  rw [hrw u, hrw u']
  exact Finset.sum_congr rfl (fun c _ => by rw [h c 0, h c 1])

/-- **★★ ASSEMBLY CAPSTONE — the WL colour cells ARE the orbits (`bᵢ=1`), modulo colouring properties + the Witt
citation.** Composing Piece 2 (the WL bridge) with Piece 1's fully-discharged Gauss capstone: at a `GoodBase` of even
ambient dimension, for a refinement-invariant, 1-WL-stable colouring `C` that refines `gramK`, the WL colour equality is
*exactly* the `Stab({a,b})`-orbit relation: **`C u = C u' ↔ StabOrbit`**. The entire Gauss/analytic content is proved
axiom-clean (`hψ` constructed); the residual is `{ColorRefinesGramK, IsWLStable, ObsInvariant}` (colouring properties,
`ColorRefinesGramK` = the WL-dimension residual) + `RefinedWittExtends` (Witt citation). Even dim only (odd = future). -/
theorem colorEq_iff_stabOrbit_wittOnly [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    [FiniteDimensional K V] {C : V → γ} {a b : V} (hbase : GoodBase Q a b)
    (heven : Even (Module.finrank K V)) (hinv : ObsInvariant C Q ({a, b} : Set V))
    (hstable : IsWLStable C Q) (hrefine : ColorRefinesGramK C Q a b)
    (hwitt : RefinedWittExtends Q a b) {u u' : V} :
    C u = C u' ↔ StabOrbit Q ({a, b} : Set V) u u' := by
  constructor
  · intro hc
    exact (gramCountsEq_iff_stabOrbit_wittOnly hF hbase heven hwitt).mp
      (sameGramStratCounts_of_sameClassCounts hrefine (hstable u u' hc))
  · intro ho
    obtain ⟨g, hfix, hgu⟩ := ho
    rw [← hgu]; exact (hinv g hfix u).symm

end ChainDescent.GramStrat
