/-
# Route A, Step C — the round-3 gram-stratified observable + the K-non-degeneracy crux (Piece 1a)

**What this module builds (recovery doc §9.7, β1/hybrid; the round-3 probe `round3_probe.py`).** The probe showed the
round-3 mechanism — *count `z` isotropic-to-`u`, stratified by `z`'s exact Gram to the base* — separates the `Stab`-orbits
**exactly and form-independently** (`T`-classes `= #orbits`, both `VO^±`). This module lands the **clean statement of that
observable** and the **K-non-degeneracy crux**, with soundness proved.

**★ Why this targets the ORBIT directly (not `SameExactGram Q {a,b}` + Witt).** The base `{a,b}` spans only the 2-plane
`W`; the `Stab({a,b})`-orbit is *finer* than `SameExactGram Q {a,b}` (probe: `#orbits = 36 > 27 =` #gram-classes at
`VO^ε₄(3)`), because the exact Gram to `{a,b}` cannot tell a plane-vertex (`u_⊥ = 0`, a singleton orbit by
`stab_fixes_span`) from a nonzero-isotropic-complement vertex (`u_⊥ ≠ 0`, `Q u_⊥ = 0`) — both have `Q u_⊥ = 0`. So
`WittExtendsToOrbit Q {a,b}` is **false**, and the `SameExactGram`+Witt route is vacuous at this base. The round-3
observable *does* see the complement (its character-sum depends on `u`'s **dual** Gram — recovery doc §9.7 (5)), so it
reaches the orbit. Hence the crux is phrased `SameGramStratCounts ⟹ StabOrbit` **directly**.

* `gramK Q a b u = (Q u, polar Q u a, polar Q u b)` — `u`'s exact Gram to the base `{a,b}` (the `z`-stratifier).
* `gramStratCount Q a b u g = #{z : gramK z = g ∧ Q (u − z) = 0}` — the round-3 count of `z` isotropic-to-`u` in
  Gram-stratum `g`; `SameGramStratCounts` the induced relation.
* **`sameGramStratCounts_of_stabOrbit`** — SOUNDNESS (free): a base-fixing isometry (`μ = 1` at the anisotropic base)
  reindexes the count, so orbit-related vertices share the profile.
* **`GramCountsRecoverOrbit`** — the CRUX (K-non-degeneracy): `SameGramStratCounts ⟹ StabOrbit`. Piece 1b/1c(i)/1c(ii)
  build the character-sum machinery (`ScratchGramStratCharSum`/`Eval`/`Invert`); **Piece 1c(iii) (`ScratchGramStratOrbit`)
  REDUCES this crux to two named predicates** — the open Gauss lemma `GramCountsRecoverGram` (probe-true) + the carried
  known-true `RefinedWittExtends`. Discharge `GramCountsRecoverGram` (via the g-profile transform + inner-sum evals) to
  close the crux.
* **`gramCountsEq_iff_stabOrbit`** — capstone: soundness + crux ⟹ **`SameGramStratCounts u u' ↔ StabOrbit`** = `bᵢ = 1`
  for the round-3 observable (no Witt detour).

Reuses `ScratchWallKernel`/`ScratchOrbitBaseCase` (`Similitude`, `StabOrbit`, `mult_eq_one_of_fixes_anisotropic`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchWallKernel

namespace ChainDescent.GramStrat

open QuadraticMap ChainDescent.OrbitBaseCase ChainDescent.Wall

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **`u`'s exact Gram to the base `{a,b}`** — the stratifier for `z` in the round-3 count. -/
def gramK (Q : QuadraticForm K V) (a b u : V) : K × K × K :=
  (Q u, QuadraticMap.polar Q u a, QuadraticMap.polar Q u b)

/-- **The round-3 gram-stratified count:** `#{z : gram(z) = g ∧ Q(u − z) = 0}` — count `z` isotropic-to-`u` in Gram
stratum `g`. (Genuine `DecidableEq K`-based `DecidablePred`, not `Classical`, so the count's filter shares its
decidability instance with the `GaussCount` toolkit — needed for the Piece 1b character-sum identity.) -/
noncomputable def gramStratCount (Q : QuadraticForm K V) (a b u : V) (g : K × K × K) : ℕ :=
  (Finset.univ.filter (fun z => gramK Q a b z = g ∧ Q (u - z) = 0)).card

/-- **The round-3 observable relation:** equal gram-stratified count profiles. -/
def SameGramStratCounts (Q : QuadraticForm K V) (a b u u' : V) : Prop :=
  ∀ g, gramStratCount Q a b u g = gramStratCount Q a b u' g

/-- A `μ=1` similitude (isometry) preserves the polar form. -/
theorem polar_isometry (g : Similitude Q) (hμ : g.mult = 1) (x y : V) :
    QuadraticMap.polar Q (g.toLinearEquiv x) (g.toLinearEquiv y) = QuadraticMap.polar Q x y := by
  have hQ : ∀ v, Q (g.toLinearEquiv v) = Q v := fun v => by rw [g.map, hμ, one_mul]
  simp only [QuadraticMap.polar]
  rw [← map_add, hQ, hQ, hQ]

/-- A base-fixing isometry preserves `gramK` (fixes `a, b`, preserves `Q` and `polar`). -/
theorem gramK_isometry (g : Similitude Q) (hμ : g.mult = 1) {a b : V}
    (hga : g.toLinearEquiv a = a) (hgb : g.toLinearEquiv b = b) (w : V) :
    gramK Q a b (g.toLinearEquiv w) = gramK Q a b w := by
  have hQ : Q (g.toLinearEquiv w) = Q w := by rw [g.map, hμ, one_mul]
  have h2 : QuadraticMap.polar Q (g.toLinearEquiv w) a = QuadraticMap.polar Q w a := by
    conv_lhs => rw [← hga]
    rw [polar_isometry g hμ]
  have h3 : QuadraticMap.polar Q (g.toLinearEquiv w) b = QuadraticMap.polar Q w b := by
    conv_lhs => rw [← hgb]
    rw [polar_isometry g hμ]
  simp only [gramK, hQ, h2, h3]

/-- **★ Soundness (FREE) — orbit ⟹ same gram-strat count profile.** A base-fixing similitude has multiplier `1` (the
anisotropic delimiter), so it is an isometry; reindexing the count by `z ↦ g z` (a bijection preserving `gramK` and
`Q(·−·)`) shows orbit-related vertices share the profile. So the round-3 cells are unions of orbits. -/
theorem sameGramStratCounts_of_stabOrbit {a b : V} (ha : Q a ≠ 0) {u u' : V}
    (h : StabOrbit Q ({a, b} : Set V) u u') : SameGramStratCounts Q a b u u' := by
  obtain ⟨g, hfix, hgu⟩ := h
  have hamem : a ∈ ({a, b} : Set V) := Set.mem_insert _ _
  have hbmem : b ∈ ({a, b} : Set V) := Set.mem_insert_of_mem _ rfl
  have hga : g.toLinearEquiv a = a := hfix a hamem
  have hgb : g.toLinearEquiv b = b := hfix b hbmem
  have hμ : g.mult = 1 := mult_eq_one_of_fixes_anisotropic g ha hga
  have hQ : ∀ v, Q (g.toLinearEquiv v) = Q v := fun v => by rw [g.map, hμ, one_mul]
  intro gg
  rw [← hgu]
  unfold gramStratCount
  rw [← Finset.card_map (g.toLinearEquiv.toEquiv.toEmbedding)]
  congr 1
  ext z
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_toEmbedding, LinearEquiv.coe_toEquiv]
  constructor
  · rintro ⟨w, ⟨hgw, hqw⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [gramK_isometry g hμ hga hgb]; exact hgw
    · rw [← map_sub, hQ]; exact hqw
  · rintro ⟨hgz, hqz⟩
    refine ⟨g.toLinearEquiv.symm z, ⟨?_, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    · rw [← gramK_isometry g hμ hga hgb, LinearEquiv.apply_symm_apply]; exact hgz
    · rw [← hQ, map_sub, LinearEquiv.apply_symm_apply]; exact hqz

/-- **★ THE CRUX (K-non-degeneracy) — the round-3 count profile RECOVERS the orbit.** Equal gram-stratified count
profiles ⟹ same `Stab({a,b})`-orbit. This is the open Gauss content (recovery doc §9.7 (5)): the profile determines `u`'s
dual Gram (which sees the complement `W^⊥`), and the dual Gram determines the orbit — a Fourier non-degeneracy of the
`𝟙[isotropic]×gram` transfer kernel. Probe-true (`round3_probe.py`: `T`-classes `= #orbits`, form-independent). -/
def GramCountsRecoverOrbit (Q : QuadraticForm K V) (a b : V) : Prop :=
  ∀ u u' : V, SameGramStratCounts Q a b u u' → StabOrbit Q ({a, b} : Set V) u u'

/-- **★ Capstone — the round-3 observable's cells ARE the orbits (`bᵢ = 1`), modulo the crux.** Soundness + the
K-non-degeneracy crux give `SameGramStratCounts u u' ↔ StabOrbit`. Targets the orbit **directly** — no `SameExactGram`
detour, so it is not vacuous at the span-dim-2 base (where `WittExtendsToOrbit Q {a,b}` fails). -/
theorem gramCountsEq_iff_stabOrbit {a b : V} (ha : Q a ≠ 0)
    (hcrux : GramCountsRecoverOrbit Q a b) {u u' : V} :
    SameGramStratCounts Q a b u u' ↔ StabOrbit Q ({a, b} : Set V) u u' :=
  ⟨hcrux u u', sameGramStratCounts_of_stabOrbit ha⟩

end ChainDescent.GramStrat
