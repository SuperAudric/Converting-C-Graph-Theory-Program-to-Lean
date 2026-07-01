/-
# The span-dim-1 orbit-multiplicity bound `bᵢ ≤ q²` (recovery route ITEM B, the provable half)

**What this module builds.** The non-vacuity probe (`forced_triangle_mult.py`, 2026-07-01) found the recovery route's
per-cell orbit multiplicity `bᵢ = #{Stab(S)-orbits in the selected cell}` is `≤ q(q−1)/2 = Θ(q²)` — POLY — and occurs at
**exactly one** base level: the **span-dimension-1** transition (`|S|=2`, `span S` a line). This module proves the
**upper half** of that, unconditionally (mod Witt): at a base whose span lies in a **line** `K·a`, the branching factor
is `bᵢ ≤ q²`.

**The mechanism (why it is provable, and why only here).** Phase 2's `stabOrbit_cover_card_le` bounds orbits by
`|K|^{|S|+1}` via the exact-Gram profile `(Q t, (polar Q t s)_{s∈S})`. When `span S ⊆ K·a`, the polar part collapses:
`polar Q t` is **linear**, so `polar Q t s = c_s · polar Q t a` for `s = c_s·a` — the whole `S`-profile is determined by
the single scalar `polar Q t a`. So the profile reduces to `(Q t, polar Q t a) ∈ K × K`, giving `≤ q²` orbits regardless
of `|S|`. This is the a-priori `|K|^{|S|+1}` sharpened to `|K|^{finrank(span S)+1}` at `finrank = 1`. It is poly precisely
because the span is bounded — the general level has `span S` of dimension `O(d)` and the bound degrades to quasipoly
(the a-priori tier), which is why the poly conclusion needs the **concentration** (below), not this bound alone.

**Honest scope — this is the provable half; the open half is the concentration.** `leaves = ∏ᵢ bᵢ`. This module bounds
`bᵢ ≤ q²` at the span-dim-1 level(s). To get `leaves ≤ poly` one composes (via `leaves_le_prod_concentrated`,
`ScratchBoundedMultLeaves`) with the **carried, probe-validated** fact that branching is *confined* to `O(1)` such levels
(`bᵢ = 1` at span-dim `≥ 2` — `CellsAreOrbits` off span-dim-1, the cell-discretisation / WL-orbit defect). That
concentration is the remaining open content; this bound makes the *branching-level factor* poly, unconditionally.

Reuses `ScratchBranchingBound` (`SameExactGram`/`StabOrbit`/`WittExtendsToOrbit`, the cover pattern of
`stabOrbit_cover_card_le`). Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchBranchingBound

namespace ChainDescent.SpanDimBound

open ChainDescent.OrbitBaseCase ChainDescent.Wall QuadraticMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  {Q : QuadraticForm K V}

/-- **Polar collapses on a line.** For `s ∈ span{a}` (so `s = c·a`), `polar Q t s = c · polar Q t a` — hence two
vertices agreeing on `polar Q · a` agree on `polar Q · s` for every `s ∈ span{a}`. The linearity fact that reduces the
whole span-dim-1 Gram profile to the single scalar `polar Q t a`. -/
theorem polar_eq_of_mem_span_singleton {a t t' : V}
    (ha : QuadraticMap.polar Q t a = QuadraticMap.polar Q t' a)
    {s : V} (hs : s ∈ Submodule.span K ({a} : Set V)) :
    QuadraticMap.polar Q t s = QuadraticMap.polar Q t' s := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  rw [← polarBilin_apply_apply, ← polarBilin_apply_apply, map_smul, map_smul,
      polarBilin_apply_apply, polarBilin_apply_apply, ha]

/-- **★ The span-dim-1 orbit-multiplicity bound.** If every base point lies on a single line `K·a`
(`span S ⊆ K·a`, i.e. `finrank(span S) ≤ 1`), then — modulo Witt — the whole vertex set is covered by `≤ |K|² = q²`
`Stab(S)`-orbit representatives. So the branching factor at a span-dim-1 base is `bᵢ ≤ q²` (POLY), unconditionally.
Sharpens `stabOrbit_cover_card_le`'s `|K|^{|S|+1}` to `|K|²` by collapsing the polar profile onto the line's scalar
`polar Q · a` (`polar_eq_of_mem_span_singleton`). The probe's `bᵢ ≤ q(q−1)/2 < q²` is consistent with this bound. -/
theorem stabOrbit_cover_card_le_line {S : Finset V} {a : V}
    (hline : ∀ s ∈ (↑S : Set V), s ∈ Submodule.span K ({a} : Set V))
    (hWitt : WittExtendsToOrbit Q (↑S : Set V)) :
    ∃ reps : Finset V, reps.card ≤ Fintype.card K ^ 2 ∧
      ∀ t : V, ∃ r ∈ reps, StabOrbit Q (↑S : Set V) r t := by
  classical
  set red : V → K × K := fun t => (Q t, QuadraticMap.polar Q t a) with hred
  set R := Finset.univ.image red with hRdef
  have hattain : ∀ p ∈ R, ∃ t : V, red t = p := by
    intro p hp; rcases Finset.mem_image.mp hp with ⟨t, _, ht⟩; exact ⟨t, ht⟩
  choose rep hrep using hattain
  refine ⟨R.attach.image (fun p => rep p.1 p.2), ?_, ?_⟩
  · calc (R.attach.image (fun p => rep p.1 p.2)).card
        ≤ R.attach.card := Finset.card_image_le
      _ = R.card := Finset.card_attach
      _ ≤ Fintype.card (K × K) := Finset.card_le_univ _
      _ = Fintype.card K ^ 2 := by rw [Fintype.card_prod, pow_two]
  · intro t
    have hpt : red t ∈ R := Finset.mem_image_of_mem red (Finset.mem_univ t)
    refine ⟨rep (red t) hpt, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨red t, hpt⟩, Finset.mem_attach _ _, rfl⟩
    · have hred_eq : red (rep (red t) hpt) = red t := hrep (red t) hpt
      have hQ : Q (rep (red t) hpt) = Q t := congrArg Prod.fst hred_eq
      have hpa : QuadraticMap.polar Q (rep (red t) hpt) a = QuadraticMap.polar Q t a :=
        congrArg Prod.snd hred_eq
      exact hWitt _ _ ⟨hQ, fun s hs => polar_eq_of_mem_span_singleton hpa (hline s hs)⟩

end ChainDescent.SpanDimBound
