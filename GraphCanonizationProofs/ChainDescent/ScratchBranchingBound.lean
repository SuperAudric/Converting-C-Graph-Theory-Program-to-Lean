/-
# Phase 2 — the a-priori branching bound `bᵢ ≤ |K|^{|S|+1}` (recovery route T0, forms graph)

**What this module builds.** The recovery route's Phase 2 (`docs/chain-descent-recovery-route.md` §6) must discharge the
Phase-1 bridge's carried hypotheses for the affine-polar forms graph: the branching factor `bᵢ = #{Stab(S)-orbits in the
selected cell}` is `≤ B`. This module lands the **foundational reduction** — orbits inject into exact-Gram profiles — and
the resulting **unconditional a-priori bound**

  `#{Stab(S)-orbits} ≤ |K|^{|S|+1}`.

**Why this is the right foundation.** By Witt (`WittExtendsToOrbit`, carried), two vertices with the same exact Gram
profile `(Q t, (polar Q t s)_{s∈S})` are `Stab(S)`-orbit-equivalent, so the orbits are *at most* the distinct Gram
profiles, of which there are `≤ |K| · |K|^{|S|} = |K|^{|S|+1}`. This is exactly the branching bound the Phase-1
`certifiedBoundedTree_of_disposition` consumes as `degBound`, with `B = |K|^{|S|+1}`.

**Honest scope — this is the QUASIPOLY tier, not yet poly.** `B = |K|^{|S|+1}` with `|S| = O(d)` gives
`leaves ≤ Bᴸ = |K|^{O(d²)}` = quasipolynomial — matching the *banked* seal, now re-derived **through the recovery
bridge**, unconditionally (modulo Witt). The **polynomial** target `B ≤ poly(q)` is the strictly sharper statement that
the *selected cell* (a fixed refinement class) cuts the `|K|^{|S|}` profiles down to `poly(q)` — the WL-orbit defect, the
open research crux (§Phase 2 leads: δ′, Skresanov, the counting/Gauss machinery). This module makes that crux precise:
poly ⟺ [per-cell profile count ≤ poly(q)], a genuine restriction of the a-priori bound proved here.

Reuses the geometric model of the demoted CellsAreOrbits route (`Similitude`/`StabOrbit`/`SameExactGram`, all
axiom-clean): soundness (`stabOrbit_imp_sameExactGram_of_anisotropic`) and the carried `WittExtendsToOrbit`.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchWallKernel

namespace ChainDescent.BranchingBound

open ChainDescent.OrbitBaseCase ChainDescent.Wall QuadraticMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  {Q : QuadraticForm K V}

/-- The **exact-Gram profile** of `t` relative to a finite base `S`: its norm together with its polar pairings against
each base point. Two vertices share a profile iff they have the same exact Gram data (`SameExactGram`). -/
def gramProfile (Q : QuadraticForm K V) (S : Finset V) (t : V) : K × (S → K) :=
  (Q t, fun s => QuadraticMap.polar Q t s.1)

/-- Equal profiles ⟺ equal exact Gram data (unfolding the subtype quantifier to `∀ s ∈ S`). -/
theorem gramProfile_eq_iff {S : Finset V} {t t' : V} :
    gramProfile Q S t = gramProfile Q S t' ↔ SameExactGram Q (↑S : Set V) t t' := by
  unfold gramProfile SameExactGram
  rw [Prod.mk.injEq]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h s hs
    exact congrFun h ⟨s, hs⟩
  · intro h
    funext s
    exact h s.1 s.2

/-- The number of distinct exact-Gram profiles relative to `S` is `≤ |K|^{|S|+1}`. -/
theorem card_gramProfiles_le (S : Finset V) :
    (Finset.univ.image (gramProfile Q S)).card ≤ Fintype.card K ^ (S.card + 1) := by
  calc (Finset.univ.image (gramProfile Q S)).card
      ≤ Fintype.card (K × (S → K)) := Finset.card_le_univ _
    _ = Fintype.card K * Fintype.card K ^ S.card := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe]
    _ = Fintype.card K ^ (S.card + 1) := by rw [pow_succ, Nat.mul_comm]

/-- **★ The a-priori branching bound (Phase 2 foundation).** Modulo Witt extension (`hWitt`), the whole vertex set is
covered by `≤ |K|^{|S|+1}` `Stab(S)`-orbit representatives — so the branching factor `bᵢ` at base `S` is
`≤ |K|^{|S|+1}`. This discharges the Phase-1 bridge's `degBound` at the **quasipoly** tier (`B = |K|^{|S|+1}`,
unconditional in the base); the polynomial target sharpens `B` to `poly(q)` per cell (the open crux). -/
theorem stabOrbit_cover_card_le (S : Finset V) (hWitt : WittExtendsToOrbit Q (↑S : Set V)) :
    ∃ reps : Finset V, reps.card ≤ Fintype.card K ^ (S.card + 1) ∧
      ∀ t : V, ∃ r ∈ reps, StabOrbit Q (↑S : Set V) r t := by
  classical
  -- one representative per attained profile
  set P := Finset.univ.image (gramProfile Q S) with hP
  have hattain : ∀ p ∈ P, ∃ t : V, gramProfile Q S t = p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨t, _, ht⟩
    exact ⟨t, ht⟩
  choose rep hrep using hattain
  refine ⟨P.attach.image (fun p => rep p.1 p.2), ?_, ?_⟩
  · calc (P.attach.image (fun p => rep p.1 p.2)).card
        ≤ P.attach.card := Finset.card_image_le
      _ = P.card := Finset.card_attach
      _ ≤ Fintype.card K ^ (S.card + 1) := card_gramProfiles_le S
  · intro t
    have hpt : gramProfile Q S t ∈ P := Finset.mem_image_of_mem _ (Finset.mem_univ t)
    refine ⟨rep (gramProfile Q S t) hpt, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨gramProfile Q S t, hpt⟩, Finset.mem_attach _ _, rfl⟩
    · -- same profile ⟹ same Gram ⟹ (Witt) same orbit
      have hprof : gramProfile Q S (rep (gramProfile Q S t) hpt) = gramProfile Q S t :=
        hrep (gramProfile Q S t) hpt
      exact hWitt _ _ (gramProfile_eq_iff.mp hprof)

end ChainDescent.BranchingBound
