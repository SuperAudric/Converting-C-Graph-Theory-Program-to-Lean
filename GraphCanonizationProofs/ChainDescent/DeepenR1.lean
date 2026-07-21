import ChainDescent.DeepenRef

/-!
# `C3b` tranche 2, part V — R1 reduced to one predicate, and the residue isolated

R1 is the reverse half of `SameOrbits deepenRefSupply deepenSupply` (ref orbits ⊆ exec orbits) — the
"the pick is interchangeable" crux. `DeepenRef.wordReach_ref_of_deepen` already has the easy half
(exec ⊆ ref), so `SameOrbits` (and thence ①c, with R2) is one reduction away.

## The reduction

`exec ⊆ ref` as generator sets, so `⟨exec⟩ ⊆ ⟨ref⟩` and `exec`-orbits ⊆ `ref`-orbits (the easy half).
R1 is the converse, and since one containment is free it is equivalent to: **the extra reference
generators merge no `exec`-orbit** — i.e. every reference generator's action is already a *word* in the
executable's verified generators. That is the predicate `DeepenRefInExec` below, and R1 follows from it
by a `WordReach` induction (`wordReach_deepen_of_ref`).

## What this file settles, and what it leaves

* `sameOrbits_of_core` : `(∀ adj χ, DeepenRefInExec adj χ) → SameOrbits deepenRefSupply deepenSupply`.
  So `DeepenRefInExec` is the **entire** residual of R1 — everything else is discharged here.
* `refInExec_of_mem_deepenGens` : a reference generator that is ALSO an executable generator satisfies
  the predicate trivially (one `WordReach` step). So the residue of `DeepenRefInExec` is **exactly the
  reference generators from NON-canonical picks** — the twists the single canonical path does not emit.

## The honest status of `DeepenRefInExec` — scoped to one crisp theorem (2026-07-21)

Unrolled and traced from every angle, R1's core is a single graph-theoretic statement. The trace:

1. `refInExec_of_mem_deepenGens` ⟹ the residue is only the NON-canonical-pick twists.
2. The recorded cell-id sequence is pick-INVARIANT (`DeepenTransport.chooseIdK_transport`): all picks
   individualise the SAME sequence of cells (by id), differing only in WHICH vertex of each id-cell.
3. **★ MEASURED STRUCTURAL FACT (`ScratchDisc`, 2026-07-21): the canonical deepening DISCRETISES THE
   WHOLE GRAPH** on every partially-firing witness — `G8`, `t3`, `wcyc9`, AND `mp7` (all return a fully
   discrete `d1.col`, distinct-colour-count = `n`). So after deepening the graph is RIGID and the twist
   `ρ = χj⁻¹ ∘ χ1` is a genuine automorphism; the branch-cell orbit relation is exactly
   "SOME verified twist connects `r₁, rⱼ`".
4. So R1 ⟺ **"if some anchor-deepen path from `r₁` yields a verified twist to `rⱼ`, the CANONICAL path
   does too (or a word connects them)"** ⟺ (via 2) **"individualising a different member of a fixed
   id-cell, following the canonical id-sequence to discreteness, yields an ISOMORPHIC coloured graph"**
   ⟺ **"the id-cells the deepening picks are `Stab`-orbit-cells"** — i.e. WL-refinement is COMPLETE on
   this graph class (colour-equal deep vertices are automorphic).

That last line is the genuine crux: it is the **harvest / WL-completeness** statement, recorded
CONJECTURAL beyond the abelian regime by the C# side (`docs/chain-descent-linear-oracle.md` §L.4,
"[FIRM behavior, CONJECTURAL characterization]"). Discreteness (3) CONSTRAINS it hard but does not close
it — two discrete deepenings following the same id-sequence are isomorphic iff the differing picks are
`Stab`-related, which is exactly the completeness being asked for. MEASURED to hold on every
partially-firing witness; the all-picks reference is exponential, so larger witnesses cannot be checked.

**Tools in hand for a proof attempt** (unused until deployed, so not yet landed): `twistOf_transport`
specialises at `σ = g ∈ Aut` (via `Consume.IsColAut.relabel`/`.transport`, both existing) to
`twistOf_conj` — the twist conjugates under an automorphism ON THE SAME GRAPH — which is the conjugation
half of "picks related by `g ∈ Aut` give conjugate twists". The remaining gap is that the relating `g`
must lie in `⟨exec⟩`, not merely `Aut` — precisely the completeness core.

**This is NOT the banned "GI∈P ⟹ impossible" reasoning** — it is "this specific WL-completeness
characterisation is empirically firm but unproven, and is the actual open theorem behind R1".
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (WordReach verified gens IsColAut)

variable {n : Nat}

/-- **R1's core.** Every reference generator's action is a word in the EXECUTABLE's verified
generators — "the pick is interchangeable" at the orbit level. -/
def DeepenRefInExec (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ ρ ∈ deepenRefGens adj χ, ∀ x : Fin n,
    WordReach (verified deepenSupply adj χ) x (ρ x)

/-- **R1 ⟸ `DeepenRefInExec`** — the reverse `SameOrbits` direction, by `WordReach` induction. -/
theorem wordReach_deepen_of_ref (hcore : ∀ (adj : AdjMatrix n) (χ : Colouring n), DeepenRefInExec adj χ)
    (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (h : WordReach (verified deepenRefSupply adj χ) u w) :
    WordReach (verified deepenSupply adj χ) u w := by
  induction h with
  | refl => exact WordReach.refl _
  | step hum hg ih =>
      rename_i m g
      have hgmem : g ∈ deepenRefGens adj χ := (List.mem_filter.mp hg).1
      exact ih.trans (hcore adj χ g hgmem m)

/-- **The core discharges the whole of `SameOrbits`** (with the easy half from `DeepenRef`). -/
theorem sameOrbits_of_core (hcore : ∀ (adj : AdjMatrix n) (χ : Colouring n), DeepenRefInExec adj χ) :
    OrbitPrune.SameOrbits (deepenRefSupply (n := n)) (deepenSupply (n := n)) := by
  intro adj χ u w
  exact ⟨wordReach_deepen_of_ref hcore adj χ u w, wordReach_ref_of_deepen adj χ u w⟩

/-- A reference generator that is ALSO an executable generator satisfies the core trivially — one
`WordReach` step. So the residue of `DeepenRefInExec` is exactly the NON-canonical-pick twists. -/
theorem refInExec_of_mem_deepenGens (adj : AdjMatrix n) (χ : Colouring n)
    {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ deepenGens adj χ) (x : Fin n) :
    WordReach (verified deepenSupply adj χ) x (ρ x) := by
  have hv : ρ ∈ verified deepenSupply adj χ := by
    rw [verified, List.mem_filter]
    exact ⟨hρ, decide_eq_true (deepenGens_isColAut adj χ hρ)⟩
  exact (WordReach.refl x).step hv

end Deepen
end ChainDescent
