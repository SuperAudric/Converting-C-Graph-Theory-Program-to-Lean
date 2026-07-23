import ChainDescent.DeepenRef
/-! ⚠⚠ SUPERSEDED & PARKED (2026-07-23, TRACK A) — NOT in `build.sh`, DOES NOT COMPILE against the current
`deepen`. This is the DISCARDED reference route (`deepenRefSupply`/`DeepenRefInExec`/R1/R2) for `deepenSupply`
's `①c`. It was made MOOT by the whole-graph-discretize redesign: `①c` now closes modulo `{Amenable}` alone
(`DeepenAmenable.deepenSupply_guarded_canonizer_direct`), with `[DISC]`/gate/termination structural and
`AnchorFires` eliminated. Retained for provenance only — see `docs/chain-descent-deepen-supply.md` STATUS +
§8/§9 (provenance) and `docs/00-START-HERE.md` §2 C3b. Do NOT build on this. -/


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

## The status of `DeepenRefInExec` — it FACTORS (2026-07-21, scoped)

**Framing (corrected 2026-07-21, user).** The obligation is **symmetry-consumption completeness, not
WL/I-R completeness.** By the force/consume division (decision limits output → force; does not → consume),
colour-equal-but-NON-automorphic pairs are FORCE's job, so the reference emits VERIFIED twists only
between genuinely-automorphic vertices — **R1 needs no external single-orbit hypothesis; the verification
gate (`twistOf_isColAut`) supplies it.** (`§L.4` of the C# linear-oracle is a FORCE-side result and only an
ANALOGY here; the earlier "Miyazaki defeats it" was RETRACTED — `deepen` takes a SINGLE path per anchor,
not the search tree.)

**The factoring.** `R1 ⟸ (Amenable ⟹ R1) + Amenable`, where

  `Amenable adj χ` := at every level of the canonical deepening, the cell `chooseIdK` selects is a single
  orbit of the pointwise-stabilizer of the vertices individualized so far.

⚠ **Firing does NOT imply `Amenable`** — a WL-merged multi-orbit cell can still discretize (a nested
force-decision the greedy pick resolves arbitrarily). So `Amenable` is a genuine domain hypothesis, and a
`¬Amenable` FIRING graph (the still-missing part-III "fires-but-incomplete" witness) is the one untested
regime. VALIDATION (`ScratchR1Probe`, deleted): no R1 falsifier — exec-orbits == ref-orbits on `G8` ×7
relabellings (rich [4,2,2]), `cG8`, `t3`, `wcyc9`; rigid `F12` all-singletons both sides; and G8 exec =
**16 = Σ k(k−1) over {4,2,2}** = one DIRECT verifying twist per same-orbit ordered pair.

**LAYER 1 — `Amenable ⟹ R1`, MECHANICAL (provable now).** A **re-relating induction** with invariant:
*the deepen-from-`a` and replay-from-`b` descents (a~b via ρ∈Aut) stay related by an automorphism ρ′
mapping a's individualized sequence to b's, pointwise.* Per level: same id (`chooseIdK_transport`);
`C_b = ρ′(C_a)` is single-orbit under `Stab(indiv_b)` (= `Amenable`) so ∃ `τ∈Stab(indiv_b)` with
`τ(ρ′ u_a) = u_b`, and `τρ′` re-establishes the invariant (τ absorbs the lowest-index mismatch). At
discreteness the leaves are automorphism-related ⟹ colour-matchable ⟹ the exec twist for (a,b) VERIFIES
⟹ direct WordReach. Tools: `refineEquivariant`, `step_transport`, `chooseIdK_transport`, `twistOf_isColAut`.
⚠ **SUB-RISK (settle FIRST):** `SameOrbits` is over ALL vertices; the induction gives completeness on the
BRANCH CELL (the anchors), but the twists also move `K∖cell` — needs the induction extended to `K` or a
"the cell controls `K`" argument.

**LAYER 2 — `Amenable`, per-family aiming GENERAL.** = IR-amenability along the canonical path (1-WL
identifies the graph at each individualized stage). FALSE universally (CFI) but known for deepen's target
families (coherent configs / bounded-WL-dim rank-2 graphs, Cayley graphs of `PGL(3,2)` = mp7's base,
affine/projective groups); discharge by connecting to existing WL-completeness seals (Route-C
`reachesRigidOrCameron_*`, Cameron), seeking a bounded categorisation that generalises the amenability
property; a resisting family routes to force/kernel.

**BACKUP (held) — the poly all-or-nothing gate.** Per level, check whether individualizing each member of
the chosen id-cell gives the same footprint-partition; emit all-or-nothing, defer on failure. CHECKS
`Amenable` locally instead of proving it (①c by construction). Only if Layer 1's K-coverage or Layer 2's
discharge truly stalls. **NOT the banned GI∈P reasoning** — `Amenable` is concrete, measured-true, and
per-family dischargeable.
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
