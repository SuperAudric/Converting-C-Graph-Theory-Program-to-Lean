import ChainDescent.DeepenTransport

/-!
# `C3b` tranche 2, part II — the crux, DECOMPOSED and stated

Part I (`DeepenTransport`) proved that every stage of the pipeline transports except the per-level
vertex pick, isolating the whole ①c obligation to the single line `w :: _` in `deepen`. This file
states precisely what remains, as two named predicates, and proves the half that is unconditional.

## The decomposition (arrived at by measurement, 2026-07-20)

**⚠⚠ A RETRACTED ARGUMENT, kept visible so it is not repeated.** An earlier version of this header
argued: measurement says the emitted relation *equals the true `Aut`-orbit relation* on every
instance tested, but "that cannot hold in general, since a cell's orbit partition is poly-time
equivalent to GI, so such a supply would be GI ∈ P". **That reasoning is BANNED by a standing project
steer** ("any `X ⟹ GI∈P, therefore X impossible` argument is BANNED" — a perfect key *is* GI∈P, which
is the TARGET, so the inference is circular). It was also unsupported: the accompanying claim that
"on hard instances the gate simply fails" was asserted, never measured, **and the measurement
contradicts it** — see below. Both are withdrawn.

**What is actually measured.** Emitted = true `Aut`-orbit relation on every instance tested: `G8`
`[2,2,2,2,4,4,4,4]` both sides; 30/30 firing graphs at `n = 7`; 19/19 at `n = 8`; `wcyc9` `[3,3,3]`
both sides (`9!` brute-forced, a genuine CFI-style witness with non-trivial orbit structure). And the
gate **never failed**: 0 failing anchors on `t3`, `wcyc9`, `ut` and `mp7` — including `mp7`, where
deck, deck2 and gauge propagation all fail. So "the gate fails on hard instances" is, so far, false.

**Status: the orbit-equality hypothesis is UNFALSIFIED, not refuted.** It is not asserted here either
— the predicates below are stated gate-conditionally, which is the right shape whichever way it
resolves, and `DeepenForcedMatch` is exactly where the question lives.

**The discriminating witness that is still missing** (and that any future attempt should build
FIRST): a graph with **non-trivial symmetry** that individualization-refinement **cannot cheaply
discretize** — i.e. CFI/multipede over a LARGE expander-like base (cf. the C#
`MultipedeGenerator.BuildRandomRegular`, whose high-treewidth base is documented to resist
refinement). Rigid multipedes do not discriminate (trivial `Aut` makes the equality hold vacuously);
`mp7` does not either (Fano is small and the gate passes). Until such a witness exists, every sweep
in this file's evidence list may be systematically blind.

So ①c reduces to the two statements below. `DeepenGateInvariant` is the one that carries the
labelling-independence: combined with part I (everything but the pick transports), rule-invariance of
the *gate outcome* is exactly what upgrades to labelling-invariance.

## Evidence (recorded so the next session need not re-measure)

* `DeepenGateInvariant`: no counterexample — gate outcomes agree under the lowest-index and
  highest-index rules on `G8` (all 8 anchors pass under both), `t3`, `wcyc9`, `ut`, and across 200
  random `n = 8` graphs.
* Rule-independence of the emitted relation itself: `G8` + `t3` + `wcyc9` + `ut` under two rules and
  under 8 labellings each; plus 400 random `n = 8` graphs (0 mismatches, 302 firing).
* ⚠⚠ **BUT THE RANDOM SWEEPS ARE DEGENERATE — measured, do not over-trust them.** At `n = 8` every
  generated graph has a branch cell of size **0 or 2** (ZERO with a cell ≥ 4), because **random
  graphs are almost surely asymmetric** so refinement discretizes them. The real evidence is the
  handful of structured witnesses, of which **`G8` is the only rich partially-firing one**. A proper
  search needs graphs WITH symmetry (Cayley / CFI / vertex-transitive families).
* ⚠ **Methodological caveat, recorded because it bit once already** (the `G8` falsifier): all this
  evidence comes from instances where the algorithm appears *complete*. A discriminating test needs
  an instance where the supply fires but is strictly incomplete, and none was found at `n ≤ 8`. Until
  such a witness exists the sweeps may be systematically blind, exactly as `mp7` was blind to the
  anchor-layer bug by firing totally.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The gate, as a function of the anchor -/

/-- **The gate outcome at anchor `r`**: the deepening reaches an all-singleton footprint over a
non-empty coupled component. This is exactly the condition `deepenGens` tests before emitting. -/
def GateAt (adj : AdjMatrix n) (χ : Colouring n) (r : Fin n) : Bool :=
  match deepen adj χ n (step adj χ r) [] with
  | none => false
  | some (d1, _) =>
      let K := coupled χ d1.col
      !K.isEmpty && allSingletonsK K d1.col

/-! ## 2. The two open statements -/

/-- **CRUX (i) — the gate outcome is labelling-invariant.**
Part I proved every other stage transports; this is the one place the per-level vertex pick can
break equivariance, so this predicate is precisely the residue of ①c at the gate level. -/
def DeepenGateInvariant : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (r : Fin n),
    GateAt (relabelAdj σ adj) (transportColouring σ χ) (σ r) = GateAt adj χ r

/-- **CRUX (ii) — when the gate passes, the emitted relation is the TRUE orbit relation.**
The `←` direction is completeness (the hard one: a discretized branch forces the match, so every
genuine automorphism `r₁ ↦ rⱼ` is found). The `→` direction is soundness and is proved below. -/
def DeepenForcedMatch : Prop :=
  ∀ (adj : AdjMatrix n) (χ : Colouring n) (r₁ rⱼ : Fin n),
    GateAt adj χ r₁ = true →
    ((∃ ρ ∈ deepenGens adj χ, ρ r₁ = rⱼ) ↔ (∃ t : Equiv.Perm (Fin n), IsColAut adj χ t ∧ t r₁ = rⱼ))

/-! ## 3. The unconditional half — soundness -/

/-- **Every emitted generator is a genuine colour-automorphism.** Untrusted construction, verified
emission: this is the `→` direction of `DeepenForcedMatch`, and it holds with no gate hypothesis. -/
theorem deepenGens_isColAut (adj : AdjMatrix n) (χ : Colouring n)
    {ρ : Equiv.Perm (Fin n)} (h : ρ ∈ deepenGens adj χ) : IsColAut adj χ ρ := by
  unfold deepenGens at h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  aesop

/-- Consequence: the emitted orbit relation is contained in the true one — the supply can only ever
under-report orbits, never over-report. (Over-splitting costs a branch; over-merging would be
unsound.) -/
theorem deepenGens_sound (adj : AdjMatrix n) (χ : Colouring n)
    {ρ : Equiv.Perm (Fin n)} (h : ρ ∈ deepenGens adj χ) (v : Fin n) :
    ∃ t : Equiv.Perm (Fin n), IsColAut adj χ t ∧ t v = ρ v :=
  ⟨ρ, deepenGens_isColAut adj χ h, rfl⟩

end Deepen
end ChainDescent
