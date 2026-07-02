/-
# Route A, Step C — Piece 1c(iii): the orbit-realization reduction (isolate the two remaining pieces)

**What this module builds (recovery doc §9.7, Piece 1c(iii)).** The round-3 crux `GramCountsRecoverOrbit`
(`SameGramStratCounts ⟹ StabOrbit`, Piece 1a) is reduced to **exactly two named predicates**, and the composition is
proved. After this, all of Route A / Piece 1 compiles modulo just these two — one open Gauss predicate (probe-true) and
one carried Witt predicate (known-true):

* **`GramCountsRecoverGram`** — the OPEN Gauss content: `SameGramStratCounts u u'` ⟹ (`SameExactGram Q {a,b} u u'`) **and**
  the plane-membership flag (`u ∈ span{a,b} ↔ u' ∈ span{a,b}`). **Probe-true** (`round3_probe.py`: the round-3 profile
  separates orbits, which refine exactly this data). **Attack (the remaining Gauss build):** instantiate a primitive
  additive character `ψ`, apply `ScratchGramStratInvert.sameGramStratCounts_transform` (⟹ equal `innerZ` fibre sums ∀`s`),
  then Fourier-invert — the **bulk** term (`gramStrat_inner_eval_ne`, `ρ=r₀+r₃≠0`) recovers the primal Gram
  `(Qu, polar u a, polar u b)` and the **boundary** term (`gramStrat_inner_eval_zero`, `ρ=0`) recovers the `u∈span{a,b}`
  flag (its indicator is `polarBilin.flip (r₁•a+r₂•b−r₃•u)=0 ⟺ u∈span{a,b}`). This is the "`K` non-degenerate" lemma.

* **`RefinedWittExtends`** — the CARRIED, **known-true** Witt content: `SameExactGram Q {a,b} u u'` + the flag ⟹
  `StabOrbit`. This is a theorem of **Witt's extension theorem on the nondegenerate complement `W^⊥`** (`W = span{a,b}`,
  nondegenerate since `a,b` orthogonal anisotropic): `SameExactGram` forces `u_W = u'_W` and `Q u_⊥ = Q u'_⊥`, and the
  flag rules out the *sole* obstruction (`u_⊥ = 0` vs nonzero-isotropic), after which Witt extends the line isometry
  `u_⊥ ↦ u'_⊥` to an isometry fixing `W` pointwise. It is carried (not proved) only because **Mathlib lacks the Witt
  extension theorem** — the same reason the project carries `WittExtendsToOrbit`. NB the *unrefined* `WittExtendsToOrbit
  Q {a,b}` (SameExactGram ⟹ orbit, no flag) is FALSE here (`36 > 27`); the flag is exactly what repairs it.
  `stabOrbit_imp_span_iff` below proves the flag is orbit-sound, so `RefinedWittExtends` is the *tight* converse.

**Reduction (proved):** `gramCountsRecoverOrbit_of` composes the two into `GramCountsRecoverOrbit`; `gramCountsEq_iff_stabOrbit_refined`
then gives `SameGramStratCounts ↔ StabOrbit` (`bᵢ=1`) modulo the two.

Reuses `ScratchGramStratCount` (`GramCountsRecoverOrbit`/`gramCountsEq_iff_stabOrbit`), `ScratchWallKernel`
(`SameExactGram`), `ScratchOrbitBaseCase` (`StabOrbit`/`Similitude`), `ScratchBranchDepth` (`stab_fixes_span`).
Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratCount
import ChainDescent.ScratchBranchDepth

namespace ChainDescent.GramStrat

open QuadraticMap ChainDescent.Wall ChainDescent.OrbitBaseCase

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **The plane-membership flag is orbit-sound.** A base-fixing similitude fixes `span{a,b}` pointwise
(`stab_fixes_span`), so it cannot move a plane vertex out of the plane (nor an off-plane vertex in): if `u, u'` are
`Stab({a,b})`-orbit-related then `u ∈ span{a,b} ↔ u' ∈ span{a,b}` (indeed either membership forces `u = u'`). This makes
the flag a genuine orbit invariant — so `RefinedWittExtends` (which uses it as a hypothesis) is the *tight* converse of
soundness, not an ad-hoc strengthening. -/
theorem stabOrbit_imp_span_iff {a b u u' : V} (h : StabOrbit Q ({a, b} : Set V) u u') :
    u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V) := by
  obtain ⟨g, hfix, hgu⟩ := h
  constructor
  · intro hu
    have hfu : g.toLinearEquiv u = u := ChainDescent.BranchDepth.stab_fixes_span hfix hu
    have huu : u = u' := hfu.symm.trans hgu
    rw [← huu]; exact hu
  · intro hu'
    have hfu' : g.toLinearEquiv u' = u' := ChainDescent.BranchDepth.stab_fixes_span hfix hu'
    have : g.toLinearEquiv u = g.toLinearEquiv u' := by rw [hgu, hfu']
    have huu : u = u' := g.toLinearEquiv.injective this
    rw [huu]; exact hu'

/-- **★ The open Gauss content (probe-true).** The round-3 count profile determines both the exact Gram to `{a,b}` and the
plane-membership flag. See the module header for the attack (transform + `inner_eval_ne`/`_zero`). -/
def GramCountsRecoverGram (Q : QuadraticForm K V) (a b : V) : Prop :=
  ∀ u u' : V, SameGramStratCounts Q a b u u' →
    SameExactGram Q ({a, b} : Set V) u u'
      ∧ (u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V))

/-- **★ The carried, known-true Witt content.** Exact Gram to `{a,b}` + the plane-membership flag ⟹ same
`Stab({a,b})`-orbit. A theorem of Witt on the nondegenerate `W^⊥`; carried only because Mathlib lacks Witt extension.
The flag is *necessary*: without it the statement is `WittExtendsToOrbit Q {a,b}`, which is FALSE (`36 > 27`). -/
def RefinedWittExtends (Q : QuadraticForm K V) (a b : V) : Prop :=
  ∀ u u' : V, SameExactGram Q ({a, b} : Set V) u u' →
    (u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V)) →
    StabOrbit Q ({a, b} : Set V) u u'

/-- **★ The reduction — the two isolated pieces compose to the crux.** `GramCountsRecoverGram` (open Gauss, probe-true) +
`RefinedWittExtends` (carried Witt, known-true) ⟹ `GramCountsRecoverOrbit`. So the entire round-3 crux is now `bᵢ=1`
modulo exactly these two named predicates. -/
theorem gramCountsRecoverOrbit_of {a b : V}
    (h1 : GramCountsRecoverGram Q a b) (h2 : RefinedWittExtends Q a b) :
    GramCountsRecoverOrbit Q a b := by
  intro u u' hcounts
  obtain ⟨hgram, hflag⟩ := h1 u u' hcounts
  exact h2 u u' hgram hflag

/-- **★ Capstone — `bᵢ=1` for the round-3 observable, modulo the two isolated pieces.** Composes the reduction with the
Piece-1a capstone `gramCountsEq_iff_stabOrbit`: at an anisotropic base, `SameGramStratCounts u u' ↔ StabOrbit`, i.e. the
round-3 cells ARE the `Stab({a,b})`-orbits, modulo `GramCountsRecoverGram` (Gauss) and `RefinedWittExtends` (Witt). -/
theorem gramCountsEq_iff_stabOrbit_refined {a b : V} (ha : Q a ≠ 0)
    (h1 : GramCountsRecoverGram Q a b) (h2 : RefinedWittExtends Q a b) {u u' : V} :
    SameGramStratCounts Q a b u u' ↔ StabOrbit Q ({a, b} : Set V) u u' :=
  gramCountsEq_iff_stabOrbit ha (gramCountsRecoverOrbit_of h1 h2)

end ChainDescent.GramStrat
