/-
# Route A, Step C — Piece 1c(iii): the orbit-realization reduction (isolate the two remaining pieces)

**What this module builds (recovery doc §9.7, Piece 1c(iii)).** The round-3 crux `GramCountsRecoverOrbit`
(`SameGramStratCounts ⟹ StabOrbit`, Piece 1a) is reduced to **exactly two named predicates**, and the composition is
proved. After this, all of Route A / Piece 1 compiles modulo just these two — one open Gauss predicate (must be PROVED) and
one carried Witt predicate (a legitimate CITATION of Witt's theorem).

**★ Both predicates carry a `GoodBase` antecedent — and this is essential, not cosmetic.** The bare `∀ Q a b` forms are
literally FALSE (e.g. `b` isotropic ⟹ `W = span{a,b}` degenerate ⟹ Witt-on-`W^⊥` fails; the Gauss probe-truth is only at
anisotropic orthogonal nondegenerate bases). A false statement can never be *discharged*, so — since the project's goal is
the **unconditional seal (citations only, no carried *unproven* hypothesis)** — leaving them false would permanently block
Route A. With `GoodBase Q a b` as antecedent both are TRUE (vacuous off-base, genuine on-base) and dischargeable, and the
caller (the affine-polar residue at odd `q`) supplies `GoodBase` at every span-dim-2 base. **Citation vs. prove:**
`RefinedWittExtends` (true `GoodBase` form) is Witt's classical theorem — carrying it is a *citation* (acceptable, exactly
as the seal cites G3/Babai), to be discharged by a Mathlib Witt build if/when one exists; `GramCountsRecoverGram` is
GENUINELY OPEN and must be proved for the unconditional seal.

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

/-- **The good span-dim-2 base conditions.** `a, b` orthogonal anisotropic (so the plane `W = span{a,b}` is nondegenerate
with Gram `diag(2·Qa, 2·Qb)`), char `≠ 2` (`(2:K)≠0`, needed both for the Gauss toolkit and for `polar a a = 2·Qa ≠ 0`),
and the whole polar form nondegenerate (so `V = W ⊕ W^⊥` with `W^⊥` nondegenerate — the setting of Witt on `W^⊥`).
**Carried as the antecedent of both predicates below** (see the "★ WHY antecedent" note): without it the bare `∀ Q a b`
forms are literally FALSE (e.g. `b` isotropic ⟹ `W` degenerate ⟹ Witt fails), so they could never be *discharged* toward
the unconditional seal; with it they are TRUE (vacuous off-base, genuine on-base) and provable. The caller (the
affine-polar residue at odd `q`) supplies `GoodBase` at every span-dim-2 base it uses. -/
def GoodBase (Q : QuadraticForm K V) (a b : V) : Prop :=
  Q a ≠ 0 ∧ Q b ≠ 0 ∧ QuadraticMap.polar Q a b = 0 ∧ (2 : K) ≠ 0 ∧ (Q.polarBilin).Nondegenerate

/-- **★ The open Gauss content (probe-true at a `GoodBase`).** At a good base, the round-3 count profile determines both
the exact Gram to `{a,b}` and the plane-membership flag. See the module header for the attack (transform +
`inner_eval_ne`/`_zero`). **★ WHY the `GoodBase` antecedent:** the probe-truth is at anisotropic orthogonal (nondeg) bases;
the bare `∀ Q a b` form is FALSE (the boundary flag needs `Q` nondegenerate to read `u∈span{a,b}`). The antecedent makes
this a *true, dischargeable* target (not a false statement carried forever). -/
def GramCountsRecoverGram (Q : QuadraticForm K V) (a b : V) : Prop :=
  GoodBase Q a b → ∀ u u' : V, SameGramStratCounts Q a b u u' →
    SameExactGram Q ({a, b} : Set V) u u'
      ∧ (u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V))

/-- **★ The carried, known-true Witt content (at a `GoodBase`).** Exact Gram to `{a,b}` + the plane-membership flag ⟹ same
`Stab({a,b})`-orbit. A theorem of Witt on the nondegenerate `W^⊥`; carried only because Mathlib lacks Witt extension (a
legitimate *cited* result — but only in this TRUE `GoodBase` form). **★ WHY the `GoodBase` antecedent:** Witt-on-`W^⊥`
genuinely fails when `W` is degenerate (`b` isotropic, or `a,b` dependent/non-orthogonal), so the bare `∀ Q a b` form is
FALSE — it could never be discharged/cited. The flag is *also* necessary: even at a good base, dropping it gives
`WittExtendsToOrbit Q {a,b}`, FALSE (`36 > 27`). -/
def RefinedWittExtends (Q : QuadraticForm K V) (a b : V) : Prop :=
  GoodBase Q a b → ∀ u u' : V, SameExactGram Q ({a, b} : Set V) u u' →
    (u ∈ Submodule.span K ({a, b} : Set V) ↔ u' ∈ Submodule.span K ({a, b} : Set V)) →
    StabOrbit Q ({a, b} : Set V) u u'

/-- **★ The reduction — the two isolated pieces compose to the crux (at a `GoodBase`).** `GramCountsRecoverGram` (open
Gauss, probe-true) + `RefinedWittExtends` (carried Witt, known-true) ⟹ `GramCountsRecoverOrbit`. So the entire round-3
crux is `bᵢ=1` modulo exactly these two named predicates, both TRUE and dischargeable at the good base. -/
theorem gramCountsRecoverOrbit_of {a b : V} (hbase : GoodBase Q a b)
    (h1 : GramCountsRecoverGram Q a b) (h2 : RefinedWittExtends Q a b) :
    GramCountsRecoverOrbit Q a b := by
  intro u u' hcounts
  obtain ⟨hgram, hflag⟩ := h1 hbase u u' hcounts
  exact h2 hbase u u' hgram hflag

/-- **★ Capstone — `bᵢ=1` for the round-3 observable, modulo the two isolated pieces.** Composes the reduction with the
Piece-1a capstone `gramCountsEq_iff_stabOrbit` (soundness needs `Q a ≠ 0`, from `GoodBase`): at a good base,
`SameGramStratCounts u u' ↔ StabOrbit`, i.e. the round-3 cells ARE the `Stab({a,b})`-orbits, modulo `GramCountsRecoverGram`
(Gauss) and `RefinedWittExtends` (Witt). -/
theorem gramCountsEq_iff_stabOrbit_refined {a b : V} (hbase : GoodBase Q a b)
    (h1 : GramCountsRecoverGram Q a b) (h2 : RefinedWittExtends Q a b) {u u' : V} :
    SameGramStratCounts Q a b u u' ↔ StabOrbit Q ({a, b} : Set V) u u' :=
  gramCountsEq_iff_stabOrbit hbase.1 (gramCountsRecoverOrbit_of hbase h1 h2)

end ChainDescent.GramStrat
