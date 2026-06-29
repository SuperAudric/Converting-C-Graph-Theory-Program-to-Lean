/-
# The wall kernel (Route B, Increment 3a) — isolate the open predicate + reduce around it

**What this module does.** `CellsAreOrbits` in the *anisotropic* regime (`span S` carries an anisotropic vector, so
`Stab(S)` has multiplier `μ = 1` — pure isometries; the delimiter `mult_eq_one_of_fixes_anisotropic`) is the route's
open core (the "wall"). This module **isolates that open content as a single named predicate `WallKernel`** and proves
the reduction *around* it — the project-standard move (cf. `WittConeTransitive`, `PotentialDrops`): everything except
`WallKernel` (and the carried Witt-extension tech debt) is discharged.

**The decomposition (route doc §4, §6 Increment 3).** At an anisotropic base `S`, the `Stab(S)`-orbit of a vertex is
characterised by its **exact** Gram data to `S` (`Q t`, `polar Q t s`); refinement only sees the **square class**
(`χ` of those — the cap, `ScratchSimilitudeCap`). So:

* **Soundness (free).** `StabOrbit ⟹ SameExactGram` — an `S`-fixing isometry (`μ = 1`) preserves the exact Gram data.
  Hence `StabOrbit ⟹ SameSquareClass`. (`stabOrbit_imp_sameExactGram_of_anisotropic`.)
* **Witt extension (carried tech debt).** `SameExactGram ⟹ StabOrbit` — equal exact Gram to `S` ⟹ same isometry orbit
  fixing `S`. The Witt extension theorem; carried as `WittExtendsToOrbit`.
* **The wall (open).** `SameSquareClass ⟹ SameExactGram` — the square-class profile *determines* the exact Gram. This
  is the only open content: `WallKernel`.

Putting them together: at an anisotropic base, **modulo {Witt}, `CellsAreOrbits` ⟺ `WallKernel`**
(`stabOrbit_iff_sameSquareClass_of_wallKernel`). The open content is exactly one predicate.

**Connection to the seal machinery (3b/3c).** `WallKernel` is the *exact-Gram* form of the bounded-base determination
that the seal's `ZProfileSeparates` (`ProfileReduction.lean`) states in *count* observables (`Z_u(S)`). The seal proves
the *count* version at a `Θ(log n)` matching base via `c0_le_threequarters` (a fraction bound) + union bound; the wall
is the same determination at the `O(d)` frame, which a fraction bound cannot reach (see route doc §6 Increment 3). The
character-inversion attack on `WallKernel` is 3c. **"Every base up to automorphism"** is the geometric
similitude-equivariance of `WallKernel` (the analogue of the spine's `baseTransport`) — deferred to the next sub-step.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchOrbitBaseCase

namespace ChainDescent.Wall

open ChainDescent.OrbitBaseCase QuadraticMap

-- `similitude_polar` is purely algebraic (no finiteness); the `χ`-level defs need `Fintype`/`DecidableEq`.
set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {S : Set V} {t t' : V}

/-- **Similitudes scale the polar form.** `polar Q (g x) (g y) = μ · polar Q x y` (polarisation of `Q ∘ g = μ·Q`).
For `μ = 1` (an isometry) the polar is preserved — the engine of orbit soundness. -/
theorem similitude_polar (g : Similitude Q) (x y : V) :
    QuadraticMap.polar Q (g.toLinearEquiv x) (g.toLinearEquiv y) = g.mult * QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]
  rw [← g.toLinearEquiv.map_add, g.map, g.map, g.map]
  ring

/-- **Exact Gram profile to `S`.** Two vertices agree on `Q` and on `polar · s` for every base point `s ∈ S`. This is
the data that determines the `Stab(S)`-isometry-orbit (by Witt extension). -/
def SameExactGram (Q : QuadraticForm K V) (S : Set V) (t t' : V) : Prop :=
  Q t = Q t' ∧ ∀ s ∈ S, QuadraticMap.polar Q t s = QuadraticMap.polar Q t' s

/-- **Square-class profile to `S`.** The `χ` (quadratic-character) of the exact Gram data — the finest pointwise
information any graph-isomorphism invariant can carry (the cap, `ScratchSimilitudeCap`). What refinement sees. -/
def SameSquareClass (Q : QuadraticForm K V) (S : Set V) (t t' : V) : Prop :=
  quadraticChar K (Q t) = quadraticChar K (Q t') ∧
    ∀ s ∈ S, quadraticChar K (QuadraticMap.polar Q t s) = quadraticChar K (QuadraticMap.polar Q t' s)

/-- **Exact ⟹ square-class (free).** Equal exact Gram data has equal square classes (apply `χ`). -/
theorem sameExactGram_imp_sameSquareClass (h : SameExactGram Q S t t') : SameSquareClass Q S t t' :=
  ⟨by rw [h.1], fun s hs => by rw [h.2 s hs]⟩

/-- **Soundness (free) — orbit ⟹ exact Gram, at an anisotropic base.** An `S`-fixing similitude with an anisotropic
vector in `S` has multiplier `1` (the delimiter), hence is an isometry preserving `Q` and `polar · s`. So the
`Stab(S)`-orbit relation refines the exact-Gram relation — the easy half of `CellsAreOrbits`. -/
theorem stabOrbit_imp_sameExactGram_of_anisotropic {a : V} (haS : a ∈ S) (ha : Q a ≠ 0)
    (h : StabOrbit Q S t t') : SameExactGram Q S t t' := by
  obtain ⟨g, hfix, hgt⟩ := h
  have hμ : g.mult = 1 := mult_eq_one_of_fixes_anisotropic g ha (hfix a haS)
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← hgt, g.map, hμ, one_mul]
  · have hps : QuadraticMap.polar Q (g.toLinearEquiv t) s = QuadraticMap.polar Q t s := by
      conv_lhs => rw [← hfix s hs]
      rw [similitude_polar, hμ, one_mul]
    rw [← hgt, hps]

/-- **★ The wall — the open kernel predicate.** At base `S`, the square-class profile *determines* the exact Gram
profile. This is the *entire* open content of `CellsAreOrbits` in the anisotropic regime — the bounded-base
determination ("separator → certifier"). Open both ways (bounded-WL-dimension); the count-observable form is the seal's
`ZProfileSeparates`. -/
def WallKernel (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ t t' : V, SameSquareClass Q S t t' → SameExactGram Q S t t'

/-- **The carried Witt-extension input (tech debt).** Equal exact Gram to `S` ⟹ same `Stab(S)`-isometry-orbit. The
Witt extension theorem (Mathlib-absent; known-true classical geometry). Carried as a named hypothesis, discharged by
the parallel Witt build. -/
def WittExtendsToOrbit (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ t t' : V, SameExactGram Q S t t' → StabOrbit Q S t t'

/-- **The reduction — `WallKernel` + Witt ⟹ cells-are-orbits (the hard direction).** Same square-class profile ⟹
(`WallKernel`) same exact Gram ⟹ (`WittExtendsToOrbit`) same `Stab(S)`-orbit. Everything but `WallKernel` and the
carried Witt input is discharged. -/
theorem stabOrbit_of_sameSquareClass (hW : WallKernel Q S) (hWitt : WittExtendsToOrbit Q S)
    (h : SameSquareClass Q S t t') : StabOrbit Q S t t' :=
  hWitt t t' (hW t t' h)

/-- **★ `CellsAreOrbits` at an anisotropic base ⟺ `WallKernel` (modulo Witt) — the isolation capstone.** At a base
carrying an anisotropic vector, the `Stab(S)`-orbit relation coincides with the square-class relation **iff** the
wall kernel holds (given the carried Witt-extension input). So the route's open content at the orbit level is *exactly*
`WallKernel` — one named predicate, everything else proved. -/
theorem stabOrbit_iff_sameSquareClass_of_wallKernel {a : V} (haS : a ∈ S) (ha : Q a ≠ 0)
    (hW : WallKernel Q S) (hWitt : WittExtendsToOrbit Q S) :
    StabOrbit Q S t t' ↔ SameSquareClass Q S t t' :=
  ⟨fun h => sameExactGram_imp_sameSquareClass (stabOrbit_imp_sameExactGram_of_anisotropic haS ha h),
   stabOrbit_of_sameSquareClass hW hWitt⟩

end ChainDescent.Wall
