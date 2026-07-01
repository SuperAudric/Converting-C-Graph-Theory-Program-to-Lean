/-
# Route A — the span-dim-2 recovery scaffold (`bᵢ=1` at span-dim ≥ 2, family instantiation, increment 1)

**What this module builds.** The recovery route's remaining half (recovery doc §6 ITEM B, route A): at a span-dim-2
anisotropic base `S` (containing `≥ 2` independent anisotropic directions), the branching factor is `bᵢ = 1` — the
`warmRefine` cells coincide with the `Stab(S)`-orbits. The `recovery_depth_probe.py` direction check found this recovery
is **bounded-round** (`r* ∈ {3,4}`, flat in `d`) on a **`d`-uniform** `Θ(q³)`-orbit problem — crackable via a 2-round
count-separation, not the frontier. This module lands **increment 1**: the *reduction scaffold* that isolates the open
Gauss content as one named predicate, exactly as the seal isolates `IsotropySeparatesAtBase`.

**The reduction (this increment, proved).** For any observable `obs : V → β` (the intended instance is the 2-round
isotropy-count profile at `S` — the seal's `χ(det G₂)` pair-form):
* **Soundness (FREE, `stabOrbit_imp_obsEq`).** If `obs` is `Stab(S)`-invariant (true for any graph-refinement observable,
  as a similitude fixing `S` is a graph automorphism fixing the individualisation), then same-orbit ⟹ same `obs`. So
  cells are always *unions* of orbits — the easy half.
* **Recovery (the open half, `WallKernelFor`).** The converse — same `obs` ⟹ same exact Gram ⟹ (Witt) same orbit — is
  `WallKernelFor (fun t t' => obs t = obs t') Q ↑S`, discharged by `stabOrbit_of_obs` (`ScratchWallKernel`).
* **Capstone `obsEq_iff_stabOrbit`.** Invariance + the wall kernel + Witt give **`obs t = obs t' ↔ StabOrbit`**, i.e. the
  `obs`-cells ARE the orbits (`bᵢ = 1`). So route A reduces to `WallKernelFor(2-round count) Q ↑S` at span-dim-2 — the
  named Gauss core, now with soundness and the reduction fully proved.

**The open core + the `d`-uniformity plan (increment 2, the genuine new math — NOT in this module).** `WallKernelFor` for
the 2-round count is the WL-orbit defect. What makes it a **family** (all `d`) rather than per-instance `decide`: the
orthogonal complement `⟨a,b⟩^⊥` (dim `d−2`) contributes a **`v`-independent Gauss factor** to every count (an isometry of
the complement, acting transitively on each `Q`-level-set, leaves the count invariant), so it **cancels** in the
separation comparison — reducing the count to a **fixed `d`-independent** local count over `⟨a,b⟩` (⟹ decidable / uniform
character sum). This complement-factoring is exactly what the `r*`-flat / orbit-count-`d`-uniform probe predicts, and is
the next increment (reuses `PairForm`/`GaussCount`, plus the orthogonal decomposition `V = ⟨a,b⟩ ⊕ ⟨a,b⟩^⊥`).

Reuses `ScratchWallKernel` (`WallKernelFor`/`stabOrbit_of_obs`/`SameExactGram`) and `ScratchOrbitBaseCase`
(`Similitude`/`StabOrbit`). Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchWallKernel

namespace ChainDescent.SpanDim2Recovery

open ChainDescent.OrbitBaseCase ChainDescent.Wall QuadraticMap

variable {K V β : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {S : Set V} {obs : V → β}

/-- **`obs` is `Stab(S)`-invariant.** Every `S`-fixing similitude preserves the observable. True for any graph-refinement
observable (a similitude fixing `S` pointwise is an automorphism of the `S`-individualised graph, so it preserves every
`warmRefine` colour / isotropy-count). Carried as the hypothesis characterising "`obs` is what refinement sees". -/
def ObsInvariant (obs : V → β) (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ g : Similitude Q, (∀ s ∈ S, g.toLinearEquiv s = s) → ∀ x, obs (g.toLinearEquiv x) = obs x

/-- **Soundness (the free half) — same orbit ⟹ same observable.** From `Stab(S)`-invariance, orbit-related vertices
share `obs`; so `obs`-cells are unions of orbits. No open content. -/
theorem stabOrbit_imp_obsEq (hinv : ObsInvariant obs Q S) {t t' : V}
    (h : StabOrbit Q S t t') : obs t = obs t' := by
  obtain ⟨g, hfix, hgt⟩ := h
  rw [← hgt, hinv g hfix]

/-- **★ The reduction capstone — `obs`-cells ARE the orbits.** With `obs` `Stab(S)`-invariant, the wall kernel for `obs`
(same `obs` ⟹ same exact Gram), and the carried Witt input, the observable's equality relation coincides *exactly* with
the `Stab(S)`-orbit relation: `obs t = obs t' ↔ StabOrbit Q S t t'` — i.e. `bᵢ = 1`. Route A at span-dim-2 is therefore
`WallKernelFor (fun t t' => obs t = obs t') Q S` for `obs` = the 2-round isotropy count; everything else is proved here.
-/
theorem obsEq_iff_stabOrbit [Fintype K] [DecidableEq K]
    (hinv : ObsInvariant obs Q S)
    (hW : WallKernelFor (fun t t' => obs t = obs t') Q S)
    (hWitt : WittExtendsToOrbit Q S) {t t' : V} :
    obs t = obs t' ↔ StabOrbit Q S t t' :=
  ⟨fun h => stabOrbit_of_obs hW hWitt h, fun h => stabOrbit_imp_obsEq hinv h⟩

/-- **The span-dim-2 recovery target, named.** `SpanDim2Recovers` bundles the two inputs route A needs at a base `S`:
`obs` is refinement-invariant, and its wall kernel holds (the open Gauss core). It yields `obsEq_iff_stabOrbit`
(`bᵢ = 1`). Increment 2 discharges the wall kernel for `obs` = the 2-round count via the complement-factoring. -/
structure SpanDim2Recovers [Fintype K] [DecidableEq K]
    (Q : QuadraticForm K V) (S : Set V) (obs : V → β) : Prop where
  invariant : ObsInvariant obs Q S
  wallKernel : WallKernelFor (fun t t' => obs t = obs t') Q S
  witt : WittExtendsToOrbit Q S

/-- **`SpanDim2Recovers ⟹ cells = orbits.** The packaged capstone: from the bundled recovery inputs, the `obs`-cell
relation is exactly the `Stab(S)`-orbit relation. -/
theorem obsEq_iff_stabOrbit_of_recovers [Fintype K] [DecidableEq K]
    (h : SpanDim2Recovers Q S obs) {t t' : V} :
    obs t = obs t' ↔ StabOrbit Q S t t' :=
  obsEq_iff_stabOrbit h.invariant h.wallKernel h.witt

end ChainDescent.SpanDim2Recovery
