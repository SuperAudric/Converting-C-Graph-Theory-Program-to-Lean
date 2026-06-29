/-
# `CellsAreOrbits` base case + the multiplier-rigidity delimiter (CellsAreOrbits attack, increment 1)

**What this module formalizes.** `CellsAreOrbits` (refinement cells = `Stab(S)`-orbits at every partial base `S`) is the
open core of the forms-graph poly route. The attack is an **induction on base size**; this module lands its **base
case** and the algebraic fact that delimits exactly how far the *free* regime extends.

The geometric model: the affine-polar graph is `V = K^d` with adjacency `Q(x−y)=0`; its automorphism group is the
affine **similitude** group (translations ⋊ linear similitudes `g`, `Q(gx)=μ(g)·Q x`). A `Similitude Q` here bundles
`(g : V ≃ₗ V, μ ≠ 0, Q∘g = μ·Q)`; an **isometry** is the `μ=1` case.

* **Empty base (depth 0)** — `affinePolar_empty_base_one_orbit`: the whole vertex set is one orbit (translations act
  transitively). This is `CellsAreOrbits` at `S = ∅`, free. The induction's base rung.
* **Depth 1 (the isotropic sphere)** — `depth1_isotropic_sphere_one_orbit`: the neighbour sphere of `0` (= the nonzero
  isotropic vectors, `neighborSphere_zero_eq_isotropic`) is a single isometry-orbit, **given** the isolated input
  `WittConeTransitive Q` (isometries transitive on the cone = Witt's theorem on isotropic vectors; Mathlib-ABSENT, the
  AUDIT-W geometric keystone). Proved conditionally so the Witt input is named and isolated, not assumed silently.
* **The multiplier-rigidity delimiter (the new content)** — `mult_eq_one_of_fixes_anisotropic` /
  `mult_eq_one_of_fixes_span_anisotropic`: a similitude fixing an **anisotropic** vector (or an anisotropic vector in
  `span S`) has `μ = 1`. This pins *exactly where the free regime ends*: `Stab(S)` retains multiplier freedom (so its
  orbits are as coarse as the square-class refinement — see `ScratchSimilitudeCap`) **iff `span S` is totally
  isotropic**. Totally-isotropic subspaces have dimension `≤` the Witt index `≤ d/2`, so the free prefix lasts `~d/2`
  individualizations; the remaining `~d/2` (needed to span `V`) force `μ=1`, dropping `Stab(S)` to pure isometries —
  which is where `CellsAreOrbits` becomes the open `square-class ⟹ exact-Gram` bridge.

**The induction obligation, made precise (what the step must prove).** `CellsAreOrbits` at base `S` ⟺ refinement's
**square-class** Gram-profile to `S` determines the `Stab(S)`-orbit. The easy half (orbit ⟹ same profile) is
soundness, free. By **Witt extension** (any partial isometry extends), "same **exact** Gram-profile ⟹ same orbit" is
also free. So the entire open content is the gap between them: *same square-class profile ⟹ same exact-Gram profile,
modulo `Stab(S)`'s multipliers*. While `span S` is totally isotropic the multipliers absorb that gap (free,
delimited above); once anisotropic (μ=1) it is bounded-WL-dimension — the open core, the same object the matching
only closed at an `Θ(log n)` base.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`. Pure geometry (no `Fintype`).
-/
import ChainDescent.PairForm

namespace ChainDescent.OrbitBaseCase

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A **similitude** of `Q`: a linear automorphism `g` with `Q ∘ g = μ · Q` for a nonzero multiplier `μ`. The
automorphism group of the affine-polar graph is the affine version (translations ⋊ these). An **isometry** is `μ = 1`. -/
structure Similitude (Q : QuadraticForm K V) where
  toLinearEquiv : V ≃ₗ[K] V
  mult : K
  mult_ne : mult ≠ 0
  map : ∀ x, Q (toLinearEquiv x) = mult * Q x

/-- **Depth 0 — the whole vertex set is one orbit (translation-transitive).** This is `CellsAreOrbits` at the empty
base: any two vertices are related by a translation (an automorphism of the affine-polar graph). Free. -/
theorem affinePolar_empty_base_one_orbit (v w : V) : ∃ t : V, v + t = w :=
  ⟨w - v, by abel⟩

/-- **Multiplier rigidity (the delimiter).** A similitude that fixes an **anisotropic** vector has multiplier `1`
(i.e. is an isometry on that direction's norm). Once the canonizer individualizes an anisotropic vector, the residual
similitude freedom collapses to isometries — the boundary of the free regime. -/
theorem mult_eq_one_of_fixes_anisotropic {Q : QuadraticForm K V} (g : Similitude Q) {v : V}
    (hv : Q v ≠ 0) (hfix : g.toLinearEquiv v = v) : g.mult = 1 := by
  have h := g.map v
  rw [hfix] at h
  have h' : g.mult * Q v = 1 * Q v := by rw [one_mul]; exact h.symm
  exact mul_right_cancel₀ hv h'

/-- **Multiplier rigidity, span form.** A similitude fixing a set `S` pointwise has multiplier `1` as soon as `span S`
contains *any* anisotropic vector. So multiplier freedom in `Stab(S)` requires `span S` to be **totally isotropic** —
the precise condition delimiting how long the free prefix of the induction lasts (`≤` Witt index `≤ d/2` levels). -/
theorem mult_eq_one_of_fixes_span_anisotropic {Q : QuadraticForm K V} (g : Similitude Q)
    {S : Set V} (hfix : ∀ v ∈ S, g.toLinearEquiv v = v)
    {w : V} (hw : w ∈ Submodule.span K S) (hwa : Q w ≠ 0) : g.mult = 1 := by
  have hwfix : g.toLinearEquiv w = w := by
    refine Submodule.span_induction (p := fun x _ => g.toLinearEquiv x = x) ?_ ?_ ?_ ?_ hw
    · intro x hx; exact hfix x hx
    · simp
    · intro x y _ _ hx hy; rw [map_add, hx, hy]
    · intro a x _ hx; rw [map_smul, hx]
  exact mult_eq_one_of_fixes_anisotropic g hwa hwfix

/-- The **Witt-on-the-cone** input (Mathlib-ABSENT, AUDIT-W keystone): isometries act transitively on the nonzero
isotropic vectors. Isolated as a named predicate; everything around it is proved unconditionally. -/
def WittConeTransitive (Q : QuadraticForm K V) : Prop :=
  ∀ v w : V, v ≠ 0 → w ≠ 0 → Q v = 0 → Q w = 0 →
    ∃ g : Similitude Q, g.mult = 1 ∧ g.toLinearEquiv v = w

/-- The neighbour sphere of `0` in the affine-polar graph is exactly the nonzero isotropic vectors: adjacency to `0`
is `Q(v−0)=0 ⟺ Q v = 0`. -/
theorem neighborSphere_zero_eq_isotropic (Q : QuadraticForm K V) (v : V) :
    Q (v - 0) = 0 ↔ Q v = 0 := by rw [sub_zero]

/-- **Depth 1 — the isotropic neighbour sphere is one orbit** (given the isolated Witt-on-the-cone input). After
individualizing the origin, the cell of its graph-neighbours is a single `Stab(0)`-isometry-orbit. This is the second
free rung of the induction; it consumes only `WittConeTransitive Q`, no square-class/Gram recovery. -/
theorem depth1_isotropic_sphere_one_orbit {Q : QuadraticForm K V} (hW : WittConeTransitive Q)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hadjv : Q (v - 0) = 0) (hadjw : Q (w - 0) = 0) :
    ∃ g : Similitude Q, g.mult = 1 ∧ g.toLinearEquiv v = w := by
  rw [sub_zero] at hadjv hadjw
  exact hW v w hv hw hadjv hadjw

end ChainDescent.OrbitBaseCase
