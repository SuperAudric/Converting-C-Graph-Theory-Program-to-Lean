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

/-! ## The totally-isotropic prefix — the orbit-level delimiter

The induction's *free prefix* (`span S` totally isotropic) rests on multiplier freedom in `Stab(S)`. The **origin base
`S = {0}`** — the prefix's first step — needs **no Witt input**: the scalar similitudes `x ↦ l·x` already realize every
square multiplier, making `Stab(0)`-orbits square-class-coarse (matching what refinement sees). The complementary wall
side is the multiplier-rigidity lemma promoted to orbits. Together they are `CellsAreOrbits` for the anisotropic shell
at the origin, free of the open core; extending the *free* side past `{0}` to a general totally-isotropic base is what
needs the Witt-decomposition construction of multiplier-realizing similitudes (the gating keystone). -/

/-- The scalar automorphism `x ↦ l • x` as a linear equivalence (`l ≠ 0`). -/
def scalarEquiv (l : K) (hl : l ≠ 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (l • LinearMap.id) (l⁻¹ • LinearMap.id)
    (by ext x; simp [smul_smul, mul_inv_cancel₀ hl])
    (by ext x; simp [smul_smul, inv_mul_cancel₀ hl])

@[simp] theorem scalarEquiv_apply (l : K) (hl : l ≠ 0) (x : V) :
    scalarEquiv l hl x = l • x := by
  simp [scalarEquiv]

/-- The **scalar similitude** `x ↦ l • x`: an automorphism of the affine-polar graph with multiplier `l²`, fixing the
origin. It realizes every **square** multiplier in `Stab(0)` with no Witt input — the engine of the free prefix at the
origin base. -/
def scalarSimilitude (Q : QuadraticForm K V) (l : K) (hl : l ≠ 0) : Similitude Q where
  toLinearEquiv := scalarEquiv l hl
  mult := l * l
  mult_ne := mul_ne_zero hl hl
  map := fun x => by rw [scalarEquiv_apply, QuadraticMap.map_smul, smul_eq_mul]

/-- The `Stab(S)`-orbit relation: `w'` is reachable from `w` by an automorphism fixing `S` pointwise. -/
def StabOrbit (Q : QuadraticForm K V) (S : Set V) (w w' : V) : Prop :=
  ∃ g : Similitude Q, (∀ s ∈ S, g.toLinearEquiv s = s) ∧ g.toLinearEquiv w = w'

/-- **The wall side of the delimiter (orbit level).** At a base containing an **anisotropic** vector, every
`Stab(S)`-orbit preserves the **exact** norm `Q` (the connecting similitude has `μ = 1`, by
`mult_eq_one_of_fixes_anisotropic`). So in the multiplier-dead regime orbits are exact-norm-fine — strictly finer than
the square-class cells refinement sees (`ScratchSimilitudeCap`). This locates the open core at the orbit level:
`CellsAreOrbits` there needs the square-class profile to recover the exact norm. -/
theorem stabOrbit_preserves_norm_of_anisotropic_base {Q : QuadraticForm K V} {S : Set V} {a : V}
    (haS : a ∈ S) (ha : Q a ≠ 0) {w w' : V} (h : StabOrbit Q S w w') : Q w' = Q w := by
  obtain ⟨g, hfix, hgw⟩ := h
  have hμ : g.mult = 1 := mult_eq_one_of_fixes_anisotropic g ha (hfix a haS)
  have hmap := g.map w
  rw [hgw, hμ, one_mul] at hmap
  exact hmap

/-- **The free side of the delimiter at the origin base (no Witt).** At base `{0}` (the depth-1 prefix), the scalar
similitude puts `l • w` in the `Stab({0})`-orbit of `w` for every `l ≠ 0`, with `Q(l•w) = l²·Q w`. So the orbit of an
anisotropic `w` already contains a vector of **every norm in `Q w`'s square class** — `Stab(0)`-orbits are
square-class-coarse, matching exactly what refinement sees. This is `CellsAreOrbits` for the anisotropic shell at the
origin, free of the open core (the isotropic sphere is the complementary `WittConeTransitive` half). -/
theorem stabOrbit_zero_base_scales {Q : QuadraticForm K V} (l : K) (hl : l ≠ 0) (w : V) :
    StabOrbit Q ({0} : Set V) w (l • w) ∧ Q (l • w) = (l * l) * Q w := by
  refine ⟨⟨scalarSimilitude Q l hl, ?_, ?_⟩, ?_⟩
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simp [scalarSimilitude]
  · simp [scalarSimilitude]
  · rw [QuadraticMap.map_smul, smul_eq_mul]

/-! ## Increment 2 — the general free prefix (modulo Witt-decomposition realizability)

The origin-base coarsening (`stabOrbit_zero_base_scales`) used scalars, which only fix `0` and only reach **square**
multipliers. For a general totally-isotropic base `S` the multiplier-`μ` similitudes fixing `S` (for *every* `μ`) are
supplied by the **Witt decomposition** `V = (W ⊕ W') ⊥ U` (Mathlib-absent, the other agent's build) — carried here as
the predicate `WittRealizes Q`. Given it, `Stab(S)`-orbits over a totally-isotropic base are multiplier-coarse (they
reach every norm `μ·Q w`), which is the orbit half of `CellsAreOrbits` for the free prefix; and the delimiter
(`not_multiplierRealizable_of_anisotropic`) shows realizability can hold **only** off the anisotropic vectors — the
precise boundary where the prefix ends and the wall begins. -/

/-- A base `S` is **totally isotropic** when `Q` vanishes on its whole span. -/
def TotallyIsotropic (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ x ∈ Submodule.span K S, Q x = 0

/-- `Stab(S)` **realizes every nonzero multiplier**: for each `μ ≠ 0` some similitude fixes `S` pointwise with that
multiplier. This is the multiplier-freedom the free prefix runs on. -/
def MultiplierRealizable (Q : QuadraticForm K V) (S : Set V) : Prop :=
  ∀ μ : K, μ ≠ 0 → ∃ g : Similitude Q, (∀ s ∈ S, g.toLinearEquiv s = s) ∧ g.mult = μ

/-- **The carried Witt-decomposition theorem (tech debt).** Over every totally-isotropic base, all multipliers are
realizable — the content of the Witt decomposition `V = (W ⊕ W') ⊥ U` (Mathlib-absent). Carried as a named hypothesis;
the parallel Witt build discharges it. The whole free prefix consumes exactly this. -/
def WittRealizes (Q : QuadraticForm K V) : Prop :=
  ∀ S : Set V, TotallyIsotropic Q S → MultiplierRealizable Q S

/-- **Increment 2 — free-prefix orbit coarsening (general base, modulo realizability).** Generalises
`stabOrbit_zero_base_scales` from `{0}` to any base with `MultiplierRealizable Q S`: the `Stab(S)`-orbit of `w` reaches a
vector of norm `μ·Q w` for **every** `μ ≠ 0`. So in the free prefix orbits cannot see the exact norm (nor its square
class), matching the totally-isotropic refinement (where `χ(det G₂)` is constant). The orbit half of `CellsAreOrbits`
for the prefix. -/
theorem stabOrbit_realizable_base_scales {Q : QuadraticForm K V} {S : Set V}
    (hR : MultiplierRealizable Q S) (w : V) {μ : K} (hμ : μ ≠ 0) :
    ∃ w', StabOrbit Q S w w' ∧ Q w' = μ * Q w := by
  obtain ⟨g, hfix, hmult⟩ := hR μ hμ
  refine ⟨g.toLinearEquiv w, ⟨g, hfix, rfl⟩, ?_⟩
  rw [g.map w, hmult]

/-- **The delimiter at the predicate level.** `MultiplierRealizable Q S` can hold only when `S` carries no anisotropic
vector: an anisotropic `a ∈ S` forces every `Stab(S)` multiplier to `1` (`mult_eq_one_of_fixes_anisotropic`), so any
realizable `μ ≠ 1` is impossible. (Caller supplies a witness `μ ≠ 0, 1`, available whenever `|K| ≥ 3` — always, for the
odd-`q` residue.) This is the precise boundary between the free prefix and the wall. -/
theorem not_multiplierRealizable_of_anisotropic {Q : QuadraticForm K V} {S : Set V} {a : V}
    (haS : a ∈ S) (ha : Q a ≠ 0) {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hR : MultiplierRealizable Q S) : False := by
  obtain ⟨g, hfix, hmult⟩ := hR μ hμ0
  have h1 : g.mult = 1 := mult_eq_one_of_fixes_anisotropic g ha (hfix a haS)
  rw [hmult] at h1
  exact hμ1 h1

/-- **Increment 2 capstone — free-prefix orbit coarsening, modulo the carried Witt input.** Given the
Witt-decomposition input `WittRealizes Q`, at any **totally-isotropic** base `S` the `Stab(S)`-orbit of `w` reaches
every norm `μ·Q w`. This is `CellsAreOrbits`' orbit half for the entire free prefix, conditional only on the carried
Witt-decomposition theorem (`modulo {Witt}`). -/
theorem stabOrbit_totallyIsotropic_scales {Q : QuadraticForm K V} (hW : WittRealizes Q)
    {S : Set V} (hS : TotallyIsotropic Q S) (w : V) {μ : K} (hμ : μ ≠ 0) :
    ∃ w', StabOrbit Q S w w' ∧ Q w' = μ * Q w :=
  stabOrbit_realizable_base_scales (hW S hS) w hμ

end ChainDescent.OrbitBaseCase
