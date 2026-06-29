# The CellsAreOrbits route — proving the forms-graph poly bound through B (bounded WL-dimension)

> **What this is.** The working doc for **Route B**: proving the affine-polar forms-graph residue is canonized in
> **polynomial** time by the *existing refinement-based* canonizer, via the open core **`CellsAreOrbits`** (= bounded
> WL-dimension of the forms graph). It is the deliberate alternative to **Route C** (constructive form recovery; more
> likely to succeed but a larger build + behavioural change). The value of Route B is structural: **`poly ⟺ B`** — the
> current design reduces the entire forms-graph poly question to this one proposition, which is worth pinning down in its
> own right. This doc scopes *exactly* what B needs, records what is already proved, and lays out the work-forward order
> so a new reader can pick it up cold.
>
> Provenance: the viability investigation (`project_formsgraph_wldim_viability_2026-06-28`), the similitude cap +
> base-case build (this session, 2026-06-29), the Route-A finding (`twinsRealizedByResidualAut_iff_cellsAreOrbits`).

---

## STATUS (read first)

**Live, early.** The base case of the induction is **built and axiom-clean**; the genuine open core (the "wall") is
isolated and precisely stated; Witt is isolated as a carried hypothesis (tech debt). Nothing of the *wall* is proved
yet — it is open both ways (the forms graph may or may not have bounded WL-dimension).

**Built (axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`):**
- `ChainDescent/ScratchSimilitudeCap.lean` — **the cap**: the graph determines `Q` only up to scaling, so refinement
  is capped at the **square class** (`χ(det G₂)` invariant; exact value and singleton square-class are *not*).
- `ChainDescent/ScratchOrbitBaseCase.lean` — **base case + delimiter + free prefix (Increment 2)**: empty base
  (translation-transitive), depth-1 isotropic sphere (modulo the isolated `WittConeTransitive`), the multiplier-rigidity
  delimiter, the origin-base orbit delimiter (scalar realization + wall-side norm preservation), and **Increment 2** —
  the general free-prefix orbit coarsening over any totally-isotropic base modulo the carried `WittRealizes` (= W-dec)
  predicate, with `not_multiplierRealizable_of_anisotropic` pinning the predicate to the free regime.
- `ChainDescent/ScratchWittCone.lean` — **Witt build W0 + W1 (cone-transitivity reduction)**: the orthogonal
  reflection as an isometry (`refl_isometry`, `reflSim`), the swap `refl_swap`, similitude composition `simComp`, the
  `polar ≠ 0` case `cone_case_polar_ne`, the hyperbolic-partner lemma `exists_hyperbolic_partner`, and the **reduction**
  `wittConeTransitive_of_pairing` — `WittConeTransitive Q` now follows from the concrete residual `IsotropicPairing Q`
  (existence of an isotropic vector non-orthogonal to two given isotropic vectors).

**Next:** finish W1 — discharge `IsotropicPairing` (concrete vector-existence, field-genericity casework) ⟹
`WittConeTransitive` unconditional ⟹ depth-1 base case done. Then Increment 3 (the wall). See §6/§7.

**Quality bar:** axiom-clean, no `sorry`/no fresh `axiom`, `native_decide` banned, full build green when ported.

---

## 1. The claim and why it is worth proving on its own

The chain-descent canonizer's cost is a **sum over descent-tree nodes** (not the naive product). For the affine-polar
forms graph the descent is empirically a **single path** (`leaves = 1`, `BranchingNodes = 0`), so the node count is
the path length `Θ(log n)` and the cost is polynomial — **provided** every cell the descent individualizes is a single
orbit, so it never has to branch. That proviso is exactly:

> **B (`CellsAreOrbits`).** Along the descent, at every partial base `S`, each refinement cell equals a single
> `Stab(S)`-orbit. Equivalently: the WL-closure (square-class refinement) partition equals the orbit partition =
> **bounded WL-dimension** of the forms-graph families.

The central fact this whole route rests on:

> **`poly ⟺ B`.** The refinement-based canonizer runs in polynomial time on the forms-graph residue **iff** B holds.
> (⟸ B ⟹ single path ⟹ poly node count ⟹ poly, per-node already poly. The reduction wiring is the landed
> `twinsRealizedByResidualAut_iff_cellsAreOrbits`, Cascade.lean, plus the sum-over-nodes budget.)

So even short of a full proof, **B is the precise, complete bottleneck of the refinement route** — not a speculative
helper. Pinning it (true, false, or conditional) is a result in itself.

**Honesty up front — B is open *both ways*.** We do not know B is true. The forms graph could have *unbounded*
WL-dimension (the "node-4 wall"); empirics (single path) support B but only reach small `d`. This is why Route C
(which does not need B; see §7) is kept in view. Route B is chosen here because `poly ⟺ B` is independently valuable and
the base case is real, **accepting that it may be a delay relative to the more-likely-to-succeed Route C.**

---

## 2. The object, precisely

- **Graph.** `V = K^d` (`K` a finite field, `d = 2m`), adjacency `Q(x − y) = 0` for a nondegenerate quadratic form `Q`.
- **Automorphisms.** The affine **similitude** group: translations ⋊ linear similitudes `g` (`Q(g x) = μ(g)·Q x`,
  `μ ≠ 0`). An **isometry** is `μ = 1`. Modelled in Lean as `OrbitBaseCase.Similitude Q` (`g : V ≃ₗ V`, `mult`,
  `mult_ne`, `map`).
- **Refinement sees only the square class** (the cap, §3): the finest pointwise form-data any
  graph-isomorphism-invariant can carry is `χ(det G₂)` = square classes of even-order Gram minors. The *exact* form
  value is not a graph invariant at all.

---

## 3. What is already proved (the foundation)

### 3a. The cap — refinement's ceiling (`ScratchSimilitudeCap.lean`)
The graph fixes `Q` only up to scaling, so any iso-invariant is scaling-invariant:
- `affinePolarAdj_smul_eq` — graph of `c•Q` = graph of `Q`.
- `chi_pairForm_smul` — `χ(det G₂)` IS scaling-invariant (`c²` killed by `χ`): the legitimate pair observable.
- `chi_singleton_smul` — singleton `χ(Q·)` flips by `χ(c)`: NOT invariant (the formal "singleton is binary").
- `pairForm_value_not_invariant` — exact value scales by `c²`: not recoverable by **any** iso-invariant.

**Consequence:** B can only ever be certified from square-class data. The exact-Gram data the orbit "really" needs is
not refinement-visible — that gap *is* the wall.

### 3b. Base case + delimiter (`ScratchOrbitBaseCase.lean`)
- `affinePolar_empty_base_one_orbit` — **depth 0**: one orbit (translations). Free.
- `depth1_isotropic_sphere_one_orbit` — **depth 1**: isotropic neighbour sphere = one orbit, modulo the isolated
  input `WittConeTransitive Q` (Witt-on-the-cone; Mathlib-absent — tech debt, §5).
- `mult_eq_one_of_fixes_anisotropic` / `mult_eq_one_of_fixes_span_anisotropic` — **the delimiter**: a similitude
  fixing an anisotropic vector (or one in `span S`) has `μ = 1`. So multiplier freedom in `Stab(S)` ⟺ `span S`
  totally isotropic.
- `stabOrbit_zero_base_scales` — **free side at the origin (no Witt)**: scalar similitudes put a vector of every
  square-class norm in the `Stab({0})`-orbit ⟹ origin-base orbits are square-class-coarse, matching refinement.
- `stabOrbit_preserves_norm_of_anisotropic_base` — **wall side**: at an anisotropic base, orbits preserve the *exact*
  norm (μ = 1) ⟹ orbits are norm-fine, strictly finer than square-class cells. The wall, located at the orbit level.

---

## 4. The induction, and exactly what B needs

B is proved by **induction on base size `k`** (`P(k)` = "every cell at a size-`k` base is a single `Stab(S)`-orbit"):

- **Base `P(0), P(1)`** — done (§3b), modulo Witt for the isotropic sphere.
- **Step `P(k) → P(k+1)`** — the content. By **Witt extension** ("same *exact* Gram-profile to `S` ⟹ same orbit",
  Mathlib-absent, tech debt §5) the step reduces to its only open part:

> **The kernel.** At base `S`, two vectors with the same **square-class** Gram-profile to `S` have the same
> **exact**-Gram-profile to `S`, modulo `Stab(S)`'s multipliers.

This splits exactly along the delimiter:

| Regime | `span S` | `Stab(S)` multipliers | Kernel status |
|---|---|---|---|
| **Free prefix** | totally isotropic (`dim ≤` Witt index `≤ d/2`) | free | multipliers absorb the square→exact gap ⟹ **free, modulo Witt** |
| **Wall (tail)** | contains an anisotropic vector (forced once you span `> d/2` dims) | `μ = 1` only | square-class must genuinely pin exact Gram = **bounded WL-dim = open** |

So B = [free prefix: tech debt (Witt)] + [anisotropic tail: the genuine open kernel]. The open content is `~d/2`
levels, sharply: **"the relative spheres the canonizer visits in the multiplier-dead regime are single orbits."**

---

## 5. Tools

1. **Witt extension / decomposition** — *tech debt* (known-true classical geometry, Mathlib-ABSENT; AUDIT-W rates it
   LARGE, single-cluster-reused). Discharges `WittConeTransitive`, the free prefix, and the easy half of every step.
   Carry it as a named hypothesis (`modulo {Witt}`) and prove forward — this is the standard project move and unblocks
   the entire scaffold. **It does NOT cross the wall.**
2. **The cap (§3a, proved)** — bounds what refinement can see (square class). Tells you the wall is real, not a
   formalization gap.
3. **The delimiter (§3b, proved)** — bounds *where* the free regime ends (totally isotropic `span S`).
4. **Gauss / quadratic-character machinery** (`PairForm`, `PerAnchorBound.c0_le_threequarters`, the matching
   `AffinePolarSeal.exists_pow_matching_block`, `ProfileReduction.ZProfileSeparates`) — the existing apparatus. **Caveat
   (critical):** as built it is a **separator** (square-class profiles *distinguish* pivots at an `Θ(log n)` base →
   quasipoly), **not a certifier** (it does not show an intermediate cell is a single orbit). The kernel needs a
   *local certification*, strictly more than separation. Re-using this machinery for the kernel means strengthening
   "profiles separate" to "the joint square-class profile *determines the orbit* at every partial base."

---

## 6. Work-forward plan (ordered increments)

- **Increment 2 — general free prefix, modulo Witt — ✅ DONE (2026-06-29, axiom-clean, `ScratchOrbitBaseCase.lean`).**
  Generalised `stabOrbit_zero_base_scales` from `S = {0}` to any totally-isotropic base via the carried predicate
  `WittRealizes Q` (= the §7 **W-dec** input: multiplier-`μ` similitudes fixing a totally-isotropic subspace exist).
  Landed: `TotallyIsotropic`, `MultiplierRealizable`, `WittRealizes` (defs); `stabOrbit_realizable_base_scales` (orbit
  reaches every norm `μ·Q w` from realizability); `stabOrbit_totallyIsotropic_scales` (the capstone, `modulo {W-dec}`);
  and `not_multiplierRealizable_of_anisotropic` (the predicate-level delimiter — realizability fails the instant `S`
  carries an anisotropic vector). **Outcome:** the free prefix's *orbit half* of `CellsAreOrbits` is proved
  `modulo {W-dec}`. (Its *cell half* — same refinement profile ⟹ same orbit — additionally needs **W-ext**; that
  wiring is folded into Increment 3's frame, since it is the same square-class→exact-Gram statement specialised to the
  free regime where it is discharged by realizability.)
- **Increment 3 — the wall (the open kernel).** State the kernel predicate (anisotropic base: same square-class
  profile ⟹ same `Stab(S)`-orbit). Reduce it via Witt extension to "square-class profile ⟹ exact-Gram profile."
  This is the genuine research. First buildable sub-step: connect it to `ZProfileSeparates` and try to **upgrade the
  separator to a certifier** — show the joint profile over a frame *determines* (not just separates) the exact Gram.
  This is bounded-WL-dim; expect it to be hard and possibly the GI-frontier.
- **Parallel — Witt build (now the higher priority; fully scoped in §7).** The shared enabler for Increments 2–3's
  easy halves and the depth-1 sphere. Mathlib has the primitives but no Witt theory; the staged plan + difficulty +
  recommendation are in **§7**. The cheap first slice (W0+W1) discharges `WittConeTransitive` and makes the depth-1
  base case unconditional.

**Definition of done for Route B:** `CellsAreOrbits` proved for the affine-polar residue (`modulo {Witt}` acceptable
as tech debt) ⟹ wired through `twinsRealizedByResidualAut_iff_cellsAreOrbits` to a polynomial seal capstone, the
poly twin of `reachesRigidOrCameron_affinePolar`.

---

## 7. The Witt build — detailed scope (current priority)

Witt is the shared enabler (depth-1 sphere, the free prefix, and the easy half of every inductive step). It is **tech
debt** (known-true classical geometry, char ≠ 2 — fine for the odd-`q` route; char 2 is a separate track regardless),
but is being built now rather than carried. Verified against current Mathlib (2026-06-29): **Mathlib has no Witt
theory, but all the primitives are present**, so this is a real build, not from scratch.

### 7.1 What's needed (three facts, increasing strength)
- **W-cone** — isometries are transitive on nonzero **isotropic** vectors. Discharges `WittConeTransitive` ⟹ makes
  `depth1_isotropic_sphere_one_orbit` **unconditional** (the depth-1 base case, done).
- **W-ext** — the **Witt extension theorem**: an isometry between subspaces of a nondegenerate space extends to a
  global isometry (equivalently: fixing a subspace `S`, isometries are transitive on vectors with equal exact-Gram
  profile to `S`). Discharges the **easy half** of every inductive step.
- **W-dec** — the **Witt decomposition**: `V = (maximal totally isotropic ⊕ hyperbolic dual) ⊥ anisotropic`; and
  multiplier-`μ` similitudes fixing a totally isotropic subspace exist. Discharges the **general free prefix**
  (Increment 2).

### 7.2 Mathlib support (present — the backbone)
- `Module.reflection (h : f x = 2) : M ≃ₗ[R] M` (`Mathlib/LinearAlgebra/Reflection.lean`) — the generic reflection
  `y ↦ y − f(y)•x`. Specializes to the orthogonal reflection `τ_v` by taking `f = polar Q (·) v / Q v` (then
  `f v = polar Q v v / Q v = 2`). The reflection *map* is free; its *isometry* property w.r.t. `Q` is the lemma to add.
- `LinearMap.BilinForm.exists_orthogonal_basis` (needs `Invertible (2:K)`) — diagonalization.
- `BilinForm.orthogonal` + `isCompl_orthogonal_of_restrict_nondegenerate` + `isCompl_span_singleton_orthogonal`
  (`Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`) — orthogonal direct-sum decompositions (the structural
  backbone of the induction).
- `QuadraticForm.Isometry` / `IsometryEquiv`, `polarBilin`, `Nondegenerate`, `Anisotropic`, `Radical`.

### 7.3 Gaps to build (no Witt theory in Mathlib)
| Stage | Target | Difficulty | Value |
|---|---|---|---|
| **W0** | orthogonal reflection `τ_v` is an isometry; `Q u = Q v ∧ Q(u−v)≠0 ⟹ τ_{u−v}` maps `u ↦ v` | ✅ **DONE** (`ScratchWittCone`) | foundation / reusable atom |
| **W1** | **cone transitivity** — `polar≠0` case ✅ done; **reduced** to the residual `IsotropicPairing` (∃ isotropic `w` non-orthogonal to both) via `wittConeTransitive_of_pairing` + the partner lemma `exists_hyperbolic_partner` | **Reduced**; residual = `IsotropicPairing` (Medium, field-genericity casework) | discharges `WittConeTransitive`; completes depth-1 |
| **W2** | anisotropic-shell transitivity (isometries transitive on a fixed nonzero norm) | **Medium** | relative-sphere structure |
| **W3** | **Witt extension theorem** (induction on `dim U`; orthogonal-complement peeling; isotropic case via hyperbolic completion) | **Large** | step's easy half |
| **W4** | **Witt decomposition** + multiplier realization fixing totally isotropic subspaces | **Large** | general free prefix (Increment 2) |

### 7.4 Build order + recommendation
- **W0 ✅ done, W1 reduced** (`ScratchWittCone.lean`, axiom-clean). The reflection engine is built and
  `WittConeTransitive` is reduced to the concrete residual `IsotropicPairing`. **Remaining for W1:** discharge
  `IsotropicPairing` — a finite-field vector-existence statement (the isotropic cone of a dim-`≥4` nondeg form is not
  covered by two hyperplanes), provable via `exists_hyperbolic_partner` + casework (edge cases at `|K|=3`, and the
  `polar Q f g ≠ 0` correction). Once landed, `wittConeTransitive_of_pairing` makes the depth-1 base case
  unconditional, *no hypothesis*.
- **W2** next only if the relative-sphere structure is wanted explicitly before the wall.
- **W3 + W4 are LARGE** and — critically — only convert `modulo {Witt}` → unconditional on the **scaffold**; they do
  **not** touch the wall (the open kernel survives regardless). So the honest cost-benefit: building them buys a cleaner
  final statement, **not** progress on the open core. Recommended to defer them as carried hypotheses until the wall's
  tractability is assessed (Increment 3), and pull them in only when closing out.

**Net:** W0+W1 is a cheap, clean, self-contained win that completes the base case. W3+W4 are the genuine LARGE build and
are defensible to keep as `modulo {Witt}` tech debt until the open core is understood, since they don't advance it.

---

## 8. Where this sits (Route B vs Route C vs the seal)

- **The seal (`AffinePolarSeal.reachesRigidOrCameron_affinePolar`, in build).** Proves **quasipoly** (the matching =
  a *separator*, `Θ(log n)` base). It does **not** prove B; B is strictly stronger (separation at one full base vs
  cells=orbits at *every* partial base). Route B is the upgrade quasipoly → poly.
- **Route C (constructive form recovery).** A *different* route to the same orbits: recover a form representative
  **geometrically** (not by counting), then canonicalize via the known group `GO(Q)`. It **does not depend on B** — it
  works whether B is true or false, because the form exists unconditionally and geometric recovery bypasses
  refinement. It is *not* an alternate form of B (counting → B; geometry → Route C); the only way it could collapse
  into B is if its recovery were done via WL counting, which it deliberately is not. Route C is **tech debt, not open
  math** (known-true polar-space coordinatization), but a larger build + behavioural change (needs the form-recovery
  oracle / a constructive Lean recovery). **If B is false, Route C is the only route** — that is its real value.
- **Why Route B anyway.** `poly ⟺ B` is independently valuable; the base case is real; and a refinement-only poly
  proof (if B is true) is cleaner than Route C's construction. Chosen with eyes open that Route C is more likely to
  succeed and this may be a delay.

---

## 9. Pointers

- **Built modules:** `GraphCanonizationProofs/ChainDescent/ScratchSimilitudeCap.lean`,
  `GraphCanonizationProofs/ChainDescent/ScratchOrbitBaseCase.lean` (decls described in `PublicTheoremIndex.md`).
- **Existing machinery to reuse:** `PairForm` (`pairForm`, `detG2_eq_pairForm`), `PerAnchorBound`
  (`c0_le_threequarters`), `AffinePolarSeal` (`exists_pow_matching_block`, `reachesRigidOrCameron_affinePolar`),
  `ProfileReduction` (`ZProfileSeparates`, `jointIsoCount`), `Cascade` (`twinsRealizedByResidualAut_iff_cellsAreOrbits`,
  `CellsAreOrbits`).
- **Viability analysis + the route fork:** memory `project_formsgraph_wldim_viability_2026-06-28`.
- **The seal / quasipoly build:** `chain-descent-formsgraph-wldim-plan.md` (STATUS + §1).
- **Route C / cameron context:** `chain-descent-formsgraph-wldim-plan.md` §11.10–§11.14; `chain-descent-ir-blindspot-solver.md`.
- **Literature (WL-dim open both ways):** memory `reference_srg_wl_literature_2026-06-17`.
