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
- `ChainDescent/ScratchOrbitBaseCase.lean` — **base case + delimiter**: empty base (translation-transitive),
  depth-1 isotropic sphere (modulo the isolated `WittConeTransitive`), the multiplier-rigidity delimiter, and the
  origin-base orbit-level delimiter (scalar realization + wall-side norm preservation).

**Next:** Increment 2 (general free prefix, modulo Witt) → Increment 3 (the wall). See §6.

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

- **Increment 2 — general free prefix, modulo Witt.** Extend `stabOrbit_zero_base_scales` from `S = {0}` to any `S`
  with `span S` totally isotropic. Define a `WittDecomposition`/`MultiplierRealizable` predicate (multiplier-`μ`
  similitudes fixing a totally isotropic subspace exist) and prove the step free in that regime. The construction of
  those similitudes is the Witt-decomposition tech debt; carry it as the predicate. **Outcome:** the free prefix is
  `CellsAreOrbits`-proved `modulo {Witt}`.
- **Increment 3 — the wall (the open kernel).** State the kernel predicate (anisotropic base: same square-class
  profile ⟹ same `Stab(S)`-orbit). Reduce it via Witt extension to "square-class profile ⟹ exact-Gram profile."
  This is the genuine research. First buildable sub-step: connect it to `ZProfileSeparates` and try to **upgrade the
  separator to a certifier** — show the joint profile over a frame *determines* (not just separates) the exact Gram.
  This is bounded-WL-dim; expect it to be hard and possibly the GI-frontier.
- **Parallel — Witt extension build.** The shared enabler for Increments 2–3's easy halves and the depth-1 sphere.
  Scope what Mathlib has (`IsometryEquiv`, `exists_orthogonal_basis`, `Anisotropic`) vs the missing extension /
  cancellation / decomposition lemmas. Discharging it converts all of `modulo {Witt}` to unconditional.

**Definition of done for Route B:** `CellsAreOrbits` proved for the affine-polar residue (`modulo {Witt}` acceptable
as tech debt) ⟹ wired through `twinsRealizedByResidualAut_iff_cellsAreOrbits` to a polynomial seal capstone, the
poly twin of `reachesRigidOrCameron_affinePolar`.

---

## 7. Where this sits (Route B vs Route C vs the seal)

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

## 8. Pointers

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
