# The CellsAreOrbits route — proving the forms-graph poly bound through B (bounded WL-dimension)

> **What this is.** The working doc for **Route B**: proving the affine-polar forms-graph residue is canonized in
> **polynomial** time by the *existing refinement-based* canonizer, via the open core **`CellsAreOrbits`** (= bounded
> WL-dimension of the forms graph). It is the deliberate alternative to **Route C** (constructive form recovery; more
> likely to succeed but a larger build + behavioural change). The value of Route B is structural: **`poly ⟸ B`** (B is
> *sufficient* for poly; a 2026-06-29 handoff-review correction of the earlier `poly ⟺ B` slogan — see §1 KNOWN GAP) —
> the current design reduces the entire forms-graph poly question to this one proposition, which is worth pinning down in
> its own right. This doc scopes *exactly* what B needs, records what is already proved, and lays out the work-forward
> order so a new reader can pick it up cold.
>
> Provenance: the viability investigation (`project_formsgraph_wldim_viability_2026-06-28`), the similitude cap +
> base-case build (this session, 2026-06-29), the Route-A finding (`twinsRealizedByResidualAut_iff_cellsAreOrbits`).
>
> **⚠ Naming note (avoid confusion).** "B" here is the *proposition* `CellsAreOrbits` (= bounded WL-dim). This doc's
> "Route B = prove poly **through** B" is the **refinement route**, which corresponds to the forms-graph plan's
> (`chain-descent-formsgraph-wldim-plan.md`) **Route A** ("prove the existing harvest poly") and its **Route B**
> ("monovariant node-count wrapper") — both rest on proving `CellsAreOrbits`. It is **unrelated** to START-HERE's
> "Route B" (the *superseded imprimitive branch*). This doc's **Route C** (constructive form recovery) **is the same**
> as the plan's Route C. When in doubt, refer to the *content* (`CellsAreOrbits` vs form-recovery), not the letter.

---

## STATUS (read first)

**Live — base case done, the wall isolated and *probed crackable*.** The base case of the induction is **built and
axiom-clean**; the node-count bridge + transport seam are built (modulo the `canonForm` placeholder); the genuine open
core (the "wall") is **isolated as one predicate `WallKernel`** (3a, axiom-clean) and Witt is a carried hypothesis (tech
debt). **The wall is no longer "open both ways":** the 2026-06-29 crackability + depth probes (§6 Increment 3) found it
is **true and crackable** — the iterated `χ(det G₂)` 2-WL observable determines the orbit with `O(1)` iteration depth,
uniformly in `d, |S|, q,` type. So the live work is the **Lean 3c proper** (prove `WallKernelFor` for that observable,
exploiting the bounded depth). What is *not yet proved in Lean* is `WallKernel` itself (= the wall) and the `canonForm`
lift; the empirics strongly support both.

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
- `ChainDescent/ScratchNodeCountBridge.lean` — **★ Increment 0, the node-count bridge + transport-seam depth-1 core
  (LANDED)**: the weaker scheduler-matching predicate `SelectedCellIsOrbit` + `selectedCellIsOrbit_of_cellsAreOrbits`
  (the §4 math discharges it for free); the **completeness core** `selectedCell_single_stabOrbit` (consumed cell = one
  `StabilizerAt`-orbit — the piece prune *soundness* alone does not give) + `selectedCell_prune_sound_complete`; the
  node-count re-export `spine_node_count_le` (`≤ n`, from the landed `defaultSpineChain_reaches_leaf`); the capstone
  `certifiedSinglePath_of_disposition` (disposition ⟹ **both** poly ingredients); **and the transport seam** —
  `repTransport` (depth-1 rep-choice invariance: orbit aut `g ∈ Stab(S)` carrying `v₁ ↦ v₂` makes the `v₂`-descent
  pulled-back-by-`g` `samePartition` the `v₁`-descent), **`baseTransport`** (the general `g`-equivariance at *any* base
  `T` vs `g(T)` — subsumes "iterate across levels" since `g` is global), and **`labelledAdj_rankPerm_transport`** (the
  `canonAdj`-lift atom: labelled output invariant under an automorphism relabel of the discrete leaf colouring, via
  `rankPerm_comp` + `labelledAdj_eq_of_isAut`). Remaining = the `samePartition`→*literal*-relabel step, which is exactly
  what `canonForm` (lex-min over `DirAssignment`s, a §15.7 placeholder) supplies.
- `ChainDescent/ScratchWallKernel.lean` — **★ Increment 3a — the wall isolated as one predicate (DONE)**: the open
  content at an anisotropic base is named `WallKernel` (square-class profile *determines* exact Gram), with the
  reduction proved around it — soundness `stabOrbit_imp_sameExactGram_of_anisotropic` (free, via the μ=1 delimiter +
  `similitude_polar`), the carried Witt-extension input `WittExtendsToOrbit`, and the isolation capstone
  `stabOrbit_iff_sameSquareClass_of_wallKernel` (at an anisotropic base, modulo {Witt}, `CellsAreOrbits` ⟺ `WallKernel`).
  **Made observable-PARAMETRIC** after the 3c probe — `WallKernelFor Obs` + `stabOrbit_iff_obs_of_wallKernelFor`: the
  single-round `WallKernel` is the **refuted separator** instance (`= SameSquareClass`, FALSE at a bounded base), and
  the framework now aims at the *right* observable `Obs` = the iterated `χ(det G₂)` 2-WL (any graph-invariant `Obs` is
  orbit-sound for free, so the reduction is identical). (`WallKernel` = the exact-Gram form of the seal's
  `ZProfileSeparates`.) **Probe status (§6 Increment 3): the iterated-observable `WallKernelFor` is empirically TRUE
  with `O(1)` determination depth, uniformly** — so 3c is the live Lean target, not a frontier wall.

**Next — current frontier (2026-06-29, post depth-probe).** The structural scaffold is *done*: node-count bridge
(Increment 0), transport seam, and the wall isolation (3a) are all built and axiom-clean. The crackability + depth
probes returned **GO** (the wall is true, crackable, `O(1)` depth). So the live work, in order:
1. **★ Lean 3c proper (the prize).** Prove `WallKernelFor Obs` (`ScratchWallKernel`) for `Obs` = the iterated
   `χ(det G₂)` 2-WL observable — i.e. the bounded-depth character-inversion. Exploit the probed `O(1)` depth: this is a
   *fixed* (1–2) number of character-sum rounds, not an unbounded WL fixpoint, so it reuses `pairCharSum_factor_gen` /
   `gaussSum_sq_ne_zero` / the `χ(det G₂)↔Z_u` bridge as a small fixed-round object. **This is the open math and the
   payoff.**
2. **3a-equivariance + 3b** — the geometric similitude-equivariance of `WallKernel` ("every base up to aut", analogue
   of `baseTransport`); the count-observable bridge `WallKernelFor` ↔ bounded-base `ZProfileSeparates`.
3. **Loose ends (low-leverage, land any time):** discharge `IsotropicPairing` (finishes W1 / the depth-1 base case);
   the `canonForm` lift of the transport seam (gating prereq, *not* Route-B-specific — blocked on the §15.7 placeholder).
4. **Residual empirics (optional, for certainty):** push the depth probe to `d=8`+ and more base-types (pure-Python
   memory capped it at `d≤6`; a C/numpy rewrite reaches further).

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

The reduction this route rests on — stated **honestly**, because the Lean is weaker than the slogan:

> **`poly ⟸ B` (B is *sufficient*; the chain has a MISSING pillar).** B gives poly along three steps:
> 1. **per base** — `twinsRealizedByResidualAut_iff_cellsAreOrbits` (LANDED, `Cascade.lean`): WL-cells at base `S` =
>    `Stab(S)`-orbits.
> 2. **assembly** — B at *every* descent node ⟹ the consumed cell is a single orbit at each step ⟹ the descent tree
>    is a **single path**. **[NOT landed** — the iff is *per-base*; assembling it across descent nodes needs the spine
>    model.]
> 3. **node-count → poly** — single path of length `= base = Θ(log n)` ⟹ poly node count ⟹ poly (per-node already
>    poly). **[NOT landed** — a *meta* budget argument; the project formalizes **no runtime model**, so every seal is
>    structural and "poly" is always meta.]

> **⚠ KNOWN GAP — this is NOT yet `poly ⟺ B` in Lean.** Steps 2 + 3 are the **node-count bridge** (§6, Increment 0),
> the route's *actually-missing pillar*. Without it, proving B and plugging into the existing infra
> (`separatesAtBoundedBase_of_twinsRealized`) yields only `SeparatesAtBoundedBase` with bound `=` base size `= Θ(log n)`
> `=` **the quasipoly seal you already have** — *not* poly. And the base is irreducibly `Θ(log n)` (spanning +
> group-order + information bound, established this session), so the base-size route *cannot* reach poly; the
> node-count bridge is the **only** mechanism that makes Route B beat quasipoly.

So B is the *math* core (sufficient; unproven in Lean but empirically supported — probed crackable, §6 Increment 3), but
it is **not the complete bottleneck**: the node-count bridge is a second piece — pure spine combinatorics, independent
of Witt and the wall (now built, modulo the `canonForm` placeholder). Pinning B (true,
false, or conditional) is a real result; but it only *pays off* through the bridge.

**Honesty up front — B is unproven in Lean, but the empirics now strongly support it.** We do not yet have a Lean proof
of B (the wall, `WallKernel`). Earlier this was "open both ways"; the 2026-06-29 crackability + depth probes (§6
Increment 3) **shifted the evidence decisively toward B being true**: the iterated `χ(det G₂)` 2-WL observable
determines the orbit with `O(1)` iteration depth, uniformly in `d, |S|, q,` type (orbit counts grown to 324). So the
"node-4 wall" is, for this family, empirically *not* a wall — it is a bounded-depth inversion awaiting formalization.
Route C (which does not need B; see §7) is still kept in view as the fallback if 3c stalls. Route B is chosen here
because `poly ⟸ B` is independently valuable and the structural scaffold is real, **accepting that it may be a delay
relative to the more-likely-to-succeed Route C.**

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

- **★ Increment 0 — the node-count bridge — PROVABLE CORE ✅ DONE (`ScratchNodeCountBridge.lean`, axiom-clean).** The
  route's actually-missing pillar (§1 KNOWN GAP), Witt- and wall-independent. **Grounding finding: the bridge is mostly
  *assembly* over a near-complete substrate** — three of its four ingredients are already landed, so the doc's earlier
  "build a node-count bridge" framing overstated what was missing:

  | Bridge ingredient | Status |
  |---|---|
  | node count `≤ n` (single path reaches a discrete leaf in `≤ n` levels) | **LANDED** — `defaultSpineChain_reaches_leaf` (`ChainDescent.lean`) |
  | canonical well-defined / direction-invariant | **LANDED** — `spine_branch_independent` + `IsLeaf` spine-invariance |
  | prune *soundness* (drop an orbit-equivalent sibling) | **LANDED** — `orbit_pathFixing_sound` / `covered_sound` (`Cascade.lean`) |
  | per-node firing (CellsAreOrbits ⟹ harvest cert) | **LANDED** — `colourMatch_exists_of_cellsAreOrbits` (`CascadeOracle.lean`) |
  | prune *completeness* (consumed cell = one orbit ⟹ one sibling-class) | **✅ BUILT this increment** — `selectedCell_single_stabOrbit` |

  - **CORRECTION — do NOT reuse `exists_potential_descent`.** That monovariant bounds the base *size* to `2^|T₀| ≤
    Φ(∅)`, i.e. `O(log n)` — it is the **quasipoly-*base* engine** (what the banked seal carries). Node *count* is a
    different quantity and is already `≤ n` for free (`defaultSpineChain_reaches_leaf`), independent of base size.
    Conflating the two would re-derive quasipoly. (Supersedes the plan's *"Route B — reuse `exists_potential_descent`"*
    framing for this purpose.)
  - **CORRECTION — the missing pillar is prune *completeness*, not node-count.** Soundness ("the dropped sibling was
    isomorphic") was landed; what `SelectedCellIsOrbit` adds is *completeness* — the consumed cell is a *single* orbit,
    so there is exactly one sibling-class and the cheap single path branches not at all. Built: `selectedCell_single_stabOrbit`.
  - **Keyed on the WEAKER predicate, as planned.** `SelectedCellIsOrbit` = `CellsAreOrbits` restricted to `sel`'s
    targeted cell (the scheduler only individualizes there; empirically `Phase2Nodes = 0`). The §4 math (full
    `CellsAreOrbits`, modulo Witt + the wall) discharges it for free (`selectedCellIsOrbit_of_cellsAreOrbits`).
  - **Capstone built:** `certifiedSinglePath_of_disposition` — `SinglePathDisposition` (the weak disposition at every
    base) delivers **both** poly ingredients: bounded nodes (`≤ n`) **and** every consumed cell certified one residual
    orbit. Packaged as `CertifiedSinglePath`.
  - **★ Transport seam (Increment-0 residual) — DEPTH-1 CORE + ITERATE + LIFT-ATOM ✅ BUILT.** That a
    `CertifiedSinglePath` *computes the iso-invariant canonical* = representative-choice invariance of the leaf canonical
    over certified single-orbit cells. Built (all axiom-clean):
    - **Depth-1 core** `repTransport`: an orbit aut `g ∈ Stab(S)` carrying rep `v₁ ↦ v₂` makes the `v₂`-descent (pulled
      back by `g`) `samePartition` the `v₁`-descent. Mechanism: cross-config `warmRefine_transport` +
      `warmRefine_congr_samePartition`.
    - **Iterate across levels** `baseTransport`: the general `g`-equivariance — for *any* base `T` and automorphism `g`,
      the descent at `g(T)` is the `g`-relabeling of the descent at `T`. Because `g` is **global**, this holds at every
      base (incl. a leaf), so it subsumes the level-by-level iteration in one lemma — no induction needed.
      (`repTransport_eq_baseTransport_instance` confirms `repTransport` is its `S`-fixing instance.)
    - **Lift atom** `labelledAdj_rankPerm_transport`: the canonical *output* `labelledAdj (rankPerm π) adj` is invariant
      under a `g`-relabel of the discrete leaf colouring (via `rankPerm_comp` + `labelledAdj_eq_of_isAut`).
    - **★ Remaining (precise):** `baseTransport` delivers `samePartition`, not a *literal* `π₂ = π₁ ∘ g`, because
      `individualizedColouring` labels by *index* (so `g` moves literal colour values while preserving the partition);
      `rankPerm`/`labelledAdj` read colour values, so the lift atom needs the literal relabel. Bridging
      `samePartition` → equal labelled canonical is exactly the job of **`canonForm`** (lex-min over `DirAssignment`s,
      designed to depend only on partition + graph) — a §15.7 *placeholder*. So the lift is complete **modulo
      `canonForm`**. Final "poly time" stays meta (no runtime model — do not aim for a runtime-complexity theorem).
      This whole seam is the rep-choice analogue of the landed `spine_branch_independent` (direction-invariance).
  - **Why this was first:** the base is irreducibly `Θ(log n)`, so this is the *only* path to beat quasipoly. The
    grounding answered the "can it even be expressed?" question affirmatively — the substrate carries it — so Route B's
    poly is *not* a priori collapsed into the banked quasipoly; the live obligation is the transport seam + the §4 math.
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
- **★ Increment 3 — the wall (the open kernel). PLAN (2026-06-29, grounded against the seal source).** Grounding
  finding: the wall is **not a new object** — the whole route reduces, through the *existing* seal chain
  `ZProfileSeparates → QProfileSeparatesAtBase → IsotropySeparatesAtBase`, to **`ZProfileSeparates`** (*agreeing joint
  isotropic counts `Z_u(S)` over every sub-frame `S ⊆ T` ⟹ agreeing exact `Q`-profile*), which is already
  *determination*-flavored. The wall is `ZProfileSeparates` **with the base `T` shrunk from the matching `Θ(log n)` to
  the `O(d)` frame**:

  | | base | status | gives |
  |---|---|---|---|
  | seal | `T` = matching, `Θ(log n)` | ✅ PROVEN via `c0_le_threequarters` (≤¾ fail/anchor) + union bound (`reachesRigidOrCameron_affinePolar`) | quasipoly |
  | **wall** | `T` = `O(d)` frame | ✗ OPEN | poly |

  **Why the gap is fundamental to the current method:** `c0_le_threequarters` is a *constant-fraction-per-anchor* bound
  (each good anchor separates ≥¼ of pairs); a fraction bound separates all `~|V|²` pairs only by union-bounding over
  `Θ(log n)` anchors — it **structurally cannot** reach an `O(d)` base. Shrinking the base needs "each anchor kills a
  fraction" replaced by "the `O(d)`-frame count-profile **determines** the orbit" — a *different kind of argument*.

  **Three sub-steps:**
  - **3a — ✅ DONE (`ScratchWallKernel.lean`, axiom-clean).** The open content at an anisotropic base is isolated as a
    single predicate, with the reduction proved around it: soundness `stabOrbit_imp_sameExactGram_of_anisotropic` (free,
    μ=1 delimiter + `similitude_polar`), carried `WittExtendsToOrbit` (Witt tech debt), and the isolation capstone — at
    an anisotropic base, **modulo {Witt}, `CellsAreOrbits` ⟺ `WallKernel`**. (Geometric `Similitude`/orbit setting,
    extending `ScratchOrbitBaseCase`.) **★ Made observable-PARAMETRIC** (`WallKernelFor Obs` +
    `stabOrbit_iff_obs_of_wallKernelFor`) after the 3c probe (below): the single-round `WallKernel` (= `SameSquareClass`
    instance) is the **refuted separator** (FALSE at a bounded base); the framework now aims at `WallKernelFor Obs` for
    the *right* observable `Obs` = the iterated `χ(det G₂)` 2-WL — any graph-invariant `Obs` is orbit-sound for free, so
    the reduction is identical. **Deferred to next:** geometric similitude-*equivariance* of the kernel ("every base up
    to aut", analogue of `baseTransport`); the count-observable bridge to bounded-base `ZProfileSeparates` (3b).
  - **3b.** Prove certifier ⟹ separator (bounded-base `ZProfileSeparates` ⟹ the seal's separation) and isolate the
    converse's extra requirement — locates the gap as a Lean object.
  - **3c (the research).** Replace the `c0` *fraction* bound with **Fourier/character inversion**: the counts `Z_u(S)`
    *are* character sums in the Gram data (exactly what `ObservableCountBridge` / `pairCharSum_factor_gen` expose), so
    "counts over all sub-frames of the frame determine the `Q`-profile" is a **moment-inversion / non-singularity**
    statement. Concrete target: the map `Q-profile ↦ (Z_u(S))_{S⊆frame}` is **injective**, via non-singularity of the
    associated character matrix. The natural strengthening of the existing Gauss machinery from *bounding* to
    *inverting* — reuses `pairCharSum_factor_gen`, `gaussSum_sq_ne_zero`, the `χ(det G₂)↔Z_u` bridge.

  **Fallbacks + criteria** (built in): if inversion is non-singular only for large `q` → **partial `CellsAreOrbits`
  (large-`q`)** = a real poly result for a sub-family; if it hits a genuine non-degeneracy obstruction = the frontier →
  formalize **wall ⟺ bounded-WL-dim** (clean meta-result) = the decisive signal to bank quasipoly + pivot to Route C.

  - **★★★ 3c CRACKABILITY PROBE — DONE (2026-06-29; Python probes in scratchpad, methodology below).** Tested
    `CellsAreOrbits` directly: compare the actual refinement partition to the true `Stab(S)`-orbit partition
    (`φ_S(v)=(Q(v),polar(v,s)_s)` exact when span(S) anisotropic; scaling-class when totally isotropic — the delimiter,
    confirmed empirically). Swept `VO^±_4(q)` `q∈{3,5,7,11}` and `VO^±_6(3)`. **Findings (each an insight):**
    1. **`CellsAreOrbits` holds at every SPANNING anisotropic (μ=1) base even with plain 1-WL** — uniformly, all `q,d`,
       both types. The only over-merges are the μ-free (totally-isotropic-span) prefix = tech debt (the delimiter).
    2. **1-WL is INSUFFICIENT at the bounded *single-anchor* μ=1 base** (`S={0,a}`, `a` anisotropic): over-merges, and
       the gap GROWS with `q` (orbits `12,30,56,132`; 1-WL stuck `≈10–11`). Even iterated/pivot-augmented *binary* 1-WL
       stays stuck. So WL-dim `>1` anchor with 1-WL.
    3. **The seal's single-round `Z_u(S)` joint-count ALSO under-determines at the bounded base** (`10<12`, `11<30`, …)
       — it is a large-base *separator* (= the quasipoly seal); its character matrix is **singular at a bounded base**.
       This is the precise form of the anticipated "non-degeneracy obstruction": **the clean single-round Gauss/`Z_u(S)`
       inversion (3c as originally written) FAILS at a bounded base.**
    4. **★ THE CRACK: the *iterated* `χ(det G₂)` pivot-count (graph-invariant 2-WL using the seal's pair observable)
       DETERMINES the orbit at the bounded single-anchor μ=1 base — exactly (`12,30,56` = orbits), uniformly across
       `q∈{3,5,7}`, both types.** Full binary 2-WL agrees (`q=3`). So the wall is **true and crackable**, but the
       determination needs **iterating** the pair observable (2-WL fixpoint), not the single round.
    5. **Caveat (cap):** the determination genuinely needs the *pair* observable `χ(det G₂)` (graph-invariant) — a probe
       using singleton square-class succeeded but is INVALID (the cap: singleton square-class flips under `Q↦cQ`), and
       binary-adjacency-only is insufficient. So the crack is specifically the `χ(det G₂)` 2-WL count.

    **⟹ REDIRECTED 3c (the actionable result).** The target is **not** the single-round `Z_u(S)` inversion (proven
    singular at bounded base) — it is the **iterated `χ(det G₂)` pivot-count** (the 2-WL fixpoint of the seal's pair
    observable): show *it* inverts to exact Gram at a bounded base. The obstruction is real for one round; **iteration
    recovers full rank**, uniformly in `q` (so NOT a large-`q`-only phenomenon — the `q≥256` fallback is not forced).
    Probe methodology (reproducible): `φ_S` orbit via Witt + scaling-class delimiter; refinement = colour refinement
    with the stated observable; `CellsAreOrbits ⟺ refinement-partition = φ_S-partition`. (Durable scripts:
    `GraphCanonizationProofs/wall_2wl.py`, `wall_pair.py`.)

  - **★★★ DEPTH PROBE — DONE (2026-06-29; the decisive go/no-go, GO). `wall_depth.py` / `wall_depth2.py`.** Measured the
    iteration *depth* of the `χ(det G₂)` pivot-count = the first round at which its partition **determines** the orbit
    (refines `φ_S`). **The depth is `O(1)` — uniformly bounded, NOT growing with `d`, base-depth `|S|`, type, or `q`:**
    determination at **round 1** (q=3) or **round 2** (q=5,7), fixpoint at round 2–3. Held across ambient `d ∈ {4,6}`,
    base depth `|S| ∈ {2,3,4,5}` with orbit count *growing* `12→36→108→324`, both `VO^±`, `q ∈ {3,5,7}` (full binary
    2-WL agreed at d=4 q=3, det@2). Notably deeper bases determine *faster* (q=5: `|S|=2` det@2 → `|S|=3` det@1), so
    depth does **not** grow with base depth. **⟹ The wall is genuinely crackable for the family; the frontier / Route-C
    fallback is NOT forced, and the large-`q` fallback is not needed (uniform in `q`).** Scope/caveat: pure-Python memory
    capped the sweep at `d ≤ 6` (geom precompute is `O(n²)`); `d=8` and more base-types are the residual uniformity
    check, but the `d=4→6` × growing-`|S|` evidence is strong. **NEXT = the Lean 3c proper**: prove `WallKernelFor Obs`
    for `Obs` = the iterated `χ(det G₂)` 2-WL, exploiting the `O(1)` iteration depth (the inversion is a *bounded* number
    of character-sum rounds, not an unbounded fixpoint).
- **Parallel — Witt build (now the higher priority; fully scoped in §7).** The shared enabler for Increments 2–3's
  easy halves and the depth-1 sphere. Mathlib has the primitives but no Witt theory; the staged plan + difficulty +
  recommendation are in **§7**. The cheap first slice (W0+W1) discharges `WittConeTransitive` and makes the depth-1
  base case unconditional.

**Definition of done for Route B** (three pieces, not one):
1. **node-count bridge** (Increment 0) — keyed on `SelectedCellIsOrbit` (weaker than full `CellsAreOrbits`, **NOT**
   `SeparatesAtBoundedBase`). **Provable core ✅ DONE** (`ScratchNodeCountBridge.lean`): `certifiedSinglePath_of_disposition`
   gives bounded nodes (`≤ n`) + every consumed cell one orbit. **Residual = the `canonAdj`-transport seam** (rep-choice
   invariance of the leaf canonical; meta-consumed).
2. **the math** — `CellsAreOrbits` (`modulo {Witt}`) discharging the disposition for the affine-polar residue (via
   `selectedCellIsOrbit_of_cellsAreOrbits` + `twinsRealizedByResidualAut_iff_cellsAreOrbits`). [OPEN — Increment 3 + Witt.]
3. **the capstone** — a poly-seal keyed on `SinglePathDisposition`, the poly twin of `reachesRigidOrCameron_affinePolar`
   (assembled from 1's `CertifiedSinglePath` + the transport seam + 2's math).

NB final "poly time" remains a meta-argument over (3); (1) supplies the structural single-path claim the meta-argument
needs and the quasipoly seal lacks. **Build order: (1) first** — it validates the whole premise and is independent of
the wall.

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
- **Why Route B anyway.** `poly ⟸ B` is independently valuable; the scaffold is real; and a refinement-only poly proof
  (now that the depth probe shows B is crackable at `O(1)` depth) is cleaner than Route C's construction. Chosen with
  eyes open that Route C is the fallback if 3c stalls.

---

## 9. Pointers

- **★ FRESH READER — PICK UP HERE (2026-06-29 handoff).** Read this STATUS + §1 (esp. the **KNOWN GAP** on `poly ⟸ B`)
  + **§6 Increment 3** (the wall: the plan table, the crackability probe, and the **DEPTH PROBE = GO**). State of play:
  the whole structural scaffold is **built and axiom-clean** — the node-count bridge (Increment 0), the transport seam,
  and the wall isolation (3a, `WallKernel`/`WallKernelFor`). The two probes (`GraphCanonizationProofs/wall_*.py`)
  established the wall is **true, crackable, and `O(1)`-depth uniformly** — so it is the route's *live target*, not a
  frontier. **THE LIVE TASK = Lean 3c proper:** prove `WallKernelFor Obs` (`ScratchWallKernel`) for `Obs` = the iterated
  `χ(det G₂)` 2-WL, as a **bounded-depth (1–2 round) character inversion** — reuse `pairCharSum_factor_gen` /
  `gaussSum_sq_ne_zero` / the `χ(det G₂)↔Z_u` bridge. Secondary: 3a-equivariance + 3b (count-observable bridge to
  `ZProfileSeparates`). Loose ends (any time): `IsotropicPairing` (finishes W1), the `canonForm` seam lift (not
  Route-B-specific). All five Scratch modules compile (`lake env lean`), axiom-clean, NOT in `build.sh`; oleans built so
  imports check directly. **Verify before building on it:** `bash scripts/build.sh` (the seal/in-build infra) +
  `lake env lean ChainDescent/ScratchWallKernel.lean` (the live module).
- **Built modules** (all axiom-clean, NOT in `build.sh`; all decls described in `PublicTheoremIndex.md`):
  `GraphCanonizationProofs/ChainDescent/ScratchSimilitudeCap.lean` (the cap),
  `…/ScratchOrbitBaseCase.lean` (base case + delimiter + free prefix),
  `…/ScratchWittCone.lean` (Witt W0+W1),
  `…/ScratchNodeCountBridge.lean` (node-count bridge + transport seam),
  `…/ScratchWallKernel.lean` (**the wall — `WallKernel`/`WallKernelFor`, the live 3c target**).
- **Probe scripts (empirical, reproducible — durable in the repo, `python3 GraphCanonizationProofs/wall_*.py`):**
  `wall_pair.py` / `wall_2wl.py` (the crack: iterated `χ(det G₂)` determines the orbit, 1-WL does not),
  `wall_depth.py` / `wall_depth2.py` (the depth-probe = GO, `O(1)` determination depth uniformly). Methodology: compare
  the refinement partition to the true `Stab(S)`-orbit (`φ_S` via Witt + the scaling-class delimiter for
  totally-isotropic span); `CellsAreOrbits ⟺ refinement-partition = φ_S-partition`. (Pure Python, no deps; `d≤6`.)
- **Existing machinery to reuse:** `PairForm` (`pairForm`, `detG2_eq_pairForm`), `PerAnchorBound`
  (`c0_le_threequarters`), `AffinePolarSeal` (`exists_pow_matching_block`, `reachesRigidOrCameron_affinePolar`),
  `ProfileReduction` (`ZProfileSeparates`, `jointIsoCount`), `Cascade` (`twinsRealizedByResidualAut_iff_cellsAreOrbits`,
  `CellsAreOrbits`).
- **Viability analysis + the route fork:** memory `project_formsgraph_wldim_viability_2026-06-28`.
- **The seal / quasipoly build:** `chain-descent-formsgraph-wldim-plan.md` (STATUS + §1).
- **Route C / cameron context:** `chain-descent-formsgraph-wldim-plan.md` §11.10–§11.14; `chain-descent-ir-blindspot-solver.md`.
- **Literature (WL-dim open both ways):** memory `reference_srg_wl_literature_2026-06-17`.
