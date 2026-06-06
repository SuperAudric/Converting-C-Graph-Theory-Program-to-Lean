# Chain descent — Part A: the stabilizer-chain / Schreier–Sims object (planning & staging)

> **STATUS (2026-06-05): the abstract layer (Stages A1–A3, A3.5, A2-complete) is LANDED, and the coverage
> discharge is now GENERAL (non-abelian) + localisation-scoped; within Part A only the concrete BSGS (A4)
> remains, and the forward thread has moved downstream to the Exhaustive-Obstruction Lemma (the "or Cameron"
> half of the goal — see [exhaustive-obstruction](./chain-descent-exhaustive-obstruction.md), Approach 3;
> its scheme-leg primitivity bridge — combinatorial `IsPrimitive`, the imprimitive ⟹ refinement-visible
> bridge, and the group-side `isPreprimitive_iff_isPrimitive` — has since landed in `Scheme.lean §11`).**
> Build plan + context dump for a permutation-group **stabilizer chain** (Schreier–Sims) in Lean —
> "tractable-buildout Part A".
> **Done (axiom-clean, full build green, `Cascade.lean` "Part A"):** the residual group `Aut_S^P` as a
> Mathlib `Subgroup` (`StabilizerAt`); the cross-branch harvest **soundness** seam (fold-in ⊆ true residual,
> orbit-prune sound); the rigid verdict (trivial ⟺ base); the per-level orbit–stabilizer order recursion;
> the full `order = ∏ basic-orbit sizes` over a base sequence (A3.5 — the abstract `Order = ∏ OrbitSize` of
> `PermutationGroup.cs`); **and (A2-complete) the harvest *completeness* seam** — `StabilizerAt = closure of
> harvested generators` under a coverage witness, so the folded chain reproduces both the residual **group**
> and its **order**. See §7 for the landed theorem names. **Remaining:**
> - **A4 — the concrete computable BSGS** mirroring the C# (`Level`/transversal/sift). Validation breadth;
>   needed only for the *computable* object, not the abstract verdict.
> - **The coverage witness for multi-step CFI** (in progress — CFI instance of A2-complete). A2-complete
>   reduces completeness to `CoversOrbits` over the path-fixing gauge generators. **CFI-cov.1 + CFI-cov.2
>   landed** (2026-06-04): the residual-membership bridge (`cfiFlipAut_residualAut` etc.; forward coverage),
>   the cycle-space `Z₂^β` object (`CycleSpace`, `xorF`, `flipSet_xorF`, closure), and the odd-degree base
>   sequence (`cfi_exists_base_seq`). **CFI-cov.3 stage 1 landed** (2026-06-04): the gauge-flip group
>   homomorphism `Z₂^β → Aut` (`cfiFlip_xorF`, `cfiFlipAut_xorF`, `cfiFlipAut_one`).
> - **DE-CLASSED COVERAGE LANDED** (2026-06-04, axiom-clean): `coversOrbits_of_residualInvolutive` /
>   `closure_eq_stabilizerAt_of_residualInvolutive` (+ `residualInvolutive_mono`) discharge `CoversOrbits`
>   for the **whole elementary-abelian-(`Z₂^d`)-residual class in one theorem** — the cross-branch analogue
>   of `theorem_2_HOR_of_pPolynomial`. **This supersedes the per-class `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` structure
>   theorem as the CFI route:** the abstract coverage holds once the residual is exponent-2 and `gens`
>   contains the harvested involutions, *without* identifying them as the literal cycle-space flips (no
>   `Φ(σ)` lift).
> - **GENERAL (NON-ABELIAN) COVERAGE LANDED** (2026-06-04, axiom-clean): `coversOrbits_of_realizers` /
>   `coversOrbits_of_visibleRealizers` / `closure_eq_stabilizerAt_of_realizers` discharge `CoversOrbits` (and
>   `closure (gensAt …) = StabilizerAt`) from **per-level path-fixing realizers with NO group-structure
>   hypothesis** — abelian *or* non-abelian (schemes, Cameron sections). This is the honest "covers everything,
>   no class ladder" coverage core: `coversOrbits_of_residualInvolutive` is now its exponent-2 **corollary**
>   (`orbitPartition_swap_of_involutive` supplies the realizer). The harvest-facing `coversOrbits_of_visibleRealizers`
>   keys the realizer hypothesis on the **refinement-visible cell relation** (polynomially computable) — the
>   shape the structural (scheme/recovery) harvest plugs into, since at a recoverable node cells *are* orbits.
> - **LOCALISATION SCOPED + first pieces LANDED** (2026-06-04, axiom-clean). The scheme consumer's content is
>   **localisation = the polynomiality layer, not a coverage-correctness gap**: a same-cell→orbit realizer
>   comes from `OrbitPartition` directly, so coverage correctness (`closure (gensAt …) = StabilizerAt`, order)
>   holds from `coversOrbits_of_realizers` *unconditionally* given the harvest collected realizers; recovery is
>   what makes the equivalent harvest target **refinement-computable**. Landed: `recoverableByDepth_pPolynomial`
>   (`CascadeOracle.lean` — the whole metric/DRG family exported to `RecoverableByDepth` at depth 1, generalizing
>   the rank-2-only `recoverableByDepth_scheme`); `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`
>   (`Cascade.lean` — at a recovered node the visible-cell-mate harvest ≡ the orbit-mate harvest, the localisation
>   core). **Honest boundary:** *per-level* recovery down the base sequence (`CellsAreOrbits` at each intermediate
>   level, not just depth 1) is **substrate-conditional** — the cascade property iterated; it is **not**
>   unconditionally true for all DRGs (the WL-dimension boundary), so it is the cascade-class discriminator
>   (`RecoverableByDepth` witnesses), not a closable theorem — the cross-branch analog of declassing §9's "B's core".
> - **GENERAL POLYNOMIALITY CAPSTONE LANDED** (2026-06-06, axiom-clean, `Cascade.lean` "Part A"): the
>   coverage→group→order chain packaged through the **refinement-computable (visible-cell) realizer** interface —
>   the honest harvest interface (the leaf-collision harvest works with `warmRefine` cells, not orbits).
>   `closure_eq_stabilizerAt_of_visibleRealizers` (group side, computable), **`crossBranchHarvest_reproduces_residual`**
>   (group **and** order, general `S` — the polynomiality-layer analogue of `exhaustiveObstruction_scheme`), and
>   `autP_reproduced_of_visibleRealizers` (the `S=∅` headline: the folded harvest generates *exactly* `Aut(G)^P` and
>   its order `= ∏ basic-orbit sizes`, no group-structure hypothesis). The **single substrate-conditional input is
>   recovery** (makes the visible-realizer hypothesis satisfiable, via `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`);
>   the chain is unconditional. Witnesses populating recovery: `recoverableByDepth_pPolynomial` (metric/DRG),
>   `recoverableByDepth_cfi` (CFI). The remaining content is *discharging* recovery on a class (the substrate-conditional
>   boundary) and the harvest-collection (firing), not the capstone.
> - **NO-FUSION layer LANDED + battery-validated** (2026-06-06, axiom-clean, `Cascade.lean` "Part A"): `NoFusion`
>   (the orbit-realizer coverage — the symmetry-only/defer-all-reals harvest reproduces every orbit, **no recovery
>   hypothesis**, distinct from the visible-realizer capstone), `reproducesResidual_of_noFusion` /
>   `autP_reproduced_of_noFusion` (`NoFusion` ⟹ `closure = Aut^P ∧ |·| = ∏ orbit-sizes` — largeness read off the
>   harvest, no Babai/no WL-dim), `noFusion_of_visibleRecovery` (recovery ⟹ no fusion). This is the leg-C
>   *largeness*-derivation layer (PP1/PP3, [fusion-battery-plan](./chain-descent-fusion-battery-plan.md);
>   exhaustive-obstruction §0.7.5), validated by the adversarial battery (`FusionBatteryExperiment.cs`, 17/17):
>   **no genuine fusion constructible** — "fusion" splits into separable (Tier-0-handled) vs non-decomposable
>   (= genuine Cameron, no third species); consumption is candidate-pinning/recovery, orthogonal to abelian-ness.
> - **CFI base-layer, colour-model RE-WIRING DONE** (2026-06-06, axiom-clean, `Cascade.lean` CFI-cov.4). **Scoping
>   finding:** `PSeparatesGadgets` (the prior "sole CFI obligation") is stated over `P`-relations but the descent's
>   CFI recovery runs on trivial `P` + colour individualization, so it is **vacuously false** at every `S` for
>   multi-gadget CFI (and vacuous at `S=∅`). The colour-model `CellSeparatesGadgets` (same `warmRefine` cell ⟹ same
>   gadget) is the dischargeable form. Landed: `gadgetPreserving_of_cellSeparates` (Lemma A colour, via
>   `warmRefine_invariant_of_isAut`), `cfi_residualInvolutive_cell` (capstone; Lemma B `cfiAut_gadgetFixing_mul_self`
>   reused verbatim), `cellSeparatesGadgets_of_discrete` (cascade bridge — `warmRefine` discreteness ⟹
>   `CellSeparatesGadgets`, the connection the `P`-form lacked), and `cfi_closure_eq_stabilizerAt_of_cellSeparates` /
>   `cfi_card_stabilizerAt_of_cellSeparates` (harvest completeness + order). These **supersede** the `pSeparates`
>   versions for the descent's actual mechanism.
> - **CFI base-graph lemma — PLANNED + Brick 1 LANDED** (2026-06-06, axiom-clean). Discharging
>   `CellSeparatesGadgets` at a *non-trivial* (gauge-remaining) `S` is **substrate-conditional on the base `H`**
>   (the gadget-level analogue of `RecoverableByDepth`); the bounded content is the implication **"1-WL identifies
>   `H` ⟹ 1-WL separates gadgets"** (statable since `h.H.adj : AdjMatrix h.m`). Three bricks: **(1) structural
>   foundation — LANDED:** `gadget_mem_neighbors_of_adj_cross` (a cross-gadget adjacency is a base-graph edge) +
>   `endpoint_crossGadget_gadget` (sharpened: an endpoint's cross-gadget neighbour lands in the bridge-target gadget
>   `w` exactly — pins the projection's multiplicity); **(2) refinement-projection induction:** CFI 1-WL refines the
>   gadget-pullback of `H` 1-WL; **(3) conclusion:** `Discrete (H-warmRefine) ⟹ CellSeparatesGadgets`.
>   `cellSeparatesGadgets_of_discrete` covers the (vacuous-harvest) full-discreteness base case.
>   **DESIGN SETTLED (2026-06-06) — `CellSeparatesGadgets` carried as a WITNESS (option 1 banked).** Brick 2 (the
>   refinement-projection induction) proved to be a *base-relative CFI cascade* (Step A subset-follows-endpoints +
>   Step B endpoint-separation via bridge + `H`-1-WL simulation, ~3–4 increments), whose **only payoff is a
>   non-vacuity demonstration** — the capstone + CFI re-wiring are already complete, and
>   `cellSeparatesGadgets_of_discrete` discharges the full-discreteness base case. Following the project's recovery
>   pattern (`RecoverableByDepth`/`recoverableByDepth_cfi`), base-identification is therefore a **substrate-conditional
>   witness** the harvest consumes, not a closed theorem. The structural bridge (Brick 1 `gadget_mem_neighbors_of_adj_cross`
>   + sharpening `endpoint_crossGadget_gadget`) is the landed well-definedness foundation; the full implication is
>   deferred to a future witness-discharge if a concrete non-vacuous instance is wanted.
> - **CFI WITNESS LANDED conditional on gauge-generation** (2026-06-04, axiom-clean): `gaugeSubgroup`
>   (the gauge group `Z₂^β` as a `Subgroup`), `closure_cfiGaugeGens_eq`, `cfiGauge_mul_self` (the gauge group
>   is exponent-2), and **`cfi_coversOrbits` / `cfi_closure_eq_stabilizerAt` / `cfi_card_stabilizerAt_eq_prod`**
>   (`|Aut(CFI)^P| = ∏ basic-orbit sizes`). All reduced to a **single** CFI hypothesis: **gauge-generation**
>   `StabilizerAt adj P ∅ ≤ Subgroup.closure (cfiGaugeGens h)` (every `P`-preserving automorphism is a product
>   of gauge flips — the *surjective half* of the classical structure theorem; the converse is free). The
>   `Φ(σ)` lift, the semidirect decomposition, and the per-level orbit-coverage clauses are **all gone**.
>   **Remaining (the sole CFI nut):** discharge **gauge-generation** for CFI. Firing content (C# canonizes
>   CFI(K₄–K₇)), not GI-hard. See §7.
>
> A fresh reader can still use this doc as the full context/name index (Mathlib + internal) for consuming
> A1–A3.5 / A2-complete or building A4.
>
> **Why now (the trigger).** The discretizing colour-match oracle was just **proven unable** to harvest a
> multi-step moved orbit: `lockstep_disc_imp_stab_trivial` (`CascadeOracle.lean §C.8`) shows its two
> completeness hypotheses are jointly satisfiable only when one rep already kills the residual. So the
> multi-step hidden-abelian case (CFI gauge twists, `tw ≥ 2`) **must** be harvested *cross-branch* — and
> the cross-branch harvest needs a group object to fold automorphisms into. That object is this doc.
> Companion: [declassing](./chain-descent-declassing.md) §6/§9 (the redirect), the memory note
> `project_discretizing_oracle_limit_2026-06-03.md`.

---

## 0. The two layers this builds

1. **The group object** — the path-fixing stabilizer `Aut_S^P` as a real Mathlib `Subgroup`, with its
   orbit structure, its **order** (`= ∏ basic-orbit sizes`), and a base/transversal (BSGS) decomposition.
2. **The cross-branch harvest seam** — *fold in* a verified automorphism (the a-posteriori "two branches
   reach the same leaf ⟹ the relabelling is an automorphism" harvest, strategy §4 step 6), and *consume*
   it (a folded generator that fixes the path prunes sibling branches). Both halves are now formalized:
   **soundness** (Stage A2: fold-in `⊆` true residual, prune sound) and **completeness** (Stage A2-complete:
   under a coverage witness the harvested generators *generate* the residual, `closure gens = StabilizerAt`).
   The remaining open piece is the coverage witness itself for multi-step CFI — the mechanism the
   conservation finding established as required (§7).

The project needs the *reasoning* ("the harvested generators generate the path-fixing stabilizer";
"residual trivial ⟺ rigid"), not a fast computable sift. So the abstract `Subgroup` layer was built first
(Stages A1–A3.5 — container + soundness + order; A2-complete — the harvest *completeness*, "harvested
generators **generate** the stabilizer", reduced to a coverage witness); the concrete computable BSGS data
structure mirroring the C# (Stage A4) is later/optional. The *reasoning* the project most needs is the
landed A2-complete, not anything in A4.

---

## 1. The formalization target — the C# object

`GraphCanonizationProject/PermutationGroup.cs` (297 lines) is the reference implementation; the Lean
object should be provably equivalent to it (Stage A4) and is the spec for the abstract layer.

- **`static class Perm`** (lines 13–73): a permutation is `int[] p` (`p[i]` = image of `i`). Ops:
  `Identity`, `Compose(p,q)` — **right operand first**: `Compose(p,q)[i] = p[q[i]]` (load-bearing
  convention; the Lean model uses `Equiv.Perm` whose `*` is also right-first, so they match), `Inverse`,
  `IsIdentity`, `IsPermutation`, `FromCycles`, `FirstMoved` (first non-fixed point, else `-1`).
- **`sealed class PermutationGroup`** (94–296): `int N`; `List<int[]> _generators`; lazy `List<Level>?
  _chain` (nulled on each `AddGenerator`, rebuilt by `EnsureChain`).
  - **`Level`** (103–110): one chain level — `int BasePoint`; `int[]?[] Transversal` indexed by orbit
    point (`Transversal[pt]` is a group element `u` with `u[BasePoint] = pt`, or `null`); `int OrbitSize`.
    This is the BSGS triple (base point, basic transversal, strong generators implicit in `_generators` +
    recursively-derived Schreier generators).
  - **Ops:** `AddGenerator` (123 — the fold-in entry point; validates, drops identities, invalidates
    chain), `Order` = `∏ level.OrbitSize` (136, the orbit-stabilizer product), `BasePoints` (150),
    `Contains` = sift/strip (161: at each level look up the rep for `cur[BasePoint]`; `null` ⟹ reject;
    else `cur := Inverse(rep) ∘ cur`; member iff final residue is identity), `Orbit(point)` BFS (177),
    **`BuildChain`** = recursive Schreier–Sims (209–274: pick first moved point as base; BFS the basic
    orbit building coset reps `u_img = g ∘ u_o`; form Schreier generators `sg = u_{g[o]}⁻¹ ∘ g ∘ u_o`,
    deduped via `PermComparer`; recurse; stop when residual gens are all identity).
- **Tests** (`GraphCanonizationProject.Tests/PermutationGroupTests.cs`): `Order` is the oracle. Corpus to
  mirror: trivial, single transposition (2), cyclic (= cycle length), **`S₃–S₇`** via `⟨(0 1),
  n-cycle⟩` = `n!`, **`D₄`** = 8, **`D18` = Aut(C18)** = 36, **`D9 ≀ Z2` = Aut(C9⊔C9)** = 648; plus orbit
  correctness, incremental-generator order growth, redundant-generator idempotence.

**Caveat:** this C# BSGS is the *unsifted* textbook variant (lines 89–93) — correct for **all** groups,
but the polynomial-construction sifting is deferred. A faithful Lean model proves **correctness** (order =
orbit product, membership = identity residue); the **poly-size** claim (T-A) stays a *citation* (Sims:
base ≤ n, SGS `O(n²)`), not a consequence of the data-structure proof. Do not conflate them.

---

## 2. The cross-branch harvest interface (the seam)

How automorphisms enter and leave the chain, from `GraphCanonizationProject/ChainDescent.cs`. The chain
is the public `PermutationGroup Automorphisms`. Two feed paths, both via `Automorphisms.AddGenerator`:

1. **A-posteriori leaf-collision harvest** (the canonical strategy §4 step 6). `HandleLeaf` (532–556):
   each discrete leaf yields a labelling `perm` and a permuted adjacency matrix, keyed by a 64-bit hash
   into `_seen`. On a hash hit, the relabelling `auto = Inverse(perm) ∘ firstPerm` is the candidate; it is
   **edge-verified** by `IsAutomorphism` (581–588) — a hash collision just fails harmlessly — and only
   then `AddGenerator(auto)`.
2. **A-priori cascade/linear harvest** `HarvestTwists` (359–379): explore the anchor rep, replay the
   iso-invariant deepening on each other rep, construct a candidate twist, edge-verify, fold in.

**Consumption — how the folded chain prunes.** `CoveredByPathFixingAut` (501–527): collect harvested
generators that fix every path vertex (`g[pt]==pt` for `pt ∈ _path`), BFS the orbit of explored reps
under just those, and skip `v` if it lands in that orbit. So a path-fixing folded automorphism prunes
redundant siblings — the "useful mid-run" property (strategy §6).

- Oracle seam: `ITransversalOracle.cs` `Classify(n, adj, targetCell, path, knownGroup)` is *handed the
  live `PermutationGroup`*; soundness contract "over-split sound, under-merge not".
- Output: `CanonGraphOrdererChainDescent.cs` `LastAutomorphisms` / `LastAutomorphismGroupOrder`;
  `FlagKind.Tier2Like` vs `IrBlindSpot` keyed on `result.ResidualGroup.IsTrivial` (≈ line 95).

---

## 3. Foundations that EXIST — Mathlib (reuse the mathematics)

Verdict: **Schreier–Sims / BSGS / base / SGS / sift are ABSENT** from Mathlib (must build). But every
*underlying* primitive is present. Paths are under `.lake/packages/mathlib/Mathlib/`.

### Group action (the core foundation) — `GroupTheory/GroupAction/`
- `MulAction.orbit (a : α) : Set α`, `MulAction.stabilizer G a : Subgroup G` — `Defs.lean`.
- **Orbit–stabilizer, constructive:** `MulAction.orbitProdStabilizerEquivGroup b : orbit α b × stabilizer
  α b ≃ α`, and `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` — `Quotient.lean`. **This is what
  makes "order = ∏ orbit sizes" nearly free** (the Stage A3 deliverable).
- `MulAction.orbitRel`, `MulAction.fixedPoints`, `MulAction.fixedBy`.
- **`fixingSubgroup M s : Subgroup M`** with `mem_fixingSubgroup_iff : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s,
  m • y = y` — `GroupAction/FixingSubgroup.lean:113/117`. **This is exactly the project's `FixesPointwise`
  as a Mathlib `Subgroup`** — the pointwise stabilizer is *not* new code. (Mathlib uses `Set α`; the
  project uses `Finset`, so a `↑s` coercion.)

### Transversals & Schreier's lemma — `GroupTheory/`
- `Subgroup.LeftTransversal H` / `RightTransversal H` (abbrevs of `{S // IsComplement …}`), `IsComplement
  S T`, `IsComplement.toLeftFun/toRightFun`, `IsComplement.leftQuotientEquiv : (G ⧸ H) ≃ leftTransversal`,
  `exists_isComplement_left/right` — `Complement.lean`.
- **Schreier's lemma:** `Subgroup.closure_mul_image_eq` (`H` is generated by `(R*S).image (g ↦ g *
  (hR.toRightFun g)⁻¹)`), `closure_mul_image_eq_top'`, `Subgroup.fg_of_index_ne_zero`,
  `rank_le_index_mul_rank` — `Schreier.lean`. This is the generators-from-transversal step the
  per-level Schreier-generator construction needs.

### Index / order / Lagrange — `GroupTheory/Index.lean`
- `Subgroup.index = Nat.card (G ⧸ H)`, `Subgroup.card_mul_index : Nat.card H * H.index = Nat.card G`,
  `Subgroup.index_dvd_card`, `Subgroup.relIndex`, **`MulAction.index_stabilizer : (stabilizer G a).index
  = Nat.card (orbit G a)`** (orbit = index of stabilizer — the per-level factor).

### Equiv.Perm / closure — `GroupTheory/Perm/`, `Algebra/Group/Subgroup/Lattice.lean`
- `Equiv.Perm.support`, `Equiv.Perm.Disjoint`, `Subgroup.closure` (subgroup generated by a set), `Fintype
  (Equiv.Perm (Fin n))` (computability), perm order. `Subgroup.subgroupOf` (for chain quotients).

---

## 4. Foundations that EXIST — internal (and the consolidation map)

All paths under `GraphCanonizationProofs/ChainDescent/`. These are what Part A builds on or **consolidates**.

### The group, already (Group.lean)
- `AutGroup adj : Subgroup (Equiv.Perm (Fin n))` (carrier `IsAut · adj`) — `:55`; `mem_autGroup` `:69`.
  **= the ambient `G` (modulo adding the `P`-preservation conjunct, see Stage A1).**
- `autGroup_smul` `:97`, `mem_orbit_autGroup_iff` `:103`, **`mem_orbit_autGroup_iff_orbitPartition` `:116`**
  (bridges `MulAction.orbit (AutGroup adj)` to `OrbitPartition adj P ∅` — the **root** orbit bridge; Part A
  generalizes it per-level via `StabilizerAt`).
- `LayerChain adj` (descending **normal** chain `AutGroup ⊵ … ⊵ ⊥`, fields `len/layer/head_eq/last_eq/
  descending/normal`) `:139`; `LayerChain.trivial` `:157`. **The stabilizer chain is the canonical
  *specialization* (base-ordered, with transversals); this may be refactored/subsumed.**
- Quotient-graph machinery: `orbitSetoid` `:200`, `OrbitQuotient` `:206`, `orbitMk` `:210`,
  `orbitMk_eq_iff` `:215`, `cell_iff_orbitMk_eq` `:233` (cell = quotient vertex under `CellsAreOrbits`),
  `quotientAdj` `:258`, `orbitPartition_empty_iff_orbitRel` `:293`, **`orbitQuotientEquivAutGroup` `:307`**
  (`OrbitQuotient … ∅ ≃ V/Aut(G)` — the root quotient is literally `V/Aut(G)`).

### Automorphism + stabilizer predicates (ChainDescent.lean / Cascade.lean)
- `IsAut` `ChainDescent.lean:2939`; `IsAut.refl/.trans/.symm` `:2947/:2950/:2957` (the `AutGroup` closure
  proofs); `labelledAdj_eq_of_isAut` `:2980`, `isAut_of_labelledAdj_eq` `:2992`.
- `FixesPointwise π S := ∀ v ∈ S, π v = v` `:3450`; `FixesPointwise.complement` `:3461`;
  `individualizedColouring_invariant` `:3472`. **= `fixingSubgroup` membership (Mathlib).**
- **`ResidualAut adj P S π := IsAut π adj ∧ (P-preserving) ∧ FixesPointwise π S` `Cascade.lean:452`** — the
  path-fixing stabilizer **as a predicate**; `orbitPartition_iff_residualAut` `:464`; **`ResidualAut.mul`
  `:489`** (closure). `ResidualAbelian` `:459`, `ResidualInvolutive` `:504`, `residualAbelian_of_involutive`
  `:509`, `orbitPartition_swap_of_involutive` `:522`, `residualAut_eq_one_of_isBase` `:548`,
  `residualAbelian_of_isBase` `:556`, `residualAbelian_mono` `:564`. **THE primary consolidation target:
  package as `StabilizerAt … : Subgroup`; these lemmas become subgroup properties.**

### Orbit relation + support backbone
- `OrbitPartition adj P S v w := ∃ π, IsAut π adj ∧ P-pres ∧ FixesPointwise π S ∧ π v = w`
  `ChainDescent.lean:3667`; `.refl/.symm/.trans` `:3679/:3683/:3700`; `subset_warmRefine` `:3722` (orbits
  refine 1-WL cells). **= per-level `MulAction.orbit` of `StabilizerAt`.**
- `OrbitPartition.mono` `CascadeOracle.lean:64` (fixing more shrinks orbits — **= stabilizer containment
  `StabilizerAt S' ≤ StabilizerAt S` for `S ⊆ S'`**); `real_stays_real` `:75`.
- **`orbitPartition_of_support_disjoint` `CascadeOracle.lean:118`** (`Disjoint S π.support` + `π v = w` ⟹
  `OrbitPartition … S v w`), **`exists_orbit_witness_of_aut` `:133`** (a symmetry of support `s` keeps its
  orbit pair alive to depth `n − s`). **These are the transversal-relocation / availability-depth facts
  the chain makes rigorous (§C.0.1 caveat).**

### Base + residual support (Cascade.lean)
- `IsBase adj P T := ∀ v w, OrbitPartition adj P T v w → v = w` `:57` (**= `StabilizerAt T = ⊥`**);
  `discrete_of_cellsAreOrbits_base` `:74`; `isBase_of_no_moved` `:944`; `exists_isBase_saturated` `:974`
  (reach a base in `≤ n − |S₀|` rounds); **`exists_isBase_saturated_support` `:1040`** (tight: `≤
  |movedSet|` rounds — **= base length ≤ support size**).
- `MovedAt` `:935`, `movedSet adj P S₀` `:1011` (the residual support), `forcedNode := S₀ ∪ movedSet`
  `:1080`; `MovedAt.anti` `:1002`, **`movedSet_image` `:1139`** / `forcedNode_image` `:1158` (equivariance),
  `forcedNode_isBase` `:1089`, `recoverableAt_base_iff_discrete` `:1195`. **= base-point selection (first
  moved point) + the equivariance a canonical base needs.**
- `CellsAreOrbits` `CascadeOracle.lean:268`, `OrbitRecoverableAt` `:221`,
  `mem_movedSet_iff_nonsingleton_cell_of_recoverable` `Cascade.lean:1226` (residual support =
  refinement-visible non-singleton cells, where recovery holds).

### The trigger (do not re-litigate)
- `lockstep_disc_imp_stab_trivial` `CascadeOracle.lean:2056` — the discretizing oracle cannot harvest a
  multi-step moved orbit; this is *why* Part A is required.

---

## 5. What is ABSENT (the actual build)

Originally absent in both Mathlib and the project. **Now built by A1–A3.5 + A2-complete** (Cascade.lean): the
**cross-branch fold-in/consume seam, both directions** — *soundness* (`closure_le_stabilizerAt`,
`covered_sound`) and *completeness* (A2-complete: `gensAt`, `stabilizerAt_le_closure_gensAt_step`,
`CoversOrbits`, `stabilizerAt_eq_closure_gensAt_of_coversOrbits`, `closure_eq_stabilizerAt_empty_of_coversOrbits`,
`card_closure_gensAt_eq_prod_of_coversOrbits` — `closure (gensAt … S) = StabilizerAt S` under a path-fixing
coverage witness); the **per-level group-order recursion** (`card_stabilizerAt_eq_orbit_mul`);
the **full order product over a base sequence** (A3.5 — `orbitSizeProd`, `card_stabilizerAt_eq_prod`,
`card_stabilizerAt_eq_prod_of_base`, `card_autP_eq_prod_of_base`); and the **stabilizer object + base
predicate** (`StabilizerAt`, `stabilizerAt_eq_bot_iff_isBase`).
**Still absent — the coverage witness (content, not abstraction):** that `CoversOrbits` *holds* for
multi-step CFI bounded-`tw` (the leaf-collision harvest collected a strong generating set) — the honest
analog of the depth witness; not GI-hard, but the remaining firing content.
**Still absent (Stage A4, computable only):** an explicit **ordered base sequence** as data (note `IsBase`
is a *predicate on a set*; A3.5 / A2-complete take the base sequence as a `List` argument but construct none),
**Schreier generators** as a construction, a **sift/strip/membership** procedure, and the **concrete
computable** `Level`/transversal structure mirroring `PermutationGroup.cs`.

---

## 6. What Part A solves / trivializes / consolidates

- **Solves:** the **rigid-residual verdict** (`card_stabilizerAt_eq_one_iff_isBase`); **`Aut(G)` order as a
  byproduct** of canonization (A3.5 `card_autP_eq_prod_of_base`, `= ∏ basic-orbit sizes` — a theorem, not a
  citation); **§C.0.1 transversal relocation** made rigorous; and **both halves of the cross-branch
  multi-step harvest** — soundness (A2) *and* completeness (A2-complete: the folded chain reproduces the
  residual group and its order, given a coverage witness). The discretizing oracle provably can't harvest a
  multi-step moved orbit (`lockstep_disc_imp_stab_trivial`); the cross-branch harvest that replaces it is now
  fully grounded **modulo the coverage witness** for multi-step CFI (the remaining firing content, §7).
- **Trivializes:** the **residual-group-order diagnostic** — `order = ∏ orbit sizes` is now a **Lean
  theorem** (A3.5 `card_autP_eq_prod_of_base`, built on Mathlib's orbit–stabilizer
  `card_mul_index` / `index_stabilizer`), not just citation-reachable; the rigid verdict
  (`card_stabilizerAt_eq_one_iff_isBase`) makes the Tier2Like-vs-IRblindspot flag split a Lean statement.
  **T-A/T-B** become Lean-reachable (orbit-stabilizer product) rather than pure citations — *except* the
  poly-size bound, which stays Sims's citation (see §1 caveat).
- **Consolidates:** the scattered predicate-level `ResidualAut` / `OrbitPartition` / support reasoning into
  one `Subgroup` object; likely subsumes `LayerChain`'s descent role; turns the §C.0.1 caveat into theorem.

---

## 7. The staged plan

Abstract-`Subgroup`-first (the reasoning the project needs); concrete BSGS later.

### Stage A1 — `StabilizerAt` as a `Subgroup` (the consolidation) — **LANDED 2026-06-03, axiom-clean**
Built in `Cascade.lean` "Part A (Stage A1)": `StabilizerAt adj P S : Subgroup (Equiv.Perm (Fin n))`
(carrier `ResidualAut`; `mem_stabilizerAt`, `stabilizerAt_smul`), `mem_stabilizerAt_empty` (root = ambient
`P`-preserving group — `AutGroupP` folded in, not a separate def), `stabilizerAt_mono`,
`stabilizerAt_eq_bot_iff_isBase`, `mem_orbit_stabilizerAt_iff` (per-node orbit bridge). **Shape decision:**
the carrier-`ResidualAut` form was used (robust, self-contained), *not* the `⊓ fixingSubgroup` form — the
`MulAction.orbit` bridge is still proved, so the Mathlib hook is present without the `⊓` plumbing. Original
plan below.
- Define `AutGroupP adj P : Subgroup (Equiv.Perm (Fin n))` = automorphisms preserving **both** `adj` and
  `P` (carrier `IsAut π adj ∧ ∀ x u, P (π x) (π u) = P x u`; closure mirrors `AutGroup` + the `P` clause).
  (`AutGroup` `:55` is the `P = ⊥`/no-`P` case; consider generalizing or keeping both.)
- Define `StabilizerAt adj P S := AutGroupP adj P ⊓ fixingSubgroup _ (↑S)` — carrier provably
  `ResidualAut adj P S` (via `mem_fixingSubgroup_iff` + `mem_inf`). Deliverable: `mem_stabilizerAt_iff :
  π ∈ StabilizerAt adj P S ↔ ResidualAut adj P S π`.
- Port the `ResidualAut` lemmas to subgroup form: monotonicity `S ⊆ S' → StabilizerAt adj P S' ≤
  StabilizerAt adj P S` (from `OrbitPartition.mono` / `FixesPointwise` monotonicity); `StabilizerAt adj P
  S = ⊥ ↔ IsBase adj P S` (from `residualAut_eq_one_of_isBase` `:548`); re-express `ResidualAbelian` /
  `ResidualInvolutive` as `IsCommutative` / exponent-2 of the subgroup.
- Bridge orbits: `MulAction.orbit (StabilizerAt adj P S) v` relates to `OrbitPartition adj P S v ·`
  (generalize `mem_orbit_autGroup_iff_orbitPartition` `:116` off the root).
- *Bar:* builds, axiom-clean, no behavioural change — pure consolidation that re-exports existing lemmas
  through the new object. **Minimal first deliverable; unblocks A2/A3.**

### Stage A2 — the harvest seam (soundness) — **LANDED 2026-06-03, axiom-clean**
Built in `Cascade.lean` "Part A (Stage A2)": `residualAut_mem_stabilizerAt` (fold-in entry),
`closure_le_stabilizerAt` (the harvested `Subgroup.closure` of verified gens stays inside the true
residual — the over-split-sound contract), `orbit_pathFixing_sound` (orbit under any `H ≤ StabilizerAt S`
⟹ `OrbitPartition`), and the capstone `covered_sound` (`CoveredByPathFixingAut` soundness). Original plan
below.
- A verified automorphism (`IsAut` + `P`-preservation, i.e. an edge-checked relabelling) is in `AutGroupP`;
  if it fixes the path it is in `StabilizerAt adj P path`. Formalize the **fold-in**: a generating
  `Finset` of such, `Subgroup.closure gens ≤ AutGroupP` (and `≤ StabilizerAt path` when all fix the path).
- Formalize the **consumption** (`CoveredByPathFixingAut`): the subgroup generated by path-fixing
  harvested generators acts on explored reps; landing in one orbit certifies the prune (soundness: the
  branches are `Aut`-equivalent — via `OrbitPartition`/`labelledAdj_eq_of_isAut`).
- *Bar:* the cross-branch harvest's soundness is a theorem; this is the conservation-finding's required
  mechanism, now grounded.

### Stage A3 — order & the rigid/Cameron verdict — **LANDED 2026-06-03, axiom-clean**
Built in `Cascade.lean` "Part A (Stage A3)": `card_stabilizerAt_pos` (finite), **`card_stabilizerAt_eq_one_iff_isBase`**
(the rigid verdict — residual trivial ⟺ base; its negation is the non-rigid/Tier-2-like side), and the order
recursion `subgroupOf_insert_eq_stabilizer` → `card_stabilizer_eq` → **`card_stabilizerAt_eq_orbit_mul`**
(`|Aut_S^P| = |orbit b| · |Aut_{insert b S}^P|`, the inductive step of `order = ∏ orbit sizes`, via
`Subgroup.card_mul_index` + `MulAction.index_stabilizer`). Required added imports `Mathlib.GroupTheory.Index`
+ `Mathlib.Algebra.Group.Subgroup.Finite`. The full product over a base sequence is **A3.5** (below), not
A4 — it is abstract. Original plan below.
- `Nat.card (StabilizerAt adj P S)` via the chain `= ∏ basic-orbit sizes` (Mathlib orbit–stabilizer over
  the base). `IsBase ⟺ StabilizerAt = ⊥ ⟺ Nat.card = 1 ⟺ rigid`. Express the flag diagnostic
  (non-trivial residual ⟹ Tier-2/Cameron; trivial ⟹ IR blind spot) as a Lean statement.

### Stage A3.5 — the full order product over a base sequence — **LANDED 2026-06-03, axiom-clean**
Built in `Cascade.lean` "Part A (Stage A3.5)". Telescopes `card_stabilizerAt_eq_orbit_mul` over an ordered
base sequence — pure induction, **no computable BSGS**, so separated out of A4:
- `orbitSizeProd adj P bs S` (noncomputable): the basic-orbit-size product along `bs` from `S`.
- `card_stabilizerAt_eq_prod`: the telescoping identity `|Aut_S^P| = orbitSizeProd bs S · |Aut_(foldl)^P|`
  for *any* sequence (induction on `bs` over `card_stabilizerAt_eq_orbit_mul`).
- `card_stabilizerAt_eq_prod_of_base`: at a base the trailing factor is 1, so `|Aut_S^P| = ∏ orbit sizes`.
- `card_autP_eq_prod_of_base`: the `S = ∅` headline — `|Aut(G)^P| = ∏ basic-orbit sizes`, the group order
  as a byproduct of canonization. The abstract `Order = ∏ level.OrbitSize` of `PermutationGroup.cs`.
- *Open within A3.5:* A3.5 takes the base sequence as a `List` argument; constructing a *canonical* one
  (and an existence corollary from `exists_isBase_saturated`) is small follow-on, lumpable with A4's
  ordered-base data.

### Stage A2-complete — the cross-branch harvest *completeness* seam — **LANDED 2026-06-04, axiom-clean**
A2 proved harvest **soundness** (`closure_le_stabilizerAt`: the folded chain stays `⊆ StabilizerAt`). The
**completeness dual** — that the harvested generators *generate* the residual — was missing from the original
A1–A4 staging, and is exactly what the conservation finding (`lockstep_disc_imp_stab_trivial`) redirected the
project to.

> **Design note — the witness must be path-fixing (non-circularity).** A first cut required the realizer to be
> *any* element of `closure gens` fixing the path. That is **circular**: since the residual shrinks down the
> base (`StabilizerAt S ≤ StabilizerAt ∅`), `closure gens = StabilizerAt ∅` already realizes every deeper orbit,
> so the "witness" is equivalent to the conclusion. The genuine reduction is the classical **strong generating
> set** condition: the realizer at level `S` must come from the *path-fixing* generators
> `gensAt adj P gens S := {g ∈ gens | g ∈ StabilizerAt adj P S}`, whose closure can be a *proper* subgroup of
> `StabilizerAt S` even when `gens` generate the top group. That is what the per-level path-fixing harvest
> (`CoveredByPathFixingAut`) actually supplies, and it is genuinely stronger than top-level generation.

Built in `Cascade.lean` "Part A (Stage A2-complete)":
- `gensAt adj P gens S` (path-fixing generators), with `gensAt_anti`, `closure_gensAt_le_stabilizerAt`,
  `closure_gensAt_anti` (the descent step), `gensAt_empty_eq` (`gensAt … ∅ = gens`).
- `stabilizerAt_le_closure_gensAt_step` — the **one-level completeness core** (strong-generation step): if the
  path-fixing closure at the next level contains `StabilizerAt (insert b S)` and the path-fixing closure at `S`
  realizes the full `Aut_S^P`-orbit of `b`, then it contains `StabilizerAt adj P S`. The dual of
  `closure_le_stabilizerAt`.
- `CoversOrbits adj P gens bs S` — the **coverage witness** along a base sequence: at each level the
  *path-fixing* closure `closure (gensAt … S)` realizes the current residual orbit; the honest analog of the
  within-cell depth witness, **class-conditional**. `coversOrbits_realize_of_mem` is the harvest interface
  (path-fixing *generators* realizing the orbit discharge a step).
- `stabilizerAt_le_closure_gensAt_of_coversOrbits` (the `≤` iteration), `stabilizerAt_eq_closure_gensAt_of_coversOrbits`
  (`closure (gensAt … S) = StabilizerAt S`, soundness intrinsic), `closure_eq_stabilizerAt_empty_of_coversOrbits`
  (root: `closure gens = StabilizerAt ∅`), and the capstone `card_closure_gensAt_eq_prod_of_coversOrbits` (with
  A3.5, the folded chain reproduces the residual **order** too).
- *Bar (met):* `closure (gensAt … S) = StabilizerAt S` under the coverage witness — the residual is *exactly*
  what the harness folds in. Closes the cross-branch harvest the way A2 closed its soundness half.

**CFI instance of A2-complete — discharging `CoversOrbits` for CFI (COMPLETE in the base-resolved regime).**
The cross-branch harvest for CFI folds in **gauge flips** (`cfiFlipAut`, the cycle-space `Z₂^β` generators
already in `CFI.lean`, with `isAut_cfiFlipAut` / `cfiFlipAut_preserves_P` / locality / `disjoint_support`).
What was scoped as a multi-week structure-theorem arc was **de-classed** to a fast discharge (see below).
Staging:
- **CFI-cov.1 — the residual-membership bridge — LANDED 2026-06-04, axiom-clean** (`Cascade.lean`):
  `cfiFlipAut_residualAut` (a path-fixing gauge flip is a `ResidualAut adj P S`), `cfiFlipAut_mem_stabilizerAt`,
  `cfiFlipAut_orbitPartition` (the **forward** coverage direction — a flip moves `v` within its orbit),
  `cfiGaugeGens` (the gauge generating set) + `cfiGaugeGens_residualAut_empty` (root soundness), and
  `cfiFlipAut_mem_gensAt` (path-fixing flip ∈ `gensAt (cfiGaugeGens h) S`). Connects the gauge-flip layer to
  the A2-complete `ResidualAut`/`StabilizerAt`/`gensAt`/`CoversOrbits` vocabulary.
- **CFI-cov.2 — cycle-space `Z₂^β` + base sequence — LANDED 2026-06-04, axiom-clean.** *Cycle space*
  (`CFI.lean`): `xorF` (the `Z₂` sum), `flipSet_xorF` (`flipSet (xorF F F') = flipSet F ∆ flipSet F'`),
  `even_xorF`, `CycleSpace` (symmetric + even flip-subgraphs = the `Z₂^β` index set), `cycleSpace_xorF`
  (closed under the sum), `cycleSpace_const_false` (zero). *Base sequence* (`Cascade.lean`):
  `isBase_of_discrete_warmRefine` (the general `Discrete ⟹ IsBase` bridge), `foldl_insert_empty_eq_toFinset`,
  and `cfi_exists_base_seq` (odd-degree CFI has an ordered base sequence, from the axiom-free cascade
  discreteness `theorem_1_HOR_cfi_oddDeg`).
- **CFI-cov.3 stage 1 — the gauge-flip group homomorphism `Z₂^β → Aut` — LANDED 2026-06-04, axiom-clean**
  (`CFI.lean`): `cfiFlip_xorF` (`cfiFlip (xorF F F') = cfiFlip F ∘ cfiFlip F'`), `cfiFlip_const_false`
  (zero ↦ id), and the lifted `cfiFlipAut_xorF` / `cfiFlipAut_one`. So `F ↦ cfiFlipAut F` is a group
  homomorphism from the cycle space into `Aut`, with image the gauge group — the `Z₂^β`-factor structure.
- **The de-classed coverage — the structure theorem SIDESTEPPED — LANDED 2026-06-04, axiom-clean**
  (`Cascade.lean`): `residualInvolutive_mono`, `coversOrbits_of_residualInvolutive`,
  `closure_eq_stabilizerAt_of_residualInvolutive`. Rather than prove the per-class `Aut(CFI(H)) ≅ Z₂^β ⋊
  Aut(H)` structure theorem (the `Φ(σ)` base-aut lift + decomposition), this discharges `CoversOrbits` from a
  **single abstract hypothesis** — the residual is exponent-2 (`ResidualInvolutive`, an elementary-abelian
  `Z₂^d`) — for the *generating set of all involutive residual automorphisms*. `orbitPartition_swap_of_involutive`
  realizes each orbit-mate by one path-fixing involution; the harvested involutions generate the residual
  **whatever their internal description**, so the literal-gauge-flip identification (and the `Φ` lift) is never
  needed. The cross-branch analogue of `theorem_2_HOR_of_pPolynomial`: one structural predicate covers the
  whole elementary-abelian-residual class (CFI's gauge regime, the twin/module regime, …). **This is the
  enabler of both CFI routes below.**

The two CFI routes are complementary — same goal (`closure {harvested} = StabilizerAt`, the order), different
hypothesis:

- **CFI-cov.3 — the literal-gauge route (gauge-generation), LANDED 2026-06-04, axiom-clean** (`Cascade.lean`):
  `gaugeSubgroup` (the gauge group `Z₂^β` as a `Subgroup` — `cfiGaugeGens` is closed under the group ops via
  `cfiFlipAut_xorF`/`_one`/`_involutive`), `closure_cfiGaugeGens_eq`, `cfiGauge_mul_self` (gauge is exponent-2);
  then `cfi_coversOrbits` / `cfi_closure_eq_stabilizerAt` (`closure cfiGaugeGens = StabilizerAt ∅`) /
  `cfi_card_stabilizerAt_eq_prod` — all conditional on **gauge-generation** `StabilizerAt adj P ∅ ≤ closure
  (cfiGaugeGens h)`. This identifies the residual with the *literal* cycle-space flips; its hypothesis is the
  *surjective half* of the structure theorem, and at `S = ∅` it is **false for non-rigid bases** (the `Aut(H)`
  factor survives), so this route is the **rigid-base / full-`Aut`-at-root framing**. The `gaugeSubgroup` +
  exponent-2 infrastructure is reusable.
- **CFI-cov.4 — the primary route (`PSeparatesGadgets` / `ResidualInvolutive`), COMPLETE 2026-06-04,
  axiom-clean** (`Cascade.lean`; plan
  [`chain-descent-cfi-gauge-discharge-plan.md`](./chain-descent-cfi-gauge-discharge-plan.md)). The faithful
  de-classed nut is **`ResidualInvolutive adj P S`** (the residual is exponent-2) — *strictly weaker* than
  gauge-generation (`g²=1`, not "`g` is a literal flip") — discharged in the **base-resolved regime** where the
  committed `P` distinguishes gadgets (`PSeparatesGadgets`, the decomposability premise; the `Aut(H)` factor
  killed by the committed individualization). **Lemma A** (`gadgetPreserving_of_pSeparates`): a residual aut
  fixes `S` pointwise and preserves `P`, so it preserves `P`-relations-to-`S` (`P (g x) s = P (g x)(g s) =
  P x s`), forcing gadget-preservation — the key move that *sidesteps* the structural "CFI auts preserve
  gadgets". **Lemma B** (`cfiAut_gadgetFixing_mul_self` + ~12 supporting lemmas: `exists_vertex_form`,
  `isEndpt`/`_equivariant`, `gadgetFixingAut_endpoint`/`_subset`/`_dir`, `mulSelf_endpoint`/`_subset`): a
  gadget-fixing CFI aut squares to `1` (type-preservation via the cross-gadget-neighbour distinguisher;
  endpoint involution via direction-preservation + 2-element-set injectivity; subset involution via
  determined-by-endpoint-adjacency). **Capstone** `cfi_residualInvolutive` (Lemma A + B). **Harvest wiring**:
  `isBase_mono`, `cfi_exists_base_seq_from` (base sequence from any `S`, via `allSeeds` + monotonicity),
  **`cfi_closure_eq_stabilizerAt_of_pSeparates`** (`closure {g | ResidualAut adj P S g ∧ g²=1} = StabilizerAt
  adj P S`) and **`cfi_card_stabilizerAt_of_pSeparates`** (`|Aut_S^P| = ∏ basic-orbit sizes`), at a **nonempty**
  base-resolved `S` (`PSeparatesGadgets` at `S=∅` is vacuously false → all gadgets equal). **This is the
  genuine route for real (non-rigid) CFI.** C# canonizes CFI(K₄–K₇); firing content, not GI-hard.

**The sole remaining CFI obligation** (after CFI-cov.4) is discharging **`PSeparatesGadgets`** for the
descent's actual `P` — that the committed individualization resolves the base layer. That is the **orthogonal
visible/cascade leg** (scheme / `PPolynomial` base-graph recovery), a separate thread, not part of the gauge
work.

### Stage A4 — concrete computable BSGS (defer)
- Model `Level` / ordered base sequence (as data) / `Transversal` / Schreier generators / `sift` as
  computable structures; prove `computes` against `StabilizerAt` and `order = ∏ OrbitSize` (the abstract
  product is already A3.5). Verification corpus = the C# tests (S₃–S₇, D₄, D18, D9≀Z2). Builds on Mathlib
  `LeftTransversal` + `closure_mul_image_eq` (Schreier). Needed only for the *computable* object; the
  abstract verdict (A3/A3.5) does not require it.

---

## 8. Decisions (1–2 resolved at A1; 3–4 open for A4)
1. **`StabilizerAt` shape — RESOLVED:** used the **carrier-`ResidualAut`** form (robust, reuses
   `ResidualAut.mul`), *not* `⊓ fixingSubgroup`. The `MulAction.orbit` bridge (`mem_orbit_stabilizerAt_iff`)
   is proved directly, so the Mathlib hook is present without the `⊓` plumbing.
2. **`AutGroup` vs `AutGroupP` — RESOLVED:** no separate `AutGroupP`; the ambient `P`-preserving group is
   `StabilizerAt adj P ∅` (`mem_stabilizerAt_empty`). `AutGroup` (Group.lean) is the no-`P` root and stays.
3. **`LayerChain` (Group.lean:139) — OPEN (A4):** whether to realize the stabilizer chain *as* a
   `LayerChain` instance or a parallel base-ordered structure. The A3 order recursion
   (`card_stabilizerAt_eq_orbit_mul`) is the per-level step either way.
4. **Computability scope — OPEN (A4):** how faithfully Stage A4 mirrors the unsifted C# variant vs. uses
   Mathlib's (noncomputable) transversal existence. The abstract layer (A1–A3.5 + A2-complete) is
   noncomputable and sufficient for the verdicts; A4 is the only stage needing decidable/`Fintype`
   computation.

## 9. Honest caveats
- The chain proves **correctness**, not the **poly bound** (T-A stays Sims's citation; the C# is unsifted).
- Part A does **not** touch T-C (per-level transversal *discovery* — the GI-hard core), the wall (leg C),
  or IR-blind-spot tractability. It is breadth (representation + the multi-step harvest mechanism), not
  the polynomial-bound needle. See the earlier impact analysis in the memory note.

---

## Appendix — quick name index

**Mathlib:** `MulAction.orbit`, `MulAction.stabilizer`, `MulAction.orbitProdStabilizerEquivGroup`,
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, `MulAction.index_stabilizer`, `fixingSubgroup` +
`mem_fixingSubgroup_iff` (`GroupAction/FixingSubgroup.lean`), `Subgroup.LeftTransversal`/`RightTransversal`
+ `IsComplement` (`Complement.lean`), `Subgroup.closure_mul_image_eq` (`Schreier.lean`), `Subgroup.index` +
`card_mul_index` (`Index.lean`), `Subgroup.closure`, `Equiv.Perm.support`.

**Internal (file:line):** `AutGroup` (Group.lean:55), `LayerChain` (Group.lean:139),
`orbitQuotientEquivAutGroup` (Group.lean:307), `mem_orbit_autGroup_iff_orbitPartition` (Group.lean:116),
`IsAut` (ChainDescent.lean:2939), `FixesPointwise` (ChainDescent.lean:3450), `OrbitPartition`
(ChainDescent.lean:3667), `OrbitPartition.mono` (CascadeOracle.lean:64), `orbitPartition_of_support_disjoint`
(CascadeOracle.lean:118), `exists_orbit_witness_of_aut` (CascadeOracle.lean:133), `ResidualAut`
(Cascade.lean:452), `ResidualAut.mul` (Cascade.lean:489), `residualAut_eq_one_of_isBase` (Cascade.lean:548),
`IsBase` (Cascade.lean:57), `exists_isBase_saturated_support` (Cascade.lean:1040), `movedSet`
(Cascade.lean:1011), `movedSet_image` (Cascade.lean:1139), `forcedNode` (Cascade.lean:1080),
`lockstep_disc_imp_stab_trivial` (CascadeOracle.lean:2056, the trigger).

**Part A landed (Cascade.lean "Part A"):** `StabilizerAt`, `mem_stabilizerAt_empty`, `stabilizerAt_mono`,
`stabilizerAt_eq_bot_iff_isBase`, `mem_orbit_stabilizerAt_iff` (A1); `residualAut_mem_stabilizerAt`,
`closure_le_stabilizerAt`, `orbit_pathFixing_sound`, `covered_sound` (A2 soundness); `card_stabilizerAt_pos`,
`card_stabilizerAt_eq_one_iff_isBase`, `subgroupOf_insert_eq_stabilizer`, `card_stabilizer_eq`,
`card_stabilizerAt_eq_orbit_mul` (A3); `orbitSizeProd`, `card_stabilizerAt_eq_prod`,
`card_stabilizerAt_eq_prod_of_base`, `card_autP_eq_prod_of_base` (A3.5); `gensAt`, `gensAt_anti`,
`closure_gensAt_le_stabilizerAt`, `closure_gensAt_anti`, `gensAt_empty_eq`, `stabilizerAt_le_closure_gensAt_step`,
`CoversOrbits`, `coversOrbits_realize_of_mem`, `coversOrbits_isBase_foldl`,
`stabilizerAt_le_closure_gensAt_of_coversOrbits`, `stabilizerAt_eq_closure_gensAt_of_coversOrbits`,
`closure_eq_stabilizerAt_empty_of_coversOrbits`, `card_closure_gensAt_eq_prod_of_coversOrbits` (A2-complete);
`residualInvolutive_mono`, `coversOrbits_of_realizers`, `coversOrbits_of_visibleRealizers`,
`closure_eq_stabilizerAt_of_realizers` (A2-complete de-classed, **general/non-abelian** — `CoversOrbits` +
`closure=StabilizerAt` from per-level path-fixing realizers, no group-structure hypothesis; the scheme/Cameron
coverage core), `coversOrbits_of_residualInvolutive`, `closure_eq_stabilizerAt_of_residualInvolutive`
(A2-complete de-classed exponent-2 corollary — `CoversOrbits` for the `Z₂^d`-residual class in one theorem);
`gaugeSubgroup`, `mem_gaugeSubgroup`, `closure_cfiGaugeGens_eq`, `cfiGauge_mul_self`, `cfi_coversOrbits`,
`cfi_closure_eq_stabilizerAt`, `cfi_card_stabilizerAt_eq_prod` (CFI-cov.3 — the CFI witness reduced to
gauge-generation `StabilizerAt ∅ ≤ closure cfiGaugeGens`); `gadgetOf`, `PSeparatesGadgets`,
`gadgetPreserving_of_pSeparates` (CFI-cov.4 Lemma A); `exists_vertex_form`, `endpointVertex_bool_inj`/`_inj`,
`subset_mem_iff_adj`, `isEndpt`(`_endpointVertex`/`_equivariant`), `not_isEndpt_subsetVertex`,
`gadgetFixingAut_endpoint`/`_subset`/`_dir`, `mulSelf_endpoint`/`_subset`, `cfiAut_gadgetFixing_mul_self`
(CFI-cov.4 Lemma B), `cfi_residualInvolutive` (CFI-cov.4 capstone A+B — `PSeparatesGadgets ⟹
ResidualInvolutive`); `isBase_mono`, `cfi_exists_base_seq_from`, `cfi_closure_eq_stabilizerAt_of_pSeparates`,
`cfi_card_stabilizerAt_of_pSeparates` (CFI-cov.4 harvest wiring — closure=StabilizerAt + order at a
base-resolved `S`; plan `chain-descent-cfi-gauge-discharge-plan.md`).

**C# target:** `GraphCanonizationProject/PermutationGroup.cs` (`Level` 103, `Order` 136, `Contains`/sift
161, `BuildChain` 209); harvest `ChainDescent.cs` (`HandleLeaf` 532, `HarvestTwists` 359,
`CoveredByPathFixingAut` 501); `ITransversalOracle.cs`; tests `PermutationGroupTests.cs`.
