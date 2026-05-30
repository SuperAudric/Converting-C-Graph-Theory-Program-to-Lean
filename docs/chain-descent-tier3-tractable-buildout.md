# Chain descent — Tier 3 tractable buildout (TEMPORARY)

> **STATUS: TEMPORARY working doc.** Scopes the *buildable* parts of Tier 3
> — the infrastructure prerequisites and the conditional ("tractable")
> theorems — as an actionable work plan. **Archive once the buildout
> lands** (move to `docs/archive/` and fold any surviving content into
> [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
> / [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)).

This doc deliberately **excludes the wall**. Tier 3's hard core —
sub-claim 2 (residual cascade) = existence of an admissible cascade-class
chain = the (O\*) self-detection lemma = the construction question — is
equivalent in strength to GI ∈ P and is *not* in scope here. Everything
below is either routine infrastructure or a result that is *conditional*
on the wall (it delivers polynomial canonization for graphs that **do**
decompose, and says nothing about whether every graph decomposes).

For the full framing see
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
(§4 sub-claims, §8 the wall) and
[`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
(Theorem 3a). For the proven base cases see
[`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md).

---

## 0. The shape of the buildout

Tier 3 wants `Aut(G) = N ⋊ Q` (N elementary-abelian — linear oracle;
Q cascade-class — Tier 1/2). The buildable pieces fall in two layers:

```
  Part A  — Infrastructure (group + quotient). Blocks even stating Part B.
  Part B  — Tractable theorems:
              B1  Tier 3a (cascade composition)        [needs A]
              B2  sub-claim 1 (abelian-stripping)      [mostly independent of A]
              B3  sub-claim 3 (oracle alternation)     [needs B2]
  OUT OF SCOPE — sub-claim 2 / (O*) (the wall).
```

The honest payoff: completing Part A + B gives **proven polynomial
canonization for any graph that admits a cascade-class normal chain**,
with the existence of such a chain left as the (excluded) open content.

### 0.1 Corrections to the existing Tier-3 docs (apply on fold-back)

Both Tier-3 docs predate recent work and were stale on two points:

- **The a-priori cascade oracle is BUILT** (C#, M1+M2, 2026-05-28; it
  eliminated CFI(K7) starvation, maxRecDepth ≈ tw(H)). The implicit-
  discovery argument's binding constraint is now the *Lean discharge of
  its contract*, not the implementation. *(Correction applied
  2026-05-30: the "unbuilt" claims in tier3-decomposability.md and
  tier3a-cascade-composition.md have been updated.)*
- **The proven Tier-1 depth bound is `baseSize` (one seed per gadget,
  linear, `≤ n/6`), NOT `tw(H)`.** The `tw(H)` bound is classical and
  documented but **not formalized**. Tier 1's Lean content is *orbit
  recovery* (cells = orbits at that depth) — a completeness foundation,
  not a polynomial-efficiency bound. Polynomial runtime still rests on
  the unformalized `tw` bound + bounded `tw`.
- **The cascade-oracle localisation obligation is NOT the wall — keep it
  distinct from sub-claim 2 / (O\*).** Phase-C work (2026-05-29,
  `CascadeOracle.lean`) split the oracle's *localisation* obligation into
  (1a) bounded-depth recoverability — **proved** on the cascade class
  (`RecoverableByDepth` + `recoverableByDepth_cfi`/`_scheme`, anchored at
  both ends by `cellsAreOrbits_of_discrete` and
  `cellsAreOrbits_of_compl_card_le_two`) — and (1b) intermediate→deep
  bridging — **open, but cascade-class construction correctness, not
  `GI ∈ P`**. This is a *different object* from Tier-3 **sub-claim 2 /
  (O\*) / existence of an admissible cascade-class chain**, which **is**
  the `GI ∈ P` wall (§8). Do not conflate: "localisation is not GI-hard"
  refers to the oracle contract *given* a recoverable chain; it says
  nothing about whether such a chain exists. Verdict iso-invariance is
  likewise discharged conditionally (it reduces to localisation).

---

## Part A — Infrastructure prerequisites

**Why this is its own part.** The Lean currently represents automorphisms
only as `IsAut π adj` (a predicate on a *single* permutation) and
`OrbitPartition adj P S v w` (the orbit *relation*). There is **no group
object** — no `Subgroup`, no `MulAction`, no quotient — anywhere in the
proof stack (verified: the only `⋊`/`Subgroup`/`Normal` token in the
sources is a comment in `CFI.lean`). The orbit-recovery program
*deliberately* avoided group structure (it only ever needed
`Discrete (warmRefine …)`). Tier 3's entire vocabulary —
`H_0 ⊵ … ⊵ H_k`, quotient graphs `G/H_i` — is meaningless without it.
So Part A is a genuine prerequisite for Part B1 (and a convenience for
B2/B3).

**Permutation-level precursors already built (what Part A lifts to the group).**
Two strands of recent work live at the single-permutation level and *motivate* —
and would be made rigorous by — Part A's group object:

- **The support backbone** (`CascadeOracle.lean` §C.0.1:
  `orbitPartition_of_support_disjoint`, `exists_orbit_witness_of_aut`). These pin
  `π ∈ Aut_S ⟺ Disjoint S (π.support)` at the permutation level — exactly A1's
  "OrbitPartition ↔ pointwise-`S`-stabilizer" bridge, minus the `Subgroup`. The
  related correction "**fixing a vertex in `supp(π)` *relocates* `π` to the
  stabilizer-chain transversal, it does not *destroy* it**" (it stays in `Aut(G)`)
  is currently *stated only informally* — making it rigorous needs the stabilizer
  chain, i.e. **A2 (MulAction/orbits) + A3 (the chain)**. The support-graded
  availability depth `n − |supp π|` then becomes a statement about chain depth.
- **B2's twists are concrete transversal elements.** The linear oracle's verified
  twists (`LinearOracle.lean`: `candidateTwist`, `canonicalTwistOracle`) are the
  `Z₂` coset representatives for each abelian decision — the elements that, under
  A1/A2, populate the level transversals and generate the residual
  **elementary-abelian** factor `N = Z₂^d`. The abelian structure is already proved
  at the `DirAssignment` level (`flipPair_idempotent` = involution,
  `flipPair_comm` = commuting); A1 lifts it to "`N` is an elementary-abelian
  *subgroup* of `AutGroup`", which is what `Aut(G) = N ⋊ Q` (§0) actually asserts.

So the **B2 → Part A path** is: B2 establishes the twists/soundness at the
permutation level; Part A's group object then (a) makes "relocation to transversal"
a theorem, and (b) packages the twists as the `N = Z₂^d` normal factor of the
semidirect product. Neither is needed for B2's own soundness (done), but both are
the natural next rigor once Part A lands.

> **STATUS — A1–A3 (the glue tier) DONE (2026-05-30).** Built in
> [`ChainDescent/Group.lean`](../GraphCanonizationProofs/ChainDescent/Group.lean)
> (module `ChainDescent.Group`, axiom-clean — `[propext, Classical.choice, Quot.sound]`,
> **no `refineStep`**, no `sorry`); theorem map in `PublicTheoremIndex.md`
> §"ChainDescent/Group.lean". Only **A4** (the quotient *graph*) remains in Part A.

### A1 — `Aut(G)` as a group — **DONE**

- **Define** `AutGroup adj : Subgroup (Equiv.Perm (Fin n))` as
  `{π | IsAut π adj}`. Discharge the `Subgroup` axioms from the existing
  `IsAut.refl / .trans / .symm` (already proved in `ChainDescent.lean`).
  ✅ `AutGroup` + `mem_autGroup` (`mul_mem'` reads `IsAut.trans hb ha`,
  since `Equiv.Perm` multiplication is `a * b = b.trans a`).
- **Mathlib:** `Subgroup`, `Equiv.Perm` group structure — all present.
  Pure glue.
- **Bridge to keep:** `OrbitPartition adj P S v w` ↔ "∃ `g ∈` the
  pointwise-`S`-stabilizer of `AutGroup adj` *that also preserves `P`*,
  with `g v = w`." Keep `OrbitPartition` as the working object; `AutGroup`
  is only needed where the *chain* is referenced. ✅ `orbitPartition_iff_autGroup`
  (the `FixesPointwise ↑g S` conjunct *is* the pointwise-`S`-stabilizer condition).
- **Effort:** ~100–150 lines. **Risk:** low. *(landed ~70 lines)*

### A2 — Action on vertices + orbit bridge — **DONE**

- **Define** the `MulAction (AutGroup adj) (Fin n)` (restriction of the
  perm action). ✅ Inherited automatically (subgroup restriction of
  `Equiv.Perm.applyMulAction`); `autGroup_smul : g • v = ↑g v` (`rfl`).
  Relate its orbits to the **root** orbit relation `OrbitPartition adj P ∅`
  (the `S = ∅` case — `FixesPointwise π ∅` vacuous; *not* `univ`, which is
  trivial). The `P`-preservation conjunct is the wrinkle — handled by a
  `P`-invariance hypothesis (`∀ π, IsAut π adj → π` preserves `P`; the
  Tier-2 `hP_invariant` pattern, holds for trivial/profile `P`).
  ✅ `mem_orbit_autGroup_iff` (pure, pre-`P`) +
  `mem_orbit_autGroup_iff_orbitPartition` (with `P`-invariance).
- **Mathlib:** `MulAction`, `MulAction.orbit`, `orbitRel` — present.
- **Effort:** ~100 lines. **Risk:** low. *(landed ~30 lines)*

### A3 — Normal subgroup chains — **DONE**

- **Define** `LayerChain adj` := a finite descending chain
  `H_0 = AutGroup adj ⊵ H_1 ⊵ … ⊵ H_k = ⊥` of normal subgroups
  (relative normality: `(layer (i+1)).subgroupOf (layer i)` is `Normal`).
  ✅ `LayerChain` structure (`len`, `layer : ℕ → Subgroup`, `head_eq`,
  `last_eq`, `descending`, `normal`) + `LayerChain.trivial` (the one-step
  `AutGroup ⊵ ⊥` chain) + `Inhabited` instance.
- **Mathlib:** `Subgroup.Normal`, `subgroupOf`, `QuotientGroup` — present.
  The chain bookkeeping is standard.
- **Effort:** ~150 lines. **Risk:** low. *(landed ~50 lines)*

### A4 — Quotient graph `G/H` (the Mathlib gap) — **DONE (core)**

> **STATUS — A4 DONE (2026-05-30).** Built in
> [`ChainDescent/Group.lean`](../GraphCanonizationProofs/ChainDescent/Group.lean)
> §A4 (axiom-clean; `cell_iff_orbitMk_eq`/`quotientAdjCompatible_of_discrete` use the
> permitted `refineStep`/`refineStep_iff` basis via `warmRefine`). Index:
> `PublicTheoremIndex.md` §A4. **Part A is now complete.**

- **Define** the quotient graph on the `Aut_S`-orbits of `V(G)`: vertices =
  orbit set, adjacency induced by `G`'s edge set. ✅ The vertex set is
  `OrbitQuotient adj P S = Quotient (orbitSetoid …)` (the orbits of
  `OrbitPartition adj P S`, already an equivalence relation), with
  `Fintype`/`DecidableEq` and the quotient map `orbitMk`.
  *Design note — the orbit object.* The quotient is taken by the **relation**
  `OrbitPartition adj P S` (the cascade machinery's working object = `Aut_S`-orbits),
  not directly by a `Subgroup` `H`; under `P`-invariance these coincide with the
  `AutGroup` `MulAction` orbits — `orbitQuotientEquivAutGroup` exhibits
  `OrbitQuotient adj P ∅ ≃ V(G)/Aut(G)`, tying A4 back to A1/A2 and honoring the
  "quotient by a subgroup of `Aut(G)`" framing for the root case.
  *Induced adjacency is genuinely conditional.* `adj v w` is **not** constant on
  orbit-pairs in general (`adj (g v) w = adj v (g⁻¹ w)`), so the simple induced
  adjacency `quotientAdj` is well-defined exactly under `QuotientAdjCompatible`
  (constant-on-orbit-pairs) — given, with the defining equation
  `quotientAdj ⟦v⟧ ⟦w⟧ = adj v w` and the discreteness anchor
  `quotientAdjCompatible_of_discrete`. This is the "induced adjacency
  well-definedness" friction the plan flagged, now isolated as a hypothesis (the
  multigraph/symmetrisation subtlety lives there).
- **Key lemma needed:** the 1-WL partition on `(G, S)` corresponds to the quotient
  vertices. ✅ `cell_iff_orbitMk_eq`: under `CellsAreOrbits`, `v, w` share a 1-WL cell
  **iff** `orbitMk v = orbitMk w`. Forward = `CellsAreOrbits` + `Quotient.sound`;
  backward = the unconditional `OrbitPartition.subset_warmRefine` + `Quotient.exact`.
  This is the bookkeeping lemma both docs flag — it came out clean because the orbit
  *relation* (not a re-indexed `AdjMatrix (Fin m)`) is the quotient carrier.
- **Effort:** ~250–400 lines estimated. **Risk:** medium. *(landed ~90 lines —
  cheaper than feared by quotienting the relation directly and leaving the induced
  adjacency conditional; the deferred bookkeeping is the `OrbitQuotient ≃ AdjMatrix
  (Fin m)` re-indexing, needed only if B1 wants the quotient literally typed as an
  `AdjMatrix` rather than an adjacency function on the orbit type.)*

**Part A total:** ~600–800 lines estimated, mostly glue except A4. Axiom-clean
(uses Mathlib group theory + existing `IsAut` lemmas). **A1–A4 all landed
2026-05-30 (~240 lines total, axiom-clean). Part A complete; B1 is now unblocked.**
*Deferred sub-bookkeeping:* the orbit-type → `AdjMatrix (Fin m)` re-indexing (a
label-choice the canonizer otherwise avoids) is left until B1 forces a concrete
`AdjMatrix`-typed quotient; the adjacency *function* on the orbit type
(`quotientAdj`) is in hand.

---

## Part B — Tractable theorems

### B1 — Tier 3a (cascade composition) — *needs Part A*

> **Theorem 3a.** If `Aut(G) = H_0 ⊵ … ⊵ H_k = ⊥` and each successive
> quotient `H_{i-1}/H_i` acts on `G_{i-1} = G/H_i` in a cascade class
> with depth bound `f_i`, then `G`'s cascade depth is `≤ Σ f_i`.

> **STATUS — Phases A + C DONE (2026-05-30).** The headline `cascadeComposition`
> ("depths add") is proved in
> [`ChainDescent/Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean)
> (axiom-clean), **conditional on the per-layer transfer** `LayerStep` (= §4.2.5);
> `cumulative_card_le` gives `|S| ≤ Σ fᵢ`. **Phase D — discharging `LayerStep` from
> Tier-1/2 via A4's quotient (the §4.2.5 transfer) — is the remaining work**, attacked
> intrinsically on `Fin n` (build-plan §3, easiest-layer-first). Full plan:
> [`chain-descent-tier3a-b1-build-plan.md`](./chain-descent-tier3a-b1-build-plan.md).

- **New mathematical content:** essentially one lemma — step 4.2.5 of the
  Tier-3a doc ("1-WL on a cell = 1-WL on the quotient vertex," = A4's key
  lemma) — plus an induction on chain length.
- **Builds on (proved):** `warmRefine_refines` (1-WL monotone in the
  individualization set); Tier 1 (`theorem_1_HOR_cfi_oddDeg`) and Tier 2
  (`theorem_2_HOR_concrete_*`, incl. the isolation-bootstrap rank-≥3
  schemes) as the per-layer cascade-class instances.
- **Structure:** a `CascadeClass` abstraction (graph family + depth-bound
  function `f`) with Tier 1 / Tier 2 as instances; the `composition`
  lemma by induction on the `LayerChain`.
- **Effort:** ~1500–3000 lines (per the Tier-3a doc §9). **Risk:** low
  for the math, medium for A4 bookkeeping. **Conditional on:** an
  admissible chain existing (the excluded wall) — Theorem 3a is an
  *implication*, not a guarantee one exists.

### B2 — Sub-claim 1 (abelian-stripping) — *mostly independent of Part A*

> Every commit set produces, per coupled component, either a **unique
> candidate twist** (→ a verified `Z₂` generator) or a non-abelian
> residual (→ the wall). The unique-twist branch is the linear oracle's
> mechanism; formalize that it yields a verified automorphism.

- **Why mostly independent of A:** the linear-oracle interface already
  lives at the *permutation / `DirAssignment`* level, not the group
  level: `LinearOracleSpec`, `LeafTwistSpec`, `DirAssignment`, `flipPair`,
  `flipPair_idempotent`, `flipPair_comm` (the `Z₂^d` action) are all in
  `ChainDescent.lean §15.8` already. Only the "twists *generate a
  subgroup*" framing wants A1; the core predicate + verification does not.
- **New content:** a precise `UniqueCandidateTwist S K t` predicate (the
  reverse-symmetric pattern over a coupled component `K` determines `t`),
  and the discovery as a total function under the uniqueness hypothesis,
  with the mandatory edge-by-edge verification as the soundness anchor.
- **Builds on (proved):** `warm_6_2` (direction-symmetric split),
  `warmRefine_agree_off'` / `spine_branch_independent` (the descent
  spine — one partition for all `2^d` leaves), `flipPair_comm`
  (abelianness).
- **Note:** the linear oracle is *built and validated in C#* (through
  CFI(K7)); B2 is its **formalization**, not new algorithm design.
- **Effort:** ~1–2k lines (Tier-3 doc §5/§11). **Risk:** low — the
  uniqueness boundary is already specified; the work is making the
  predicate + discovery precise. Main hazard: cleanly delineating a
  coupled component from the refinement footprint.

> **STATUS — B2 soundness core DONE (2026-05-30).** Built in
> [`ChainDescent/LinearOracle.lean`](../GraphCanonizationProofs/ChainDescent/LinearOracle.lean)
> (module `ChainDescent.LinearOracle`, axiom-light, no `sorry`); detail in
> [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §8.2;
> theorem map in `PublicTheoremIndex.md` §L.1–§L.3.
>
> - **The plan above is superseded on one point.** It anticipated a
>   `UniqueCandidateTwist S K t` predicate + "discovery as a total function". At
>   the **leaf level** (where `LinearOracleSpec` operates) the twist is not
>   *searched* among candidates — it is **forced**: `canonAdj σ = labelledAdj
>   (rankPerm π_σ) adj`, so the two branches' leaves differ by exactly the rank
>   rebasing `candidateTwist = rankPerm π_flip · (rankPerm π_σ)⁻¹`, which *always*
>   realises the flip (`candidateTwist_realizesFlip`, via the `canonAdj_rebase`
>   bridge = the `warm_6_2`/spine → `canonAdj` step). Determinacy is then automatic
>   (`candidateTwist_unique`), discharging the iso-invariance gate (strategy §15
>   gap 2) at the leaf level. The §4.2 "construction risk" (calculator §9 item 4)
>   **dissolves**: the permutation is determined; only the §4.5 edge-check is
>   runtime content.
> - **Delivered:** `RealizesFlip`, `TwistWitness`, `twistOracle` +
>   `twistOracle_leafTwist` (soundness for any verified discovery, explicit witness
>   `σ' = flipPair σ`); `candidateTwist` + `canonAdj_rebase` + the forced-candidate
>   realisation; `canonicalTwistOracle` — a **fully concrete** `LinearOracleSpec`
>   (select pair → forced candidate → return iff `IsAut` verifies) satisfying
>   `LeafTwistSpec`; `candidateTwist_flip_inv` (the `Z₂` involution) — with
>   `flipPair_comm` the elementary-abelian `Z₂^d` structure.
> - **Completeness CHARACTERISED (2026-05-30, `LinearOracle.lean` §L.4, axiom-clean).**
>   The oracle **fires ⟺ forced candidate ∈ Aut** (`canonicalTwistOracle_isSome_iff`);
>   firing is semantically justified (`realizableFlip_of_isAut_candidateTwist` — branches
>   genuinely `Aut`-equivalent) and `Z₂`-direction-consistent (`candidateTwist_flipBack_isAut`).
>   **Key finding:** completeness is regime-dependent *by design* — the forced
>   (rank-aligned) candidate ∈ Aut exactly on **abelian** decisions (the calculator §6
>   boundary); the general converse fails (conjugation gap). The open core is the
>   **abelian-sufficiency lemma** (forced candidate verifies for real abelian flips, via
>   `warm_6_2`).
> - **Remaining (B2):** (i) the `canonForm` lex-min tie (Tier-3 §8.2 step 3 — needs
>   a descent-with-pruning model, the genuine big piece); (ii) the **abelian-sufficiency
>   lemma** (the open core of completeness, above); (iii) lifting the twists to an
>   elementary-abelian *subgroup* `N` — that is **Part A** (now built; see the precursors
>   note at the top of Part A).

### B3 — Sub-claim 3 (oracle alternation) — *needs B2*

> The cascade and linear oracles compose soundly under any call order,
> because the cascade oracle's failure mode is a polynomial *degenerate*
> output (return every target-cell vertex), not a flag. So the descent
> alternates freely and stays correct.

- **New content:** reduces to a case analysis: (1) cascade oracle
  terminates polynomially in failure with a sound degenerate output —
  already the shipped behaviour, captured in `CascadeOracle.lean`'s
  soundness (`OrbitMapSpec`/`merged_sameCell`); (2) linear oracle
  terminates (B2); (3) the two failure modes are disjoint per node.
- **Do NOT prove** sub-conjecture 3′ (commutation — *same* residual
  group regardless of order). It is **optional and not needed**. Note
  the proven partition-level order-independence (`spine_branch_independent`)
  is the closest established fact; 3′ is the unproven lift of it.
- **Builds on:** B2 + the cascade-oracle contract (`CascadeOracle.lean`,
  already axiom-clean).
- **Effort:** ~500–1000 lines. **Risk:** low; cheap given B2.

---

## Dependency graph & suggested order

```
   A1 ─┬─ A2 ─┐
       └─ A3 ─┴─ A4 ───────────── B1 (Tier 3a)
                                    │
   (independent) ── B2 (linear) ────┴── B3 (alternation)
```

**Recommended order** (progress as of 2026-05-30):

1. **B2 — soundness core DONE** (see B2 STATUS above). The reusable formal object
   (`canonicalTwistOracle`, `candidateTwist`) that B3 and the Tier-3 narrative want
   exists. Remaining B2 pieces (canonForm tie, completeness, subgroup `N`) are
   listed there; (iii) is Part A.
2. **Part A — A1→A2→A3→A4 ALL DONE (2026-05-30). Part A complete.** The group object
   exists (`ChainDescent.Group`: `AutGroup`, the vertex `MulAction` + orbit bridge,
   `LayerChain`), *and* the quotient layer (`OrbitQuotient`, `cell_iff_orbitMk_eq`,
   `quotientAdj` + the root `≃ V(G)/Aut(G)`). That gives the full substrate for B1,
   *and* the home for making rigorous (a) the support backbone's "fixing relocates to
   transversal, not destroys" and (b) B2's twists-as-`N` (the Part A precursors note)
   — both now stateable as group-level theorems (not yet proved; they want A2's orbit
   machinery + A1's subgroup, both present). **B1 (Tier 3a) is now unblocked** — its
   induction step is `cell_iff_orbitMk_eq`. One deferred sub-bookkeeping remains
   (orbit-type → `AdjMatrix (Fin m)` re-indexing), needed only if B1 demands a
   literally `AdjMatrix`-typed quotient.
3. **B1 (Tier 3a).** The headline composition theorem, once A4's
   cell = quotient-vertex lemma is in hand.
4. **B3.** Cheap capstone once B2 + the cascade contract are in place. (Cascade
   side already axiom-clean; B2 soundness done — B3 is the alternation glue.)

Each step independently axiom-clean and independently valuable: B2 gives
the abelian-stripping theorem; A+B1 gives polynomial canonization for
decomposable layered graphs; B3 ties the oracle alternation together.

---

## Out of scope (the wall)

**Sub-claim 2 / residual cascade / (O\*) self-detection / existence of an
admissible cascade-class chain.** Equivalent in strength to GI ∈ P. Every
Part B theorem is *conditional* on it (they assume a chain exists or
decomposition holds). Progress on the wall is a separate research track
(an (O1)/(O2)-shaped "any hidden Johnson must have fingerprint X" result;
the scheme-side `RelIsolatedAt` isolation bootstrap is a partial model of
(O\*) but does not cross the encoded-symmetry bridge). Do **not** let Part
B work drift into it — the value of this buildout is precisely that it is
the GI-independent, finite-effort remainder.

---

## Build / verification protocol

- Build target: `lake build ChainDescent.Scheme` (or the relevant module);
  new group/quotient infra likely a new sub-module
  `ChainDescent/Group.lean` registered in `lakefile.toml` defaultTargets.
- After each lemma: `#print axioms <name>` must show only the standard
  basis (`propext, Classical.choice, Quot.sound` + `refineStep`,
  `refineStep_iff` where refinement is used). **No new placeholder
  axioms.** Mathlib group theory adds none.
- Incremental: build after each piece; the existing Tier-1/2 + bootstrap
  results must stay green and axiom-clean.

---

## Cross-references

- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §4 (sub-claims), §8 (the excluded wall + (O\*)), §11 (Lean order).
- [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
  §4 (proof), §9 (Lean phases A–D — Part A/B1 here refine those).
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
  — Tier 1 (§5) / Tier 2 (§14, §10.11 bootstrap) base cascade classes.
- [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
  — the linear oracle B2 formalizes (built, validated through CFI(K7)).
- [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
  — the a-priori cascade oracle (built; contract in `CascadeOracle.lean`).
- `ChainDescent.lean §15.8` — `DirAssignment`, `flipPair`,
  `LinearOracleSpec`, `LeafTwistSpec` (B2's existing scaffolding).
