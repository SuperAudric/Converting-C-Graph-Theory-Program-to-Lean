# The recovery route — proving the forms-graph poly bound the way the canonizer actually works

> **What this is.** The working doc for the **recovery route**: proving the affine-polar forms-graph residue is canonized
> in **polynomial** time by the *existing* chain-descent canonizer, the way it actually achieves a single path —
> **cross-branch automorphism harvest + form-recovery of the residue**, not refinement reaching orbits. This is the
> **recommended** polynomial target (2026-06-30), and it is **implementation-faithful**: the open Lean content is the same
> object the C# canonizer's completeness counter measures, and that counter is empirically clean on the residual family.
>
> **Relation to the other route doc.** [`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md)
> pursues poly *through* bounded WL-dimension (`CellsAreOrbits` = refinement reaches orbits). That was found to be the
> **wrong model of the C#** (the canonizer does not rely on refinement reaching orbits) and is now demoted to
> independent-math value. **This doc is the live route.** Where the two overlap, this doc wins for "what the canonizer does."
>
> **Provenance.** The forms-graph plan ([`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md))
> §1 item 1 (the PROVABLE-BOUND INVESTIGATION, Routes A/B/C); the Stage A/B landings (`remaining-work.md` §3a);
> the C# model comparison + the residual-reconciliation probe (this session, 2026-06-30).

---

## STATUS (read first)

> **════════ PICK-UP (2026-06-30) — READ THIS FIRST ════════**
>
> **The route is recommended AND empirically validated on the residual family.** The chain-descent canonizer canonizes
> `VO^ε_4(q)` (q=3,5; both ε) with **no flag, full `|Aut|` recovered, no starvation** in both descent modes
> (`RecoveryReconcileProbe.cs`). The completeness counter `ClassifyStarved`/`BranchStarved` — documented in `CanonResult.cs`
> as *"the Route-A breaker: if this is ever > 0 the existing harvest is NOT provably complete"* — is **0 in every case**.
> That counter is the exact C# counterpart of the open Lean core `RelCountsDetermineOrbit` / `hFormCert`. So the route's
> central obligation is **empirically true** where the seal needs it.
>
> **What the route proves (the claim).** The canonizer's cost is a **sum over descent-tree nodes**. On the forms-graph
> residue the descent is a **poly-size single path** (the cross-branch harvest recovers `Stab(path)`-orbits and prunes
> isomorphic siblings), and per-node work is **hard-poly** (every harvest loop is `n`-bounded; no exponential mechanism —
> code analysis, plan §1 item 1 "RESOLVED"). Poly node count × poly per-node = **polynomial**. This **sidesteps the open
> bounded-WL-dimension conjecture** (the matching/frame WL route is only quasipoly): the harvest reaches orbits
> *a-posteriori*, it does not need refinement to reach them.
>
> **The ONE open piece (the research core).** Completeness: that the harvest is **starvation-free at a bounded base** on
> the residual families = `RelCountsDetermineOrbit` (Lean, idx 1203). It is **GI-adjacent and FALSE in general** — claimed
> **only** on the Skresanov-isolated small-Aut affine forms-graphs `{affine-polar / alternating / half-spin / Suzuki–Tits}`,
> where it is empirically validated (above) and conjectured to hold. Its concrete, computable handle is the existing Gauss
> machinery: `IsotropySeparatesAtBase Q T` (idx 1240) at a **bounded** base — the quasipoly seal already proved this at the
> `Θ(log n)` matching base; the poly upgrade is to prove it at a bounded (`O(d)` symmetry-broken) base.
>
> **LIVE NEXT TASK.** Strengthen the Gauss endpoint from *separate-at-one-big-base* to *determine-the-orbit-at-a-bounded-base*:
> prove `IsotropySeparatesAtBase Q T` for a bounded symmetry-broken `T`, feeding the **already-landed, axiom-clean** Witt-free
> capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248). Secondary: formalize the harvest-completeness
> ↔ `RelCountsDetermineOrbit` bridge (§5), and the per-node / node-count poly (a complexity proof, or accept it meta).
>
> **Banked (unaffected):** quasipoly seal `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (in `build.sh`, axiom-clean);
> sub-exp `reachesRigidOrCameron_viaSpielman` (citable). **Durable harness:** `GraphCanonizationProject.Tests/RecoveryReconcileProbe.cs`.
> **════════ END PICK-UP ════════**

**Quality bar:** every Lean theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; no `sorry`, no fresh `axiom`;
`native_decide` banned; full build green when ported. "Poly time" stays a **meta-argument** — the project formalizes no
runtime model, so the structural deliverable is the seal disjunction `reachesRigidOrCameron` (modulo `{G3}`), and "poly"
is the meta-claim that the node count is poly and per-node work is poly.

---

## 1. The claim, and why this is the right route

**The cost model.** Chain descent's cost is `Σ_{nodes} (per-node work)`, **not** the naive product over a fully-explored
IR tree (00-START-HERE §1). Two things make this polynomial on the forms-graph residue:

1. **Poly node count.** The descent is a single path (or a branch-but-resolve tree with poly-many leaves): at each node the
   cross-branch harvest discovers the `Stab(path)`-automorphisms and prunes every sibling that is in the same orbit
   (`CoveredByPathFixingAut`). The path length is `≈ d+1` (the group base), and `d ≤ log₂ n` (since `n = q^d ≥ 2^d`), so any
   `d`-factor in the node count collapses to `poly(n)`.
2. **Poly per-node.** Every harvest loop in `ChainDescent.cs` is `n`-bounded; there is no exponential mechanism (plan §1
   item 1 "RESOLVED", code analysis). Per-node work has a hard poly ceiling (≈ `n⁵–n⁶`).

**Why it sidesteps bounded-WL-dimension.** The matching/frame route reaches orbits by *individualization-refinement* — it
needs the WL-closure partition to equal the orbit partition at a bounded base = **bounded WL-dimension = open math**, and
even at the `O(d)` frame the base is `Θ(d)` so it only gives `n^{Θ(d)}` = quasipoly. The recovery route does **not** ask
refinement to reach orbits. It lets the descent branch, **recovers the automorphisms by harvest**, and prunes — orbits are
reached *a-posteriori from verified automorphisms*, never from refinement. Forms-graph isomorphism is known to be poly; the
recovery route is the mechanism that delivers it, and it is the mechanism the C# canonizer actually runs.

**Honest scope.** This does **not** make the hard part disappear — it **relocates** it. The open content is no longer
"WL-dim bounded" but **harvest completeness**: that the harvest is starvation-free (recovers enough automorphisms to prune
to a poly-size tree) at a bounded base. That is `RelCountsDetermineOrbit`, GI-adjacent and false in general; the route's bet
— now backed by the probe — is that it holds on the carved residual families, via the Gauss machinery already built for the
quasipoly seal.

---

## 2. The object + the C# mechanism

### 2a. The residue
- **Graph.** `V = K^d` (`K = F_q`, `d = 2m`), adjacency `Q(x − y) = 0` for a nondegenerate quadratic form `Q` of type `ε`
  — the affine-polar forms graph `VO^ε_{2m}(q)`. A translation (Cayley) scheme ⟹ vertex-transitive + schurian.
- **Automorphisms.** The affine similitude group: translations `⋊` `ΓO^ε(Q)` (linear similitudes `Q(gx) = μ(g)·Qx`, with
  field automorphisms; for prime `q`, just `GO^ε(Q)`). `|Aut|` is huge (e.g. `VO⁻₄(3)`: `233280 = 3⁴ · |GO⁻₄(3)|`) — the
  graph is far from rigid, which is *why* the harvest single-paths.
- **Skresanov isolation.** By the route-doc §9.9.18 reduction, the small-Aut non-geometric *schurian* rank-3 residue is
  affine, and splits into `{1-dim cyclotomic (cited) + forms-graphs (c)–(f)}`. The recovery core is needed only on (c)–(f)
  `{affine-polar / alternating / half-spin / Suzuki–Tits}`.

### 2b. How the canonizer reaches a single path (verified against `GraphCanonizationProject/`)
1. **1-WL refinement** (`WarmPartition.cs`): colour refinement to cells. Cells are coarser than orbits at bounded bases —
   the canonizer does **not** rely on cells = orbits.
2. **All-reps oracle** (`CascadeOracle.cs`): "certifies nothing a priori" — `Classify` returns every vertex of the target
   cell. Orbit structure is recovered a-posteriori, not asserted.
3. **Cross-branch harvest + prune** (`ChainDescent.cs:589 CoveredByPathFixingAut`): after exploring the first representative
   of a cell, the descent harvests verified automorphisms that fix the individualized path pointwise, then **prunes any
   sibling reachable from an explored one via those `Stab(path)`-automorphisms** (its subtree is isomorphic — no canonical
   it omits). This is the engine that collapses the tree.
4. **Deferral selector** (`ChainDescent.cs:251-281`, **on in normal operation** — it changes the canonical form): among
   non-singleton cells, consume one the oracle collapses to a single orbit (symmetric), defer multi-orbit cells, branch a
   real one only when none is symmetric (Phase 2). An *optimization* over the harvest, not the core mechanism.

**The default (canonical-form-preserving) path — what Lean's `spine_branch_independent` certifies — reaches completeness
via the HARVEST (step 3), not the deferral (step 4).** So the Lean poly proof should target **harvest completeness**, and
treat deferral as an optional canonical-form-changing optimization.

---

## 3. What is already proved (the foundation, all axiom-clean)

The recovery route's Lean spine is **substantially landed** — the open content is isolated to one Gauss predicate.

### 3a. The conditional capstones (carry the open core, everything else discharged)
- **Stage A — `reachesRigidOrCameron_viaAffineFormScheme`** (idx 1207). The abstract scheme-level capstone for the
  forms-graph residue: carries `hbase : IsBase … T` (the **free** group base `T = {0,e₁,…,e_d}`, `(G^(2))_T = {1}`,
  discharged outright) + `hFormCert : RelCountsDetermineOrbit … T` (**the only open content**). Wiring:
  `cellsAreOrbits_of_relCountsDetermineOrbit` → `twinsRealizedByResidualAut_iff_cellsAreOrbits` →
  `separatesAtBoundedBase_of_twinsRealized` → `reachesRigidOrCameron_viaSpielman`. **Carries NO `hSmallAutThin`.**
- **Stage B (live) — `reachesRigidOrCameron_viaIsotropySeparates_wittFree`** (idx 1248). The concrete forms-graph
  capstone: seals the rank-3 SRG `VO^ε` residue from a **bounded symmetry-broken base** + **isotropy-count injectivity**,
  carrying **NO Witt** (the easy half `RelationRefinesIsotropy` is discharged Witt-free by similitude-invariance,
  `relationRefinesIsotropy_similitude`, idx 1247). The **only** open input is the Gauss target `IsotropySeparatesAtBase Q T`
  (idx 1240). This is the live endpoint.

### 3b. The recovery-core plumbing (Stage A, idx 1203-1206)
- `RelCountsDetermineOrbit` (1203) — the open predicate (two vertices with equal relation-count profile at base `T` lie in
  the same `Stab(T)`-orbit). **Open / GI-adjacent / false for high `s(C)`.**
- `cellsAreOrbits_of_relCountsDetermineOrbit` (1204), `recoversWhileSymmetric_of_relCountsDetermineOrbit` (1205),
  `selfDetectsWhileSymmetric_of_relCountsDetermineOrbit` (1206) — the producers that lift the predicate to the seal.

### 3c. Stage B.0 — the recovery back-half (form coords ⟹ vector), landed
- `coords_determine` (1211) + `polar_eq_of_sub` (1210): if `Q`'s polar is nondegenerate and `Q v`, `Q(v − e_i)` agree on
  the basis, then `v = v'`. The Witt-free back-half — **reusable**.
- `isometryGroup` / `similitudeGroup` (1212/1218), `frameBase` (1215), `reachesRigidOrCameron_viaOrthogonalForm` (1217):
  the isometry scheme `O(Q)` discretizes at the basis-frame and seals via depth-1. **Caveat (the crux gap, §4):** this is
  the *finer* `O(Q)`, not the rank-3 SRG `VO^ε` (= similitude `GO(Q)`, relation = `isoClass`).

### 3d. The Gauss toolkit (the analytic engine, shared with the quasipoly seal)
`GaussCount.lean` (Gauss-sum lemmas incl. `gaussSum_sq_ne_zero`, `sum_addChar_quadForm_ne_zero`); `IsotropicIncidenceCount*`
(`configGaussSum_eq_det`, `card_quadForm_eq`); `ObservableCountBridge*` (`χ(det G₂) ↔ Z_u(S)`); `PairForm`,
`PerAnchorBound.c0_le_threequarters`. **All field-generic** (`FieldGeneric*`). This is exactly the machinery that proved
`IsotropySeparatesAtBase` at the matching base — the poly upgrade reuses it.

### 3e. SUPERSEDED (do not build on — frame-locked, FALSE for `VO^-`)
`SimilitudeFrameSeparates` (1221), `reachesRigidOrCameron_viaSimilitudeForm` (1222), `CountsDetermineFrameQ` (1224),
`IsotropyCountsRecoverFrameQ` (1234), `reachesRigidOrCameron_viaCountsDetermineFrameQ` (1226), `…viaIsotropyCounts` (1237).
A finite probe showed the one-round count is shell-blind at the *symmetric* frame for minus-type (an `e_i`-swap isometry).
The fix — already landed — is the **arbitrary / symmetry-broken base** family (`SeparatesAtBase` 1238,
`reachesRigidOrCameron_viaSymmetryBrokenBase` 1239, `IsotropySeparatesAtBase` 1240). Use those.

---

## 4. The open core, precisely — and the `O(Q)` vs `VO^ε` gap

The route reduces to **one** statement, in two equivalent languages:

> **Harvest completeness / `RelCountsDetermineOrbit`** (orbit language). At a bounded base `T`, the relation-count profile
> determines the `Stab(T)`-orbit — equivalently, the cross-branch harvest is **starvation-free** (`ClassifyStarved = 0`).

> **`IsotropySeparatesAtBase Q T`** (Gauss language). At a bounded symmetry-broken base `T`, the isotropy-class counts are
> injective in the relevant vertex — the affine-quadric point count *determines* the orbit.

**The gap that makes it non-trivial (plan §1 item 1, ROUTE-A DEEP-SCOPE).** Stage B.0's clean
"orbit-of-difference ⟹ exact `Q(v−t)` ⟹ `coords_determine`" mechanism works only on the **isometry** scheme `O(Q)`. The
descent runs on the coarser **similitude SRG** (relation = `isoClass` ∈ {0, isotropic, anisotropic}, *not* the exact
`Q`-value). So resolving a relative sphere to an orbit at a partial base needs the **count crux** — the isotropy counts must
*determine* the orbit, not merely separate it. That is the strengthening from the quasipoly seal:

| | base | what's proved | gives |
|---|---|---|---|
| **quasipoly seal (landed)** | matching, `Θ(log n)` | `IsotropySeparatesAtBase` via `c0_le_threequarters` + union bound — a *separator* | quasipoly |
| **recovery core (open)** | bounded `O(d)` symmetry-broken | `IsotropySeparatesAtBase` as a *determiner* at a bounded base | poly |

**Why the gap is fundamental to the current proof technique.** `c0_le_threequarters` is a *constant-fraction-per-anchor*
bound (each good anchor separates ≥¼ of pairs); a fraction bound covers all pairs only by union-bounding over `Θ(log n)`
anchors — it **structurally cannot** reach a bounded base. The bounded-base statement needs "each anchor kills a fraction"
replaced by "the `O(d)`-frame count-profile **determines** the orbit" — a moment-inversion / non-singularity argument
(natural strengthening of the same Gauss machinery from *bounding* to *inverting*).

**The crackability evidence (from the demoted route's probes, still valid).** `wall_*.py` (now in
`chain-descent-cellsareorbits-route.md` §6) found that the iterated `χ(det G₂)` 2-WL observable **determines** the orbit at
a bounded base with `O(1)` iteration depth, uniformly in `d, |S|, q,` type — so the inversion is a *bounded* number of
character-sum rounds, not an unbounded fixpoint. (Caveat: that probe is about the *2-WL* observable; the recovery route's
descent is 1-WL + harvest. The probe shows the *information* is there at a bounded base; the recovery route extracts it via
harvest rather than 2-WL, which is consistent — the harvest is at least as strong as the relation-count profile.)

---

## 5. The C# ↔ Lean bridge (the empirical validation, and a sub-task)

The route is implementation-faithful because its open Lean core is the same object the canonizer's completeness counter
measures. The correspondence:

| C# (`CanonResult.cs` / `ChainDescent.cs`) | Lean | meaning |
|---|---|---|
| `ClassifyStarved` / `BranchStarved` = 0 | `RelCountsDetermineOrbit` holds | harvest recovers every true orbit-equivalence; no flag |
| `Phase2Nodes` = 0 (deferral) | `∃` single-orbit cell to consume at each base | deferral single-paths (an optimization) |
| `LeafCount` (poly) / single path | poly node count | the descent tree is poly |
| `GeneratorsHarvested`, `ResolvedByRecursion` | the harvest itself | a-posteriori orbit recovery |

**Empirical validation (`RecoveryReconcileProbe.cs`, 2026-06-30, the REAL canonizer on `VO^ε_4(q)` q=3,5):**
- `ClassifyStarved = BranchStarved = 0` in **every** case, **both** modes; **no flag, full `|Aut|` recovered**. ⟹ harvest
  empirically complete on the family = the open core HOLDS here.
- `Phase2 = 0` everywhere (deferral always finds a single-orbit cell). The earlier `descent_probe.py` `Phase2 = 1` was a
  greedy-replication artifact — there is **no genuine rigid residue with no orbit-pure cell**.
- Default mode may *branch-but-resolve* (`VO⁻₄(5)`: 4 resolved branches, leaves=6, STARVED=0); deferral gives the true
  single path (leaves=1). Both modes complete. *(d-scaling check `VO⁻₆(3)` / `VO⁻₄(7)` pending — confirms STARVED stays 0
  as `d` grows.)*

**Sub-task (not yet a Lean lemma).** The table's top row — `ClassifyStarved = 0 ⟺ RelCountsDetermineOrbit` — is **asserted
in the docs but not itself a proved bridge**. Formalizing "harvest completeness (the C# `CoveredByPathFixingAut` prune is
exhaustive) ⟺ the relation-count profile determines the orbit" is a genuine modelling lemma on the seam between the C#
algorithm and the Lean predicate. It is on the route but not the *research* core (which is discharging the predicate itself).

---

## 6. Work-forward plan (ordered)

1. **★ LIVE — discharge `IsotropySeparatesAtBase Q T` at a bounded base.** The single research deliverable. Strengthen the
   Gauss endpoint from *separator* (matching base, landed) to *determiner* (bounded `O(d)` symmetry-broken base). Reuse
   `pairCharSum_factor_gen` / `gaussSum_sq_ne_zero` / the `χ(det G₂) ↔ Z_u` bridge; the target is moment-inversion /
   non-singularity of the character matrix at a bounded base (probed crackable, `O(1)` depth). Feeds the **already-landed**
   `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248) ⟹ seals `VO^ε` modulo `{G3}`, Witt-free, no
   `hSmallAutThin`. **Fallback criterion:** if inversion is non-singular only for large `q`, that is still a real poly result
   for a sub-family (large-`q` slice); if it hits a genuine non-degeneracy obstruction, that *is* the frontier and the
   signal to bank quasipoly + pivot to Route C (§7).
2. **d-scaling confirmation (running).** `RecoveryReconcileProbe.Reconcile_dScaling` (`VO⁻₆(3)`, `VO⁻₄(7)`): confirm
   `STARVED = 0` as `d` grows (the open residue is *unbounded* `d`). If starvation appears, that is the precise residue the
   recovery core must handle — re-scope before the Lean push.
3. **The C#↔Lean completeness bridge (§5 sub-task).** Formalize `ClassifyStarved = 0 ⟺ RelCountsDetermineOrbit` (or the
   weaker single-orbit-cell version) so the empirical validation is connected to the Lean predicate, not just asserted.
4. **Per-node + node-count poly (the complexity proof).** Either formalize the hard-poly-ceiling code analysis
   (loops `n`-bounded, single path, `d ≤ log n`) into a Lean cost statement, or keep "poly" meta and deliver only the
   structural seal (the project's standing convention). Decide with the user.
5. **Other families (Layer C).** Once affine-polar lands: alternating / half-spin reuse the field-generic skeleton; char-2 +
   Suzuki are a separate bespoke track (Arf + additive trace, Mathlib substrate absent). Plan §11.4–§11.5.
6. **PORT.** Move the recovery-route modules into `build.sh` + `lakefile` + `PublicTheoremIndex.md` once the core lands
   (mechanical, no math).

**Definition of done (recovery route, affine-polar):** `IsotropySeparatesAtBase Q T` proved at a bounded base ⟹
`reachesRigidOrCameron_viaIsotropySeparates_wittFree` discharges the `VO^ε` residue modulo `{G3}`; the C# completeness
(`STARVED = 0`) is the empirical witness that the predicate is true on the family. "Poly" remains the meta-claim over the
poly node count + poly per-node.

---

## 7. Route C — the constructive-oracle alternative (recorded fallback)

**Route C (constructive-Witt oracle).** Sidestep `RelCountsDetermineOrbit` *entirely*: **recover `Q` algebraically** from
the rank-3 relations (the two non-identity relations *are* the isotropy types — Stage B.0 `coords_determine` content), then
`Aut = GO(Q)` is a **known** group with explicit generators, canonicalized by standard poly group algorithms
(Schreier–Sims) through the existing `ITransversalOracle` seam. Complexity elementary; correctness depth = form-recovery
(carry it as a hypothesis, prove the downstream canonicalization closes). **It does not depend on the open core** — it works
whether or not the count crux holds, because the form exists unconditionally and geometric recovery bypasses both refinement
and counting.

**Cost-benefit.** Route C is a **larger build + a behavioural change** (needs the form-recovery oracle / a constructive Lean
recovery), and the user prefers to avoid the C# oracle risk. It is the **fallback if step 1 stalls** (the inversion hits a
genuine non-degeneracy obstruction), and the **only** route if the count crux turns out false on some family. Keep it in
view; do not build it unless step 1 stalls.

**Where this sits.** The banked quasipoly seal (`reachesRigidOrCameron_affinePolar`) is the floor; the recovery route
(step 1) is the upgrade to poly via the same Gauss machinery; Route C is the heavier guaranteed-poly alternative. Pursue in
that order.

---

## 8. Pointers

- **★ FRESH READER — PICK UP HERE.** Read this STATUS + §1 (the claim) + §4 (the open core + the `O(Q)`/`VO^ε` gap) + §6
  step 1 (the live task). Then verify the landed substrate (`bash scripts/build.sh` for the in-build seal infra;
  `lake env lean ChainDescent/CascadeAffine.lean` for the Stage A/B capstones).
- **Live Lean endpoint:** `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248), open input
  `IsotropySeparatesAtBase Q T` (idx 1240) at a **bounded** base. Stage A abstract twin:
  `reachesRigidOrCameron_viaAffineFormScheme` (idx 1207), open input `RelCountsDetermineOrbit` (idx 1203).
- **Reusable Lean assets:** `coords_determine` (1211), `relationRefinesIsotropy_similitude` (1247, Witt-free),
  `GaussCount` / `IsotropicIncidenceCount*` / `ObservableCountBridge*` / `PairForm` / `PerAnchorBound`, all field-generic
  (`FieldGeneric*`). **Do NOT build on** the SUPERSEDED frame-locked predicates (§3e).
- **C# canonizer:** `GraphCanonizationProject/ChainDescent.cs` (harvest `:589`, deferral `:251-281`), `CascadeOracle.cs`
  (all-reps), `WarmPartition.cs` (1-WL), `CanonResult.cs` (`CascadeStats` — the `ClassifyStarved` completeness counter).
- **Harness (durable):** `GraphCanonizationProject.Tests/RecoveryReconcileProbe.cs` — runs `VO^ε` through the real canonizer
  in both modes, reports the completeness counters. Run:
  `dotnet test GraphCanonizationProject.Tests/*.csproj --filter "FullyQualifiedName~RecoveryReconcileProbe"`.
- **Crackability probes (information-is-there evidence):** `GraphCanonizationProofs/wall_*.py` (documented in
  `chain-descent-cellsareorbits-route.md` §6).
- **Forms-graph plan (seal/quasipoly build + Routes A/B/C arc):** `chain-descent-formsgraph-wldim-plan.md` STATUS + §1 item 1.
- **Modulo set / what's left map:** `chain-descent-remaining-work.md` §3a. **Demoted WL-dim route:**
  `chain-descent-cellsareorbits-route.md`. **Cross-session detail:** `[[project_formsgraph_wldim_viability_2026-06-28]]`.
