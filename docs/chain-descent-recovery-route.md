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
> **Two deliverables — keep them separate (this is the key clarification).**
> - **The SEAL** (the `reachesRigidOrCameron` disjunction modulo `{G3}` — *correctness*) is **already BANKED at quasipoly**
>   (`AffinePolarSeal.reachesRigidOrCameron_affinePolar`). `RelCountsDetermineOrbit` / `IsotropySeparatesAtBase` feed *that*,
>   via discretization + Spielman. The recovery route does **not** need to re-prove the seal.
> - **POLY** (the *cost* claim — what this route is about) is a **sum over descent-tree nodes**. On the residue the descent
>   is a **poly-size single path** (the cross-branch harvest recovers `Stab(path)`-orbits and prunes isomorphic siblings —
>   the node count is `≈ d+1`, the path length, **not** `n^{Θ(d)}`), and per-node work is **hard-poly** (every harvest loop
>   `n`-bounded; no exponential mechanism — plan §1 item 1 "RESOLVED"). The harvest converts the `Θ(d)` base into a poly
>   node count — that is the win over the individualization/frame route (`n^{Θ(d)}` = quasipoly).
>
> **The open core — count-determination, reached by several BRIDGES (see §2c).** Every poly route
> except Route C reduces to the **same analytic core**: count-determination (`RelCountsDetermineOrbit` / `CellsAreOrbits` /
> the `χ(det G₂)` determiner), GI-adjacent, **claimed only on the Skresanov families** `{affine-polar/alternating/half-spin/
> Suzuki–Tits}` (false in general), and empirically true here (`STARVED = Phase2 = 0`). It does **NOT** sidestep
> bounded-WL-dim — it needs a *weaker form* of it (only Route C truly sidesteps). What differs across routes is the **bridge**
> from core to poly:
> - **Route II — cross-branch harvest (DEFAULT mode, canonical-form-preserving): the most faithful, best-substrated; the
>   recommended primary.** `crossBranchHarvest_reproduces_residual` reproduces the residual group + order; matches the probe's
>   default-mode `STARVED = 0` (branch-but-resolve). Open witness ⟸ the core via `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`.
> - **Route I — node-count bridge / deferral** (`SinglePathDisposition`, `ScratchNodeCountBridge`): models the deferral
>   single-path (`Phase2 = 0`); weaker per-base predicate but changes the canonical form (needs the `canonAdj` seam).
> - **Route III — full `CellsAreOrbits`** (the scaffold): strongest; discharges I and II.
> - **Free/partial:** depth-1 is free (forms graph is P-polynomial ⟹ `theorem_2_HOR_of_pPolynomial`); only `|S| ≥ 2` is open.
>
> **LIVE NEXT TASK.** Two tracks, both live (§2c, §6): **(core)** discharge the count-determination via the `χ(det G₂)`
> determiner (`WallKernelFor Obs`) — and/or the **untried leads** δ′ dominator-closure / Skresanov 2-closure / `EdgeGeneratesFromSet`;
> **(bridge)** wire Route II (`crossBranchHarvest_reproduces_residual`) — or Route I — at `affineScheme`, exposing the core as the
> single open input. The DRG freebie discharges depth 1. *(The seal is banked; no need to re-derive a bounded-base seal predicate.)*
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

**How it beats the individualization/frame route (the `n^{Θ(d)}` → poly win).** The matching/frame route reaches orbits by
*individualization-refinement* and is charged `≈ n^{|T|}`: with the base `|T| = Θ(d)` (the group base — killing `O^ε_d`
needs `d` rigidifying points, information-theoretically), that is `n^{Θ(d)}` = quasipoly. The recovery route does **not**
individualize to discreteness. It lets the descent branch, **recovers the automorphisms by harvest**, and prunes — so the
`Θ(d)` base is the *path length* (poly node count), not an exponent. Same `Θ(d)` base, but harvest pruning turns
`n^{Θ(d)}` into `poly`. This is the mechanism the C# canonizer actually runs, and forms-graph iso is known poly.

**Honest scope — it does NOT sidestep the WL-vs-orbit core (a correction).** The hard part is **relocated, not removed**.
The open content is **`SinglePathDisposition`** = `∀ S`, `SelectedCellIsOrbit` (the selected cell is one `Stab(S)`-orbit) —
the node-count bridge's keyed hypothesis (`ScratchNodeCountBridge`), and the structural form of the probe's `Phase2 = 0`.
This is **strictly weaker than full `CellsAreOrbits`** (one cell vs all) — *possibly more tractable*, and empirically true
(`STARVED = 0`) — **but it is still a WL-vs-orbit statement at partial bases.** So "recovery sidesteps bounded-WL-dim" (an
earlier overclaim) is **false**: it needs a *weaker form* of the same core. The only route that genuinely sidesteps it is
**Route C** (recover `Q` algebraically ⟹ `Aut = GO(Q)` known; §7) — a bigger, behaviour-changing build the user prefers to
avoid. The recovery route's bet, backed by the probe, is that the *weaker* `SinglePathDisposition` holds on the carved
residual families.

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
via the HARVEST (step 3), not the deferral (step 4).** Important consequence (it corrects an earlier framing of this doc):
in default mode the descent **branches but resolves** — `RecoveryReconcileProbe.cs` shows `VO⁻₄(5)` runs
`branchingNodes = 4`, `leaves = 6`, **`branch[resolved] = 4`, `STARVED = 0`**. So the selected cell is *not* always one
orbit there; `SinglePathDisposition` (no branch) describes the **deferral** single-path (`Phase2 = 0`), while the default
canonical-form-preserving path is **branch-but-resolve via the cross-branch harvest**. These are *different bridges* — see §2c.

---

## 2c. The route menu — bridges to poly, and leads to the shared core

A double-check (2026-06-30) found that retargeting onto `SinglePathDisposition` alone silently dropped several real routes.
The accurate structure: **every poly route except Route C reduces to the SAME analytic core** — count-determination
(`RelCountsDetermineOrbit` / `CellsAreOrbits` / the `χ(det G₂)` determiner) — but there are **multiple bridges** from that
core to "poly", and **multiple leads** to attack the core itself. Keep all of them live until one closes.

**Bridges (core ⟹ poly) — pick the most faithful/tractable; all reduce to the core:**
- **Route II — cross-branch harvest (DEFAULT mode, canonical-form-preserving) — the most faithful, best-substrated.**
  `crossBranchHarvest_reproduces_residual` / `autP_reproduced_of_visibleRealizers` (`Cascade.lean`, Part A) reproduce the
  residual group **AND its order** `∏ orbit sizes` from per-level *visible (cell) realizers* — exactly the leaf-collision
  harvest, allowing branch-but-resolve (matches default-mode `STARVED = 0`). Open witness = the visible-realizer hypothesis
  `hreal`, satisfiable via `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` (⟸ the core). The **symmetric** variant
  `coversOrbits_of_realizers_symmetric` needs realizers only at *non-base* prefixes = `RecoversWhileSymmetric`, discharged by
  `recoversWhileSymmetric_of_relCountsDetermineOrbit` (idx 1205). **This was screened out; it is arguably the primary route**
  (no schedule-iso-invariance needed, reproduces order, matches the canonical-form-preserving path).
- **Route I — node-count bridge / deferral single-path.** `certifiedSinglePath_of_disposition` ⟸ `SinglePathDisposition`
  (`ScratchNodeCountBridge`). Models the **deferral** path (`Phase2 = 0`, no branch). Weaker per-base predicate
  (`SelectedCellIsOrbit`), but the deferral changes the canonical form ⟹ also needs the `canonAdj`-transport seam.
- **Route III — full `CellsAreOrbits`.** The strongest predicate (all cells); the demoted route's scaffold reduces it to
  `WallKernelFor Obs`. Discharges I and II for free but asks for more.

**Reusable partial assets (shrink the open part — screened out before):**
- **DRG depth-1 freebie.** The forms graph **is P-polynomial** (diameter-2 SRG: `R:{0,1,2}` bijective onto the 3 relations),
  so `theorem_2_HOR_of_pPolynomial` (`Scheme.lean`) gives `CellsAreOrbits` at base `{v}` (depth 1) **for free**. The WL-dim>1
  failure is only at `|S| ≥ 2`, so the open content is the **deeper** bases; the first descent step is discharged.
- **Depth-graded recovery** `recoverableByDepth_pPolynomial` / the `RecoverableByDepth adj P bound` interface — the recovery
  witness need only hold to a bounded *depth*; combine with the DRG freebie to target only `|S| ∈ [2, O(d)]`.
- **Weakest variant (deferral, `∃` a pure cell):** poly needs only "*some* cell is a single orbit at each base" (not the
  *selected* one) — strictly weaker than `SelectedCellIsOrbit`; my probe's `Phase2 = 0` validates it. Costs schedule-iso-invariance.

**Leads to attack the core itself (count-determination) — beyond the Gauss `χ(det G₂)` determiner:**
- **Gauss / `WallKernelFor Obs`** — the iterated `χ(det G₂)` 2-WL determiner (probed `O(1)`-depth crackable). The analytic spine.
- **Skresanov rank-3 2-closure** — the *group-theoretic* twin: `G^(2)` structure trivialising the 2-closure deficiency at a
  bounded base. An independent angle on the same core (route-doc §9.9.18; `reference_srg_wl_literature_2026-06-17`).
- **δ′ dominator-closure** — `reachesRigidOrCameron_viaDominatorClosure` + `dominatorReachable_affine_step` (`CascadeAffine`):
  a forced-triangle single-base closure (discharged the `H={±1}` and subfield cyclotomic families). A *non-counting* route to
  recovery — check whether the similitude forms-graph closes via forced-triangle uniqueness. **Not yet tried on `VO^ε`.**
- **`EdgeGeneratesFromSet`** — the checkable multi-base isolation closure (`remaining-work.md` §3b): a constructive
  sufficient condition that *produces* the separation certificate. Buildable infra; single-base `EdgeGenerates` exists.

**Dead for THIS residue (note, don't re-walk):** the **block/imprimitive decomposition** route
(`coversOrbits_of_blockDecomposition`, `hfiber/hreach_VisibleRealizers`) is **vacuous** — the forms graph is a *primitive*
rank-3 SRG (no nontrivial blocks). It is `hImprim` territory, not the primitive forms-graph residue.

**Last resort:** **Route C** (recover `Q` algebraically ⟹ `Aut = GO(Q)` known; §7) — the *only* route that avoids the core.
Per user: exhaust Routes I/II/III + the core leads **before** committing to C.

---

## 3. What is already proved (the foundation, all axiom-clean)

Two layers are landed: the **poly spine** (the node-count bridge — the recovery route's own mechanism) and the **seal
infrastructure** (Stage A/B — the correctness disjunction, already banked at quasipoly). The open content lives in the
poly spine (`SinglePathDisposition`); the seal layer is reference/banked.

### 3a′. THE POLY SPINE — the node-count bridge (`ScratchNodeCountBridge`, axiom-clean, NOT in build)
The recovery route's actual mechanism. Reduces "poly node count" to the weak disposition:
- `SelectedCellIsOrbit adj P sel S` — the **selected** cell is one `Stab(S)`-orbit (1-WL `warmRefine`); **strictly weaker
  than `CellsAreOrbits`** (the scheduler only individualizes within the selected cell).
- `SinglePathDisposition = ∀ S, SelectedCellIsOrbit` — *"the structural form of the empirical `Phase2Nodes = 0` /
  single-path finding"* (source comment) = the Lean counterpart of `RecoveryReconcileProbe.cs`.
- `certifiedSinglePath_of_disposition` — disposition ⟹ `CertifiedSinglePath` (`boundedNodes ≤ n` + `cellsCertified`: every
  consumed cell is a single residual orbit). The two poly ingredients, bundled.
- `singlePathDisposition_of_cellsAreOrbits` / `selectedCellIsOrbit_of_cellsAreOrbits` — full `CellsAreOrbits` discharges
  the disposition for free (the "go through the strong predicate" angle).
- **Residual (Increment-0):** the `canonAdj`-transport seam — representative-choice invariance of the leaf canonical (the
  analogue of `spine_branch_independent` across rep-choice). Depth-1 core landed; the meta poly-argument consumes it.

### 3a. The conditional capstones (the SEAL layer — banked at quasipoly; reference)
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

## 4. The open core, precisely — `SelectedCellIsOrbit`, and the `O(Q)` vs `VO^ε` gap

**The open core (poly).**

> **`SinglePathDisposition` = `∀ S, SelectedCellIsOrbit Q S`.** At every partial base `S`, the descent's **selected cell**
> (the lowest-colour non-singleton 1-WL cell — a *relative sphere*) equals a single `Stab(S)`-orbit. Empirically:
> `STARVED = Phase2 = 0` on `VO^ε_4(q)` (`RecoveryReconcileProbe.cs`). **Weaker** than `CellsAreOrbits` (one cell, not all).

This is **not** a bounded-base seal predicate (those — `RelCountsDetermineOrbit` / `IsotropySeparatesAtBase` — feed the
*seal*, banked at quasipoly). It is the **poly** obligation, keyed by `ScratchNodeCountBridge`.

**The gap that makes it non-trivial (plan §1 item 1, ROUTE-A DEEP-SCOPE).** `SelectedCellIsOrbit` asks that the selected
relative sphere is a single orbit. Stage B.0's clean "orbit-of-difference ⟹ exact `Q(v−t)` ⟹ `coords_determine`" mechanism
would settle it — but it works only on the **isometry** scheme `O(Q)`. The descent runs on the coarser **similitude SRG**
(relation = `isoClass` ∈ {0, isotropic, anisotropic}, *not* the exact `Q`-value), so collapsing the relative sphere to a
single orbit there is a genuine **count-determination** (the isotropy counts must *determine* the orbit within the sphere,
not merely separate vertices). Two ways to discharge it:
- **(a) directly on the sphere** — prove `SelectedCellIsOrbit` for the *specific* selected cell (a structured relative
  sphere; `Probe_RouteA_PartialBaseSpheres` found it clean — depth-1 = neighbour sphere = valency, free by rank-3/schurian).
  Exploits the weakening; *possibly easier* than full `CellsAreOrbits`.
- **(b) through full `CellsAreOrbits`** — `selectedCellIsOrbit_of_cellsAreOrbits`; reuses the demoted route's scaffold
  (`ScratchWallKernel` etc.) and the `χ(det G₂)` 2-WL determination.

**Crackability evidence (the demoted route's probes, still valid).** `wall_*.py` found the iterated `χ(det G₂)` 2-WL
observable **determines** the orbit at a bounded anisotropic base with `O(1)` iteration depth, uniformly in `d, |S|, q,`
type — so the count-determination is a *bounded* number of character rounds, not an unbounded fixpoint. (That probe is the
*2-WL* observable; the descent is 1-WL + harvest. The probe shows the *information* is present at a bounded base; the harvest
extracts it — at least as strong as the relation-count profile — which is why `STARVED = 0`.)

**Aside — the seal's own bounded-base tightening (optional, separate).** If one *also* wants to tighten the banked
quasipoly *seal* to a bounded base, that is `IsotropySeparatesAtBase` as a *determiner* (not the per-anchor `c0_le_threequarters`
+ matching *separator*, which structurally needs `Θ(log n)` anchors). It gives a fixed-`d`-poly / quasipoly-for-growing-`d`
seal — a different, weaker-payoff deliverable than the harvest poly above. Not the live target.

---

## 5. The C# ↔ Lean bridge (the empirical validation)

The route is implementation-faithful because its open Lean core **is named in the source as the structural form of the
counter the probe measures** — `ScratchNodeCountBridge` defines `SinglePathDisposition` as *"the structural form of the
empirical `Phase2Nodes = 0` / single-path finding."* The correspondence is therefore concrete, not asserted:

| C# (`CanonResult.cs` / `ChainDescent.cs`) | Lean (`ScratchNodeCountBridge`) | meaning |
|---|---|---|
| `Phase2Nodes = 0` / single-orbit cell consumed | `SinglePathDisposition` (= ∀ S, `SelectedCellIsOrbit`) | the open core: the selected cell is one orbit at every base |
| `ClassifyStarved` / `BranchStarved` = 0 | `cellsCertified` (consumed cell = single `StabilizerAt`-orbit) | harvest completeness: no real branch survives |
| `LeafCount` (poly) / single path | `boundedNodes` (`≤ n`) → poly node count | the descent tree is poly |
| `GeneratorsHarvested`, `ResolvedByRecursion` | `StabilizerAt` orbit + `covered_sound` | a-posteriori orbit recovery (the prune) |

**Empirical validation (`RecoveryReconcileProbe.cs`, 2026-06-30, the REAL canonizer on `VO^ε_4(q)` q=3,5):**
- `ClassifyStarved = BranchStarved = 0` in **every** case, **both** modes; **no flag, full `|Aut|` recovered**. ⟹ harvest
  empirically complete = `SinglePathDisposition` HOLDS on the family.
- `Phase2 = 0` everywhere (deferral always finds a single-orbit cell). The earlier `descent_probe.py` `Phase2 = 1` was a
  greedy-replication artifact — there is **no genuine rigid residue with no orbit-pure cell**.
- Default mode may *branch-but-resolve* (`VO⁻₄(5)`: 4 resolved branches, leaves=6, STARVED=0); deferral gives the true
  single path (leaves=1). Both modes complete.
- **d-scaling CONFIRMED at d=6:** `VO⁻₆(3)` n=729 → CANON, leaves=1, `STARVED=0`, `Phase2=0`, **full `|Aut|=38093690880`
  recovered**. So the harvest stays complete and single-path as the dimension grows (d=4→6) — the open residue is *unbounded*
  `d`, and there is no sign of starvation appearing with `d`. (`VO⁻₄(7)` n=2401 dropped as infeasible wall-clock.)

The remaining seam (Increment-0 residual, `ScratchNodeCountBridge`): the **`canonAdj`-transport** — that a `CertifiedSinglePath`
computes the iso-invariant canonical (rep-choice invariance). Depth-1 core landed; it is plumbing the *meta* poly-argument
consumes, not the research core.

---

## 6. Work-forward plan (ordered)

1. **★ LIVE — the two tracks (see the §2c menu; do not collapse to one).** The poly deliverable splits into a **CORE**
   (shared by all routes) and a **BRIDGE** (pick the most faithful).
   - **CORE — discharge count-determination.** The analytic spine = the `χ(det G₂)` determiner (`WallKernelFor Obs`), same
     Gauss machinery as the seal (`pairCharSum_factor_gen` / `gaussSum_sq_ne_zero` / `χ(det G₂) ↔ Z_u`); probed `O(1)`-depth
     crackable. **Run the untried leads in parallel before assuming this is the only handle:** (α) **δ′ dominator-closure**
     (`dominatorReachable_affine_step` — a *non-counting* forced-triangle route, never tried on `VO^ε`); (β) **Skresanov
     2-closure** (group-theoretic); (γ) **`EdgeGeneratesFromSet`** (constructive certificate). The DRG freebie discharges
     depth 1, so the core is open only at `|S| ≥ 2`.
   - **BRIDGE — core ⟹ poly.** Prefer **Route II** (`crossBranchHarvest_reproduces_residual`, default-mode, reproduces
     group + order, no schedule-iso cost). Alternatives: Route I (`SinglePathDisposition`/deferral, `ScratchNodeCountBridge`),
     Route III (full `CellsAreOrbits`). All wire at `affineScheme`, exposing the core as the single open input.
   **Fallback:** if the determiner is non-singular only for large `q`, that is still a real poly sub-family result; a genuine
   obstruction across **all** core leads (α/β/γ + Gauss) is the signal to consider Route C (§7) — not before.
   > **★ BUILD MAP (scoping, 2026-06-30) — three pieces, with a model-translation seam.** Angle (b) is NOT a one-liner:
   > the scaffold and the bridge live in **different models** that must be connected:
   > - **(i) the open core** — `WallKernelFor Obs` for `Obs` = the iterated `χ(det G₂)` 2-WL (the bounded-depth
   >   count-determination). The observable is **not yet defined in Lean** (only probed in `wall_*.py`); defining it +
   >   proving its similitude-invariant **soundness** (`StabOrbit ⟹ Obs`, free from `isoClass_similitude_invariant` /
   >   `chi_pairForm_smul`) is the natural **first brick**, then the hard *determiner* direction.
   > - **(ii) the model seam** — `ScratchWallKernel`/`ScratchOrbitBaseCase` prove `CellsAreOrbits` in the **vector-space
   >   model** (`StabOrbit Q S` on `V = K^d`, `SameExactGram`); `ScratchNodeCountBridge` needs `SelectedCellIsOrbit` in the
   >   **canonizer model** (`OrbitPartition adj P S` on `Fin n`, `warmRefine`). Connecting them = the `affineScheme`/`schemeAdj`
   >   instantiation (`affineE : Fin (p^d) ≃ V`) + the bridge's own `repTransport`/`baseTransport` seam. Real infrastructure,
   >   not new math.
   > - **(iii) Witt** — tech debt (§6 — the demoted doc's W0–W4); carried until close-out.
   > **Realistic first session:** piece (i) brick 1 (define the observable + soundness) OR piece (ii) (wire the two models at
   > `affineScheme`, exposing `WallKernelFor Obs` as the single open input end-to-end). Either is a self-contained,
   > axiom-clean landing; the hard determiner (i, brick 2) is the multi-session research core.
2. **The `canonAdj`-transport seam (Increment-0 residual).** Rep-choice invariance of the leaf canonical (the meta
   poly-argument's missing plumbing). Depth-1 core landed in `ScratchNodeCountBridge`; finish it.
3. **d-scaling confirmation — ✅ DONE at d=6** (`RecoveryReconcileProbe.Reconcile_dScaling`, `VO⁻₆(3)` n=729: CANON,
   `STARVED=0`, full `|Aut|` recovered). The harvest stays complete as `d` grows; no starvation appeared. (Larger `d` is
   wall-clock-infeasible in pure C#; d=4→6 is the available evidence. Re-run if a cheaper harness becomes available.)
4. **Per-node + node-count poly (the complexity argument).** `boundedNodes ≤ n` is landed; per-node hard-poly is the code
   analysis (loops `n`-bounded). Either formalize a Lean cost statement or keep "poly" meta and deliver the structural
   `CertifiedSinglePath` (the project's standing convention — "poly" is never formalized). Decide with the user.
5. **Other families (Layer C).** Once affine-polar lands: alternating / half-spin reuse the field-generic skeleton; char-2 +
   Suzuki are a separate bespoke track (Arf + additive trace, Mathlib substrate absent). Plan §11.4–§11.5.
6. **PORT.** Move `ScratchNodeCountBridge` (+ any new modules) into `build.sh` + `lakefile` + `PublicTheoremIndex.md` once
   the core lands (mechanical, no math).

*(The SEAL is banked at quasipoly — `reachesRigidOrCameron_affinePolar`. Tightening the seal to a bounded base via
`IsotropySeparatesAtBase`-as-determiner is a separate, weaker-payoff option, NOT this route's live target.)*

**Definition of done (recovery route, affine-polar):** `SinglePathDisposition` proved for the family ⟹
`certifiedSinglePath_of_disposition` gives `CertifiedSinglePath` (bounded nodes + every consumed cell one orbit) ⟹ the
`canonAdj`-transport seam closes ⟹ the structural poly object is complete; the C# completeness (`STARVED = Phase2 = 0`) is
the empirical witness. The SEAL is separately banked (`reachesRigidOrCameron_affinePolar`, quasipoly). "Poly" remains the
meta-claim over the bounded node count + poly per-node.

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
  `lake env lean ChainDescent.ScratchNodeCountBridge` for the poly spine; `lake env lean ChainDescent.CascadeAffine` for the
  banked seal capstones).
- **Live Lean endpoint (POLY):** `SinglePathDisposition` / `SelectedCellIsOrbit` + `certifiedSinglePath_of_disposition`
  (`ChainDescent.NodeCountBridge`, `ScratchNodeCountBridge.lean`) — the open input is `SelectedCellIsOrbit Q S` on the family.
- **SEAL endpoints (banked at quasipoly; reference):** `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248,
  input `IsotropySeparatesAtBase Q T` idx 1240) and the abstract twin `reachesRigidOrCameron_viaAffineFormScheme` (idx 1207,
  input `RelCountsDetermineOrbit` idx 1203). The in-build seal is `AffinePolarSeal.reachesRigidOrCameron_affinePolar`.
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
