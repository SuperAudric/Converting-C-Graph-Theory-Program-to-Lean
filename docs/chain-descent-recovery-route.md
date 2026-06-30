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

> **════════ PICK-UP (2026-06-30, v2 — RETARGETED to the weakest predicate) — READ THIS FIRST ════════**
>
> **What this route is, in one line.** Prove the *existing* canonizer runs in poly time on the forms-graph residue by
> bounding its **leaf count** — NOT by proving cells = orbits. This targets the **mathematically weakest** sufficient
> condition, which is exactly what the C# default mode satisfies. (An earlier version of this doc drifted onto
> `CellsAreOrbits` / cross-branch-harvest predicates that secretly require cells = orbits — a *stronger*, harder,
> likely-only-quasipoly target. Those are now relocated; see "Relocated" below and §2c.)
>
> **Empirical anchor.** `RecoveryReconcileProbe.cs`: the canonizer canonizes `VO^ε_4(q)` (q=3,5) with **no flag, full
> `|Aut|`, `STARVED = 0`** — but in **default (canonical-form-preserving) mode it BRANCHES and resolves**: `VO⁻₄(5)` runs
> `branchingNodes = 4`, `leaves = 6`. So cells ≠ orbits there; the cost stays poly because the **leaf count is small**, not
> because the descent is a single path. That is the target to formalize.
>
> **Two deliverables — keep separate.**
> - **SEAL** (`reachesRigidOrCameron` modulo `{G3}` — *correctness*): **already BANKED at quasipoly**
>   (`AffinePolarSeal.reachesRigidOrCameron_affinePolar`). Not this route's job.
> - **POLY** (the *cost* claim — this route): cost ≈ `#leaves × depth × per-node`. Depth `= O(d)` and per-node hard-poly are
>   ~landed; the open content is **poly leaf count**.
>
> **THE OPEN TARGET — poly leaf count (the weakest sufficient condition).**
> `leaves = ∏ᵢ bᵢ`, where `bᵢ = #{Stab(Sᵢ)-orbits in the selected cell at level i}`. **`CellsAreOrbits` is the special
> case `bᵢ = 1 ∀i` (single path) — strictly STRONGER and not needed.** The weak target only needs the *product* bounded.
> The arithmetic that makes it reachable: `∏bᵢ ≤ Bᴸ` with `L = O(d)`, and since `n = q^d`, **`B ≤ poly(q) ⟹ Bᴸ = q^{O(d)} =
> poly(n)`**. And `bᵢ ≤ q` is structurally plausible — individualizing one point refines a cell by **one** new Gram
> coordinate (`≤ q` values), so the selected cell splits into `≤ q` orbits, **uniformly in `d`**. THAT uniform-in-`d`
> `bᵢ ≤ poly(q)` is the crux, and it is far weaker than `CellsAreOrbits`.
>
> **LIVE NEXT TASK — Phase 0 (GATE), then the bridge.** (1) **Phase 0 (empirical, do first):** extend the descent probe to
> report `leaves`, depth, and per-level `bᵢ` for `VO^ε` as `d` grows (d=4,6,8); confirm leaves poly and pin `B`'s form
> (`bᵢ ≤ q`? `≤ O(1)`?). Gates the whole target and reveals the exact predicate. (2) **Phase 1 (Lean bridge):** generalize
> `ScratchNodeCountBridge` from `SinglePathDisposition` (`B=1`) to **`BoundedBranchingDisposition`** (`bᵢ ≤ B`) ⟹
> `leaves ≤ Bᴸ` ⟹ poly. Then Phase 2 discharges `bᵢ ≤ poly(q)` for the forms graph (DRG freebie gives `b₁ = 1`). Full plan: §6.
>
> **Relocated (stronger target — valid but harder, likely quasipoly-adjacent; → CellsAreOrbits doc / §2c):** full
> `CellsAreOrbits` + the `WallKernelFor Obs` determiner (the demoted route); and **Route II
> `crossBranchHarvest_reproduces_residual`**, whose hypothesis `hreal` *provably requires* cells = orbits
> (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`) — it is the **|Aut|-computation** deliverable, a *different,
> stronger* goal than poly leaf count. Do not put them on the poly-leaf-count critical path.
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
IR tree (00-START-HERE §1). Polynomial = three factors:

1. **Poly leaf count — `leaves = ∏ᵢ bᵢ ≤ poly(n)`**, where `bᵢ = #{Stab(Sᵢ)-orbits in the selected cell at level i}`.
   The descent **branches** over the orbits of the selected cell (within-orbit siblings pruned by harvest,
   `CoveredByPathFixingAut`); cross-orbit branches are genuine and compared. **This is the open content** (§4, §6). It is
   *not* "single path": default mode branches (`VO⁻₄(5)`: `leaves = 6`).
2. **Poly depth — `L = O(d)`** (the group base; `d ≤ log₂ n`). ~landed (`defaultSpineChain_reaches_leaf ≤ n`).
3. **Poly per-node.** Every harvest loop in `ChainDescent.cs` is `n`-bounded; no exponential mechanism (plan §1 item 1
   "RESOLVED"). Hard poly ceiling (≈ `n⁵–n⁶`).

**Why poly leaf count is reachable (the arithmetic).** `∏ᵢ bᵢ ≤ Bᴸ` with `B = maxᵢ bᵢ`, `L = O(d)`. Since `n = q^d`,
**`B ≤ poly(q) ⟹ Bᴸ = q^{O(d)} = poly(n)`.** Plausibly `bᵢ ≤ q`: individualizing one point refines a cell by **one** new
Gram coordinate (`≤ q` values), so the selected cell splits into `≤ q` orbits — **uniformly in `d`**. That uniform-in-`d`
bound is what the `n^{Θ(d)}` individualization/frame route (base `Θ(d)`, charged `n^{Θ(d)}`) cannot get; the harvest's
orbit-pruning replaces the `n`-way fork at each level by a `≤ q`-way fork, and `q^{O(d)} = poly(n)`.

**Honest scope — strictly weaker than `CellsAreOrbits`, but NOT a sidestep of the WL-vs-orbit axis.** The open content is
**bounded branching** (`bᵢ ≤ poly(q)`), of which `CellsAreOrbits` (`bᵢ = 1 ∀ cells`) is the much stronger special case. So
the recovery route asks for *genuinely less* than the demoted CellsAreOrbits route — but it is still a statement *about*
the orbit-vs-cell relation (it bounds, rather than collapses, the defect). The only route that avoids that axis entirely is
**Route C** (recover `Q` ⟹ `Aut = GO(Q)` known; §7) — bigger, behaviour-changing, the user's last resort. The recovery
route's bet, backed by the probe (`STARVED = 0`, `leaves` small): bounded branching holds on the carved residual families.

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

### 2b. How the canonizer stays poly — a small branch-but-resolve tree (verified against `GraphCanonizationProject/`)
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

## 2c. The target predicate, and the strength ladder (do not drift upward)

**The live target is the WEAKEST sufficient condition: bounded branching ⟹ poly leaf count.** Everything stronger is
relocated. The strength ladder, weakest → strongest:

| # | predicate | what it gives | who needs it | landed substrate |
|---|---|---|---|---|
| **★ T0** | **bounded branching `bᵢ ≤ poly(q)`** (selected cell has `≤ poly(q)` orbits) | **poly leaf count `∏bᵢ = poly(n)`** — branch-but-resolve | **default mode** (`STARVED=0`, `leaves` small) | **none yet — Phase 1 builds it** (generalize `ScratchNodeCountBridge`) |
| T1 | `∃` a pure cell at each base | single path **via deferral** | deferral mode (`Phase2=0`) | `SelectedCellIsOrbit` parametric in `sel` (the "pick a pure cell" part unbuilt) |
| T2 | `SinglePathDisposition` (the *selected* cell is one orbit) | single path | a *fixed-selector* deferral | `certifiedSinglePath_of_disposition` (`ScratchNodeCountBridge`) — the `B=1` corner of T0 |
| T3 | full `CellsAreOrbits` (∀ cells = orbits) | single path, **+ reproduces |Aut|** | — (false at 1-WL, `|S|≥2`) | `WallKernelFor Obs`; Route II `hreal` |

**Why T0 is the right target.** `T0` is the only rung the C# *default, canonical-form-preserving* mode actually satisfies
(it branches; `T1–T3` all assert no branching). And `T0` is **strictly weaker** than `T3`: it bounds the orbit-vs-cell
defect rather than collapsing it. `T0 → poly` is pure arithmetic (`∏bᵢ ≤ Bᴸ = q^{O(d)} = poly(n)`), so the only *math* is
the structural bound `bᵢ ≤ poly(q)` (§4, §6 Phase 2).

**RELOCATED — the stronger rungs (valid, but harder; likely only quasipoly-adjacent in difficulty):**
- **`T3` full `CellsAreOrbits` + the `WallKernelFor Obs` determiner** → the demoted CellsAreOrbits route
  ([`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md)). Independent-math value (WL-dim 2),
  **not** on the poly-leaf-count critical path.
- **Route II `crossBranchHarvest_reproduces_residual` / `autP_reproduced_of_visibleRealizers`** (Part A): reproduces the
  residual group **and order**, but its hypothesis `hreal` *provably requires* `CellsAreOrbits`
  (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`) — so it is the **|Aut|-COMPUTATION** deliverable (a *different,
  stronger* goal than canonical-form poly), kept as a reference, not a leaf-count bridge.

**Reusable partial assets (shrink T0's open part):**
- **DRG depth-1 freebie.** The forms graph **is P-polynomial** (diameter-2 SRG), so `theorem_2_HOR_of_pPolynomial`
  (`Scheme.lean`) gives `CellsAreOrbits` at base `{v}` for free ⟹ `b₁ = 1`; the open content is `bᵢ` at `|S| ≥ 2`.
- **Depth-graded recovery** (`RecoverableByDepth`) — the within-orbit pruning (D4) holds to bounded depth.

**Untried leads on `bᵢ ≤ poly(q)` / orbit recovery (run before concluding it's hard):**
- **δ′ dominator-closure** (`dominatorReachable_affine_step`, `CascadeAffine`) — a *non-counting* forced-triangle route
  (closed the `H={±1}`/subfield cyclotomic families). **Never tried on `VO^ε`.** If it bounds the per-cell orbit split it
  feeds T0 directly, no Gauss.
- **Skresanov rank-3 2-closure** — the group-theoretic bound on the orbit-vs-cell defect.
- **`EdgeGeneratesFromSet`** — constructive certificate (`remaining-work.md` §3b).
- **Gauss `χ(det G₂)`** — the analytic determiner; note this proves the *stronger* `bᵢ = 1`, so it overshoots T0 (use only if T0's weaker bound is not separately reachable).

**Dead for THIS residue:** block/imprimitive decomposition (`coversOrbits_of_blockDecomposition`) — vacuous (forms graph is a
*primitive* rank-3 SRG). **Last resort:** Route C (§7); per user, exhaust T0 + the leads first.

---

## 3. What is already proved (the foundation, all axiom-clean)

Two layers are landed: the **poly spine** (the node-count bridge — the recovery route's mechanism, currently at the `B=1`
corner) and the **seal infrastructure** (Stage A/B — the correctness disjunction, already banked at quasipoly). The open
content is the **T0 bounded-branching** generalization of the spine (Phase 1) + its forms-graph discharge (Phase 2); the
seal layer is reference/banked.

### 3a′. THE POLY SPINE — the node-count bridge (`ScratchNodeCountBridge`, axiom-clean, NOT in build)
The recovery route's mechanism. **Currently landed at the `B=1` (single-path) corner; Phase 1 generalizes it to T0
(bounded-branching `B`).** What exists:
- `SelectedCellIsOrbit adj P sel S` — the **selected** cell is one `Stab(S)`-orbit (the `B=1` per-base condition).
- `SinglePathDisposition = ∀ S, SelectedCellIsOrbit` (= ladder rung **T2**; the structural form of `Phase2=0`, deferral mode).
- `certifiedSinglePath_of_disposition` — ⟹ `CertifiedSinglePath` (`boundedNodes ≤ n` + every consumed cell one orbit).
- `singlePathDisposition_of_cellsAreOrbits` / `selectedCellIsOrbit_of_cellsAreOrbits` — full `CellsAreOrbits` (T3) discharges
  it (the "go through the strong predicate", overshoot angle).
- **Residual (Increment-0):** the `canonAdj`-transport seam — rep-choice invariance of the leaf canonical (analogue of
  `spine_branch_independent`). Depth-1 core landed.

**Phase 1 builds on top:** `BoundedBranchingDisposition` (`bᵢ ≤ B`) + `certifiedBoundedTree_of_disposition`
(`leaves ≤ Bᴸ`) — the **T0** generalization that captures the C# default mode (branch-but-resolve). `certifiedSinglePath_*`
is its `B=1` special case.

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

## 4. The open core, precisely — T0 = bounded branching `bᵢ ≤ poly(q)`

**The open core (poly).**

> **T0 (bounded branching).** At every partial base `Sᵢ` on the descent path, the **selected cell** (a *relative sphere*)
> splits into `bᵢ ≤ poly(q)` `Stab(Sᵢ)`-orbits — a bound **uniform in `d`**. Then `leaves = ∏ᵢ bᵢ ≤ q^{O(d)} = poly(n)`.

This is the **poly** obligation (the node-count bridge's hypothesis), **NOT** a seal predicate (`RelCountsDetermineOrbit` /
`IsotropySeparatesAtBase` feed the *seal*, banked). It is **strictly weaker** than `CellsAreOrbits` (`bᵢ = 1 ∀ cells`).

**Why even the weak per-cell bound is non-trivial (the `O(Q)` vs `VO^ε` gap).** The descent runs on the **similitude SRG**
(relation = `isoClass` ∈ {0, isotropic, anisotropic}, *not* the exact `Q`-value). Stage B.0's clean "orbit-of-difference ⟹
exact `Q(v−t)`" mechanism works only on the finer **isometry** scheme `O(Q)` — there `bᵢ = 1` outright. On the coarser
similitude SRG, a cell can hold several orbits (the isotropy class doesn't pin the exact Gram), so `bᵢ > 1` is real and
must be *bounded*. **Crucial point: T0 only asks `bᵢ ≤ poly(q)`, not `bᵢ = 1`** — so the *full* count-determination (which
gives `bᵢ = 1` and is the demoted CellsAreOrbits route) is an **overshoot**. The handles:
- **structural / one-new-coordinate** — individualizing one point adds one Gram coordinate (`≤ q` values) ⟹ `bᵢ ≤ q`. The
  natural direct argument; needs no Gauss.
- **untried non-counting leads** — δ′ dominator-closure (`dominatorReachable_affine_step`), Skresanov 2-closure,
  `EdgeGeneratesFromSet` (§2c). These could bound `bᵢ` without the analytic machinery.
- **DRG freebie** — `b₁ = 1` free (forms graph P-polynomial).
- **(overshoot, reserve)** the `χ(det G₂)` determiner (`WallKernelFor`, demoted route) — proves the stronger `bᵢ = 1`.

**Empirical anchor (Phase 0 will sharpen).** `RecoveryReconcileProbe.cs`: `STARVED = 0`, `leaves = 6` for `VO⁻₄(5)`, and
`VO⁻₆(3)` (d=6) canonizes with `STARVED = 0`, full `|Aut|` — completeness holds as `d` grows. **What's unmeasured (Phase 0):**
the per-level `bᵢ` and the `leaves`-vs-`d` growth — i.e. whether `bᵢ ≤ poly(q)` actually holds uniformly. That is the gate.

**Aside — the seal's own bounded-base tightening (optional, separate).** Tightening the *seal* (not poly leaf count) to a
bounded base is `IsotropySeparatesAtBase`-as-determiner — a fixed-`d`-poly / quasipoly deliverable, different from and
weaker-payoff than the harvest poly. Not the T0 target.

---

## 5. The C# ↔ Lean bridge (the empirical validation)

The route is implementation-faithful: the open Lean target (T0) is exactly what the canonizer's counters measure. The
correspondence (T0's `BoundedBranchingDisposition` is *Phase 1* — not yet in source; `SinglePathDisposition`/T2 is the landed
`B=1` corner):

| C# (`CanonResult.cs` / `ChainDescent.cs`) | Lean | meaning |
|---|---|---|
| `LeafCount` poly, `branchingNodes` bounded | **T0 `BoundedBranchingDisposition`** (`bᵢ ≤ B`) → `leaves ≤ Bᴸ` | **the open target** — poly leaf count (default mode branches) |
| `ClassifyStarved` / `BranchStarved` = 0 | **D4** within-orbit pruning (no stuck residue) | branching is by *orbit*, not by rep |
| `Phase2Nodes = 0` (deferral) | rung **T1/T2** (`SinglePathDisposition`) | the *deferral* single-path corner (`B=1`) |
| `GeneratorsHarvested`, `ResolvedByRecursion` | `StabilizerAt` orbit + `covered_sound` | a-posteriori orbit recovery (the prune) |

**Empirical validation (`RecoveryReconcileProbe.cs`, 2026-06-30, the REAL canonizer):**
- `ClassifyStarved = BranchStarved = 0` in **every** case, **both** modes; no flag, full `|Aut|` recovered ⟹ **D4 holds**
  (within-orbit recovery complete; the descent never gets stuck).
- **Default mode (T0-relevant):** `VO⁻₄(5)` *branches* — `branchingNodes=4`, `leaves=6`. So `bᵢ > 1` occurs; T0 ≠ single path.
- **Deferral mode:** `Phase2=0`, `leaves=1` (incl. `VO⁻₆(3)` d=6, full `|Aut|=38093690880`) — the T1/T2 corner.
- **What Phase 0 must still measure:** per-level `bᵢ` and `leaves`-vs-`d` in **default mode** — i.e. whether `bᵢ ≤ poly(q)`
  uniformly (the T0 bound). `STARVED=0` confirms D4/completeness, **not** the leaf-count bound.

The remaining seam (Increment-0, `ScratchNodeCountBridge`): the **`canonAdj`-transport** — rep-choice invariance of the leaf
canonical. Depth-1 core landed; meta-plumbing, not the research core.

---

## 6. Plan of attack (phased) — target T0, poly leaf count

The deliverable = poly leaf count `∏ᵢ bᵢ ≤ poly(n)` (§4). Decomposition: **D1** depth `L=O(d)` (~landed) · **D2** per-level
`bᵢ ≤ poly(q)` (the open math) · **D3** `∏bᵢ ≤ Bᴸ = poly(n)` (arithmetic) · **D4** within-orbit pruning (recovery) · **D5**
lex-min = canonical (~landed + `canonAdj` seam).

**Phase 0 — GATE (empirical; do first).** Extend `RecoveryReconcileProbe.cs` to report, for `VO^ε_{2m}(q)` as `d = 4,6,8`
grows: the **leaf count**, the **depth `L`**, and the **per-level selected-cell orbit count `bᵢ`** (the new measurement —
current probe reports aggregate `leaves`/`branchingNodes`, not per-level `bᵢ`). Outcomes:
- **Confirm `leaves` is poly** and **pin `B`'s form** (`bᵢ ≤ q`? `≤ O(1)`? grows?). This *is* the D2 predicate to formalize.
- **Gate:** if `leaves` grows super-poly at `d=6,8`, T0 fails on this family — learn it cheaply, before any Lean. *(d=6
  `VO⁻₆(3)` already canonizes with `STARVED=0`, full `|Aut|` — completeness holds; leaf-count/`bᵢ` scaling is what's unmeasured.)*

**Phase 1 — the bridge (Lean; generalize `ScratchNodeCountBridge`).** Build **`BoundedBranchingDisposition adj P sel B`**
(the selected cell has `≤ B` `Stab(S)`-orbits at every base) and **`certifiedBoundedTree_of_disposition`**: `bᵢ ≤ B` + depth
`L` ⟹ leaf count `≤ Bᴸ` ⟹ the poly node-count object. `certifiedSinglePath_of_disposition` is the `B=1` corner. Self-contained,
axiom-clean; **does not need the forms graph** — pure tree combinatorics. **The cleanest first Lean landing.**

**Phase 2 — discharge D2 for the forms graph (Lean; the open math).** Prove `bᵢ ≤ poly(q)` (the form Phase 0 pins). The
structural handle: individualizing one point refines a cell by **one new Gram coordinate** (`≤ q` values), so the selected
cell splits `≤ q` ways. DRG freebie gives `b₁ = 1`. **Untried non-Gauss leads to try here first** (they target the *weak* `bᵢ`
bound, not the strong `bᵢ=1`): **δ′ dominator-closure** (`dominatorReachable_affine_step`, never tried on `VO^ε`),
**Skresanov 2-closure**, **`EdgeGeneratesFromSet`**. Gauss `χ(det G₂)` proves the *stronger* `bᵢ=1` — overshoots T0; reserve it.

**Phase 3 — D4 within-orbit recovery.** Same-orbit siblings are pruned (the harvest finds the map). The orbit-existence is
the *free* direction; reuse `RecoverableByDepth` / the harvest substrate. (This is where the landed Part A machinery is
genuinely useful — for *pruning*, not for the leaf-count bound.)

**Phase 4 — assembly + the `canonAdj`-transport seam + meta-poly.** Rep-choice invariance of the leaf canonical (depth-1 core
landed in `ScratchNodeCountBridge`); assemble D1–D5; "poly" stays the meta-claim over the structural `CertifiedBoundedTree`.

**Later — other families (Layer C):** alternating / half-spin reuse the skeleton; char-2 + Suzuki bespoke. **PORT** at the end.

*(The SEAL is banked at quasipoly — `reachesRigidOrCameron_affinePolar`. Stronger rungs T1–T3 / `WallKernelFor` / Route II
are relocated (§2c) — valid but harder, likely quasipoly-adjacent; not the T0 critical path.)*

**Definition of done (recovery route, affine-polar):** `BoundedBranchingDisposition` (with `B = poly(q)`) proved for the
family ⟹ `certifiedBoundedTree_of_disposition` gives the poly leaf-count object ⟹ the `canonAdj` seam closes ⟹ structural poly
object complete; the C# `STARVED = 0` + small `leaves` is the empirical witness.
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

- **★ FRESH READER — PICK UP HERE.** Read this STATUS + §1 (the cost model) + §2c (the strength ladder — target T0) + §4
  (T0, the open core) + §6 (the phased plan). Then verify the landed substrate (`lake env lean ChainDescent.ScratchNodeCountBridge`
  for the poly spine's `B=1` corner; `bash scripts/build.sh` for the in-build banked seal).
- **Live Lean target (POLY, T0):** **Phase 0** (extend `RecoveryReconcileProbe.cs` to report per-level `bᵢ` + `leaves`-vs-`d`),
  then **Phase 1** = `BoundedBranchingDisposition` + `certifiedBoundedTree_of_disposition` (generalize `ScratchNodeCountBridge`,
  whose `B=1` corner `certifiedSinglePath_of_disposition` is landed). Open math = `bᵢ ≤ poly(q)` (Phase 2).
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
