# Archived scratch modules — closed / refuted / superseded research

These 45 `Scratch*.lean` modules were moved out of `ChainDescent/` on **2026-07-08** to declutter the
active scratch layer. They are **dormant**: not in `scripts/build.sh`, not in `lakefile.toml` `defaultTargets`,
and not imported by any live module. Their internal `import ChainDescent.Scratch*` paths are now stale (the
imported files moved here too); this is a **snapshot for the record**, not a buildable target — like `Archive/V4/`.

**Why keep them instead of deleting?** In this project dead leads keep resurfacing, and re-walking a closed
route is the dominant time-sink. Each cluster below records *how it failed*, so a future session recognizes the
wall before rebuilding toward it. Cross-check the authoritative dead-route record in
`docs/Archive/ChainDescent/chain-descent-steers-archive.md` and `docs/chain-descent-recovery-route.md` §9.8.

**Nothing here was hard-deleted; all are git-tracked.** Group 1 is tagged *purge-safe* (superseded by a named
build module) — verify the named capstone re-proves the increment, then delete from the archive if wanted.

---

## Group 1 — Forms-graph pair-route increments (SUPERSEDED by named build modules; **purge-safe once diff-verified**)

The shipped affine-polar seal lives in the named modules `PairForm` / `PencilTBound` / `PerAnchorBound` /
`BadAnchorCount` / `Coordinatization` / `IsotropicIncidenceCount` / `ProfileReduction` / `AffinePolarSeal`
(build.sh L68–81). These are *later* increments (post the 2026-06-28 restructure) whose results should be in
those modules — but they are increments, not the literal originals, so **diff the named capstone before purging.**

- `ScratchBM3Bridge`, `ScratchBM3Glue` — the `VO⁻₄(3)` minus-form instance seal (`vo4minus_seal`). Lemma-A/B
  substrate ported to `IsotropicIncidenceCount` / `ProfileReduction`; the single instance is subsumed by the
  general `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (all q=p, incl. q=3 minus-form). *(00-START-HERE
  still calls the instance "not yet ported" — that line is stale; the general seal supersedes it.)*
- `ScratchPencilBridge`, `ScratchPencilCorank`, `ScratchPencilCorank2`, `ScratchPencilRegroup` — pencil radical
  / corank increments → `PencilTBound` ("was Corank+…+TBound").
- `ScratchTBoundCorank`, `ScratchTBoundCorank2` — q-floor corank tightening (#1: q≳d²→q≥256; small-q corank2).
- `ScratchRoute2`, `ScratchRoute2Arith`, `ScratchCountTight` — small-q "Route 2" per-anchor `c₀<1` with no
  q-threshold (`c0_le_route2`). ⚠ **The likeliest genuine purge risk:** confirm the small-q coverage is present
  in `PerAnchorBound`/`AffinePolarSeal` before deleting — this may hold the only copy of `c0_le_route2`.

## Group 2 — Direct-WL / recovery route (CLOSED at the node-4 WL-dimension wall; superseded by **Route C**)

The direct-WL build of `bᵢ=1` (recover the Gram orbit by 1-WL) is an **open research problem**, not a tractable
build: it is gated on `ColorRefinesGramK` = "WL refines `gramK` at exactly the round it hits orbits" = the
node-4 WL-dimension wall, **open both ways**. Route C (form-recovery, `RouteC*` modules) sidesteps it. All the
Gauss/analytic content below was proved axiom-clean and is banked correct — but the route as a whole is closed.
Full verdict: recovery-route §9.8.9. **Do not re-walk.**

- `ScratchGramStrat{CharSum,ConeEval,ConeSep,Count,Eval,Gauss,GaussReduce,Invert,Orbit,WLBridge}` (10) — the
  `bᵢ=1` Gauss-strata build. Capstone `colorEq_iff_stabOrbit_wittOnly` reduces to `{ColorRefinesGramK, …}`;
  `ColorRefinesGramK` is the disguised crux (= the goal), not a residual. The re-base onto round-2 `Zprof`
  came back NEGATIVE (`Zprof` incomparable to `gramK`); the FLAG lead is also negative.
- `ScratchWallKernel` — the iterated `WallKernelFor` observable ("= banked quasipoly, pivot to Route C").
- `ScratchSpanDim2{Geom,Recovery,Span}`, `ScratchSpanDimBound` — recovery Phase-2 span-dim branching bounds
  (span-dim-1 `bᵢ≤q²` proven; span-dim≥2 = the closed Route A).
- `ScratchConicCount`, `ScratchConicSpan` — conic-count `hspan` discharge for Route A.
- `ScratchComplementFactor`, `ScratchComplementFactorK` — complement-factoring seal-reuse helpers.
- `ScratchBaseAug` — Route-A "Step B".
- `ScratchBoundedBranching`, `ScratchBoundedMultLeaves`, `ScratchBranchDepth`, `ScratchBranchingBound` —
  recovery-route leaf/branch/depth bounds.
- `ScratchJointCountInvariant` — Route-A observable soundness (`obsInvariant_jointCountProfile`).
- `ScratchOrbitBaseCase`, `ScratchWittCone` — WL / Witt-cone base cases for the direct-WL build.
- `ScratchDominatorForms` — δ′ dominator lead on `VO^ε`; hit a **dimensional wall** (cannot pin at d≥3).

## Group 3 — REFUTED leads (kept as the falsifier record)

- `ScratchPlanePin`, `ScratchPlanePinInduction`, `ScratchPlaneSep`, `ScratchWLWiring` — plane-point pinning.
  **`PlanePinnable` REFUTED** (`pin_probe.py`); the correct observable is *ambient colour-CLASS counts*, not
  plane-point pinning. (recovery §9.7.)
- `ScratchWLClassCounts` — `ClassCountsSeparateGram`; superseded (Witt-dead at `{a,b}`) inside the closed
  direct-WL route.

## Group 4 — Closed verdict (informs current design)

- `ScratchSimilitudeCap` — proves the **exact form value is NOT a graph invariant**, so any in-architecture
  *exact*-value recovery is closed-as-unviable. This is *why* Route C recovers `Q` **up to similitude**, not
  exactly. Keep as the rationale record.

## Group 5 — Superseded confinement scaffolds (archived 2026-07-09 during the confinement port)

Archived when the stable confinement/cost/canon substrate was ported into the named modules
`ChainDescent.CostModel` / `ChainDescent.CanonForm` / `ChainDescent.Confinement`. Both reference modules
that were removed in that port; they are frozen records, not maintained.

- `ScratchConfinementX3Reconcile` — the ii-b **iso-CONVERGENCE / C2 confluence-diamond** framing of the ①b→
  cut. **SUPERSEDED — do not build C2.** The W-plan (W1–W4, in `ScratchConfinementX3Complete`) closed ①b→ via
  fixed-schedule iso-invariance + per-level McKay reconciliation instead. Nothing imported it.
- `ScratchConfinementResidual` — the **whole-complement** faithful-model reframe (`ResidualSchemeModel` on
  `{x // x ∉ D}`). Refuted as the model: the residual group is transitive within a colour class but **not
  across** the complement's several cells, so `{x // x∉D}` is intransitive and not a single orbital scheme. The
  live model is CELL-based (`ScratchConfinementCellModel`). Kept only for its faithful-embedding / count-bridge
  substrate patterns.
