# Route C — the constructive form-recovery route to a POLYNOMIAL forms-graph canonizer

> **What this is.** The self-contained build plan for **Route C**: proving the affine forms-graph residue is
> canonized in **polynomial** time by *recovering the defining algebraic structure* (the form/geometry) from the
> abstract graph and then using its **known** automorphism group — instead of driving Weisfeiler–Leman refinement to
> orbits. Route C **sidesteps the node-4 WL-dimension wall** that closed the direct recovery route
> ([`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) §9.8.9). This doc is the staging point: a
> fresh reader should be able to read it and build forward. It carries the plan, the knowledge foundation, the exact
> names of the preexisting lemmas Route C rides on, and the probe evidence.
>
> **Relation to the other docs.** The SEAL (correctness disjunction `reachesRigidOrCameron`) is **already banked at
> quasipoly** and is *not* Route C's job. The direct WL/poly routes (A/B, `bᵢ=1` via `ColorRefinesGramK`) **STALLED**
> at the node-4 wall — full verdict in the recovery doc §9.8.9. Route C is the **bounded, guaranteed-poly alternative**
> that route pointed to. The forms-graph plan ([`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md))
> §11.4/§11.5 has the per-family (alternating / half-spin / Suzuki–Tits / char-2) analysis this doc's architecture generalizes.

---

## STATUS (read first)

**Where Route C stands (2026-07-05) — see the HANDOFF SNAPSHOT below for the current state + next tasks.** **★ ALL FOUR
FORM FAMILIES ARE SEALED** (affine-polar, alternating `Alt(5,q)`, half-spin, Suzuki–Tits), **the whole Lean spine is
PORTED into `build.sh` and axiom-clean** (`RouteCTransport` / `RouteCFormAdapters` / `RouteCSeam` / `RouteCNode4`; full
`build.sh` green ~68s; verify a decl with the checker pattern in "VERIFY" below), **the seam is atom-free** (L1
`htransport` DISCHARGED), and **L4 is DONE** — the affine-polar node-4 residue is discharged with no `hFormCert`
(`RouteCNode4.reachesRigidOrCameron_viaAffineFormScheme_routeC`), and the multi-form families have the §9.0a
meta-composition (Track B: `routeC_polySupport_of_adapter` + per-family corollaries). The C# runtime is
~as-complete-as-useful (affine-polar + Suzuki live). **★ SUZUKI IS CITATION-FREE:** the old scoped citation
`SuzukiFormsDetermine` is **discharged** — `separates` is proved outright by second-derivative recovery on an enlarged
base, so `reachesRigidOrCameron_suzuki` carries no citation and no `hσ`. So three families rest on one exact scoped
citation each (`NondegQuadricDeterminesForm` / `JointVarietyDeterminesFamily`), Suzuki on none.
**⟹ The remaining work is NOT another family and NOT the combine (both done); it is (a) promoting the scoped citations to
full Lean proofs (optional), and (b) — if a per-family coarse `SealDisj` is wanted for the multi-form families — Track A
(a multi-quadric pair-route, major).** Landed (all in `build.sh`, axiom-clean; module homes in §1 / `RouteCFormAdapters`):
- **The single-form spine (affine-polar):** F1+A1 (C#, confirmed vs the real harness) → A3 brick 1 (isometry scheme
  refines the graph) → discretize at a spanning base (`viaOrthogonalForm_spanning`) → **F4** iso-invariance
  (`recoveredForm_colouring_equivariant`). Rests on ONE exact scoped citation, `NondegQuadricDeterminesForm` (below).
- **F2 (`q=pᵉ` Frobenius/ΓL seam):** semilinear iso-invariance (`recoveredForm_colouring_equivariant_semilinear`),
  rests on the cited `ConePreservingCollineationIsSemiSimilitude` (fundamental thm of projective geometry).
- **F3 the engine interface (`IFormStructure`):** `FormAdapter` + `FormAdapter.reachesRigidOrCameron` (any adapter ⟹
  the seal). **Instance 1 (affine-polar) `affinePolarAdapter` ✅. Instance 2 (alternating `Alt(5,q)`) ✅ SEALED**
  (`reachesRigidOrCameron_alternating`, via the multi-quadric engine `multiFormAdapter`/`coords_determine_multi` +
  the concrete Plücker sub-Pfaffians `plucker_hjoint`) — first non-quadratic family. **Instance 3 (half-spin) ✅
  SEALED** (`reachesRigidOrCameron_halfSpin`, via the 10 validated D₅ spinor quadrics `S0..S9` + `spinor_hjoint` +
  `multiFormAdapter`; brick-1 `halfSpin_refines_coneScheme`; full instance-1 parity). **Instance 4 (Suzuki) ✅ SEALED
  + CITATION-FREE (2026-07-04)** — `reachesRigidOrCameron_suzuki` via the 5 σ-twisted ovoid forms + the
  `GF(q)^4↔𝔽₂^d` module bridge (`suzukiAdapter`); `separates` PROVED by the second-derivative recovery identities
  (`SF0_recover` etc. + `suzukiForms_determine`) on the enlarged base `{0,eᵢ,eⱼ,eᵢ+eⱼ}` (8 pts) — **no citation, no
  `hσ`**. **⟹ ALL FOUR FORM FAMILIES SEALED** (three modulo one scoped citation, Suzuki modulo none).
- **Multi-quadric bridges (NEW 2026-07-03, axiom-clean) — brings the multi-form families to full instance-1
  parity.** Previously the `multiFormAdapter` families (alternating, half-spin) carried only the *seal* leg, not
  the *refinement* + *iso-invariance* legs the single-quadratic instance has. Both now supplied GENERICALLY over
  the form family: **brick-1-multi** `multiIsometryScheme_refines_coneScheme` (the recovered joint-isometry scheme
  `⨅ₖ O(Q_k)` refines the *graph-intrinsic* cone-stabilizer scheme `jointConeStab Qs` — cleaner than the
  single-form case, since the cone stabilizer is defined from the connection set, not a form-defined group) and
  **F4-multi** `recoveredFamily_colouring_equivariant` + `recoveredFamily_partition_isoInvariant` (a graph iso
  transports the value-tuple colouring by a global INJECTIVE `Φ`, so the colour partition is iso-invariant; `Φ`
  is the multi-form replacement for the single-form scalar `μ`; rests on the carried scoped citation
  `JointVarietyDeterminesFamily`, the multi-form sibling of `NondegQuadricDeterminesForm`). Factored the generic
  `affineScheme_refines_of_le` (`H ≤ G ⟹` finer; `isometryScheme_refines_similitudeScheme` is now its corollary);
  concrete `alternating_refines_coneScheme` / `halfSpin_refines_coneScheme` confirm the bridge fires on the real
  Plücker / spinor families. **⟹ alternating AND half-spin both at full instance-1 parity.**
- **Both review-flagged items resolved:** the classical carry is **discharged as an exact scoped citation**
  (`NondegQuadricDeterminesForm`); the **meta-poly bootstrapping is assessed sound** (§7a — global coordinatization,
  not the node-4 wall in disguise).

**▶▶▶ HANDOFF SNAPSHOT (2026-07-05, current). Read this first; the dated bullets below are the build history.**

**LEAN — the seam is now ATOM-FREE.** All four family adapters sealed axiom-clean (`RouteCFormAdapters.lean`), and **★ L1
`htransport` is DISCHARGED** (`RouteCSeam.lean`, axiom-clean; §9 item 3, [[project_routec_seam_2026-07-04]]) —
the Route-C seam carries **no uncited/unproved atom**. Mechanism: transport the ONE light predicate `SeparatesAtBoundedBase`
(not the 4-way `SealDisj`) via a cross-graph `warmRefine_transport_iso`; capstone `reachesRigidOrCameron_viaSchurianRank3Affine_proved`.
**★ HONEST SCOPE (do not overstate): the four family seals + the seam are done, PORTED, and the node-4 discharge (L4)
has landed** — a genuine coarse `SealDisj` for **affine-polar** (`RouteCNode4.reachesRigidOrCameron_viaAffineFormScheme_routeC`,
no `hFormCert`) and the §9.0a **meta-composition** for the three multi-form families (Track B). The Route-C *poly* claim
itself stays the project's standard **meta** claim (§9.0a — there is no non-vacuous coarse-scheme Lean predicate). So the
Lean deliverable is complete **modulo scoped citations** (+ optional Track A for a per-family multi-form coarse `SealDisj`).
Landed:
- (a) **PORT — ✅ DONE (2026-07-05).** The five scratch spine files are consolidated into **three named build modules**:
  `RouteCTransport` (← Cascade; `SchemeRealizes` + the `…_transport_iso` tower + `separatesAtBoundedBase_transport` + the
  3 distilled partition helpers), `RouteCFormAdapters` (← CascadeAffine; the four family seals + engine; git-mv of
  `ScratchRouteC`), `RouteCSeam` (← CascadeAffine, RouteCTransport; `SealDisj` + generic dispatch + affine-polar atom-free
  capstone + cyclotomic dispatch + finer→coarser group-pinning). Added to `build.sh` MODULES; **full `build.sh` green (66s),
  all nine capstones axiom-clean `[propext, Classical.choice, Quot.sound]`** (verified via a checker file, per the
  build-noise caveat below). `PublicTheoremIndex.md` updated (scoped: −`ScratchSeam` section, +3 RouteC sections with
  headline descriptions). Dropped, not ported: `ScratchSeam`'s superseded carried-`htransport` theorem, and
  `ScratchNodeCountBridge`'s demoted CellsAreOrbits half (only its 3 transport helpers were distilled into `RouteCTransport`;
  the file itself stays scratch — still imported by the demoted `ScratchBoundedBranching`). The 4 superseded scratch seam
  files (`ScratchSeam`/`…Transport`/`…Dispatch`/`…RecoveredFormTransfer`) are deleted. *Note on `defaultTargets`:* Route C
  goes in `build.sh` MODULES only (not `lakefile.toml` `defaultTargets`) — matching the existing convention where
  `AffinePolarSeal` + the whole pair route are build.sh-only and bare `lake build` is the intentionally-lighter set.
- (b) **L4 — the node-4 discharge — ✅ DONE for the affine-polar family (2026-07-05, `RouteCNode4.lean`, axiom-clean,
  in build).** `reachesRigidOrCameron_viaAffineFormScheme_routeC`: the abstract affine-polar node-4 residue `S` reaches
  the **same** seal disjunction as `reachesRigidOrCameron_viaAffineFormScheme` (`CascadeAffine.lean:2057`) — but carries
  **NO `hFormCert`** and **no carried `IsotropySeparatesAtBase`**. Key correction to the earlier framing: `viaAffineFormScheme`'s
  `hFormCert` is a `RelCountsDetermineOrbit`/`CellsAreOrbits`-style predicate, which §9.0a shows is **false at bounded base**
  (the node-4 stall) — Route C does *not* discharge it; it supplies the **alternative** path that bypasses it
  (pair-route `exists_isotropySeparatesAtBaseK` → `isotropySeparatesAtBase_of_K` → `separatesAtBoundedBase_transport`
  → `viaSpielman`). So L4 *supersedes* the hook for this family rather than filling its hypothesis. The residual carried
  content is the **classification** (`SchemeRealizes f S (affineScheme(similitudeGroup Q))` — the Skresanov/Cameron/Liebeck
  citation that `S` *is* this family) + the pair-route scope (`q=p` odd, large) + `{G3}` — the same premises as the banked
  `reachesRigidOrCameron_affinePolar`, now transported to the abstract residue. **The affine-polar node-4 case is now
  actually discharged** (poly-ness stays the project meta-claim, §9.0a).
  - **Multi-form Track B — ✅ DONE (2026-07-05, `RouteCNode4.lean`, axiom-clean).** The three multi-form families get the
    §9.0a meta-composition via a generic engine `routeC_polySupport_of_adapter` (any `FormAdapter` + a coarse over-group
    `Gc ≥ A.G₀`, mod one Skresanov `AffineSchemeTwoClosed`) → the triple (coarse Aut = `affineG Gc` ∧ fine harvest
    **extracted from the adapter**, no carried `hfine` ∧ fine ≤ coarse), with corollaries
    `routeC_polySupport_{alternating,halfSpin,suzuki}`. Suzuki needed a `formConeStab` generalization (its ovoid cone is
    **cubic**, so `jointConeStab` — typed for `QuadraticForm` — doesn't apply) + a `suzukiG₀ ≤ formConeStab` bridge. This
    retires the multi-form island status at the meta level (fine seal ↔ coarse graph via group-pinning + refinement).
  - **Track A (deferred):** a genuine coarse `SealDisj` for the multi-form families (full parity with affine-polar's
    strong L4) needs a multi-quadric coarse discretization (`IsotropySeparatesAtBase Qs` — a multi-quadric pair-route),
    major new math; only affine-polar has one. Not blocking (Track B suffices for the meta poly argument).
- (c) **promote the scoped citations** to full proofs (`NondegQuadricDeterminesForm`, `JointVarietyDeterminesFamily`,
  `ConePreservingCollineationIsSemiSimilitude`, `AffineSchemeTwoClosed`) — optional, `chain-descent-citation-discharge.md` has routes.

**C# — the runtime is ~as-complete-as-useful (reassessment 2026-07-05).** Built and green (60/60 fast Route-C tests +
Suzuki LongRunning, 0 regressions, full build clean). Pipeline: recover form family (C1a) → build answer group (C1b) →
classify (C2) → canonicalize by iso-type (C3, **default ON**) → Aut-free geometry (C4), dispatched over an
`IFormFamilyHandler` registry (§9.2.7). **Live families: affine-polar (odd q) + Suzuki (VSz(8), NEW 2026-07-05 runtime
prototype).** Alternating/half-spin are **dormant by design** — the **FEASIBILITY WALL** (§9.2.7): dense `n²` adjacency
makes `Alt(5,q)=q^{10}` (≥14 GB) and half-spin `q^{16}` uninstantiable at every usable `q`, so those handlers would never
fire; their correctness content is the sealed Lean adapters. Suzuki files: `SuzukiOvoid.cs` + `SuzukiHandler.cs` +
`RouteCCanonicalizer.SuzukiAutOrder`; the load-bearing new idea is a **field-agnostic F₂ degree-signature `Confirm`**
(cone is cubic-cut but not quadric-cut ⟹ distinguishes VSz(8) from its cospectral mate VO⁻₄(8) with no field recovery).
Other files: `QuadraticFormRecovery.cs` (C1a), `ClassicalGroupGenerators.cs`+`ClassicalSimilitude.cs` (C1b),
`FormsGraphClassifier.cs` (C2), `FormFamilyHandler.cs`+`AffinePolarHandler.cs`+`{Alternating,HalfSpin}Handler.cs`+
`FormsGraphBuilder.cs` (C3), `GeometricCoordinatizer.cs` (C4). Tests: `RouteC*Probe.cs`.

**★ REASSESSMENT VERDICT (2026-07-05): the remaining high-value Route-C work is LEAN, not more C#.** The genuine
through-the-wall mechanism (recover `Q` globally → known group `AΓO(Q)`) is confirmed for affine-polar; the 2026-07-05
frame+WL finding is a *negative* result (it dissolves the fake cone-blindness sub-problem but reduces to the project's
existing WL-dim core, so it advances no proof); and alternating/half-spin runtime is blocked by the feasibility wall. So
the C# runtime is close to as complete as it usefully can be. Fuller record: [[project_routec_csharp_build_2026-07-04]].

**▶ NEXT TASKS (any is a clean pick-up; rough priority):**
0. ✅ **PORT — DONE (2026-07-05).** Route C is in `build.sh` as `RouteCTransport`/`RouteCFormAdapters`/`RouteCSeam`
   (consolidated from the 5 scratch files + the NodeCountBridge transport helpers); full build green, axiom-clean, index
   updated. See STATUS "HONEST SCOPE" item (a).
1. ✅ **L4 — DONE (2026-07-05, `RouteCNode4.lean`, axiom-clean, in build).**
   - **affine-polar (L4-strong):** `reachesRigidOrCameron_viaAffineFormScheme_routeC` — a genuine coarse `SealDisj` on the
     abstract residue, NO `hFormCert` (STATUS "HONEST SCOPE" item (b); the `hFormCert`-is-false-at-bounded-base correction).
   - **multi-form (Track B / L4-meta, ALL THREE families):** `routeC_polySupport_of_adapter` (generic engine over any
     `FormAdapter` + coarse over-group `Gc ≥ A.G₀`, mod one Skresanov `AffineSchemeTwoClosed`) + corollaries
     `routeC_polySupport_{alternating,halfSpin,suzuki}`. Delivers the §9.0a meta-composition triple — (i) coarse Aut =
     `affineG(coarse group)` ∧ (ii) fine harvest **extracted from the adapter** (via
     `schemeRecoveredByDepth_of_separatesAtBoundedBase` on the adapter's own `SeparatesAtBoundedBase` witness — no carried
     `hfine`, an improvement over affine-polar's `routeC_polySupport`) ∧ (iii) fine ≤ coarse. Retires the island status of
     the multi-form fine seals at the meta level. Suzuki needed a `formConeStab` generalization (its ovoid cone is **cubic**,
     not quadric-cut, so `jointConeStab` — typed for `QuadraticForm` — doesn't apply) + a `suzukiG₀ ≤ formConeStab` bridge.
   - **Deferred (Track A):** a coarse `SealDisj` for the multi-form families (full L4-strong parity) needs a multi-quadric
     coarse discretization (`IsotropySeparatesAtBase Qs` — a multi-quadric pair-route), major new math; only affine-polar has it.
   **NEXT frontier here** = promote scoped citations, or (if a per-family coarse `SealDisj` is wanted) Track A.
2. **Promote scoped citations** to full Lean proofs (above) — `chain-descent-citation-discharge.md` §routes.
   **★ F4 DISCHARGE DONE (2026-07-05):** `NondegQuadricDeterminesForm` + `JointVarietyDeterminesFamily` are now off the
   **F4 iso-invariance object** — the §3.2 vanishing-space transport is BANKED (5 axiom-clean lemmas in
   `RouteCFormAdapters.lean`: `vanishingForm_transport_gen`, `recoveredForm_partition_isoInvariant{_gen,}`,
   `recoveredFamily_partition_isoInvariant_vanishing`, `vanishingColour_refines_form`; the recovered colour partition is
   proved iso-invariant with no dimension count). Those two remain carried ONLY on the strictly-stronger `|Aut|`-naming
   theorems (`recovered{Form,Family}_colouring_equivariant`). So the live Route-C carries are now just FTPG
   `ConePreservingCollineationIsSemiSimilitude` (hard, q=pᵉ only) + Skresanov `AffineSchemeTwoClosed` (meta-poly pinning),
   plus `JointVarietyDeterminesFamily` on the `|Aut|`-naming side only.
   **★ FULL `NondegQuadricDeterminesForm` discharge DONE (2026-07-06, axiom-clean, in `build.sh`).** Ported →
   `ChainDescent.Nullstellensatz{,Structural,Count,Hlink}` (Scratch dropped). Structural route: `section_iso_count`
   (crux, exact isotropic-`u` section, gap `(q−2)q²>0` clears the `q=3` VO⁻₄(3) boundary that the `hconn` k=4 walk
   fails) → `cone_punctured_span` (hspan) + `aniso_polar_diameter_two` (hlink) → `nullstellensatz_of_structural` →
   `nondegQuadric_zmod_of_even` = exact `NondegQuadricDeterminesForm p d` for **even `d`** (every `VO^ε_{2m}` use).
   `RouteC.nondegQuadricDeterminesForm_of_even` proves the predicate; `recoveredForm_colouring_equivariant`'s `hcite`
   is DELETED (carries only `Even d`). Live Route-C carries now = FTPG + Skresanov + `JointVarietyDeterminesFamily`.
3. *(lower)* **C# frame+WL confirmation** into `AffinePolarHandler.Confirm` (harvest-free p≥5 mate-ruling) — sound but
   advances no proof (reduces to the WL-dim core); the harvest-based `ConfirmByMultiQuadricReconstruction` already works.
4. *(lower)* **Suzuki generalization** past q=8 or **alternating/half-spin runtime** — both gated on a sparse/implicit
   graph representation (the feasibility wall); large infra, arguably not worth it (those graphs can't be canonizer inputs).
5. *(cleanup)* Move the one-shot exploratory `Probe_*` tests out of the gating build (`[Trait("Category","Exploratory")]`
   + default filter) — they are report-only by design (26 flagged, sweep in this session's history); the 3 RouteC probes
   that back live §9.2.8 claims are already asserted.
6. *(cleanup, pre-existing)* `PublicTheoremIndex.md` is stale for ~27 non-build scratch files (the generator sweeps all
   active source; a blanket `rewrite` surfaces ~200 undescribed rows). Not this port's job — a separate scoped decision
   (exclude scratch, or a full description pass). The Route-C rows were spliced in without triggering that sweep.
Everything below is the dated build history.

**▶ C# BUILD (2026-07-04) — C1a + C1b (build history follows).**
- **C1a `RecoverFormFamily`** (added to `QuadraticFormRecovery.cs`): generalizes A1 from `kernel[0]` (one quadratic) to
  the whole degree-2 **vanishing-space basis** (`RecoveredFormFamily{Basis[][], EvaluateAll, OnCone}`). Test
  `RouteCFormFamilyProbe.cs` (6/6): multi-quadric Cayley graphs (F₃⁴/F₅⁴/F₃⁶, VanishDim 2–4) reconstruct with **0
  mismatches** (valid because S := joint zero of chosen quadrics ⟹ `Z(V)=S∪{0}` exactly), + single-quadric consistency
  with A1 on VO±₄.
- **C1b `ClassicalGroupGenerators` + `ClassicalSimilitude` (the load-bearing piece)** (new files): builds
  `affineG(similitudeGroup Q)` generators = translations + orthogonal reflections `x↦x−(B(x,a)/Q(a))a` (Cartan–Dieudonné)
  + scalar scalings + **the non-square-factor similitude** (via congruence-diagonalization → factor-ν block map). Test
  `RouteCGroupProbe.cs`: **order-check EXACT at n=81 both types** — `built.Order == harvested |Aut|` (VO⁺₄(3)=186624,
  VO⁻₄(3)=233280), the executable form of `schemeAutGroup_coarse_eq_affineG`. **KEY FINDING (predicted):** without the
  non-square similitude the built group is the index-2 subgroup (ratio exactly 2 = [F_p*:squares]); the similitude
  closes it. **SIFTING LIMITATION:** the order-check is exact at n=81 but Schreier–Sims *without sifting* does not scale
  the `Order` computation past ~n=81 with the full reflection set (~120 gens at n=625) — a `PermutationGroup` deferred
  concern, NOT a C1b-correctness issue; the *construction* scales fine (n=2401, 356 gens, all stabilise, fast). Closed
  form `|affineG^ε₄(q)| = q⁴·2q²(q²−ε)(q²−1)(q−1)` validated == harvested at n=81.
- **C2 `FormsGraphClassifier`** (new file): strong-regularity gate + **constructive** affine-polar detection
  (valency = VO^ε isotropic count `(qᵐ−ε)(qᵐ⁻¹+ε)`, confirmed by the recovered quadric reconstructing the graph) +
  Suzuki SRG(4096,455,6,56) fingerprint. Test `RouteCClassifyProbe.cs` (6/6): classifies VO±₄(3,5) with correct
  `(p,m,ε)`; non-SR / empty graphs → Unknown (misclassification is SAFE by design). Returns `Unknown` for
  alternating/half-spin (recovery = future multi-form track).
- **C3 `RouteCCanonicalizer` + the option-ii orderer wire** (new file + `CanonGraphOrdererChainDescent.EnableRouteC`,
  default OFF): canonicalizes a forms-graph residue via the **recovered algebraic invariant** `(q,m,ε)` (the form's
  iso-type is a complete invariant ⟹ canonical graph = standard VO^ε, `|Aut|` = closed form). Wire reuses the single
  descent's harvested group (`RecognizeFromResult`, no double-descent), returns the standard graph when recognized else
  the descent's lex-min. Test `RouteCCanonicalizeProbe.cs`: **END-TO-END ISO-STABILITY** — VO±₄(3) and 3 random
  scrambles recover the SAME `(q,m,ε)`, `|Aut|`, and canonical adjacency, both via the canonicalizer directly AND via
  the public orderer `Run` API. **KEY FINDING:** the wire's *d-scaling* payoff is gated on **C4** — recognition still
  needs the descent's harvest to coordinatize (F1's `O_p(Aut)`), so at large `d` (where the plain descent stalls)
  recognition stalls too; C4 (Aut-free coordinatization) is what makes the certified path independent of the harvest.
  No regressions (129/129 core canon + Route C + PermutationGroup; default-off preserves behaviour).
- **C4 `GeometricCoordinatizer` (Aut-free) — ENABLING STEP LANDED** (new file). Recovers the isotropic **lines**
  through `o` from **adjacency alone** (no Aut harvest) via the local invariant `|N(o)∩N(x)∩N(y)|` + largest-gap
  thresholding + union-find. Test `RouteCGeometryProbe.cs` (4/4): VO±₄(3,5) recover 10/16/26/36 lines, each of size
  `q−1`, **all genuinely collinear** (checked vs ground truth), directions **span dim 4** — the enabling property for
  coordinatization, validating `route_c_bootstrap_probe.py` in production C#. **REMAINING (scoped, not built):** the
  full coordinate assignment — scalar labelling of each line (Von Staudt cross-ratio / fundamental thm of projective
  geometry) + reading a vertex's coords off the parallel-line grid (Buekenhout–Shult; poly + citable for rank ≥ 3, i.e.
  `d ≥ 6`; `d=4` = special GQ). Until it lands, C3's wire uses F1's harvest at small `d`; this step is what makes the
  certified path harvest-free (hence d-scalable).

- **C4 — HARVEST-FREE INVARIANT + Route C ON BY DEFAULT (2026-07-04).** **Route C is now enabled by default**
  (`EnableRouteC = true`); the full suite passes **291/291, 0 breakages** (iso-stability tests stay green — Route C is
  iso-invariant; no test hardcodes a canonical matrix for a recognized odd-q affine-polar graph). **★ KEY C4 FINDING:**
  the canonical **invariant** `(q,m,ε)` — hence C3's whole *answer* (standard canonical graph + closed-form `|Aut|`) — is
  recoverable **HARVEST-FREE** from just `(n, valency, strong-regularity)` (`GeometricCoordinatizer.RecoverAffinePolarInvariant`,
  tested `RouteCGeometryProbe` 4/4 vs the coord-based classifier). So the d-scaling concern **for the answer is resolved
  without coordinatization**; `RecognizeFromResult` now computes the invariant harvest-free and uses the harvest **only
  for the safety confirmation** (does the recovered form reconstruct the graph — rules out a parameter-mate SRG). **What
  full coordinatization is still needed for:** making that *confirmation* harvest-free (distinguishing a genuine VO graph
  from a hypothetical cospectral parameter-mate).
- **★★ C4 FULL COORDINATIZATION — HARVEST-FREE for VO±₄(3), + the obstruction CHARACTERIZED (2026-07-04).** The
  parallelism/orientation wall was dissolved by a **linear** method: an isotropic line is an arithmetic progression, so
  `Σ coord(line points) = 0` (odd p) — a constraint with NO ordering/orientation. `CoordinatizeByLineSums` (+
  `RecoverAllIsotropicLines`) solves the line-sum system over `F_p` and recovers coords **from adjacency alone**.
  **KEY OBSTRUCTION, now crisp — CONE-BLINDNESS:** the solution space is `{linear functionals} ⊕ {cone-blind functions}`;
  the quadratic form `Q` itself satisfies every isotropic-line-sum (`ΣQ = 2Q(d) = 0` since `Q(d)=0`), so the graph
  determines coords only **up to adding multiples of `Q`**. Measured ambiguity `A = nullDim − d`: **`A=1` at q=3, `A=45`
  at q=5** (d=4). The linear part is isolated by a **shear search** over the ambiguity (the unique complement that
  *reconstructs* the form), feasible when `p^{d·A}` is small (`A=1 ⟹ 81` for p=3). **RESULT: VO±₄(3) is coordinatized
  HARVEST-FREE and reconstructs (0 mismatches, `RouteCGeometryProbe`), now WIRED into the confirmation
  (`ConfirmByMultiQuadricReconstruction` tries harvest-free first) ⟹ the WHOLE Route-C pipeline is harvest-free for
  VO±₄(3) = provably poly for that case, no descent/T0 dependence.** For `p≥5` the coordinatizer honestly DECLINES
  (ambiguity search infeasible) — the general case is the remaining hard core: **isolating the linear part past the
  cone-blind `Q`-ambiguity, whose dimension grows with `p`** (this IS the fundamental-theorem-of-geometry difficulty, now
  precisely located — NOT parallelism-detection, which the line-sum method sidesteps). **Honest state: C4 = harvest-free
  invariant DONE + harvest-free full coordinatization DONE for small-ambiguity (p=3, pipeline provably poly there) +
  large-ambiguity (p≥5) isolation = the precisely-characterized open core.**
  > **⚠ SUPERSEDED (2026-07-05) — read §9.2.8 CORRECTION.** The "p≥5 open core" here was a **line-sum-method artifact**.
  > The natural method — **fix a size-`(d+1)` frame + WL** — discretizes VO^ε_d(q) for ALL p in `d+1` greedy steps
  > (`RouteCScalarRecoveryProbe`), so harvest-free coordinatization is cheap for every p. The residual open item is
  > *proving* that discretization is poly (= the project's existing WL-dim core), not a Route-C-specific barrier. The
  > p=3 line-sum coordinatizer stays as a landed alternative; the go-forward confirmation route is frame+WL (§9.2.8).

- **FAMILY-DISPATCH SCAFFOLD (2026-07-04, §9.2.7).** Refactored the hardwired affine-polar pipeline into an
  **`IFormFamilyHandler` registry** (C# mirror of the Lean `FormAdapter`). `AffinePolarHandler` real; `Alternating` /
  `HalfSpin` / `Suzuki` handlers with **all interconnection live** (dispatch, generic result plumbing, and — for the
  odd-q multi-quadric families — the **`Confirm` step fully wired** via C1a `RecoverFormFamily`) and only their per-family
  math core (fingerprint / standard-graph / closed-form |Aut|; char-2 recovery for Suzuki) as documented stubs with a
  crisp completion contract. Dormant handlers decline safely (fall back to the descent). Suzuki's VSz(8) fingerprint is
  live. Regression clean (114/114 Route-C + core suite). This is the prep-for-other-families work: a future builder fills
  well-defined stubs, not a green field.

**▶ C# BUILD SUMMARY (2026-07-04): C1a, C1b, C2, C3, C4 + FAMILY-DISPATCH SCAFFOLD LANDED. Route-C + core suite green,
0 regressions.**
The runtime spine (recover form family → build the answer group → classify → canonicalize by iso-type → Aut-free line
recovery) is in place and validated end-to-end (order-check exact vs harvested |Aut| at n=81; scramble-invariant
canonicalization through the public orderer). **Two precisely-scoped remainders:** (a) **C4 full coordinatization**
(Von Staudt scalar recovery + Buekenhout–Shult grid) — unblocks d-scaling; (b) **PermutationGroup sifting** — unblocks
the order-check past n≈81. Multi-form (alternating/half-spin) + char-2 (Suzuki) recovery are the other future tracks.

**▶ PICK UP HERE (next actionable steps, in rough priority):**
0. ✅ **Multi-quadric bridges — DONE 2026-07-03** (brick-1-multi + F4-multi, generic; alternating at full
   instance-1 parity, half-spin pre-equipped). See STATUS "Multi-quadric bridges".
1. ✅ **Half-spin instance — DONE 2026-07-03** (`reachesRigidOrCameron_halfSpin`, axiom-clean). The 10 validated D₅
   spinor quadrics `S0..S9` are transcribed (`RouteCFormAdapters.lean §HalfSpin`), `spinor_hjoint` proved from `S0..S4`
   by coordinate isolation, sealed via `multiFormAdapter` + the shared engine; brick-1 `halfSpin_refines_coneScheme`
   landed; F4 generic. Full instance-1 parity. (This was the 3rd of 4 seals; Suzuki, item 2, followed.)
2. ✅ **Suzuki–Tits instance — DONE + CITATION-FREE 2026-07-04** (`reachesRigidOrCameron_suzuki`, axiom-clean, **no
   citation, no `hσ`**). De-risked (5 σ-twisted forms, joint zero=cone exact), forms rederived, the `GF(q)^4↔𝔽₂^d`
   module bridge + `suzukiAdapter` landed, and — the citation discharge — `separates` PROVED by the second-derivative
   recovery identities on the enlarged base `{0,eᵢ,eⱼ,eᵢ+eⱼ}` (each coordinate = `DᵢDⱼ SF_k`, σ-terms cancel in char
   2; base 8, still O(d²) poly). Probes `route_c_suzuki_determine_probe.py` (frame injective for q=8/32; forms cut the
   cone exactly) + `route_c_suzuki_symbolic.py` (the polarization). **⟹ ALL FOUR FAMILIES SEALED** (three modulo one
   scoped citation each, Suzuki modulo none). §6 "Suzuki".
3. **★ Lean-side seam — DONE (2026-07-04).** The combine is landed at the honest level (§9.0a): the finer→coarser
   transfer reframed after a **vacuity correction** (`GroupReproduced` was a tautology; non-vacuous coarse-reaches-rigid
   is false = node-4), yielding the *genuine* non-vacuous content — group-pinning
   `schemeAutGroup_affineScheme_eq_affineG` (all 4 families, mod the named Skresanov citation `AffineSchemeTwoClosed`) +
   `routeC_polySupport` certificate (`RouteCSeam.lean`), and the **cyclotomic dispatch branch**
   `reachesRigidOrCameron_seamDispatch`/`cyclotomic_sealDisj` (`RouteCSeam.lean`, the dropped 5th case). All
   axiom-clean. **★ `htransport` (L1) is now DISCHARGED (2026-07-05, `RouteCSeam.lean`, axiom-clean) — the
   seam carries NO atom.** Decomposition (user's, source-validated): the forms-graph seal is Cameron-free and inhabits
   only `SchemeRecoveredByDepth` via the light `SeparatesAtBoundedBase`, so transport ONE predicate, not four —
   `separatesAtBoundedBase_transport` (via a cross-graph `warmRefine_transport_iso`, a localized generalization of the
   landed single-graph `warmRefine_transport`) + `separatesAtBoundedBase_affinePolar` (extract the Cameron-free content
   before the `Or.inl (Or.inr …)` padding) → `reachesRigidOrCameron_viaSchurianRank3Affine_proved` (seam, `htransport`
   proved, not carried). **Eliminates** the `IsCameronScheme`-invariance premise (Cameron asserted on `S` directly, never
   transported) AND the `SchemeBlockRecovered`/`schemeEquiv` wrinkle (block never transported). Supersedes ScratchSeam's
   carried-`htransport` `reachesRigidOrCameron_viaSchurianRank3Affine`.
4. ✅ **The C# runtime — C1a–C4 + family-dispatch LANDED (2026-07-04/05); Suzuki runtime prototype ADDED (2026-07-05).**
   See the "HANDOFF SNAPSHOT" at the top of STATUS + §9.2 + §9.2.7. **Live families: affine-polar (odd q) + Suzuki
   (VSz(8))**; alternating/half-spin **dormant by design** (FEASIBILITY WALL, §9.2.7 — dense-infeasible at every `q`).
   60/60 fast Route-C tests + Suzuki LongRunning, 0 regressions. **★ REASSESSMENT (2026-07-05): C# runtime is
   ~as-complete-as-useful; the remaining high-value Route-C work is LEAN (PORT + citations), not more C#** — the frame+WL
   confirmation (§9.2.8) is sound but advances no proof (reduces to the WL-dim core), and the harvest-based `Confirm`
   already works. Details: HANDOFF SNAPSHOT "NEXT TASKS" + [[project_routec_csharp_build_2026-07-04]].
5. **The remaining carried scoped citations** (optional, to remove them from the spine): full Lean proofs of
   `NondegQuadricDeterminesForm` (single-quadric uniqueness), `JointVarietyDeterminesFamily` (multi-quadric — alt /
   half-spin), `ConePreservingCollineationIsSemiSimilitude` (F2 semilinear seam), and `AffineSchemeTwoClosed` (the
   Skresanov rank-3 2-closure — new this session). *(Suzuki's `SuzukiFormsDetermine` is already discharged — item 2 —
   so it is no longer on this list.)* All are exact, correctly-scoped classical statements (finite-geometry /
   classical-group developments) — carried like `Theorem41Statement`/`G3`, discharged externally.
6. **The meta-poly rigor side (last):** residuals R1–R3 (§7a) — build the Aut-free geometric
   coordinatizer (also delivers F2's field recovery), name Buekenhout–Shult (R2), double-check `d=4` (R3).

**✅ DONE — the C# recovery front (abstract graph → coordinates → form → graph), confirmed against the REAL harness.**
- **F1 — additive-structure recovery** (`PermutationGroup.RegularNormalPSubgroup` + `AffineStructureRecovery.Recover`):
  `T = O_p(Aut)` (the socle) recovers the regular elementary-abelian translations `≅ (𝔽_p)^d`, and a basis coordinatizes
  the vertices. Probe `route_c_f1_probe.py` (algorithm) + `RouteCF1Probe.cs` (production, vs the real `ResidualGroup`,
  ground-truth exact).
- **A1 — form recovery** (`QuadraticFormRecovery.RecoverForm`): recovers `Q` up to scalar by ONE degree-2 kernel solve
  on the cone. Probe `route_c_reconstruct_probe.py` (`vanishDim=1` all ε/d/q) + `RouteCF1Probe.cs`: the recovered `Q` +
  coords **reconstruct the entire graph** (`Q(coords[x]−coords[y])=0 ⟺ x~y`, **0 mismatches**, VO^±₄(3), VO^±₄(5)).
- Both odd-q and char-2 for F1 (full `Aut` delivered); A1 is odd-q (char-2 = separate Arf track). All C# tests green,
  existing `PermutationGroup` tests unaffected.

**✅ DONE — the Lean spine (`ChainDescent/RouteCFormAdapters.lean`, all axiom-clean, in `build.sh`).**
- `coords_determine_spanning` + `reachesRigidOrCameron_viaOrthogonalForm_spanning` — the **spanning-base** generalization
  of the landed `coords_determine`/`viaOrthogonalForm`: the isometry scheme `O(Q)` discretizes at ANY base whose
  differences span (Route C individualizes an iso-invariantly chosen base, not the literal standard frame).
- `isometryScheme_refines_similitudeScheme` (**A3 brick 1**) — `O(Q)≤GO(Q)` ⟹ the isometry scheme (exact-`Q` relations)
  refines the given similitude graph (isotropy-only). The consistency half of the bridge.
- **F4 equivariance core (NEW 2026-07-03, axiom-clean):** `recoveredForm_colouring_equivariant` — the linear part `g` of
  a graph iso carries the `Q`-cone to the `Q'`-cone, hence (via the carried `NondegQuadricDeterminesForm`) the recovered
  **difference colouring** transports by one global scalar: `Q'(g u − g t) = μ · Q(u − t)`. Provable bricks
  `similitude_colouring_equivariant` (the equivariance identity) + `similitude_conePreserving` (cone consistency); the
  one non-elementary link is `NondegQuadricDeterminesForm` (below).
- **The assembled spine:** recover `Q` (F1+A1, C# done) → work on the finer isometry scheme (refines the given graph,
  brick 1) → discretize at a spanning base (`viaOrthogonalForm_spanning`, landed) → the whole thing is iso-invariant
  (F4). **Discreteness does NOT transfer down to the similitude scheme** (that's the node-4 stall) — so Route C is a
  *distinct canonicalization object*, and F4 supplies exactly the iso-invariance that makes "discrete ⟹ canonical".

**◻ REMAINING — the classical carry, the meta claim, and the bootstrapping question.**
- **✅ `NondegQuadricDeterminesForm` — DISCHARGED as an exact citation (2026-07-03).** "a nondegenerate quadric
  determines its quadratic form up to a nonzero scalar" (the `vanishDim=1` fact, = A1's Lean side = F4's one
  non-elementary link — they unify). Now a **correctly-scoped named premise** (`p ≠ 2`, `4 ≤ d`, `Q.polarBilin`
  nondegenerate) — the *exact range where it is TRUE* (the unrestricted `∀ Q R` form is FALSE at `d=3,q=3`: a conic's 4
  points lie on a pencil, `vanishDim=2`). Carried like `Theorem41Statement`/G3 (Mathlib has no quadric Nullstellensatz);
  reference = Hirschfeld, *Projective Geometries over Finite Fields* / the projective Nullstellensatz for a nondegenerate
  quadric; probe-confirmed exactly in-scope (`d=4,6,8`, `q=3,5,7,11`). A full Lean proof (finite-geometry development) is
  optional future work; the citation is exact + non-vacuous, so the carry is legitimate.
- **Meta poly claim:** "poly" stays a meta-argument over the bounded-base discreteness object + poly per-node (no runtime
  model in Lean).
- **★ ASSESSED — meta-poly bootstrapping (spotted + resolved 2026-07-03; full write-up §7a):** F1 as built recovers
  coordinates from `T = O_p(Aut)` — it **consumes `Aut`**, whose poly computation is the open T0 problem Route C sidesteps
  (potential circularity). **Verdict: resolved at the meta level — Route C is genuinely poly, non-circular.** Key points:
  (i) coordinatization is a **global** computation, not bounded-round WL, so it is NOT the node-4 wall in disguise; (ii)
  `O_p(Aut)` was only a de-risking shortcut — the poly pipeline uses **Aut-free geometric coordinatization** (recover the
  polar-space geometry from the graph, coordinates via Buekenhout–Shult, rank≥3 / `d≥6`; `d=4` = GQ special case); (iii)
  the enabling primitive is **probe-confirmed Aut-free** (`route_c_bootstrap_probe.py`: the local invariant separates
  collinear triangles and recovers spanning isotropic lines, all VO^± `d=4,6` `q=3,5`). Residuals (record, don't block):
  build the geometric coordinatizer (R1), name the geometry-recovery citation (R2), double-check `d=4` (R3). The Lean
  object (F4) is unaffected (no runtime model in Lean). See §7a.
- **◑ F2 (`q=pᵉ` Frobenius seam) — Lean core LANDED (2026-07-03, axiom-clean):**
  `recoveredForm_colouring_equivariant_semilinear` — the recovered form is iso-invariant up to scalar **and** a field
  automorphism σ (a graph iso over 𝔽_q is 𝔽_p-semilinear, `g = M∘σ̂`). `q=p` is the `σ=id` case. Remaining F2 = the C#
  field-recovery side, which folds into R1 (geometric coordinatization recovers PG over 𝔽_q, field included).
- **✅ F3 (`IFormStructure` engine interface) — LANDED + ALL 4 INSTANCES SEALED (axiom-clean):**
  `FormAdapter` + `FormAdapter.reachesRigidOrCameron` (any adapter ⟹ seal; char-2-ready, verified at `p=2`);
  **inst 1** affine-polar `affinePolarAdapter`; **inst 2** alternating `Alt(5,q)` `reachesRigidOrCameron_alternating`
  (`multiFormAdapter` + Plücker forms); **inst 3** half-spin `reachesRigidOrCameron_halfSpin` (`multiFormAdapter` + 10
  spinor quadrics); **inst 4** Suzuki `reachesRigidOrCameron_suzuki` (σ-twisted multi-form + `GF(q)^4↔𝔽₂^d` module
  bridge, `suzukiAdapter`). Each family = one `FormAdapter`; the multi-quadric families reduce to `Qs`+`hjoint` via
  `multiFormAdapter`; Suzuki reduces to the 5 σ-forms + the bridge + `suzuki_separates`.
- **✅ §9 combine / seam — DONE at the honest level (2026-07-04):** the group-pinning (`schemeAutGroup_coarse_eq_affineG`,
  all 4 families mod the named Skresanov citation `AffineSchemeTwoClosed`) + `routeC_polySupport` certificate
  (`RouteCSeam.lean`) + the cyclotomic dispatch (`RouteCSeam.lean`), all axiom-clean, after
  the **vacuity correction** (§9.0a). **★ `htransport` (L1) DISCHARGED (2026-07-05, `RouteCSeam.lean`,
  axiom-clean) — no carried atom remains** (4 lemmas: cross-graph `warmRefine_transport_iso` → `separatesAtBoundedBase_transport`
  + `separatesAtBoundedBase_affinePolar` → `reachesRigidOrCameron_viaSchurianRank3Affine_proved`; see item 3 above).
  **★ PORT DONE (2026-07-05):** the whole spine is in `build.sh` as `RouteCTransport`/`RouteCFormAdapters`/`RouteCSeam`/`RouteCNode4`.
  **★ L4 DONE (2026-07-05, `RouteCNode4.lean`):** affine-polar node-4 discharged with no `hFormCert`; multi-form Track B
  meta-composition landed (see NEXT-TASKS item 1). **★ C# runtime BUILT.** **Remaining:** promoting the scoped citations
  (`NondegQuadricDeterminesForm`, `JointVarietyDeterminesFamily`, `ConePreservingCollineationIsSemiSimilitude`,
  `AffineSchemeTwoClosed`) to full Lean proofs, or Track A (a multi-quadric pair-route) for a per-family coarse `SealDisj`.
  **No further family builds remain.**

**▶ VERIFY what's landed (fresh-reader notes).** The Route-C spine is now in `build.sh`, so verification is the
normal build + an axiom-checker file (the ported modules carry **no** inline `#print axioms` — that would print on every
build; the axiom check is done out-of-line):
- **Full build:** `bash scripts/build.sh` (serial, ~68s; ends `✔ serial build complete`, `exit=0`). The four Route-C
  modules build last: `RouteCTransport` → `RouteCFormAdapters` → `RouteCSeam` → `RouteCNode4`.
- **Axiom-clean check** (per gap: a scratch/temp file's `#print axioms` survives to stdout; a built `.olean` doesn't, so
  check out-of-line). Write a temp file that imports the module and prints axioms, then `cd GraphCanonizationProofs &&
  lake env lean /path/to/check.lean` (expect `[propext, Classical.choice, Quot.sound]` for each). NB always
  `cd GraphCanonizationProofs` first — a stray cwd gives a spurious `no such file`. Example:
  ```lean
  import ChainDescent.RouteCNode4
  open ChainDescent
  #print axioms reachesRigidOrCameron_viaAffineFormScheme_routeC   -- L4 (affine-polar, no hFormCert)
  #print axioms routeC_polySupport_of_adapter                      -- Track B engine (multi-form meta-support)
  #print axioms RouteC.Plucker.reachesRigidOrCameron_alternating   -- a family seal
  #print axioms reachesRigidOrCameron_viaSchurianRank3Affine_proved -- L1 seam (htransport proved)
  ```
- **Key decl homes:** the four seals + `FormAdapter` engine + multi-quadric bridges = `RouteCFormAdapters` (namespace
  `ChainDescent.RouteC`, sub-namespaces `Plucker`/`HalfSpin`/`Suzuki`); the cross-graph transport tower + `SchemeRealizes`
  + `separatesAtBoundedBase_transport` = `RouteCTransport`; `SealDisj` + dispatch + group-pinning + L1 seam capstone =
  `RouteCSeam`; L4 + Track B (`routeC_polySupport_*`, `formConeStab`) = `RouteCNode4`.
- C#: `cd GraphCanonizationProject.Tests && dotnet test --filter "FullyQualifiedName~RouteCF1Probe.F1_Recovers_TranslationGroup&Category!=LongRunning"`
  (fast, q=2,3; the `_Large` q=5 cases are `LongRunning`, ~5 min each — canonizer cost, not F1/A1).
- C# (Suzuki, NEW 2026-07-05): `dotnet test --filter "FullyQualifiedName~RouteCSuzukiProbe&Category!=LongRunning"`
  (fast: σ-form model + Clebsch negative-control degree signature + `AutOrder`); the `StandardGraph_IsVSz8_SRG`,
  `DegreeSignature_CubicNotQuadric`, `Confirm_Path_IsBasisInvariant_VSz8` cases are `LongRunning` (build the 4096-vertex
  graph, ~2 min each). Whole fast suite: `dotnet test --filter "FullyQualifiedName~RouteC&Category!=LongRunning"` (60/60).
- Python probes: `cd GraphCanonizationProofs && python3 route_c_reconstruct_probe.py` / `route_c_f1_probe.py` /
  `route_c_halfspin_probe.py` (spinor quadrics: dim 10, 𝔽₂ count 2296) / `route_c_suzuki_probe.py` (Suzuki: SRG params,
  5 σ-forms, joint zero=cone, base analysis) / `route_c_bootstrap_probe.py`.

**Quality bar (project-wide):** every Lean theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no fresh `axiom`; `native_decide` banned; full build green when ported. "Poly time" stays a **meta-argument** (the
project formalizes no runtime model): the structural deliverables are the seal disjunction `reachesRigidOrCameron`
(banked) and the *bounded-base discreteness object* Route C constructs; "poly" is the meta-claim over that + poly
per-node.

---

## 1. The claim, and why Route C

**The claim.** The abstract forms graph determines its defining form `Q` (up to scalar) by elementary linear algebra;
its automorphism group is then the **known** affine similitude group `AΓO^ε(Q)`, whose canonicalization is standard
poly group theory (Schreier–Sims — already implemented, §4). No WL-reaches-orbits, no count crux.

**Why Route C (the wall it dodges).** The direct routes canonize by driving refinement to the orbit partition. On the
forms graph the descent runs on the **similitude SRG**, whose relations record only the **isotropy class** of a
difference (zero / nonzero-isotropic / anisotropic), *not* the exact `Q`-value. Recovering the exact bilinear values
from bounded-base isotropy counts is the **node-4 WL-dimension wall** — open both ways, and it closed the direct build
(`ColorRefinesGramK` is circular; the round-2 colouring is a character-handleless "count of counts"; the FLAG lead is
negative — recovery doc §9.8.9). Route C reads `Q` off the cone **directly** (the cone is an iso-invariant of the
graph; the degree-2 form vanishing on it is canonical up to scalar), so it never touches that wall.

**Where it sits.** Banked quasipoly seal `AffinePolarSeal.reachesRigidOrCameron_affinePolar` = the floor (correctness).
Route C = the poly-cost upgrade for the forms-graph residue. It is a **larger build + a behavioural change** (a
structure-recovery pre-processor); pursue it *because* the lighter WL route stalled, not before.

---

## 2. Knowledge foundation

### 2a. The object
- **Graph.** `V = K^d` (`K = 𝔽_q`, `q = p^e`, `d = 2m`); adjacency `Q(x − y) = 0` for a nondegenerate quadratic form
  `Q` of type `ε` — the affine-polar forms graph `VO^ε_{2m}(q)`. A translation (Cayley) scheme ⟹ vertex-transitive,
  schurian, primitive rank-3 SRG.
- **Automorphisms.** `Aut = ` translations `⋊ ΓO^ε(Q)` (affine similitudes: linear maps `g` with `Q(gx) = μ(g)·σ(Q(x))`
  for a scalar `μ` and a field automorphism `σ`; for prime `q`, just `GO^ε(Q)`, no field twist). `|Aut|` is huge (e.g.
  `VO⁻₄(3)`: `233280 = 3⁴·|GO⁻₄(3)|`) — the graph is far from rigid, which is *why* the harvest keeps branching small.
- **The two forms `make_Q` uses** (probe ground truth): `ε=+1`: `Σᵢ x_{2i}x_{2i+1}` (hyperbolic); `ε=−1`:
  `Σ x_{2i}x_{2i+1} + x_{d-2}² − g·x_{d-1}²` with `g` = least non-square (elliptic).
- **Skresanov isolation.** The seal's residue is the schurian affine slice `{1-dim cyclotomic (cited) + forms-graphs
  (c)–(f)}`; Route C's recovery is needed on (c)–(f) `{affine-polar / alternating / half-spin / Suzuki–Tits}`.

### 2b. Why the cone determines `Q` (the algebra that dodges the wall)
The connection set from the origin is the punctured isotropic cone `C = {x ≠ 0 : Q(x) = 0}`. The homogeneous degree-2
forms vanishing on `C` form a vector space; for a nondegenerate quadric with `d ≥ 3` and non-tiny `q` that space is
**1-dimensional = ⟨Q⟩** (a classical finite-geometry fact; probe-confirmed dim `= 1` with no exceptions in range).
So `Q` is recovered by ONE linear solve over the `d(d+1)/2` degree-2 monomials — poly, non-circular (no WL, no orbits).
The cone only fixes `Q` **up to scalar `μ`**, but that is exactly right: `O(Q) = O(μQ)` and `GO(Q) = GO(μQ)`, so the
recovered object is well-defined, and in the refined colouring the global `μ` cancels in every comparison.

### 2c. The honest subtlety — isometry scheme vs. the given similitude graph
The landed `reachesRigidOrCameron_viaOrthogonalForm` (§4) seals `affineScheme (isometryGroup Q)` — the **isometry**
scheme `O(Q)`, whose relations are the **exact** `Q`-value of a difference. But the *given graph* is
`affineScheme (similitudeGroup Q)` — the **similitude** scheme `GO(Q)`, whose relations are only the isotropy class
(`∃ g∈GO(Q), g(u−t)=u'−t ⟺ isoClass(u−t)=isoClass(u'−t)`). At any bounded base the isotropy profile does **not**
jointly-separate — that is the stall. So Route C's load-bearing new content is **not** "invoke `viaOrthogonalForm`";
it is:

> **The recovered form `Q` refines the similitude graph to the isometry scheme.** Colour each pair `(t, z)` by `Q(z − t)`
> (well-defined up to the *global* scalar `μ`, which cancels in comparisons). That refined colouring is (i)
> **iso-invariant** (a graph iso carries the cone to the cone, hence `Q` to a scalar multiple), and (ii) **discretizes
> at a spanning base** via `coords_determine` / `spanning_sameExactGram_determines`.

`coords_determine` and the spanning generalization are landed; the refinement bridge + its iso-invariance are the new
lemmas (A3 / F4 in §6).

---

## 3. The architecture — 1 engine + N adapters (the merge)

The families **merge at the "recovered structure → iso-invariant refining data on `V`" boundary**. Once a family hands
the generic engine (a) the recovered form as a colouring of pairs and (b) a "form-values-at-a-base determine the vertex"
certificate, everything downstream is shared. So Route C is **one generic engine + a small `IFormStructure` interface
with 4 implementations** — *not* four separate objects, and *not* one monolith with four branches.

```
        ┌─────────────── GENERIC ENGINE (1 copy, all families) ───────────────┐
 graph ─►  F1 recover additive/affine structure  (T = O_p(Aut), the socle)      │  ← family-agnostic
        │  F2 [q=pᵉ] recover 𝔽_q-scalar structure  (Frobenius/ΓL seam)          │  ← family-agnostic
        │                         │                                             │
        │      IFormStructure.RecoverForm(graph, V) ──► φ         ◄── family     │  ← family hook 1
        │                         │                                             │
        │  refine pairs by φ  (iso-invariant colouring; global scalar cancels)  │
        │      IFormStructure.Separates(φ, base) ──► certificate  ◄── family     │  ← family hook 2
        │                         │                                             │
        │  canonical spanning base + discretize ──► canonical labelling         │
        │     (OR IFormStructure.AutGens(φ) ──► existing Schreier–Sims → |Aut|)  │  ← family hook 3 (|Aut| side)
        └──────────────────────────────────────────────────────────────────────┘
```

**Merge boundaries — what is shared vs. family-specific:**

| layer | shared (1 impl) | family-specific (N adapters) |
|---|---|---|
| additive/affine recovery (F1) | ✅ `T = O_p(Aut)` — identical for all | — |
| 𝔽_q-scalar recovery (F2) | ✅ | — |
| the generic engine (refine-by-φ, canonical base, discretize) — F3/F5 | ✅ | — |
| Schreier–Sims / `PermutationGroup.cs` | ✅ (exists) | — |
| iso-invariant base construction, direction-blind lex-min | ✅ | — |
| **`RecoverForm`** (which variety / linear system) | — | **the form/geometry object** |
| **`Separates`** (the `coords_determine` analog) | — | **the form's nondegeneracy** |
| **`AutGens`** (classical-group generators; only for the \|Aut\| side) | — | **the classical group** |

Affine-polar / alternating / half-spin share ~all of `RecoverForm` and `Separates` (all recover a bilinear/quadratic
form and separate by polar-nondegeneracy). **Suzuki–Tits is the one genuinely-different adapter** (non-form σ-twisted
ovoid, char-2 — same interface, different internals; folds into the char-2 track, plan §11.5).

---

## 4. The preexisting foundation Route C rides on (exact names)

### Lean — LANDED & AXIOM-CLEAN (the back-half + the generic spine)
All in `GraphCanonizationProofs/ChainDescent/` unless noted. Index rows = `GraphCanonizationProofs/PublicTheoremIndex.md`.

| name | location | what it gives Route C |
|---|---|---|
| `affineScheme (G₀) (hneg)` | `CascadeAffine.lean:2204` | **the generic merge point** — the affine scheme of any `G₀ ≤ GL(V)` with `−1∈G₀`; `SchurianScheme (p^d)` |
| `discrete_affineScheme_of_jointSeparates` | `CascadeAffine.lean:2427` | **generic** — a base `T` that jointly-separates ⟹ `warmRefine` from `T` is `Discrete`. The only family input is the separation hypothesis `hsep` |
| `coords_determine` | `CascadeAffine.lean:2640` (idx 1211) | `Q` nondeg polar + `Q v`, `Q(v−eᵢ)` agree with `v'` ⟹ `v = v'` — **the `Separates` certificate for the quadratic case** |
| `coords_determineK` | `FieldGeneric.lean:87` | the field-generic (`[Field K]`) version of `coords_determine` |
| `spanning_sameExactGram_determines` | `ScratchBranchDepth.lean:65` | generalizes `coords_determine` to any **spanning** base (not just the standard frame) |
| `spanning_exactQ_determines` | `ScratchDominatorForms.lean:67` | the affine-isometry-scheme form of the above (Q-value-of-difference data) |
| `isometryGroup Q` | `CascadeAffine.lean:2656` | `O(Q) = {g : ∀x, Q(gx)=Q(x)}` as a `Subgroup` |
| `neg_mem_isometryGroup` | `CascadeAffine.lean:2678` | `−1 ∈ O(Q)` (the `hneg` for `affineScheme`) |
| `frameBase`, `frameBase_card_le` | `CascadeAffine.lean:2684`,`:2688` (idx 1215-6) | the `{0,e₁,…,e_d}` base and `card ≤ d+1` |
| `reachesRigidOrCameron_viaOrthogonalForm` | `CascadeAffine.lean:2704` (idx 1217) | **the back-half** — `O(Q)` (nondeg) discretizes at `frameBase` and seals via `viaSpielman`. NB: **isometry** scheme, not the given similitude graph (§2c) |
| `RouteC.coords_determine_spanning` | `RouteCFormAdapters.lean` (**Route C, NEW, axiom-clean**) | spanning generalization of `coords_determine`: `Q`-values at any *spanning* base `S` (`span S = ⊤`) determine the vertex |
| `RouteC.reachesRigidOrCameron_viaOrthogonalForm_spanning` | `RouteCFormAdapters.lean` (**Route C, NEW, axiom-clean**) | spanning generalization of `viaOrthogonalForm`: `O(Q)` discretizes at any base `T∋o` whose differences `{t̄−ō}` span — the iso-invariantly-chosen base Route C needs |
| `RouteC.isometryScheme_refines_similitudeScheme` | `RouteCFormAdapters.lean` (**Route C A3 brick 1, NEW, axiom-clean**) | `O(Q)≤GO(Q)` ⟹ the isometry scheme refines the given similitude graph (finer `relOfPair`) — the recovered form is consistent, not fabricated |
| `RouteC.NondegQuadricDeterminesForm` | `RouteCFormAdapters.lean` (**Route C — the exact carried classical citation, NEW**) | scoped premise (`p≠2`, `4≤d`, `Q` nondeg): same isotropic cone ⟹ scalar-multiple form (A1's `vanishDim=1` uniqueness). The EXACT true statement (unrestricted form false at `d=3,q=3`); Hirschfeld / projective Nullstellensatz; carried like `Theorem41Statement` |
| `RouteC.similitude_colouring_equivariant`, `RouteC.similitude_conePreserving` | `RouteCFormAdapters.lean` (**Route C F4 bricks, NEW, axiom-clean**) | a form similitude carries the difference colouring by one scalar (`Q'(gu−gt)=μ·Q(u−t)`) + preserves the cone — pure linearity |
| `RouteC.recoveredForm_colouring_equivariant` | `RouteCFormAdapters.lean` (**Route C F4 capstone, NEW, axiom-clean**) | graph-iso cone-preservation + `NondegQuadricDeterminesForm` ⟹ the recovered difference colouring is equivariant (iso-invariant up to global scalar) — the "discrete ⟹ canonical" link |
| `RouteC.frobVec`, `RouteC.frobVec_sub`, `RouteC.semisimilitude_colouring_equivariant` | `RouteCFormAdapters.lean` §F2 (**Route C F2 bricks, NEW, axiom-clean**) | coordinate-wise Frobenius σ̂ + its additivity + the semilinear equivariance identity `Q'(M(σ̂u)−M(σ̂t))=μ·σ(Q(u−t))` |
| `RouteC.ConePreservingCollineationIsSemiSimilitude` | `RouteCFormAdapters.lean` §F2 (**Route C F2 cited premise, NEW**) | scoped (`(2:K)≠0`, `4≤d`): cone-preserving collineation `g` ⟹ `g=M∘σ̂` semi-similitude (fundamental thm of projective geometry + `NondegQuadricDeterminesForm`; carried) |
| `RouteC.recoveredForm_colouring_equivariant_semilinear` | `RouteCFormAdapters.lean` §F2 (**Route C F2 capstone, NEW, axiom-clean**) | q=pᵉ: the recovered form is iso-invariant up to scalar **and** field auto σ — F4 for the semilinear (ΓL) case; `q=p` = the `σ=id` specialization |
| `RouteC.FormAdapter`, `RouteC.FormAdapter.reachesRigidOrCameron` | `RouteCFormAdapters.lean` §F3 (**Route C engine interface, NEW, axiom-clean**) | the `IFormStructure` interface (`G₀` + `−1∈G₀` + bounded base + `separates`) + the shared engine theorem (any adapter ⟹ the seal). 1 engine, N family adapters |
| `RouteC.affinePolarAdapter` | `RouteCFormAdapters.lean` §F3 (**Route C instance 1, NEW, axiom-clean**) | affine-polar `VO^ε` as a `FormAdapter` (`G₀=O(Q)`, frame base, `coords_determine` certificate) — validates the interface, reproduces `viaOrthogonalForm` |
| `RouteC.coords_determine_multi`, `RouteC.coords_determine_multi_spanning` | `RouteCFormAdapters.lean` (**Route C alternating-family `separates` core, NEW, axiom-clean**) | a *family* `{Q_k}` with trivial common polar-radical determines the vertex from the joint value-profile (frame / spanning base) — the multi-quadric `separates` for `Alt(n≥5,q)` (Plücker quadrics), generalizes `coords_determine` |
| `RouteC.multiFormAdapter` | `RouteCFormAdapters.lean` (**Route C alternating engine hookup, NEW, axiom-clean**) | a form family `{Q_k}` with joint nondegeneracy ⟹ a `FormAdapter` (`G₀ = ⨅ₖ O(Q_k)` the joint isometry group, frame base, `coords_determine_multi` certificate). `affinePolarAdapter` = the `ι=Unit` case |
| `RouteC.Plucker.{Pf0..Pf4, pluckerForms, plucker_hjoint}` | `RouteCFormAdapters.lean §Plucker` (**Route C alternating instance, NEW, axiom-clean**) | the concrete 5 sub-Pfaffian quadrics on `𝔽_p^10` (via `linMulLin`) + their joint nondegeneracy `plucker_hjoint` (the sole geometric input) |
| `RouteC.Plucker.alternatingAdapter`, `RouteC.Plucker.reachesRigidOrCameron_alternating` | `RouteCFormAdapters.lean §Plucker` (**Route C instance 2 CAPSTONE, NEW, axiom-clean**) | `Alt(5,q)` as a sealed `FormAdapter` + the rigid-or-Cameron seal — the **first concrete non-quadratic (multi-form) Route-C family, end to end** |
| `RouteC.affineScheme_refines_of_le` | `RouteCFormAdapters.lean` (**generic refinement bridge, NEW, axiom-clean**) | `H ≤ G` (both `∋ −1`) ⟹ `affineScheme H` refines `affineScheme G`. The reusable core of every Route-C refinement brick; `isometryScheme_refines_similitudeScheme` is now its one-line corollary |
| `RouteC.jointConeStab`, `RouteC.neg_mem_jointConeStab`, `RouteC.iInf_isometryGroup_le_jointConeStab` | `RouteCFormAdapters.lean` (**multi-quadric bridges, NEW, axiom-clean**) | the **graph-intrinsic** setwise stabilizer of the joint cone `{v : ∀k, Q_k v=0}` (= the connection set) as a `Subgroup` + `−1∈` it + `⨅ₖ O(Q_k) ≤` it. The multi-form analog of `similitudeGroup`, defined from the graph not the form |
| `RouteC.multiIsometryScheme_refines_coneScheme` | `RouteCFormAdapters.lean` (**brick-1-multi, NEW, axiom-clean**) | the recovered joint-isometry scheme `⨅ₖ O(Q_k)` refines the cone-stabilizer scheme — the multi-form refinement leg (analog of `isometryScheme_refines_similitudeScheme`), tied to the actual graph via `jointConeStab`. `alternating_refines_coneScheme` = the concrete `Alt(5,q)` application |
| `RouteC.multiSimilitude_colouring_equivariant`, `RouteC.JointVarietyDeterminesFamily`, `RouteC.recoveredFamily_colouring_equivariant`, `RouteC.recoveredFamily_partition_isoInvariant` | `RouteCFormAdapters.lean` (**F4-multi, NEW, axiom-clean**) | the multi-form iso-invariance leg: provable equivariance brick (colouring transports by global `Φ`) + the scoped carried citation `JointVarietyDeterminesFamily` (joint variety determines the family up to invertible `Φ`; multi-form sibling of `NondegQuadricDeterminesForm`) + capstone (injective `Φ`) + partition-invariance payoff (`Φ` cancels in comparisons) |
| `RouteC.polar_linMulLin` | `RouteCFormAdapters.lean` (**reusable primitive, NEW, axiom-clean**) | `polar (linMulLin f g) x y = f x·g y + f y·g x` — the polar of a Clifford-term-sum quadric (Plücker / spinor forms) |
| `RouteC.HalfSpin.{S0..S9, spinorForms, S0_polar..S4_polar, spinor_hjoint}` | `RouteCFormAdapters.lean §HalfSpin` (**Route C instance 3, NEW, axiom-clean**) | the 10 concrete D₅ spinor quadrics on `𝔽_p^16` (validated by `route_c_halfspin_probe.py`: dim=10, exact 𝔽₂ count 2296, radical 0) + their joint nondegeneracy `spinor_hjoint` (from the 5 quadruple forms by coordinate isolation) |
| `RouteC.HalfSpin.{halfSpin_reduction, spinAdapter, reachesRigidOrCameron_halfSpin, halfSpin_refines_coneScheme}` | `RouteCFormAdapters.lean §HalfSpin` (**Route C instance 3 CAPSTONE, NEW, axiom-clean**) | half-spin as a sealed `FormAdapter` (`spinAdapter`) + the rigid-or-Cameron seal (`reachesRigidOrCameron_halfSpin`) + brick-1 (`halfSpin_refines_coneScheme`) — instance 3 DONE, full instance-1 parity |
| `RouteC.Suzuki.{ovoidC, SF0..SF4, suzukiForms, four_eq_zero, suzukiForms_ovoid, suzukiForms_infty, suzukiForms_homog}` | `RouteCFormAdapters.lean §Suzuki` (**Route C instance 4 — the σ-twisted forms rederived, NEW, axiom-clean**) | over a char-2 `CommRing K` with a Tits endo `σ` (`σ∘σ=(·)²`): the 5 σ-twisted Suzuki forms + proofs they cut the cone (vanish on the ovoid + at infinity + σ-twisted homogeneous). De-risk-validated (`route_c_suzuki_probe.py`, joint zero=cone exact) |
| `RouteC.Suzuki.{SFv, PreservesForms, SuzukiFormsDetermine, preservesForms_eq, suzuki_separates}` | `RouteCFormAdapters.lean §Suzuki` (**Route C instance 4 — the σ-twisted `separates`, NEW, axiom-clean**) | the σ-twisted analog of `coords_determine_multi`'s `separates`: the joint-isometry orbit-profile at the frame ⟹ (via `preservesForms_eq` + the scoped citation `SuzukiFormsDetermine`) `v=v'`. `SuzukiFormsDetermine` is carried (false for small `K`, true for `GF(2^{2e+1})`; `Sz(q)` 2-transitivity) |
| `RouteC.Suzuki.{SFbar, suzukiG₀, preservesForms_of_mem_G₀, neg_mem_suzukiG₀, suzukiBase, suzukiBase_card_le, suzukiAdapter, reachesRigidOrCameron_suzuki}` | `RouteCFormAdapters.lean §Suzuki` (**Route C instance 4 CAPSTONE — module bridge + seal, NEW, axiom-clean**) | the `GF(q)^4↔𝔽₂^d` bridge via an additive iso `Ψ` (no `ZMod 2`-module on `K` needed) → `suzukiG₀` (joint isometry, subgroup of `Fin D→ZMod 2 ≃ₗ …`) + `neg_mem` free (char 2) + `suzukiBase` (`≤5`) + `separates` transported to `suzuki_separates` ⟹ `suzukiAdapter` + the seal `reachesRigidOrCameron_suzuki`. **Instance 4 SEALED (modulo `SuzukiFormsDetermine`); all 4 families done** |
| `similitudeGroup Q`, `neg_mem_similitudeGroup`, `isometry_le_similitude` | `CascadeAffine.lean:2746`,`:2766`,`:2771` | `GO(Q)` = the given graph's linear group; `O(Q) ≤ GO(Q)` |
| `reachesRigidOrCameron_viaSpielman` | `Cascade.lean:4690` | the wrapper: a bounded-base discreteness witness ⟹ the seal disjunction (Cameron-free sub-exp floor) |
| `reachesRigidOrCameron_viaAffineFormScheme` | `CascadeAffine.lean:2057` (idx 1207) | Stage-A capstone; the seal wiring for the forms-graph residue (context) |
| `orbMk_affine_eq_iff`, `affineScheme_relOfPair_eq_iff`, `affineScheme_relOfPair_translation` | `CascadeAffine.lean:2218`,`:2281`,`~:2438` | the affine-scheme relation↔difference-orbit dictionary (used to state the refined colouring) |
| `AffinePolarSeal.reachesRigidOrCameron_affinePolar` | `AffinePolarSeal.lean:410` | the **banked quasipoly seal** (in `build.sh`) — the floor Route C upgrades |

> **⚠ Do NOT build on these (superseded/false at the plain frame, idx 1221-1226,1237):**
> `SimilitudeFrameSeparates`, `reachesRigidOrCameron_viaSimilitudeForm`, `…viaCountsDetermineFrameQ`,
> `…viaIsotropyCounts`. They ask the similitude scheme to separate at the *frame*, which is FALSE for minus-type (the
> node-4 stall). Route C avoids them by recovering `Q` and refining to the isometry scheme (§2c), not by counting.

### C# — EXISTS (the group back-end + the seam + the pre-processor template)
In `GraphCanonizationProject/`.

| file | what it gives Route C |
|---|---|
| `PermutationGroup.cs` | **full Schreier–Sims** — stabilizer chain, `AddGenerator`, `Order`, `Contains`, `Orbit`, `BasePoints`, `IsAbelian`, `IsElementaryAbelian`. **+ Route-C F1 ops (NEW 2026-07-03):** `RegularNormalPSubgroup(p)` (the socle/translations), `NormalClosure`, `Elements`, `HasExponentDividing`, `Perm.Order`/`Pow` |
| `AffineStructureRecovery.cs` | **Route C, NEW 2026-07-03** — `Recover(aut, p, origin)` = F1's entry point: socle `T` + `Dim` + vertex→`(𝔽_p)^Dim` coordinate map (via `T`'s regular action). Confirmed by `RouteCF1Probe.cs` |
| `QuadraticFormRecovery.cs` | **Route C, NEW 2026-07-03 (A1)** — `RecoverForm(adj, n, aff)`: recovers `Q` up to scalar by the degree-2 kernel solve on the cone; `RecoveredForm.Evaluate`. The quadratic family's `RecoverForm`. Odd-q; confirmed to reconstruct the whole graph |
| `ITransversalOracle.cs` | the T-C seam (`Classify(n, adj, targetCell, path, knownGroup) → representatives`) — where a Route-C oracle plugs in |
| `CascadeOracle.cs` | the all-reps oracle (returns the whole cell; harvest prunes a-posteriori) — the current default |
| `ChainDescent.cs` | the harness: cross-branch harvest + prune (`CoveredByPathFixingAut`, ~`:589`), deferral selector (~`:251-281`) |
| `Option2ExtractionProbe.cs`, `TwistConstruction.cs` | **the pre-processor template** — Option 2's Layer D (the F₂/rigid mirror). Route C's engine is the *symmetric-form clone* of this architecture (§6) |

---

## 5. The probes (what is already validated, and how to re-run)

All in `GraphCanonizationProofs/` (pure Python, `python3 <file>`; reuse `model_gap.py` helpers `make_Q`/`sub`/`polar`/
`isoclass`/`add`).

- **`route_c_reconstruct_probe.py` — A1 (form recovery).** For each `(ε,d,q)`, builds the isotropic cone and computes
  the rank of the degree-2 vanishing system. **Result: `vanishDim = 1` everywhere** (ε=±, d=4,6,8, q=3,5,7,11) ⟹ `Q`
  reconstructible up to scalar by one linear solve, no small-`q` exception. (Odd `q`; char-2 is a separate track — over
  `𝔽_{2^k}` squaring collapses degree, so the degree-2 vanishing space differs; handled by the Arf/char-2 substrate.)
- **`route_c_f1_probe.py` — F1 (additive-structure recovery).** Builds `VO^ε₄(q)` with true translations + monomial
  isometries, **scrambles** by a random relabelling, then recovers `O_p` via normal closures with **no ground-truth
  reference**. **Result (VO^ε₄(3), VO^ε₄(5), both types): `Op == T` exactly, regular, elementary-abelian, and the
  recovered coordinates give `coneVanishDim = 1`** ⟹ recovery is method-correct, scramble-invariant, and hands A1 a
  valid coordinatization. (Odd `q`: `−1` is a `p'`-element so `G₀` is a `p'`-group and `O_p(G)=T` is clean; char-2
  recovers `T` the same way but needs Aut's `p'`-part, e.g. `S₅` for Clebsch.)
- **`RouteCF1Probe.cs` — F1 + A1 against the REAL harness (C#, `GraphCanonizationProject.Tests/`).** Builds `VO^ε₄(q)`,
  runs the actual chain-descent canonizer, and confirms end-to-end (via the **production** methods) that (I)
  `CanonResult.ResidualGroup` contains the translations and has full `|Aut|`, (II) `AffineStructureRecovery.Recover`'s
  translation group equals `T` **exactly** (ground-truth), regular + elementary-abelian, and (III)
  `QuadraticFormRecovery.RecoverForm`'s `Q` + those coordinates **reconstruct the entire graph** (`Q(coords[x]−coords[y])
  =0 ⟺ x~y`, 0 mismatches). **All pass** (q=2,3 fast, both types; q=5 `LongRunning`). Confirms the harness↔F1↔A1 chain.
- **`route_c_halfspin_probe.py` — the D₅ half-spin spinor-quadric de-risking (2026-07-03).** Generates genuine
  pure spinors via the char-free big-cell Pfaffian formula and empirically fits the degree-2 vanishing ideal, then
  validates: dim `= 10` (q=3,5,7,11), **exact 𝔽₂ zero-locus count `= 2296` = the spinor-variety target** (`1+(q−1)∏₁⁴(qⁱ+1)`),
  𝔽₃ Monte-Carlo match (z=0.10), and **joint polar radical `= 0`** (= the Lean `hjoint`, provable from the 5 quadruple
  forms). Prints the 10 explicit forms (§6). Caught that the naive moment map gave the wrong forms — the reason to
  de-risk empirically, not template. The port reference for instance 3.
- **`route_c_suzuki_probe.py` — the Suzuki–Tits (f) de-risk (2026-07-04, q=8).** Builds GF(8) + the Tits
  endomorphism `σ` + the ovoid + cone + VSz(8) (Cayley on 𝔽₂¹², adjacency = 12-bit XOR ∈ cone). Validates the object
  (`σ²=Frob`, `|O|=65`, `|cone|=455`, SRG(4096,455,6,56) — ovoid formula `c=ab+σ(a)a²+σ(b)` correct) and measures the
  `separates` base three ways: **plain-cone direct-profile > 30 (rank-3 ⟹ ≥log₂n ⟹ quasipoly)**, **iterated
  refinement = 4**, and — decisive — **joint σ-form-value profile injective at base 4 ≤ d+1 (POLY)**. Also derives the
  poly object: a **5-dim family of σ-twisted forms** whose joint zero = cone exactly ⟹ Suzuki = **multi-(σ)-form
  adapter** (σ-twisted sibling of alternating/half-spin). §6 "Suzuki".
- **`route_c_bootstrap_probe.py` — the meta-poly bootstrapping crux (§7a).** Confirms the isotropic-line geometry through
  `o` is recoverable from **adjacency alone** (no `Aut`): the local invariant `|N(o)∩N(x)∩N(y)|` **perfectly separates**
  collinear from non-collinear isotropic triangles (all VO^± `d=4,6` `q=3,5`), and the recovered lines' directions **span
  `V`**. This is the Aut-free enabling primitive that de-circularizes F1's coordinatization.
- **Supporting (from the direct route, still relevant):** `model_gap.py` (the isoClass scheme + orbit/refinement
  helpers), `factorization_probe.py`/`flag_stall_probe.py` (the node-4 stall evidence that motivates Route C).

---

## 6. The build plan

### Foundation (must exist before the family builds)

| # | piece | side | status / notes |
|---|---|---|---|
| **F1** | **Additive/affine recovery** — `T = O_p(Aut)` (the socle), a basis → coordinates, any vertex → origin | C#+Lean | **✅ CONFIRMED + PRODUCTIONIZED (2026-07-03).** Confirmed against the REAL harness (`RouteCF1Probe.cs`): recovers `T` exactly (ground-truth), regular + elementary-abelian, coordinatizes the cone (`vanishDim=1`) — VO^ε₄(q), q=2,3,5, both types; char-agnostic (full `Aut` delivered). **Production code landed:** general group ops on `PermutationGroup.cs` (`RegularNormalPSubgroup(p)`, `NormalClosure`, `Elements`, `HasExponentDividing`, `Perm.Order`/`Pow`) + `AffineStructureRecovery.Recover` (coordinatization); the probe now exercises the production path (all pass; 26 existing `PermutationGroup` tests green). "`soc = O_p = T`" = the affine-primitive **socle theorem** (cite). Remaining: the Lean side (F4 iso-invariance) + `q=pᵉ` (F2). |
| **F2** | **𝔽_q-scalar recovery** (q=pᵉ) — recover the field/Frobenius structure (the ΓL/semilinear seam) | C#+Lean | **◑ SEMILINEAR CORE LANDED (2026-07-03, axiom-clean, `RouteCFormAdapters.lean` §F2):** `recoveredForm_colouring_equivariant_semilinear` — a graph iso over 𝔽_q is 𝔽_p-**semilinear** (`g = M∘σ̂`), so the recovered form transports up to scalar **and** field auto σ: `Q'(gu−gt)=μ·σ(Q(u−t))`. Bricks `frobVec`/`frobVec_sub`/`semisimilitude_colouring_equivariant` (provable) + cited `ConePreservingCollineationIsSemiSimilitude` (fundamental thm of proj. geometry, carried). The `q=p` case = the `σ=id` specialization. **𝔽_q-structure RECOVERY** (getting the field) is subsumed by geometric coordinatization (§7a/R1: Buekenhout–Shult recovers PG over 𝔽_q). Remaining: C# field recovery (with R1) |
| **F3** | **`IFormStructure` interface + generic engine** (refine-by-φ, canonical base, discretize) | C#+Lean | **◑ LEAN INTERFACE LANDED (2026-07-03, axiom-clean, `RouteCFormAdapters.lean`):** `FormAdapter` (bundles `G₀` + `−1∈G₀` + a bounded base + the `separates` certificate) + `FormAdapter.reachesRigidOrCameron` (the shared engine theorem: any adapter ⟹ the seal, family-agnostic) + `affinePolarAdapter` (instance 1, validates non-vacuity, reproduces `viaOrthogonalForm`). Each family now = **one `FormAdapter`** (supply only `separates`). C# side (thin merge point) still to build |
| **F4** | **Iso-invariance of the recovered `φ`** — the `forcedNode_relabel` analog: `RecoverForm` is relabeling-equivariant up to scalar | Lean | **✅ EQUIVARIANCE CORE LANDED (2026-07-03, axiom-clean, `RouteCFormAdapters.lean`):** `recoveredForm_colouring_equivariant` (+ bricks `similitude_colouring_equivariant`/`similitude_conePreserving`). Rests only on `NondegQuadricDeterminesForm` — **discharged as an exact scoped citation** (= A1's finite-geometry uniqueness; F4 and A1-Lean unify). Not vacuous (scoped `p≠2`/`d≥4`, exactly the true range) |
| **F5** | **Generic seal→poly spine** — `RecoverForm ⟹ refined scheme ⟹ discrete_affineScheme_of_jointSeparates ⟹ viaSpielman` | Lean | **downstream all landed & generic**; only the A3 refinement bridge is new |

### Instance 1 — affine-polar `VO^ε` (proves the whole spine)

| # | piece | status |
|---|---|---|
| **A1** | `RecoverForm` = solve the degree-2 vanishing system on the cone | **✅ CONFIRMED + PRODUCTIONIZED (2026-07-03, `QuadraticFormRecovery.RecoverForm`):** recovers `Q` up to scalar by one kernel solve on F1's coordinates; the recovered `Q` + coords **reconstruct the entire graph** (`Q(coords[x]−coords[y])=0 ⟺ x~y`, **0 mismatches**, VO^±₄(3)). Odd-q (returns null in char-2). Lean side = a finite-geometry nondegeneracy lemma (`⟨Q⟩` = the vanishing space) |
| **A2** | `Separates` = `coords_determine` / `spanning_sameExactGram_determines` | **LANDED, axiom-clean** |
| **A2⁺** | the spanning back-half — `RouteC.coords_determine_spanning` + `RouteC.reachesRigidOrCameron_viaOrthogonalForm_spanning` (isometry scheme discretizes at any iso-invariantly-chosen spanning base) | **✅ LANDED 2026-07-03, axiom-clean** (`RouteCFormAdapters.lean`, in `build.sh`) |
| **A3** | **the refinement bridge** — recovered `Q` upgrades the similitude graph to the isometry scheme, which `viaOrthogonalForm_spanning` discretizes | **◑ brick 1 LANDED (2026-07-03, axiom-clean, `RouteCFormAdapters.lean`):** `isometryScheme_refines_similitudeScheme` — `O(Q)≤GO(Q)` ⟹ the isometry scheme (exact-`Q` relations) refines the given similitude graph (isotropy-only). The consistency half. Remaining A3 content = the discreteness-transfer, now discharged by **F4** (`recoveredForm_colouring_equivariant`, ✅ landed 2026-07-03) — the iso-invariance that makes "discrete ⟹ canonical" |
| **A4** | `AutGens` = `GO(Q)` generators (reflections) → existing `PermutationGroup` (only for the \|Aut\| side) | Schreier–Sims exists; generator list is standard classical-group data |

Instance 1 forces F1/F3/F4/F5 into existence, so it is **most of the total work**; the other three families then
reduce to writing their `IFormStructure` implementation.

### Instances 2–4 — reuse the engine, write only the adapter (plan §11.4/§11.5)
**The Lean interface `FormAdapter` (F3) is now LANDED** — each family reduces to **one `FormAdapter` instance**, i.e.
supplying its `G₀`, base, and `separates` certificate; `FormAdapter.reachesRigidOrCameron` then seals it for free.
The genuine per-family content is exactly `separates` (+ identifying `G₀`):
- **Alternating (d) — SCOPED + build STARTED (2026-07-03).** `Alt(n,q)`: vertices `Λ²(𝔽_q^n)` (alternating
  matrices), adjacency `rank(A−B)=2`. **Two regimes:**
  - **`n=4` is affine-polar in disguise:** `Λ²(𝔽_q^4)≅𝔽_q^6`, `rank<4 ⟺ Pf=0`, and the Pfaffian `Pf=A₁₂A₃₄−A₁₃A₂₄
    +A₁₄A₂₃` is a single **nondegenerate quadratic form** ⟹ `Alt(4,q)=VO⁺₆(q)`, already covered by `affinePolarAdapter`
    (`Q:=Pf`). **Not a new family.** (Buildable now: define `Pf`, prove nondeg, instantiate — deferred, low value.)
  - **`n≥5` is the genuinely-new family — MULTI-QUADRIC:** `rank≤2` is cut out by the **Plücker quadrics** (4×4
    sub-Pfaffians; 5 for `n=5`), so the connection set is their **joint cone** (Grassmann `G(2,n)`). Each Plücker form
    is individually degenerate; only *jointly* do their polar forms separate. **✅ `Alt(5,q)` FULLY SEALED
    (2026-07-03, axiom-clean, `RouteCFormAdapters.lean §Plucker`):** the concrete 5 sub-Pfaffians `Pf₀..Pf₄` on `𝔽_p^10`
    (built via `linMulLin`), their joint nondegeneracy `plucker_hjoint` (`Pf₀` isolates coords `4..9`, `Pf₁` isolates
    `1,2,3`, `Pf₂` isolates `0`), assembled by `multiFormAdapter` into `alternatingAdapter`, sealed by the capstone
    **`reachesRigidOrCameron_alternating`** — the first concrete **non-quadratic (multi-form)** Route-C family, end to
    end. (Honest scope: the seal is for `affineScheme(⨅ₖ O(Pf_k))`; that this scheme *is* `Alt(5,q)` is the modeling
    claim, same status as `affinePolarAdapter` modeling `VO^ε`.) The rank-3 alternating forms graph is exactly
    `Alt(4,q)` [=affine-polar] + `Alt(5,q)` [sealed], so **instance 2 (alternating) is DONE — now at full
    instance-1 parity** (all three legs: seal + brick-1-multi `alternating_refines_coneScheme` +
    F4-multi `recoveredFamily_colouring_equivariant`, the last resting on the carried `JointVarietyDeterminesFamily`).
    *Was Medium — landed.*
- **Half-spin (e) — SCOPED + reduction LANDED + ✅ SPINOR QUADRICS DE-RISKED & VALIDATED (2026-07-03).** The
  **D₅ half-spin** action: `Spin₁₀(q)` on the 16-dim half-spin module `𝔽_q^16`, rank 3. Connection set = the
  **pure-spinor cone** (spinor variety `S₅ ⊂ P^15`), cut out by **10 quadratic equations** (the D₅ vector rep = the
  Berkovits SO(10) pure-spinor constraint `λΓ^aλ=0`). Another MULTI-QUADRIC family — reuses `multiFormAdapter` +
  `coords_determine_multi` + the just-landed generic bridges (**no new engine, no new bridges**). `halfSpin_reduction`
  (axiom-clean, `§HalfSpin`) commits the dimensions and reduces to: supply the 10 spinor quadrics `Qs` + `hjoint`.
  **✅ DE-RISKING PASS DONE — the 10 equations are FOUND, EXPLICIT, and VALIDATED (`route_c_halfspin_probe.py`).**
  Method: generate genuine pure spinors by the char-free big-cell Pfaffian formula (`ω(b)_∅=1`, `ω(b)_{ij}=b_{ij}`,
  `ω(b)_{ijkl}=Pf(b|_{ijkl})`) and empirically fit the degree-2 vanishing ideal (bulletproof — the naive moment map
  `(ω∧Γ^aω)_top` gave WRONG forms, caught by the probe). **Validation (all pass):** dim of vanishing ideal `= 10`
  exactly (q=3,5,7,11); **EXACT 𝔽₂ point count of the joint zero locus `= 2296 = 1+(q−1)∏₁⁴(qⁱ+1)`** (the forms cut
  *precisely* the spinor cone, nothing bigger); 𝔽₃ Monte-Carlo count matches target (z=0.10); **joint polar radical
  `= 0` (the Lean `hjoint`)**, and it holds already from just the 5 "quadruple" forms — so `hjoint` is provable by the
  `plucker_hjoint` coordinate-isolation pattern (each `Q_a` isolates ∅, its own quadruple, and 6 pairs). **The 10
  forms, in port-ready `Fin 16` indexing** (`0:∅`; pairs `1:12 2:13 3:23 4:14 5:24 6:34 7:15 8:25 9:35 10:45`;
  quadruples `11:1234 12:1235 13:1245 14:1345 15:2345`), each a 4-term `linMulLin` sum like the Plücker `Pf`:
  - **quadruple forms** (`x_∅·x_{ijkl} = Pf`): `Q₀=-x₀x₁₁+x₁x₆-x₂x₅+x₃x₄`, `Q₁=-x₀x₁₂+x₁x₉-x₂x₈+x₃x₇`,
    `Q₂=-x₀x₁₃+x₁x₁₀-x₄x₈+x₅x₇`, `Q₃=-x₀x₁₄+x₂x₁₀-x₄x₉+x₆x₇`, `Q₄=-x₀x₁₅+x₃x₁₀-x₅x₉+x₆x₈`  ← these 5 give `hjoint`.
  - **pair×quadruple forms**: `Q₅=-x₁x₁₄+x₂x₁₃-x₄x₁₂+x₇x₁₁`, `Q₆=-x₁x₁₅+x₃x₁₃-x₅x₁₂+x₈x₁₁`,
    `Q₇=-x₂x₁₅+x₃x₁₄-x₆x₁₂+x₉x₁₁`, `Q₈=-x₄x₁₅+x₅x₁₄-x₆x₁₃+x₁₀x₁₁`, `Q₉=-x₇x₁₅+x₈x₁₄-x₉x₁₃+x₁₀x₁₂`  ← needed to model
    the graph (cone = joint zero of all 10), not for `hjoint`.
  **✅ PORTED & SEALED (2026-07-03, axiom-clean, `RouteCFormAdapters.lean §HalfSpin`):** the 10 forms `S0..S9` transcribed
  via `linMulLin`+`LinearMap.proj`; polars `S0_polar..S4_polar`; `spinor_hjoint` proved from `S0..S4` by the
  `plucker_hjoint` coordinate-isolation pattern; assembled by `multiFormAdapter` into `spinAdapter`, sealed by
  `reachesRigidOrCameron_halfSpin`; brick-1 `halfSpin_refines_coneScheme` (F4 generic). **Instance 3 DONE, full
  instance-1 parity.** *Was Medium–high — de-risked then landed.*
- **Suzuki–Tits (f) — SCOPED (2026-07-03). The outlier, but much cleaner under Route C than the old pair-route
  framing.** `VSz(q)` = the Cayley graph on `GF(q)^4` (`q=2^{2e+1}`), connection set = the cone over the **Tits ovoid**
  `O={(1,a,b,ab+a^{σ+2}+b^σ)}∪{(0,0,0,1)}`, `σ` = the Tits endomorphism (`σ²=Frob`; `q=8⟹σ(x)=x⁴`); small-Aut
  (`Sz(q)⊂Aut`, `|Aut|~q⁴`), **cospectral with `VO⁻₄(q)`** (separated only by `Sz(q)`).
  - **Route-C shape: a PLAIN `FormAdapter`, NOT a `multiFormAdapter`** (there is no quadratic-form family; the ovoid
    polynomial is σ-twisted, non-quadratic). `G₀` = the ovoid-cone stabilizer linear group (`⊇ Sz(q)`), viewed over
    `𝔽₂` after restricting scalars from `GF(q)` (module `Fin d → ZMod 2`, `d=4(2e+1)`). `base` = an `O(1)` base (an
    old probe shatters at base 9 ≪ √4096). `separates` = the **only** bespoke content.
  - **★ THE BIG WIN — Route C sidesteps Suzuki's worst risk.** The old plan's Handle 2 (σ-twisted exponential-sum
    *count*, "the highest analytic risk of any family", Weil/Deligne territory — formsgraph-plan §11.4) is a
    WL-refinement/counting artefact. Route C never counts; it only needs **discreteness at a bounded base** =
    **Handle 1** (direct geometric individualization on the explicit Tits coordinates: individualize `O(1)` reference
    vertices, read off σ-twisted incidences ⟹ pin `(a,b,c)` combinatorially). So the Weil risk is OFF THE TABLE, and
    no char-2 `χ`/Gauss/Arf substrate is needed for the ENGINE (that was a pair-route requirement).
  - **✅ VERIFIED — the shared engine is char-2-ready (Lean-checked 2026-07-03).** `FormAdapter.reachesRigidOrCameron`
    elaborates and seals at `p=2`, and **`neg_mem` is FREE** in char 2 (`LinearEquiv.neg (ZMod 2)` *is* the identity,
    so it lies in any `G₀`). So the entire engine + seal wiring + F1 translation-recovery are shared/free; **`separates`
    is the sole bespoke piece.**
  - **Discharging `separates` (= the ovoid-stabilizer discretizes at a bounded base):** neither `Sz(q)` nor the Tits
    ovoid nor `σ` (`σ²=Frob` over `GF(2^{2e+1})`) is in Mathlib, so a full proof is a major standalone build.
    **Recommended = carry it as a scoped citation** `SuzukiOvoidStabilizerSeparatesAtBase` (the geometric
    individualization / `Sz(q)` 2-transitivity + short stabilizer chain), same discipline as
    `NondegQuadricDeterminesForm` — but a *bigger* carry (the other families PROVE `separates`; only Suzuki cites it),
    reflecting the outlier status. Fixed-`q` `decide` is infeasible (`n=4096`, `native_decide` banned).
  - **✅ DE-RISK PROBE DONE (2026-07-04, `route_c_suzuki_probe.py`, q=8) — object validated + a design-changing
    finding.** (i) **Object EXACTLY validated:** `σ²=Frob`; `|O|=q²+1=65`; `|cone|=(q²+1)(q−1)=455`; VSz(8) =
    **SRG(4096,455,6,56)** — the ovoid formula `c = a·b + σ(a)·a² + σ(b)` is correct (the connection set the Lean
    adapter models). (ii) **★ Poly-vs-quasipoly finding:** VSz is a **rank-3 SRG** (1-WL stable at 1 colour;
    per-base-point relation is only 2-valued). So Route C's **direct** orbit-profile `separates`
    (`discrete_affineScheme_of_jointSeparates`) on the **plain cone scheme** needs a base `≥ log₂n = 12` (probe: greedy
    `> 30`, never injective) ⟹ **only QUASIPOLY = no improvement over the banked floor.** Iterated
    individualization+1-WL discretizes at base **4** (the `Sz(q)` 2-transitivity mechanism), but that is *not* the
    direct-profile the engine uses.
  - **✅ POLY PATH CONFIRMED (2026-07-04 follow-up) — Suzuki is a MULTI-(σ)-FORM adapter, the σ-twisted sibling of
    alternating/half-spin.** No *single* σ-twisted form cuts the cone (the derived `F = x₃x₀^{σ+1}+x₁x₂x₀^σ+x₁^{σ+2}+
    x₂^σx₀²` over-vanishes: `|{F=0}|=512≠456`; the Tits ovoid isn't that hypersurface). **BUT** a **5-dim family
    `{F_k}` of σ-twisted type-(1,2) forms** (`σ(xₐ)·x_b·x_c`) has **joint zero locus = cone EXACTLY (456)** — probe
    `route_c_suzuki_probe.py`. And the **joint `F_k`-value profile separates at base 4 ≤ d+1** (injective over all 4096
    at the frame) ⟹ **POLY**, exactly the `coords_determine_multi` mechanism. (Plain cone scheme stays quasipoly.) The
    5 forms have **all-unit coefficients** (`F₀` = the derived `F`; `F₁..F₄` trim the spurious zeros) — clean,
    representation-independent support, ready to transcribe.
  - **⟹ Lean design (the σ-twisted analog of the multi-quadric adapter):** `σ` (a Frobenius power over `GF(q)`) + the
    5 σ-twisted forms `F_k` + a **σ-twisted `coords_determine_multi`** (`separates` via the joint `F_k`-value profile —
    the genuine bespoke content; prove or carry scoped) + `G₀ = ⨅ₖ {g : F_k∘g = F_k}`. **NOT the quadratic
    `multiFormAdapter`** (the `F_k` are σ-twisted, not quadratic — over the `𝔽₂` linearization they are cubic), so it
    needs a σ-twisted *sibling* of `coords_determine_multi`; but the generic `FormAdapter` engine + `neg_mem` + seal are
    shared/free (char-2-ready, verified). Then `suzukiAdapter` → `reachesRigidOrCameron_suzuki`.
  - **✅ REDERIVATION LANDED (2026-07-04, axiom-clean, `RouteCFormAdapters.lean §Suzuki`):** over an abstract char-2
    `CommRing K` with a Tits endomorphism `σ` (`σ∘σ = (·)²`), the 5 σ-twisted forms `SF0..SF4` + the `ovoidC`
    parametrization are defined, and each is **proven to cut the cone**: `suzukiForms_ovoid` (vanish on the affine
    ovoid `(1,a,b,ovoidC a b)` — via `σ` a ring hom + `σ∘σ=(·)²`, char-2 cancellation), `suzukiForms_infty` (vanish
    at `(0,0,0,1)`), `suzukiForms_homog` (σ-twisted homogeneous `SF_k(λx)=σλ·λ²·SF_k(x)`, so `{SF_k=0}` is a cone).
    `SF0` = the single derived form; `SF1..SF4` trim its spurious zeros. Representation-independent (all-unit coeffs).
  - **✅✅ `separates` PROVED CITATION-FREE (2026-07-04, axiom-clean, `§Suzuki`) — the citation discharge.** The
    earlier draft carried `separates` via the scoped citation `SuzukiFormsDetermine` (the first-order frame `{0,eⱼ}`
    value-profile determines the vertex — true for `GF(2^{2e+1})`, verified injective for q=8/32 by
    `route_c_suzuki_determine_probe.py`, but its only known proof needs `Sz(q)` 2-transitivity: first-order data ⟹
    nonlinear, large-`q`-only recovery). **The discharge:** enlarge the base to include **pairwise sums**
    `{0, eᵢ, eⱼ, eᵢ+eⱼ}` — then each coordinate is a **second discrete derivative** of one σ-form,
    `DᵢDⱼ SF_k(v) := SF_k(v)+SF_k(v−eᵢ)+SF_k(v−eⱼ)+SF_k(v−eᵢ−eⱼ)`, and in char 2 the σ-terms and constants **cancel**,
    collapsing it to a bare coordinate: `x₂=D₀D₁ SF0`, `x₃=D₀D₁ SF1`, `x₀=D₁D₃ SF1`, `x₁=D₂D₃ SF4` (verified by hand
    + over GF(8) all-4096 + GF(32); found via `route_c_suzuki_symbolic.py`). So `separates` is **elementary char-2
    algebra**, valid over ANY `CharP K 2` ring — no citation, no `hσ`, no field-size hypothesis. Decls: the scalar
    identities `SF0_recover`/`SF1_recover_x3`/`SF1_recover_x0`/`SF4_recover_x1` (`simp`+`ring_nf`+char-2 close), their
    `SFv`-lifts `recover_x0..x3`, and the PROVED determiner `suzukiForms_determine` (funext over `Fin 4`, one recovery
    per coordinate). Base grows `4+1 → 8` (`suzukiBaseVecs`, still `O(d²)` poly). `SuzukiFormsDetermine` and the old
    `suzuki_separates` are **removed**.
  - **✅ MODULE BRIDGE + SEAL LANDED (2026-07-04, axiom-clean, `§Suzuki`):** the `GF(q)^4 ↔ 𝔽₂^d` bridge via an
    **additive** iso `Ψ : (Fin D → ZMod 2) ≃+ (Fin 4 → K)` (no `ZMod 2`-module on `K` needed — `PreservesForms` is a
    function condition; `Ψ` additive suffices for difference-transport). `SFbar` (forms in 𝔽₂-coords), `suzukiG₀`
    (clean joint-isometry subgroup), `neg_mem_suzukiG₀` (free in char 2), `suzukiBase` (`suzukiBaseVecs` images, `≤8`),
    `base_sfv_eq` (per-base-vector transport), `suzukiAdapter` (`FormAdapter (p:=2)(d:=D) 8`, `separates` = the engine
    orbit-profile transported to `suzukiForms_determine`), and the capstone **`reachesRigidOrCameron_suzuki`**. Seals
    via the shared engine.
  *Single family, no Weil, no char-2 χ-substrate, no engine work. **Instance 4 SEALED end-to-end, CITATION-FREE**
  (no `SuzukiFormsDetermine`, no `hσ`); a multi-σ-form adapter with an O(d²) poly base — the σ-twisted sibling of
  alternating/half-spin.*

### C# / Lean split, and the reuse to exploit
- **The C# engine is the symmetric mirror of Option 2's Layer D** (IR doc §11.10, built through D-M4 as a Phase-2
  pre-processor: recover structure → refine/solve → plug the existing seam). **Clone that architecture**, swapping
  `IFormStructure` for the F₂ extractor. This is the payoff of the recovery↔co-recovery duality
  ([[project_recovery_corecovery_duality_2026-07-03]]): the two pre-processors share a skeleton.
- **Lean deliverable is the poly-supporting structural object**, not a runtime proof: "the recovered-form-refined
  scheme discretizes at an iso-invariantly-constructible `O(d)` base" (F5 + A3), with "poly" the meta-claim over that
  bounded base + the existing Schreier–Sims meta-cost (same discipline as Part A's `Order = ∏ orbit sizes`).

### Sequencing & risks (updated 2026-07-03)
1. ✅ **F1 + A1** (C# recovery front) — DONE + confirmed against the real harness (`AffineStructureRecovery`,
   `QuadraticFormRecovery`, `RouteCF1Probe.cs`).
2. ✅ **A2⁺ + A3 brick 1** (Lean spine from landed pieces) — DONE, axiom-clean (`RouteCFormAdapters.lean`).
3. ✅ **F4** equivariance core — **LANDED 2026-07-03, axiom-clean** (`recoveredForm_colouring_equivariant` + bricks).
   Rests only on `NondegQuadricDeterminesForm` — now DISCHARGED as an exact scoped citation (§ STATUS remaining).
4. ✅ **Meta-poly bootstrapping** — ASSESSED + RESOLVED (§7a): Route C is poly, non-circular (global coordinatization ≠
   bounded WL; Aut-free geometric recovery, probe-confirmed enabling primitive). Residuals R1–R3 deferred to the rigorous
   C#→Lean runtime stage (build the geometric coordinatizer; name Buekenhout–Shult; double-check `d=4`).
5. ◑ **F2** (`q=pᵉ` semilinear seam) — **Lean core LANDED** (`…_semilinear`, axiom-clean): the recovered form is
   iso-invariant up to scalar **and** Frobenius σ. Remaining: the C# field-recovery side (folds into R1's geometric
   coordinatizer — Buekenhout–Shult recovers PG over 𝔽_q, field included).
6. ✅ **Instances 1→2→3→4 — ALL SEALED axiom-clean (2026-07-03/04).** inst 1 affine-polar (`affinePolarAdapter`),
   inst 2 alternating `Alt(5,q)` (`reachesRigidOrCameron_alternating`), inst 3 half-spin (`reachesRigidOrCameron_halfSpin`),
   inst 4 Suzuki (`reachesRigidOrCameron_suzuki`). Plus the generic multi-quadric bridges (brick-1 + F4) → alternating
   and half-spin at full instance-1 parity. **No further family builds remain.**
7. **▶ NEXT — the §9 post-four-seals combine** (four seals → one correctness object; start with the L1 iso-invariance
   de-risk, §9.1) + the C# runtime handlers (C1–C4, §9.2) + optional citation-discharge.

**Definition of done (Route C, affine-polar):** F1 recovers coordinates iso-invariantly (F4 ✅ equivariance core); A1
recovers `Q` (C# ✅; Lean uniqueness = the carried `NondegQuadricDeterminesForm`); A3 refines to the isometry scheme (brick 1
✅); `viaOrthogonalForm_spanning` discretizes at the `O(d)` base and seals via `viaSpielman` (✅) — the structural
bounded-base discreteness object complete, "poly" the meta-claim over it **modulo the bootstrapping question**. The C#
engine reproduces `|Aut|` via `PermutationGroup`. **The Lean spine is now assembled;** the open items are the classical
carry + the meta-poly bootstrapping.

### 6a. F4 — iso-invariance of the recovered form (✅ LANDED 2026-07-03; kept as the design record)

**What F4 is.** The recovered `Q` (and hence F1's coordinates and the isometry-scheme colouring) must be a *canonical
function of the graph*: a graph isomorphism `σ` must carry the recovered structure of `G` to the recovered structure of
`σ(G)` (up to the scalar ambiguity of `Q`). Concretely, the connection set (cone) is carried to the connection set, so
the degree-2 form vanishing on it is carried to a scalar multiple — the recovered-`Q` difference colouring is
relabeling-**equivariant**. This is what makes "canonicalize via the recovered form" produce a *canonical* labelling
(the same up to iso), i.e. it is the iso-invariance the poly canonicalization claim needs.

**Why it's the last load-bearing piece.** The spine (recover → isometry scheme → discretize) is assembled: brick 1 says
the isometry scheme refines the given graph; `viaOrthogonalForm_spanning` says it discretizes. What is *not* yet Lean-
certified is that the isometry scheme used is derived *iso-invariantly* from the given graph — without which "discrete"
does not give "canonical". F4 supplies exactly that. (Discreteness does not transfer down to the similitude scheme — the
node-4 stall — so F4 is genuinely needed; it is not implied by the banked seal.)

**The template to mirror (landed).** The symmetry-phase iso-invariant-node machinery in `Cascade.lean`:
`forcedNode` (`:2752`), `forcedNode_image` (`:2830`, image under an automorphism), `movedSet_relabel` (`:3004`),
`forcedNode_relabel` (`:3024`, equivariance under an arbitrary relabelling). F4 is the *form-recovery* analog:
`recoveredForm(σ • G) = σ • recoveredForm(G)` (up to scalar). State it against the abstract-graph relabelling the same
way `forcedNode_relabel` does.

**Risk — the vacuity trap (cf. `SchemeReproduced`, memory `project_...`).** Make the equivariant predicate strong enough
to be *useful* (it must actually pin the colouring iso-invariantly) yet true (holds for the real recovery). Check
non-vacuity against the C# ground truth (`RouteCF1Probe.cs` already exhibits the recovered `Q` reconstructing the graph —
the semantic content F4 formalizes).

**How it composes (the end state).** F4 (equivariant recovery) + brick 1 (isometry refines the graph) +
`viaOrthogonalForm_spanning` (isometry discretizes at a spanning base) ⟹ the graph has an iso-invariant discrete
colouring at an `O(d)` base ⟹ (meta) poly canonical labelling. That is the Route-C deliverable for affine-polar.

---

## 7. Honest scope — what Route C does and does NOT do
- **Does:** upgrade the **forms-graph** residue from the banked quasipoly seal to **polynomial**, family by family,
  via a shared engine. Sidesteps the node-4 WL wall entirely (recovery is linear algebra, not WL).
- **Does NOT:** touch the **rigid mirror** (the IR-solver **row 4** / multipede / non-schurian residue). There is no
  large classical group to recover there — Route C is structurally inapplicable. That residue is Option 2's job
  (F₂-structure recovery, IR doc §11). **But the meta-strategy is identical** — "recover the algebraic substrate, use
  exact algebra instead of WL" — so the two pre-processors share the Layer-D architecture (§6).
- **Char-2 / Suzuki:** a separate analytic track (Arf/additive-trace, no `χ`); the *combinatorial* engine (F1/F3/F5)
  transfers char-agnostically, only `RecoverForm`/`Separates` change.
- **Dead ends (do not re-walk):** the WL/`bᵢ=1` build via `ColorRefinesGramK` (circular, node-4 wall, recovery doc
  §9.8.9); the frame-locked similitude predicates (idx 1221-1226, §4). δ′ dominator-closure is walled for `bᵢ=1`
  (dimensional wall, `ScratchDominatorForms`).

---

## 7a. The meta-poly bootstrapping — assessment & resolution (2026-07-03)

**The concern.** Route C's poly claim runs: recover coordinates (F1) → recover `Q` (A1, one linear solve) → `Aut = AΓO(Q)`
known → canonicalize. A1 and canonicalization are clearly poly *given coordinates*. But **F1 as built/documented
recovers coordinates from `T = O_p(Aut)` — it consumes `Aut`** (`AffineStructureRecovery.Recover(PermutationGroup aut,…)`;
the socle theorem gives `O_p(Aut)=T` *given* `Aut`, not `Aut` itself). Poly-time computation of `Aut` for this SRG
residue is *itself* the open T0 problem Route C advertises it sidesteps (recovery §7 "does not depend on the open core").
So the meta-poly *first step* is potentially circular. This must be resolved before the cost analysis, not after.

**Resolution — three findings, verdict: sound (not circular, not the node-4 wall in disguise).**

1. **Global computation ≠ bounded-round WL — the distinction that keeps Route C alive.** The node-4 wall is specifically
   that *bounded-round WL refinement* stalls (cannot recover `gramK` at a bounded base — recovery §9.8.9). Coordinatization
   is a **global** computation (all `n` vertices, linear algebra / geometry recovery), a strictly stronger model in which
   poly is reachable even when bounded-WL-dimension is unbounded (this is the whole individualization-beats-WL premise).
   So recovering coordinates is **not** the node-4 wall re-encountered — provided a concrete *global, Aut-free* procedure
   exists. It does (finding 2).

2. **`T = O_p(Aut)` was only a de-risking shortcut; the poly pipeline uses Aut-free GEOMETRIC coordinatization.** The graph
   is the collinearity graph of the affine polar space. Recover the classical geometry (isotropic points/lines) from the
   graph and read off coordinates by the **fundamental theorem of projective geometry / Buekenhout–Shult** (a polar space
   of rank ≥ 3 is classical ⟹ embeds in `PG(d,q)` ⟹ coordinates up to `PΓO`), then lift to affine — poly and **needing no
   `Aut`**. The `O_p(Aut)` route was a valid *shortcut for the de-risking probes* (which had `Aut` from the harness), not
   the poly argument. Rank ≥ 3 means **`d ≥ 6`; `d = 4` (Witt index 2) is the generalized-quadrangle special case** (outside
   Buekenhout–Shult's rank≥3 hypothesis — flagged for the rigorous stage, but the enabling primitive holds there too,
   finding 3).

3. **The enabling primitive is confirmed Aut-free — probe `route_c_bootstrap_probe.py` (2026-07-03).** The local graph
   invariant `|N(o) ∩ N(x) ∩ N(y)|` (common cone-neighbours of an isotropic triangle) **perfectly separates collinear from
   non-collinear** triangles — a clean gap in *every* case (VO^±, `d=4,6`, `q=3,5`: e.g. VO⁺₄(5) collinear=42 vs non=22;
   VO⁻₆(3) 60 vs 6). Reconstructing the isotropic lines through `o` from that invariant alone (no `Aut`, no ground truth)
   recovers exactly the punctured lines (`q−1` points each), and **their directions span `V`** uniformly. So the geometry
   is poly-recoverable from adjacency — the step that turns "recover coordinates" from circular into a standard geometry
   problem. (`d = 4` included: the primitive separates and spans there too, evidence the GQ case also goes through.)

**Verdict.** The bootstrapping is **resolved at the meta level: Route C is genuinely poly, non-circular.** The poly first
step is *geometric coordinatization* (global, Aut-free, probe-confirmed enabling primitive + Buekenhout–Shult for the
coordinate read-off), **not** `O_p(Aut)`. Route C sidesteps the *WL-refinement* crux and does **not** inherit it in
disguise (global ≠ bounded-WL).

**Residuals for the later rigorous (C#→Lean runtime) stage — record, don't block:**
- **(R1) Build the Aut-free geometric coordinatizer** to replace/supplement `AffineStructureRecovery.Recover`'s
  `O_p(Aut)` path (which is fine for de-risking but is the circular step for the poly claim). The enabling primitive
  (line recovery) is confirmed; the remaining engineering is line-geometry → frame → coordinates (the group-law/embedding).
- **(R2) Name + verify the geometry-recovery citation** — see the **2026-07-06 REFINEMENT** below.
- **(R3) Double-check `d = 4` (GQ, rank 2)** — outside the rank≥3 embedding theorem; the probe supports it, but the
  coordinate read-off needs its own (standard) argument for generalized quadrangles.

**★ 2026-07-06 REFINEMENT — the citation split, the poly obligation, and the transitivity-membership sharpening
(literature run + a soundness argument; corrects the earlier "poly rests on Buekenhout–Shult" framing).**

*(a) The citation split — R2 is NOT a poly citation.* A verified literature search (Buekenhout–Shult, Veldkamp–Tits,
Cameron; constructive-recognition-of-classical-groups; SRG canonization) found: **no off-the-shelf theorem states a
polynomial-time coordinatization of a classical polar-space graph.** The available results split cleanly —
  - **Buekenhout–Shult / Veldkamp–Tits** (rank ≥ 3) and **Payne–Thas** (GQ) are **existence/characterization** theorems:
    the recovered geometry *is* a classical polar space and the form is recoverable up to the standard equivalence. These
    are legitimate **correctness/classicality citations** — but they carry **no complexity bound**.
  - **Constructive recognition of classical groups** (Kantor–Seress; Leedham-Green–O'Brien; Dietrich et al.) is poly-time
    in field + rank, but for the **group in a representation**, is Las Vegas, and runs poly-time only **modulo a
    discrete-log oracle** — it does not solve the "coordinatize the abstract graph" problem (and discrete log is not needed
    for our canonization use: the field is recovered only up to Frobenius, already handled by F2/FTPG).
  - **SRG canonization** (Babai–Chen–Sun–Teng–Wilmes, FOCS 2013) is **sub-exponential** `exp(Õ(n^{1/5}))`, not poly (= the
    project's existing `viaSpielman` floor).
  So R2 becomes: **cite Buekenhout–Shult (rank ≥ 3) + Payne–Thas (GQ) for CLASSICALITY/CORRECTNESS only.**

*(b) Poly-time is an in-project OBLIGATION, not a citation (and NOT the wall).* The coordinatization — line-recovery
(done) → classicality (cited) → coordinatize the projective residues by the classical ternary-ring / Von Staudt effective
procedure (linear algebra + incidence) — is **manifestly polynomial**, and it is a **different method** from the frame+WL
route of §9.2.8 that reduces to the WL-dimension wall. So the poly bound is a **tractable, non-wall effective-construction
argument the project makes itself** (cleanest for rank ≥ 3, `d ≥ 6`), *not* an axiom. Per the firewall (endgame-spec), an
unproven poly claim cannot be axiomatized — so poly-time stays an obligation, and the good news is it is provable, not the wall.

*(c) The transitivity-membership sharpening — the per-graph obligation is weaker than "coordinatize + harvest Aut".*
**▶ SUPERSEDED by §7b (2026-07-07): the witness-or-flag mechanism needs no membership certification at all — you witness
VT (harvest succeeds) or flag; poly-mode assumes VT from the confinement lemma. Read §7b; (c) is kept for provenance.**
Every
handled residue is **vertex-transitive** (schurian ⟹ orbital scheme of a transitive group; Cameron = rank-3 primitive).
Two consequences narrow R1's real target:
  - **Existence-of-transitivity suffices for sound pruning — no explicit `Aut`-harvest is needed.** To pick one root and
    prune the other `n−1` soundly, the canonizer needs only that *some* automorphism relates any two vertices (one orbit),
    not the explicit permutation. Recursing (each forms-graph residue is a smaller vertex-transitive `VO_{d−2}`) gives a
    **single-path** descent of `O(d)` steps ⟹ **poly** — exactly the recovery-route's empirical single-path finding
    (`leaves=1, BranchingNodes=0`).
  - **So the load-bearing per-graph step is `certify vertex-transitive MEMBERSHIP` ("is this really `VO_d`?"), not full
    coordinatization.** Transitivity ⟹ single-path ⟹ poly is then *cited structural theory* (the orthogonal group is
    transitive on isotropic points), applied once, not reproven per graph. Membership certification is R1's confirmation;
    it may be strictly cheaper than explicit coordinates.

*(d) No poly-time transitivity test is KNOWN — but this is a current-knowledge fact, NOT a hardness theorem (corrected
2026-07-07).* Precise status: vertex-transitivity is **reducible to GI** (`VT ≤ₚ GI`, via computing `Aut` — Mathon), but is
**NOT known to be GI-hard**; its complexity is **open** (not in P, not GI-hard). *(The GI-complete object is the finer
"are these two *specific* vertices in the same orbit?" / computing the orbit partition — the standard gadget reduction
builds a graph that is not vertex-transitive either way, so that hardness does NOT transfer to the global VT yes/no.)* The
only WL handle (Fuhlbrück–Köbler–Verbitsky, arXiv:2005.08887) is poly **only for prime `n`**, **provably blocked for `n`
divisible by 16** (⊇ the char-2 forms graphs), **open for odd prime-power `n`** (the odd-`q` forms graphs `n = q^d`). So
"recognize parameters ⟹ assume transitive" is **unsound** (parameter-mates exist that are not vertex-transitive) and **no
KNOWN test rescues it** — but a poly (relative/coloured) VT test, if found even just for these graphs, would be a legitimate
non-paradoxical avenue (it would NOT imply GI ∈ P). So (c)'s membership-certification is the sound route *by current
knowledge*; transitivity is **cited, not tested**, because no test is available — not because one is barred.

*(e) The genuine soft spot stays `d = 4` (R3).* The GQ case has no clean poly citation for recognizing/coordinatizing a
*classical* GQ from its graph (non-classical GQs exist), so it needs its own argument or an explicit scope note. This is the
one place the literature does not hand us correctness-for-free either.

**Net for R1:** *not* closable by "add a citation" (the earlier hope), *not* wall-blocked. Shape = **{Buekenhout–Shult +
Payne–Thas cite CLASSICALITY} + {poly-time = an in-project effective-construction obligation, cleanest `d ≥ 6`} + {the
per-graph obligation is certified vertex-transitive membership, explicit `Aut`-harvest shown unnecessary} + {`d = 4` GQ = the
residual}.** The `Publication.lean` firewall list gains Buekenhout–Shult + Payne–Thas as *correctness* citations; poly-time
does not become an axiom.

---

## 7b. Witness-or-flag, and the assume-VT poly upgrade (2026-07-07) — supersedes (c)'s membership search

The membership-certification framing of §7a(c) is **superseded** by a mechanism that needs no VT test (§7a d) and no
membership oracle. It refines the flag from a global to a **per-node** budget.

**One canonizer — witness-or-assume, with a phase-discriminated flag action.** At a Phase-1 descent node the per-node
orbit-harvest either (i) **completes** within budget — and since the harvest *is* a certified orbit (verifiable by
construction; §7a-residual (1) is a non-issue), pruning the target cell to one root is sound with VT *witnessed* — or
(ii) **exceeds** budget → the flag fires, and *by the confinement lemma below* the residue is node-4/Cameron ⟹
**vertex-transitive** ⟹ the cell is one Aut-orbit ⟹ **pick any root and prune the rest soundly WITHOUT exhibiting the
automorphism** (pruning needs only the orbit-equality *guarantee*, which the structural VT theorem supplies, not the
*witness*). Either branch is *prune-and-continue*: the flag **never means "give up" in Phase 1**. Recursion (each
residue a smaller VT `VO_{d−2}`) gives a **single-path `O(d)` descent = poly** — the recovery-route's empirical
`leaves=1, BranchingNodes=0`. There is **no separate "safe mode"**: the only place a flag emits `none` is **Phase 2**
(the rigid / IR-row-4 residue), out of the non-rigid scope by design. So the flag's *action* is phase-discriminated —
Phase-1: assume-VT-prune-continue (handled); Phase-2: emit `none` (unhandled rigid) — which is also what structurally
selects the `UnhandledResidue` atom. This resolves the §7a(d) VT-test blocker outright: you never *test* transitivity,
you witness it or (on a flag) get it from confinement.

**What this delivers, and the one thing left to prove.** The mechanism is **poly-time** and **complete for the
non-rigid residue** (every non-rigid input resolves to a canonical form; no Phase-1 `none`). **Correctness is the
remaining obligation** — assume-VT-prune on a residue that is *not* VT would be a **correctness bug** (unsound pruning ⟹
wrong canonical form). So ① (`canon_sound`/`canon_complete`) on the non-rigid side is **conditional on the confinement
lemma delivering VT**. The budget/flag mechanism is therefore **load-bearing for correctness, not external accounting**
— the cost model shifts from a *demonstration* into a **prerequisite of the algorithm** (cost-model §1/§7a). **The
correctness proof for the non-rigid residue *is* the confinement lemma** (planned in §7c below).

**The confinement lemma — the ONE obligation, and it is "the remainder" the seal already chases.**
One-line summary: *a Phase-1 over-budget flag ⟹ the residue is primitive rank-3 (node-4/Cameron) ⟹ VT ⟹ the target
cell is one orbit ⟹ prune sound.* **The full plan — the largeness argument that kills the non-Schurian-SRG soundness
danger, the four sub-obligations P1–P4, assembly, and tuning-≠-theorem — is §7c below.**

**Net.** No VT test, no membership oracle. One poly-time canonizer, complete on the non-rigid residue; its correctness
= the confinement lemma (§7c) = the seal's own remaining content, now soundness-critical.

---

## 7c. The confinement lemma — plan for the non-rigid correctness proof (2026-07-07)

**Target (the whole non-rigid correctness proof reduces to this).** At every Phase-1 branching node, the target cell is
a single orbit of the residue's automorphism group — so pruning it to one root is sound. It suffices to prove the flag
case (the witness case is sound by construction):

> **CONFINEMENT.** If a Phase-1 node's orbit-harvest exceeds the per-node budget `w`, then its residue is a **primitive
> rank-3 (node-4/Cameron) scheme**, hence **vertex-transitive**, and the target cell (a `warmRefine` colour class) is a
> single `Aut`-orbit.

**Why this is the right reduction — soundness of the *dangerous* case is killed by *largeness*, not by an oracle.** The
soundness worry is a **non-Schurian SRG** (small, non-transitive `Aut`) being assume-VT-pruned. CONFINEMENT excludes it
*structurally*: such a graph has **small `Aut`** ⟹ a cheap exact orbit-oracle ⟹ it **resolves within `w` and never
flags** (or fails to discretize and is **deferred to Phase 2**). Only **large-`Aut`** residues flag; a large-`Aut`
rank-3 residue has a rank-3 automorphism group ⟹ is the orbital scheme of a primitive group ⟹ **schurian and VT by the
classification**. So we never need the general (undischarged) `SchurianScheme` assumption — only its restriction to the
flagged (large) subset, which the largeness clause *delivers*.

**Decomposition into four sub-obligations (proof targets):**

| # | Sub-obligation | Content | Status / where |
|---|---|---|---|
| **P1** | **Largeness confinement** (the soundness linchpin) | small-`Aut` residue ⟹ orbit-harvest ≤ `w` ⟹ **does not flag**. Contrapositive: flag ⟹ large `Aut`. Pins the budget `w` ≥ the small-`Aut` oracle cost; this is where the cost model (`w`, §4 oracle term) and correctness interlock. Excludes non-Schurian SRGs from Phase-1 flags. | **New.** Needs the per-node oracle-cost bound + small-`Aut`⟹cheap-oracle. Uses landed `exists_greedy_base_le_log` (small `Aut` ⟹ base `O(log n)`). |
| **P2** | **Deferral confinement** | Phase-1 per-node cost = symmetric-harvest cost only; rigid decisions are *deferred* (cheap push), never expensively harvested. ⟹ a Phase-1 flag is not rigid-caused ("rigid does not entangle into non-rigid"). | Substrate landed (direction-blind deferral, `exists_potential_descent`); needs a per-node cost lemma. |
| **P3** | **Trichotomy, restricted** | large `Aut` ∧ (¬rigid, by P2) ⟹ residue is Cameron ∨ node-4 (both primitive rank-3). | The seal `reachesRigidOrCameron` (quasipoly, **in build**) — a recomposition. |
| **P4** | **Cells-are-orbits on primitive rank-3** | for a primitive rank-3 scheme the `warmRefine` colour class (target cell) is a single `Aut`-orbit ⟹ pruning it is sound. Primitive ⟹ transitive ⟹ VT. | **New but clean.** Connect `orbitalScheme` / primitivity machinery; the actual soundness content of the prune step. |

**Assembly.** P1 ⟹ flag is large; P2 ⟹ not rigid; P3 ⟹ Cameron/node-4 primitive rank-3; P4 ⟹ VT + cell = orbit ⟹
prune sound ⟹ ① on the non-rigid residue. **Weakest links: P1 (soundness linchpin) and P4 (the prune-soundness core);
P2/P3 are recompositions of landed pieces.**

**A tuning fact, not a proof step.** `w` must sit above every small-`Aut` oracle cost and below the large-`Aut` exact
harvest; over-large only costs speed, too-small is a correctness bug (P1). Tuning fixes *which* inputs flag; P1 is the
*theorem* that whatever flags is large — the two are not interchangeable.

**★ Empirical de-risk of P1 (2026-07-07, PASSED) — `P1ConfinementProbe.cs`.** Ran the real `ChainDescent` canonizer on
the sharpest danger case: **Chang graphs** `SRG(28,12,6,4)` (Seidel-switch of `T(8)=J(8,2)` by a perfect matching and by
an 8-cycle) — the classic **small-`Aut`, non-Schurian, non-VT** SRGs (`|Aut| = 384, 96`; harvested-group **orbits = 2**
⟹ certified non-transitive), with `T(8)` (`|Aut| = 8! = 40320`, orbits = 1, VT/schurian) as control. Every P1 prediction
held on both Chang graphs, both descent modes:
- **No flag** (resolved well within the `~9.8M` node budget: `nodes = 11–17`, `maxDepth = 3–6` — a short base, as
  small-`Aut` predicts);
- **Zero Phase-1 starvation** (`ClassifyStarved = BranchStarved = 0`) ⟹ a per-node-flag assume-VT mechanism would
  **never fire** on these non-VT graphs;
- **Rigid decisions routed to Phase 2** under deferral (`Phase2Nodes = 2`) — the *largeness*-clause saving grace
  (non-VT small-`Aut` residue treated as rigid, not as a VT family), observed directly;
- **Iso-invariance held** (`canon(G) = canon(πG)`, soundness anchor).
The control `T(8)` (the VT case the mechanism must keep) resolved single-path (`leaves = 1, branchingNodes = 0`). **No
falsifier.** Scope/limits (honest): one parameter family at `n = 28`; the current canonizer flags only on *global*
budget exhaustion (per-node flag not built yet), so "no flag + zero starve + Phase-2 routing" is the faithful *proxy*
for "would not Phase-1-flag". Strengthening (later, if wanted): Paulus `SRG(25,12,5,6)`/`SRG(26,10,3,4)` and larger
non-VT SRGs. This clears P1 to proceed to the Lean proof (step 2 = P4).

---

## 8. Pointers
- **Live route it replaces:** [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) (STATUS + §7 Route
  C sketch + §9.8.9 stall verdict).
- **Per-family analysis:** [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §11.4
  (alternating/half-spin/Suzuki), §11.5 (char-2), §1 item 1 (the Route A/B/C fork).
- **The rigid mirror (same meta-strategy):** [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md)
  §11 (Option 2, Layer D) + [[project_option2_f2_gap_2026-06-20]].
- **The seal it upgrades:** `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (banked, in `build.sh`);
  `GraphCanonizationProofs/PublicTheoremIndex.md` idx 1207-1237 (Stage A/B decl map).
- **What's-left map:** [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §3a.1, §4.
- **Cross-session memory:** [[project_recovery_corecovery_duality_2026-07-03]],
  [[project_formsgraph_wldim_viability_2026-06-28]].

---

## 9. After the four seals — the combined correctness object + the C# runtime (FORWARD PLAN, build later)

**Status: THIS SECTION IS NOW LIVE (2026-07-04).** All four per-family adapters are sealed (affine-polar ✅,
alternating ✅, half-spin ✅, Suzuki ✅ — each modulo its scoped citation). Each gives
`reachesRigidOrCameron (affineScheme A.G₀)` for a *concrete* group `A.G₀` built from recovered forms. This section
is the **immediate next work**: how those four combine into ONE correctness object (§9.1), and how the C# canonizer
gets the family handlers it currently lacks (§9.2). **The recommended entry point for the next session** — start
with the L1 de-risk (§9.1: spot-check whether the four seal disjuncts are already iso-invariant), which is cheap and
validates the whole combine plan.

### 9.0 The key structural fact that keeps it clean (read first)

Route C's `FormAdapter.reachesRigidOrCameron` is **threshold-free**: it is `viaSpielman ∘
discrete_affineScheme_of_jointSeparates`, needing only *nondegeneracy* + *a bounded base* — **no `q ≥ 256` /
`q ≳ 32d` floor** (those were the pair-route/quasipoly seal's Gauss-sum thresholds, which Route C does not touch),
and the `hjoint` lemmas (`plucker_hjoint`, `spinor_hjoint`) are proved for **all primes `p`** (coordinate
isolation, ±1 coeffs, no division — not even `p≠2`). Consequence: **the small-`q`/small-`d`/sporadic cases do NOT
pile up as Route-C exceptions.** Route C only ever engages the *unbounded-WL-dimension* residue (the infinite
families); any finite/sporadic small graph has bounded `|V|` ⟹ bounded base ⟹ it is already sealed by the
*generic* bounded-base machinery (`viaSpielman` on a trivial base) and never reaches the forms-graph residue. So
the combined object carries **no finite exception pile** — the only systematic split is **char 2** (→ the
Suzuki / Arf branch, one branch, not scattered exceptions). This is why "4 seals + finitely many exceptions"
collapses to "1 classification citation + 1 iso-invariance lemma".

### 9.0a ★ CORRECTION (2026-07-04) — the combine target is the FINER→COARSER transfer, not disjunct-transport

**A scheme-level mismatch invalidates the naïve §9.1 dispatch below; read this first.** The four adapters seal the
**fine** scheme `affineScheme(isometryGroup Q)` / `affineScheme(⨅ₖ O(Q_k))` / `suzukiG₀` — the *exact*-value
scheme. The canonizer's residue `X` is the **coarse** given graph `affineScheme(similitudeGroup Q)` /
`affineScheme(jointConeStab)` — the *isotropy-only* rank-3 SRG. These are **different schemes (different rank)**, so:
- there is **no realizing permutation** `X ≅ affineScheme(G₀)` (§9.1's "transport along hiso" has a type error — the
  ScratchSeam-style transport applies only between a residue and *the same* scheme it is iso to);
- `SchemeRecoveredByDepth(fine) → SchemeRecoveredByDepth(coarse)` is **FALSE at bounded/poly base** — the coarse
  scheme's own 1-WL does not discretize there (the node-4 stall Route C sidesteps). Both `SchemeRecovered`/
  `SchemeRecoveredByDepth` are hardwired to `warmRefine (schemeAdj X)`, so they are the **wrong target** for `X`.

**User decision (2026-07-04): pursue the finer→coarser recovered-form TRANSFER** — the only route that yields
*polynomial* (not another quasipoly) closure of node 4, which is the seal's purpose (Spielman already banks quasipoly;
another quasipoly build adds nothing). **Mechanism:** the recovered `Q` is a *global*, iso-invariant (F4) poly
function of the graph — refining the coarse graph by the recovered-`Q` colouring is **free** (no branching; canonical
up to one global scalar `μ`). A *similitude* (`μ≠1`) permutes the value-classes rather than fixing them, so
`Aut(fine)=AO(Q)` is strictly smaller than `Aut(coarse)=AΓO(Q)` — refining by exact values *loses* the scalings; the
descent recovers them via a **single reference-pin orbit-branch** (individualize one anisotropic pair to pin `μ`; the
choices form one Aut(coarse)-orbit ⟹ a true symmetry ⟹ free, and its covering automorphisms ARE the scalings).

**★ VACUITY CORRECTION (2026-07-04) — there is NO non-vacuous "coarse reaches rigid" predicate to prove.** A first
build attempt targeted `GroupReproduced Sc := ∃ gens, closure gens = SchemeAutGroup Sc`. **That is VACUOUS**
(`⟨↑(SchemeAutGroup Sc), Subgroup.closure_eq _⟩` proves it for every scheme — exactly the retired `SchemeReproduced`
the project excised, `Cascade.lean` "do not regress (2026-06-07)"). The genuine, non-vacuous "reaches rigid" is
`SchemeRecoveredByDepth` — keyed on the **visible-realizer harvest over `warmRefine (schemeAdj Sc)`**, non-vacuous
precisely because its same-cell clause fails when cells ⊋ orbits. **Decisive consequence:** `SchemeRecoveredByDepth Sc`
is about the *coarse* `warmRefine`, whose cells ⊋ orbits at bounded/poly base — that IS the node-4 stall. So the
*non-vacuous* "coarse reaches rigid" is **false** here, and the only *true* form is the *vacuous* tautology.
**Route C cannot produce a non-vacuous coarse `SchemeRecoveredByDepth`; there is no finer→coarser transfer at that
level.** Instead Route C **changes the canonization object**: it augments the descent with the poly, iso-invariant
recovered form `Q` (F4) — i.e. runs on the **fine** scheme, whose `SchemeRecoveredByDepth` *is* non-vacuously true
(the adapter) — and the coarse graph is canonized because that colouring is an iso-invariant poly refinement of it
(brick-1 + F4), adding no branching. "Poly" stays the project's meta-claim over that augmented descent.

**✅ WHAT T1 ACTUALLY PROVES (2026-07-04, all axiom-clean + genuinely non-vacuous,
[`RouteCSeam.lean`](../GraphCanonizationProofs/ChainDescent/RouteCSeam.lean)):**
- `affineG_le_schemeAutGroup` — `affineG G₀ ≤ SchemeAutGroup(affineScheme G₀)` (the affine group acts as scheme auts
  of its own orbital scheme; via `orbMk_smul` + `isSchemeAut_of_relOfPair_eq`). The `≥` half of every 2-closure here.
- `schemeAutGroup_affineScheme_mono` (`hmono`) — `H ≤ G ⟹ SchemeAutGroup(affineScheme H) ≤ SchemeAutGroup(affineScheme G)`
  (finer affine scheme ⟹ smaller Aut group), via `affineScheme_refines_of_le` + the `relOfPair`-characterisation of
  `IsSchemeAut`. Instantiated `isometrySimilitude_schemeAutGroup_mono` (the honest "recovered form only *refines*").
- `schemeAutGroup_coarse_eq_affineG` — **modulo the Skresanov 2-closure citation `hSkresanov`** (`SchemeAutGroup(coarse)
  ≤ affineG(similitude)` = no unexpected automorphisms = Skresanov rank-3 2-closure, already in the seal's stack), the
  coarse scheme's Aut group is *exactly* `affineG(similitudeGroup Q) = translations ⋊ AΓO(Q)`. The non-vacuous
  group-pinning the |Aut| side + the meta poly argument consume (and where the reference-pin scalings `AΓO ⊋ AO` live).

**Honest scope of the poly closure.** "The coarse forms graph is poly-canonized" is the **meta-composition** of: the
**fine** adapter (`SchemeRecoveredByDepth fine`, genuine harvest content) + the F4/brick-1/`hmono` canonicity bridge +
`schemeAutGroup_coarse_eq_affineG` (mod Skresanov). It is **not** a further non-vacuous Lean predicate — any predicate
on the coarse `warmRefine` is vacuous or false. This is consistent with the project's stance that "poly" is a
meta-claim over a structural object, never a Lean runtime proof.

**✅ T1-cite + certificate LANDED (2026-07-04, axiom-clean).** The Skresanov 2-closure is now a **single named
generic citation** `AffineSchemeTwoClosed hneg := SchemeAutGroup(affineScheme G₀) ≤ affineG G₀` (carried like
`Theorem41Statement`/G3), and `schemeAutGroup_affineScheme_eq_affineG` pins `SchemeAutGroup(affineScheme G₀) = affineG
G₀` for **any** `G₀` modulo it — **one lemma, all four families** (instantiate `G₀ := similitudeGroup Q` /
`jointConeStab Qs` / Suzuki cone-stab; affine-polar instance = `schemeAutGroup_coarse_eq_affineG`). The honest
deliverable is bundled in **`routeC_polySupport`**: given the citation + the fine adapter's `SchemeRecoveredByDepth
fine`, it returns the triple `(i)` coarse Aut `= affineG(similitude)` `∧` `(ii)` fine harvest (genuine) `∧` `(iii)`
fine `≤` coarse (only refines) — the full structural support for the meta poly-canonization (+ F4 for iso-invariance).

**✅ T4 (cyclotomic dispatch) LANDED (2026-07-04, axiom-clean,
[`RouteCSeam.lean`](../GraphCanonizationProofs/ChainDescent/RouteCSeam.lean)).** The four-case
sketch dropped the **cyclotomic** branch (the affine residue is `{1-dim cyclotomic} ∪ {forms-graphs (c)–(f)}` — 5
cases). Fixed by generalizing the ScratchSeam dispatch: `reachesRigidOrCameron_seamDispatch` routes `S` that is
"Cameron, **or realized by *some* already-sealed scheme `Y`** (`SchemeRealizes f S Y ∧ SealDisj Y`)". Because the
cyclotomic seal `reachesRigidOrCameron_affineSlice` and every forms-graph seal conclude the **same `SealDisj` shape**,
both are instances of the single "sealed realized `Y`" disjunct — one theorem dispatches all of them. `cyclotomic_sealDisj`
supplies the cyclotomic `Y` (via `affineSlice`, mod its cited `TwinsAreSemilinear`/`PrimitiveCCClassification`);
`reachesRigidOrCameron_affineResidue` is the named combined seam. Carries the `htransport` (= L1) obligation, exactly
as ScratchSeam. **⟹ the cyclotomic branch is now first-class, and the dispatch is uniform over the whole affine residue.**

**Remaining follow-ups:** (T3) the multi-form instantiation is **already covered** by the generic pinning lemma (plug in
`jointConeStab Qs`); a concrete instance landed with the 2026-07-05 port; (T2) the C# |Aut| runtime uses
`schemeAutGroup_coarse_eq_affineG` to hand `AΓO(Q)` to Schreier–Sims. The classification premise §9.1/L3 is unchanged
and sound (Cameron + Liebeck 1987 + Skresanov 2020/22 + Ponomarenko). `AffineSchemeTwoClosed` (= Skresanov rank-3
2-closure) is registered in `chain-descent-citation-discharge.md`. The one carried Lean obligation across the seam is
still `htransport` (L1 — the `SealDisj`-transport along a realizing permutation; scoped positive, `ScratchSeam` /
§9.0a).

> **▶ §9.1 below is SUPERSEDED for the multi-form families by §9.0a** (its "transport the adapter seal along hiso"
> mis-types the fine/coarse schemes). It stays correct for affine-polar's *quasipoly* pair-route seal (ScratchSeam),
> which is a different, already-banked object. The live combine is §9.0a's finer→coarser transfer.

### 9.1 The Lean correctness object — one dispatch theorem over one cited premise

Target shape (the clean "reaches rigid or Cameron via Route C"):
```
theorem reachesRigidOrCameron_formsGraphResidue
    (hclass : FormsGraphResidueClassification)      -- the ONE cited premise that combines the 4
    (X) (hX : «X = the unbounded-WL rank-3 primitive schurian affine residue») :
    reachesRigidOrCameron X := by
  rcases hclass X hX with ⟨Q, hiso⟩ | ⟨Qs, hiso⟩ | ⟨Qs, hiso⟩ | ⟨ov, hiso⟩   -- affine-polar / alt / half-spin / Suzuki
  -- each case: transport the matching adapter's concrete seal along hiso
```
Beyond the four adapters this needs exactly two things:

- **(L1) Scheme-level iso-invariance of `reachesRigidOrCameron`** — `X ≅ Y → (reachesRigidOrCameron X ↔
  reachesRigidOrCameron Y)`, so each adapter's *concrete* `affineScheme(G₀)` seal transports onto the abstract
  `X`. **This is the one genuinely load-bearing NEW lemma.** Requires each disjunct (`SchemeBlockRecovered`,
  `AbelianConsumed`, `SchemeRecoveredByDepth`, `IsCameronScheme`) to be iso-invariant. *NB: distinct from F4 —
  F4 is iso-invariance of the recovered form (for the runtime canonicalization); L1 is iso-invariance of the
  seal predicate (for the correctness statement). Both needed, different halves.* **De-risk first:** spot-check
  whether the four disjuncts are already iso-invariant before committing (cheap, and it validates the whole plan).
- **(L2) The dispatch theorem** above, gated on **(L3) `FormsGraphResidueClassification`** = the cited premise
  (Skresanov's rank-3 2-closure classification: the unbounded-WL rank-3 primitive schurian affine residue is
  *exactly* affine-polar / alternating / half-spin / Suzuki, and it *hands over the concrete structure*
  `Q`/`Qs`/ovoid so the adapter can be built). Carried like `Theorem41Statement`/`G3` — **one named premise, not
  a finite pile**. This premise IS the "combination".
- **(L4) Wire into the existing residue seam** `reachesRigidOrCameron_viaAffineFormScheme` (idx 1207, the node-4
  hook), retiring its quasipoly `hFormCert` in favour of this poly seal.

Sizing: L1 medium (the real work), L2 small once L1 exists, L3 a citation/scoping task, L4 small–medium.

### 9.2 The C# runtime — build spec (grounded handoff for the next builder)

> **Read this before starting the C# build.** It names every existing piece to build on (exact file/method), every
> new piece to write (with its interface + dependencies), the pipeline, the Lean contract each piece must satisfy,
> and the probes/tests that validate it. Verified against the source 2026-07-04.

#### 9.2.0 The goal + the key reframe (what this session's Lean work changed)

**Goal:** for a residue the canonizer flags as a forms-graph family, recover the defining form, compute `|Aut|` and a
canonical labelling in poly time, and return them through the existing harness — instead of the (stalled) WL descent.

**★ HONEST VALUE PROPOSITION (2026-07-04, grounded against `RouteCF1Probe.cs`) — read before building.** The existing
harness (`ChainDescent` + `CascadeOracle`, deferral on) **already canonizes the probed forms graphs with no flag and
full `|Aut|` recovered**: `RouteCF1Probe.cs` asserts `res.Flagged == false` on VO±₄(3) and VO±₄(5) via the generic
cross-branch harvest. So at small `d`, **nothing is broken**, and the acceptance bar is NOT "no longer flags" (already
true). Route C's C# payoff is the **two things the generic harvest does not give**:
1. **A provably-poly, *certified* path** — orbits read off a *known, reconstructed* classical group `AΓO(Q)`, not
   harvested empirically. This is the runtime image of the Lean seal (correctness by construction, not "the harvest
   happened to complete").
2. **`d`-scalability** — the generic harvest's cost has an open `d`-factor (2026-06-28 finding: poly-vs-superpoly in `d`
   unresolved, infeasible to run at `d=8`); building the group from the recovered form is `poly(d,q)` by construction.
So the test strategy (§9.2.4) targets **"the built group equals the recovered classical group, and the labelling is
iso-invariant"**, NOT "flags → no-flag".

**The reframe that drives the design (this session):** the Lean group-pinning `schemeAutGroup_coarse_eq_affineG`
(`RouteCSeam.lean`, mod the Skresanov citation `AffineSchemeTwoClosed`) proves the answer group is
**exactly `affineG(similitudeGroup Q) = translations ⋊ AΓO(Q)`** — a *known* classical group. So the C# runtime does
**not** need to *harvest* `Aut` from the descent on the coarse graph (that's the node-4 stall). It **recovers `Q`,
constructs a generating set for `AΓO(Q)` directly, and hands it to the existing Schreier–Sims** (`PermutationGroup`),
which returns `|Aut|` and the base/labelling. Correctness is then *verified by reconstruction* (the generated group
stabilises the graph; `Q`+coords reproduce adjacency — `RouteCF1Probe.cs` already does the reconstruction half).
This is why the new load-bearing C# piece below is **the generator-list producer (C1b)**, which the old C1–C4 sketch
omitted.

#### 9.2.1 Existing C# infra to build on (exact names, all verified present)

| Piece | File · API | Gives the build |
|---|---|---|
| Schreier–Sims back-end | `PermutationGroup.cs` — `AddGenerator(int[])`, `Order:BigInteger`, `Contains`, `Orbit(pt)`, `BasePoints`, `Generators`, `Elements()` | **the |Aut| + base engine** — seed generators, read `Order` = `|Aut|`, `BasePoints` = the base. |
| Route-C group ops | `PermutationGroup.cs` — `RegularNormalPSubgroup(p)`, `NormalClosure(g)`, `HasExponentDividing(p)`; `Perm.Order/Pow/Compose/Inverse/FromCycles` | F1 socle recovery + perm arithmetic for building generators. |
| **F1** additive recovery | `AffineStructureRecovery.cs` — `Recover(PermutationGroup aut,int p,int origin) → AffineStructure{Translations,Origin,P,Dim,Coords[vertex]→(Z_p)^Dim}` | coordinates (mod the `O_p(Aut)` shortcut — see C4). |
| **A1** single-quadratic recovery | `QuadraticFormRecovery.cs` — `RecoverForm(int[] adj,int n,AffineStructure aff) → RecoveredForm{P,Dim,Monomials,Coeffs,Evaluate(v)}` (odd-q; null in char 2) | the `ι=Unit` case of C1. |
| Oracle seam | `ITransversalOracle.cs` — `Classify(n,adj,targetCell,path,PermutationGroup knownGroup) → TransversalDecision{Representatives}` | **where a Route-C oracle plugs in** (soundness: reps cover every orbit of the target cell). |
| Harness / residue seam | `ChainDescent.cs` — target-cell selection + `target == −1` (~L287), `CoveredByPathFixingAut` prune, deferral (~L274–287), `ResidualGroup` | where C3 wires the recovered-`Aut` canonicalisation. |
| Refinement | `WarmPartition.cs`, `RefinementFootprint.cs` | where the recovered-`Q` colouring is injected (the "fine scheme", §9.2.3). |
| Pre-processor template to clone | Tests: `Option2ExtractionProbe.cs`, `TwistConstruction.cs` (Option 2 Layer D — the F₂/rigid mirror) | the architecture to mirror (recover structure → build group → plug the seam). |
| End-to-end validation | Tests: `RouteCF1Probe.cs` (F1+A1 vs the REAL harness: `ResidualGroup` has full `|Aut|`; `Recover`'s `T` exact; `Q`+coords reconstruct the graph, 0 mismatches) | the harness↔F1↔A1 chain, already green. |

**Confirmed absent:** no `ITransversalOracle` implementation for Route C, no family dispatch, no classical-group
generator producer. The Lean `FormAdapter` interface has **no C# counterpart**. This is the whole build.

#### 9.2.2 Pieces to build (named, with interfaces + dependencies)

- **(C1a) `RecoverFormFamily`** — generalize `QuadraticFormRecovery` from one quadratic to a form **family**. New type
  `RecoveredFormFamily{Monomials, Coeffs[][] (one row per basis quadric)}`; `RecoverFormFamily(adj,n,aff)` solves the
  degree-2 vanishing system on the cone and returns a **basis of the vanishing space** (span of quadrics), not just
  `kernel[0]`. Covers Plücker (alt) + spinor (half-spin). Dep: F1 coords. Probe refs: `route_c_halfspin_probe.py`
  (dim 10), `route_c_reconstruct_probe.py` (`vanishDim=1` for the single-quadratic case). *Odd-q.*
- **(C1b) `ClassicalGroupGenerators` — THE new load-bearing piece.** Given the recovered form (family) + `AffineStructure`,
  produce a generating set for `AΓO(Q)` (resp. `⨅ₖ O(Q_k)`, Suzuki cone-stab) as **`int[]` permutations of the `p^d`
  vertices**, ready for `PermutationGroup.AddGenerator`. Contents: the **translations** (already have — `AffineStructure.Translations.Generators`), the **linear isometries/reflections** of `Q` (standard classical-group generator list — orthogonal reflections `x ↦ x − (B(x,a)/Q(a))a` realized as vertex permutations via `Coords`), and the **similitude scalings** (`x ↦ c·x` and one non-square-factor similitude — the `AΓO ⊋ AO` part, §9.0a). This is the C# realization of the Lean `similitudeGroup Q` / `affineG`. Dep: C1a. **Lean contract:** the produced group must equal `affineG(similitudeGroup Q)` — i.e. `PermutationGroup.Order` == `p^d · |AΓO^ε_d(q)|` **and** `Contains(AffineStructure.Translations generators)`. **★ ORDER-CHECK DESIGN (2026-07-04, corrected — do NOT hand-derive the closed form as the primary gate):** deriving `|AΓO^ε_d(q)|` by hand is error-prone (the `O^+`/`O^-` parity factor, the `(q−1)` similitude factor, the Frobenius `e` factor). **Bootstrap the check against the harness's OWN harvested `|Aut|`:** at small `d` the generic harvest recovers the *true* `|Aut|` (`RouteCF1Probe.cs` proves this), so C1b's order-check compares `built.Order` against `res.ResidualGroup.Order` for VO±₄(3,5), and only *extrapolates* to the hand-derived closed form once it is validated equal at small `d`. This removes the "checking against a wrong constant" risk and is the acceptance gate = the executable form of the group-pinning theorem `schemeAutGroup_coarse_eq_affineG`. Anchor the closed form on `|O^ε_{2m}(q)| = 2·q^{m(m−1)}·(q^m−ε)·∏_{i=1}^{m−1}(q^{2i}−1)` (q odd), with the similitude `×~(q−1)` and Frobenius `×e` (q=pᵉ; e=1 for the sealed q=p case) factors pinned against Kleidman–Liebeck AND the harvested order at `d=4`.
- **(C2) `FormsGraphClassifier.Detect(n,adj,aff) → FamilyTag`** — decide which family (affine-polar / alternating /
  half-spin / Suzuki) from SRG parameters `(n,k,λ,μ)` + cone-geometry signature (e.g. VSz(8)=SRG(4096,455,6,56) is the
  Suzuki fingerprint — `route_c_suzuki_probe.py`), select the C1a/C1b variant. C# analog of L3's classification.
- **(C3) residue-seam handler (integration decision (ii), 2026-07-04).** Two integration levels were scoped:
  **(i)** a `RouteCOracle : ITransversalOracle` returning short certified rep-lists (minimal harness change, but the
  reported `|Aut|` still comes from the harness harvest — so it does NOT deliver the `d`-scaling payoff, only fewer
  branches); **(ii)** a handler at the residue seam (`ChainDescent.cs target == −1`, `RecoveryOnly` currently returns
  `StuckResidual`) that runs C2→C1a→C1b, **verifies** (order-check + every generator stabilises `adj`), and if verified
  **adopts the built group** to report `|Aut|` and generate the canonical labelling — instead of flagging/stalling.
  **DECISION: (ii)** — the residue seam is exactly where the generic harvest stalls at large `d`, so it is the honest
  place for the certified path; (i) is the lighter fallback. Soundness: if the build fails to verify (misclassification,
  char-2 gap), the handler declines and the harness falls back to its existing flag — never a wrong answer. The C1b
  order-check is a **unit test independent of this choice**, so C1b can be built and validated before C3 is wired.
- **(C4) `GeometricCoordinatizer` (= §7a R1, the Aut-free path)** — replace `AffineStructureRecovery`'s `O_p(Aut)`
  shortcut (which consumes `Aut`, the potential circularity) with **adjacency-only** recovery: recover the isotropic
  lines through `o` via the local invariant `|N(o)∩N(x)∩N(y)|` (validated Aut-free by `route_c_bootstrap_probe.py`),
  build the polar-space geometry, read coordinates by Buekenhout–Shult; also recovers the field (F2, `q=pᵉ`). Biggest;
  can be last (F1's `O_p(Aut)` path is fine for de-risking/tests). Cite Buekenhout–Shult.

**Suzuki / char-2** is a separate track for C1a/C1b (σ-twisted forms, Arf; `route_c_suzuki_probe.py` has the 5 σ-forms);
the harness wiring (C3) and the classifier (C2) are char-agnostic.

#### 9.2.3 The pipeline + the "augment with recovered `Q`" step

```
abstract graph (residue, target==−1)
  → C2 Detect family
  → C4 GeometricCoordinatizer (or F1 Recover, de-risk path)   → AffineStructure (coords)
  → C1a RecoverFormFamily                                     → RecoveredFormFamily (Q up to scalar)
  → C1b ClassicalGroupGenerators                              → int[] gens of AΓO(Q)
  → PermutationGroup.AddGenerator×… ; .Order = |Aut| ; .BasePoints = base
  → C3 return certified Representatives (Orbit off the known group) + canonical labelling
```

**The "fine scheme" in C# = inject the recovered-`Q` colouring as an extra refinement colour** (colour each pair by
`RecoveredForm.Evaluate(Coords[x]−Coords[y])`, well-defined up to the global scalar) into `WarmPartition` before the
residue branches. This is the runtime realisation of "refine the coarse graph to the fine isometry scheme"; it is the
step that makes the descent discretize (the Lean `SchemeRecoveredByDepth fine`). Optional if C3 supplies the full
known group directly (then orbits are read off the group, not the refined WL) — **prefer C3's group route**; the
colouring-injection is the fallback / cross-check.

#### 9.2.4 Verification (how the builder confirms each piece — no Lean runtime model, so C# is the check)

- **C1a:** recovered family's joint cone == connection set (`Evaluate` all-zero ⟺ adjacent), 0 mismatches (extend
  `RouteCF1Probe.cs`'s reconstruction check to families).
- **C1b (the critical check):** `PermutationGroup` built from the generators has `Order` == the closed-form
  `p^d · |ΓO^ε_d(q)|`, `Contains` the translations, and every generator stabilises the graph (`adj` invariant). This is
  the empirical stand-in for the Skresanov citation — if the *generated* group already has the full order and stabilises
  the graph, the |Aut| answer is correct regardless of the 2-closure proof.
- **C3:** end-to-end — the canonizer returns the same labelling for isomorphic copies (extend the iso-stability bed) and
  `|Aut|` matches the closed form, on VO^±₄(3,5), Alt(5,q), VSz(8).
- Probes already validating inputs: `route_c_reconstruct_probe.py`, `route_c_f1_probe.py`, `route_c_halfspin_probe.py`,
  `route_c_suzuki_probe.py`, `route_c_bootstrap_probe.py` (C4).

#### 9.2.5 Lean contracts the C# must honour (the spec is not free-floating)

- `RouteCSeam.schemeAutGroup_coarse_eq_affineG` — **the group C1b builds IS `affineG(similitudeGroup Q)`**;
  its `Order` is `|AΓO(Q)|·p^d`. This is the correctness target for C1b.
- `RouteCSeam.routeC_polySupport` — the triple (coarse Aut = known group ∧ fine harvest ∧ fine refines
  coarse); C1b delivers (i), the colouring-injection (§9.2.3) delivers (ii)/(iii).
- The `FormAdapter` instances (`affinePolarAdapter`, `…_alternating`, `…_halfSpin`, `…_suzuki`) — each family's
  `separates` certificate; C1a/C1b are their runtime mirror (the form + its group).

**Ordering:** C1a → C1b (+ its order-check) → C2 → C3 (end-to-end) → C4 last. C1b is the load-bearing new piece and the
first to build; everything else is plumbing or already exists. The engine is the **symmetric mirror of Option 2's Layer
D** (clone `Option2ExtractionProbe.cs`/`TwistConstruction.cs`, swapping the F₂ extractor for `RecoverFormFamily`).
[[project_recovery_corecovery_duality_2026-07-03]].

#### 9.2.6 Lean adherence — what's backed vs. new territory (be explicit)

The C# splits into **Lean-backed** pieces (a faithful runtime of a proved theorem) and **new-territory** pieces
(correct + useful, but *not* backed by a Lean theorem — fine, as long as it is labelled). The build is applicable to
the Lean where it counts (the `|Aut|` answer is certified by a proved theorem) and honestly new everywhere the Lean was
never going to reach.

| C# piece | Status | Lean anchor / why not |
|---|---|---|
| **C1b built group == answer group** | **HARD contract (Lean-backed, tightest)** | `schemeAutGroup_coarse_eq_affineG` — answer group is *exactly* `affineG(similitudeGroup Q)` mod the Skresanov citation. A proper subgroup (forgetting the similitude scalings = AO not AΓO) or supergroup (spurious gens) both fail the order-check. **The order-check IS the executable form of the group-pinning theorem.** |
| **C1a null-when-kernel≠1** | Lean-backed (soft) | `NondegQuadricDeterminesForm` — `RecoverForm` returning null on kernel-dim≠1 is the runtime check of the citation's `vanishDim=1` hypothesis. |
| **C3 orbit reps + labelling** | Lean-backed (soft) | oracle soundness (reps one-per-orbit) + F4 `recoveredForm_colouring_equivariant` + brick-1 `isometryScheme_refines_similitudeScheme` (iso-invariance of the labelling). |
| **F1 / C4 coordinatization** | **NEW territory — NOT Lean-backed** | the Lean *starts* from the already-coordinatized `affineScheme`; recovering `(F_p)^d` from the abstract graph (socle / geometric) has no Lean model. A computation the proof assumes done. |
| **The "poly" claim** | **NEW / META — cannot be Lean-backed** | per the §9.0a vacuity correction, poly is inherently a meta-claim (any coarse-scheme predicate is vacuous-or-false). The C# runtime is the closest evidence; it discharges no Lean obligation. |
| **C2 classifier** | NEW (safe) | C# analog of the L3 classification citation; a runtime heuristic. Misclassification is *safe* (wrong family → wrong group → order mismatch → handler declines → harness flags), just not complete. |
| **Char-2 / Suzuki recovery** | NEW (separate track) | `suzukiAdapter` is sealed in Lean, but the C# char-2 form recovery (Arf, not the degree-2 kernel solve) is unbuilt; `RecoverForm` already returns null for `p==2`. |

**One-line takeaway:** rigid Lean↔C# coupling at exactly one point (C1b = group-pinning, checked by the order gate);
soft coupling at C1a + C3; everything else (coordinatization, poly, classification, char-2) is legitimately outside the
Lean. That is the *expected* shape — the Lean proves *correctness of the group answer*, and leaves *"recover the
structure"* and *"poly runtime"* as the meta/engineering layer.

#### 9.2.7 The FAMILY-DISPATCH architecture (built 2026-07-04) — how the four families interconnect

> **★ UPDATE (2026-07-05): Suzuki is now BUILT (runtime prototype), not a scaffold** — see the "★ SUZUKI BUILT" +
> "★★ FEASIBILITY WALL" blocks lower in this section. Live families = affine-polar + Suzuki; alternating/half-spin
> stay dormant (dense-infeasible). The paragraph just below is the original 2026-07-04 scaffold description.

Node 4 = four families; each is an **`IFormFamilyHandler`** (the C# mirror of the Lean `FormAdapter` engine), and
`RouteCCanonicalizer` dispatches over a registry. **Affine-polar is fully built; the other three are handlers with all
interconnection LIVE and only their per-family math core stubbed** — so a future builder fills a well-defined stub, not
a green field. Files: `FormFamilyHandler.cs` (interface + generic `FormFamilyHandlerBase<TInv>` + generalized
`RouteCCanonicalResult` + shared helpers), `AffinePolarHandler.cs` (real), `AlternatingHandler.cs` / `HalfSpinHandler.cs`
/ `SuzukiHandler.cs` (scaffolds — Suzuki since built, above). Tests: `RouteCFamilyDispatchProbe.cs` (regression through the
dispatch + stubs decline gracefully; 114/114 with the core suite).

**The four hooks each handler implements** (the base wires the flow: `RecognizeInvariant` → `Confirm` → emit
`StandardGraph` + `AutOrder`):
| Hook | What it does | Shared vs per-family |
|---|---|---|
| `RecognizeInvariant(adj,n)` | HARVEST-FREE iso-type from `(n, valency, SRG params)`; `null` ⟹ not this family (dormant) | per-family fingerprint |
| `Confirm(adj,n,harvest,inv)` | SAFETY: rules out a parameter-mate SRG | **odd-q families SHARE `ConfirmByMultiQuadricReconstruction` (C1a) — already wired**; Suzuki = char-2 (per-family) |
| `StandardGraph(inv)` | the canonical standard graph of the iso-type (emitted canonical form) | per-family construction |
| `AutOrder(inv)` | closed-form `|Aut|` of the iso-type | per-family formula |

**Safety invariant:** a dormant handler's `RecognizeInvariant` returns `null`, so its `NotImplementedException` cores are
never reached — the graph falls back to the descent. Activating `RecognizeInvariant` forces completing `StandardGraph` +
`AutOrder` (their throws fire otherwise) — a crisp completion contract.

**Per-family completion specs (the well-defined remaining work):**
- **Alternating** (`AlternatingHandler`, Lean `reachesRigidOrCameron_alternating`, Plücker sub-Pfaffians, odd q,
  multi-quadric): `Confirm` DONE (multi-quadric). TODO = (1) SRG fingerprint + params→iso-type; (2) `StandardGraph` =
  canonical alternating forms graph (joint zero of the standard Plücker quadrics); (3) `AutOrder` = alternating
  similitude group order.
- **Half-spin** (`HalfSpinHandler`, Lean `reachesRigidOrCameron_halfSpin`, 10 D₅ spinor quadrics `S0..S9`, odd q,
  multi-quadric): same shape as alternating. `Confirm` DONE. TODO = fingerprint + `StandardGraph` (spinor quadrics) +
  `AutOrder` (half-spin/spin group order). Probe `route_c_halfspin_probe.py` (dim 10).
- **Suzuki–Tits** (`SuzukiHandler`, Lean `reachesRigidOrCameron_suzuki`, CITATION-FREE, char-2): recognition LIVE for
  VSz(8)=SRG(4096,455,6,56). TODO = (1) generalize the fingerprint to `Sz(q)`, `q=2^{2e+1}`; (2) `Confirm` = char-2 form
  recovery (Arf / σ-twisted ovoid forms via the `GF(q)^4↔𝔽₂^d` bridge + second-derivative recovery — does NOT reuse the
  odd-q `RecoverFormFamily`); (3) `StandardGraph` = canonical `Sz(q)` ovoid graph; (4) `AutOrder` = `q^4·|Sz(q)|·factors`,
  `|Sz(q)| = q²(q²+1)(q−1)`. Probes `route_c_suzuki_probe.py` / `_determine_probe.py`.

**Note — C1b (`ClassicalGroupGenerators`) is odd-q single-quadratic only; the multi-form / char-2 group generators are
NOT needed for the runtime** (|Aut| comes from the closed-form `AutOrder`), only for an optional order-check verification
test — so they are off the completion critical path for each family.

**★★ FEASIBILITY WALL (2026-07-05) — the per-family runtime is size-bounded; only affine-polar + Suzuki are
dense-instantiable.** The whole pipeline is a dense `n²` adjacency (`adj[x*n+y]`, `StandardCayleyGraph` allocates
`new int[n*n]`). The families' vertex counts: affine-polar `VO^ε_{2m}(q)` = `q^{2m}` (feasible, `n≤625`); **alternating
`Alt(5,q)` = `q^{10}`** (smallest odd-q = `3^{10}=59 049` ⟹ **~14 GB dense** — infeasible; q=2 is size-OK but char-2, so
no feasible odd-q test exists); **half-spin D₅ = `q^{16}`** (even `2^{16}=65 536` ⟹ ~17 GB — infeasible at every q);
**Suzuki `VSz(q)` = `q⁴`** (q=8 ⟹ 4096, feasible; q=2 degenerate, q=32 ⟹ `2^{20}` infeasible). ⟹ **alternating &
half-spin runtime handlers are MOOT** in the dense infra (such graphs can't even be loaded; they'd never fire) — they
stay **dormant prototypes**, their correctness content being the sealed Lean adapters + probe-validated forms; they
become real only under a sparse/implicit graph representation (a large, separate infra item). **The one feasible +
genuine non-affine-polar runtime family is Suzuki (VSz(8)).**

**★ SUZUKI BUILT (2026-07-05, runtime prototype).** `SuzukiHandler` all four hooks implemented against
`SuzukiOvoid.cs` (GF(2ᵏ), Tits ovoid/cone, `StandardGraph`, σ-twisted GF(q) forms, + the F₂ degree-signature).
Validated (`RouteCSuzukiProbe`): VSz(8)=SRG(4096,455,6,56); the 5-dim σ-twisted GF(8) form family cuts the cone
exactly (the Lean `suzukiAdapter` model); and — the load-bearing new idea — a **FIELD-AGNOSTIC F₂ DEGREE-SIGNATURE
`Confirm`** that separates VSz(8) from its cospectral affine-polar mate VO⁻₄(q): the Tits-ovoid cone is genuinely
**cubic** over F₂ (cut by degree-3 forms) but **NOT quadric-cut**, whereas VO⁻₄(q)'s cone IS a quadric. Basis-invariant
(a linear F₂ change preserves monomial degree) ⟹ **no field recovery needed**. Negative control passes (Clebsch=VO⁻₄(2)
reads quadric ⟹ rejected). `Confirm`'s real path validated on F1-recovered coords. **Honest limits:** (i) only q=8 is
runnable; general-q recognition/`StandardGraph`/`AutOrder` are formula-only; (ii) `AutOrder = q⁴·|Sz(q)|·(2e+1)` is a
CITED closed form — the empirical order-check hits the PermutationGroup sifting wall at n=4096 (can't compute the true
|Aut| of a 4096-vertex SRG). Files: `SuzukiOvoid.cs`, `SuzukiHandler.cs`, `RouteCCanonicalizer.SuzukiAutOrder`, test
`RouteCSuzukiProbe.cs`.

**★ SLOT AUDIT (2026-07-04) — the 4-hook interface is COMPLETE for all four families; no missing slot.** Suzuki is an
outlier only in *implementation* (char-2/Arf inside its `Confirm`, and the `GF(q)⁴↔𝔽₂^d` module bridge inside
recovery/construction) — not in *interface shape*; even char-2 coordinatization is the shared `Coordinatize` (F1 works
for p=2). Two audit-driven refinements landed: (a) **`AffinePolarHandler` is now explicitly odd-q scoped** (declines
`q==2` at recognition) so **char-2 affine-polar** (Clebsch = VO⁻₄(2)) is a *clean separate slot*, exactly like Suzuki —
rather than a "recognized-but-always-declines" oddity; (b) a shared **`FormsGraphBuilder.StandardCayleyGraph(q, dim,
diff => …)`** builder (used by `StandardVO`, referenced in every stub's `StandardGraph` TODO) makes each family's
`StandardGraph` a near one-liner once its standard forms are known. Net: **five clean slots** — the four families plus a
char-2-affine-polar branch — each completed by filling fingerprint + `StandardGraph` (via the shared builder) + `AutOrder`
(+ char-2 `Confirm` for the two char-2 slots).

#### 9.2.8 The C4 hard core — conceptual analysis + ruled-out approaches (2026-07-04)

**The crux, precisely.** Harvest-free coordinatization for `p ≥ 5` requires recovering the AFFINE/ADDITIVE structure of
`V = F_p^d` from the graph. This is genuinely the fundamental theorem of projective/affine geometry (Von Staudt's algebra
of throws), and the reason is **CONE-BLINDNESS**: every constraint readable from the graph lives *on the cone* `{Q=0}`,
where `Q` vanishes — so `Q` (and, for larger `p`, all low-degree polynomials) satisfy every graph constraint and are
indistinguishable from `0`/linear. Formally: `Σᵢ f(x₀+id) = 0` automatically whenever `deg f < p−1`, so the line-sum
solution space `S = {linear} ⊕ {degree 2..p−2 polynomials}`; the ambiguity `= dim S − d` is **1 at p=3 (just `Q`) but 45
at p=5** (all quadratics + cubics).

**The Heisenberg picture (why it's structural).** The `S`-lift `φ(x) = (ℓ₁(x),…,ℓ_d(x), Q(x), …)` embeds `V`, and the
true addition lifts to a *twisted* law `(a,α)⊕(b,β) = (a+b, α+β+B(a,b))` — a Heisenberg/nilpotent group whose center is the
cone-blind part and whose **abelianization is the linear coords `L`**. Computing `L` needs the twist `B(a,b)` = the polar
form's off-cone values — exactly the cone-blind information. So there is **no bootstrap-free shortcut**: isolating `L`
needs the additive structure, which needs `B`, which is cone-blind.

**Ruled-out combinatorial shortcuts (probed, negative — do NOT re-walk):**
- **Recover addition `x+y` via the induced 4-cycle `o–x–z–y`** (`RouteCSumRecoveryProbe`): `x+y` is always a common
  neighbour of `x,y` avoiding `o`, but there are **~20 such candidates** at q=5 (5 at q=3) — not unique; pinning it needs
  the parallelogram/translation structure = the additive structure (circular).
- **Recover 2-flats via isotropic-line closure** (`RouteCPlaneRecoveryProbe`): the closure of `{o,x,y}` **stalls**
  (5 points at p=3, 9 at p=5, vs. the p² plane) — the isotropic lines *within* a plane are too sparse (non-adjacent
  in-plane pairs aren't on isotropic lines) to fill it. So planes are not recoverable by line-completion.
- **Parallelism by edge-count / perfect-matching**: aliases on perpendicular directions; distinguishing a *translation*
  matching from an *affine* one needs the line ordering = the scalar structure (cone-blind).

**★★★ CORRECTION (2026-07-05) — the "hard core" above was a LINE-SUM ARTIFACT; the natural method (frame + WL) is cheap
for ALL p.** A user push (recover scalars via a fixed frame, using incidences) led to the decisive experiment
(`RouteCScalarRecoveryProbe`): **greedy, coordinate-free individualize-refine discretizes VO^ε_d(q) in `d+1` steps,
SINGLE PATH, for every case tested** (q=3,5,7; d=4,6 — VO⁻₄(5): 5 steps → 625/625 cells; VO⁻₆(3): 6 → 729/729;
VO⁻₄(7): 5 → 2401/2401). So the whole graph is pinned by a size-`(d+1)` frame + 1-WL — no line-sums, no cone-blindness,
no O_p(Aut) harvest. The cone-blindness / 45-freedom obstruction was an **artifact of the line-sum method's
over-generation**, NOT fundamental (the `RouteCAmbiguityProbe`, q=5, separately confirmed the freedoms are
wrong-coordinatizations of the *same* graph: of 12 randomly-sampled freedoms, **`stillValid=0`** give a *distinct valid*
coordinatization — all 12 collapse to non-injective coords, 0 broke reconstruction — so the freedoms are wrong coords, not
distinct graphs). **Consequence — the correct framing:** harvest-free
coordinatization/canonicalization of these graphs is **easy empirically** (greedy WL-discretize, `O(d)=O(log n)` frame);
the ONE remaining open item is *proving* that discretization is poly (that the greedy choices are Aut-symmetric ⟹
single-path), which is **the project's EXISTING WL-dimension / node-4 core** — NOT a new Route-C-specific problem.
So my earlier "distinct narrow hard core" claim was wrong: the line-sum method manufactured a separate problem; the
natural frame+WL method reduces right back to the one open core the whole project already has. Structural facts confirmed
en route (all correct, `RouteCScalarRecoveryProbe`): scalars are DETERMINED once a frame is fixed (Aut point-stabilizer of
`o` is linear ⟹ fixes all multiples of a fixed axis point); the only real freedom is the frame/reflection choice; the
multiplicative structure recovers `−1` (=`4e` at q=5) for free, leaving the `2↔3` step, which the frame+WL discretization
resolves directly. **NEXT (revised): build the harvest-free confirmation as frame+WL discretize → compare to StandardVO
(cheap, all p), NOT the line-sum/Von Staudt route.** The p=3 line-sum coordinatizer stays as a landed alternative.

**(Superseded framing, kept only as history — do NOT pursue these; the CORRECTION above replaces them.)** Before the
frame+WL finding, the p≥5 options considered were: (a) implement Von Staudt's algebra of throws (multi-session); (b) a
*lighter sound* mate-ruling certificate without full coords; (c) accept the harvest-based confirmation for p≥5. **These are
all subsumed:** frame+WL (the CORRECTION) delivers exactly what (b) wanted — a cheap, sound, harvest-free discretization
that rules out mates by comparison to `StandardVO` — for all p, without Von Staudt (a) and without falling back to (c).
So the go-forward is the frame+WL confirmation; (a)/(b)/(c) are not live.

### 9.3 Later — the meta-poly rigor stage

The §7a residuals R1–R3 (build the geometric coordinatizer; cite Buekenhout–Shult / Payne–Thas for **classicality
only** — poly-time is an in-project effective-construction obligation, NOT a citation, per the §7a 2026-07-06
REFINEMENT; double-check `d=4` GQ) and, at the far end, the C#-design-into-Lean runtime model (the **cost model**,
`docs/chain-descent-cost-model.md`, now STARTED) that makes "poly" rigorous rather than a meta-argument. This is
the project's planned final stage; nothing above blocks on it.

### 9.4 Suggested ordering
1. Finish Suzuki (all four sealed).
2. **L1 spot-check** (are the four `reachesRigidOrCameron` disjuncts iso-invariant?) — cheap, de-risks the whole
   combination; do before L2.
3. L1 → L2/L3 → L4 (the clean Lean object), in parallel with C1–C3 (the runtime).
4. C4 + the R1–R3 / meta-poly rigor stage last.

---

## 8. Pointers  <!-- (kept below §9 for git-history stability; §9 is the forward plan) -->
- **Live route it replaces:** [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) (STATUS + §7 Route
  C sketch + §9.8.9 stall verdict).
- **Per-family analysis:** [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §11.4
  (alternating/half-spin/Suzuki), §11.5 (char-2), §1 item 1 (the Route A/B/C fork).
- **The rigid mirror (same meta-strategy):** [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md)
  §11 (Option 2, Layer D) + [[project_option2_f2_gap_2026-06-20]].
- **The seal it upgrades:** `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (banked, in `build.sh`);
  `GraphCanonizationProofs/PublicTheoremIndex.md` idx 1207-1237 (Stage A/B decl map).
- **What's-left map:** [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §3a.1, §4.
- **Cross-session memory:** [[project_recovery_corecovery_duality_2026-07-03]],
  [[project_formsgraph_wldim_viability_2026-06-28]].

---

*Maintenance: update STATUS as F1–F5 / A1–A4 land; keep the exact-name table (§4) in sync with source line numbers
(they drift — verify before citing); this doc is the Route-C staging point, the recovery doc §9.8.9 is the reason it exists.
§9 = the forward plan for combining the four seals (Lean L1–L4) + wiring the C# runtime (C1–C4), to build after Suzuki.*
