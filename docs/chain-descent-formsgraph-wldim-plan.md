# Proof plan — bounded WL-dimension for the affine forms-graph families (the seal's node-4 content)

> **What this is.** The live proof plan for **bounded Weisfeiler–Leman dimension** (= bounded individualization base ⟹
> `hSmallAutThin`) of the affine forms-graph rank-3 SRG families that are node-4-for-the-seal — affine-polar `VO^ε_{2m}(q)`,
> alternating, half-spin, Suzuki–Tits. By the Skresanov reduction (route-doc §9.9.18) these + the cited 1-dim cyclotomic
> slice are the *entire* small-Aut non-geometric schurian rank-3 residue. **The `VO⁻₄(3)` instance is SEALED** (axiom-clean);
> this doc is now the **generalization plan** — read §11.
>
> **▶ Build history + superseded routes** (the old STATUS saga, the `QProfileSeparatesAtBase` / M0–M5 route, the Lemma A/B
> build records, all spike logs) are frozen in
> [`Archive/ChainDescent/chain-descent-formsgraph-wldim-archive.md`](Archive/ChainDescent/chain-descent-formsgraph-wldim-archive.md)
> — consult before re-walking anything. This live doc keeps only: what's proved + the reusable architecture (§1), the
> difficulty calibration (§2), and the forward roadmap (§11).

---

## STATUS (read first)

> **★★★ 2026-06-28 REFRAME — the polynomial route is NOT this doc's WL-dimension/matching route; it is the RECOVERY /
> harvest route, and it sidesteps the open bounded-WL-dim conjecture. READ §1 "WHAT'S LEFT" item 1 for the full finding.**
> One-screen version: (1) the matching seal below is **quasipolynomial** and that is essentially TIGHT for any
> *individualization/WL* method — measured: frame & count base = `Θ(d)`, residue `d` UNBOUNDED, and bounded-WL-dim is
> **open math** (not Skresanov-citable). (2) **BUT running the actual chain-descent canonizer (route #5) shows it canonizes
> `VO⁻₄(q)` in a SINGLE PATH** (`leaves=1`, `BranchingNodes=0`, full `|Aut|` recovered) — forms graphs are huge-`Aut`, not
> rigid, so the `n^{|T|}` cost model is WRONG; the descent tree is poly. (3) The real cost is the **generic automorphism
> harvest**, which is faithfully poly in `n` at fixed `d` (`~n^{2.85}`) but carries a **`d`-factor beyond `n`** (same
> `n=256`: `d=4`=19s, `d=8`>9min) ⟹ infeasible at `d=8`. (4) **Whether that `d`-factor is super-poly (a new structure-aware
> "Witt" harvest is NECESSARY) or high-poly (the existing harvest already gives poly, just slow — Witt is an OPTIMIZATION)
> ~~is OPEN and gates the build~~ **— RESOLVED 2026-06-28 (code analysis): HIGH-POLY; Witt = optimization, not necessity.**
> The `ChainDescent.cs` harvest has NO exponential mechanism (every loop `n`-bounded + single-path ⟹ hard poly ceiling
> ≈ n⁵–n⁶ at fixed `n`), and `d ≤ log₂ n` (since `n=q^d ≥ 2^d`) collapses ANY `d`-overhead — `d^k` or constant-base `C^d`
> — to poly(n), so **poly-vs-exp-in-d is MOOT for polynomiality**. The existing generic harvest ALREADY canonizes forms
> graphs in polynomial time; the `d=8` 30× slowdown is a high-degree-poly worst case (q=2 = weakest WL refinement ⟹
> deepest `DeepenAnchor` + largest cells), not exponential. ⟹ **the build task is a COMPLEXITY PROOF of the existing harvest
> + the Lean recovery route, NOT a new oracle.** Full reasoning: §1 item 1 "RESOLVED" block. The
> recovery route = `SchemeRecovered`/`hFormCert`/Stage B.0 `coords_determine` (partly landed, `remaining-work.md:256-279`).
> Banked: quasipoly (the matching, below) + sub-exp (`reachesRigidOrCameron_viaSpielman`). Floor-lowering / q=pᵉ / other
> families are now LOWER priority (they widen the *quasipoly* result, which the recovery route would supersede).
> Full detail: §1 item 1 + [[project_formsgraph_wldim_viability_2026-06-28]] (memory).

**THE q=p AFFINE-POLAR SEAL IS DONE AND PORTED (2026-06-27, axiom-clean `[propext, Classical.choice, Quot.sound]`, in
`build.sh`).** Capstone **`AffinePolarSeal.reachesRigidOrCameron_affinePolar`** (`PublicTheoremIndex.md` →
`ChainDescent/AffinePolarSeal.lean`): for an odd prime `p` and a nondegenerate quadratic form `Q` on `Fin d → ZMod p`
(even `d ≥ 2`, `p ≥ 256`, `p ≳ 32d`), the affine-polar `VO^ε` residue **reaches the `reachesRigidOrCameron` disjunction
modulo `{G3}`, Witt-free, no `hSmallAutThin`**, carrying an explicit base bound
`T.card ≤ 128·(Nat.log 2 ((p^d)²) + 1) = O(d log p)` — a non-vacuous **quasipolynomial** WL-base for this slice. The
27 forms-graph scratch modules are now in `build.sh` (serial full build ~98s; whole closure axiom-clean).

**The chain — every step now in `build.sh`; full decl list = `PublicTheoremIndex.md`, design = §1 + §13:**
`per-anchor c₀ ≤ ¾` (increment 3, `PerAnchorBound.c0_le_threequarters`) + `bad-anchor β = O(d/q)` (increment 4,
`BadAnchorCount{,b,c,d}`) ⟹ `c̄₀ < 1` ⟹ a log-bounded **matching base** (increment 5, `Matching` +
`AffinePolarSeal.exists_pow_matching_block`) ⟹ `ZProfileSeparatesK` ⟹ `IsotropySeparatesAtBaseK` ⟹ the q=p seal. The
observable↔count **bridge** (`χ(det G₂) ↔ Z_u(S)`, `ObservableCountBridge{A,B,C,D,AllK}` / `IsotropicIncidenceCount{,K}`) is the analytic
heart; the whole analytic chain is **field-generic** (`FieldGeneric*`), with `affineE` a single endpoint relabel.

**★ REUSABLE BUILDING BLOCKS — the non-obvious assets a future contributor should know EXIST (not rebuild):**
- **Schwartz–Zippel over a finite field** — `PencilTBound.mvPoly_zeros_count_le` (`p ≠ 0 ⟹ #zeros ≤ totalDegree·|K|`).
- **Abstract first-moment / matching lemma** — `Matching.exists_separating_base` (`|ι|·Fᵐ < |W|ᵐ ⟹ a separating
  base`, pure cardinality, no probability), with the **log-free length bound** `AffinePolarSeal.exists_pow_matching_block`.
- **Coordinatization workhorse** — `Coordinatization` turns linear-functional / quadratic-form data into `MvPolynomial`
  evaluations (`coordPoly`, `gramQuadPoly`, `pencilDetPoly`) — what puts a pencil determinant under Schwartz–Zippel.
- **χ-kills-squares** — `ObservableCountBridge.chi_configDet_eq_chi_pairForm`: the `½·polar` factor-2 and any change-of-basis
  `det` enter only as squares, so the quadratic character `χ` erases them (no "is this the standard basis?" obligation).
- **Gauss-sum closed forms** — `IsotropicIncidenceCount*`: `configGaussSum_eq_det` (config-Gram det ↔ Gauss sum) + `card_quadForm_eq`
  (isotropic count via an orthogonal anisotropic basis); plus `GaussCount.gaussSum_sq_ne_zero` / `sum_addChar_quadForm_ne_zero`.
- **polarRad as a `Submodule`** + the **corank-uniform** proper-subspace bound `|radical|·q ≤ |V|` (`PencilTBound`) —
  avoids any corank case-split.
- **Field-genericity** (`FieldGeneric*`) — the analytic content needs no `ZMod p`-specific fact; this makes q=pᵉ
  (Layer D) and the other families a typeclass swap, not a re-proof.

**WHAT'S LEFT (frontier, roughly priority order):**
1. **O(1) / frame WL-dim — VIABILITY SPIKED (2026-06-28, `Probe_FrameWLScaling`); the finding RESHAPES this item.**
   The canonizer charges ~`n^{|T|}` (a rigid residue forks `n` ways per individualization; the deterministic-base escape
   would prove too much and was not found in prior search), so the base size `|T|` is the exponent. **MEASURED (best-fit
   minimal individualization base of `VO⁻_d(q)`): `|T| = d+1`, EXACTLY — flat in q, linear in d** (q-sweep d=4: base
   `5,5,5,5` at q=2,3,4,5; d-sweep: `5,7,9` at d=4,6,8; matches the group base `1 (translations) + d (rigidify O⁻_d)`).
   **CONSEQUENCE — a frame is NOT `O(1)`; it is `Θ(d)`.** So:
   - **Fixed d, growing q** (the `q ≳ 32d` slice we work in): frame base `d+1` is *constant in q* ⟹ `n^{O(1)}` =
     **POLYNOMIAL**, strictly beating the matching's `O(d log q)` base (`n^{O(log q)}` = quasipoly). This is the frame's
     genuine win, and it is real and buildable (generalize `VO⁻₄(3)`'s `T₉` to a uniform `(d+1)`-vector rigidifying frame,
     proven by coordinate recovery + the closed-form counts — no `decide`).
   - **Growing d**: frame base `d+1` gives `n^{Θ(d)}` = quasipoly/super-poly — **no better than the matching.** Pure
     individualization (frame OR matching) is capped at `Θ(d)` base because killing `O⁻_d(q)` needs `d` rigidifying points;
     `O(1)`-in-d is information-theoretically impossible for individualization. **TRUE all-d polynomial therefore needs
     `O(1)` k-WL dimension (a fundamentally different algorithm — k-tuple WL + iteration, NOT individualization).**
   **CAVEAT NOW CLOSED (2026-06-28, `Probe_CountBaseScaling`): the richer count predicate `IsotropySeparatesAtBase` is
   ALSO `Θ(d)`** — min count-base measured `= d` exactly (q-sweep d=4: `4,4,5,4` @ q=2,3,4,5; d-sweep: `4,6,8,10` @
   d=4,6,8,10). Counting shaves the constant (`d` vs `d+1`) but not the scaling. (Aside: so `T₉=9` for `VO⁻₄(3)` was
   oversized — minimal count-base there is ~4; `T₉` was sized for `decide` convenience.) **Both the project's own Stage
   B.0 (`O(Q)` discretizes at the basis-frame `d+1`, `remaining-work.md:261`) and these probes agree: base = `Θ(d)`.**
   - **TWO FACTS THAT RESHAPE THE WHOLE ITEM (verified 2026-06-28):**
     (i) **The residue dimension `d` is UNBOUNDED** (the canonizer faces `VO^ε_{2m}(q)` with growing `m`; plan §1 target
     "`d` bounded ⟺ small-Aut", and `general-cc-separability §1A` — the carve-out does NOT bound the forms-graph residue's
     `d`). So `Θ(d)` base ⟹ `n^{Θ(d)}` = **quasipolynomial worst-case (small q, `d~log n`), NEVER polynomial.**
     (ii) **Bounded WL-dimension for these forms-graphs (c)–(f) is an OPEN MATH PROBLEM, not citable**
     (`reference_srg_wl_literature_2026-06-17`: "the wall is genuinely open in math, no citable theorem either direction";
     **Skresanov gives the *group* `G^(2)` 2-closure structure, NOT the WL-base bound** — "computing `G^(2)` ≠ proving the
     gap bounded"). So the "k-WL route" is *not* a turnkey citation; it is the open node-4 conjecture.
   - **CORRECTNESS IS NOT AT STAKE (C3, `reference_srg_wl…:54`): the high-WL-dim case is handled by FLAGGING by design**
     (the seal is keyed IR-core-free via `reachesRigidOrCameron_viaSymmetricRecovery`, dropping `DiscretizesAtBases`; the
     unbounded-base case is the IR-solver's row 4 ⟹ flag). So the WL-dim work is about **reducing flagging / usefulness on
     the forms-graph family, not seal correctness.**
   **⟹ STRATEGIC CONCLUSION: the O(1)/frame route CANNOT reach polynomial (base is `Θ(d)`, `d` unbounded), and the true
   polynomial endpoint (bounded WL-dim O(1) via k-WL) is OPEN MATHEMATICS, not a build task.** The realistic, *provable*
   deliverables for the forms-graph family are **quasipolynomial** (the matching — built) and **sub-exponential**
   (`reachesRigidOrCameron_viaSpielman` — citable). A frame would only buy the fixed-d-poly slice (a slice, not the
   residue) or a constant improvement — **NOT a priority, since it does not advance the polynomial goal.** Pushing toward
   polynomial = attacking the open bounded-WL-dim conjecture (a GI-theory frontier; Skresanov affine-2-closure carve and
   the `s(X)=b(X)−b(G)` gap are the leads, both open).
   **★★★ ROUTE-#5 FINDING (2026-06-28, `Probe_FormsGraphCanonScaling`) — the cost model above is WRONG for forms graphs;
   there is a THIRD route that sidesteps the open WL-dim problem.** Running the ACTUAL chain-descent canonizer on
   `VO⁻₄(q)`: for `d≤6` it canonizes in a **SINGLE PATH** — `leaves=1`, `≈d+2` nodes, depth profile `[1,1,…,1]`, recovering
   the **full** `|Aut|` (q=2→1920=|Aut(Clebsch)|✓, q=3→233280, q=4→12533760). **The `n^{|T|}` charge that drives the whole
   quasipoly/WL-dim pessimism assumes a RIGID residue that forks `n` ways per individualization — but forms graphs are the
   OPPOSITE (huge `Aut`), so the harness's a-posteriori orbit-pruning collapses ALL forking to one path.** ⟹ the descent
   TREE is polynomial (single path, depth `~d~log n`), regardless of WL-dim. **The real barrier is the PER-NODE HARVEST
   cost** (generic automorphism discovery — `CascadeOracle` is 30 lines, pruning lives in `ChainDescent.cs`): at `d=8` it
   does NOT resolve even at budget=50 (would flag instantly if forking) ⟹ stuck inside `<50` nodes ⟹ per-node harvest
   blows up, NOT the tree. **For forms graphs the automorphisms are isometries, findable in poly time by constructive Witt
   = exactly Stage B.0 `coords_determine` (`remaining-work.md:261`).** So the **polynomial route = single-path descent +
   a STRUCTURE-AWARE (Witt) per-node harvest**, which is the RECOVERY route (`SchemeRecovered`/`hFormCert`), and it
   **sidesteps the open bounded-WL-dim conjecture** (harvest ≠ WL-discretization; forms-graph iso is known poly via the
   classical-group algebra). **This REORDERS the strategic conclusion: the matching/frame WL-separation analysed the
   harder, suboptimal route (try bases ⟹ quasipoly); the harvest route the canonizer actually uses is poly and is the
   right target.** NEXT = (a) implement a constructive-Witt per-node harvest in C# + confirm `d=8,10,12` stay
   single-path-fast; (b) align the Lean seal to the recovery route (depth `d+1` frame + poly Witt harvest =
   Stage B.0/B.1 `coords_determine`/`reachesRigidOrCameron_viaSimilitudeForm`, already partly landed).
   **★ SHARPENED (2026-06-28, instrumented `BranchingNodes`/`Phase2Nodes`/wall-clock) — corrects an over-claim:**
   (i) **NO real branching, confirmed:** every completing case has `BranchingNodes=0`, `Phase2Nodes=0`, `leaves=1` (true
   single path), and budget=50 at `d=8` never flags (committed nodes `<50`). (ii) **At FIXED d the canonizer is genuinely
   polynomial in n** (`d=4`: `~n^{2.85}`, `45→703→18757ms` for `n=16,81,256`) — it is *faithfully poly on the n-axis*,
   matching its track record. (iii) **The harvest cost depends on the form dimension `d` BEYOND `n`:** at the SAME `n=256`,
   `d=4` (q=4) completes in 19s but `d=8` (q=2) exceeds **9 min** (`>30×`) — a real `d`-factor, infeasible at `d=8`. (iv)
   **BUT poly-in-d vs exp-in-d is UNRESOLVED by timing** — only `d=4,6` complete, too short a range (a `30×` factor over
   `Δd=4` fits both `d^5` and `~2.4^d`). So the honest status: **not a correctness blindspot** (the canonizer canonizes
   correctly, single-path, right `|Aut|` — it does NOT flag); a **performance** wall at growing `d`. The constructive-Witt
   harvest is poly-in-d *by construction*, so it removes the `d`-factor regardless — **justified as the scaling fix; whether
   the generic harvest is strictly super-poly (Witt "necessary") or high-poly (Witt "optimization") is open.** Decisive
   resolutions: analyse the harvest recursion's `d`-complexity directly, OR build Witt and observe `d=8,10,12` go fast.
   The single-path STRUCTURE is solid; the harvest is NOT gated on the open WL-dim math.
   **★★★ RESOLVED (2026-06-28, code analysis of the `ChainDescent.cs` harvest — the "analyse directly" resolution above):
   the generic harvest is POLYNOMIAL; Witt is an OPTIMIZATION, not a necessity. Poly-vs-exp-in-d is MOOT for polynomiality.**
   Two pillars. **(P1) No exponential mechanism — hard poly ceiling at fixed `n`.** Every harvest loop is `n`-bounded and
   nothing forks: the committed `Search`→`Branch` descent is single-path (`BranchingNodes=0`, and capped at `budget=16n⁴`
   regardless else it flags); **`DeepenAnchor` is single-path** (one sub-cell + one vertex per level, strictly refining ⟹
   ≤ `n` levels, hard cap `depth ≤ _n`); **`ReplayDeepening` is single-path** (≤ `|seq|` levels); the rep loops are
   `≤ |cell| ≤ n`; and the helpers (`TwistConstruction` O(n) dict-match, `RefinementFootprint` O(n log n) diff,
   `CoveredByPathFixingAut` BFS) are poly. So total work = a *product of n-bounded factors* `committed-path(≤budget) ×
   cells(≤n) × DeepenAnchor-levels(≤n) × reps(≤n) × refine(poly)` = **poly(n)** — a hard ceiling (≈ n⁵–n⁶) that `d` cannot
   breach. **(P2) `d ≤ log₂ n`** (since `n=q^d ≥ 2^d`) ⟹ ANY d-overhead — `d^k` OR even constant-base `C^d` — is
   `≤ C^{log₂ n} = n^{log₂ C} =` **poly(n)**. So both branches of the "gating question" collapse to poly(n); the real
   distinction was always *single-path poly(n)·poly(d)* vs *rigid-forking `n^{|T|}`*, already settled by `BranchingNodes=0`.
   **No contradiction with the matching's "quasipoly never poly":** the matching charges `n^{|T|}` (multiplies `n` PER
   base-element ⟹ `n^d=q^{d²}` quasipoly), whereas the harvest pays `n` ONCE + a `poly(d)` single-path overhead (the
   huge-Aut orbit-pruning collapses the n-way fork). The `d=8`/`n=256` 30× slowdown is consistent with a **high-degree
   polynomial** (≈ `d^5` at q=2 — weakest WL refinement ⟹ deepest `DeepenAnchor` + largest cells; `n=256` at ~n⁵ ≈ 10¹²
   ops ≈ minutes), NOT an exponential. ⟹ **the existing generic harvest already canonizes forms graphs in POLYNOMIAL time.**
   Witt (Stage B.0 `coords_determine`) lowers the polynomial DEGREE / wall-clock at small `n` — worth building for
   feasibility at large `d` — but is not needed for the *polynomial* claim. **The build task is a COMPLEXITY PROOF of the
   existing harvest + the Lean recovery route, NOT a new oracle.** Remaining genuine open piece for the LEAN seal: the
   recovery route must show the `Θ(d)` frame is iso-invariantly *constructible* (poly), not *searched* (`n^{|T|}`) — that
   is exactly what the single-path empirical finding asserts and `coords_determine`/`viaSimilitudeForm` must formalize.
2. **Floor-lowering** `q ≳ 32d → O(d) → small-q` — the matching has its OWN q-floor from the isotropic shells (NOT the
   per-anchor c₀). Needs a TIGHT corank shell count (→ `q≳O(d)`), then larger separating frames for small-q-growing-d.
   The landed-but-unwired route-2 / corank-2 lemmas (`c0_le_route2`, `c0_le_threequarters_corank2`, on disk, axiom-clean,
   NOT in `build.sh`) + the design = §13 "Floor-lowering assets".
3. **q = pᵉ scheme seam (Layer D)** — `efield : GaloisField p e ≃ₗ F_p^{de}`; the q=p adapter `FieldGeneric`
   is the template. §11.6.
4. **Other schurian families** (alternating / half-spin) — reuse the skeleton + the field-generic chain. §11.4.
5. **char-2 + Suzuki** — one bespoke track (Arf + additive trace; Mathlib substrate absent); deferred. §11.5.
6. **The seam build** — `htransport` (spiked `ScratchSeam`, on disk), mechanical, on the landed `forcedNode_relabel`. §11.6.

**NOT the open SRG-WL-dimension problem** — structure/base/answer are known (Skresanov); see §2.
**History** (increment 3–5 blow-by-blow, sessions 1–3, the `VO⁻₄(3)` instance seal, the spike/dead-end log) →
`docs/Archive/ChainDescent/chain-descent-formsgraph-wldim-archive.md` (+ git). Cross-session detail =
`[[project_witt_free_bridge_lead_2026-06-20]]`; "what's left" map = `chain-descent-remaining-work.md` §3a.1.

---

## 1. The target, what's proved, and the reusable architecture

**Target theorem (uniform form).** Let `X = affineScheme G₀` be a primitive rank-3 schurian SRG on `V = F_q^d`, with
`G₀ ≤ ΓL(V)` a classical *similitude* group preserving a nondegenerate form and `d` bounded (small-Aut: `|Aut| = n^{Θ(d)}`
poly ⟺ `d = O(1)`). Then `X` individualizes to **discrete** at a base of size `O(d + log q)` (§11 reframe — not the naive
`d+1`), hence has bounded WL-dimension ⟹ `hSmallAutThin` for this residue. By Skresanov (route-doc §9.9.18) + the
cyclotomic citation this is node-4-for-the-seal, modulo the CFSG identification `{Cameron, Liebeck, Skresanov}`.

> **▶ SCOPE NOTE — `d = 2` is OUT OF SCOPE by construction (not a gap).** The target affine-polar families are
> `VO^ε_{2m}(q)`, so `d = 2m ≥ 4`; the per-anchor capstone `PerAnchorBound.c0_le_threequarters` carries `hq1 : 64q² ≤ |V| = qᵈ`
> (⟺ `q^{d−2} ≥ 64`, i.e. `d ≥ 3` for any `q ≥ 8`), which the families satisfy with room to spare. `d = 2` is excluded both
> there and at the level of the *phenomenon* (R3 caveat: "the joint phenomenon lives at `d ≥ 4`; `d = 2` is too degenerate").
> So a reader should not treat the `d ≥ 3` hypothesis as missing coverage — it is the families' own range.

**What's proved — the `VO⁻₄(3)` instance (axiom-clean).** Module / decl map:

*In the build* (`build.sh` + `lakefile.toml`, axiom-clean, green ~33s cached / ~140s cold):
- **`ChainDescent/GaussCount.lean`** (Mathlib-only) — the Gauss toolkit: counts (`count_eq_charsum`, `countk_*`,
  `count_pi_setValued`), Gauss sums (`sum_addChar_*`, **`card_quadForm_eq`** = the affine-quadric level-set count),
  `sum_addChar_multiQuad`/`_zero`/`sum_addChar_linearMap`.
- **`ChainDescent/CascadeAffine.lean §OrthogonalForm`** — the capstone chain. **★ live capstone
  `reachesRigidOrCameron_viaIsotropySeparates_wittFree`** (`PublicTheoremIndex.md:1248`): seals the `VO^ε` residue from a
  bounded base + `IsotropySeparatesAtBase Q T`, **no Witt, no `hSmallAutThin`** (Witt-free bridge =
  `relationRefinesIsotropy_similitude` + `separatesAtBase_of_isotropySeparates_weak`). Target predicate
  **`IsotropySeparatesAtBase Q T`** (`:3102`); shared back-half `coords_determine` (`:2640`).

### Forms-graph pair-route module map

**Restructure note (2026-06-28).** The pair route was ported into `build.sh` and restructured from 27 `Scratch*` files
into 14 named modules. **Authoritative sources: `scripts/build.sh`'s `MODULES` array (one-line module annotations) and
`GraphCanonizationProofs/PublicTheoremIndex.md` (per-decl descriptions — every decl of the 14 modules is described).**
The decl-level math writeup that used to live here is now fully captured by those; this is the orientation map.

**In build (14 modules, axiom-clean `[propext, Classical.choice, Quot.sound]`, topological order):**
- **`Matching`** — the abstract first-moment / union-bound separating-base lemma `exists_separating_base` (REUSABLE, general).
- **`PairForm`** — the per-pair χ-separation foundation: `pairForm` (the `|S|=2` config-Gram det as a quadratic), the
  Gauss bridge, the `M(y,z)` closed form, `normT_le`.
- **`PencilTBound`** — the `‖T‖` magnitude bound: pencil radical (`polarRad` Submodule, corank-uniform), Schwartz–Zippel
  `mvPoly_zeros_count_le` + `degenerate_count_le`, the two-bucket arithmetic (REUSABLE), capstone `normT_bucket_bound`.
- **`PerAnchorBound`** — the per-anchor non-separation capstone `c0_le_threequarters` (`NS ≤ ¾·|V|`) + the counting identity.
- **`BadAnchorCount`** — the good-anchor fail bound `good_anchor_fail_le_const` (`≤ 15/16·|V|`) + the structural β reduction.
- **`Coordinatization`** — form data → `MvPolynomial` evaluations (`coordPoly`/`gramQuadPoly`/`pencilDetPoly`) (REUSABLE);
  what puts the pencil determinant under Schwartz–Zippel.
- **`GoodAnchorNonvacuity`** — `exists_hgood` (a good anchor exists for `u≠v`, nondeg `Q`, `finrank≥2`, `|K|≥7`).
- **`IsotropicIncidenceCount`** — Lemma A over `ZMod p`: the isotropic-incidence count as an explicit Gram-function
  (`card_quadForm_eq`, `configGaussSum_eq_det`, `levelset_count_eq`).
- **`IsotropicIncidenceCountK`** — Lemma A over an abstract finite field `K` (the field-generic mirror).
- **`ProfileReduction`** — the `ZProfileSeparates` reduction (D1) + the B-M1 incidence step (`incidence_agree_V`).
- **`ObservableCountBridge`** — the χ(det G₂)↔`Z_u(S)` bridge over `ZMod p`: the `|S|=2` even-`d` closed form
  (`levelset_count_collapse`), the χ-kills-squares identification (`chi_configDet_eq_chi_pairForm`), capstone
  `jointIsoCount_ne_of_chiSep_pair`.
- **`ObservableCountBridgeK`** — the same bridge over abstract `K` (`jointIsoCountK_ne_of_chiSep_pair`).
- **`FieldGeneric`** — the abstract-`K` substrate: V-indexed predicates (`ZProfileSeparatesK`, `IsotropySeparatesAtBaseK`,
  `isotropySeparatesK_of_zProfileSeparatesK`), the soft endpoint `zProfileSeparatesK_of_zSep`, and the q=p `affineE` adapter
  `reachesRigidOrCameron_viaIsotropySeparatesK_wittFree`.
- **`AffinePolarSeal`** — the matching assembly + the q=p seal **`reachesRigidOrCameron_affinePolar`** (carries
  `T.card = O(d log p)`), via the keystone `exists_pow_matching_block`.

**On disk, NOT in build — follow-up (detail: §13 "Floor-lowering assets" + the archive):**
- **Floor-lowering** (per-anchor tightening below `q≥256`; axiom-clean, verified, not yet wired): `ScratchPencilCorank{,2}`,
  `ScratchPencilBridge`, `ScratchPencilRegroup`, `ScratchTBoundCorank{,2}` (`c0_le_threequarters_corank{,2}`, drops `hq2`,
  reaches `q≥16`), `ScratchRoute2{,Arith}`, `ScratchCountTight` (`c0_le_route2`: `NS ≤ (1−1/4q²)·|V|`, no threshold).
- **`VO⁻₄(3)` instance** (the concrete `decide`-based proof-of-concept; its *result* is superseded by `AffinePolarSeal` as
  the general route, kept as a worked instance): `ScratchBM3Bridge`, `ScratchBM3Glue` (`vo4minus_seal`).
- **Seam spike**: `ScratchSeam` (the one mechanical `htransport` obligation; §11.6).

**Rename / merge map (new ← old).** `Matching`←ScratchMatching · `PairForm`←PairSep · `PencilTBound`←Corank+GoodAnchor+
Bucket+ChiNorm+TBound · `PerAnchorBound`←Count+C0+C0Final · `BadAnchorCount`←Incr4+Incr4b · `Coordinatization`←Incr4c ·
`GoodAnchorNonvacuity`←Incr4d · `IsotropicIncidenceCount`←LemmaA · `IsotropicIncidenceCountK`←LemmaAK ·
`ProfileReduction`←Crux+LemmaB · `ObservableCountBridge`←BridgeA+B+C+D · `ObservableCountBridgeK`←BridgeAllK ·
`FieldGeneric`←FieldGen+BridgeK+FieldGenAdapter · `AffinePolarSeal`←Incr5. (Orphans `ScratchBridge` / `ScratchBridgeZ`
were deleted — their `pairCount_ne_of_chiSep` / `zProfileSeparates_of_zSep` are superseded by the field-generic
`pairCount_ne_of_chiSep_field` (in `ObservableCountBridge`) and `zProfileSeparatesK_of_zSep` (in `FieldGeneric`).)

- **`FormsGraphConcrete.lean`** (IN BUILD, `lakefile.toml` `defaultTargets`, axiom-clean, GENERAL in `p,d,Q,T`) — the
  **route-(b) decomposition** and a live consumer. `QProfileSeparatesAtBase` (`:157`, arbitrary base `T`: agreeing isotropy
  counts ⟹ the field-valued `Q`-profile `{Q(v−t)}` agrees) + **`isotropySeparates_of_qProfileSeparates`** (`:174`, PROVEN
  general — `QProfileSeparatesAtBase + nondeg ⟹ IsotropySeparatesAtBase`, via the landed `coords_determine`). NB this is NOT
  superseded (corrects the old note): it is a second, general decomposition whose back-half is landed; only its front-half
  `QProfileSeparatesAtBase` is the open crux (`:145` — shell-blindness; never discharged in Lean even for VO⁻₄(3), probe-only).
  Route (a) (Lemma A/B → `sigF` `decide`) is what closed the *instance*; (a)/(b) share the SAME open core (joint `Z(S)`).

**The reusable architecture (template for every family — §11).** `IsotropySeparatesAtBase Q T` ⟸ **Lemma A** (count =
explicit function of the config Gram) ∘ **Lemma B** (the antecedent reduces to restricted-count agreement over sub-frames)
∘ an **injectivity kernel** (the restricted-count profile over sub-frames recovers `u`) → fed to the **wittFree capstone**.
For the single instance the kernel was discharged by `decide` on the bridged `Nat` counts; the generalization must replace
that finite check by the **uniform** kernel (§11.1) — the one open research problem.

---

## 2. Why this is NOT the open SRG-WL-dimension problem

A fresh reader's natural worry: *"the kernel is uncited, so it's open research, not formalisation."* Honest calibration:

**True (don't overclaim against it):** the kernel is **uncited** (genuine content to prove, not look up); bounded WL-dim of
the affine forms-graphs is **unpublished** (no citation, route-doc §9.9.18b); uniformity over all `q`, the Skresanov
small-degree exceptions, and the Suzuki outlier are real.

**Wrong — why it's a different difficulty class:** the open SRG-WL problem is hard because the SRG is a **black box**; here
every black-box element is removed. (1) The **structure is known** (Skresanov: explicit similitude group + nondegenerate
form). (2) The **base is handed**, not searched (the group base, now `O(d+log q)`). (3) The **WL machinery is already done**
— the landed engine reduced "bounded WL-dim" to a finite, geometry-specific count-separation statement; no WL theory
remains. (4) The **probe gives the answer and the mechanism** (`Probe_FormsGraphs`: discreteness at the bounded base; the
counts recover the field-valued form, not binary isotropy).

**Honest framing:** the kernel is *concrete uncited classical finite geometry about an explicit family with a handed base*
— unpublished because nobody needed it, not because it resists technique. The genuine residual *mathematical* difficulty is
narrow and located: the **non-isotropic shell** and **char-2** (§11.1 / §11.5). The `VO⁻₄(3)` seal confirms the whole
architecture end-to-end; §11 is the generalization.

---

## 11. FULL ROADMAP to the schurian-residue seal (modulo `{G3}`) — revised 2026-06-24

> **What this is.** The total remaining work to prove, **unconditionally modulo the `{G3}` citation stack**, that after
> deferred-decisions stage 1 (every decision real, IR-solver not yet run) the graph residue is **rigid or Cameron** for
> the small-Aut non-geometric **schurian** rank-3 residue (the node-4 obligation `hSmallAutThin` was a placeholder for —
> but per AUDIT-S finding 3 the forms-graph route does NOT literally discharge `hSmallAutThin`; it is a *parallel* seal
> route + a cited classification seam, §11.0/§11.6). The single `VO⁻₄(3)` instance is sealed (§1, `vo4minus_seal`); this
> section is the generalization program. **Scope:** the schurian residue only — the non-schurian wall is the IR-solver's
> job (separate thread, `project_option2_f2_gap`). `SchurianScheme` is *carried* (`orbitalScheme H`) and **resolved FREE**
> by AUDIT-S (schurian by construction; nothing to discharge).
>
> **▶ ENDPOINT DISCIPLINE (read first).** The target is the **full unconditional seal + a clean citation stack** — NOT a
> partial seal carrying a messy `modulo {…}` residual. Every family (incl. d/e/f and char-2) ends up **proven** or
> **cleanly cited**; there is no acceptable "seal modulo {d/e/f}" endpoint. If a family stalls, the project **reroutes /
> backtracks as far as needed to close it**, rather than banking a messy residual. (The HUNT/citation work below is about
> finding *clean* citations where they genuinely exist, never about deferring the uncitable.)
>
> **▶ TWO COST CHANGES vs. the naive plan (cost, not correctness):** (1) generalize the field via an **abstract `[Field K]
> [Fintype K]` typeclass refactor**, NOT a `GaloisField` construction — likely deletes the prime-power sweep; (2) treat
> the kernel's **Route-1 (char-sum) vs Route-3 (Witt frame-rigidity)** choice as an explicit *spiked* decision. Both hinge
> on the **scoping audits in §11.0.**
>
> **▶ THE CENTRAL REFRAME (2026-06-24) — what the kernel actually is, and why `q=3` may flatter it.** The restricted count
> is an affine-quadric count, so (A-side) it depends ONLY on `(m, χ(D), level-pattern)` — the **square-class** of the
> discriminant `D = det G`, plus a level term that is **parity-gated**: `dim` even ⟹ the count sees only `[c_lev = 0]`
> (one bit); `dim` odd ⟹ only `χ(c_lev)` (square-class of the level). **At `q=3` this is invisible** — `det G ∈ {1,2}`
> *is* its square class and `c_lev ∈ {0,1,2}` is fully resolved — so the per-sub-frame invariant looks rich. **At `q ≥ 5`
> it is genuinely coarser** (`det G ∈ {1,4}` collapse, `{2,3}` collapse; likewise the level). Consequences:
> - the open **kernel is geometric, not analytic**: "does the *coarse* profile `(m, sqclass(det G_u(S)), level-pattern_u(S))`
>   over sub-frames `S ⊆ T_Q` determine `u`, **uniformly in `q`**?" The char-sum (Route 1) and perp-graph (Route 3) only
>   **extract** this invariant; the **inversion is the shared hard part** in both routes.
> - coarser per-frame info at large `q` ⟹ **more sub-frames needed** ⟹ **the base grows with `q`** — consistent with the
>   probe `[5,5,6,7]` for `q=2..5` at `d=4` (§9.9.18c). The old "`T_Q ≈ d+2`" (constant) is **WRONG**; expect
>   `|T_Q| = O(d + log q)`, with the **separate obligation `|T_Q| = O(log n)`** (within the individualization budget;
>   the capstone's `bound` becomes a function of `q`, proven, not a constant).
> - **the `VO⁻₄(3)` instance may be misleadingly easy** precisely because `q=3` conflates `det G` with its square class
>   and fully resolves the level. The generalization's real risk is whether coarse-invariant injectivity **survives at
>   `q ≥ 5`** — and that is cheap to probe (SPIKE-K, §11.1) before any build.

### 11.0 Scoping audits — DO THESE FIRST (each ≈ an afternoon; they gate the routes AND the target statements)

- **AUDIT-S — the seam target + `SchurianScheme` status (do this FIRST; it dictates what every family must deliver).**
  Pin the Skresanov/CFSG transport — "any small-Aut non-geom schurian rank-3 scheme `≅ affineScheme (similitudeGroup Q)`
  for one of these `Q`, **up to scheme equivalence**" — precisely enough to state each family's target theorem (which `Q`,
  up to what equivalence). **AND resolve `SchurianScheme`:** is "schurian" a **scope hypothesis** (free — we only claim
  the result for schurian residues) or an **obligation** (prove the deferred-decisions-stage-1 residue *is* schurian)? If
  the latter it likely touches CFSG/Skresanov and belongs in the **citation stack**, not a "Step-group-4 discharge."
  **Deliverable:** the exact per-family target statement + a go/no-go on `SchurianScheme` = hypothesis vs citation. A
  wrong target shape wastes the whole kernel effort, so this precedes AUDIT-W (which only matters once the target is known).

  > **✅ AUDIT-S DONE (2026-06-24).** Verified against current source (two Explore passes) + route-doc §9.9.18/§9.9.18a.
  > Three findings:
  >
  > **(1) Per-family target statement — CLEAN, no transport, no schurian obligation.** Each family delivers exactly
  > **`IsotropySeparatesAtBase Q_fam T_fam`** for its bundled form `Q_fam` and a base `T_fam` of size `O(d+log q)` (the
  > `VO⁻₄(3)` template, §1). Reasons: `affineScheme (similitudeGroup Q)` is **schurian *by construction*** (built via
  > `orbitalScheme`, returns type `SchurianScheme (p^d)` — `CascadeAffine.lean:2204`; `neg_mem_similitudeGroup` discharges
  > the `-1∈G₀` side-condition), and the live capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`:3317`)
  > already takes a *concrete* `Q` and concludes the seal disjunction **for `affineScheme (similitudeGroup Q)` directly** —
  > so a family needs no scheme-iso/transport of its own. ⚠ For non-quadratic families (**(d) alternating** bilinear,
  > **(e) half-spin**, **(f) Suzuki**) the capstone/`similitudeGroup`/`IsotropySeparatesAtBase` are **quadratic-specific**
  > and must be re-instantiated per form object (parallel infra, same shape) — confirms §11.4's note.
  >
  > **(2) `SchurianScheme` = SCOPE HYPOTHESIS, FREE — neither an obligation nor a citation for this work.** It is
  > discharged *by construction* for the concrete affine schemes (above). The only residual is "does the canonizer's
  > actual 2-WL-closure residue equal the `orbitalScheme H` model?" — a **pre-existing, seal-wide scope assumption**
  > (route-doc §9.9.18a/C3; promoting a *computed* scheme to schurian is documented infeasible,
  > `general-cc-separability.md:554-558`), **orthogonal to node-4 / forms-graphs.** §11 does NOT need to prove anything
  > about `SchurianScheme`. (The §11-header "discharged in Step group 4" is superseded — nothing to discharge.)
  >
  > **(3) ★ THE REAL FINDING — the SEAM is unbuilt and is the genuine §11.6 design question.** The `wittFree` capstone is
  > a **parallel seal route** (it concludes the rigid-or-Cameron disjunction *for `affineScheme(Q)`*; it does **NOT**
  > produce `hSmallAutThin`/`BoundedMinMult`, and there is **no Lean lemma** linking `IsotropySeparatesAtBase ⟹
  > hSmallAutThin`). To turn per-family results into "the abstract residue `S` is rigid or Cameron" the seam must route
  > `S` to its concrete `affineScheme(Q)` — but **no scheme-isomorphism / `SchemeEquiv` / "the seal disjunction transports
  > along a scheme iso" exists in Lean** (only an intra-scheme `schemeEquiv` on *vertices*). So §11's "discharge
  > `hSmallAutThin`" framing is imprecise: the deliverable is the **rigid-or-Cameron conclusion for the residue via the
  > per-family parallel route + a cited classification case-split**, not a discharge of the generic `viaBoundedMinMult`
  > hypothesis. **Seam decision (for §11.6), two options:** (a) carry the Skresanov/Liebeck reduction as ONE cited
  > predicate (the route-doc's proposed `reachesRigidOrCameron_viaSchurianRank3Affine`) whose conclusion is *directly* the
  > seal disjunction for `S` — discharged on its forms-graph part by the per-family `IsotropySeparatesAtBase` (needs no new
  > infra, but the predicate carries the transport implicitly); or (b) build a minimal `SchemeEquiv` + a "seal disjunction
  > transports along `SchemeEquiv`" lemma, then the cited classification gives `∃Q, S ≅ affineScheme(Q)` and you transport
  > the per-family seal back. **Recommend (a)** — matches the existing citation-carrying style (`PrimitiveCCClassification`),
  > avoids new scheme-iso infrastructure. Either way: the per-family *math* (finding 1) is independent of this choice, so
  > the seam can be designed in parallel with the kernel — but it should be **pinned before assembly** (§11.6).
- **AUDIT-A — CascadeAffine's `ZMod p` dependence (gates the abstract-field refactor, §11.1-field).** Read `CascadeAffine.lean`
  + `GaussCount.lean` and catalogue every essential use of `ZMod p` that is NOT already abstract over `[Field K]`:
  the scheme index `Fin (p^d)`, `affineE`, the affine/similitude group, `frobPerm` (field automorphisms), and the
  `Invertible (2:ZMod p)` / `ringChar ≠ 2` assumptions. **Question to answer:** can the whole chain be restated over a
  variable `[Field K] [Fintype K] [DecidableEq K]` (with `V := Fin d → K`, scheme on `Fin (Fintype.card K ^ d)`,
  `frobPerm := FiniteField.frobenius`)? Mathlib's `quadraticChar`/`gaussSum` API is already abstract-finite-field, so the
  toolkit side is likely cheap; the scheme side is the risk. **Deliverable:** a refactor cost estimate + a go/no-go on
  abstract-`K`. If GO, the "all q prime" and "prime powers" line items MERGE into one.

  > **✅ AUDIT-A DONE (2026-06-24) — verdict GO (cost small–medium).** The toolkit (`GaussCount.lean`, the deepest math)
  > is *already* abstract over `{K} [Field K] [Fintype K] [DecidableEq K]` + `[Invertible (2:K)]`/`ringChar K ≠ 2` — **zero
  > `ZMod p`, zero work.** The forms layer (`CascadeAffine §AffineScheme/§OrthogonalForm`, Lemma A + Lemma B (now `IsotropicIncidenceCount` + `ProfileReduction`)) uses `ZMod p`
  > only as "finite field + cardinality witness": `affineE = Fintype.equivFinOfCardEq affV_card`, `similitudeGroup`/affine
  > group are pure `≃ₗ[K]`/`Kˣ` code, the count math is intrinsic to `K`. **`[Fact p.Prime]` is used ONLY to manufacture
  > `Fin (p^d)` nonemptiness (`NeZero`), and there is NO Frobenius in the forms argument** (Frobenius/`frobLinear` lives only
  > in the disjoint cyclotomic leg-B slice). Mathlib `quadraticChar`/`gaussSum`/`isometryEquivWeightedSumSquares` are already
  > finite-field-generic. **Refactor = mechanical search-replace** (`ZMod p`→`K`, `p^d`→`Fintype.card K ^ d`,
  > `ZMod.card`→`Fintype.card_fun`, nonemptiness from `Fintype.card K ≥ 2`). **Single biggest risk = the `Fin (p^d) →
  > Fin (Fintype.card K ^ d)` reindexing churn** across ~40 signatures + `affineScheme`'s return type (volume, not difficulty;
  > defeq/positivity proofs leaning on `p^d` being a numeral must be re-derived from `card K ≥ 2`). **CONSEQUENCE: prove the
  > kernel ONCE over `K`, covering prime `q=p` AND prime powers `q=p^e` in one stroke — SKIP §11.3-3's `q`-prime special case**
  > (no `GaloisField` sweep; that construction is needed only for the separate cyclotomic leg-B residue). Char-2 stays excluded
  > under either form (`[Invertible 2]` pervasive) — separate track (§11.5), not an AUDIT-A obstruction.
- **AUDIT-W — the exact Witt statement needed (gates Route 3, §11.1-kernel).** Pin down precisely which form of Witt's
  theorem the frame-rigidity argument consumes (Witt extension/transitivity for finite-field quadratic forms; the
  hyperbolic-decomposition). Check Mathlib for partial coverage (`QuadraticForm.Isometry`, `Matrix.... `, the
  `BilinForm` isometry API). **Deliverable:** a Mathlib-contribution size estimate for Witt, and a yes/no on "Route 3's
  kernel proof is uniform over `q` and reusable across the polar families." This is the number that decides Route 1 vs 3.

  > **✅ AUDIT-W DONE (2026-06-24) — statement = Witt EXTENSION; Mathlib coverage ABSENT; build LARGE; reuse single-cluster.**
  > **(A) The exact statement:** **Witt's extension/transitivity theorem** over a finite field of char ≠ 2 — *any isometry
  > between subspaces of a nondeg `(V,Q)` extends to all of `V`*, used as "`O(Q)`/`GO(Q)` acts transitively on the nonzero
  > isotropic vectors and each `Q`-value shell." This is what Route-3 frame-rigidity ("apartment determines the point") AND
  > the hard half of `OrbitIsIsotropyClass` (the clean rank-3 `{0,isotropic,anisotropic}` identification) both consume.
  > **(B) Mathlib coverage = ABSENT** (verified against the current pin): the `Witt` files are unrelated (`Order/BourbakiWitt`,
  > `RingTheory/WittVector`); `QuadraticForm/` has NO Witt extension/cancellation/decomposition, NO finite-field
  > classification (only ℂ/ℝ), NO orthogonal group of a form. Substrate present (shortens but does not close it):
  > `IsometryEquiv`, `exists_orthogonal_basis` (`Basic.lean:1293`), `isometryEquivWeightedSumSquares`/
  > `equivalent_weightedSumSquares_units_of_nondegenerate'` (`IsometryEquiv.lean:151,169`), `Anisotropic`.
  > **(C) Build = LARGE** (hyperbolic plane + extension theorem proper = the bulk; then cancellation/decomposition +
  > finite-field dim/discriminant classification + similitude-scalar fusion; char-2 bespoke regardless). **Payoff IS real:**
  > if built, a *single* geometry-agnostic lemma `IsotropySeparatesAtBase ⟸ nondeg Q + hyperbolic frame` discharges the
  > WHOLE affine-polar family (c) `VO^ε_{2m}(q)` uniform in (ε,m,q) at once, and templates (d) alternating / (e) half-spin
  > with `B` swapped — so Route-3's kernel proof is uniform over `q` AND amortizes across c/d/e. Only (f) Suzuki–Tits stays
  > bespoke. **(D) Reusability tally:** Witt is **NOT load-bearing on the current critical path** (every live seal decl is
  > Witt-free via `relationRefinesIsotropy_similitude`); its value is concentrated in ONE cluster (Route-3 extraction + the
  > c/d/e generalization + the clean unconditional rank-3 identification) — all the SAME extension theorem amortized, not
  > independent consumers. The "Witt keeps coming up" impression is *mention count* across 6 docs that mostly record
  > routing-AROUND this one absent theorem. **⟹ building Witt "as a generic resource" is weakly justified (single-cluster);
  > it is well justified ONLY if Route 3 is chosen for the c/d/e generalization.**

### 11.1 The kernel route fork — decide BEFORE building (the central decision)

The injectivity kernel — "the **coarse** profile `{(sqclass(det G_u(S)), level-pattern_u(S))}_{S⊆T_Q}` recovers `u`,
uniformly in `(ε,m,q)`" (the header reframe) — is **the one open research problem**, unbuilt in *both* routes, and the
**inversion is the same geometric statement either way**. The routes differ only in the **extraction layer** (how the
coarse invariant is read off) and in how they **scale across families**. (The `wittFree` capstone removed Witt from the
*bridge* via `relationRefinesIsotropy_similitude`, but NOT from the kernel; Route 3 brings Witt back for the *extraction*.)

- **Route 1 — char-sum extraction (where the code is).** Extraction (counts → `(χ(D), c)`) is **already built**
  (GaussCount + A-side; instance proven). Per-`q` analytic. Open = the shared inversion. **Cost ≈ the inversion alone**
  (extraction free), but **per-family** (≈ linear in #families).
- **Route 3 — Witt + perp-graph frame-rigidity (archive §10.4).** Extraction needs the **one-time Witt build** (AUDIT-W, large).
  But `IsotropySeparatesAtBase Q T` is **geometry-agnostic for quadratic forms**, so a *single* "nondeg `Q` + hyperbolic
  frame ⟹ separates" lemma discharges the **entire orthogonal family (a/c, all ε,m,q) at once** and templates d/e. **Cost
  ≈ Witt + the shared inversion, then near-free per family** (amortizes).
- **Coupling to scope (matters, given the FULL endpoint).** Because the endpoint requires **all** classical families
  (c,d,e are in scope — not deferrable), Route 3's fixed Witt cost **amortizes across them**, strengthening its case
  beyond the naive "Route 1 because the code exists." Route 1's head start (extraction done) still counts; (f) Suzuki–Tits
  and char-2 need bespoke work under either route. So the fork is a genuine decision — settle it on SPIKE-K + AUDIT-W, not
  on which code already exists.

- **★ SPIKE-K (after the audits, before committing) — now a cheap, char-sum-FREE probe of the real risk.** Two parts:
  1. **Coarse-invariant injectivity (the de-risk that matters).** Pure `F_q` linear algebra, NO Gauss machinery: compute
     `(m, sqclass(det G_u(S)), level-pattern_u(S))` profiles over sub-frames for several `(ε,m,q)` **with `q ≥ 5`
     emphasized**, and measure (i) **does injectivity survive** the coarse invariant at large `q`? (ii) **how does the
     minimal base size scale** — is it `O(d + log q)`, and within `O(log n)`? This is the genuine open question, and it
     is cheap (the `VO⁻₄(3)` success may be a `q=3` artifact, header reframe).
  2. **Route comparison (paper).** Sketch BOTH extractions far enough to compare: does the char-sum inversion have a
     *uniform-in-q* closed form or fragment per residue class of `q`? **Does Witt/frame-rigidity make the *inversion*
     dramatically cleaner** — a clean "apartment determines the point" argument closing the non-isotropic shell with no
     extra counting round — not merely "uniform in `q`" (it is, by construction) but genuinely *easier*?
  - **Decision rule.** Default-lean **Route 1** (extraction free) UNLESS (a) Witt collapses the inversion to a clean
    geometric argument, OR (b) AUDIT-W is cheap enough that amortization across c/d/e wins, OR (c) the char-sum inversion
    fragments in `q` / AUDIT-A is NO-GO. Record the decision here.

  > **✅ SPIKE-K PART 1 DONE (2026-06-24) — the existential de-risk PASSES; the kernel is viable at `q≥5`.**
  > `A2MonovariantProbe.Probe_CoarseInvariantInjectivity` (C#, green, ~13min/8-restart): greedy individualisation of
  > `VO^ε_4(q)` under the **exact `VO⁻₄(3)`-`decide` invariant** `cnt(u;t₁,t₂)=#{y≠0:Q(y)=0,Q(y−(t₁−u))=0,Q(y−(t₂−u))=0}`
  > (char-sum-FREE brute-force counts; by the Gauss identity the count only ever sees `χ(det G)`, so the measured base
  > faithfully reflects the **coarse-invariant** separating power), min base over 8 random restarts (greedy ⟹ upper bound):
  >
  > | `q` | minus base | plus base | √n | log₂n | d+log₂q |
  > |---|---|---|---|---|---|
  > | 3 | 5 | 5 | 9 | 6.3 | 5.6 |
  > | 5 | 7 | 7 | 25 | 9.3 | 6.3 |
  > | 7 | 8 | 7 | 49 | 11.2 | 6.8 |
  > | 9 | 9 | 8 | 81 | 12.7 | 7.2 |
  >
  > **(i) Injectivity SURVIVES at every odd `q≥5`, both ε** — the coarsening does NOT kill it (the header-reframe risk is
  > refuted). **(ii) Base scales `O(d+log q)`** — min base `5,7,8,9` tracks `d+log₂q` to the integer; the old "`≈d+2`"
  > (constant) is refuted (it grows, but only logarithmically). **(iii) Base ≪ √n with widening margin, and `≤ log₂n` at
  > every `q≥5`** ⟹ the `|T_Q|=O(log n)` obligation (§11.7) is empirically met. `q=9` = the odd prime-power point (GF(9)),
  > behaves like the primes. Greedy is noisy (worst-restart spread `[7..24]`/`[8..31]` at minus `q=5,7`); the **min** is the
  > trustworthy upper bound. **Consequence for the fork:** the inversion is **geometric/uniform** (base law uniform in `q`,
  > both types) ⟹ supports the **Route-1 default** (no evidence the char-sum fragments in `q`); the part-2 paper comparison
  > + AUDIT-W still decide whether Witt makes the *inversion proof* dramatically cleaner. **NOT yet done in part 1:** the
  > mechanism confirmation `count = f(sqclass det G, level-pattern)` (the A-side identity is *proved* for the instance via
  > `configGaussSum_eq_det`, so this is corroboration not a gap) + the explicit char-2 / `d=6` extension — feeds the GATE.

  > **✅ SPIKE-K PART 2 DONE (2026-06-24) — ROUTE 1 CHOSEN (pending the GATE).** Both branches confirmed VIABLE; the
  > decision is Route 1. **Empirical core** (`A2MonovariantProbe.Probe_IncidenceVsCounts`, green): greedy base under
  > rank-3 RELATIONS-only (direct adjacency — the Route-B "perp-graph/frame-rigidity, no counting" picture) vs the full
  > COUNT profile:
  >
  > | family | n | rel-only | full counts |
  > |---|---|---|---|
  > | VO⁻₄(3) | 81 | 13 | 5 |
  > | VO⁺₄(3) | 81 | 9 | 5 |
  > | VO⁻₄(5) | 625 | 33 | 7 |
  > | VO⁺₄(5) | 625 | 23 | 6 |
  > | VO⁻₄(7) | 2401 | **fails (>cap ~36)** | 8 |
  > | VO⁺₄(7) | 2401 | **fails (>cap)** | 7 |
  >
  > **The counts (the inversion) are ESSENTIAL and are the efficient workhorse** — with them the base is tiny+uniform;
  > without them it explodes and fails by `q=7`. So Route B's distinctive promise (the inversion is *avoidable/dramatically
  > cleaner* via incidence) does NOT cash out into a small base. **Route-1 inversion is uniform in `q`** (independent confirm):
  > for even `d` the char-sum closed form has `χ(s)^d=1` and `g^d=(χ(−1)q)^{d/2}` — only a GLOBAL `q mod 4` sign, no
  > *structural* fragmentation of the recovery; and SPIKE-K.1 already spanned both residue classes (`q=3,7≡3`; `q=5,9≡1`)
  > with one base law. **Decision rationale:** (1) Route-1 extraction is BUILT and the inversion is cheap+uniform (SPIKE-K.1/.2);
  > (2) AUDIT-A GO makes Route 1 uniform over `q` anyway, neutralising Route 3's headline edge; (3) Witt is LARGE (AUDIT-W) and
  > its only saving — a count-free isotropic skeleton — targets an inversion Route 1 already does cheaply (poor value); (4) the
  > Route-1 inversion *technique* transfers to (d)/(e) with `B` swapped (archive §3: "same skeleton, `B` symplectic/spinor"),
  > so cross-family amortisation is NOT exclusive to Witt. **Witt stays the documented FALLBACK** iff (a) the non-isotropic-shell
  > inversion proves nastier than SPIKE suggests, OR (b) (d)/(e) fail to transfer cleanly from (c) (then Witt's single-lemma
  > packaging regains value). **Route-1 milestones = §11.3** (now the active path); Route-3 milestones = archive §4 (fallback).
  > **NEXT = the §11.2 GATE:** promote the inversion (§11.3-2 / M2) to a convincing uniform proof sketch — the real research.

### 11.2 Risk-gate — prove the math before the engineering

The count-assembly bridge, form-bundling, and field generalization are all **low-risk engineering that only pays off if
the uniform kernel has a proof.** So the ordering is risk-gated, not merely dependency-ordered:

1. **GATE (research):** a paper-level, probe-validated argument for the chosen kernel route (SPIKE-K outcome promoted to a
   convincing uniform proof sketch). **Nothing heavy is built until this gate passes.**
2. Then the engineering lifts (bridge, bundling, field) and the per-family sweep.

> **✅ GATE — PASS / GO-with-isolated-crux (2026-06-24).** The uniform inversion now has a coherent, probe-validated proof
> sketch end-to-end; the single open piece is sharply isolated, with its tool landscape mapped. **The target** (`§11.3-2`):
> the count profile over a bounded base `T` recovers `u`, uniform in `(ε,m,q)`.
>
> **The proof sketch (3 reductions + 1 crux):**
> - **(R1) count = coarse invariant [A-side, LANDED].** `levelset_count_eq` + `configGaussSum_eq_det` give
>   `cnt(u,S) = F(|S|, χ(det G_u(S)), c)`, and for **even `d`** (all our families) the level collapses to the single bit
>   `[c=0]` (`∑_{s≠0}ψ(−sc)=q·[c=0]−1`, `χ(s)^d=1`). So a profile-agreement antecedent ⟹ agreement of the
>   square-class+bit data `{(χ(det G_u(S)), [c_u(S)=0])}_S`. `G_u(S)` = Gram of the differences `{t−u : t∈S}`.
> - **(R2) reduce `u` to coordinates [nondeg].** With `β_t := B(t,u)` (linear in `u`) and `γ := Q(u)`, every datum is a
>   square-class of a low-degree polynomial in `(β_t, γ)`: singletons give `χ(Q(t−u))`, pairs give
>   `χ(4Q(w_i)Q(w_j)−B(w_i,w_j)²)` with `w=t−u`. A spanning set of recovered `{β_t}` determines `u` by nondegeneracy.
> - **(R3) the nondeg back-half [LANDED `coords_determine` flavour].** `{β_t over a spanning frame} ↔ u`. NB the *frame*
>   version (`d+1`, `coords_determine`) is FALSE for minus-type because square-classes ≠ field values — which is exactly
>   the gap (R4) closes; the real target is the larger-base `IsotropySeparatesAtBase`.
> - **(★ CRUX, the open math, now ISOLATED):** the square-class+bit profile over `{frame {0,eᵢ}} ∪ {O(log q) probes}`
>   **jointly** recovers `(β_t, γ)` hence `u`, uniformly in `q`.
>
> **Probe validation** (`A2MonovariantProbe.Probe_FrameThenProbes`, green): the `d+1` frame separates *most* points but is
> **not discrete** (frame colours `79/81`, `488/625`, `318/625`, `1340/2401`, `444/2401` — esp. minus) — the field-value
> ambiguity is **real and located**, confirming R3's frame-version failure precisely. **`O(log q)` extra points close it**
> (min-extra `1,3,2,3` for `q=3,5,7`, tracking `log₂q`), uniform across both ε. Combined with SPIKE-K.1 (base `O(d+log q)`,
> survives `q≥5`) + SPIKE-K.2 (counts essential), the mechanism is empirically robust end-to-end.
>
> **Crux tooling + the ONE residual risk.** The recovery is **JOINT, not per-coordinate** (SPIKE-K finding C): the clean
> "detect the roots of `Q(u−(t+c·e))` along a line" shortcut is *refuted* (it would need ~`q` probe points to catch the
> roots, not `log q`), so the genuine content is **injectivity of the `χ`-profile of low-degree polynomials in `(β,γ)`
> from `O(log q)` joint constraints**. Tool: the **exact quadratic-character / Gauss-sum identities already wielded in
> `GaussCount.lean`** are the favourable case; **general Weil bounds (absent in Mathlib)** are the unfavourable case and
> the residual risk. **GATE verdict: GO** — the kernel is TRUE (probes), the reduction is mostly LANDED, the crux is
> sharply scoped with a present-tooling path. Build the crux recovery lemma **first** (it gates everything); if it needs
> general Weil, that is a contained sub-build, else fall back to Route 3 (Witt).
>
> **▶ GATE REFINEMENT (2026-06-24, lemma audit) — TWO packagings of the crux, ONE shared core; the scaffold + tools are
> already built.** (1) **`coords_determine` is NOT dead** (corrects the narration): it is the live nondeg finish of
> **route (b)** — `isotropySeparates_of_qProfileSeparates` (FormsGraphConcrete:174, PROVEN general) reduces the crux to
> **`QProfileSeparatesAtBase`** (recover the field-valued `Q`-profile from isotropy counts at an arbitrary base), then
> `coords_determine` finishes. So the back-half splits two ways: route (a) `count=F(Gram)` [Lemma-A landed] + profile
> injectivity; route (b) `QProfileSeparatesAtBase` [crux] + `coords_determine` [landed]. (2) **Both meet at the SAME hard
> core** — shell-blindness (FormsGraphConcrete:145: `isoClass` can't tell `Q=square` from `Q=nonsquare` pairwise; the
> pointwise Fourier hinge stops; the **joint `Z(S)` over sub-frames** is what's needed). (3) **The core's attack tools are
> built:** `count_pi_setValued` (GaussCount:541, value-SET→value-POINT counts — the lever turning shell-blind isotropy
> counts into field-valued `Q`-counts) → `multiCharSum_eq_sum_count` (:568, Fourier hinge) → `sum_addChar_multiQuad_zero`
> (:511, the `R=0`/symmetry-broken-base Gauss sum the probe used). The joint sub-frame structure is what defeats
> shell-blindness — still the open content. (4) **δ′/forced-triangle is confirmed inapplicable** (rank-3 ⟹ no rainbow
> triangles / no `c=1` forced triangles; route-doc §9.9.9a) — the Gauss-count route is genuinely necessary.
> **Next = discharge `QProfileSeparatesAtBase` uniformly** (route (b): the cleanest crux statement — concrete field-value
> recovery + landed `coords_determine` finish + the in-build general scaffold; first attack = the three-tool chain above).
> Caveat: route (b)'s crux was never closed in Lean even at VO⁻₄(3) (probe-only `/tmp/m3probe.py`), so it is a
> scaffold-with-open-crux, not a closed instance being lifted — weigh against route (a)'s landed Lemma-A front-half.

### 11.3 Step group 1 — affine-polar `VO^ε_{2m}(q)` (the direct extension; our work lives here)

Dependency-ordered, with the modifications folded in:

1. **Count-assembly bridge (A-side, mostly built — §1 Lemma A / archive §10.12).** Substitute `levelset_count_eq` + `configGaussSum_eq_det` +
   the global Gauss sum into one closed form `count = F(D, c)`. Pure assembly of landed axiom-clean pieces. Low risk.
   **NOTE (don't skip) — the `R' → ℤ` descent:** the closed form lives in a ring `R'` that must be **characteristic 0
   with a primitive `p`-th root of unity** (`ℤ[ζ_p]` or `ℂ`, so `ℕ ↪ R'`); recovering the actual **ℕ** count is then "the
   char-sum value is a rational integer + `Nat.cast` injective, then divide by `q^{m+1}` in `ℕ`" — a real (small) step.
2. **★ The uniform injectivity kernel — THE OPEN MATH (Route per §11.1).** The coarse-invariant inversion of the header
   reframe (NOT a per-`Q` analytic fact): `{(sqclass(det G_u(S)), level-pattern_u(S))}_S` recovers `u`, uniformly in `q`.
   High risk; the real research. Every other family shares its spirit, so cracking it here is highest-leverage. Gated by §11.2.
3. **`q` prime all `(ε,m)` — SKIP (AUDIT-A = GO, 2026-06-24).** Prove over abstract `K` directly (step 4); this special
   case is subsumed. [Original conditional, now resolved:] If AUDIT-A is GO and SPIKE-K shows the inversion is
   geometric/uniform (the expected case, header reframe), prove the kernel **once over abstract `[Field K]`** and **SKIP**
   this `ZMod p` special case — else you prove it twice. Keep "`q`-prime first" ONLY as a fallback if SPIKE-K shows the
   proof *technique* needs concreteness, or AUDIT-A is NO-GO. ⚠ Either way this is the open kernel, NOT a `decide`
   extension (`q` unbounded ⇒ decide dies).
4. **Field generalization — via abstract `[Field K] [Fintype K]` (per AUDIT-A), NOT `GaloisField`.** A typeclass refactor
   of CascadeAffine + the Gauss toolkit, covering prime AND prime-power in one stroke. Falls back to a `GaloisField`
   prime-power sweep ONLY if AUDIT-A is NO-GO. Medium (refactor) / Big (fallback).
5. **Uniform symmetry-broken base `T_Q` — `O(d + log q)`, NOT `≈ d+2`** (header reframe: coarser info at large `q` ⟹ more
   sub-frames; probe `[5,5,6,7]` for `q=2..5`). Construct via `exists_greedy_base_le_log`, and **discharge the obligation
   `|T_Q| = O(log n)`** so the capstone's `bound` (now a function of `q`) stays within the individualization budget.
   Low–medium (the `O(log n)` bound is a real sub-proof, not free).
6. **Bundle the `VO^ε` forms uniformly** (both signs, general `2m`) as `QuadraticForm`s + nondegeneracy. Generalizes our
   `Bil`/`Qbun`. Low–medium.
- **Per-family smoke-test (tooling):** for each new concrete instance the proven `decide` pattern (ScratchBM3Bridge/Glue)
  is a cheap correctness check + interim instance-seal that unblocks Step-group-4 wiring while the uniform kernel is in
  progress. Keep it as a regression/CI device, not the proof.

### 11.4 Step group 2 — the other schurian families (reuse the skeleton / Witt template)

- **(d) alternating forms** — same Lemma A/B (or Route-3) skeleton with a symplectic/alternating bilinear `B`; its own
  `IsotropySeparatesAtBase`. ⚠ NOTE: the form object is an *alternating bilinear* form, not a quadratic form, so the
  geometry-agnostic orthogonal lemma (§11.1) does NOT cover it directly — it needs its own predicate instance, but rides
  on the same kernel *technique*. Medium.
- **(e) half-spin** — spinor geometry, different incidence. Medium–high. **(Less special than (f): char-agnostic, form-adjacent
  incidence — expect a Handle-1/form-count transfer closer to affine-polar/alternating. Spike pending.)**
- **(f) Suzuki–Tits** — the exceptional outlier; the `Sz(q)` geometry is genuinely special (small-Aut, but neither odd-char nor a form).

> **▶▶▶ SUZUKI–TITS (f) TRANSFER SPIKE DONE (2026-06-26) — verdict: reachable, NOT a wall, but the most bespoke analytic engine;
> FOLD INTO the char-2 track. The odd-char technique does NOT transfer, and the failure clues a direct-geometric alternate.**
>
> **Structural facts (grounded: probe `SuzukiTits`, route-doc §9.9.18c).** `VSz(q)` is the Cayley graph on `GF(q)^4` with
> connection set the cone over the Suzuki–Tits ovoid `O = {(1,a,b, ab + a^{σ+2} + b^σ)} ∪ {(0,0,0,1)}`, `q = 2^{2e+1}`, `σ` the
> **Tits endomorphism** (`σ² = Frobenius`; `q=8 ⟹ σ(x)=x⁴`). It is small-Aut (`|Aut| ~ q⁴ = n^{1+o(1)}`, `Sz(q) ⊂ Aut`),
> **cospectral with `VO⁻₄(q)`** (same params `(4096,455,6,56)`, distinguished ONLY by `Sz(q)`), and the probe **shatters it at
> base 9 ≪ √4096** (bounded-WL-dim confirmed).
>
> **Why the affine-polar technique does NOT transfer — two independent reasons, both clueing the alternate:**
> 1. **Char-2, necessarily.** `Sz(q) = ²B₂(q)` exists ONLY for `q = 2^{2e+1}`. So Suzuki inherits the *entire* char-2 situation
>    (§11.5): no `χ` (every element of `F_{2^k}^×` is a square), no Gauss sums, no `det`-via-polar — the whole odd-char A-side
>    (`χ(det G₂)`, `K = χ(disc)·gaussSum^{d+2}`, `c0_le_threequarters`, the bridge B1a/B1b) has **no char-2 analog through `χ`**.
> 2. **Non-form.** `VSz(q)` is defined by the σ-twisted **ovoid polynomial** `c + ab + a^{σ+2} + b^σ`, not a quadratic/bilinear
>    form — so even the char-2 *orthogonal* substrate (Arf, char-2 quadric count) does **not** directly apply. And cospectrality
>    with `VO⁻₄(q)` means **no shortcut via spectrum/parameters** — the separating invariant MUST see the σ-twist.
>
> **The alternate technique (what the failure clues — there is no form, so use the explicit ovoid coordinates):**
> - **★ Handle 1 (OPTIMISTIC — direct geometric individualization, no exponential sums).** The Tits coordinatization makes a
>   vertex's `(a,b)` explicit (`c` determined by the ovoid equation). Individualize `O(1)` reference vertices, read off the
>   σ-twisted incidences ⟹ pin `(a,b,c)` purely combinatorially. Char-2-substrate-light, **no `χ`/Gauss/Weil**; consistent with
>   the base-9 probe. **Try this FIRST.**
> - **Handle 2 (FALLBACK — σ-twisted count).** Run the Layer-A skeleton with the σ-twisted ovoid form replacing `Q`, in char-2
>   additive-trace. ⚠ **RISK:** the σ-twist (`a^{σ+2}`, `σ²=Frob`) yields σ-twisted exponential sums (Kloosterman/Sato–Tate
>   territory) that may need **Weil/Deligne** — exactly the deep bounds the affine-polar route worked to avoid. Suzuki's count
>   route is the **highest analytic risk of any family**; Handle 1 exists precisely to dodge it.
>
> **Strategic placement — Suzuki is NOT a 5th independent family; fold it into the char-2 track.** Both are char-2; both reuse
> the **char-agnostic combinatorial layer** (matching `Matching`, `ZProfileSeparates`/`FieldGeneric`, the seam
> `ScratchSeam`, Layer B) which touches no `χ`; both need the non-`χ` additive-trace substrate (which char-2 already builds).
> Suzuki is the most bespoke *analytic* engine but it is a **single family with fully explicit coordinates**. Sequence: after the
> char-2 orthogonal substrate exists, Suzuki either **extends** it (Handle 2) or **sidesteps** it (Handle 1, geometric).
>
> **Net feasibility:** reachable, not a wall — single family, explicit Tits coordinates, empirical base-9 shatter, reusable
> combinatorial layer. Risks: the shared char-2 Mathlib substrate gap (§11.5), the σ-twisted semilinear structure (no Mathlib
> support — the Tits endomorphism is exotic), and the Handle-2 Weil risk (mitigated by Handle 1). **The handle IS findable; the
> open question is which of the two, settled by attempting Handle 1's geometric recovery on the explicit coordinatization.**
- **★ CITATION-HUNT FIRST (before any bespoke (e)/(f) proof):** the core orthogonal/affine-polar family is **uncitable**
  (forms-graph bounded-WL-dim is OPEN both ways in the literature — `reference_srg_wl_literature_2026-06-17`), which is
  what makes proving it a contribution. But (e)/(f) are exceptional and MAY have a handle in the rank-3 / 2-transitive /
  Skresanov literature. Confirm open-vs-citable for each BEFORE committing to a bespoke argument; cite ONLY where a clean
  citation genuinely exists. **Per the endpoint discipline (§11 header): if a family is uncitable it is IN SCOPE to prove
  (reroute/backtrack), never banked as a `modulo {…}` residual.** Under Route 3, (d)/(e) (classical forms) amortize on
  the one-time Witt build; (f) Suzuki–Tits is bespoke regardless.

### 11.5 Step group 3 — char-2

- **Forms over `𝔽_{2^k}`** — quadratic vs. bilinear diverge; the polar form is alternating/degenerate, breaking the entire
  A-side (`Invertible 2`, `ringChar ≠ 2` are pervasive). A distinct Gauss/incidence argument. **Lowest priority,** and
  **cite ONLY if the classification's char-2 cases are genuinely covered by an existing theorem (a clean citation);
  otherwise it is in scope to prove** — per the endpoint discipline it is NOT a messy deferral. Distinct track regardless.

> **▶ WHY char-2 IS A REQUIRED BRANCH, NOT OPTIONAL (the "odd-`q` only" question, 2026-06-26).** The entire pair route
> (and the `wittFree`/Lemma-A machinery, and `c0_le_threequarters`/B1a/B1b) carries `ringChar ≠ 2` / `Invertible 2` — it is
> **odd-`q` only**. But the affine rank-3 forms-graph families `VO^ε_{2m}(q)` exist over **every** `q`, including `q = 2^k`,
> and Liebeck's affine-rank-3 classification places the **even-`q` orthogonal instances squarely in the same node-4
> small-Aut non-geometric schurian residue** as the odd-`q` ones (they are genuine, distinct residue graphs — the char-2
> quadratic form carries the Arf/quadratic-refinement data its alternating polar does *not*, so they do **not** collapse
> into the geometric bilinear-forms leg). **So every graph DOES hit a branch — but the char-2 forms-graphs hit a branch
> that is currently NEITHER built NOR cited.** This is the honest status: it is a **tracked, in-scope obligation** (endpoint
> discipline, §11 header: "every family incl. char-2 ends up proven or cleanly cited", §11.8 net ordering
> "char-2 cite-if-covered-else-prove") — NOT a silent hole in the seal's logic (the residue is carried, the branch is named)
> — but it IS genuine remaining work: the seal is **not complete** until the char-2 forms-graph branch is filled. The "odd-`q`
> only" limit of the pair route is therefore correct and expected, with char-2 a parallel obligation, not a non-issue.
> **Recommended next for that branch:** a citation-hunt (Liebeck classification + any char-2 forms-graph WL-dim/base results)
> — cite if a clean one exists, else prove via the bespoke char-2 Gauss/incidence argument (the polar is alternating, so the
> A-side reduction must be redone; `card_quadForm_eq`-style counts over `𝔽_{2^k}` with the Dickson/Arf invariant replacing
> `χ(disc)`). The 1-dim cyclotomic slice over even `q` is separately covered by the Ponomarenko citation (§11.6), so the
> char-2 GAP is specifically the forms-graphs (c)–(f), not the cyclotomic part.


> **▶▶▶ CHAR-2 CITABILITY / FEASIBILITY CHECK DONE (2026-06-26) — verdict: NOT citable, NOT a wall, but a SUBSTANTIAL
> bespoke build + missing Mathlib substrate.** Mirrors the AUDIT-W format.
>
> **(A) Citability = NO (must be proved).** A literature sweep (Gavrilyuk/Ponomarenko WL-dim line + polar-space SRG line)
> finds **no published bounded-WL-dim / poly-individualization result for the orthogonal forms-graph `VO^ε_{2m}(q)`
> families**, char-2 or otherwise. The closest WL-dim results are for *adjacent-but-different* families — Cai–Guo–Gavrilyuk–
> Ponomarenko (Combinatorica 2025, `arXiv:2312.00460`) prove WL-dim ≤ 4 for the **Fon-Der-Flaass** construction (a different
> SRG family) — and the polar-space papers (`arXiv:2402.05055`, `arXiv:1606.05898`) are about *constructing/switching* polar
> SRGs, not their WL-dimension. So char-2 bounded-WL-dim is **open, same status as odd char** (the SRG-WL wall is char-agnostic).
> The *structure* (Liebeck/Skresanov) covers char-2; only the WL-dim **result** is uncited. **No free pass via geometry:** the
> char-2 *quadratic* forms-graph does NOT collapse into the carved geometric *bilinear/symplectic* leg — the quadratic form
> strictly refines its alternating polar (the Arf datum), giving a distinct non-geometric rank-3 SRG. **Positive signal:** the
> SAME authors as our cited stack (Gavrilyuk, Ponomarenko) are *actively* proving bounded-WL-dim for structured SRG families,
> so the technique class is alive and a future/ongoing watch could yield coverage.
>
> **(B) What breaks in char 2 (the entire odd-char A-side evaporates).** (1) `Invertible 2` fails ⟹ `Q` is **not** recoverable
> from its polar; (2) the polar form is **alternating/symplectic** and degenerate-relative-to-`Q` ⟹ `det G` (polar-Gram det) is
> a Pfaffian², **blind to the type** — the wrong invariant; (3) **there is no quadratic character `χ`** — `F_{2^k}^×` has odd
> order `2^k−1`, every element is a square (squaring = Frobenius, a bijection) ⟹ the whole `χ(det G₂)` observable, `K =
> χ(disc)·gaussSum^{d+2}`, `c0_le_threequarters`, B1a/B1b, the bridge **have no char-2 analog through `χ`**; (4) the `gaussSum²=
> χ(−1)q` identity is odd-char.
>
> **(C) What replaces it (classical, complete, but UNBUILT).** The **Arf invariant** (`∈ F_2`, the ± type) replaces `χ(disc)`;
> the count of `{Q=c}` over `F_{2^k}` is the classical char-2 quadric point-count (`q^{d-1} ± q^{d/2-1}`, governed by Arf),
> computed via the **additive (trace) character** and an Arf-weighted exponential sum. The config invariant becomes the **Arf of
> the restricted/pair form**, not a Gram determinant. None of this is open math — char-2 quadrics are fully understood.
>
> **(D) Mathlib coverage = essentially NIL.** No **Arf invariant**, no **Dickson invariant** (only Dickson *polynomials* /
> Dickson's lemma), no `CharTwo` development in `LinearAlgebra/QuadraticForm/`, no char-2 quadric point-count. `quadraticChar`/
> `gaussSum` are odd-char by construction. So char-2 needs the missing substrate built from near-zero.
>
> **(E) Net — reachable, parallel-to-affine-polar + substrate, MODERATE-to-LARGE.** The **combinatorial layer transfers
> char-agnostically** (the matching trick `exists_separating_base`, the `ZProfileSeparates` reduction `FieldGeneric`, the seam
> `ScratchSeam`, Layer B — all pure finite combinatorics / scheme structure, no `χ`). The **analytic kernel must be rebuilt**:
> a char-2 `IsotropySeparatesAtBase` proved with Arf + additive-trace counts replacing `χ`/Gauss, on top of a from-scratch
> Mathlib char-2 quadratic-form substrate (Arf invariant + quadric count). So char-2 ≈ **a second copy of Layer A in char-2
> language + a substrate build** — not a wall (the result is empirically plausible: the early `Probe_FormsGraphs` included
> `q=2` and it shattered at a small base), but real volume. The proof *skeleton* (count profile separates at a bounded base) is
> the SAME; only the count engine changes (`χ`/Gauss → Arf/additive-trace). **Recommended:** treat it as its own track, started
> by building the Mathlib char-2 substrate (Arf invariant of a quadratic form over `F_{2^k}` + the quadric point-count), which
> is reusable and the genuine prerequisite; defer until odd-char affine-polar + the seam are closed (it shares no analytic code
> with them, only the combinatorial layer).

### 11.6 Step group 4 — structural wiring (citations + glue) — DESIGN THE SEAM EARLY

This is the **load-bearing** step — it produces the rigid-or-Cameron conclusion for the schurian residue (NOT, per
AUDIT-S finding 3, a "discharge of `hSmallAutThin`": the per-family `wittFree` route is a *parallel* seal route, and the
seam is a cited classification case-split that routes the abstract residue `S` to its concrete `affineScheme(Q)`). Target
pinned by **AUDIT-S (§11.0)**; this step executes it.

> **▶▶▶ SEAM SPIKE DONE (2026-06-26, `ChainDescent/ScratchSeam.lean`, axiom-clean) — the seam CLOSES architecturally; it
> reduces to ONE new obligation, and option (b) is the clean route (correcting the earlier option-(a) lean).** The stub
> **`reachesRigidOrCameron_viaSchurianRank3Affine`** compiles axiom-clean: from (C) the cited classification
> (`IsCameronScheme S ∨ ∃ Q T f, T.card ≤ bound ∧ IsotropySeparatesAtBase Q T ∧ SchemeRealizes f S (affineScheme Q)`) and
> (T) a transport hypothesis, it concludes `SealDisj S` — the forms-graph case discharged by the landed
> `reachesRigidOrCameron_viaIsotropySeparates_wittFree`, transported back to `S`. **So the seam closes modulo exactly ONE
> new piece: `htransport` — the seal disjunction is invariant along a realizing permutation `f`
> (`SchemeRealizes f S X := ∀ v w, (schemeAdj S).adj v w = (schemeAdj X).adj (f v) (f w)`).**
>
> **`htransport` is mechanical, not a wall — and it should be PROVED (option b), not hidden in the citation (option a).**
> The earlier AUDIT-S lean toward option (a) ("carry the transport *inside* the citation") is **dispreferred**: it would make
> `hclass` assert a non-trivial transport as an axiom, breaking the faithful-citation bar — and it is unnecessary, because the
> transport substrate is **already landed**. All four disjuncts are defined purely via `schemeAdj` + `IsAut`/`IsBase`
> (`isAut_schemeAdj_iff` = adjacency-auts ARE scheme-auts), and the recovery side — the riskiest disjunct
> `SchemeRecoveredByDepth` — sits on **`forcedNode_relabel`** (`Cascade.lean:3020`, "the forced node is equivariant under
> *arbitrary* relabelling — full iso-invariance") + `movedSet_relabel` + the residual-support equivariance lemmas, which
> already prove the recovery machinery commutes with an arbitrary `relabelAdj σ`. So `htransport` assembles from landed
> equivariance atoms (forced-node/moved-set relabelling + `IsAut`/`IsBase` conjugation); `IsCameronScheme` (a free predicate)
> only has to be *instantiated* iso-invariantly (a design constraint, trivially met). **Residual risk = assembly friction
> (connecting `SchemeRealizes`'s `schemeAdj` form to `relabelAdj`, and threading conjugation through the 4 disjuncts), NOT a
> wall.** Verdict: build `htransport` as a real lemma (option b); `AlgIso.InducedBy f` already provides the "iso realized by
> `f`" primitive. The seam is no longer the under-scoped unknown AUDIT-S flagged — it is bounded, landed-atom-backed glue.

- **Cite Ponomarenko** for (a) the 1-dim cyclotomic slice (→ `reachesRigidOrCameron_affineSlice`). (citation)
- **The seam vehicle — `reachesRigidOrCameron_viaSchurianRank3Affine` (stub LANDED, see the spike box above).** A single
  carried *classification* predicate (Skresanov/Liebeck/Cameron) routing `S` to `Cameron ∨ (≅ a forms-graph `affineScheme(Q)`
  with `IsotropySeparatesAtBase Q T`)`, **+ a separately-PROVED transport lemma `htransport`** (option b). The forms-graph
  obligation is discharged per-family by `IsotropySeparatesAtBase` + `…viaIsotropySeparates_wittFree`; the transport is the
  one new build, backed by the landed `forcedNode_relabel`/`movedSet_relabel`/`IsAut`-conjugation equivariance. (Option (a) —
  transport hidden inside the citation — is rejected as unfaithful; see the spike box.)
- **`SchurianScheme` — RESOLVED FREE (AUDIT-S finding 2):** `affineScheme(similitudeGroup Q)` is schurian by construction;
  the canonizer-residue-is-schurian question is a pre-existing seal-wide scope assumption, orthogonal to this work.
  **Nothing to discharge here.**
- **Assemble:** per-family results + the cited classification ⟹ the **full** rigid-or-Cameron seal for every small-Aut
  non-geom schurian rank-3 residue, modulo `{G3 + cited}` (no `modulo {family}` residual — endpoint discipline, §11 header).

### 11.7 Consolidated probe / confirmation checklist (gates, in order)

| # | Probe / confirm | Gates | Risk if skipped |
|---|---|---|---|
| AUDIT-S ✅ | DONE 2026-06-24 (§11.0): per-family target = `IsotropySeparatesAtBase Q_fam T_fam` (no transport); `SchurianScheme` free; seam = cited `…viaSchurianRank3Affine` (finding 3) | every family's target (§11.6) + AUDIT-W | — (done) |
| AUDIT-A ✅ | DONE 2026-06-24 (§11.0): GO — toolkit already abstract; forms layer mechanical `ZMod p`→`K`; merges prime+prime-power, SKIP §11.3-3; risk = `Fin(p^d)` reindex churn | field-gen vehicle (§11.3-4) | — (done; GO) |
| AUDIT-W ✅ | DONE 2026-06-24 (§11.0): Witt EXTENSION; Mathlib ABSENT; build LARGE; reuse single-cluster (c/d/e + rank-3 id); not on critical path | Route 1 vs 3 (§11.1) | — (done; fork leans Route 1 pending SPIKE-K.2) |
| SPIKE-K.1 ✅ | DONE 2026-06-24 (§11.1): injectivity SURVIVES at odd `q∈{3,5,7,9}` both ε; base `5,7,8,9` ≪ √n; kernel viable | kernel route + the §11.2 gate | — (done) |
| SPIKE-K.2 ✅ | DONE 2026-06-24 (§11.1): counts ESSENTIAL (rel-only base 13/33/fails vs full 5/7/8); inversion uniform in `q` ⟹ **ROUTE 1 CHOSEN** (Witt fallback) | Route 1 vs 3 (§11.1) | — (done; Route 1) |
| base-O(log n) ✅ | DONE 2026-06-24 (SPIKE-K.1): `\|T_Q\|` tracks `d+log₂q` to the integer, `≤ log₂n` at every `q≥5` (the false `≈d+2` refuted) | §11.3-5 + capstone `bound` | — (within budget, confirmed) |
| GATE ✅ | DONE 2026-06-24 (§11.2): PASS/GO — sketch = (R1 A-side)+(R2 coords)+(R3 nondeg, all landed) + 1 isolated CRUX (joint χ-profile recovery, uniform-q); probe-validated (`Probe_FrameThenProbes`: frame not discrete, +log q probes close it); tool = exact quad-Gauss (present) vs Weil (absent=risk) | ALL heavy builds | — (done; GO, crux-first) |
| HUNT | citation search for (e) half-spin / (f) Suzuki-Tits WL-dim/base | §11.4 bespoke-vs-cite | redundant bespoke proofs |
| descent | confirm the `R' → ℤ` descent (char-0 `R'` w/ primitive `p`-th root) for `F(D,c)` | §11.3-1 | a silent gap in the closed form |

### 11.8 Net ordering

**[DONE 2026-06-24: `AUDIT-S` → `AUDIT-A`+`AUDIT-W` → `SPIKE-K.1`+`SPIKE-K.2` ⟹ ROUTE 1 chosen, abstract-`K` field-gen,
base `O(d+log q)` confirmed; `GATE` PASS (§11.2) — sketch = R1+R2+R3 (landed) + 1 isolated CRUX = joint χ-profile coordinate
recovery, uniform in `q`; build the crux FIRST.]** Remaining heavy build (now unblocked): **the CRUX recovery lemma** (state
`IsotropySeparatesAtBase` at the constructed `{frame ∪ O(log q) probes}` base + the R1/R3 reduction scaffold, isolating the
crux) → count-assembly bridge incl. `R'→ℤ` descent →
**the uniform kernel** — over abstract-`K` directly if AUDIT-A = GO (skipping the `q`-prime special case, §11.3-3) —
with the `|T_Q| = O(log n)` base bound → bundling + uniform base → **Step group 4 seam** (target pinned in AUDIT-S; glue
in parallel) → families d/e/f (HUNT-gated; uncitable ⟹ prove, never defer) → char-2 (cite-if-covered-else-prove) →
assemble into the **full** seal modulo `{G3 + cited}`. `decide` rides along as the per-family smoke-test.

---

## 12. Preexisting lemmas — the landed scaffolding the crux build reuses (index sweep 2026-06-24)

> **What this is.** A full read of `PublicTheoremIndex.md` surfaced substantial **already-built, axiom-clean**
> infrastructure for the Route-1 crux — more than the GATE assumed. Line numbers are rows in `PublicTheoremIndex.md`
> (the **Notes/Line** there give the source location). The headline: the crux's *extraction layer is essentially complete*
> and there are **two** decomposition routes to `IsotropySeparatesAtBase`, not one. Don't rebuild these.

**A. Extraction toolkit — `GaussCount.lean` (fully built; the count-assembly bridge, §11.3-1, is mostly *already here*).**
- `count_eq_charsum`  · `count2_eq_charsum`  · `countk_eq_charsum`  · `countk_eq_sum_charsum`  — k-fold counts as character sums.
- `sum_addChar_quadForm`  · `sum_quadForm_eval`  · `sum_addChar_quadForm_smul`  — multivariable quadratic Gauss sum + the `χ(s)^d` scaling.
- `card_quadForm_eq`  — the affine-quadric point count.
- `sum_addChar_multiQuad`  + `sum_addChar_multiQuad_zero`  — the multi-point Gauss sum **at a symmetry-broken base** (the inner sum of the k-fold count); `sum_addChar_linearMap`  evaluates the boundary.
- `count_pi_setValued`  — value-**set** → value-**point** counts (isotropy → Q-value).
- `multiCharSum_eq_sum_count`  — **Fourier inversion** (counts agree ⟹ Gram agrees). ★ The **shell-blindness of `isoClass`** is exactly where this hinge stops — the crux's hard core, precisely located.
- **★ R3 AUDIT REFINEMENT (2026-06-24) — what these bricks do and do NOT cover.** All of the above are **additive-character
  (ψ)** machinery: they are the complete engine for **D3a/Lemma A** (assemble `Z(S) = F(χ det Gram)`; the M2 hinge would give
  clean Gram-recovery *if* full pointwise `Q=c` counts were available). They **do NOT touch D3d**: with isotropy-only data
  (the `c=0` slice) the hinge stops at `χ(det Gram_S)`, and inverting square-classes-of-minors → Gram needs a **multiplicative
  character sum `∑_v χ(poly(v))` (Weil)** — Mathlib-absent, and absent here (`χ` appears only as the Gauss-sum *constant*
  `∏χ(wᵢ)`, never summed over a polynomial). So §12.A is the D3a toolkit; D3d's tool is a genuinely new (contained) build.
  `sum_addChar_quadForm_smul_ne_zero` (M2 cancellation) + `countk_eq_sum_charsum` are the load-bearing pair for the additive
  side; the **existential-counting route** (§13 R3 block) needs only these additive bricks for its finite-averaging wrapper,
  isolating the one Weil estimate.

**B. Forms-graph consumer — `FormsGraphConcrete.lean` (partially built; isolates the crux + a second decomposition).**
- `count_transport`  · `qvalue_count_transport`  · `isotropy_count_transport`  — move the counts into `V`.
- `isoSetOf` / `qSetOf` / `mem_isoSetOf_iff` · `coarse_eq_sum_iso`  — isotropy↔Q-value dictionary, fine→coarse.
- `QProfileSeparatesAtBase`  — **the M3 crux** (isotropy-counts at `T` ⟹ Q-profile); probe-validated for `VO⁻₄` at a **symmetry-broken** `T = frameBase ∪ {2e₃}`, 81/81.
- `isotropySeparates_of_qProfileSeparates`  — `QProfileSeparatesAtBase` + nondeg ⟹ `IsotropySeparatesAtBase`, **via `coords_determine`** ⟹ a *live* second route (see the correction below).
- ✅ **§1 now corrected** (verified against source 2026-06-24): this is a **live, in-build** (`lakefile.toml` `defaultTargets`), **general** (`p,d,Q,T`) module — NOT superseded. `isotropySeparates_of_qProfileSeparates` is PROVEN general (calls `coords_determine`); only the front-half `QProfileSeparatesAtBase` is the open crux (`:145` shell-blindness; probe-only, never closed in Lean). Reuse, don't rebuild.

**C. The general affine depth-2 engine our crux plugs into.**
- `IsotropySeparatesAtBase`  · `SeparatesAtBase`  · `separatesAtBase_of_isotropySeparates_weak`  · `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (1248, the live capstone).
- `discrete_affineScheme_of_twoRoundDiffSeparates`  · `affineScheme_relOfPair_translation`  · `affineDepth2Count`  — multi-coset-intersection-injectivity engine; `IsotropySeparatesAtBase → SeparatesAtBase →` this engine `→ Discrete`.

**D. General crux framing + an alternative node-4 capstone.**
- `PersistentTwinYieldsBlock`  + `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive`  — on the primitive floor the general crux collapses to "¬separates → IsLarge" (the general form of node 4 the geometric attack targets).
- `reachesRigidOrCameron_viaAffineFormScheme`  + `RelCountsDetermineOrbit`  · `cellsAreOrbits_of_relCountsDetermineOrbit`  — a **second** node-4 forms-graph capstone (general counting predicate at the free frame → `…viaSpielman`); relevant to the §11.6 seam optionality.
- `cellsAreOrbits_schemeAdj_singleton`  · `jointProfileRecoversAt_singleton`  — single-base recovery is project-wide free; multi-base is the open content (our crux is the concrete `VO^ε` instance).

**E. Base construction + seam.**
- `exists_greedy_base_le_log`  · `exists_greedy_base_scheme`  — the `O(log n)` base tool (§11.3-5).
- `AlgIso` (1328 `Separability` / 1361 `CoherentConfig`) — the **inter-scheme** iso object; sharpens AUDIT-S seam option (b) (the transport object exists; only a "seal-disjunction transports along `AlgIso`" lemma is missing).

**Approach impact (✅ FOLDED into §1 + the §11.2 GATE-refinement block, 2026-06-24; verified against source):**
1. **★ Correction to the GATE (§11.2):** `coords_determine` is **not** a dead route. The frame-locked (`d+1`) version is dead, but `QProfileSeparatesAtBase` + `isotropySeparates_of_qProfileSeparates` is a *live* alternative decomposition at a symmetry-broken base, probe-validated for `VO⁻₄(3)`. The build has **two** routes to the crux: (a) direct profile-injectivity (Lemma A/B, the `vo4minus_seal` path) and (b) Q-profile recovery + `coords_determine`. **Sharpened in §11.2:** (a)/(b) are two *packagings* of the SAME hard core (shell-blindness / joint `Z(S)`), differing only in the back-half.
2. The crux is **better-scaffolded than the GATE recorded** (extraction layer A fully built; Fourier hinge + shell-blindness locate the hard core) — strengthens the GO verdict. **§11.2:** the core's first attack = `count_pi_setValued → multiCharSum_eq_sum_count → sum_addChar_multiQuad_zero`.
3. **δ′ / forced-triangle route confirmed inapplicable** to the rank-3 core (route-doc §9.9.9a: no rainbow triangles, generic `λ,μ>1` ⟹ no `c=1` forced triangles), so the Gauss count route is genuinely necessary — closes a tempting shortcut.
4. **Direction unchanged** (Route 1 / `IsotropySeparatesAtBase` via uniform count-injectivity); these are refinements + a correction, not a redirect.

---

## 13. Discharge of `ZProfileSeparates` (D3d) — DONE; + floor-lowering assets

**What §13 was.** The scoped discharge of the one open research lemma — `QProfileSeparatesAtBase Q` for general `Q`,
reduced (D1 + D2-bridge, `ProfileReduction`) to the single predicate **`ZProfileSeparates Q T`** (= D3d = forms-graph
bounded WL-dim). **This is now CLOSED**: the q=p affine-polar seal `reachesRigidOrCameron_affinePolar` is built and in
`build.sh` (see STATUS + §1). The build-increment chronology (increment 3 `c₀≤¾`, the observable↔count bridge B1a/B1b,
the increment-4 cleanup, the singleton→pair correction, increment 5) is frozen in the archive + git; the decl-level map
is `PublicTheoremIndex.md`.

**Verified corrections worth NOT re-walking** (detail in the archive):
- **The observable is the PAIR count `Z_u({t,t'})`, not the singleton** — `Z_u({t})` is binary (`Probe_D3cObservable`),
  so `χ(Q)` is unobservable; the square class lives at `|S|=2`, where `Z_u({t,t'})` recovers `χ(det G₂)`.
- **D3d is Weil-free** — the per-pair character sum factors into additive Gauss sums (`PairForm.pairCharSum_factor_gen`,
  the reusable "no-Weil" core); the nondeg lines are triangle-bounded and absorbed by `hq1`, never beaten.

**Evidence base** (regression assets, `GraphCanonizationProject.Tests/A2MonovariantProbe.cs`, all green):
`Probe_D3dPairCount` (`c₀ ≤ 0.49 < 1`, `sep@1anchor ≈ 100%`, base `O(d log q)`), `Probe_D3cObservable` (the
singleton→pair correction), `Probe_Route2ExactSmallQ` / `Probe_Route2DegenerateLines` (the small-q tail).

### Floor-lowering assets — landed, axiom-clean, NOT in `build.sh`, NOT yet wired

These tighten the **per-anchor** `c₀` bound below the seal's `q ≥ 256`. **Important scope fact:** they do **NOT** by
themselves lower the *matching's* q-floor (`q ≳ 32d`) — that floor comes from the isotropic-shell counts `#{I_u=0}+#{I_v=0}`
(each `~|V|/q`) which `good_anchor_fail_le` folds into the matching's input `c`, controlled only by the loose
`zeroCountShift_card_le`. Tightening `NS` (the χ-equal block) leaves the shells untouched (at `q=3` each shell is
`~⅔|V|`). **Real floor-lowering (`q ≳ 32d → O(d)`) needs a TIGHT corank-based shell count** (`~|V|/q`, not the loose
`√q`-corrected bound) — that lemma is NOT yet designed; then small-q-with-growing-d walls the 2-point-frame matching and
needs larger separating frames. The per-anchor assets below are inputs to that eventual work, not a blueprint for it.

- **Corank tightening** (`q ≳ d² → q ≳ const`): `ScratchTBoundCorank.c0_le_threequarters_corank` — drop-in for
  `c0_le_threequarters` with `hq2 (64d²≤q)` removed, `hq3 (q≥256)` the lone binding threshold. Crux = the matrix-pencil
  `corank(A+t₀B) ≤ rootMultiplicity`. Modules: `ScratchPencilCorank`/`Bridge`/`Regroup`/`ScratchTBoundCorank`. A second
  variant `ScratchTBoundCorank2.c0_le_threequarters_corank2` reaches `q ≥ 16` (corank-cap `d−2` + a corank-1 `z_u` fix).
- **Small-q tail** (no threshold): `ScratchRoute2.c0_le_route2` — `NS ≤ (1 − 1/(4q²))·|V| < |V|` for odd `q ≥ 3` (good
  anchor, `d ≥ 4`). Modules: `ScratchCountTight` (`card_agree_le_tight : 2·NS ≤ zu+|V|+T`, the tighter pointwise identity),
  `ScratchRoute2Arith`, `ScratchRoute2`. **Coverage of per-anchor `c₀<1`:** odd `q∈{3,5,7,9,11,13}` → `c0_le_route2`;
  `q ≥ 16` → `c0_le_threequarters_corank2`; char-2 `q∈{4,8,16}` → separate Arf track (deferred, bespoke). Findings: the
  tight `zu` was NOT needed (loose `zeroCount_sq_le` suffices, `n ≥ q⁴` dominates); `line_regroup` is ℤ-validated but
  unused for the bound (the degenerate part is triangle-bounded via `corank ≤ d−2`, no cancellation). Caveat: `δ=1/(4q²)`
  is loose (true `c₀ ≤ 0.556`); only affects a matching base-size constant.

*Maintenance: this doc is the live proof target — keep §1's module map current as scratch modules port into the build
(the forms-graph pair-route closure was ported 2026-06-27), and update §11's audit/spike outcomes + the §11.1 route
decision as they resolve. Build history + superseded routes are frozen in
`docs/Archive/ChainDescent/chain-descent-formsgraph-wldim-archive.md`. Live seal: `reachesRigidOrCameron_affinePolar`
(q=p slice, in build); Witt-free capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree`
(`PublicTheoremIndex.md`); `VO⁻₄(3)` instance sealed (`ScratchBM3Glue.vo4minus_seal`).*
