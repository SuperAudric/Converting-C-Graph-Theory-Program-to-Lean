# Remaining work — the living tracker (modulo set · citation replacement · IR solver)

> **What this is.** The single, top-level tracker for *what is left* before the seal is unconditional and the
> canonizer is complete. It collects, in one place: the seal's current **`modulo` set** and what each hypothesis
> really is; the **citations** to be replaced by proofs (and the one that may stay cited); the **buildable
> non-research infrastructure**; and the **IR-blind-spot solver** (the forward payoff). It is a map — the
> authoritative state is each capstone's `#print axioms`, [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md),
> and the linked deep-dive docs' STATUS blocks. Quality bar throughout: axiom-clean
> `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned.

---

## STATUS (read first)

**The headline (2026-06-17).** The seal `reachesRigidOrCameron` is assembled and axiom-clean. Its live canonical
capstone `reachesRigidOrCameron_viaBoundedMinMult` stands **`modulo {G3 + hSmallAutThin + hcatch + hImprim}`**. The
three cleanup passes this session (`hcatch`, the separation engine, `hImprim`) reached a consistent conclusion:

> **The three non-G3 hypotheses are facets of ONE open object — the residue/constituent WL-recovery (`s(C)`) core —
> not four independent gaps.** In honest substance the seal is **`modulo {G3 + [one WL-recovery / s(C) core]}`.**

So "what's left" is short: **one research core** (conditional on the cited classification G3), plus a small amount of
**citation-formalization** and **one buildable infrastructure piece** (`EdgeGeneratesFromSet`), and the **forward IR
solver** (gated on the same core). There is **no long cleanup list**.

> **▶ UPDATE (2026-06-24) — the first forms-graph instance is SEALED.** `VO⁻₄(3)` (`ScratchBM3Glue.vo4minus_seal`,
> axiom-clean `[propext, Classical.choice, Quot.sound]`) closes the affine-polar residue at the minus form modulo `{G3}`
> — the first member of the forms-graph open residue below, now **proved** (not just empirically probed). The remaining
> node-4 content is the **generalization** to all small-Aut non-geom schurian rank-3 families **+ a cited classification
> *seam*** (no `SchemeEquiv`/transport exists in Lean yet — AUDIT-S finding 3). **▶ PROGRESS (2026-06-24, late): §11
> scoping DONE** (AUDIT-S/A/W, **Route 1 chosen**, **GATE passed**); the live work moved to
> [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) **§13** — the reduction chain
> (**D1 + D2-bridge**, `ChainDescent/ScratchCrux.lean`, axiom-clean) collapses the whole generalization to a **single open
> predicate `ZProfileSeparates`**, whose core = **D3d = uniform-`q` bounded WL-dimension of the affine forms-graphs**.
> **D3d is now WEIL-FREE** (the exact-vs-Weil question is resolved): the seal's observable is the **pair** count `Z_u({t,t'})`
> (not the singleton — a verified correction), its invariant `χ(det G₂)` is `χ` of a quadratic, and the per-pair sum factors
> into additive Gauss sums.
>
> **▶▶▶ UPDATE (2026-06-25) — INCREMENT 3 CLOSED (all axiom-clean, NOT in build.sh).** The Weil-free pair route's
> **per-anchor `c₀ ≤ ¾ < 1` bound is COMPLETE.** Capstone **`ScratchC0Final.c0_le_threequarters`**: for a good anchor
> (`hgood` ∃ nondeg pencil member + `hnz` no zero member + `hPu` pairForm≠0) with `q ≥ q₀` (`64q²≤|V|` ⟺ `d≥3`, `64d²≤q`,
> `256≤q`), the agreement count `NS = #{t : χ(I_u t)=χ(I_v t)} ≤ ¾·|V|`. Built across **8 new scratch modules** on top of
> `ScratchPairSep` (24 lemmas): `ScratchCorank` (corank-uniform radical bound `radical_card_mul_card_le`), `ScratchGoodAnchor`
> (good-anchor count `degenerate_count_le`, fully proven incl. the degeneracy⟺det bridge), `ScratchBucket`/`ScratchChiNorm`/
> `ScratchTBound` (the `|T|` bound `normT_bucket_bound`), `ScratchCount`/`ScratchC0` (counting identity `card_agree_le`),
> `ScratchC0Final` (`c0_le` + the capstone). **The reduction backbone `ZProfileSeparates → IsotropySeparatesAtBase → seal`
> is LANDED** (`ScratchCrux.isotropySeparates_of_zProfileSeparates` + `reachesRigidOrCameron_viaIsotropySeparates_wittFree`,
> both axiom-clean). **NEXT = the matching trick (increments 4–5) + the layered remainder** to general seal — see §3a.1 below.
> Read plan §13 (all-DONE) + [[project_witt_free_bridge_lead_2026-06-20]] (tail) + `ScratchC0Final.lean`.

---

## 1. The `modulo` set — what each hypothesis is, and its true status

The live capstone is `reachesRigidOrCameron_viaBoundedMinMult` (CascadeAffine §S-gate2). Capstone map:
[`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) seal section.

| Hypothesis | What it is | True status | Collapses to |
|---|---|---|---|
| **G3** (`hClassify`, `PrimitiveCCClassification`) | "large primitive ⟹ Cameron section" — the cited classification | **Citation** (Babai/Sun–Wilmes/Kivva). The one citation that *may stay cited* (CFSG-based). | — (kept) |
| **hSmallAutThin** | "small-Aut primitive residue ⟹ bounded `minMult`" = thick⟹large-Aut | **REDUCED to AFFINE this session (§9.9.18–18b):** for the SCHURIAN residue, Cameron+Liebeck+Skresanov ⟹ the residue is **affine** = `{1-dim cyclotomic — CITED (Ponomarenko-2-sep) + forms-graphs (c)–(f) — UNCITED, bounded-WL-dim OPEN}`. So **not** fully closed-mod-citations; the forms-graph part `{affine-polar, alternating, half-spin, Suzuki–Tits}` is the precise open residue — but now **explicit & CONSTRUCTIBLE** (refuting "no witness") and **PROBED across 3 classes: affine-polar `VO^-_4(q)` (q=2..5), alternating `A(5,2)`, Suzuki–Tits `VSz(8)` all SHATTER at base ≪ √n** (§9.9.18c, `Probe_FormsGraphs`; `VSz(8)` params validate exactly) — hSmallAutThin confirmed on the first unbounded-`s` (s=−3..−57) witnesses. **★ FIRST INSTANCE PROVED (2026-06-24): `VO⁻₄(3)` SEALED** (`vo4minus_seal`, axiom-clean) — the affine-polar minus-form residue is no longer only probed; open content is now the **generalization** to all `(ε,m,q)` + families (d)–(f) + the cited seam (plan §11). Sub-exp floor `n^{1/5}` (§2). | the affine slice; open residue = the **generalization** of the forms-graph families (plan §11, AUDIT-S done) — `VO⁻₄(3)` proved, the rest open. Non-schurian wall → IR-solver row 4 (§4). |
| **hcatch** | "1-WL cell ⟹ 2-WL fiber" = CFI-1992 Thm 5.2 (dimWL exchange) | At a complete extension `⟺ warmRefine discrete`. Free where 1-WL discretizes; residual = the `s(C)` certificate. | the core (§9.9.14–15) |
| **hImprim** | "imprimitive ⟹ block-recovered ∨ abelian-consumed" | Block-tower infra **built**; content = constituent WL-recovery (A2-ii), one tower-layer down. | the core (§9.9.16) |

**The collapse, precisely.** `hcatch` (1-WL↔2-WL exchange) and `hImprim` (constituent recovery) both reduce, via
landed machinery, to the same content as `hSmallAutThin`: *does the bounded-depth relation-count profile separate the
residue's orbits at a bounded base?* — the `s(C)` self-detection certificate (`RelCountsDetermineOrbit` /
`PersistentTwinYieldsBlock`). Deep-dives: [`chain-descent-a2-potential-route.md`](./chain-descent-a2-potential-route.md)
§9.9.14 (hcatch), §9.9.15 (the engine), §9.9.16 (hImprim).

**The 2026-06-17 reframe of that core (§9.9.17–18a).** The `s(C)` core, **for the seal's scope**, is the *schurian*
residue (the seal is typed on `SchurianScheme`; the non-schurian / high-WL-dim term `DiscretizesAtBases` is
provably split off to the IR-solver — §4, route §9.9.18a). Closure-angle work (§9.9.17) showed the "⟹ block" escape is
*vacuous on the primitive floor* (lemma `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive`), so the crux is the
2-closure deficiency `G^(2)_T/G_T`; Skresanov's rank-3 2-closure theory (§9.9.18) then shows **every small-Aut
non-geometric schurian rank-3 residue is affine** (Cameron kills almost-simple/grid; only affine survives). **C1
(§9.9.18b) then splits the affine target:** `{1-dim cyclotomic — CITED (Ponomarenko-2-sep / δ′) + forms-graphs (c)–(f):
affine-polar / alternating / half-spin / Suzuki–Tits — UNCITED, bounded-WL-dim OPEN}` ((b) bilinear forms is excluded as
geometric). So the schurian `s(C)` core is **mostly** reduced to citations, with the **forms-graph residue (c)–(f) still
open** — but now **explicit and constructible** (refuting "no witness"; the probe-record's 0 falsifiers were bounded-`s`
node-3 catalogue data, never these growing-`q` families). They are *probable* (small-Aut ⟹ group base `O(log n)`); the
open question is bounded-WL-dim for these 4 named classical schemes — far more tractable than "all SRGs". The
genuinely-open *uncited non-schurian* wall is the IR-solver row 4 (§4) — never the seal's obligation. Caveat (separate):
`SchurianScheme` is a carried model assumption (`orbitalScheme H`), not discharged.

**Citation-free / lighter endpoints already landed** (use these where the family fits — they carry *less*):
- `…viaRainbowRank` — rank-≥4 amorphic (rainbow-rigid) families, `modulo {G3 + hImprim}`, **no hcatch/largeness**.
- `…viaSpielman` — the **fully-citable, Cameron-free sub-exp floor**, carries only `hSpielman` (no G3/hImprim).
- `…viaG0powNeg` / `…viaG0powNeg`-family — the affine `H={±1}` family, δ′ closure **discharged** (not carried).
- `…viaCompleteBase` / `…viaBoundedMultiplicity` — node-2 discrete-base pipeline, `modulo {G3 + hcatch + hImprim}`.

---

## 2. Citation replacement — the table

Policy (user): **eventually all citations except maybe Babai (G3/CFSG) are to be fully built in Lean.** A citation is
carried as a labeled hypothesis (never a fresh `axiom`), so the build stays axiom-clean; "replacing" it means proving
it in-project and discharging the hypothesis.

| Citation | Where carried | Faithful source | Replace? | Notes |
|---|---|---|---|---|
| **G3 — primitive-CC / Cameron classification** | `hClassify` (all capstones) | Babai ITCS 2014 (rank 3) + J.Algebra 2015 (II); Kivva JCTB 164 (2024) (rank 4); Sun–Wilmes (`exp(n^{1/3})` threshold) | **Maybe not** (CFSG-based — the one allowed to stay cited) | The "or Cameron" escape. |
| **CFI-1992 Thm 5.2 — dimWL exchange** | `hcatch` | Cai–Fürer–Immerman 1992 Thm 5.2; Ponomarenko arXiv:2006.13592 eq. (41) | **Yes**, but largely **moot for the residue**: collapses onto the `s(C)` core; needs a `dimWL` framework to state verbatim. | Free where 1-WL discretizes. |
| **Spielman — primitive-SRG discretization** | `hSpielman` (`…viaSpielman`) | Spielman, STOC 1996 (`Õ(n^{1/3})` base) | **Yes** (a genuine but large WL/SRG result) | Gives the honest sub-exp floor, Cameron-free. **DELTA (2026-06-17, lit. check):** the SRG-iso *floor value* is `exp(Õ(n^{1/5}))` (Babai–Chen–Sun–Teng–Wilmes, FOCS 2013); `n^{1/3}` is the broader-PCC bound. Spielman's *individualize-to-discrete-at-base* form is what `hSpielman` consumes; confirm BCSTW gives a base statement before re-citing. See route §9.9.17 / [[reference_srg_wl_literature_2026-06-17]]. |
| **Affine cyclotomic 2-separability** | `…affineSlice` | Ponomarenko arXiv:2006.13592 Thm 1.1 | **Yes** — superseded for sub-families by the citation-free δ′/rainbow routes (`viaG0powNeg`, `viaRainbowRank`). | |
| **Babai SRG structure (node-4 form)** | `hSmallAutThin` | Babai ITCS 2014 + Kivva (the *structure*, at sub-exp threshold) | **= the research core** — at poly threshold it is *open*, not a citation. | The wall. |

**Net:** the only citation expected to remain is **G3 (Babai/CFSG)**. `hcatch`/`hImprim` are not really "citations to
replace" — they are the project's own `s(C)` core in disguise (§1). Spielman and the affine 2-sep are genuine
citations that *can* be built but are not on the critical path (the δ′/rainbow routes already bypass them per-family).

---

## 3. The remaining work items (categorized)

### 3a. The research core — `hSmallAutThin` / the `s(C)` certificate (node 4)

> **★★★ 3a.1 — THE LAYERED REMAINDER (2026-06-25, authoritative "what's left" from increment-3-done to general seal mod
> citations).** Increment 3 (per-anchor `c₀ ≤ ¾`) is CLOSED (capstone `ScratchC0Final.c0_le_threequarters`, axiom-clean).
> The remaining work, by layer (★=open, ✓=landed):
> - **Layer A — finish discharging `ZProfileSeparates` for affine-polar (the live frontier = increment 5).**
>   - ✓ **Increment 4 — FULLY DONE (cleanup CLOSED), axiom-clean** (`ScratchIncr4`/`b`/`c`/`d`).
>     Anchor-averaging backbone `fail_count_split`/`matching_F_bound` (`F ≤ c·|V| + |V|·β_full`). **Input `c`:**
>     `good_anchor_fail_le_const` (good anchor ⟹ `#{¬sep} ≤ 15/16·|V|`). **Bad-anchor `β`:** `pencilDetPoly` CONSTRUCTED +
>     `badHgood_count_le`; **B-iii** `pencilDetPoly_totalDegree_le ≤2d` + **B-ii** `beta_count_closed` (`β·|K| ≤ 2d·|V|+2·|K|`) +
>     **C-corr** `beta_full_count_closed` (full good-anchor predicate incl. `Q(t₀−u),Q(t₀−v)≠0`, kills bridge corr:
>     `β_full·|K| ≤ (2d+4)·|V|+2·|K| = O(d/q)`). **C-basis** `exists_orthoAnisotropic_basis`+`associated_separatingLeft_of_polarRad`
>     (bridge's `hv/hw`). **NV** `ScratchIncr4d.exists_hgood` (14 lemmas: `hgood` non-vacuity, for `u≠v`/nondeg `Q`/`finrank≥2`/
>     `|K|≥7`). So `c̄₀ = c/|V|+β_full/|V| ≤ 15/16 + O(d/q) < 1`, **β unconditional** modulo family props. No carried existence
>     hypotheses remain in inc-4.
>   - ★ **Increment 5 (THE LIVE FRONTIER) — the matching assembly + bridge wiring:** feed `c̄₀<1` into
>     **`ScratchMatching.exists_separating_base` (LANDED, axiom-clean)** (`m=O(d log q)`, needs a `c̄₀ᵐ`-smallness ℕ helper)
>     ⟹ separating base; define matching `fail := ¬(bridge criterion)` so `¬fail ⟹` separation IS
>     `jointIsoCount_ne_of_chiSep_pair` (its `corr`/`hv`/`hw` discharged by C-corr/C-basis; per-pair anchor existence = NV
>     `exists_hgood`); then `zProfileSeparates_of_zSep` → seal. **MAIN CARE (field/seam typing) ✅ RESOLVED 2026-06-26 — the
>     lift-first is DONE** (concern #4: `ScratchFieldGen`/`ScratchFieldGenAdapter`/`ScratchBridgeK`/`ScratchLemmaAK`/`ScratchBridgeAllK`,
>     all axiom-clean), so increment 5 wires over **abstract `K`** with the K-named lemmas (`jointIsoCountK_ne_of_chiSep_pair` →
>     `zProfileSeparatesK_of_zSep` → `isotropySeparatesK_of_zProfileSeparatesK` → `reachesRigidOrCameron_viaIsotropySeparatesK_wittFree`
>     for q=p). Plus the **decoupled #1 corank tightening ✅ DONE 2026-06-26** (`q≳d²`→`q≳const`; capstone
>     `ScratchTBoundCorank.c0_le_threequarters_corank` = drop-in replacement for `c0_le_threequarters` with `hq2` removed —
>     increment 5 should call the `_corank` capstone). Full layout: plan §13 "INCREMENT 5 — WHAT'S EXPECTED" + top SESSION-2 handoff.
>   - ✓ **Observable↔count bridge — CLOSED END-TO-END 2026-06-26** (`ScratchBridge`/`A`/`B`/`C`/**`D`**/`Z`, all axiom-clean):
>     `c0_le_threequarters` is in `χ(det G₂)`-agreement; `ZProfileSeparates` is in the joint counts `Z_u(S)`. Chain: (config-nondeg
>     χ-separating base) →[`pairCount_ne_of_chiSep_field` (**B1b**, ℂ) + the per-pair closed form `jointIsoCount_pair_closed_corr0`
>     (**B1a**: `Z_u·p³ = |V| + χ(I_u)·K·(p[Q w₀=0]−1)`)]→ (`Z`-separating base) →[`zProfileSeparates_of_zSep`]→ `ZProfileSeparates`,
>     packaged as the per-pair capstone **`jointIsoCount_ne_of_chiSep_pair`**. **B1-deg DISSOLVED** (config-degenerate locus density
>     `O(1/√q)`, folds into the increment-4 matching density). **All B1a wraps LANDED** — (i)`ScratchBridgeB` + (ii)`ScratchBridgeC` +
>     **(iii) `ScratchBridgeD.chi_configDet_eq_chi_pairForm`** (`χ(D)=χ(I_w)`; `½·polar` factor + change-of-basis both enter as squares
>     killed by `χ`) + the ℂ assembly. Carried: `hK : gaussSum²·∑ψ(Q)≠0` (independent Gauss nonvanishing). ★ **FINDING:** the `corr`
>     term ([both config-diffs isotropic], codim-2, `O(1/q²)`) ⟹ increment-4 good-pair predicate gains `corr=0` → `{hgood ∧ hnz ∧ corr=0}`.
>     NO Weil, NO `R'→ℕ` descent (worked over ℂ), NOT a hidden wall. (Plan §13 BRIDGE block; prime-field model `q=p`.)
>   - ✓ **Field generalization (concern #4) — DONE 2026-06-26 (the analytic + bridge lift).** `c0_le_threequarters` was already
>     abstract `[Field K]`; the rest (`ScratchCrux`/`ZProfileSeparates`/`IsotropySeparatesAtBase` + the bridge) is now lifted to
>     **abstract `[Field K][Fintype K]`** V-indexed (`ScratchFieldGen`+`ScratchLemmaAK`+`ScratchBridgeAllK`+`ScratchBridgeK`), with
>     the q=p adapter `ScratchFieldGenAdapter` connecting to the in-build seal capstone. GaussCount was already abstract ⟹ the lift
>     was mechanical. **Remaining:** the q=pᵉ SCHEME seam (`efield` transport, Layer D — separate); + the **small-q tail** (explicit
>     handling of sub-threshold `q < 256`; the corank tightening already lowered the threshold from `q≳d²` to the constant `q≥256`).
> - **Layer B — `ZProfileSeparates → seal`: ✓ LANDED.** `isotropySeparates_of_zProfileSeparates` (ScratchCrux) +
>   `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248), both axiom-clean (no Witt, no `hSmallAutThin`). ⟹ once
>   Layer A lands, **affine-polar `VO^ε` is sealed modulo `{G3}` + the seam.**
> - **Layer C — other forms-graph families (★, spikes done 2026-06-26).** Pair route is generic in a *quadratic* `Q` (covers
>   affine-polar in one stroke), but NOT: **(d) alternating** (alternating bilinear form, own predicate, same technique, medium);
>   **(e) half-spin** (char-agnostic form-adjacent spinor geometry — expect a transfer closer to affine-polar; spike pending);
>   **char-2 §11.5** (uncitable per the char-2 feasibility check; whole odd-char A-side evaporates — no `χ`; needs a from-scratch
>   Mathlib substrate = Arf invariant + char-2 quadric count via additive-trace; the combinatorial layer reuses char-agnostically;
>   distinct track); **(f) Suzuki–Tits** — SPIKED (plan §11.4): reachable not a wall, but **folds INTO the char-2 track** (it IS
>   char-2: `Sz(q)`, `q=2^{2e+1}`) and is the most bespoke analytic engine (non-form σ-twisted ovoid, cospectral with `VO⁻₄`).
>   Optimistic path = direct geometric individualization on the explicit Tits coordinates (no `χ`/Weil); fallback = σ-twisted
>   count (Weil risk). The handle is findable; the open question is which.
> - **Layer D — the structural seam (◐ SPIKED 2026-06-26, `ScratchSeam.lean`, axiom-clean; §11.6).** The cited classification
>   case-split routing the abstract residue `S` → concrete `affineScheme(Q)`, where `{G3 + Skresanov + Liebeck + Ponomarenko-2-sep}`
>   get consumed. **The seam CLOSES architecturally** — stub `reachesRigidOrCameron_viaSchurianRank3Affine` compiles, reducing it to
>   ONE new obligation `htransport` (the seal disjunction is invariant along a realizing permutation). `htransport` is **mechanical,
>   not a wall**: the riskiest disjunct (`SchemeRecoveredByDepth`) sits on the landed `forcedNode_relabel` (full iso-invariance under
>   arbitrary relabelling) + `IsAut`/`IsBase` conjugation. Build it as a real lemma (option b); option (a) (hide transport in the
>   citation) rejected as unfaithful. No longer the under-scoped unknown — bounded, landed-atom-backed glue. Still the biggest
>   *structural* build beyond affine-polar, but de-risked.
> - **Layer E — carried hypotheses (Lean-carried, not new math): `hImprim`** (block tower built; collapses to same core) +
>   **`SchurianScheme`** (model assumption `orbitalScheme H`, not discharged).
> - **Layer F — PORT (mechanical, no math):** the 8 new modules + `ScratchCrux`/`Matching`/`PairSep`/`LemmaA-B`/`BM3*` into
>   `build.sh`+`lakefile`+`PublicTheoremIndex.md`. Same "only remaining = PORT" status as the sealed `VO⁻₄(3)` modules.
> - **Residual citations at the endpoint:** `{G3` (Babai/CFSG, allowed to stay)` + Skresanov + Liebeck + Ponomarenko-cyclotomic-2-sep}`.
>   Honest caveat: affine-polar alone isn't the whole residue — the seam (D) + non-quadratic families (C) are where "general
>   seal" still needs real work or citations.

> **▶ LATEST (2026-06-24): `VO⁻₄(3)` SEALED — the first forms-graph instance proved; live work = the generalization.**
> `ScratchBM3Glue.vo4minus_seal` (axiom-clean) closes the affine-polar minus-form residue modulo `{G3}`. The remaining
> node-4 content is the **generalization** to all small-Aut non-geom schurian rank-3 families + a **cited classification
> seam** (AUDIT-S done — per-family target = `IsotropySeparatesAtBase Q_fam T_fam`; `SchurianScheme` free; the seam is
> unbuilt and is the genuine new obligation). Forward roadmap =
> [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §11. **The dated bullets below are
> landed history** (the `QProfileSeparatesAtBase` route, the Lemma A/B build, etc. — superseded by the seal; provenance
> in the plan's `Archive/`).

> **★ MAJOR REFRAME (2026-06-17, route §9.9.18, Skresanov): node-4-SCHURIAN is AFFINE, not uncited open math.**
> A schurian rank-3 residue has `Aut(X)=G^(2)` = a primitive rank-3 group; Cameron's trichotomy + small-Aut (kills
> almost-simple/grid as large) ⟹ **only affine survives**; Skresanov [arXiv:2007.14696/2202.03746] pins `G^(2)` affine.
> Merged with §9.9.9b (non-affine amorphic = non-schurian): **every small-Aut primitive *schurian* residue is affine**,
> hence in the domain of the affine slice. This moves node-4-schurian from "uncited open" to the citation stack
> `{G3 + Liebeck + Skresanov + Ponomarenko-cyclotomic-2-sep + finite exceptions}` — the "conditional on citations" goal,
> at the cost of citations beyond G3. The genuinely-uncited "thick wall, no witness" is a **non-schurian** abstract-SRG
> phenomenon that **cannot be a WL-closure residue**. **(C3) RESOLVED (route §9.9.18a, verdict A):** the seal is
> *deliberately* scoped to schurian residues — `StablyRecoverable ↔ DiscretizesAtBases ∧ RecoversWhileSymmetric`, and
> the seal is keyed IR-core-free (`reachesRigidOrCameron_viaSymmetricRecovery` drops `DiscretizesAtBases`). So the
> Skresanov reduction genuinely **completes the SEAL's node-4 obligation modulo citations** — node-4-*for-the-seal* =
> affine. The genuine wall is **relocated** to the IR-solver's row 4 (non-schurian, generic unbounded-`s`, where A2 may
> fail ⟹ flag) — by design, not a seal gap. **PENDING:** (C1) the forms-graph affine classes (e.g. bilinear `H_q(2,m)`,
> small-Aut + non-geometric + affine-but-not-cyclotomic) need a non-cyclotomic separability citation — the main open
> hole. Separate acknowledged gap: `SchurianScheme` is a carried model assumption (`orbitalScheme H`), not discharged
> from the canonizer's output.

**One object, three faces** (the residue, the 1-WL↔2-WL exchange, the imprimitive constituents). The open question:
*does the bounded-depth relation-count profile separate the small-Aut primitive residue's orbits at a bounded base?*
- **Status:** open, GI-adjacent. No constructible falsifier across every probe (sporadics, trivial-Aut, cospectral
  mates, Doob/Hamming twists, k-WL ladder — all negative). Not directly attackable by covers/regularity/WL-level/twists
  (all closed, §9.9.10–12). The honest characterization: *is the WL-dim gap `base − b(Aut)` bounded for the residue?*
- **Intended discharge:** ~~the fusion / closed-subset closure (`schemeEquiv_trans`) for `PersistentTwinYieldsBlock`~~
  **— CORRECTED (2026-06-17, route §9.9.17): the block escape is VACUOUS on the primitive floor** (a primitive scheme
  has no nontrivial proper `ClosedSubset`, so `PersistentTwinYieldsBlock` collapses to `¬Separates → IsLarge`;
  lemma `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive`). The fusion-closure block construction discharges
  only the *imprimitive* case (already `hImprim`). The primitive crux is irreducibly the **2-closure deficiency**
  `G^(2)_T / G_T` = `s(X)` wall, with no block shortcut. Project verdict unchanged: *won't close from Mathlib alone.*
- **The closure angle, precisely (route §9.9.17):** the open content factors as (A) `Separable` + (B) the transport
  + (C) a bounded group base; **(C) is FREE** (`exists_greedy_base_le_log`, `b(G)=O(log n)` for small Aut). The open
  (A)+(B) = *the point extension recovers Aut-orbits at a bounded base* = no 2-closure deficiency. Its group-theoretic
  form is **Skresanov's rank-3 2-closure** theory (`G^(2)` structure) — the closure-angle and Skresanov leads merge.
  **Concrete next:** test whether Skresanov's rank-3 `G^(2)` description trivialises the deficiency at a bounded base
  for the affine residue (an affine-rank-3 carve capstone, sibling to the cyclotomic slice). See [[reference_srg_wl_literature_2026-06-17]].
- **Floors available now:** sub-exp via `…viaSpielman` (fully citable, Cameron-free; floor value `exp(Õ(n^{1/5}))`, §2 DELTA).
- **★ Stage A LANDED (2026-06-18, axiom-clean):** `reachesRigidOrCameron_viaAffineFormScheme` (CascadeAffine.lean,
  `PublicTheoremIndex.md:1207`) is the conditional capstone for the schurian node-4 forms-graph residue. It carries the
  free group base `IsBase … T` + the certificate `hFormCert : RelCountsDetermineOrbit … T` (the **only open content**),
  composing the landed depth-`k` engine + base + `…viaSpielman`; **no `hSmallAutThin`**. The route is validated
  end-to-end; the open content is now exactly `hFormCert`.
- **★ Stage B.0 LANDED (2026-06-18, axiom-clean):** `reachesRigidOrCameron_viaOrthogonalForm` + the quadratic-form
  infrastructure (`isometryGroup`, `coords_determine`, `polar_eq_of_sub`, `frameBase`) (CascadeAffine.lean §OrthogonalForm,
  `PublicTheoremIndex.md:1210-1217`). For any nondegenerate-polar `Q` on `F_p^d`, the **isometry** group `O(Q)` affine
  scheme discretizes at the basis-frame (size `d+1`) and seals via **depth-1** — the orbit-of-difference determines
  `Q(v−t)`, recovering form coords (`coords_determine`, the crux's Witt-free back-half). **Caveat:** `O(Q)` is the *finer*
  orthogonal scheme, **not yet** the rank-3 SRG `VO^ε`. **Next = Stage B.1**: the **similitude** group `ΓO(Q)` (rank-3
  SRG; depth-1 → isotropy bits only) + the genuine two-round **count** crux (Route A; back-half = `coords_determine`),
  `d=4 VO^ε_4(q)` first. Residual = the non-isotropic shell. Plan: [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §1–§2 (now `VO⁻₄(3)` SEALED) + §11 (generalization).
- **★ Stage B.1 LANDED (2026-06-18, axiom-clean):** the **similitude** group + the node-4 conditional capstone —
  `similitudeGroup` (`GO(Q)`), `neg_mem_similitudeGroup`, `isometry_le_similitude`, `SimilitudeFrameSeparates` (the
  named count crux), `reachesRigidOrCameron_viaSimilitudeForm` (CascadeAffine.lean §OrthogonalForm,
  `PublicTheoremIndex.md:1218-1222`). The genuine rank-3 SRG `VO^ε` residue (`affineScheme (similitudeGroup Q)`) seals
  once `SimilitudeFrameSeparates Q` holds; open content isolated to that one predicate. **Carries NO `hSmallAutThin`.**
- **★ RESEARCH-CORE CHECKPOINT CONFIRMED (2026-06-18, axiom-clean):** `reachesRigidOrCameron_viaCountsDetermineFrameQ`
  + `CountsDetermineFrameQ` + `similitudeFrameSeparates_of_countsDetermineFrameQ` + `FrameCountsAgree`
  (`PublicTheoremIndex.md:1223-1226`). The chain is now confirmed END-TO-END modulo one front-half predicate:
  `CountsDetermineFrameQ` (= Witt + Gauss) →[`coords_determine`, landed]→ `SimilitudeFrameSeparates` →[landed]→ seal.
  So the research core is **sound** (the heavy machinery, once built, provably closes), and the B.0 back-half
  `coords_determine` is confirmed to compose. The entire open content is isolated to `CountsDetermineFrameQ`.
- **★ WITT-BOUNDARY CHECKPOINT CONFIRMED (2026-06-18, axiom-clean):** `reachesRigidOrCameron_viaIsotropyCounts` +
  `OrbitIsIsotropyClass` (Witt deliverable) + `IsotropyCountsRecoverFrameQ` (Gauss deliverable) +
  `countsDetermineFrameQ_of_orbitIsIsotropyClass` (`PublicTheoremIndex.md:1227-1233`). Splits the open content along
  the Witt | Gauss boundary: `OrbitIsIsotropyClass` + `IsotropyCountsRecoverFrameQ` → `CountsDetermineFrameQ` → seal.
  B.1c-ii's exact target (pure isotropy-class counts ⟹ frame `Q`-profile, no opaque relations) is now confirmed.
- **★★ CORRECTION (2026-06-18 later) — the B.1c predicates are MIS-SHAPED; the bullets just above are SUPERSEDED.**
  Finite probe over `VO^ε_4(3)`: `IsotropyCountsRecoverFrameQ` / `CountsDetermineFrameQ` / `SimilitudeFrameSeparates`
  are **FALSE at the standard frame** for `VO^-` (one-round count shell-blind via the frame's `e_i`-swap isometry).
  The scheme still discretizes (iterated WL) ⟹ bounded-WL-dim holds; fix = a **symmetry-broken base** (`≈ d+2`, greedy
  size-4 at q=3) where the one-round count IS injective. Landed B.1 capstones (`via{IsotropyCounts,CountsDetermineFrameQ,
  SimilitudeForm}`, idx 1221-1233) axiom-clean but **unprovable as stated → need reformulation** around base
  `T = frameBase ∪ {p}`; the "recover-Q-profile-then-`coords_determine`" architecture is wrong for minus-type. Correct
  target = **direct count-injectivity at the symmetry-broken base** → `discrete_of_kRoundRelationSeparates` → seal (no
  `coords_determine`). **Gauss-sum toolkit BUILT** (13 axiom-clean lemmas, `ChainDescent/ScratchGauss.lean`, WIP/Mathlib-
  only): A/A2/B1/B2/B3/eval/scaling/`card_quadForm_eq`/D1/`sum_addChar_multiQuad`/helpers. Remaining = k-fold count
  (generalize `count2_eq_charsum`; inner = `sum_addChar_multiQuad`) + inclusion-exclusion + injectivity at the broken
  base + bridge + PORT. **B.0 (`viaOrthogonalForm`, isometry `O(Q)`) UNAFFECTED.** Witt (B.1c-i `OrbitIsIsotropyClass`)
  still needed for orbit=isotropy-class. Authoritative: plan doc STATUS (the ⚠/⚠⚠ boxes).
- **★ WITT REMOVED FROM THE CRITICAL PATH (2026-06-20, axiom-clean, full build green).** `OrbitIsIsotropyClass`
  (the Mathlib-absent "heaviest piece") is **off the seal's critical path.** New axiom-clean decls in
  `CascadeAffine.lean §OrthogonalForm` (`PublicTheoremIndex.md:1243-1248`): the easy-half `RelationRefinesIsotropy` is
  **discharged Witt-free outright** (`relationRefinesIsotropy_similitude`, via similitude-invariance), the bridge
  `separatesAtBase_of_isotropySeparates_weak` needs only it, and the capstone
  **`reachesRigidOrCameron_viaIsotropySeparates_wittFree`** seals the `VO^ε` residue carrying ONLY a bounded base + the
  Gauss target `IsotropySeparatesAtBase Q T` — NO Witt. Witt is needed only for the cosmetic rank-3 identification the
  seal never uses. **⟹ proving `IsotropySeparatesAtBase Q T₉` seals `VO⁻₄(3)` modulo `{G3}` ALONE.** The "capstone also
  needs `OrbitIsIsotropyClass` (parallel Witt track)" framing below/above is SUPERSEDED.
- **★ STEP-4 BUILD UNDERWAY via the LEMMA A / LEMMA B split (2026-06-20).** The live route now proves
  `IsotropySeparatesAtBase Q T₉` **directly** (Lemma A = "isotropic-incidence count = explicit Gram-function on
  nondeg configs"; Lemma B = "counts recover `u`"), **superseding the `QProfileSeparatesAtBase` framing** of the bullet
  below. Uses the **size-9 base `T₉`** (avoids degenerate cases). Landed axiom-clean (WIP scratch, NOT in build):
  **A-M1+A-M2** (`ChainDescent/ScratchLemmaA.lean`: cone-count → homogeneous level-set, for invertible config Gram) and
  **B-M1+B-M2-bridge** (`ChainDescent/ScratchLemmaB.lean`: antecedent → incidence-agreement, + `y=0` correction). The
  two novel reductions are done; **NEXT = A-M3** (`card_quadForm_eq` on subspace `Uᗮ`) → A-M4 → B-M3 → ASM. Authoritative:
  plan [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §1 (decl map) + §11 (roadmap); full build records in the plan's archive.
- **★★★ CURRENT (2026-06-18 HANDOFF) — reformulation + M0–M3 LANDED; the bullets above are landed history.** The
  reformulation around a symmetry-broken base is DONE (`SeparatesAtBase` / `IsotropySeparatesAtBase` /
  `reachesRigidOrCameron_via{SymmetryBrokenBase,IsotropySeparates}`, the frame-locked predicates ⚠ SUPERSEDED in-source);
  the Gauss toolkit is PORTED to a real module **`ChainDescent/GaussCount.lean`** (18+ axiom-clean lemmas); the consumer
  **`ChainDescent/FormsGraphConcrete.lean`** has the M0–M3 chain (transport, fine→coarse conversion, the M3 reduction).
  **The ENTIRE remaining Gauss-work content is now ONE open predicate `QProfileSeparatesAtBase Q T`** (counts at
  `T = frameBase∪{2e₃}` recover the `Q`-profile; probe-validated `VO^-_4(3)` 81/81, UNPROVED). `isotropySeparates_of_qProfileSeparates`
  + `coords_determine` reduce the seal to it; M4 is wiring but **blocked** on it. **Two viable discharge routes fully
  expanded in the plan's archive (`Archive/ChainDescent/chain-descent-formsgraph-wldim-archive.md`) §10:** (1) explicit
  Gauss/incidence `Z(S)` computation (Witt-free, recommended; open step = a char-sum inversion), (3) structural perp-graph
  + Witt frame-rigidity (blocks on building Witt). Carrying the predicate as a certificate is RULED OUT (quality bar). Key
  constraint: `isoClass` is shell-blind ⟹ pointwise-count machinery off-path; recovery is the joint `Z(S)`. **Authoritative:
  plan §9 (milestones) + §10 (handoff).**

### 3b. Buildable non-research infrastructure — `EdgeGeneratesFromSet`
The **checkable multi-base isolation closure** — the relation-count analogue of `dominatorReachable_of_rainbowRank`:
a structural sufficient condition that *produces* the `s(C)` separation certificate for a family (makes recovery
checkable). The single-base `EdgeGenerates` exists (`Scheme.lean`) but fails on cyclotomic/catalogue schemes; the
multi-base version is deferred ([`chain-descent-self-detection-plan.md`](./chain-descent-self-detection-plan.md) §9.3).
- **Status:** buildable, moderate; **not on the seal's critical path** (it adds checkability, not closure).
- It is the *one* shared piece behind the engine (§9.9.15) and `hImprim` (§9.9.16).

### 3c. Citation formalization (optional, off critical path)
- **Spielman** → fully built `…viaSpielman` (large WL/SRG result).
- **Affine cyclotomic 2-sep** → mostly superseded by δ′/rainbow per-family; build only if a uniform affine closure is wanted.
- **CFI-1992 dimWL exchange** → needs a `dimWL` framework; moot for the residue (§1). Lowest priority.

### 3d. Node-2 polish (optional)
A *uniform* rainbow rank for a parametric amorphic family (generalize `clebschZ4`/`clebschScheme` off `n=16`) →
feeds `…viaRainbowRank` / `…viaCompleteBase`. Honest scope (§9.9.9b): the schurian rainbow-rigid amorphic instances
are **affine** (leg-B-adjacent); the genuinely-new non-affine ones are non-schurian (not residues). So this is
citation-reduction on the affine amorphic slice, **not** new territory and **cannot** approach node 4 (rank-counting,
§9.9.9a). Low priority.

---

## 4. The IR-blind-spot solver (the forward payoff)
**Doc:** [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) (STATUS first).
Canonizes the **rigid** residue (incl. the multipede / IR-blind-spot that 1-WL cannot discretize) in polynomial time.
- **Gating:** its polynomiality is delivered by A2 (bounded WL-dim of the residue: `c(X_T), k(X_T) = O(1)` at an
  `O(1)` base) — the IR-solver's polynomiality and A2's last open quantity are **the same object in two languages**.
- **★ POST-SKRESANOV SPLIT (2026-06-17, §9.9.18a) — this is where the genuine wall now lives.** A2 is one predicate
  (bounded WL-dim) over two residue classes. On the **schurian** residue (the seal's scope, §3a) A2 is delivered by
  the Skresanov reduction (residue is affine ⟹ affine slice, mod citations). On the **non-schurian** residue — the
  IR-solver's "row 4" (generic unbounded-`s` SRG, multipede) — A2 may **fail**, and that is exactly where the canonizer
  **flags** ("polynomial-or-flag"). So §3a's reduction does **not** cover the IR-solver's case; the genuinely-uncited
  open research is **this non-schurian row 4**, which was never the seal's obligation (it is `DiscretizesAtBases`, split
  off by `stablyRecoverable_iff_symmetric_and_bases`). Closing it = closing the *overall*-canonizer poly wall.
- **Status:** *solver not built;* prerequisites landed (deferral architecture, direction-blind canonizer substrate,
  the potential-descent engine `exists_potential_descent`, A2's consumer chain).
- **★ ROW 4 IS NOW UNDER ACTIVE ATTACK — "option 2" (2026-06-20, IR doc §11).** The flag set is *attackable*, not just
  acceptable: the multipede is **F₂-linear**, and the descent (WL) = F₂ **unit-propagation**, which stalls where
  **Gaussian elimination** does not. **Layers A–C DONE** (probe-/prototype-clean): the rigid gap is real & constructible
  (var-regular meager expander: `dim ker = 0` but descent forcing `Θ(n)`); WL = unit-prop verified on real multipedes;
  the F₂ system `H` is **soundly extractable from the descent alone** (no gadget recognition). **Layer D PLANNED**
  (IR doc §11.10, **C# first**) = the row-space generalization of the *deferred/unbuilt* C# `LinearOracle`
  (`TwistConstruction.cs` is the `ker`-half), a Phase-2 F₂-Gaussian pre-processor. **Scope/flag floor** (honest): option
  2 absorbs the canonical **F₂-multipede**; the **ring-varying** residue (Lichter, FPC+rank ≠ P) + unbounded-arity +
  non-WL-easy-base stay the flag floor. Memory: [[project_option2_f2_gap_2026-06-20]].

---

## 5. One-screen summary

```
SEAL  reachesRigidOrCameron_viaBoundedMinMult   modulo {G3 + hSmallAutThin + hcatch + hImprim}
                                                  └──────────── collapses to ───────────┘
                                                  modulo {G3 + the SCHURIAN s(C) core}
                                                          └── Skresanov (§9.9.18) ──┘
                                                          = the AFFINE slice, mod {G3+Liebeck+Skresanov+2-sep+C1}

REMAINING:
  3a  the schurian s(C) core ............. REDUCED to AFFINE (Skresanov). Splits (C1, §9.9.18b):
                                            • 1-dim cyclotomic ... CITED (Ponomarenko-2-sep / δ′)
                                            • forms-graphs (c)-(f) ... UNCITED, bounded-WL-dim OPEN, but
                                              EXPLICIT & CONSTRUCTIBLE (affine-polar/alternating/half-spin/Suzuki),
                                              and PROBED across 3 classes (§9.9.18c): VO^-_4(q) base=[5,5,6,7] vs
                                              √n=[4,9,16,25] (q=2..5); Alt(5,2) base 8 (√n 32); VSz(8) base 9
                                              (√n 64) — ALL SHATTER ⟹ hSmallAutThin confirmed, s=−3..−57.
                                              PROOF PLAN: chain-descent-formsgraph-wldim-plan.md — free base +
                                              landed depth-k engine + ONE crux lemma (count profile recovers form
                                              coords B(v,e_i)). Stage A capstone reachesRigidOrCameron_viaAffineFormScheme
                                              LANDED (2026-06-18, axiom-clean) — open content isolated to hFormCert;
                                              Stage B = discharge hFormCert for VO^ε.
  3b  EdgeGeneratesFromSet ............... BUILDABLE infra (checkability; off critical path)
  3c  citation formalization ............ OPTIONAL (Spielman n^{1/5} / affine 2-sep / CFI dimWL; off path)
  3d  node-2 uniform rainbow rank ....... OPTIONAL (affine/leg-B; can't reach node 4)
  4   IR-solver row 4 (NON-schurian) ..... THE GENUINE UNCITED WALL — generic unbounded-s SRG where A2 may
                                            fail ⟹ flag. Outside the seal by design; the canonizer's poly wall.
```

**Bottom line.** The seal's open content reduces to the *schurian* `s(C)` core; this session's Skresanov reduction
shows that core is **affine**, and C1 sharpens the residue to **four explicit constructible forms-graph families**
(affine-polar / alternating / half-spin / Suzuki–Tits) whose bounded-WL-dimension is *open but uncited* — the
cyclotomic part is already cited. So the SEAL is *mostly* citations-away, with one precisely-characterized,
probable, *probable-by-experiment* open residue (no longer a mysterious wall). The **genuine uncited research wall is
the non-schurian IR-solver row 4** (the forward payoff), never the seal's obligation; the canonizer stays
"polynomial-or-flag" with the flag set = exactly that row 4.

---

*Maintenance: update §1's modulo table when a capstone's `#print axioms` carry-set changes; update §3 as items land;
keep the deep-dives (`chain-descent-a2-potential-route.md` §9.9.x, `-ir-blindspot-solver.md`, `-self-detection-plan.md`)
authoritative and this doc a one-screen map.*
