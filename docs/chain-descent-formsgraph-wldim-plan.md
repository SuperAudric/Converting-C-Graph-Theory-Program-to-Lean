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

> **▶▶▶▶▶ CURRENT HANDOFF (2026-06-26, SESSION 2 — read THIS first; supersedes the SESSION-1 handoff block just below).**
> **User-set working order (one at a time): #4 field-gen (DONE) → #1 corank tightening (✅DONE) → small-q tail (NEXT) →
> hK cleanup → increment 5.** State:
> - **✅ CONCERN #4 (field generalization to abstract `[Field K][Fintype K]`) — DONE this session (the analytic + bridge lift).**
>   The SESSION-1 "MAIN CARE = field/seam typing decision, lift-first" is **RESOLVED by executing the lift.** Five NEW modules
>   (all axiom-clean `[propext, Classical.choice, Quot.sound]`, zero warnings, NOT in build): **`ScratchFieldGen.lean`**
>   (V-indexed `V=Fin d→K` predicates + reductions: `isoClassK`, `coords_determineK`, `jointIsoCountK`, `ZProfileSeparatesK`,
>   `QProfileSeparatesAtBaseK`, `IsotropySeparatesAtBaseK`, D1 `qProfileSeparatesAtBaseK_of_zProfileSeparatesK`, end-to-end
>   `isotropySeparatesK_of_zProfileSeparatesK`, D2 `jointIsoCountK_eq_restricted`); **`ScratchFieldGenAdapter.lean`** (the q=p
>   adapter: `isotropySeparatesAtBase_of_K` + capstone `reachesRigidOrCameron_viaIsotropySeparatesK_wittFree` — the abstract-K
>   predicate REACHES the in-build seal capstone for q=p, via an `affineE` relabel); **`ScratchBridgeK.lean`** (soft endpoint
>   `zProfileSeparatesK_of_zSep`); **`ScratchLemmaAK.lean`** (full K-lift of `ScratchLemmaA`, ~20 lemmas, the Gauss analytic core);
>   **`ScratchBridgeAllK.lean`** (full K-lift of `ScratchBridge{A,B,C,D}` + `cone_count_zero_split`, capstone
>   **`jointIsoCountK_ne_of_chiSep_pair`** — χ(pairForm)-sep ⟹ `jointIsoCountK` differ; carries `2<Fintype.card K` + `hK`;
>   reuses the already-abstract `pairCount_ne_of_chiSep_field`). **⟹ increment 5 should now wire over abstract `K`** (the
>   coordinate seam dissolves). KEY scoping finding: the whole analytic chain is field-generic in substance; only `affineE` +
>   the scheme machinery (`affineScheme`/`similitudeGroup`) is the seam, staying at the capstone boundary. The **only** remaining
>   concern-#4 piece is the **q=pᵉ SCHEME seam** (`efield` transport, Layer D — separate; the q=p adapter is the template).
> - **✅ #1 CORANK TIGHTENING — DONE this session (4 NEW modules, 24 lemmas, all axiom-clean, NOT in build.sh).** Drops
>   `ScratchBucket.c0_le`'s `hq2 (64d²≤q)`, leaving `hq3 (q≥256)` as the CONSTANT binding threshold. The crux was the
>   genuinely-new matrix-pencil `corank(A+t₀B) ≤ rootMultiplicity` (`N=M₀·D` column-scaling + `le_rootMultiplicity_iff`).
>   **THE CAPSTONE = `ScratchTBoundCorank.c0_le_threequarters_corank`** — a **drop-in corank-tightened replacement** for
>   `ScratchC0Final.c0_le_threequarters` (same `hgood`/`hnz`/`hPu`/`hq1`/`hq3` interface + trivial `hd:1≤d`/`hq4:4≤|K|`,
>   **`hq2` GONE**), proving `NS ≤ ¾·|V|`. Modules (build order): **`ScratchPencilCorank.lean`** (matrix-pencil core
>   `finrankKer_le_rootMult`/`sum_finrankKer_le`, concentration `concentration_bound`, `pencilPoly_det_ne_zero`) →
>   **`ScratchPencilBridge.lean`** (`finrank_polarRad_eq_finrankKer`) → **`ScratchPencilRegroup.lean`** (scale-inv, ratio
>   regroup, `deg_bucket_le`, `pencilDet_ne_zero_of_good`) → **`ScratchTBoundCorank.lean`** (`normT_bucket_bound_corank`,
>   `c0_le_const`, the capstone). Verify: `lake env lean ChainDescent/ScratchTBoundCorank.lean` (after its import oleans
>   build). **Full detail = the "§13 — CORANK TIGHTENING (SCOPE)" + "BUILD PROGRESS" blocks in §13. Wiring note: increment 5
>   should call `c0_le_threequarters_corank` (not the un-tightened `c0_le_threequarters`) to inherit the dropped `hq2`.**
> - The reduction `seal ⟸ ZProfileSeparates ⟸ (separating base) ⟸ (matching: `c̄₀<1`)` is built end-to-end (over both `ZMod p`
>   AND now abstract `K`) **except increment 5 + the two open items above.** Increment-3 (`c₀≤¾`), the bridge (all wraps), and
>   the ENTIRE increment-4 cleanup (B-ii/B-iii/C-corr/C-basis/NV) are landed axiom-clean. **Read the SESSION-1 "PICK UP HERE"
>   block below** for the increment-4/5 lemma-level detail (still current); full detail = §13; strategic framing =
>   `chain-descent-remaining-work.md` §3a.1; cross-session detail = `[[project_witt_free_bridge_lead_2026-06-20]]` tail.
>
> **▶▶▶▶ CURRENT HANDOFF (2026-06-26, SESSION 1 — superseded by SESSION 2 above for the frontier; still current for the
> increment-4/5 lemma detail).** The
> reduction `seal ⟸ ZProfileSeparates ⟸ (separating base) ⟸ (matching: `c̄₀<1`)` is built end-to-end **except the
> increment-5 assembly + two decoupled items (corank tightening, field/seam typing).** Landed axiom-clean: increment 3
> (`c₀≤¾`), the observable↔count **bridge** (B1a, all wraps), and the **ENTIRE increment-4 cleanup** — input `c`, bad-anchor
> `β`, AND every bridge-input / non-vacuity gap (**B-ii, B-iii, C-corr, C-basis, NV**). **β is now UNCONDITIONAL** modulo
> family properties (nondeg `Q`, `finrank ≥ 2`, `|K| ≥ 7`); the `hgood` non-vacuity is fully discharged
> (`ScratchIncr4d.exists_hgood`, 14 axiom-clean lemmas). **THE LIVE FRONTIER IS INCREMENT 5** — wire the landed inputs into
> `ScratchMatching.exists_separating_base` (now over abstract `K`, concern #4 done). **Read the "PICK UP HERE" block below**
> (the four numbered bullets are bridge/finding/spike history); full detail = §13 ("INCREMENT 5 — WHAT'S EXPECTED" + the
> bridge/inc-3/4 blocks); strategic framing = `chain-descent-remaining-work.md` §3a.1.
>
> 1. **★ THE BRIDGE (`χ(det G₂)` observable ⟷ `Z_u(S)` counts) is ARCHITECTURALLY CLOSED; B1-deg DISSOLVED.** Chain:
>    (config-nondeg χ-separating base) →[`ScratchBridge.pairCount_ne_of_chiSep` (B1b) + `ScratchBridgeA.levelset_count_collapse`
>    (B1a core)]→ (`Z`-separating base) →[`ScratchBridgeZ.zProfileSeparates_of_zSep`]→ `ZProfileSeparates`. The degenerate-config
>    case is *dissolved* into the increment-4 matching density (`O(1/√q)` locus), not computed. Modules: `ScratchBridge`,
>    `ScratchBridgeA`, `ScratchBridgeZ` (all axiom-clean, NOT in build).
> 2. **★ B1a WRAP — COMPLETE; the bridge is now closed end-to-end (2026-06-26, `ScratchBridgeD.lean`, all axiom-clean).**
>    (i) `ScratchBridgeB.fullcount_eq_jointIsoCount_add_corr` + (ii) `ScratchBridgeC.fullcount_pair_*` (the fullcount closed
>    form `fullcount·q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀=0]−1)`) + **(iii) `chi_configDet_eq_chi_pairForm`** (`χ(D)=χ(I_w)`;
>    the `½·polar` factor and the `finBasis↔basisFun` change of basis BOTH enter as **squares**, killed by `χ` — no `finBasis`-is-
>    standard identification needed) + **final assembly `jointIsoCount_pair_closed_corr0`** (the corr=0 per-pair closed form
>    `Z_u·p³ = |V| + χ(I_u)·K·(p·[Q w₀=0]−1)`) + **the ℂ-restated B1b** (`chiSep_imp_zSep_field`/`pairCount_ne_of_chiSep_field`,
>    `CharZero` — no `R'→ℕ` descent) + **the end-to-end per-pair capstone `jointIsoCount_ne_of_chiSep_pair`** (`χ(I)`-separation
>    ⟹ `Z`-separation, the exact input to `ScratchBridgeZ.zProfileSeparates_of_zSep`). NB the model is the **prime-field** case
>    (`q = p`, field `ZMod p`); `q = pᵉ` is the field generalization (concern #4). One named fact is *carried* not re-derived:
>    `hK : gaussSum²·∑ψ(Q) ≠ 0` (Gauss-factor nonvanishing — independent of increment 4, dischargeable via `‖gaussSum‖²=q` +
>    `∑ψ(Q)=χ(disc)·gaussSumᵈ`).
> 3. **★ FINDING (do NOT lose) — the `corr` term ⟹ increment-4 predicate refinement.** The observable closed form is
>    `jointIsoCount·q³ = qᵈ − corr·q³ + χ(I_w)·K·(q·[Q w₀=0]−1)`, `corr=[both config-diffs isotropic]` (codim-2, density `O(1/q²)`).
>    B1b's clean four-value distinctness needs `corr_u=corr_v=0`, so **increment 4's good-pair predicate is `{hgood (disc≢0) ∧ hnz
>    (pairForms indep) ∧ corr=0}`** on both points (three small Schwartz–Zippel loci, all density `O(1/q)`–`O(1/q²)`, folded into the
>    matching bad set). The analytic core (`c0_le_threequarters`) is untouched.
> 4. **★ SPIKES DONE (feasibility of the rest) — all reachable, none a wall.** (a) **SEAM** (`ScratchSeam.lean`, axiom-clean):
>    `reachesRigidOrCameron_viaSchurianRank3Affine` stub compiles ⟹ the abstract residue routes to `affineScheme(Q)` modulo ONE new
>    obligation `htransport` (seal disjunction invariant along a realizing permutation), which is **mechanical** — the riskiest
>    disjunct sits on the landed `forcedNode_relabel` (full iso-invariance). **Build it as a real lemma (option b), not hidden in the
>    citation.** §11.6. (b) **char-2 + Suzuki** (§11.4/§11.5): both need a **bespoke** char-2 engine (no `χ`/Gauss; Arf + additive-trace,
>    Mathlib substrate absent) but it is one shared track (Suzuki folds into char-2), reachable, gated on that substrate, **deferred**
>    until odd-char affine-polar + seam close. The char-agnostic combinatorial layer (matching/bridge/seam/Layer B) reuses.
>
> **PICK UP HERE — FRONTIER = INCREMENT 5; the increment-4 cleanup is fully CLOSED (2026-06-26).**
>
> **Increment-4 cleanup — ALL DONE (axiom-clean, `ScratchIncr4`/`b`/`c`/`d`; NOT in build):**
> - **input `c`** — `good_anchor_fail_le_const` (`#{t:¬sep} ≤ 15/16·|V|`), via `good_anchor_fail_le` + `zeroCountShift_card_le`.
> - **bad-anchor `β`** — B-iii `pencilDetPoly_totalDegree_le` (`≤ 2d`, via `det_totalDegree_le_gen`) + B-ii `beta_count_closed`
>   (`β·|K| ≤ 2d·|V|+2·|K|`; cross-module `DecidablePred` bridged by `convert … <;> congr!`) + **C-corr** `beta_full_count_closed`
>   (full good-anchor predicate incl. `Q(t₀−u),Q(t₀−v)≠0`, which kills the bridge's `corr`: `β_full·|K| ≤ (2d+4)·|V|+2·|K| = O(d/q)`).
> - **C-basis** — `exists_orthoAnisotropic_basis` + `associated_separatingLeft_of_polarRad` (the bridge's `hv`/`hw`, from `polarRad Q=⊥`).
> - **NV** (`hgood` non-vacuity) — `ScratchIncr4d.exists_hgood` (14 lemmas): for `u≠v`, nondeg `Q`, `finrank≥2`, `|K|≥7`, a good
>   anchor `t₀₀` + `(y₀,z₀)` with `polarRad(y₀•pairForm Q(t₀₀−u)+z₀•pairForm Q(t₀₀−v))=⊥` exists. (NV-3 `polarRad_pencil_eq_bot`
>   ← NV-4 `exists_good_plane_anchor` ← NV-4a `exists_pairForm_self_sub_ne_zero` + NV-4b counting.)
>
> **INCREMENT 5 — THE HOOK-IN (what to wire, with the exact landed lemmas):**
> 1. **`c̄₀ < 1`:** `fail_count_split`/`matching_F_bound` give `F ≤ c·|V| + |V|·β_full`; plug `c = 15/16·|V|`
>    (`good_anchor_fail_le_const`) + `β_full ≤ (2d+4)·|V|/|K| + 2` (`beta_full_count_closed`) ⟹ `c̄₀ = F/|V|² ≤ 15/16 + O(d/q) < 1`
>    for `q ≳ d` (consistent with `|K|≥256`). Pure arithmetic.
> 2. **ℕ-package into `ScratchMatching.exists_separating_base`** (`m = O(d log q)`; needs a `c̄₀ᵐ`-smallness ℕ helper, the only
>    genuinely-new combinatorics). Per-pair good-anchor existence for the matching = `exists_hgood` (NV).
> 3. **`fail (u,v) (t,t₀) := ¬(bridge criterion)`** so `¬fail ⟹ jointIsoCount Q u {t,t₀} ≠ jointIsoCount Q v {t,t₀}` IS the
>    bridge capstone `ScratchBridgeD.jointIsoCount_ne_of_chiSep_pair`. Its hypotheses are now all supplied: `hcorru/hcorrv` by
>    C-corr (`corr_zero_of_anchor`, free on good anchors with `Q(t₀−u)≠0`), `hv/hw` by C-basis, config-nondeg = `I_u,I_v≠0`.
> 4. **Assemble `ZProfileSeparates`:** `zProfileSeparates_of_zSep` → Layer B (`ScratchCrux` + idx 1248
>    `reachesRigidOrCameron_viaIsotropySeparates_wittFree`) → seal.
> **★★ MAIN CARE = the field/seam typing decision (concern #4) — ✅ RESOLVED (SESSION 2): lift-first DONE.** The bridge +
> reductions + `IsotropySeparatesAtBase` are now lifted to abstract `[Field K][Fintype K]` (`ScratchFieldGen`/`ScratchBridgeK`/
> `ScratchLemmaAK`/`ScratchBridgeAllK`), and the q=p adapter (`ScratchFieldGenAdapter`) connects them to the in-build seal
> capstone. So increment 5 wires over abstract `K` using the K-named lemmas: matching `fail := ¬(bridge criterion)` →
> `ScratchBridgeAllK.jointIsoCountK_ne_of_chiSep_pair` (its `hcorru/hcorrv` from C-corr, `vb/hv/hw` from C-basis, anchor
> existence from NV `exists_hgood`) → `ScratchBridgeK.zProfileSeparatesK_of_zSep` → `ScratchFieldGen.isotropySeparatesK_of_zProfileSeparatesK`
> → `ScratchFieldGenAdapter.reachesRigidOrCameron_viaIsotropySeparatesK_wittFree` (q=p) → seal. (q=pᵉ uses the same chain + the
> `efield` scheme seam, Layer D.) The `Fin(p^d)`/`affineE` bridge of the ORIGINAL (SESSION-1) modules is no longer needed for inc-5.
>
> **DECOUPLED ITEMS:**
> - **#1 corank tightening** (`q≳d²` → `q≳const`) — **✅ DONE (SESSION 2). Capstone
>   `ScratchTBoundCorank.c0_le_threequarters_corank` (axiom-clean) = drop-in replacement for `c0_le_threequarters` with `hq2`
>   removed.** 4 modules (`ScratchPencilCorank`/`ScratchPencilBridge`/`ScratchPencilRegroup`/`ScratchTBoundCorank`). Full detail
>   = the "§13 — CORANK TIGHTENING (SCOPE) + BUILD PROGRESS" blocks in §13. **Increment 5 should call the `_corank` capstone.**
> - **Field generalization (concern #4)** — ✅ DONE this session (the analytic+bridge lift, see SESSION-2 block at top). Remaining:
>   the q=pᵉ SCHEME seam (`efield` transport, Layer D — separate; the q=p adapter `ScratchFieldGenAdapter` is the template).
>
> Then: families (d)/(e) + char-2 (Layer C), the seam build (Layer D, spiked `ScratchSeam`), and the **PORT** of all scratch
> modules into `build.sh`/`lakefile`/`PublicTheoremIndex.md`. Still carried by the bridge capstone: `hK` (Gauss-factor `≠0`,
> dischargeable via `‖gaussSum‖²=q` + `∑ψ(Q)=χ(disc)·gaussSumᵈ`). **Strategic note:** the goal is the *polynomial* seal;
> `reachesRigidOrCameron_viaSpielman` (idx 1117, axiom-clean) is the citable **sub-exp fallback** if a family walls.

> **▶▶▶ `VO⁻₄(3)` SEALED (2026-06-21, axiom-clean `[propext, Classical.choice, Quot.sound]`).**
> `ScratchBM3Glue.vo4minus_seal` proves the Witt-free capstone's conclusion for the bundled minus-form `Qbun = x₀x₁+x₂²+x₃²`
> at the size-9 base `T₉`, modulo the cited `{G3}` stack — carrying **NO `hSmallAutThin`, NO Witt**. Chain:
> `isoSep : IsotropySeparatesAtBase Qbun T₉` (B-M1 `incidence_agree_V` → restricted counts agree → bridge
> `restricted_bridge` → decided `sigF_injective`, kernel `decide` ~20s, no `native_decide`) →
> `reachesRigidOrCameron_viaIsotropySeparates_wittFree`. Four scratch modules (`ScratchLemmaA/B`, `ScratchBM3Bridge/Glue`),
> all axiom-clean (verified `lake env lean` + `lake build` oleans), **not yet ported** into `build.sh`/`lakefile` (port = the
> only remaining step for the *instance*; no new math). Module map + reusable architecture = §1.
>
> **▶▶▶ THE LIVE FRONTIER = §13 (the discharge); §11 scoping is DONE.** Generalizing from the sealed instance to the full
> schurian residue (`hSmallAutThin` for every small-Aut non-geometric schurian rank-3 family, modulo `{G3}`). **§11's
> scoping front is fully resolved:** AUDIT-S/A/W done, **Route 1 chosen** (char-sum, not Witt), **GATE passed**. The live
> work is **§13**, the discharge of the one open predicate.
>
> **▶▶ CURRENT STATE (chronological — current frontier is the PICK UP HERE block above, increment 5).** The entire generalization is
> reduced (axiom-clean, `ScratchCrux.lean`: **D1** + **D2-bridge** + `isotropySeparates_of_zProfileSeparates`) to the single
> predicate **`ZProfileSeparates Q T`** (the joint `Z(S)`-profile separates pivots at a bounded base = **D3d**). Two big
> developments since:
> - **D3d is WEIL-FREE** (the exact-vs-Weil question is RESOLVED in favour of *no Weil*). The seal's observable is the
>   **pair** joint-isotropic count `Z_u({t,t'})` (NOT the singleton — `Z_u({t})` is binary, a verified correction). Its
>   separating invariant `χ(det G₂(u;t,t₀))` is `χ` of a **quadratic** in the probe, and the relevant per-pair character sum
>   **factors through scalar values into additive Gauss sums** — proved general as `pairCharSum_factor_gen`. Probe
>   `Probe_D3dPairCount`: `c₀ ≤ 0.49 < 1` bounded, anchor existence robust (`sep@1anchor ≈ 100%`).
> - **★★★ INCREMENT 3 CLOSED (2026-06-25, all axiom-clean, NOT in build.sh).** `ScratchPairSep.lean` (24 lemmas: Gauss bridge,
>   `M(y,z)` closed form, `norm_gaussSum_sq`, `zeroCount_sq_le`, `normT_le`) + `ScratchCorank` (corank-uniform radical bound) +
>   `ScratchGoodAnchor` (good-anchor count `#degenerate ≤ d·q`, fully proven incl. the degeneracy⟺det bridge) + `ScratchBucket`/
>   `ScratchChiNorm`/`ScratchTBound` (the `|T|` bound `normT_bucket_bound`) + `ScratchCount`/`ScratchC0` (counting identity
>   `card_agree_le`) + `ScratchC0Final` (**`c0_le_threequarters`**). Net: **for a good anchor with `q≥q₀` (`d≥3`), `c₀ = NS/|V| ≤ ¾ < 1`.**
>   **EXACT NEXT STEP — increments 4–5 (matching-trick assembly):** `c0_le_threequarters` (per good anchor) + the good-anchor
>   fraction ⟹ `c̄₀ < 1` (V×V non-separating density) ⟹ `ScratchMatching.exists_separating_base` (LANDED) ⟹ separating base
>   `O(d log q)` ⟹ `ZProfileSeparates`. Full detail: §13 INCREMENT 3 PLAN (now all-DONE) + the increment-4/5 block.
>
> **▶ Witt is OFF the seal's critical path** (`relationRefinesIsotropy_similitude` discharges the bridge's easy half
> Witt-free); **Route 1 (char-sum) was chosen over Route 3 (Witt)** at the GATE (§11.1). Witt is the documented *fallback*.

---

## 1. The target, what's proved, and the reusable architecture

**Target theorem (uniform form).** Let `X = affineScheme G₀` be a primitive rank-3 schurian SRG on `V = F_q^d`, with
`G₀ ≤ ΓL(V)` a classical *similitude* group preserving a nondegenerate form and `d` bounded (small-Aut: `|Aut| = n^{Θ(d)}`
poly ⟺ `d = O(1)`). Then `X` individualizes to **discrete** at a base of size `O(d + log q)` (§11 reframe — not the naive
`d+1`), hence has bounded WL-dimension ⟹ `hSmallAutThin` for this residue. By Skresanov (route-doc §9.9.18) + the
cyclotomic citation this is node-4-for-the-seal, modulo the CFSG identification `{Cameron, Liebeck, Skresanov}`.

> **▶ SCOPE NOTE — `d = 2` is OUT OF SCOPE by construction (not a gap).** The target affine-polar families are
> `VO^ε_{2m}(q)`, so `d = 2m ≥ 4`; the per-anchor capstone `ScratchC0Final.c0_le_threequarters` carries `hq1 : 64q² ≤ |V| = qᵈ`
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

*Scratch (axiom-clean, NOT yet in build — `lake env lean` / `lake build` oleans; PORT at ASM):*
- **`ScratchLemmaA.lean` — Lemma A** ("isotropic-incidence count = explicit Gram-function on nondeg configs"): the count
  reduces to a homogeneous level-set (`reduction_to_levelset_nondeg`), a Route-B char-sum closed form (`levelset_count_eq`),
  and the config-side Gauss sum **`configGaussSum_eq_det`** (`∑ψ(s·QR ρ) = χ(s)ⁿ·χ(D)·gaussSumⁿ`; config-dependence only
  through the invariant `D`). **The generalization's A-side asset (§11.3).**
- **`ScratchLemmaB.lean` — Lemma B** ("counts recover `u`"): **`incidence_agree_V`** (fine isotropy-count antecedent ⟹
  restricted incidence counts agree, fiberwise + transport to `V`), `cone_count_zero_split`, `fullcount_agree_modulo_corr`.
- **`ScratchBM3Bridge.lean`** (Mathlib-only) — bridges the abstract count over `Fin d→ZMod p` to a kernel-fast `Nat`-predicate
  count over `Finset (Fin 81)` along the *computable* digit equiv `encV = finFunctionFinEquiv` (**`restricted_bridge`**,
  `Finset.card_nbij'`); **`sigF_injective`** = `Function.Injective sigF` by kernel `decide` (~20s, no `native_decide`).
- **`ScratchBM3Glue.lean`** — bundles `Qbun`/`Bv`/`T₉`, proves **`isoSep : IsotropySeparatesAtBase Qbun T₉`** (B-M1 → bridge
  → `sigF_injective`) and **`vo4minus_seal`** (the capstone instantiated).
- **`ScratchCrux.lean`** (NEW 2026-06-24, compiles axiom-clean) — the generalization's crux reduction: `jointIsoCount` (`Z_u(S)`),
  **`ZProfileSeparates Q T`** (the sole open predicate, general `Q`), **D1** `qProfileSeparatesAtBase_of_zProfileSeparates` (DONE),
  `isotropySeparates_of_zProfileSeparates` (end-to-end `ZProfileSeparates + nondeg ⟹ IsotropySeparatesAtBase`), and **D2 bridge**
  `jointIsoCount_eq_restricted` (`Z_u(S)` = the Lemma-A-ready restricted count). See §13.
- **`ScratchFieldGen.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, zero warnings, NOT
  in build; imports `GaussCount` only) — **CONCERN #4 (field generalization), foundational half: the V-indexed, abstract
  `[Field K][Fintype K]` lift of the analytic count chain.** Re-types the build's `ZMod p`/`Fin(p^d)` analytic layer over
  an abstract finite field `K` with `V = Fin d → K` indexed **directly** (no `affineE` digit encoding — it becomes a single
  endpoint conversion at the scheme seam). Mirrors, with `affineE` stripped (which only *simplifies* the proofs — the
  `count_transport`/`affineE.symm.injective` steps vanish): `isoClassK` + the 4 dictionary lemmas (`CascadeAffine.isoClass`),
  `polar_eq_of_subK`/`coords_determineK` (`CascadeAffine`), the count predicates `jointIsoCountK`/`ZProfileSeparatesK`/
  `QProfileSeparatesAtBaseK`/`IsotropySeparatesAtBaseK`, `extProfileK`(+`_mem`), **D1** `qProfileSeparatesAtBaseK_of_zProfileSeparatesK`,
  `isotropySeparatesK_of_qProfileSeparatesK` (= `coords_determineK` directly), the end-to-end `isotropySeparatesK_of_zProfileSeparatesK`,
  and **D2** `jointIsoCountK_eq_restricted`. **Remaining concern-#4 pieces:** lift the bridge modules (`ScratchBridge{A,B,C,D,Z}`)
  to `K` (re-target `jointIsoCountK`/`ZProfileSeparatesK`); q=pᵉ adapter = Layer D seam (`efield`). [q=p adapter DONE — see next.]
- **`ScratchFieldGenAdapter.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, zero warnings/
  sorryAx, NOT in build; imports `ScratchFieldGen` + `CascadeAffine`) — **CONCERN #4, the q=p adapter: the abstract-K chain
  REACHES the in-build capstone.** `isoClassK_eq_isoClass` (the V-indexed `isoClassK` at `K=ZMod p` = the build's `isoClass`,
  via both dictionaries) + `isoCount_transport` (the σ-profile count relabel `affineE`, via `Finset.card_nbij'`) +
  **`isotropySeparatesAtBase_of_K`** (`IsotropySeparatesAtBaseK Q (T.image affineE.symm)` ⟹ the build's `Fin(p^d)`-indexed
  `IsotropySeparatesAtBase Q T` — pure relabel) + capstone **`reachesRigidOrCameron_viaIsotropySeparatesK_wittFree`**
  (composes the adapter with `reachesRigidOrCameron_viaIsotropySeparates_wittFree`: the abstract-K predicate at a bounded base
  seals the `VO^ε` residue mod `{G3}`, no Witt/`hSmallAutThin`). **Confirms `affineE` is exactly "a single endpoint conversion
  at the scheme seam"** — analytic content over abstract `K`/`V`, only this thin relabel touches the `Fin(p^d)` scheme machinery.
- **`ScratchBridgeK.lean`** (NEW 2026-06-26, axiom-clean, zero warnings, NOT in build; imports `ScratchFieldGen`) —
  **CONCERN #4, bridge soft endpoint:** `zProfileSeparatesK_of_zSep` (a `Z`-separating base ⟹ `ZProfileSeparatesK`, pure logic).
- **`ScratchLemmaAK.lean`** (NEW 2026-06-26, axiom-clean, zero warnings, NOT in build; imports `ScratchFieldGen`) —
  **CONCERN #4, the bridge analytic core:** the full abstract-`K` lift of `ScratchLemmaA` (~20 lemmas — `levelset_count_eqK`,
  `configGaussSum_eq_detK`, `reduction_to_levelset_nondegK`, `configFormK`(+`_apply`), `s0_boundary_collapseK`, …). Mechanical
  (`GaussCount` already abstract over a finite field; `ZMod p`→`K`, `(p:R')`→`(Fintype.card K:R')`, drop `NeZero`/`ZMod.card`).
- **`ScratchBridgeAllK.lean`** (NEW 2026-06-26, axiom-clean, zero warnings, NOT in build; imports `ScratchLemmaAK` +
  `ScratchPairSep` + `ScratchBridgeD`) — **CONCERN #4, the FULL bridge over abstract `K`** (K-lift of `ScratchBridge{A,B,C,D}` +
  `cone_count_zero_split` in one module): `cone_count_zero_splitK`, `fullcount_eq_jointIsoCountK_add_corr`,
  `levelset_count_collapseK`, `fullcount_pair_{eq_levelset,closed}K`, `configPolarDet_eq_pairFormK`, `chi_configDet_eq_chi_pairFormK`,
  `chi_eq_one_or_neg_oneK`, `jointIsoCountK_pair_closed_corr0`, and the **per-pair capstone `jointIsoCountK_ne_of_chiSep_pair`**
  (χ(pairForm)-separation ⟹ `jointIsoCountK Q u {t,t₀} ≠ jointIsoCountK Q v {t,t₀}`; carries `2 < Fintype.card K` + `hK`; **reuses
  the already-abstract `pairCount_ne_of_chiSep_field`/`chiSep_imp_zSep_field` from `ScratchBridgeD`**). **⟹ Concern #4's analytic +
  bridge lift is COMPLETE** (over abstract `[Field K][Fintype K]`); only the q=pᵉ SCHEME seam (`efield` transport, Layer D) remains.
- **`ScratchPencilCorank.lean`** (NEW 2026-06-26, axiom-clean, NOT in build; imports Mathlib matrix/polynomial + `Real.Basic`)
  — **CORANK TIGHTENING, the matrix-pencil core.** `pencilPoly A B := A.map C + X•B.map C`; `pow_card_dvd_pencilDet_of_cols`
  + `exists_cols_ker` ⟹ **`finrankKer_le_rootMult`** (`corank(A+t₀B) ≤ rootMultiplicity t₀ (det)`, the genuinely-new crux);
  `pencilDet_natDegree_le` + **`sum_finrankKer_le`** (`∑corank ≤ d`); `pow_sum_mul_bound` + **`concentration_bound`**
  (`∑(√q)^{c_t} ≤ 2(√q)^{d−1}` under `1≤c_t≤d−1, ∑c_t≤d`); `pencilPoly_det_eval` + `pencilPoly_det_ne_zero` (good anchor ⟹
  pencil det ≠ 0). GOTCHAS: needs `import Mathlib.Data.Real.Basic`; use `pow_le_pow_right₀` (not `pow_le_pow_right'` — no
  `MulLeftMono ℝ`); `le_or_lt` not in scope (use `by_cases`).
- **`ScratchPencilBridge.lean`** (NEW 2026-06-26, axiom-clean, NOT in build; imports `ScratchPencilCorank` + `ScratchCorank`)
  — **CORANK, the `|radical| ↔ ker` bridge:** **`finrank_polarRad_eq_finrankKer`** (`finrank(polarRad G) =
  finrank ker((toMatrix₂ b b (polarBilin G)).mulVecLin)`, via `b.equivFun` carrying `polarRad` onto the matrix kernel).
- **`ScratchPencilRegroup.lean`** (NEW 2026-06-26, axiom-clean, NOT in build; imports `ScratchPencilBridge` +
  `ScratchGoodAnchor` + `Analysis.SpecialFunctions.Sqrt`) — **CORANK, the ratio regroup + assembly:** `ker_smul_mulVecLin`/
  `finrankKer_ratio` (scale-inv), `radicalCard_eq_pow`/`corank_ratio_eq` (`|radical| = q^{corank(ratio)}`), `sum_comp_ratio_le`/
  `fiber_fst_card_le` (fiber regroup), `sqrt_natpow`, **`deg_bucket_le`** (the corank-stratified deg bucket
  `∑_{x∈s deg} g x ≤ 2·|K|·(|V|/√|K|)`), `pencilDet_ne_zero_of_good` (the `hgood → hp` bridge).
- **`ScratchTBoundCorank.lean`** (NEW 2026-06-26, axiom-clean, NOT in build; imports `ScratchTBound` + `ScratchC0` +
  `ScratchPencilRegroup`) — **CORANK, the `|T|` bound + capstone:** `normT_bucket_bound_corank`
  (`|K|·‖T‖ ≤ |K|²·√|V| + 2·|K|·(|V|/√|K|)` — deg coeff `2` not `d`), `c0_le_const` (`c0_le` at `dR:=2` ⟹ `hq2` collapses
  to `hq3`), and **THE CAPSTONE `c0_le_threequarters_corank`** — drop-in replacement for `ScratchC0Final.c0_le_threequarters`,
  same interface (`hgood`/`hnz`/`hPu`/`hq1`/`hq3` + trivial `hd:1≤d`/`hq4:4≤|K|`), **`hq2` removed**. Verify the whole chain:
  `lake build ChainDescent.ScratchTBoundCorank`.
- **`ScratchPairSep.lean`** (NEW 2026-06-24, compiles axiom-clean, NOT in build) — the **Weil-free per-pair route** core:
  **`quadChar_addChar_sum`** (the multiplicative↔additive **Gauss bridge** `∑_y χ(y)ψ(a·y) = gaussSum·χ(a)` ∀`a`; reusable
  atom) + **`pairCharSum_factor_gen`** (the **"no Weil" core, GENERAL**: for ANY `f, g : V → K`,
  `gaussSum² · ∑_t χ(f t)χ(g t) = ∑_y ∑_z χ(y)χ(z)·(∑_t ψ(y·f t + z·g t))` — factoring never uses structure on `f,g`;
  applied with `f,g =` the pair invariants `det G₂(u;·,t₀)`, `det G₂(u';·,t₀)` (χ-of-quadratics in the probe), the inner
  sum is an additive quadratic Gauss sum ⟹ the degree-4 product is exactly evaluable, **no Weil**) + **`pairCharSum_factor`**
  (the form-specific `f=Q`, `g=Q(·−c)` singleton instance, now a one-line corollary). Needs `[CharZero R']`. **+ Increment 2
  foundation:** `pairForm` / `pairForm_apply` (the pair invariant `det G₂(u;t,t₀)` IS a quadratic form `4 Q(a)·Q − (polar Q ·
  a)²` at the shift `t−u`), `detG2_eq_pairForm`, **`pairCombine`** (the two-pivot integrand `y·det G₂(u;·) + z·det G₂(v;·)` =
  quadratic form `(y•pairForm_u + z•pairForm_v)` at shift `t−u` + linear `z·polar pairForm_v(·,u−v)` + const), and
  `sum_addChar_quadForm_translate` (Gauss translation invariance). **+ Increment 2 `M(y,z)` closed form (COMPLETE on the
  nondeg locus):** `pairSum_to_shifted` (unconditional reorganisation `M = ψ(const)·∑_s ψ(F s + linear)`),
  `sum_addChar_shifted_eval` (complete-the-square given a representing `b`), `pairSum_closed_of_repr` (chained),
  `exists_repr_of_nondeg` (`F.polarBilin` nondeg ⟹ `b` exists, via `LinearMap.BilinForm.toDual`), `pairSum_closed_of_nondeg`
  (`b` discharged from nondeg), and the capstone `pairSum_fully_closed` (`M = ψ(z·pairForm_v(u−v))·ψ(−F b)·(∏χ wᵢ)·gaussSum^d`,
  so `|M|=q^{d/2}`). **+ Degenerate locus (exact part DONE):** `pairForm_polar_anchor`/`pairForm_self_anchor` (every `pairForm Q a`
  degenerate, `a∈radical`) and `sum_addChar_radical_vanish` (degenerate diagonal-vanishing: `r∈radical`, `L r≠0` ⟹ `∑_s ψ(F s+L s)=0`).
  Open tail = increment-3 `c₀` bound. **+ Increment 3 step 3b (ℂ magnitude) DONE:** `norm_gaussSum_sq` (`‖gaussSum‖²=card`),
  `norm_addChar_eq_one` (AddChar values unit-modulus), `norm_pairSum_le` (`‖M‖≤‖gaussSum‖^d` on nondeg locus), and the
  **unified degenerate-magnitude tool** `norm_sq_sum_addChar_quadForm` (`‖∑ψ(Q)‖²=qᵈ·|radical Q|`, ANY `Q`), its **with-linear
  bound** `norm_sq_sum_addChar_quadForm_linear_le` (`‖∑ψ(Q+L)‖²≤qᵈ·|radical Q|`), and the **uniform M bound (3c)**
  `norm_sq_pairSum_le` (`‖M(y,z)‖²≤qᵈ·|radical F|`, covers nondeg+conic). Needs `import Mathlib.Analysis.Complex.Basic`.
  + the **zero-count bound (3d)** `zeroCount_sq_le` (`(z·q−qᵈ)²≤(q−1)²·qᵈ·|radical P|`) + the **`|T|` bound (3e-i)** `normT_le`
  (`q·‖T‖ ≤ ∑_{y,z} ‖χy‖‖χz‖·√(qᵈ·|radical F|)`). See §13 ("INCREMENT 3 — PLAN", steps 3b+3c+3d+3e-i DONE). Open tail =
  3e-(ii/iii): good-anchor #conic count (Schwartz-Zippel, shared w/ inc4) + `c₀` counting identity + arithmetic.
- **`ScratchMatching.lean`** (NEW 2026-06-24, compiles axiom-clean, NOT in build) — the **increment-4/5 combinatorial core**:
  **`exists_separating_base`**, the matching-trick first moment as a pure finite-counting theorem (`fail : ι → W → Prop`,
  `∀g #{w:fail g w}≤F`, `|ι|·Fᵐ<|W|ᵐ ⟹ ∃ base P:Fin m→W, ∀g ∃j ¬fail g (P j)`). Consumes the single analytic input `c̄₀<1`
  (instantiate `W=V×V`, `ι={(u,u'):u≠u'}`) ⟹ separating base of size `O(d log q)`; anchor existence dissolves (anchor = the
  other matched coordinate). See §13's "MATCHING TRICK CONFIRMED" block.
- **`ScratchIncr4.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchMatching` + `ScratchC0Final`) — **increment 4: the anchor-averaging backbone + the good-anchor fail bound (input `c`).**
  - **Backbone:** **`fail_count_split`** (`fail : A→B→Prop`, `A`=probe `t`, `B`=anchor `t₀`; per good anchor `#{a:fail a b}≤c`
    + `#bad ≤ β` ⟹ `#{(a,b):fail} ≤ c·|B| + |A|·β`, pure finite counting) + **`matching_F_bound`** (target-indexed
    `fail : ι→A→B→Prop` ⟹ `∀ g, #{(t,t₀):fail g} ≤ c·|B|+|A|·β =: F`, exactly `exists_separating_base`'s `hF`). So
    `c̄₀ = F/|V|² = c/|V| + β/|V|`.
  - **Input `c` DONE:** **`good_anchor_fail_le`** (decomposition `fail ⟹ {χ-eq} ∨ {I_u=0} ∨ {I_v=0}` + `c0_le_threequarters`
    ⟹ `#fail ≤ ¾|V| + #{I_u=0} + #{I_v=0}`) + **`zeroCountShift_card_le`** (`P≠0 ⟹ #{t:P(t−u)=0}·q ≤ |V|+(q−1)|V|/√q`,
    extracted from the `z_u` block of `c0_le_threequarters`) ⟹ capstone **`good_anchor_fail_le_const`**: a good anchor
    (`hnz ∧ hgood ∧ hPu ∧ hPv`, `q≥256`) has **`#{t : ¬sep} ≤ 15/16·|V|`** (`z/|V| ≤ 1/256+1/16 = 17/256 < 3/32` twice ⟹
    `¾+3/16=15/16`). So `c/|V| ≤ 15/16 < 1` — the good-anchor side of `c̄₀<1` is closed.
  - **Increment-4 `β` (bad-anchor count) is DONE** in `ScratchIncr4b`+`ScratchIncr4c` (`badHgood_count_le`, `O(d/q)`).
    Remaining = the increment-5 ℕ-packaging/matching assembly (modulo non-vacuity).
- **`ScratchIncr4b.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchIncr4` + `ScratchGoodAnchor`) — **increment 4: the bad-anchor count `β` (Schwartz–Zippel in `t₀`).**
  **★ Structural reduction (key):** since `pairForm Q (t₀−v)` is ALWAYS degenerate (`pairForm_polar_anchor`: `t₀−v ∈`
  its radical), a nondeg pencil member needs a genuine `(y,z)`-combination ⟹ **`hgood` alone forces `hnz ∧ hPu ∧ hPv`**
  (a zero/proportional member would make the whole pencil a multiple of one degenerate form). So the bad set collapses
  (mod `t₀∈{u,v}`) to `{¬hgood} ∪ {Q(t₀−u)=0} ∪ {Q(t₀−v)=0}`. The two quadric loci are immediate from
  `zeroCountShift_card_le` (applied to `Q`); the meaty piece is `{¬hgood} = {t₀ : pencilDisc(·,·;t₀) ≡ 0}`.
  **Landed (all 7 axiom-clean):** (a) the Schwartz–Zippel-in-`Fin d` engine **`mvPoly_zeros_count_le_dim`** (`p≠0 ⟹
  #{f:Fin d→K | eval f p=0}·|K| ≤ totalDegree·|K^d|`, zero-density `≤ totalDegree/q`); (b) the **reduction
  `hgood ⟹ hnz∧hPu∧hPv`** — helpers `mem_polarRad_smul_pairForm` + `polarRad_smul_pairForm_ne_bot` feed
  `hPu_of_hgood`/`hPv_of_hgood`/`hnz_of_hgood`; (c) packaged **`bad_anchor_card_le_hgood`: `β ≤ #{¬hgood} + 2`**;
  (d) the **rigorous SZ reduction `bad_anchor_count_le_of_poly`** — given a nonzero `P : MvPolynomial (Fin d) K` with
  `(¬hgood t₀ → eval (b.equivFun t₀) P = 0)`, `#{¬hgood}·|K| ≤ P.totalDegree·|V|` (coordinatize `V≅K^d` via `b.equivFun`
  + the engine); (e) **`notHgood_eval_zero_of_repr`** — discharges that `hrep` whenever `P` *represents* the pencil
  determinant at a fixed witness (`eval (coords t₀) P = det(toMatrix₂ b b (polarBilin (y₀•pairForm_u+z₀•pairForm_v)))`),
  via `polarRad_ne_bot_iff_det_eq_zero`.
- **`ScratchIncr4c.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchIncr4b`) — **the representing polynomial `P` is CONSTRUCTED — β's heavy coordinatization is DONE (12 lemmas).**
  Coordinatization workhorse `coordPoly`/`coordPoly_eval_linFunc` (a linear functional `f` ↦ `∑ₖ C(f bₖ)·Xₖ`, evaluating
  to `f t₀`); the quadratic `Q(t₀)` via the diagonal double-sum `polar_t0_t0_sum` + `gramQuadPoly_eval`; the affine
  `LPoly`/`QPoly` (`polar Q w (t₀−c)`, `Q(t₀−c)`); the general `polar_pairForm_apply`; the Gram-entry `entryPoly`/
  `entryPoly_eval`; **`pencilDetPoly := det(Matrix.of (C y₀·entryPoly_u + C z₀·entryPoly_v))`** with
  **`pencilDetPoly_eval`** (represents the pencil det, via `RingHom.map_det` + per-entry) and **`pencilDetPoly_ne_zero`**
  (nonzero from a good-anchor witness). Capstone **`badHgood_count_le`: `#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V|`**.
  **B-iii (2026-06-26):** the explicit degree cap **`pencilDetPoly_totalDegree_le : totalDegree ≤ 2·d`** via the
  bounded-degree generalization **`det_totalDegree_le_gen`** (`totalDegree ≤ D` entries ⟹ `det ≤ D·d`) + per-layer caps
  (`coordPoly`/`LPoly` `≤ 1`; `gramQuadPoly`/`QPoly`/`entryPoly` `≤ 2`). **B-ii (2026-06-26):** the explicit composition
  **`beta_count_closed`: `β·|K| ≤ 2d·|V| + 2·|K| = O(d/q)`** (combines `badHgood_count_le` + `pencilDetPoly_totalDegree_le`
  + `bad_anchor_card_le_hgood`; cross-module `DecidablePred` mismatch bridged by `convert … <;> congr!`). **So β is CLOSED
  to an explicit `O(d/q)` bound modulo ONLY (i) non-vacuity `hgood`** (∃ good anchor for `u≠v` = distinct radicals — item
  **NV**, carried as the `t₀₀` hypothesis). Items (ii) Nat-composition + (iii) `totalDegree ≤ 2d` are DONE (B-ii/B-iii).
  **C-corr (2026-06-26):** `corr_zero_of_anchor` (good anchor `Q(t₀−u)≠0` kills the bridge's `corr` ∀`t`) + `QPoly_ne_zero`
  + `qZero_count_le` (`#{Q(t₀−c)=0}·|K| ≤ 2·|V|`) + capstone **`beta_full_count_closed`** (FULL good-anchor predicate incl.
  `Q(t₀−u),Q(t₀−v)≠0`: `β_full·|K| ≤ (2d+4)·|V| + 2·|K|`). **C-basis (2026-06-26):** `exists_orthoAnisotropic_basis`
  (nondeg `Q` ⟹ ortho-anisotropic basis = the bridge's `vb`/`hv`/`hw`, via Mathlib `exists_orthogonal_basis` +
  `not_isOrtho_basis_self_of_separatingLeft`) + the project-native bridge `associated_separatingLeft_of_polarRad`
  (`polarRad Q = ⊥ ⟹ (associated Q).SeparatingLeft`). **26 axiom-clean lemmas total.** Both bridge-input gaps (C-corr,
  C-basis) CLOSED; lone deep remaining inc-4 item = **NV** (algebraic heart now also done — see `ScratchIncr4d` below).
- **`ScratchIncr4d.lean`** (NEW 2026-06-26, **14 axiom-clean lemmas**, NOT in build; imports `ScratchIncr4c`) — **NV
  (non-vacuity of `hgood`) COMPLETE.** Discharges `∃ y z, polarRad(y•pairForm Q(t₀₀−u)+z•pairForm Q(t₀₀−v))=⊥`.
  *Algebraic heart:* `polar_pencil_apply` (NV-1) + `pencil_radical_key` + `polarRad_pencil_subset_span` (NV-2) +
  **`polarRad_pencil_eq_bot`** (NV-3: nondeg `Q`, `y,z≠0`, `c≠0`, `pairForm Q a b≠0` ⟹ member nondeg, via `2×2`
  `det=4yz·pairForm`). *Geometry+counting:* `pairForm_self_sub` (the degree-2 formula `pairForm Q a (a−w)=4QaQw−polar(a,w)²`) +
  `exists_ne_zero_polar_eq_zero` (rank-nullity) + **`exists_pairForm_self_sub_ne_zero`** (NV-4a: ≢0, the rank-≤1 contradiction)
  + `exists_anisotropic`/`gramQuadPoly_ne_zero`/`planeDiscPoly`(+`_eval`/`_totalDegree_le`/`_ne_zero`) + **`exists_good_plane_anchor`**
  (NV-4: ∃ `a` with `Qa,Q(a−w),pairForm Q a (a−w) ≠ 0`, union bound over 3 quadrics, `|K|≥7`). *Capstone:* **`exists_hgood`**
  (NV-5 + assembly: `t₀₀=a+u`, `(y,z)=(1,±1)`). ⟹ inc-4 cleanup CLOSED.
- **`ScratchCorank.lean`** (NEW 2026-06-25, compiles axiom-clean, NOT in build) — the **corank ≥ 2 enabler** for 3e-ii:
  **`radical_card_mul_card_le`** (`F ≠ 0 ⟹ |radical F| · |K| ≤ |V|`, i.e. `|radical| ≤ q^{d−1}` UNIFORMLY over all coranks —
  the degenerate bucket of `normT_le`'s RHS needs no per-corank stratification), built from `polarRad` (the polar-radical as a
  submodule), `polarRad_card_filter` (filter-card = `Nat.card` of the submodule, instance-free via `Nat.card`/`Set.ncard`), and
  `polarRad_ne_top_of_ne_zero` (`F ≠ 0 ⟹ radical proper`, char ≠ 2). See §13 "CORANK ≥ 2 HANDLED".
- **`ScratchGoodAnchor.lean`** (NEW 2026-06-25, compiles axiom-clean, NOT in build; imports `ScratchCorank` so needs
  `lake build ChainDescent.ScratchCorank` first) — the **good-anchor count, FULLY PROVEN**: capstone **`degenerate_count_le`**
  (`good anchor ⟹ #{(y,z): polarRad (y•P+z•R) ≠ ⊥} ≤ d·|K|`), from analytic cores `mvPoly_zeros_count_le` (Schwartz–Zippel) +
  `det_totalDegree_le` (degree cap) and the concrete-pencil bridge (`pencilDisc`/`_eval`/`_totalDegree_le`,
  `polarRad_ne_bot_iff_det_eq_zero`, `toMatrix₂_polarBilin_pencil`, `polar_pencil`).
- **`ScratchBucket.lean`** / **`ScratchChiNorm.lean`** / **`ScratchTBound.lean`** (NEW 2026-06-25, axiom-clean, NOT in build) —
  the **3e-ii `|T|`-bound assembly**. `ScratchBucket`: `sum_two_bucket_le` (abstract nondeg/deg split `∑g ≤ Ca·Ma+Cb·Mb`) +
  `sqrt_mul_le_div` (`r·k≤V ⟹ √(V·r)≤V/√k`, deg magnitude). `ScratchChiNorm`: `norm_quadraticChar` (`‖χy‖ = if y=0 then 0 else 1`).
  `ScratchTBound`: **`normT_bucket_bound`** = `|K|·‖T‖ ≤ |K|²·√|V| + (d·|K|)·(|V|/√|K|)`, wiring `normT_le` + the two buckets.
  (`ScratchTBound` imports the four scratch modules → build their oleans first.)
- **`ScratchCount.lean`** / **`ScratchC0.lean`** (NEW 2026-06-25, axiom-clean, NOT in build) — the **3e-iii counting identity**.
  `ScratchCount`: `int_char_pointwise` (per-element χ-value ineq, no axioms) + **`counting_identity`** (`2·NS ≤ 2·z_u + n + T_ℤ`,
  generic `a,b:V→K`). `ScratchC0`: `charSum_int_le_norm` (`T_ℤ ≤ ‖T_ℂ‖`) + **`card_agree_le`** (`2·NS ≤ 2·z_u + n + ‖T_ℂ‖` over ℝ).
- **`ScratchC0Final.lean`** (NEW 2026-06-25, axiom-clean, NOT in build; imports `ScratchTBound`+`ScratchC0` → build their oleans) —
  **INCREMENT 3 CAPSTONE `c0_le_threequarters`**: per good anchor + threshold `q≥q₀`, `NS ≤ ¾·|V|` (`c₀ ≤ ¾ < 1`). Plus
  `ScratchBucket.c0_le` (the pure-real final arithmetic). Assembles `card_agree_le`+`normT_bucket_bound`+`zeroCount_sq_le`+radical bound.
  NB `hq1 : 64q²≤|V|` ⟺ `d ≥ 3`, the families' own range (`VO^ε_{2m}`, `d=2m≥4`) — see §1 SCOPE NOTE; `d=2` is out of scope.
- **`ScratchBridge.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build) — the
  **observable↔count bridge, B1b**: `chiSep_imp_zSep` (from the `|S|=2` even-`d` closed form `Z_w = qᵈ + χ(det G₂_w)·K·(q[c=0]−1)`,
  `K ≠ 0`, the four `(χ,[c=0])` values are distinct for `q>2` ⟹ `χ(det G₂)_u ≠ χ(det G₂)_v ⟹ Z_u({t,t₀}) ≠ Z_v({t,t₀})`) +
  **`pairCount_ne_of_chiSep`** (the same in joint-count language: closed form for each point + χ-separation ⟹ `Z_u ≠ Z_v`). Feeds
  the bridge capstone `ScratchBridgeZ.zProfileSeparates_of_zSep`. **B1a (analytic core + all wraps) now COMPLETE** —
  `ScratchBridgeA`–`D`; the ℤ-stated `chiSep_imp_zSep`/`pairCount_ne_of_chiSep` here are superseded by the ℂ-restated
  `ScratchBridgeD` versions used in the assembly (B1-deg **dissolved** — see §13 BRIDGE block).
- **`ScratchBridgeZ.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchCrux` → build its olean first) — the **bridge capstone** `zProfileSeparates_of_zSep`: any `Z`-separating base
  (`∀ u≠u', ∃ S⊆T, jointIsoCount Q u S ≠ jointIsoCount Q u' S`) discharges `ScratchCrux.ZProfileSeparates Q T` outright. With
  `pairCount_ne_of_chiSep` + `levelset_count_collapse` (turning a config-nondeg χ-separating pair into a `Z`-separating sub-frame),
  this **architecturally closes the bridge** and **dissolves B1-deg** (the config-degenerate locus, density `O(1/√q)`, folds into
  the increment-4 matching density — no degenerate-config `Z` value needed). See §13 BRIDGE block.
- **`ScratchBridgeB.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchCrux` + `ScratchLemmaB`) — **B1a wrap (i)** `fullcount_eq_jointIsoCount_add_corr`: the Lemma-A fullcount =
  `jointIsoCount Q u S + [∀t∈S, Q(t̄−ū)=0]` (`cone_count_zero_split` ∘ `jointIsoCount_eq_restricted`). Connects the bridge
  observable `jointIsoCount` to `levelset_count_collapse`'s fullcount.
- **`ScratchBridgeC.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchBridgeA` + `ScratchBridgeB`) — **B1a wrap (ii):** `fullcount_pair_eq_levelset` (ii-a, `Finset {t,t₀}`↔`Fin 2` config
  indexing + `reduction_to_levelset_nondeg`) + **`fullcount_pair_closed`** (ii-b, the **fullcount closed form**
  `fullcount·q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀=0]−1)`, config-nondeg + even `d`). NB wrap (ii) surfaced the **`corr`
  term** ⟹ increment-4 good-pair predicate gains `corr=0` (§13 BRIDGE net verdict "FINDING").
- **`ScratchBridgeD.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchBridgeC` + `ScratchPairSep`) — **B1a wrap (iii) + the final ℂ assembly, closing the bridge end-to-end.**
  `configPolarDet_eq_pairForm` (2×2 polar Gram det = `pairForm`) → **`chi_configDet_eq_chi_pairForm`** (wrap (iii): `χ(D)=χ(I_w)`;
  the `½·polar` factor + the `finBasis↔basisFun` change of basis enter as squares killed by `χ`, via reindex + `det_submatrix_equiv_self`
  + `toMatrix_mul_basis_toMatrix` — no standard-basis identification) → **`jointIsoCount_pair_closed_corr0`** (assembly: the corr=0
  per-pair closed form) ; `chi_eq_one_or_neg_one` + **`chiSep_imp_zSep_field`/`pairCount_ne_of_chiSep_field`** (ℂ-restated B1b,
  `CharZero`, no `R'→ℕ` descent) → end-to-end capstone **`jointIsoCount_ne_of_chiSep_pair`** (`χ(I)`-sep ⟹ `Z`-sep, feeds
  `ScratchBridgeZ.zProfileSeparates_of_zSep`). Carries `hK : gaussSum²·∑ψ(Q)≠0` (independent Gauss nonvanishing). Prime-field model.
- **`ScratchBridgeA.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `ScratchLemmaA` → build its olean first) — the **B1a analytic core** `levelset_count_collapse`: for config size `m=2`, **even `d`**,
  nondeg config Gram, `(level-set count at c)·q³ = |V| + χ(D)·(gaussSum²·∑ₓψ(Qx))·(q·[c=0]−1)`. The `s`-sum collapse from
  `levelset_count_eq` (the "big but mechanical" `D3a` at `|S|=2` the `VO⁻₄(3)` instance bypassed via `decide`); config-dependence
  enters only through `χ(D) = χ(det G₂)`, the bridge observable. Feeds `ScratchBridge.chiSep_imp_zSep`. (Consumed by wrap (ii)
  in `ScratchBridgeC`; B1a is now COMPLETE — wrap (iii) + assembly are in `ScratchBridgeD`, see §13 BRIDGE net verdict.)
- **`ScratchSeam.lean`** (NEW 2026-06-26, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build; imports
  `CascadeAffine`) — **THE SEAM SPIKE** `reachesRigidOrCameron_viaSchurianRank3Affine` (+ `SchemeRealizes`, `SealDisj`): the
  abstract residue `S` reaches the seal disjunction given (C) the cited classification (`Cameron ∨ ≅ affineScheme(Q)` with
  `IsotropySeparatesAtBase Q T`) + (T) the transport `htransport`. Stub COMPILES ⟹ seam closes modulo the one mechanical
  obligation `htransport` (seal disjunction invariant along a realizing permutation; build via landed `forcedNode_relabel`,
  option b). See §11.6 SEAM SPIKE box. Forms-graph case discharged by `…viaIsotropySeparates_wittFree`.
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
  > `ZMod p`, zero work.** The forms layer (`CascadeAffine §AffineScheme/§OrthogonalForm`, `ScratchLemmaA/B`) uses `ZMod p`
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
> the **char-agnostic combinatorial layer** (matching `ScratchMatching`, `ZProfileSeparates`/`ScratchBridgeZ`, the seam
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
> char-agnostically** (the matching trick `exists_separating_base`, the `ZProfileSeparates` reduction `ScratchBridgeZ`, the seam
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

## 13. Discharge scoping — `QProfileSeparatesAtBase` for general `Q` (2026-06-24)

> **What this is.** The scoped plan for the one open research lemma (the GATE crux). Target chosen, proof chain laid out
> against the landed scaffolding (§12), the open core isolated, the build increments ordered. This is the active work.

> **§13 STATUS (read first; the blocks below are the chronological detail).**
> - **▶ SESSION-2 (2026-06-26): CONCERN #4 (field-gen) DONE + CORANK TIGHTENING SCOPED — see the top-of-doc SESSION-2
>   handoff + the "CORANK TIGHTENING (SCOPE)" block immediately below.** Working order: #4 (done) → corank (scoped, building) →
>   small-q tail → hK cleanup → increment 5. Increment 5 now wires over **abstract `K`** (concern #4's 5 new modules).
> - **▶▶▶▶ CURRENT FRONTIER = INCREMENT 5 (see the top-of-doc "CURRENT HANDOFF (2026-06-26)" PICK UP HERE block).** All of:
>   increment 3 (`c₀≤¾`), the observable↔count **bridge** (B1a, all wraps — `ScratchBridge`/`A`/`B`/`C`/`D`/`Z`), increment-4
>   **input `c`** (`good_anchor_fail_le_const`, `ScratchIncr4`), and increment-4 **bad-anchor `β`** (`badHgood_count_le`,
>   `ScratchIncr4b`/`ScratchIncr4c` — repr polynomial constructed) are LANDED axiom-clean. **Increment 5** = wire `c̄₀<1` into
>   `exists_separating_base` + the bridge (§"INCREMENT 5 — WHAT'S EXPECTED" below). The dated bullets below are CHRONOLOGICAL
>   HISTORY (increment 3, the bridge blocks, the increment-4 blocks — all now done; trust this bullet + the top-of-doc PICK UP HERE).
> - **(HISTORY) 2026-06-25 — INCREMENT 3 CLOSED (all axiom-clean, full `lake build` green, NOT in build.sh).**
>   The pair route's per-anchor `c₀ ≤ ¾ < 1` bound is COMPLETE: capstone **`ScratchC0Final.c0_le_threequarters`** (good anchor
>   `hgood`/`hnz`/`hPu` + `q≥q₀` [`64q²≤|V|`⟺`d≥3`, `64d²≤q`, `256≤q`] ⟹ `NS = #{t:χ(I_u)=χ(I_v)} ≤ ¾·|V|`). Built across 8 new
>   scratch modules on top of `ScratchPairSep` (24 lemmas): `ScratchCorank` (`radical_card_mul_card_le`), `ScratchGoodAnchor`
>   (`degenerate_count_le`, incl. degeneracy⟺det bridge), `ScratchBucket`/`ScratchChiNorm`/`ScratchTBound` (`normT_bucket_bound`),
>   `ScratchCount`/`ScratchC0` (`card_agree_le`), `ScratchC0Final` (`c0_le` + capstone). Reduction backbone `ZProfileSeparates →
>   IsotropySeparatesAtBase → seal` LANDED (`ScratchCrux` + idx 1248). **REMAINING = increments 4–5 (matching trick) + the
>   layered remainder:** (4) good-anchor density `c̄₀<1`; (5) `exists_separating_base` (LANDED) ⟹ separating base `O(d log q)`;
>   observable↔count bridge ⟹ `ZProfileSeparates`; then families (d–f)/char-2 + the structural seam + port. PICK-UP detail: the
>   "▶▶ STATUS (2026-06-25)" note in the INCREMENT 4 block below + `chain-descent-remaining-work.md` §3a.1 (full layered map).
>   The bullets below this one are CHRONOLOGICAL HISTORY (steps now done — trust this bullet + the INCREMENT 3 PLAN block, all-DONE).
> - **★ OBSERVABLE↔COUNT BRIDGE ARCHITECTURALLY CLOSED; B1-deg DISSOLVED (2026-06-26, `ScratchBridge`/`ScratchBridgeA`/
>   `ScratchBridgeZ`, all axiom-clean).** End-to-end chain: (config-nondeg χ-separating base, increment 4/5)
>   →[`pairCount_ne_of_chiSep` (**B1b**) + `levelset_count_collapse` (**B1a core**, the `s`-sum collapse
>   `Z_w·q³ = qᵈ + χ(det G₂_w)·K·(q[c=0]−1)`, `K≠0`)]→ (`Z`-separating base) →[`zProfileSeparates_of_zSep`]→ `ZProfileSeparates`.
>   Three of the four pieces are LANDED axiom-clean (`pairCount_ne_of_chiSep`, `levelset_count_collapse`,
>   `zProfileSeparates_of_zSep`). **B1-deg (degenerate config `χ=0`) is DISSOLVED** — the config-degenerate locus has density
>   `O(1/√q)` and folds into the increment-4 matching's bad set (no degenerate-config `Z` value needed). **ONLY remaining bridge
>   work = B1a's mechanical wrapping** (cone↔levelset + `w=0` + `D↔pairForm` + `R'→ℕ`, all landed-tool). Detail: "▶▶ OBSERVABLE↔COUNT
>   BRIDGE" block in the INCREMENT 4 region below. **Not a hidden wall** — contained Gauss assembly, no Weil.
> - **LANDED** (`ChainDescent/ScratchCrux.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, compiles via
>   `lake env lean`, NOT yet in `build.sh`): **D1** `qProfileSeparatesAtBase_of_zProfileSeparates`, **D2-bridge**
>   `jointIsoCount_eq_restricted`, and the end-to-end `isotropySeparates_of_zProfileSeparates`. Reuses landed
>   `coords_determine`, `isotropySeparates_of_qProfileSeparates`, `count_transport`, `isoClass_ne_two_iff`.
> - **⟹ the entire generalization = one open predicate `ZProfileSeparates Q T`** (joint `Z(S)`-profile injectivity, general `Q`).
> - **(D-step taxonomy — the SINGLETON-era ordering, now SUPERSEDED by the pair route below; kept only as a map of the
>   pieces.)** **D2-analytic/D3a** (closed form `Z=F(χ det G,[c_lev=0])` — Lemma A) → **D3b** (degenerate configs) → **D3c**
>   (`Z=Z ⟹ χ det G agree`) → **★D3d** (the research core) → **D3e** (construct `T`). **Under the pair route, D3a is OFF the
>   critical path** (only the `|S|=2` invariant is used).
> - **★ LEAN INCREMENT 1 LANDED** (`ScratchPairSep.lean`, axiom-clean): the **Gauss bridge** `quadChar_addChar_sum` + the
>   **"no Weil" core** `pairCharSum_factor_gen` (general `f,g`; `pairCharSum_factor` = its singleton corollary).
> - **★★ CORRECTION (the singleton route is FLAWED; see the §13 CORRECTION block).** The observable is the PAIR count, not
>   `χ(Q)`: `Z_u({t})` is BINARY (`Probe_D3cObservable` — only `[Q(u−t)=0]`), so `χ(Q(u−t))` is unobservable and the exact-`S`
>   bound is for the wrong object. The square class lives at `|S|=2` (`Z_u({t,t'})` recovers `χ(det G₂)`). **Fix:** use the
>   observable pair invariant `χ(det G₂(u;t,t₀))` (a quadratic in `t`) — same factoring shape, bridge transfers,
>   `pairCharSum_factor` needs generalizing to two quadratic polynomials.
> - **★ PAIR ROUTE CONFIRMED + GENERALIZED FACTORING LANDED (2026-06-24).** `Probe_D3dPairCount`: `c_max ∈ [0.44,0.49]<½`,
>   `sep@1anchor≈100%` ⟹ anchor existence + averaging viable; `|T|≈0.8n` (main term, exact, no Weil). **`pairCharSum_factor_gen`**
>   (axiom-clean) = the factoring for any `f,g:V→K`, applied to the pair invariants ⟹ "no Weil" for the real observable is a
>   theorem-shaped reduction. **INCREMENT 2 FOUNDATION LANDED** (`ScratchPairSep`, axiom-clean): `pairForm`/`pairForm_apply`/
>   `detG2_eq_pairForm` (pair invariant = quadratic form at a shift), **`pairCombine`** (two-pivot integrand = form + linear +
>   const), `sum_addChar_quadForm_translate`. **D3d STILL OPEN, remaining:** finish `M(y,z)` closed form (complete-the-square
>   via `sum_addChar_quadForm_linear` at `r=1` [needs `F=y•pairForm_u+z•pairForm_v` nondeg + solve `b`] + `sum_addChar_quadForm`
>   + degenerate locus); then (3) `c₀<1` bound (one ℂ-magnitude step); (4) anchor existence; (5) averaging ⟹ `ZProfileSeparates`.
> - **Evidence base (all green, regression assets in `GraphCanonizationProject.Tests/A2MonovariantProbe.cs`):**
>   `Probe_CoarseInvariantInjectivity` (SPIKE-K.1, used the pair count `Z_u({t,t'})`), `Probe_IncidenceVsCounts` (.2),
>   `Probe_FrameThenProbes` (GATE), `Probe_D3dChiInvariant` + `Probe_D3dStructuredBase` (D3d), `Probe_D3dHigherD` +
>   `Probe_D3dCollisionDecay` (R3), `Probe_D3dExactVsWeil` (singleton exact-vs-Weil), **`Probe_D3cObservable`** (proved
>   `Z_u({t})` BINARY, `Z_u({t,t'})` recovers `χ(det G₂)` — the singleton→pair correction), **`Probe_D3dPairCount`** (the
>   real pair observable: `c₀ ≤ 0.49 < 1`, `sep@1anchor ≈ 100%`). Findings: bounded base survives `d=6`; the **pair**
>   observable separates with `c₀<1` bounded + anchor existence; **D3d is Weil-free**; base `O(d log q)`.

### §13 — CORANK TIGHTENING (SCOPE) — the `q≳d² → q≳const` fix (SESSION 2, 2026-06-26)

**Goal.** Remove `ScratchBucket.c0_le`'s hypothesis `hq2 : 64·dR² ≤ q` (the `q≳d²` threshold), leaving the existing
`hq3 : 256 ≤ q` (a CONSTANT) as the binding one. This determines what the final theorem proves on the families: for `VO⁻₄(q)`
(d=4) it currently needs `q ≥ 1024`; the fix drops that to `q ≥ 256`, shrinking the sub-threshold tail (handled by the
"small-q tail" item next) from `{q<1024}` to `{q<256}`.

**Where the threshold enters (exactly one place).** `c0_le` (`ScratchBucket.lean`) step `hB`/`h8d` needs the deg-bucket term
`dR·n/√q ≤ n/8`, i.e. `8·dR ≤ √q`, i.e. `64dR²≤q`. That term comes from `normT_bucket_bound` (`ScratchTBound.lean`): the
degenerate bucket is bounded `(d·|K|)·(|V|/√|K|)` = (count `d·q` via `degenerate_count_le`) × (uniform magnitude `q^{d−1/2}`
via `radical_card_mul_card_le`, i.e. charging EVERY degenerate member the worst corank `d−1`).

**No shortcut (verified this session).** The incidence count `∑_{(y,z)}|radical F_{y,z}|` and a Cauchy–Schwarz route BOTH
reduce back to `∑_λ corank(B'−λA')` — the same pencil-corank sum. And a uniform `corank ≤ const` is FALSE: for two corank-1
forms the pencil reaches **corank `d−2` at a single ratio** (`A'=diag(1,…,1,0)`, `B'=diag(0,1,…,1)`, at `y+z=0`; there
`∑corank = d−2 ≤ d = deg`). So the load-bearing fact is genuinely `corank ≤ rootMultiplicity`, summed — real matrix-pencil math.

**The route (all Mathlib tools confirmed present).**
1. `p(X) := det(A' + X·B')` over `K[X]` (`A',B'` = the `d×d` Gram matrices `(pairForm_u).polarBilin`, `(pairForm_v).polarBilin`
   in a basis). For SUPPORT ratios `(y,z)`, `y,z≠0`, the member `∝ A'+X·B'` at `X=z/y≠0`; the `q−1` scalar multiples of a ratio
   share one radical. `p ≠ 0` on a good anchor; `natDegree p ≤ d`.
2. **`corank(A'+t₀B') ≤ p.rootMultiplicity t₀`** (the genuinely-NEW core — build in `ScratchPencilCorank.lean`):
   let `c = finrank ker(A'+t₀B')`; take an invertible `Q : Matrix (Fin d)(Fin d) K` whose columns on a size-`c` index set `S`
   span `ker(A'+t₀B')` (basis extension of the kernel). Then `N(X) := (A'.map C + X•B'.map C) * Q.map C` has, for `j∈S`,
   column `j = (X − C t₀) • (const vector C(B'·qⱼ))` — because `(A'+t₀B')·qⱼ = 0 ⟹ A'qⱼ = −t₀·B'qⱼ`. So **`N = M₀ · D`** with
   `D = Matrix.diagonal (fun i => if i∈S then (X − C t₀) else 1)` (`det D = (X−C t₀)^c`) and `M₀` = `N` with the `S`-columns
   replaced by the constants. `det N = det M₀ · (X−C t₀)^c`, and `det N = p · C(det Q)` with `C(det Q)` a unit in `K[X]`
   (`det Q ∈ Kˣ`) ⟹ `(X − C t₀)^c ∣ p` ⟹ (by **`Polynomial.le_rootMultiplicity_iff`**, needs `p≠0`) `c ≤ rootMultiplicity`.
   *Tools:* `Matrix.det_mul`, `Matrix.det_diagonal`, `det_mul_column`-free (use `N=M₀·D`), `LinearIndependent.extend` / `Basis`
   for `Q`, `Polynomial.le_rootMultiplicity_iff`/`pow_rootMultiplicity_dvd` (`Algebra/Polynomial/Div.lean`). Map/eval:
   `(A'+t₀B') = eval-at-t₀ of (A'.map C + X•B'.map C)` via `RingHom.map_det` / `Matrix.det` over `K[X]`.
3. **`∑_{roots} corank ≤ d`:** `∑_{roots} rootMultiplicity = Multiset.card p.roots ≤ natDegree p ≤ d` (**`Polynomial.card_roots'`**).
4. **Arithmetic + integration:** with the per-ratio corank `c_r` and `∑c_r ≤ d`, the deg-bucket sum `∑_r (q−1)·√(qᵈ·q^{c_r}) =
   (q−1)·q^{d/2}·∑_r q^{c_r/2}`, and `∑_r q^{c_r/2} ≤ C·q^{(d−1)/2}` (concentration: under `∑c_r ≤ d` the max is one big term
   `q^{(d−1)/2}` + tail). ⟹ deg term `≈ n/√q` (constant `C`, NO `d` factor). Replace the deg bucket in `normT_bucket_bound`
   accordingly; then a new `c0_le` variant with `hT : T ≤ q·√n + C·n/√q` (no `dR`) ⟹ drop `hq2`. **⚠ The single high-corank
   member** (`corank` up to `d−1`) is exactly the `q^{(d−1)/2}` term — handled by the concentration bound, NOT a special case.

**Reusable (built):** `ScratchPairSep.norm_sq_pairSum_le` (`‖M(y,z)‖²≤|V|·|radical(y•pairForm_u+z•pairForm_v)|`),
`ScratchGoodAnchor.degenerate_count_le` (≤`d·|K|`) + `pencilDisc_totalDegree_le` (≤`d`), `ScratchCorank.radical_card_mul_card_le`
(corank ≤ `d−1`, the uniform fallback). **New:** `ScratchPencilCorank.lean` (step 2) + the arithmetic/integration in
`ScratchTBound`/`ScratchBucket`/`ScratchC0Final`. **Size ≈ 150–250 lines**, bulk in step 2 (the `Q`-from-basis-extension and
the `K[X]`-matrix eval/column plumbing). NB the per-pivot pairForm has corank EXACTLY 1 when `Q(t₀−w)≠0` (good anchor): radical
`= ⟨t₀−w⟩` (`pairForm_polar_anchor` + nondeg) — so `A'`,`B'` are rank `d−1` (used implicitly; the route does not actually need it,
the general `corank ≤ mult` suffices).

**▶ BUILD PROGRESS (SESSION 2 cont., 2026-06-26) — STEP 2 + STEP 3 DONE (axiom-clean, NOT in build).**
`ScratchPencilCorank.lean` (6 lemmas, all `[propext, Classical.choice, Quot.sound]`, `lake env lean` green):
- `pencilPoly A B := A.map C + X • B.map C : Matrix _ _ K[X]`; `pencilPoly_mul_map` (`pencilPoly A B * Q.map C =
  pencilPoly (A*Q) (B*Q)` — the key product identity that makes the `S`-columns `(X−C t₀)•const`).
- **`pow_card_dvd_pencilDet_of_cols`** (the column-factoring core): ANY invertible `Q` with its `S`-columns in
  `ker(A+t₀•B)` ⟹ `(X−C t₀)^|S| ∣ det(pencilPoly A B)`. Realized via `N = M₀'·D`, `D = diagonal(S↦X−C t₀, else 1)`,
  `det D = (X−C t₀)^|S|` (`Matrix.mul_diagonal`+`det_diagonal`+`prod_ite_mem_eq`); unit `C(det Q)` absorbed via `isUnit_C`.
- **`exists_cols_ker`** (the adapted `Q`): basis of `ker(M₀.mulVecLin)` ⊕ complement (`Submodule.exists_isCompl` +
  `prodEquivOfIsCompl` + `Basis.prod` + reindex `finSumFinEquiv∘finCongr`), packaged as `(Pi.basisFun).toMatrix`;
  `|S| = finrank ker`, invertible via `Basis.invertibleToMatrix`.
- **`finrankKer_le_rootMult`** (★ THE CRUX, axiom-clean): `finrank ker(A+t₀•B) ≤ rootMultiplicity t₀ (det(A+X•B))`
  (combine the two via `le_rootMultiplicity_iff`). This is the genuinely-new matrix-pencil math the scope flagged.
- `pencilDet_natDegree_le` (`≤ d`, via Mathlib `natDegree_det_X_add_C_le`) + **`sum_finrankKer_le`** (★ ∑ corank ≤ d over
  any ratio set `T`: `∑ finrankKer ≤ ∑ rootMult ≤ card roots ≤ natDegree ≤ d`) — the budget that replaces the uniform
  bucket's `d` factor with a constant.
**(B) CONCENTRATION — DONE (axiom-clean, in `ScratchPencilCorank.lean`):** `pow_sum_mul_bound` (`s≥2 ⟹ ∑ s^{c_t} ≤
s^{∑c_t}`, by `Finset.induction` + `a+b≤ab` via `nlinarith`) + **`concentration_bound`** (`s≥2, 1≤c_t≤D−1, ∑c_t≤D ⟹
∑ s^{c_t} ≤ 2·s^{D−1}`, by the split `∑≤D−1` / `=D`). The `pow_le_pow_right₀` + `Finset.add_sum_erase` are the keys.
**(A) BRIDGE + REGROUP INFRASTRUCTURE — DONE (axiom-clean).** `ScratchPencilBridge.lean`:
**`finrank_polarRad_eq_finrankKer`** (`finrank(polarRad G) = finrank ker((toMatrix₂ b b (polarBilin G)).mulVecLin)`)
via `b.equivFun` carrying `polarRad G` *onto* the matrix kernel (key `(Gram *ᵥ b.equivFun h) i = polarBilin G (b i) h`
+ a functional zero on the basis is zero + `LinearEquiv.finrank_map_eq`). `ScratchPencilRegroup.lean` (6 lemmas):
`ker_smul_mulVecLin` + `finrankKer_ratio` (scale-inv `ker((y•A+z•B))=ker((A+(z/y)•B))`, `y≠0`); `radicalCard_eq_pow`
(`|radical(y•P+z•R)| = |K|^{corank(A+(z/y)•B)}` — bridges `ScratchTBound`'s filter-card to the matrix corank) +
`corank_ratio_eq` (finrank version); `sum_comp_ratio_le` (fiber-collapse `∑_{x∈S} h(ρx) ≤ N·∑_{t∈image} h t`, `N`=max
fiber card) + `fiber_fst_card_le` (each ratio-fiber `≤ |K|`, injects via fst).
**(A-assembly) + (C) — DONE (axiom-clean). THE `hq2` THRESHOLD IS REMOVED END-TO-END.**
- `ScratchPencilRegroup.deg_bucket_le` (+ helper `sqrt_natpow`): `∑_{x∈s deg} g x ≤ 2·|K|·(|V|/√|K|)` — factors
  `g x = √|V|·(√q)^{c(ρx)}` (`radicalCard_eq_pow`), `sum_comp_ratio_le` (N=|K|, `fiber_fst_card_le`), `concentration_bound`
  (s=√q, D=d; `1≤c≤d−1` from `polarRad≠⊥`/`hnz` via `corank_ratio_eq` + `Submodule.finrank_eq_zero`/`finrank_lt`,
  `∑c≤d` from `sum_finrankKer_le`).
- `ScratchTBoundCorank.normT_bucket_bound_corank`: `|K|·‖T‖ ≤ |K|²·√|V| + 2·|K|·(|V|/√|K|)` (reuses
  `normT_bucket_bound`'s χ-collapse + nondeg bucket; swaps the deg bucket for `deg_bucket_le`).
- `ScratchTBoundCorank.c0_le_const`: `NS ≤ ¾·n` from `c0_le` **at `dR := 2`** — the original `hq2 : 64·dR²≤q` becomes
  `64·2²=256 ≤ q` = the existing `hq3`, so **`hq2` is dropped**; binding hyps are just `hq1 (d≥3)` and `hq3 (q≥256)`.
**WIRING — DONE (axiom-clean). ⟹ CORANK TIGHTENING COMPLETE.**
- `ScratchPencilCorank.pencilPoly_det_eval` (`(pencilPoly A B).det.eval t₀ = (A+t₀•B).det`, via `RingHom.map_det`+`evalRingHom`)
  + `pencilPoly_det_ne_zero` (`(∃ y z, (y•A+z•B).det≠0) ⟹ (pencilPoly A B).det≠0`; `y≠0` → eval at `z/y`, `y=0` → the
  `X^d`-coeff is `det B` via `Polynomial.coeff_det_X_add_C_card`).
- `ScratchPencilRegroup.pencilDet_ne_zero_of_good` (the `hgood → hp` bridge, via `polarRad_ne_bot_iff_det_eq_zero`).
- **`ScratchTBoundCorank.c0_le_threequarters_corank`** (THE CAPSTONE) — a **drop-in corank-tightened replacement** for
  `ScratchC0Final.c0_le_threequarters`: same `hgood`/`hnz`/`hPu`/`hq1`/`hq3` interface (plus trivial `hd:1≤d`,
  `hq4:4≤|K|`), **`hq2` removed**. Proves `NS ≤ ¾·|V|` (so `c₀ ≤ ¾ < 1`) with binding threshold `hq3 (q≥256)` only.
**⟹ VO⁻₄(q) family threshold `q ≥ 1024 → q ≥ 256`, fully formalized.** Build: `ScratchPencilCorank` (11) +
`ScratchPencilBridge` (1) + `ScratchPencilRegroup` (9) + `ScratchTBoundCorank` (3) — all axiom-clean, NOT in build.sh
(PORT = follow-up). NEXT QUEUE ITEM = small-q tail, then hK cleanup, then increment 5.

**Target + route.** Prove **`QProfileSeparatesAtBase Q T`** (FormsGraphConcrete:157) for general `Q` at a constructed base
`T` of size `O(d + log q)`. This is the **route-(b) wrapper** — its reduction to the seal is LANDED and general
(`isotropySeparates_of_qProfileSeparates` + `coords_determine`, zero new wiring) — proved using the **route-(a) engine**
(Lemma A `configGaussSum_eq_det`, landed + general). The routes CONVERGE: FormsGraphConcrete:144–148 already pins the crux
as the **joint incidence content `Z(S) = #{x : Q(x−t)=0 ∀t∈S}`** over sub-frames `S ⊆ T`, which is exactly route (a)'s
`Z(S)` profile. So there is one crux, two names.

**The proof chain (what's landed ▸ what's open).**
1. ▸ *[landed `coarse_eq_sum_iso` / `count_pi_setValued`]* the fine isotropy-count antecedent ⟹ coarse `Q`-value-**set**
   count agreement; specialising the set to `{0}` (isotropic) ⟹ the **joint isotropic counts `Z(S)` agree** for all `S ⊆ T`.
   (D1 below = completing this marginalisation from the `QProfileSeparatesAtBase` antecedent.)
2. ▸ *[landed + general Lemma A `configGaussSum_eq_det`]* `Z(S) = F(|S|, χ(det G_u(S)), c)` — explicit; `G_u(S)` = Gram of
   `{t−u : t∈S}`, even `d` ⟹ level collapses to the bit `[c=0]`. (D2 = wiring this for general `Q`, generalising Lemma B.)
3. **★ OPEN CRUX (D3):** the profile `{(χ(det G_u(S)), [c=0])}_{S⊆T}` is **injective in `u`**, uniformly in `q`, for
   `T = frame {0,eᵢ} ∪ {O(log q) probes}`. Equivalently (shell-blindness, FormsGraphConcrete:145): the joint `Z(S)`-profile
   separates. Probe-validated (SPIKE-K.1/.2 + `Probe_FrameThenProbes`): frame = linear skeleton (separates most), `O(log q)`
   probes resolve the residual field-value ambiguity via the pair-config square-classes.
4. ▸ *[landed `coords_determine`]* recovered `Q`-profile + nondeg ⟹ `u`; `QProfileSeparatesAtBase ⟹ IsotropySeparatesAtBase`.

**The crux's hard core + tool.** The recovery is **joint, not per-coordinate** (the "root-detect along a line" shortcut is
refuted — needs ~`q` points). The content is injectivity of the `χ`-profile of the 2×2 Gram determinants
`det G_u({t,p}) = 4Q(ū−t)Q(ū−p) − B(ū−t,ū−p)²` over `{frame × probes}`. First attack = the landed chain
`count_pi_setValued → multiCharSum_eq_sum_count → sum_addChar_multiQuad_zero` (the `R=0` symmetry-broken-base Gauss sum) to
turn the joint isotropic counts into the explicit `χ(det G)` data, then a **quadratic-character argument** that `O(log q)`
probe square-classes pin the frame `Q`-values. **Residual risk:** whether that last step is EXACT (quadratic Gauss-sum
identities, present in `GaussCount`) or needs general **Weil bounds** (absent in Mathlib — a contained sub-build). Route-3
(Witt) remains the fallback.

**Build increments (ordered).**
- **D1 — `Z(S)` extraction.** Lemma: the `QProfileSeparatesAtBase` fine antecedent ⟹ `∀ S ⊆ T, Z_u(S) = Z_{u'}(S)` (joint
  isotropic counts). Marginalise the fine profile (sum over base-points ∉ S and the pivot class) via `coarse_eq_sum_iso`.
  Reduces the target to a clean **`ZProfileSeparates`** predicate. *Achievable now; reuses landed pieces.*
- **D2 — `Z(S) = F(χ det G)` for general `Q`.** Generalise Lemma B's `incidence_agree_V` off the instance, feeding Lemma A.
- **D3 — THE CRUX.** `ZProfileSeparates` for `T = frame ∪ probes`, uniform in `q` (the research; D3a skeleton / D3b probe
  resolution per the GATE mechanism).
- **D4 — construct `T` + assemble.** Explicit base (`frameBase ∪ probe set`, `|T| ≤ d+1+O(log q)`); compose D1–D3 +
  `isotropySeparates_of_qProfileSeparates` ⟹ the uniform `IsotropySeparatesAtBase`, fed to the wittFree capstone.
- Then: field-gen (abstract `K`, AUDIT-A GO), `VO^ε` bundling, families d/e (B swapped), char-2, Suzuki, seam.

**First increment = D1**, in a scratch module reusing FormsGraphConcrete + GaussCount; isolates `ZProfileSeparates` as the
single open predicate over general `Q`.

**▶ `ChainDescent/ScratchCrux.lean`** (compiles, axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`;
NOT in build). **D1 ✅ DONE (2026-06-24).** Landed:
- `jointIsoCount Q u S` (the joint isotropic count `Z_u(S)`; "isotropic" = `isoClass ≠ 2`) + **`ZProfileSeparates Q T`**
  (the reduced crux predicate — agreeing `Z(S)` over `S ⊆ T` ⟹ the `Q`-profile, general `Q`).
- **`qProfileSeparatesAtBase_of_zProfileSeparates`** (D1) — the marginalisation: `Z_w(S)` fibered by each point's
  `(T`-profile`, pivot-class)` via `Finset.card_eq_sum_card_fiberwise`; good fibers (`c≠2`, profile `≠2` on `S`) = the
  `QProfileSeparatesAtBase` fine counts (matched via `hfine` + `extProfile`), bad fibers empty ⟹ `Z_u(S)=Z_{u'}(S)`.
- **`isotropySeparates_of_zProfileSeparates`** — the end-to-end chain `ZProfileSeparates + nondeg ⟹ IsotropySeparatesAtBase`
  (composes D1 with the landed `isotropySeparates_of_qProfileSeparates`/`coords_determine`).

**⟹ the ENTIRE open content of the generalization is now the single predicate `ZProfileSeparates Q T`** (the joint
`Z(S)`-profile injectivity, general `Q`).

**D2 (bridge) ✅ DONE (2026-06-24, axiom-clean).** `jointIsoCount_eq_restricted` — `Z_u(S) = #{w ≠ 0 : Q w = 0 ∧
∀t∈S, Q(w − (t̄ − ū)) = 0}` (dictionary `isoClass≠2 ⟺ Q=0` + `count_transport` + shift `w = x − ū`). This is the
instance's `restrictedF` for general `Q,u,S` — the **Lemma-A entry point** (config `a t = t̄ − ū`).

**▶ The D2/D3 boundary + the D3 PLAN (2026-06-24).** What remains splits into a large landed-tool-heavy *analytic*
assembly and the genuine *research* core:
- **D2-analytic / D3a — the closed form `Z_u(S) = F(|S|, χ(det G_u(S)), [c=0])` for nondegenerate config Gram.**
  Pieces LANDED in `ScratchLemmaA`: `reduction_to_levelset_nondeg` (→ homogeneous level-set), `levelset_count_eq`
  (char-sum form), `configGaussSum_eq_det` (config Gauss = `χ(s)ⁿ·χ(D)·gaussSumⁿ`); plus `cone_count_zero_split`
  (`ScratchLemmaB`, the `w=0` correction). NOT yet assembled into the single `= F` statement (the instance *bypassed*
  this via `decide`). Remaining: substitute `configGaussSum_eq_det` + the global `∑ψ(sQx)=χ(s)^d·gaussSumᵈ` into
  `levelset_count_eq`, collapse the `s`-sum, divide by `q^{m+1}`, + the `S ↔ Fin m` reindex. Big, but mechanical.
- **D3b — degenerate configs.** Lemma A needs `IsUnit (det G)`; singletons with isotropic difference (`Q(ū−t)=0`),
  and other rank-deficient sub-frames, fall outside it — handle separately (the level-bit `[c=0]` slice).
- **D3c — invariant recovery.** From `Z_u(S) = Z_{u'}(S)` deduce `χ(det G_u(S)) = χ(det G_{u'}(S))` (+ level bit), via
  `F`'s structure (the recovery the `sigF` `decide` did finitely).
- **★ D3d — THE RESEARCH CORE (uniform-`q`, tool-uncertain).** The `{χ(det G), [c=0]}` profile over `T = frame ∪
  O(log q) probes` pins the field-valued `Q`-profile `{Q(ū−eᵢ)}`. Mechanism (GATE-probed): frame square-classes +
  pair-determinant `χ(4Q(ū−t)Q(ū−t')−B(ū−t,ū−t')²)` over probes resolve the field values jointly (NOT per-coordinate).
  **Tool question unresolved:** exact quadratic-Gauss-sum identities (present) vs general Weil bounds (absent). This is
  the genuine open content.
- **D3e — construct `T` (`frameBase ∪ probe set`, `|T| ≤ d+1+O(log q)`) + assemble** D3a–d ⟹ `ZProfileSeparates`,
  then `isotropySeparates_of_zProfileSeparates` ⟹ the seal.

**Recommendation (GATE discipline):** before formalising the large D3a assembly, **SPIKE D3d's mechanism on paper** —
secure the uniform-`q` field-value-recovery argument (and settle exact-vs-Weil) on a small parametric family. D3a is only
worth building once D3d's argument is in hand; D3d is where the difficulty and the residual risk live.

**▶ D3d INVESTIGATION — DONE (2026-06-24); spikes `Probe_D3dChiInvariant` + `Probe_D3dStructuredBase` (green).**
The decisive findings, and the unknown-vs-handleable split.

*Findings:*
1. **χ-invariants separate at `q≥5` (D3c loses nothing)** — the `χ(det G_S)` pair-profile individualises to discrete
   with greedy base ~7–9 over `q=5..13` (`≪√n`, margin widening). `q=3` additionally needs the level bit `[c_lev=0]`
   (small-case; the faithful invariant is `(χ det G, [c_lev=0])`, exactly Lemma A's `F`-arguments).
2. **★ Information bound — NO fixed algebraic recovery.** A size-`b` base gives `≈C(b,2)` ternary `χ`-queries `≈0.79 b²`
   bits, vs `4 log₂q` bits to separate `q⁴` points ⟹ **`b ≳ 2.25·√(log q)`**. The base *cannot* be constant ⟹ D3d is
   genuinely a character-sum statement, not a fixed identity (the greedy "looks flat" only because `√log q` is tiny over
   `q≤13`).
3. **Naive structured probes fail** — frame `∪ {2eᵢ}` separates only at `q=5` (`>4` probes insufficient for `q≥7`); the
   recovery needs *coupled* probes. So D3e's base construction is non-trivial (use `exists_greedy_base_le_log` for an
   `O(log n)` base *existence*, leaving "it separates" = D3d).
4. **Uncited** — `VO^ε` WL-dim is not in the literature (Skresanov [2007.14696] = rank-3 2-closure = the *seam*, not the
   WL-dim bound); confirms route-doc §9.9.18b. So D3d cannot be *cited* — it must be *proved*.

*The refined tool question (exact-quad vs Weil — the key unknown):* the recovery is `χ` of a **quadratic along a line**
(`Q(ū − (t̄+c·v̄)) = Q(v̄)c² − B(ū−t̄,v̄)c + Q(ū−t̄)`), and quadratic-character sums of *quadratic* polynomials have
**EXACT Gauss-sum evaluations — already in `GaussCount`** (`sum_addChar_quadForm` etc.). So each per-constraint sum is
exact-quadratic (Mathlib-present); **whether the *joint* `O(log q)`-constraint assembly stays exact or needs higher-degree
Weil (Mathlib-absent) is UNRESOLVED** — this is the one question that decides whether D3d is a contained build or a large
Weil sub-build. More optimistic than the GATE's blanket "Weil risk."

*Unknown (the irreducible open core):* **D3d** = uniform-`q` proof that the `χ`-profile at a bounded base separates
(= forms-graph bounded WL-dim). Info-bound-TRUE, uncited, exact-quad-vs-Weil unresolved.

*Handleable now (reduces the seal to the single D3d predicate):* D3a (closed form, landed-tool assembly), D3b (degenerate
configs), D3c (from D3a + the level bit), D3e-scaffold (`exists_greedy_base_le_log` base existence), + the landed chain
(D1, D2-bridge, `isotropySeparates_of_zProfileSeparates`).

**Viability verdict.** D3d is provable-*in-principle* (concrete family, empirically TRUE, info-bound forces a character-sum
argument) but is the genuine uncited research core. **Recommended path:** (i) build the handleable parts ⟹ the entire
generalization is "modulo the single explicit predicate D3d" (clean, honest, achievable); (ii) resolve the exact-quad-vs-Weil
question by working the *smallest* joint case (`d=2`, one probe) explicitly — if exact-quad, D3d is a contained `GaussCount`
build; if Weil, a sub-build (or a deeper literature dive on character-sum bounds for these configs). Do NOT start the large
D3a assembly until (ii) settles the tool.

**▶ R3 (higher-`d`) + GaussCount shape-check + EXISTENTIAL-COUNTING REFRAME — DONE (2026-06-24).** Spikes
`Probe_D3dHigherD` + `Probe_D3dCollisionDecay` (`A2MonovariantProbe.cs`, green). Reshapes the D3d attack and **corrects
two over-optimistic reads** of the GATE / D3d-investigation blocks above.

- *Higher-`d` evidence:* greedy χ-base at **`d=6` separates at 8–12** (q=5) ≈ `d=4 + O(1)`; `d=4` at 6–8 over q=5..13.
  Bounded base survives the genuine joint case. (`q=3` shows `>cap` only because the χ-only probe omits the level bit
  `[c_lev=0]` — the documented small-case, finding 1; not a failure.)
- *GaussCount shape-check (the requested audit):* the landed bricks — `sum_addChar_multiQuad`/`_zero` (`:369`/`:511`),
  `countk_eq_sum_charsum` (`:442`), `card_quadForm_eq` (`:258`), `sum_addChar_quadForm_smul_ne_zero` (M2 cancellation,
  `:232`), `multiCharSum_eq_sum_count` (M2 hinge, `:568`) — are **all ADDITIVE-character (ψ)** machinery. They are the
  engine for **D3a/Lemma A** (assemble `Z(S)=F(|S|, χ det Gram, [c_lev])`, and the "counts-agree ⟹ Gram-agree" hinge
  *given the full pointwise `Q=c` counts*). **They do NOT touch D3d.** ⟹ **CORRECTION** to the investigation block's
  "tool may largely exist / may be exact": D3d needs **MULTIPLICATIVE character-sum (Weil) bounds `∑_v χ(poly(v))`** —
  Mathlib-ABSENT and absent from GaussCount (χ appears only as the Gauss-sum *constant* `∏χ(wᵢ)`, never summed over a
  polynomial). The additive/multiplicative split is the precise reason **D3a is closable now and D3d is not**.
- *Why the gap is intrinsic:* the seal's data is the ISOTROPY incidence only (`isoClass`: `Q=0` vs `Q≠0`, shell-blind) =
  the `c=0` slice. The additive hinge would give clean Gram-recovery **if** all pointwise `Q=c` counts were available; the
  `c=0` slice yields only `χ(det Gram_S)` (square-classes of principal Gram minors). Inverting square-classes-of-minors →
  Gram is the multiplicative/Weil step = D3d.
- *The EXISTENTIAL-COUNTING reframe (the value):* `Probe_D3dCollisionDecay` — adding RANDOM probes to the frame,
  #surviving collision-pairs decays geometrically to **0 at frame+4–5 probes** (q=13 and q=23 alike). Validates a **finite
  averaging** route (NO probability/measure): `∑_{k-probe tuples} #surviving = ∑_pairs (#failing probes)^k ≤ C(n,2)·c₀^k`,
  so `c₀^k·C(n,2) < 1` ⟹ some tuple separates ⟹ a separating base **EXISTS**, its size falling out of the count (the
  steer "prove `|T| ≤ const`, don't pin it / let it fall out"). It reduces D3d's joint-over-`qᵈ` injectivity to a **single
  per-pair bound**: `#{v : v fails to separate a fixed (u,u')} ≤ c₀·n`, `c₀<1`. That is **one** multiplicative χ-sum
  `∑_v χ(g·h)(v)` of a deg-≤4 poly (`g,h` = pair-Gram dets `4Q(v−u)Q(f−u)−B(v−u,f−u)²`, quadratics in `v`) — **Weil enters
  as ONE standard incomplete-sum estimate, not the joint problem.**
- *Base-growth CORRECTION:* per-probe decay is a **constant fraction** (`c₀ ≈ 2^{−(d+1)}`, observed ~0.02 at *both* q=13,23
  — NOT `1/q`), so `k = Θ(log q)` probes and **`|T| = O(d + log q)`, GROWING** (consistent with the info-bound `b≳√log q`).
  The "near-constant base" read from q≤23 was a small-`q` artifact (`q ≪ 3^{d+1}`, below the crossover). The existential
  route is robust to this — it yields whatever `B(d,q)` the per-pair `c₀` supports, automatically.
- *Net (updated verdict):* D3d **does** need a Weil bound (corrects "may be exact"), but the existential route **contains**
  it to a single per-pair incomplete multiplicative character sum + a finite-averaging lemma — far smaller than the GATE's
  "joint Weil sub-build". **Recommended next:** (i) state the per-pair separation lemma + the finite-averaging existence
  wrapper (additive-only; reuses landed counting infra) so D3d collapses to the single Weil estimate; (ii) check whether
  `∑_v χ(Q(v−u)·Q(v−u'))` (singleton-only product of two translated quadratics) has an EXACT evaluation — if so a contained
  build, else a small Weil sub-build. **D3a's "big mechanical" assembly is OFF the critical path** under this route (we need
  the per-pair bound, not the full `Z=F` closed form). Supersedes the `d=2` step above (R3 caveat: `d=2` is too degenerate;
  the joint phenomenon lives at `d≥4`).

**▶ EXACT-vs-WEIL CHECK — RESOLVED: EXACT, NO WEIL (2026-06-24, spike `Probe_D3dExactVsWeil`, green).**
**⚠ THE "singleton observable" CLAIM IN THIS BLOCK IS SUPERSEDED — see the CORRECTION block below: the singleton count is
binary; the live route uses the PAIR observable. The "exact, no Weil" conclusion SURVIVES (it transfers to the pair invariant).**
The per-pair sum `S(u,u') = ∑_v χ(Q(v−u)·Q(v−u'))` (the singleton-model `c₀` driver) is **exactly evaluable without
Weil/Deligne**. Both a proof sketch and the numerics.

- *Why exact (the argument):* `S` depends ONLY on `δ = Q(u−u')` (Witt: `O(Q)` is transitive on level sets — numerically
  confirmed, `singleδ = yes` across all q,d,ε). Conditioning on the **scalar** values `(s,t) = (Q(v−u), Q(v−u'))`,
  `S = ∑_{s,t} χ(s)χ(t)·N(s,t)` with `N(s,t)` a **two-quadric count** (exact, additive — `countk`/`card_quadForm_eq`). The
  multiplicative character lands on the *scalars* `s,t`; `∑_s χ(s)ψ(rs) = ` a **Gauss sum**. So `S` is a finite combination
  of standard Gauss sums — **no `χ` of an irreducible high-degree polynomial** ⟹ **no Weil**. Bounding it needs only
  `|gaussSum| = √q` (elementary, in Mathlib), and the crude triangle bound gives `|S| ≤ q^{d/2+1} < n` for **`d ≥ 4`**.
- *Numerics:* `|S| ≈ 0.8–0.96·√q^d` (square-root size — the earlier `n/√q` size guess was WRONG; the leading terms cancel,
  which is *consistent with* the exact closed form, not evidence against it). Crucially **`c₀(δ) ∈ [0.36, 0.49] < ½`
  uniformly** (d=4/6, q=5..23, both ε), and `c₀ → ½` from below as q grows (since `S/n ~ 1/√q → 0`).
- *Consequence — the singleton route, Weil-free:* `c₀ < 1` provably (`c₀ = ½ + (S + 3z₂ − 2z)/2n`, all terms exact: `z, z₂`
  via `card_quadForm_eq`/multiQuad, `S` via the Gauss closed form). So a **random base of size `O(d·log q)` singleton-separates
  all pairs** (first-moment: `∑_pairs c₀^k ≤ C(n,2)·c₀^k < 1` for `k > 2d·log_q(1/c₀)·…`), and a singleton-separating base
  makes `ZProfileSeparates` hold (its antecedent then forces `u = u'`). **The pair-determinant / higher-`Z(S)` observables are
  NOT needed** — only the singleton `χ(Q(u−t))`, recovered from `Z_u({t})` at `|S|=1` (a small `D3c`-at-`|S|=1` lemma).
- *Net — the D3d build, Weil-free:* (1) **D3c-1** — `Z_u({t})` recovers `χ(Q(u−t))` (`|S|=1` Lemma A + `F` injective in its
  χ-arg, finite). (2) **per-pair `c₀(δ) < 1`** — the exact Gauss closed form for `S` + `|gaussSum|=√q` + the exact `z, z₂`.
  (3) **finite-averaging existence** — `∃ T, |T| = O(d log q)`, singleton-separating (additive-only counting, no probability).
  (4) ⟹ `ZProfileSeparates`. **D3a (the full `Z=F` closed form) and D3d's feared "Weil sub-build" are both OFF the path.**
  The remaining genuine content is the exact-`S` evaluation (Gauss-sum algebra, contained in `GaussCount`) + the averaging
  lemma. **This is the recommended D3d build.**

**▶ LEAN SIBLING — INCREMENT 1 LANDED (2026-06-24, `ChainDescent/ScratchPairSep.lean`, axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`; NOT in build).** The load-bearing core of the Weil-free route,
in Lean:
- **`quadChar_addChar_sum`** — the multiplicative↔additive **Gauss bridge** `∑_y χ(y)·ψ(a·y) = gaussSum χ ψ · χ(a)` for
  ALL `a : K` (`χ = (quadraticChar K).ringHomComp (Int.castRingHom R')`, `R'` a char-zero domain). Proof: `a=0` via
  `MulChar.sum_eq_zero_of_ne_one`; `a≠0` via Mathlib `gaussSum_mulShift` + `χ(a)²=1` (quadratic). Reusable project-wide.
- **`pairCharSum_factor`** — the **"no Weil" core**: `gaussSum χ ψ ^ 2 · (∑_w χ(Q w)·χ(Q(w−c))) =
  ∑_y ∑_z χ(y)·χ(z)·(∑_w ψ(y·Q w + z·Q(w−c)))`. Proof: bridge twice + `Finset.sum_mul_sum` + Fubini. The RHS inner sum is
  exactly the landed `sum_addChar_multiQuad`/`_zero`, so `S` is rigorously a finite combination of additive Gauss sums —
  the "no `χ` of an irreducible high-degree polynomial" fact, now a theorem.
- **Remaining increments (ordered):** (2) **`M`-evaluation + diagonal vanishing** — plug `sum_addChar_multiQuad` (`y+z≠0`)
  and `sum_addChar_multiQuad_zero`+`sum_addChar_linearMap` (`y+z=0` ⟹ `0` for `c≠0`, nondeg) into the RHS (equality, no ℂ);
  (3) **magnitude bound** `|S| ≤ q^{d/2+1} < n` for `d≥4` — the one ℂ-flavored step (`gaussSum_sq` ⟹ `|gaussSum|=√q`,
  needs `R'=ℂ`/an absolute value); (4) **`c₀(δ) ≤ ¾`** for `q≥q₀` from `|S|` + exact `z, z₂` (`card_quadForm_eq`), small `q`
  by `decide`; (5) **finite-averaging existence** of a singleton-separating `T`, `|T|=O(d log q)` ⟹ `ZProfileSeparates`.
  Increment (3) is the only one outside the existing equality toolkit (a small contained `ℂ`-magnitude sub-build).

**▶▶ CORRECTION (2026-06-24) — the SINGLETON route is FLAWED; the observable is the PAIR count (spike `Probe_D3cObservable`,
green). The two bullets above (and the EXACT-vs-WEIL block's "singleton route, Weil-free") OVERSTATE the result.** The seal's
real observable is the joint-isotropic count `Z`, not `χ(Q)` directly. Probe verdict:
- **`|S|=1` is BINARY:** `Z_u({t}) = #{w≠0 : Qw=0 ∧ Q(w−c)=0}` takes the SAME value for `χ(Q(u−t))=1` and `=2` (e.g.
  `VO⁻₄(5)`: both `{20}`; only `Q(u−t)=0` differs). Proof: `w↦λw` fixes the cone `{Q=0}` and scales `polar(w,c)`, so the
  count is constant on every nonzero level — it sees only `[Q(u−t)=0]`, NOT the square class. **So `χ(Q(u−t))` is NOT
  observable, and `D3c-1` (recover it from `Z_u({t})`) is FALSE.** The exact-`S = ∑_v χ(Q(v−u)Q(v−u'))` computation, though
  genuinely Weil-free, is for an **unobservable** quantity.
- **`|S|=2` recovers the square class:** `Z_u({t,t'})` splits cleanly by `χ(det G₂)` (disjoint value-sets, every q). So the
  square-class lives at **pairs** (consistent with Lemma A's `Z=F(χ det G)` for the nondeg 2-config, and with `vo4minus_seal`,
  which separated via size-2 sub-frames).
- **The fix (route recoverable, technique transfers):** use the **observable pair invariant** `χ(det G₂(u; t, t₀))` against an
  anchor `t₀` in place of the singleton. As a function of the probe `t` this is **`χ` of a quadratic** (`det G₂ =
  4Q(t−u)Q(t₀−u) − B(t−u,t₀−u)²`, degree 2 in `t`), and it IS recoverable from `Z_u({t,t₀})`. The per-pair separation count is
  then `#{t : χ(P_u(t)) = χ(P_{u'}(t))}` with `P_u, P_{u'}` quadratics in `t` — the SAME factoring shape as `pairCharSum_factor`
  (→ finite additive Gauss sums, Weil-free). Increment 1's **bridge transfers directly**; `pairCharSum_factor` needs
  generalizing from "form `Q` + translate `c`" to "two quadratic *polynomials*" (inner sum = an inhomogeneous-quadratic Gauss
  sum, still exactly evaluable).
- **What this means for the open core (honest):** D3d is **still open**, now precisely scoped to the **pair** observable:
  (1) the per-pair bound `c₀<1` for `χ(det G₂(·;t,t₀))` (plausibly Weil-free by the same factoring — the inner
  `∑_t ψ(y·P_u + z·P_{u'})` is an inhomogeneous-quadratic Gauss sum — but **NOT yet computed**); (2) **anchor existence**
  (∀`u≠u'` ∃`t₀` making `P_u, P_{u'}` square-class-different for enough `t` — the pair-level analog of the nested-quadric
  argument); (3) averaging + small-`q` `decide`. Empirically the pair-`Z` profile separates at `O(d+log q)` (SPIKE-K.1 used
  exactly `Z_u({t,t'})`), so the result is true; the proof's load-bearing analytic step (the pair-observable `c₀` bound) is the
  genuine remaining content. **The reduction skeleton + the no-Weil technique are proven; the core D3d is sharply scoped but
  unsolved.**

**▶ PAIR-COUNT PROBE + GENERALIZED FACTORING LANDED (2026-06-24).** Acting on the CORRECTION (pair observable), both the
probe and the Lean generalization came back in favor:
- **`Probe_D3dPairCount`** (green): the observable invariant `χ(det G₂(u;t,t₀))` vs anchor `t₀`. **`c_max = max_pair
  min_anchor c₀ ∈ [0.44, 0.49] < ½`** (q=5..13, both ε); **`sep@1anchor ≈ 100%`**, `medAnchorFrac = 1.0` ⟹ **anchor
  existence is robust** (essentially every anchor separates every pair) and averaging gives a base `O(d log q)`.
  `|T| ≈ 0.8n` (a large MAIN TERM, not `√n`) — fine: the factoring makes `T` exact *with* a main term, no Deligne.
  (Note: the singleton `|S|` *did* cancel to `√n`; the pair `T` has a main term — both exactly evaluable.)
- **`pairCharSum_factor_gen`** (`ScratchPairSep.lean`, axiom-clean): the factoring for ANY `f,g : V → K`. Applied with
  `f = det G₂(u;·,t₀)`, `g = det G₂(u';·,t₀)` (each `χ` of a quadratic in the probe `t`), it reduces the degree-4 pair
  sum to `∑_y∑_z χ(y)χ(z)·(∑_t ψ(y·f + z·g))` — the inner an exactly-evaluable quadratic Gauss sum. **The "no Weil" for
  the real observable is now a theorem-shaped reduction**, not an analogy. `pairCharSum_factor` (singleton) is now its corollary.
- **Remaining increments (pair route, updated):** (2) **inner-sum evaluation** `∑_t ψ(y·I_u(t)+z·I_v(t))` for the quadratic
  polynomials `I_u(t)=det G₂(u;t,t₀) = 4Q(t−u)Q(t₀−u) − B(t−u,t₀−u)²` (complete the square; degenerate `(y,z)` = the
  diagonal analog); (3) **`c₀(u,u';t₀) < 1`** from the closed form (`c₀·n = z₂' + ½(nn' + T)`, all exact: `T` via the
  factoring, the zero-counts `z₂', nn'` via affine-quadric counts of `I=0`); (4) **anchor existence** (∀`u≠u'` ∃`t₀`,
  empirically `sep@1anchor≈100%`); (5) **finite-averaging existence** of a separating base `|T|=O(d log q)` ⟹
  `ZProfileSeparates`. Increment (2)'s inner eval is in the additive toolkit; the one ℂ-magnitude step (increment 3's bound)
  is small and contained. **D3d is now a concrete, Weil-free build program on the pair observable.**

**▶ INCREMENT 2 FOUNDATION LANDED (2026-06-24, `ScratchPairSep.lean`, axiom-clean).** The opaque pair invariant is now in
the quadratic-Gauss arena:
- **`pairForm Q a := (4·Q a)•Q − sq.comp((flip Q.polarBilin) a)`** + **`pairForm_apply`** (`= 4 Q(a) Q(s) − (polar Q s a)²`)
  + **`detG2_eq_pairForm`**: `det G₂(u;t,t₀) = pairForm Q (t₀−u) (t−u)` — the pair invariant is a homogeneous **quadratic
  form at a shift**.
- **`pairCombine`**: `y·det G₂(u;t,t₀) + z·det G₂(v;t,t₀) = (y•pairForm_u + z•pairForm_v)(t−u) + z·polar pairForm_v(t−u, u−v)
  + z·pairForm_v(u−v)` — the two-pivot integrand in "quadratic form + linear + const" shape (expand `v`'s form around `u` via
  the polar identity). The algebraic core of the inner sum.
- **`sum_addChar_quadForm_translate`**: `∑_t ψ(P(t−a)) = ∑_t ψ(P t)`.

**▶ INCREMENT 2 — `M(y,z)` CLOSED FORM ASSEMBLED (modulo two isolated inputs) (2026-06-24, `ScratchPairSep.lean`,
axiom-clean).** Three forward lemmas land the closed form down to two clean nondeg-dependent pieces:
- **`pairSum_to_shifted`** (UNCONDITIONAL) — the reorganisation: `M(y,z) = ∑_t ψ(y·pairForm_u(t−u) + z·pairForm_v(t−v))
  = ψ(z·pairForm_v(u−v)) · ∑_s ψ(F(s) + z·polar pairForm_v(s, u−v))`, `F = y•pairForm_u + z•pairForm_v`. Proof: `pairCombine`
  pointwise + pull out the constant phase + recentre `t ↦ t−u` (`Fintype.sum_equiv (Equiv.subRight u)`). No nondeg used.
- **`sum_addChar_shifted_eval`** (complete the square; UNCONDITIONAL given the representation) — if the residual linear term
  `L s` equals `polar F s b` for a vector `b`, then `∑_s ψ(F s + L s) = ψ(−F b)·∑_s ψ(F s)`. Proof: `sum_addChar_quadForm_linear`
  at `r = 1`.
- **`pairSum_closed_of_repr`** (ASSEMBLED) — chains the two: given `b` with `z·polar pairForm_v(s, u−v) = polar F s b ∀s`,
  `M(y,z) = ψ(z·pairForm_v(u−v)) · ψ(−F b) · ∑_s ψ(F s)`.

**▶ INCREMENT 2 — `M(y,z)` CLOSED FORM COMPLETE on the nondegenerate locus (2026-06-24, `ScratchPairSep.lean`, axiom-clean;
pieces (i)+(ii) DONE).** The two nondeg-dependent inputs are now both landed in Lean:
- **(i) `exists_repr_of_nondeg`** — `F.polarBilin` nondeg ⟹ every functional `ℓ` is `polar F (·, b)` for some `b`. Via
  Mathlib `LinearMap.BilinForm.toDual` (nondeg-form ≃ dual) + `apply_toDual_symm_apply` + `polar_comm`. Then
  **`pairSum_closed_of_nondeg`** discharges the `b` hypothesis: from `F.polarBilin.Nondegenerate` alone,
  `∃ b, M = ψ(z·pairForm_v(u−v))·ψ(−F b)·∑_s ψ(F s)`.
- **(ii)+capstone `pairSum_fully_closed`** — chains `pairSum_closed_of_nondeg` with `sum_addChar_quadForm` ⟹ the FULLY
  EXPLICIT value `M(y,z) = ψ(z·pairForm_v(u−v))·ψ(−F b)·(∏ᵢ χ(wᵢ))·gaussSum^d`. Every factor is unit-modulus except
  `gaussSum^d` ⟹ **`|M| = |gaussSum|^d = q^{d/2}`** — exactly the increment-3 `c₀`-bound magnitude. Carries `F.polarBilin.Nondegenerate`
  (for `b`) + `(associated F).SeparatingLeft` (for the Gauss eval) — the SAME nondegeneracy of `F` up to the unit `2`
  (`two_nsmul_associated`), both discharged concretely at instantiation.
**▶ INCREMENT 2 — DEGENERATE LOCUS FINISHED (exact part) (2026-06-24, `ScratchPairSep.lean`, axiom-clean).** The exact
(no-ℂ) handling of the `(y,z)` where `F = y•pairForm_u + z•pairForm_v` drops rank is now landed; together with
`pairSum_fully_closed` (nondeg locus) this covers the whole `(y,z)` plane structurally:
- **`pairForm_polar_anchor`** (`∀ s, polar (pairForm Q a) s a = 0`) + **`pairForm_self_anchor`** (`pairForm Q a a = 0`) —
  the verified structural fact that *every* `pairForm Q a` is degenerate with `a` in its radical. This forces degeneracy
  on the axes `{y=0}∪{z=0}` — but those are killed by the outer weight `χ(y)χ(z) = 0`, so they never contribute to `T`.
- **`sum_addChar_radical_vanish`** — the pair analog of the singleton's diagonal-vanishing: if `r` is in `F`'s polar-radical
  (`∀s, polar F s r = 0`, `F r = 0`) and the residual linear term does not annihilate it (`L r ≠ 0`), then
  `∑_s ψ(F s + L s) = 0`. Proof: translating by `c•r` fixes `F`, shifts `L` by `c·(L r)`, multiplies the sum by `ψ(c·L r)`;
  primitivity gives `c` with `ψ(c·L r) ≠ 1` ⟹ the sum is `0`. This kills every conic point with `L(r) ≠ 0`.
- **What's left of the locus = a bounded, lower-order remainder:** only the thin `L(r)=0` sub-locus of the pencil's
  discriminant conic survives (`≤ d` ratios `(y:z)`, both nonzero), with `|M| ≤ q^{(d+1)/2}` (corank-1) — a MAGNITUDE bound,
  hence increment-3 (`ℂ`) work, NOT exact. So the degenerate locus is *structurally finished*; its residual is folded into
  the increment-3 magnitude bookkeeping. **(Correction to the earlier "MAIN TERM" note: the `|T|≈0.8n` the probe saw is a
  BAD-ANCHOR phenomenon — pencil-alignment — not the degenerate locus; for good anchors the degenerate locus is `o(n)`.)**

**▶ INCREMENT 3 — PLAN (the per-pair / good-anchor `c₀ < 1` bound).** The goal: for a *good* anchor `t₀` (pencil generically
nondegenerate), `c₀(u,v;t₀) = (#{t : χ(I_u(t)) = χ(I_v(t))})/n ≤ 1 − δ`, `I_w(t) = det G₂(w;t,t₀) = pairForm Q (t₀−w)(t−w)`.
- **The exact decomposition (no ℂ; reuses GaussCount counting):**
  `c₀ = ½ + (T + 3 z₂ − z_u − z_v)/(2n)`, where `z_w = #{t : I_w(t)=0}`, `z₂ = #{t : I_u=I_v=0}`,
  `T = ∑_t χ(I_u(t))·χ(I_v(t))`. (From `χ(I_u)=χ(I_v) ⟺ both 0 ∨ (both ≠0 ∧ same class)`; `#same = ½(N₂+T)`.) So `c₀<1`
  reduces to `T + 3z₂ − z_u − z_v < n`, and `c₀ → ½` once each term is `o(n)`.
- **Step 3a — the ℂ setup.** `R' = ℂ` (added `import Mathlib.Analysis.Complex.Basic`); `ψ : AddChar K ℂ` primitive,
  `χ = quadraticChar` into `ℂ`. The one place the development leaves the equality regime.
- **★ UNIFIED TOOL — LANDED (2026-06-24, `norm_sq_sum_addChar_quadForm`, axiom-clean) — de-risks 3c AND 3d; corrects the
  ordering (3c/3d precede 3e).** Both the degenerate-conic magnitude (3c) and the zero-counts (3d) reduce to ONE lemma,
  **`‖∑_x ψ(Q x)‖² = qᵈ · |radical Q|`** (`radical = univ.filter (fun h => ∀x, polar Q x h = 0)`), now proved for ANY quadratic
  form `Q` (no nondegeneracy). Quotient-FREE proof: `‖·‖² = S·conj S` (`Complex.mul_conj` + `Complex.normSq_eq_norm_sq`;
  `conj(ψ z) = ψ(−z)` since values are unit-modulus) `= ∑_{x,h} ψ(Q x − Q(x+h))`, expand `= −polar Q x h − Q h`, and
  `∑_x ψ(−polar Q x h) = qᵈ·[h ∈ radical]` by the project's **`sum_addChar_linearMap`**; on the radical `Q h = 0` (via
  `polar_self` + `Invertible 2`) so the phase is 1. Generalizes 3b (nondeg ⟹ radical = {0} ⟹ `‖∑‖² = qᵈ`). **3c** = this at
  `|radical| ≤ q` (corank ≤ 1 on the conic) ⟹ `‖∑ψ(F)‖ ≤ q^{(d+1)/2}`; **3d** = this fed through `card_quadForm_eq` ⟹
  `z_w ≤ q^{d-1} + q^{(d+1)/2}`. Both now follow from the landed tool; then 3e assembles.
- **★ Step 3b — `|M| ≤ q^{d/2}` on the nondeg locus — DONE (2026-06-24, `ScratchPairSep.lean`, axiom-clean).** Three lemmas:
  **`norm_gaussSum_sq`** (the genuinely-new core: `‖gaussSum χ ψ‖² = card K`, via Mathlib
  `gaussSum_mul_gaussSum_pow_orderOf_sub_one` ⟹ `gaussSum² = χ(−1)·card` for the order-2 `χ`, and `‖χ(−1)‖ = 1`);
  **`norm_addChar_eq_one`** (`AddChar` values into `ℂ` are unit-modulus — `(card K)`-th roots of unity via `map_nsmul_eq_pow`
  + `card_nsmul_eq_zero`); **`norm_pairSum_le`** (`‖M(y,z)‖ ≤ ‖gaussSum‖^d` from `pairSum_fully_closed`: the two `ψ`-phases
  have norm 1, the `∏χ(wᵢ)` factor has norm ≤ 1 via `Finset.prod_le_one`). Together: `‖M‖² ≤ (card K)^d = q^d`.
- **★ Step 3c — `|M|²` UNIFORM bound (nondeg AND conic) — DONE (2026-06-24, `ScratchPairSep.lean`, axiom-clean).** Built the
  WITH-LINEAR generalization of the unified tool, **`norm_sq_sum_addChar_quadForm_linear_le`** (`‖∑_x ψ(Q x + L x)‖² ≤ qᵈ·|radical Q|`
  for ANY `Q, L`; exact form `S·conj S = qᵈ·∑_{h∈radical}ψ(−L h)`, bounded by triangle ineq), and the corollary
  **`norm_sq_pairSum_le`** (`‖M(y,z)‖² ≤ qᵈ·|radical F|`, `F = y•pairForm_u + z•pairForm_v`, via `pairSum_to_shifted`). This
  covers nondeg (`|radical|=1 ⟹ ‖M‖²≤qᵈ`) AND the degenerate conic (`|radical|≤q ⟹ ‖M‖²≤q^{d+1}`) UNIFORMLY — subsumes
  `norm_pairSum_le`, no separate corank-1 descent or `radical_vanish` case-split needed.
- **★ Step 3d — the zero-count — DONE (2026-06-24, `zeroCount_sq_le`, axiom-clean).** `(z·q − qᵈ)² ≤ (q−1)²·qᵈ·|radical P|`
  for any quadratic form `P` (`z = #{x : P x = 0}`). Via `count_eq_charsum` (`z·q = ∑_x ∑_t ψ(t·P x)`), peeling the `t=0`
  term (`= qᵈ`), and the magnitude tool on each `t≠0` slice (`‖∑_x ψ(t·P x)‖² = qᵈ·|radical P|`, scaling preserves the
  radical). **Simplification found:** `c₀<1` only needs `NS ≤ z_u + ½(n+T)` (drop `z₂`,`z_v`), so ONE zero-count `z_u` suffices.
- **★ Step 3e (i) — the `|T|` bound — DONE (2026-06-24, `normT_le`, axiom-clean).** `q·‖T‖ ≤ ∑_{y,z} ‖χ y‖·‖χ z‖·√(qᵈ·|radical F_{y,z}|)`
  (`T = ∑_t χ(det G₂(u;t,t₀))·χ(det G₂(v;t,t₀))`), via `pairCharSum_factor_gen` + `‖gaussSum‖²=q` (`norm_gaussSum_sq`) + triangle
  inequality + the uniform `‖M(y,z)‖ ≤ √(qᵈ·|radical F|)` (`norm_sq_pairSum_le`). Axes drop (`‖χ 0‖=0`).
- **★ CORANK ≥ 2 HANDLED — LANDED (2026-06-25, `ChainDescent/ScratchCorank.lean`, axiom-clean).** The flagged worry — that
  high-corank pencil members (`|radical F_{y,z}| = q^{corank}`, corank ≥ 2) need a delicate per-level stratification — is
  RESOLVED with NO stratification. KEY INSIGHT: every *nonzero* form `F` has a radical that is a PROPER subspace
  (`radical = ⊤ ⟺ polar F ≡ 0 ⟺ F = 0` in char ≠ 2), so `|radical F| ≤ q^{d-1}` UNIFORMLY — corank 1, 2, … all obey the SAME
  bound. Lemma **`radical_card_mul_card_le`**: `F ≠ 0 ⟹ |radical F| · |K| ≤ |V|` (via `polarRad` submodule + `Submodule.finrank_lt`
  + `Module.natCard_eq_pow_finrank`; routed through `Nat.card` to dodge `Fintype`-on-submodule instance mismatch). Supporting:
  `polarRad`, `polarRad_card_filter` (filter-card = `Nat.card` of the radical submodule), `polarRad_ne_top_of_ne_zero`. **NB the
  uniform bound is for the DEGENERATE bucket only** — the nondegenerate members must keep `|radical| = 1` (`√|V|` each), else the
  `(q−1)²` count of them blows the bound. So 3e-ii's split is: nondeg `(q−1)²·q^{d/2}` + deg `(#deg)·q^{d−1/2}`, the deg term
  now uniformly controlled by `radical_card_mul_card_le` regardless of corank.
- **★★ GOOD-ANCHOR COUNT — FULLY PROVEN (2026-06-25, `ChainDescent/ScratchGoodAnchor.lean`, axiom-clean).** Capstone
  **`degenerate_count_le`**: given a good anchor (`∃ y z, polarRad (y•P+z•R) = ⊥`), `#{(y,z): polarRad (y•P+z•R) ≠ ⊥} ≤ d·|K|`
  (`P,R = pairForm_u/_v`). This is the "one remaining analytic input, shared with increment 4" — now CLOSED, not just its cores.
  Built from: analytic cores **`mvPoly_zeros_count_le`** (Schwartz–Zippel, `#{(y,z): p(y,z)=0} ≤ totalDegree(p)·q`, via
  `MvPolynomial.schwartz_zippel_totalDegree`+`Fintype.piFinset_univ`+NNRat `div_le_iff₀`/`div_mul_cancel₀`) + **`det_totalDegree_le`**
  (`det` of a linear-entry `d×d` matrix has `totalDegree ≤ d`, via `Matrix.det_apply`+`totalDegree_finset_sum/_prod/_smul`); plus the
  concrete-pencil bridge — (C) `pencilDisc`/`pencilDisc_totalDegree_le`/`pencilDisc_eval` (`eval ![y,z] disc = det(y•A+z•B)` via
  `RingHom.map_det`); (D) LINCHPIN **`polarRad_ne_bot_iff_det_eq_zero`** (`polarRad G ≠ ⊥ ⟺ det(toMatrix₂ b b (polarBilin G))=0`,
  via `polarRad_eq_bot_iff_separatingRight` + Mathlib `LinearMap.separatingRight_iff_det_ne_zero`) + `toMatrix₂_polarBilin_pencil`
  (+`polar_pencil`); (E) good anchor ⟹ `disc ≠ 0`. GOTCHA: `Basis` is now `Module.Basis` (`open Module`); scratch-import needs
  `lake build ChainDescent.ScratchCorank` first.
- **★★ Step 3e-ii — the `|T|` bound — DONE (2026-06-25, `ChainDescent/ScratchTBound.lean`, axiom-clean).** Capstone
  **`normT_bucket_bound`**: `|K|·‖T‖ ≤ |K|²·√|V| + (d·|K|)·(|V|/√|K|)` (so `‖T‖ ≤ q^{d/2+1} + d·q^{d−1/2} = o(q^d)`). Assembles
  `normT_le` (the RHS) by bucket-splitting `∑_{y,z}` over the support `{y≠0,z≠0}` into nondeg (`|radical|=1`, magnitude `√|V|`,
  count ≤ `|K|²`) and deg (`|radical|≤|V|/|K|` via `radical_card_mul_card_le`, magnitude `≤|V|/√|K|` via `sqrt_mul_le_div`, count
  ≤ `d·|K|` via `degenerate_count_le`) buckets, glued by the abstract `sum_two_bucket_le` + χ-norm `norm_quadraticChar` (`‖χy‖∈{0,1}`,
  collapses the sum onto the support). Reusable atoms in `ScratchBucket.lean` (`sum_two_bucket_le`, `sqrt_mul_le_div`) +
  `ScratchChiNorm.lean` (`norm_quadraticChar`). Hypotheses: good anchor `hgood` (∃ nondeg member) + no-zero-member `hnz`
  (`pairForm_u, pairForm_v` independent on support).
- **★★ Step 3e-iii — counting identity + magnitude connection — DONE (2026-06-25, `ChainDescent/ScratchCount.lean` +
  `ScratchC0.lean`, axiom-clean).** `int_char_pointwise` (per-element `2·[ca=cb] ≤ 2·[ca=0]+1+ca·cb` for `ca,cb∈{-1,0,1}`, by
  `decide`; NO axioms) ⟹ **`counting_identity`** `2·NS ≤ 2·z_u + n + T_ℤ` (generic in `a,b:V→K`). Then **`charSum_int_le_norm`**
  (`T_ℤ ≤ ‖T_ℂ‖`, via `T_ℂ=(T_ℤ:ℂ)`+`Complex.norm_real`+`le_abs_self`) ⟹ **`card_agree_le`**: `2·NS ≤ 2·z_u + n + ‖T_ℂ‖` over ℝ —
  the count now controlled by the analytic magnitude (`normT_bucket_bound`).
- **★★★ Step 3e-iii FINISH — DONE; INCREMENT 3 CLOSED (2026-06-25, `ChainDescent/ScratchC0Final.lean` + `ScratchBucket.c0_le`,
  axiom-clean).** `c0_le` (pure real: from `2·NS≤2z_u+n+T`, `T≤q√n+d·n/√q`, `z_u·q≤n+(q−1)n/√q`, threshold `64q²≤n` [⟺ `d≥3`],
  `64d²≤q`, `256≤q` ⟹ `NS≤¾n`; via `Real.sqrt_le_sqrt`/`abs_le_of_sq_le_sq'`/`nlinarith`). Capstone **`c0_le_threequarters`**:
  wires `card_agree_le` + `normT_bucket_bound` (÷q) + `zeroCount_sq_le` (z_u reindexed `{I_u(t)=0}→{P x=0}` via `card_nbij'`;
  radical `≤|V|/q` via `radical_card_mul_card_le`) into `c0_le` ⟹ for a good anchor (`hgood`, `hnz`, `hPu=pairForm≠0`) with `q≥q₀`:
  **`NS ≤ ¾·|V|`, i.e. `c₀ = NS/|V| ≤ ¾ < 1`** — the per-anchor non-separation bound, the analytic heart of the pair route, COMPLETE.
  **NEXT = increments 4–5 (matching-trick assembly):** `c0_le_threequarters` (per good anchor) + the good-anchor fraction ⟹ `c̄₀<1`
  (V×V non-separating density) ⟹ `ScratchMatching.exists_separating_base` ⟹ separating base `O(d log q)` ⟹ `ZProfileSeparates`.
  (b) **`c₀` counting identity** `2·NS ≤ 2·z_u + n + T_ℤ` (χ-value case analysis over ℤ; `NS = #{t: χ(I_u)=χ(I_v)}`); cast
  `T_ℤ ↔ T_ℂ` (`‖T_ℂ‖ = |T_ℤ|`). (c) **arithmetic** — plug `zeroCount_sq_le` (`z_u`) + the `‖T‖` bound ⟹ `c₀ ≤ ¾` for `q ≥ q₀`
  (sqrt comparisons, done squared). **All magnitude tools (3b/3c/3d + `normT_le`) AND the corank-uniform deg bound are landed;
  what remains is the good-anchor Schwartz-Zippel count + the χ-norm/split glue + the elementary counting identity + arithmetic.**
- **★ The good-anchor hypothesis = the pencil is generically nondegenerate** (`disc_{(y,z)} det(y·G_u + z·G_v) ≢ 0`, ⟺ `∃ (y,z)`
  with `F` nondeg, ⟺ `≤ d` degenerate ratios). This is EXACTLY increment 4's good-anchor predicate (the alignment locus is its
  complement) — so increment 3's `c₀ ≤ 1−δ` for good anchors feeds directly into increment 4's `c̄₀ ≤ 1−δ(1−O(1/q))`. The two
  increments meet at the pencil-nondegeneracy condition.
  **NB (needed for `radical_card_mul_card_le` to apply on the whole support):** good-anchor must ALSO exclude a *zero member* —
  `F_{y,z} = 0` for some `(y,z) ≠ 0` ⟺ `pairForm_u, pairForm_v` proportional ⟺ the anchor gives `u,v` identical-up-to-scalar
  invariants (it genuinely fails to separate). On the χ-support (`y,z ≠ 0`) zero-member ⟺ `pairForm_u ∝ pairForm_v`; requiring
  `pairForm_u, pairForm_v` linearly independent (a Zariski-open, hence good-anchor-typical condition) makes `F_{y,z} ≠ 0` on the
  support, so the corank-uniform bound `|radical|·q ≤ |V|` applies to every degenerate `(y,z)`.
- **The single genuinely-new content = step 3b/3c (the ℂ magnitude of `M`)**; everything else reuses landed counting bricks
  (`card_quadForm_eq`, `count2_eq_charsum`, `pairCharSum_factor_gen`) or is the matching-trick combinatorics already landed.

**▶▶ INCREMENT 4 — STRUCTURAL BACKBONE LANDED (2026-06-26, `ScratchIncr4.lean`, axiom-clean).** The anchor-averaging that
produces the matching `F` is now a theorem (`fail_count_split`/`matching_F_bound`): with `A`=probe `t`, `B`=anchor `t₀`,
per-good-anchor fail bound `c` and bad-anchor count `β`, `F = #{(t,t₀):fail} ≤ c·|V| + |V|·β`, so `c̄₀ = c/|V| + β/|V|`.
This is exactly `exists_separating_base`'s `hF`; the matching closes once `c̄₀ < 1`. **Input `c` is now DONE; one analytic
input (`β`) remains.**
- **✓ `c` (per-good-anchor fail bound) DONE — `good_anchor_fail_le_const`: `#{t:¬sep} ≤ 15/16·|V|`.** `fail(t,t₀) ⟹
  {χ(I_u)=χ(I_v)} ∨ {I_u(t)=0} ∨ {I_v(t)=0}` (the bridge `jointIsoCount_ne_of_chiSep_pair` separates only when **both** configs
  nondeg ∧ `χ` differ; **the `corr` term is folded into `β`**, since for a good anchor we also require `Q(t₀−u),Q(t₀−v)≠0`,
  killing `corr`). `#{χ-equal} ≤ ¾|V|` (`c0_le_threequarters`); the zero-counts `#{I_u=0}`,`#{I_v=0}` are each `≤ 3/32·|V|`
  via `zeroCountShift_card_le` (`z·q ≤ |V|+(q−1)|V|/√q`, so `z/|V| ≤ 1/q + (q−1)/(q√q) ≤ 1/256+1/16 = 17/256 < 3/32` at `q≥256`)
  — the `O(1/√q)` zero-counts DOMINATE the gap. Net `c/|V| ≤ ¾ + 3/16 = 15/16 < 1`. Carries `hPv` (the `v`-form nonzero)
  alongside `hPu` (derivable from `hgood`; added explicitly for now).
- **★ `β` (bad-anchor count) `O(|V|/q)` — the remaining increment-4 piece** = `#{t₀ : ¬(hgood ∧ hnz ∧ hPu ∧ hPv ∧ Q(t₀−u)≠0
  ∧ Q(t₀−v)≠0)}`, Schwartz–Zippel **in `t₀`** (a different variable than `ScratchGoodAnchor.degenerate_count_le`, which is in
  `(y,z)`); each condition is the zero-set of a nonzero polynomial / quadric in `t₀`'s coords (non-vacuity = `∃` good anchor,
  i.e. `pairForm_u`,`pairForm_v` have distinct radicals for `u≠v`). Then increment 5 = ℕ-packaging into `exists_separating_base`.

**▶ INCREMENT 4 (anchor existence) FOLDS INTO INCREMENT 5 (averaging) — the matching trick (2026-06-24, de-risked).** A handoff
question: is "anchor existence" a separate hard (nested-quadric) argument? **No — it dissolves into the averaging, via a specific
device, but with one subtlety to respect.**
- **The matching trick.** Build `T = {t₁,…,t_k}` (k even) iid uniform and match into **disjoint** pairs `(t₁,t₂),(t₃,t₄),…`;
  disjoint ⟹ the k/2 pairs are **independent**. `(u,u')` unseparated by `T` ⟹ none of the matched pairs separates ⟹
  `P[unsep] ≤ c̄₀^{k/2}`, where `c̄₀ = ` density of non-separating ordered pairs in `V×V`. First moment: `E[#unsep] ≤ n²·c̄₀^{k/2}
  < 1` for `k > 4d·log q / log(1/c̄₀)` ⟹ a base of size `O(d log q)` separates ALL pairs. **No separate anchor-existence
  argument** — the anchor is the other matched element, and `det G₂` is symmetric in `(t,a)`. **Single required input: `c̄₀ < 1`
  bounded.**
- **The subtlety (decide before committing).** Computing `c̄₀` as a *joint* `(a,t)` character sum is a **degree-4 sum** (`det G₂`
  is degree-2 in each of `a,t`) ⟹ **Deligne**, harder than the Weil-free per-anchor (fixed `a`, quadratic-in-`t`) sum of
  increments 2/3. So the fold-in is NOT free if done naively.
- **The reconciliation (stays Weil-free).** Bound `c̄₀ = E_a[c₀(·;a)] ≤ 1 − ρδ`, where `ρ` = density of **good anchors**
  (`c₀(u,u';a) ≤ 1−δ`). A bad anchor (`c₀≈1`) is one where the two quadratics-in-`t` `det G₂(u;·,a)`, `det G₂(u';·,a)` align —
  a **proper subvariety in `a`, density `O(1/q)`** ⟹ `ρ ≥ 1−O(1/q)` ⟹ `c̄₀ ≤ 1−δ'` (constant gap). Uses only the **Weil-free
  per-anchor `c₀`** + a soft **"bad-anchor locus is low-dimensional"** lemma — NOT a universal-anchor construction, NOT Deligne.
- **De-risked numerically (`Probe_D3dPairCount`, c̄₀/maxC0 columns):** `c̄₀ ≈ 0.45` **flat and bounded** over q=5..13, both ε
  ⟹ matching trick closes. The worst *single* anchor `maxC0` **hits 1.00 at q=5,7** ⟹ a universal anchor does NOT have a uniform
  gap — so the **averaging (c̄₀) route is correct and the fixed-universal-anchor route is fragile**. Bad anchors are ~1%
  (`sep@1anchor` 99–100%), matching the `O(1/q)` subvariety estimate.
- **⟹ Recommendation:** increment 4 = a short lemma "bad-anchor locus is a proper subvariety (density `O(1/q)`)" feeding
  `c̄₀ ≤ 1−δ`; increment 5 = the matching-trick first moment. State the averaging input as `c̄₀` (anchor-averaged), discharged
  from per-anchor (Weil-free) `c₀` — do NOT use a joint `(a,t)` Deligne sum and do NOT construct a universal anchor.

**▶▶ STATUS (2026-06-25) — INCREMENT 3 CLOSED; THIS BLOCK (increments 4–5) IS THE IMMEDIATE NEXT STEP.** The per-anchor input
`c₀ ≤ ¾ < 1` is now LANDED axiom-clean as **`ScratchC0Final.c0_le_threequarters`** (good anchor + `q≥q₀` ⟹ `NS ≤ ¾·|V|`). So the
remaining frontier is exactly: (4) the **good-anchor density** lemma below (`c̄₀ = E_a[c₀] ≤ 1−δ'`, bad-anchor locus a proper
subvariety, density `O(1/q)`) + (5) feed `c̄₀<1` into `exists_separating_base` (LANDED) ⟹ separating base `O(d log q)` + the
**observable↔count bridge** (`χ(det G₂)` ⟸ `Z_u({t,t₀})`; separating base ⟹ `ZProfileSeparates`'s `∀ S⊆T` profile-separation).
Then Layer B (`ZProfileSeparates → IsotropySeparatesAtBase → seal`) is already landed (`ScratchCrux` + idx 1248). Full layered
remainder (families, seam, port): `chain-descent-remaining-work.md` §3a.1.

**▶▶ OBSERVABLE↔COUNT BRIDGE — CONFIRMED + B1b LANDED (2026-06-26, `ChainDescent/ScratchBridge.lean`, axiom-clean
`[propext, Classical.choice, Quot.sound]`, NOT in build).** Confirmed early (the user-flagged "real unbuilt risk"): the bridge is
**contained, not a hidden wall**, on the nondeg-config locus — but it surfaces three subtleties that must be respected.
- **The link, precisely.** `ScratchCrux.ZProfileSeparates Q T` requires `(∀ S⊆T, Z_u(S)=Z_v(S)) → Q-profile agrees`. The
  increment 3/4/5 chain produces a `T` separating every `u≠v` in the **pair observable** `χ(det G₂)` (`NS = #{t:χ(I_u t)=χ(I_v t)}`,
  `I_w(t)=det G₂(w;t,t₀)`). The contrapositive at the heart of `ZProfileSeparates` is closed by the **`|S|=2` Lemma A**:
  `Z_u({t,t₀}) = Z_v({t,t₀}) ⟹ χ(det G₂(u;t,t₀)) = χ(det G₂(v;t,t₀))`.
- **The closed form (assembled on paper from landed pieces; B1a = the Lean assembly, still open).** For `m=|S|=2`, **even `d`**,
  on the nondeg config locus (`IsUnit (det G₂)`):
  `Z_u({t,t₀})·q³ = qᵈ + χ(det G₂(u;t,t₀))·K·(q·[c=0] − 1)`, `K = χ(disc Q)·gaussSum^{d+2}` a **nonzero rational integer**
  (`gaussSum² = χ(−1)·q`). Derivation: `levelset_count_eq` (landed) + `configGaussSum_eq_det` (landed: config-dependence enters
  **only** through `χ(det G₂)` — the key) + `sum_addChar_quadForm_smul` (landed global Gauss); then `m=2 ⟹ χ(−s⁻¹)²=1`,
  even `d ⟹ χ(s)ᵈ=1` collapse the `s`-bracket to `∑_{s≠0}ψ(−sc)=q[c=0]−1`. **★ B1a ANALYTIC CORE LANDED (2026-06-26,
  `ScratchBridgeA.levelset_count_collapse`, axiom-clean):** exactly this `s`-sum collapse — `(level-set count at c)·q³ =
  |V| + χ(D)·(gaussSum²·W)·(q·[c=0]−1)`, `W = ∑ₓψ(Qx)`, `D = det` config Gram — assembled from `levelset_count_eq` +
  `configGaussSum_eq_det` + `sum_addChar_quadForm_smul` + `AddChar.sum_mulShift`, with the `m=2`/even-`d` χ-power kill
  (`χ(−s⁻¹)²=1`, `χ(s)ᵈ=1`) done by rewriting only the power subterms (the `finBasis` dependent type is untouched). `K = gaussSum²·W`
  is `u`-independent (config enters only via `χ(D)`; `= χ(disc Q)·gaussSum^{d+2}` after `sum_quadForm_eval`). **Remaining B1a (all
  landed-tool or mechanical, OFF the analytic core):** (i) cone-count↔level-set (`reduction_to_levelset_nondeg`) + the `w=0`
  correction (`ScratchLemmaB.cone_count_zero_split`); (ii) `D ↔ pairForm`/`det G₂` identification (so `χ(D)=χ(I_w(t))`); (iii) the
  `R'→ℕ` descent (`÷q³`, `Nat.cast` injective). The `VO⁻₄(3)` instance *bypassed* all of this via `decide`.
- **★ B1b LANDED (the load-bearing distinctness): `ScratchBridge.chiSep_imp_zSep`.** From the closed form, the four
  `(χ,[c=0]) ∈ {±1}×{0,1}` values `qᵈ ± K`, `qᵈ ± K(q−1)` are **distinct for `q>2` (`K≠0`)**, so `χ(det G₂)_u ≠ χ(det G₂)_v ⟹
  Z_u ≠ Z_v`. Proved abstractly (`Z_w = n + χ_w·K·(q·b_w−1)`, `χ_w∈{±1}`, `b_w∈{0,1}` ⟹ `χ_u≠χ_v ⟹ Z_u≠Z_v`), so it consumes
  B1a directly once assembled.
- **★ THREE SUBTLETIES surfaced by the confirmation (do not skip):**
  1. **The `[c=0]` bit is genuinely in the bridge.** `Z` depends on *both* `χ(det G₂)` and the level bit `[c=0]` (`c=−Q(w₀)`).
     The increment-3/4/5 separation is in `χ(det G₂)` **alone** — that is still *sufficient* (B1b shows `χ`-separation survives
     the `c`-bit: no `(χ_u,b_u)` vs `(χ_v,b_v)` collision when `χ_u≠χ_v`), but the bridge proof must carry the explicit 4-value
     form, NOT merely "`Z` is a function of `χ`". B1b is exactly this check.
  2. **The degenerate-config case (`χ=0`) — B1-deg — is DISSOLVED, not a remaining piece (2026-06-26).** Lemma A needs
     `IsUnit (det G₂)`; a separating pair with `χ_u=0` (config-degenerate) vs `χ_v=±1` would need the rank-deficient count
     `Z_deg` (the `D3b` value). **The clean resolution is to never need it:** the bridge reduction
     **`ScratchBridgeZ.zProfileSeparates_of_zSep`** (axiom-clean) shows `ZProfileSeparates Q T` follows from *any*
     `Z`-separating base (`∀ u≠v, ∃ S⊆T, Z_u(S) ≠ Z_v(S)`), and the per-pair step **`ScratchBridge.pairCount_ne_of_chiSep`**
     (B1b in count form, axiom-clean) turns a **config-nondeg** χ-separating pair into a `Z`-separating one. So the matching
     (increment 4) is targeted at config-nondeg separating pairs; the config-degenerate locus `{det G₂ = 0}` is an affine-quadric
     zero set of density `O(1/√q)` (the `zeroCount_sq_le` bound increment 3 already uses), folded into the matching's "bad" set
     alongside bad anchors — costing only an `O(1/√q)` gap shrink (`#{strict-sep t} ≥ (¼ − O(1/√q))·|V| > 0` for `q ≳ const`).
     **So B1-deg is relocated into the increment-4 density, not proved** (computing `Z_deg` directly via rank-deficient Lemma A
     remains an off-critical-path option). The bridge is thereby **architecturally closed**: it needs only B1a's mechanical
     wrapping + a config-nondeg `Z`-separating base from increment 4/5.
  3. **`q=2` breaks distinctness** (`q−1=1` collapses two of the four values) — harmless, char-2 is already a separate excluded
     track (`Invertible 2`), but it confirms the bridge is **odd-`q` only**, consistent with the rest of the route (see §11.5).
- **Net verdict — bridge ARCHITECTURALLY CLOSED, B1-deg dissolved.** The end-to-end chain is: (config-nondeg χ-separating base,
  increment 4/5) →[`pairCount_ne_of_chiSep` (B1b) + `levelset_count_collapse` (B1a core)]→ (`Z`-separating base)
  →[`zProfileSeparates_of_zSep`]→ `ZProfileSeparates`. Landed axiom-clean: the two endpoints (`pairCount_ne_of_chiSep`,
  `zProfileSeparates_of_zSep`) + the analytic core (`levelset_count_collapse`). **Remaining = B1a's mechanical wrapping**
  (no degenerate-config computation, no Weil, no new theory):
  - ✓ **wrap (i) LANDED (2026-06-26, `ScratchBridgeB.fullcount_eq_jointIsoCount_add_corr`, axiom-clean):**
    `fullcount = jointIsoCount + [y=0 corr]` — connects the observable `jointIsoCount` to the Lemma-A `fullcount`
    (`cone_count_zero_split` ∘ `jointIsoCount_eq_restricted`).
  - ✓ **wrap (ii) LANDED (2026-06-26, `ScratchBridgeC`, axiom-clean):** `fullcount_pair_eq_levelset` (ii-a, the `Finset
    {t,t₀}`↔`Fin 2` config indexing + `reduction_to_levelset_nondeg`) + **`fullcount_pair_closed`** (ii-b) — the **fullcount
    closed form** `fullcount·q³ = qᵈ + χ(D)·(gaussSum²·∑ψ(Q))·(q·[Q w₀ = 0] − 1)`, config-nondeg + even `d`, over general `R'`.
  - ✓ **wrap (iii) LANDED (2026-06-26, `ScratchBridgeD.chi_configDet_eq_chi_pairForm`, axiom-clean):** `χ(D) = χ(I_w(t))`.
    Proved cleaner than the `D = ¼·det G₂` framing: BOTH the `associated = ½·polar` factor (`(⅟2)²`) AND the
    `Module.finBasis ↔ Pi.basisFun` change of basis (`(det P)²`, via `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix` after
    reindexing `finBasis` to `Fin 2` — det-preserving, `det_submatrix_equiv_self`) enter as **squares**, killed by `χ`
    (`hkill : χ(s²·x)=χ x`). So **no identification of `finBasis` with the standard basis is needed** (it is generally false);
    `χ(D)=χ(I_w)` exactly, no residual `χ(2)`. Supporting: `configPolarDet_eq_pairForm` (2×2 polar Gram det = `pairForm`).
  - ✓ **final assembly + ℂ-restated B1b LANDED (2026-06-26, `ScratchBridgeD`, axiom-clean):** `jointIsoCount_pair_closed_corr0`
    (the corr=0 per-pair closed form `Z_u·p³ = |V| + χ(I_u)·K·(p·[Q w₀=0]−1)`, K=`gaussSum²·∑ψ(Q)`) + `chiSep_imp_zSep_field`/
    `pairCount_ne_of_chiSep_field` (B1b over a `CharZero` field — the `q(bᵤ+bᵥ)−2≠0` step is a nat-cast argument, NO `R'→ℕ`
    descent) + the end-to-end per-pair capstone **`jointIsoCount_ne_of_chiSep_pair`** (`χ(I)`-separation ⟹ `Z`-separation, the
    exact `∃S⊆T` witness `zProfileSeparates_of_zSep` consumes). **The bridge is now closed end-to-end.** Carried (not re-derived):
    `hK : gaussSum²·∑ψ(Q) ≠ 0` (independent Gauss nonvanishing). NB prime-field model (`q=p`); `q=pᵉ` = field-gen (concern #4).
  - **★★ FINDING from wrap (ii) — the `corr` term, and a refinement to increment 4 (do NOT lose this).** Combining wrap (i)+(ii)
    gives the *observable* closed form `jointIsoCount·q³ = qᵈ − corr·q³ + χ(I_w)·K·(q·[Q w₀=0] − 1)`, `corr = [Q(t̄−w̄)=0 ∧
    Q(t̄₀−w̄)=0]` (both config-differences isotropic). The clean B1b (`pairCount_ne_of_chiSep`, `Z = n + χ·K·(q·b−1)`, same `n`)
    **silently assumed `corr = 0`** — with `corr_u ≠ corr_v` the effective `n` differs by `q³` and the four-value distinctness can
    collide (checked: e.g. `q=3, d=4`). **Resolution (same dissolution as B1-deg):** `corr_w = 1` is a *codimension-2* condition
    (`Q(a₁)=Q(a₂)=0`), density `O(1/q²)`, so require `corr_u = corr_v = 0` in the matching's separating-pair predicate — folding the
    `O(1/q²)` `corr=1` locus into the increment-4 bad set alongside the config-degenerate and bad-anchor loci. Then `jointIsoCount`
    reduces to the clean `Z = qᵈ + χ·K·(q·b−1)` and B1b applies unchanged. **So increment 4's good-pair predicate is now
    `{config-nondeg ∧ corr=0}` on both points** (three small Schwartz–Zippel loci total: `disc≢0`/`hgood`, `pairForm` indep/`hnz`,
    `corr=0`); the analytic core (`c0_le_threequarters`, B1b) is untouched.
  - **SIMPLIFICATION (no `R'→ℕ` descent needed):** work in `R' = ℂ` throughout. Distinctness in ℂ suffices — the counts are
    `ℕ`-casts, `K = gaussSum²·∑ψ(Q)` is a **nonzero cyclotomic integer** (need not be in `ℤ`), and `pairCount_ne_of_chiSep`/B1b
    restate over ℂ (the `q(b_u+b_v)−2 ≠ 0` step holds for the nat-cast `q ≥ 3`). So the integrality/`÷q³` descent drops out.
  This is *not* the hidden wall the route's success hinged on.

**▶ MATCHING TRICK CONFIRMED + COUNTING CORE LANDED + GAPS SHARPENED (2026-06-24).** Stress-tested the increment-4 fold-in
above; it is **sound**, and the load-bearing combinatorial core is now an axiom-clean theorem. Three things:
- **★ `ScratchMatching.exists_separating_base`** (`ChainDescent/ScratchMatching.lean`, axiom-clean
  `[propext, Classical.choice, Quot.sound]`, `lake env lean`; NOT in build) — the matching-trick first moment as a **pure
  finite-counting** theorem (no probability/measure): for `fail : ι → W → Prop` (`W` = matched-pair space, `ι` = targets) with
  `∀g, #{w : fail g w} ≤ F` and `|ι|·Fᵐ < |W|ᵐ`, there is a base `P : Fin m → W` with `∀g, ∃j, ¬fail g (P j)`. Proof: the count
  of bases failing a fixed target factors as `(#fail)ᵐ` (independent coordinates, `Fintype.card_piFinset`); union bound over
  targets. **This is the increment-5 engine and it consumes the single analytic input `c̄₀ < 1` directly** — instantiate `W=V×V`
  (probe×anchor), `ι={(u,u'):u≠u'}`, `F=⌊c̄₀·n²⌋`; `|ι|·Fᵐ<|W|ᵐ ⟺ n²·c̄₀ᵐ<1 ⟺ m=O(d log q)`. Anchor existence has fully
  dissolved: the anchor is the other matched coordinate (`det G₂` symmetric in `(t,a)`), no universal-anchor construction.
- **★ Probe strengthened + premise validated (`Probe_D3dPairCount`, new cols).** The old `c̄₀` column was the *global* mean over
  (pair,anchor) — NOT the first-moment input. New **`cbarMax = max_pair (mean_anchor c₀)`** (the TRUE input) = **0.47–0.52, flat
  and <1 over q=5..17, both ε** ⟹ first moment closes uniformly over pairs with gap **δ≈0.5**. **`maxC0` hits 1.000 at q=5,7**
  ⟹ universal-anchor route confirmed FRAGILE (averaging essential). **`q·badFrMx` ≈ 0.2–0.3 then 0** (bad anchors = frac with
  `c₀≥0.9`) ⟹ bad/aligned anchors are O(1/q) or rarer — the Schwartz-Zippel regime. The premise `c̄₀<1` is solidly validated on
  the right quantity.
- **★ Sharpened remaining gaps (the `c̄₀<1` input decomposes cleanly).** `c̄₀(u,u') = mean_a c₀(u,u';a) ≤ 1 − δ(1 − β)`, β = bad-anchor
  fraction:
  1. **(G-align, NEW, soft, tool CONFIRMED present)** bad/aligned anchors form a *proper subvariety* in `a`, density `β ≤ O(1/q)`.
     The alignment condition (the two quadratics-in-`t` `det G₂(u;·,a)`, `det G₂(u';·,a)` are square-proportional) is the zero set
     of a nonzero `MvPolynomial` of bounded total degree in `a`; density bound = **`Mathlib.Algebra.MvPolynomial.SchwartzZippel`
     `schwartz_zippel_totalDegree`** (`#{zeros}/qⁿ ≤ totalDegree/q`, integral domain) — Weil-FREE. **One non-vacuity obligation
     remains (the irreducible residue of "anchor existence", now trivial): the alignment polynomial is `≢ 0` for every `u≠u'`
     (≡ ∃ a good anchor) — true because for generic `a` the two `pairForm` have DIFFERENT radicals `⟨a−u⟩≠⟨a−u'⟩` (`u≠u'`).**
  2. **(G-anchor = increments 2/3, the real analytic core, UNCHANGED)** off the alignment variety, the per-anchor Gauss sum is small
     ⟹ `c₀(u,u';a) ≤ 1−δ`. This is the `pairCharSum_factor_gen` + `M(y,z)` closed-form + `|gaussSum|=√q` work.
  - **NB the doc bullet above said "degree-4 ⟹ Deligne" for the joint sum — that is why we do NOT compute `c̄₀` jointly; the
    decomposition (G-align via Schwartz-Zippel + G-anchor Weil-free per-anchor) keeps everything Weil-free.** The matching trick
    relocates "construct a universal anchor" to "alignment poly ≢ 0" (much weaker) + a Schwartz-Zippel density bound (Mathlib).
- **Net verdict:** the matching trick **solves** anchor existence. Remaining math = G-anchor (the per-anchor `c₀<1`, = increments
  2/3, already the planned analytic frontier) + G-align (Schwartz-Zippel density + the soft `≢0` non-vanishing). The combinatorial
  glue (`exists_separating_base`) and the empirical premise are now locked.

**▶▶ INCREMENT-4 REFINEMENT (2026-06-26) — state the good-anchor density against `c0_le_threequarters`'s ACTUAL hypotheses,
not "square-proportional alignment".** Increment 3 closed, so the per-anchor bound is now a concrete Lean theorem with a concrete
hypothesis set, and increment 4 must deliver *exactly* its complement. `ScratchC0Final.c0_le_threequarters` consumes **three**
predicates on the anchor `t₀` (per pair `u≠v`):
  - **`hgood`** : `∃ y z, polarRad (y•pairForm Q (t₀−u) + z•pairForm Q (t₀−v)) = ⊥` — the **pencil is generically nondegenerate**
    (⟺ the discriminant `det(y•G_u + z•G_v) ≢ 0` in `(y:z)`). This is the genuine "good anchor" condition.
  - **`hnz`** : `∀ y z ≠ 0, y•pairForm_u + z•pairForm_v ≠ 0` — **no zero pencil member** on the χ-support ⟺ `pairForm Q (t₀−u)`,
    `pairForm Q (t₀−v)` **linearly independent**. THIS is the "square-proportional" condition the G-align bullet names — but it is
    only ONE of the three.
  - **`hPu`** : `pairForm Q (t₀−u) ≠ 0` — the pivot form is nonzero.
So increment 4 must bound `#{t₀ : ¬(hgood ∧ hnz ∧ hPu)} ≤ O(1/q)·|V|` — the union of THREE proper subvarieties in `t₀`, each a
Schwartz–Zippel count (the `ScratchGoodAnchor`/`degenerate_count_le` tooling applies to all three: `disc ≢ 0` for `hgood`,
`pairForm_u ∧ pairForm_v` independent for `hnz`, `pairForm_u ≠ 0` for `hPu`), NOT just the alignment locus of the G-align bullet.
The `c̄₀ = E_{t₀}[c₀]` average then splits as: good anchors (density `1−O(1/q)`) contribute `≤ ¾` (increment 3), bad anchors
(density `O(1/q)`) contribute `≤ 1` ⟹ `c̄₀ ≤ ¾ + O(1/q) < 1`. **Two consequences for the matching/bridge:** (i) the matching's
`fail` set should be defined over the **good-anchor** locus so the bridge (above) only meets the `±1/±1` config-nondeg case; (ii) the
"alignment poly ≢ 0" non-vacuity of the G-align bullet is *exactly* `hgood`'s `∃` witness, already discharged by
`degenerate_count_le`'s `hgood` hypothesis being satisfiable for `u≠v`. (The §13 increment-3 NB at "good-anchor must ALSO exclude a
zero member" already flagged `hnz`; this refinement makes the full triple the increment-4 target.)

**▶▶ INCREMENT 4 BAD-ANCHOR `β` — STRUCTURAL REDUCTION + SZ ENGINE LANDED (2026-06-26, `ScratchIncr4b.lean`, axiom-clean).**
Key simplification: `pairForm Q (t₀−v)` is ALWAYS degenerate (`pairForm_polar_anchor`), so `hgood` (a nondeg pencil
member exists) forces `hnz ∧ hPu ∧ hPv` — the bad set collapses (mod `t₀∈{u,v}`) to `{¬hgood} ∪ {Q(t₀−u)=0} ∪ {Q(t₀−v)=0}`.
**`β` is now REDUCED TO ONE EXPLICIT OBLIGATION (all surrounding infra axiom-clean).** Landed: `hgood ⟹ hnz∧hPu∧hPv`
(`hPu_of_hgood`/`hPv_of_hgood`/`hnz_of_hgood`) → `bad_anchor_card_le_hgood`: `β ≤ #{¬hgood} + 2`; the SZ engine
`mvPoly_zeros_count_le_dim`; the rigorous SZ reduction `bad_anchor_count_le_of_poly` (given a nonzero representing
polynomial `P`, `#{¬hgood}·|K| ≤ deg P·|V|`); and `notHgood_eval_zero_of_repr` (discharges its `hrep` from `P` representing
the pencil det at a fixed witness, via `polarRad_ne_bot_iff_det_eq_zero`). **`P` is now CONSTRUCTED (`ScratchIncr4c`, 12
axiom-clean lemmas)** — `coordPoly_eval_linFunc` (workhorse), `gramQuadPoly_eval` (via `polar_t0_t0_sum`), `LPoly`/`QPoly`,
`polar_pairForm_apply`, `entryPoly_eval`, **`pencilDetPoly`** + `pencilDetPoly_eval` (`RingHom.map_det`) +
`pencilDetPoly_ne_zero` → capstone **`badHgood_count_le`: `#{¬hgood}·|K| ≤ (pencilDetPoly).totalDegree·|V| = O(d/q)`**.

**▶▶▶ B-iii + B-ii DONE (2026-06-26, `ScratchIncr4c.lean`, all axiom-clean) — `β` now closed to an EXPLICIT `O(d/q)` bound.**
- **B-iii (`totalDegree(pencilDetPoly) ≤ 2d`):** the bounded-degree generalization `det_totalDegree_le_gen` (entries of
  `totalDegree ≤ D` over any variable type ⟹ `det.totalDegree ≤ D·d`, generalizing `ScratchGoodAnchor.det_totalDegree_le`)
  + the per-layer caps `coordPoly_totalDegree_le`/`LPoly_totalDegree_le` (`≤ 1`),
  `gramQuadPoly_totalDegree_le`/`QPoly_totalDegree_le`/`entryPoly_totalDegree_le` (`≤ 2`) ⟹
  **`pencilDetPoly_totalDegree_le : totalDegree ≤ 2·d`** (det of `d×d` quadratic-entry matrix, `D=2`).
- **B-ii (the explicit composition):** **`beta_count_closed`** combines `badHgood_count_le` + `pencilDetPoly_totalDegree_le`
  + `ScratchIncr4b.bad_anchor_card_le_hgood` (`β ≤ #{¬hgood}+2`) into the full **`β·|K| ≤ 2d·|V| + 2·|K|`** (density
  `β/|V| ≤ 2d/q + 2/|V| = O(d/q)`). The cross-module `Classical.propDecidable` mismatch on the `{¬hgood}` filter is bridged
  by `convert … using 2 <;> congr!` (the instances are subsingletons); no longer deferred.
- **β CLOSED modulo ONLY (i): non-vacuity `hgood`** (∃ good anchor for `u≠v` = distinct radicals — increment-4 item **NV**,
  the lone deep remaining piece; carried as the `t₀₀` hypothesis of `beta_count_closed`/`pencilDetPoly_ne_zero`). Items
  (ii) Nat-composition and (iii) `totalDegree ≤ 2d` are now DONE (above). [historical: (ii)/(iii) were tagged
  deferred/optional; both landed 2026-06-26.]

**▶▶▶ C-corr DONE (2026-06-26, `ScratchIncr4c.lean`, all axiom-clean) — the bridge's `corr=0` is folded into `β`.** The
bridge `ScratchBridgeD.jointIsoCount_ne_of_chiSep_pair` carries `hcorru/hcorrv` (`¬(Q(t−u)=0 ∧ Q(t₀−u)=0)` ∀ probe `t`).
A good anchor with `Q(t₀−u)≠0` discharges it for ALL `t` (`corr_zero_of_anchor` — the second conjunct is false). The price
is two quadric loci `{t₀:Q(t₀−u)=0}`,`{t₀:Q(t₀−v)=0}`, each counted by the SAME SZ engine on the already-built `QPoly`
(`QPoly_ne_zero` + `qZero_count_le : #{Q(t₀−c)=0}·|K| ≤ 2·|V|`, via `QPoly_totalDegree_le ≤ 2`). Capstone
**`beta_full_count_closed`**: the FULL good-anchor predicate `hnz ∧ hgood ∧ hPu ∧ hPv ∧ Q(t₀−u)≠0 ∧ Q(t₀−v)≠0` has bad-set
**`β_full·|K| ≤ (2d+4)·|V| + 2·|K| = O(d/q)`** (union bound: `beta_count_closed` + 2·`qZero_count_le`). So `corr` is no
longer a separate inc-5 worry — the matching's good-anchor locus already excludes it, at no asymptotic cost.

**▶▶▶ C-basis DONE (2026-06-26, `ScratchIncr4c.lean`, axiom-clean) — the bridge's `hv`/`hw` discharged from nondegeneracy.**
`exists_orthoAnisotropic_basis`: a nondegenerate (`(associated Q).SeparatingLeft`) form over a finite-dim space (char ≠ 2)
has an **orthogonal basis of anisotropic vectors** — exactly the `vb`/`hv : (associated Q).IsOrthoᵢ vb`/`hw : ∀ i, Q(vb i)≠0`
that `jointIsoCount_ne_of_chiSep_pair` carries. Via Mathlib `LinearMap.BilinForm.exists_orthogonal_basis` (diagonalize) +
`IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft` (a null diagonal vector ⟹ left radical, ⊥ by nondeg) +
`associated_eq_self_apply` (`(associated Q)(vb i)(vb i)=Q(vb i)`). Plus the **project-native bridge**
`associated_separatingLeft_of_polarRad` (`polarRad Q = ⊥ ⟹ (associated Q).SeparatingLeft`, via
`polarRad_eq_bot_iff_separatingRight` + `two_nsmul_associated`), so the family's nondegeneracy — stated as `polarRad = ⊥`,
the project workhorse — feeds it directly. A `Q`-level fact (no anchor/probe). **So both bridge-input gaps (corr = C-corr,
`hv/hw` = C-basis) are CLOSED; the lone deep remaining inc-4 item is NV** (non-vacuity `hgood`, distinct radicals).

**▶▶▶ NV ALGEBRAIC HEART DONE (2026-06-26, `ScratchIncr4d.lean`, 4 axiom-clean lemmas) — the deep part.** `hgood` is
`∃ y z, polarRad(y•pairForm Q(t₀₀−u) + z•pairForm Q(t₀₀−v)) = ⊥`. Writing `a = t₀₀−u`, `b = t₀₀−v = a−w`, `w = v−u ≠ 0`:
- **NV-1 `polar_pencil_apply`** — `polar(y•pairForm Q a + z•pairForm Q b) s r = 4c·polar Q s r − 2y·polar(s,a)polar(r,a)
  − 2z·polar(s,b)polar(r,b)`, `c = yQa+zQb` (pure algebra on `polar_pairForm_apply` + form-level `polar_add`/`polar_smul`).
- **`pencil_radical_key`** — `s ∈ polarRad ⟹ (4c)·s = (2y polar(s,a))·a + (2z polar(s,b))·b` (invert the nondeg `polar Q`,
  from `polarRad Q = ⊥`).
- **NV-2 `polarRad_pencil_subset_span`** — `c ≠ 0 ⟹ polarRad ⊆ ⟨a,b⟩` (divide by `4c`).
- **NV-3 `polarRad_pencil_eq_bot`** (capstone) — nondeg `Q`, `y,z ≠ 0`, `c ≠ 0`, **`pairForm Q a b ≠ 0`** ⟹ the member is
  **nondegenerate**. Evaluate the radical equation at `r = a,b` ⟹ a `2×2` system in `(polar(s,a),polar(s,b))` with
  `det = 4yz·pairForm Q a b ≠ 0` ⟹ both vanish ⟹ `pencil_radical_key` ⟹ `s = 0`.
Key identity used: `pairForm Q a b = 4QaQb − polar(a,b)² = det(polar Q |_{⟨a,b⟩})`, so `pairForm Q a b ≠ 0 ⟺ ⟨a,b⟩` is a
**nondegenerate plane**. **So `hgood` reduces to: ∃ `a` with `pairForm Q a (a−w) ≠ 0` (nondeg plane through `w`) ∧
`Q(a),Q(a−w) ≠ 0` (anisotropic — gives `c≠0` and corr-kill) ∧ `a, a−w` independent.** ⚠ NB the **both-isotropic case is
genuinely excluded**: if `Q(a)=Q(a−w)=0` (hyperbolic plane) then `c=0` for ALL `y,z` and every member is degenerate
(radical ⊇ `⟨a,b⟩^⊥`, nonzero for `d>2`) — so NV-4 must deliver anisotropic generators, not merely a nondeg plane.
**▶▶▶▶ NV COMPLETE (2026-06-26, `ScratchIncr4d.lean`, 14 axiom-clean lemmas) — `hgood` non-vacuity fully discharged.**
- **NV-4 `exists_good_plane_anchor`** (∃ `a`: `Q a ≠ 0 ∧ Q(a−w) ≠ 0 ∧ pairForm Q a (a−w) ≠ 0`, for nondeg `Q`, `w≠0`,
  `finrank V ≥ 2`, `|K| ≥ 7`). Key simplification — the **degree-2** formula `pairForm Q a (a−w) = 4 Q a Q w − polar(a,w)²`
  (`pairForm_self_sub`). **NV-4a `exists_pairForm_self_sub_ne_zero`** (the geometric core): this is not identically zero in
  `a`, else `Q` is rank-≤1 (its polar would kill a nonzero `b ⊥ w`, found by `exists_ne_zero_polar_eq_zero` via rank-nullity),
  contradicting `polarRad Q = ⊥` — a clean degenerate-everywhere⟹contradiction argument, **no orthogonal-complement /
  totally-isotropic machinery needed**. **NV-4b** (counting): the three quadric loci `{Q a=0}`,`{Q(a−w)=0}`,`{pairForm=0}`
  each have `≤ 2·|V|/|K|` points (Schwartz–Zippel on `gramQuadPoly`/`QPoly`/the new `planeDiscPoly`, the last nonvanishing
  by NV-4a); their union has `< |V|` points for `|K| > 6`, so a common good `a` exists.
- **NV-5 + capstone `exists_hgood`**: `t₀₀ = a+u` (so `t₀₀−u = a`, `t₀₀−v = a−w`); pick `(y₀,z₀) = (1,1)` if
  `Q a + Q(a−w) ≠ 0`, else `(1,−1)` (then `c = 2 Q a ≠ 0`); NV-3 (`polarRad_pencil_eq_bot`) seals
  `polarRad(y₀•pairForm Q(t₀₀−u) + z₀•pairForm Q(t₀₀−v)) = ⊥` — exactly `pencilDetPoly_ne_zero`/`beta_full_count_closed`'s
  carried `hgood`.
**⟹ The entire increment-4 cleanup (B-ii, B-iii, C-corr, C-basis, NV) is now CLOSED.** The β bound is unconditional modulo
the family properties (nondeg `Q`, `finrank ≥ 2`, `|K| ≥ 7`). Next: **#1 corank tightening (✅DONE — capstone
`c0_le_threequarters_corank`, hq2 removed)** → **small-q tail** → **hK cleanup** → **increment 5** (matching assembly;
field/seam typing decision RESOLVED by concern #4). NB increment 5's per-anchor input is now the `_corank` capstone.

**▶▶ INCREMENT 5 — WHAT'S EXPECTED (the matching assembly + bridge wiring).** All inputs are now landed (`c`, `β_full`,
non-vacuity `hgood`, the bridge, C-corr/C-basis); increment 5 produces the separating base and discharges `ZProfileSeparates`:
1. **`c̄₀ < 1`:** `F = c·|V| + |V|·β_full`; plug `c = 15/16·|V|` (`good_anchor_fail_le_const`) + `β_full·|K| ≤ (2d+4)·|V|+2·|K|`
   (`beta_full_count_closed`, so `β_full ≤ (2d+4)|V|/|K| + 2`) ⟹ `c̄₀ = F/|V|² ≤ 15/16 + O(d/q) < 1` for `q ≳ d` (consistent
   with `q ≥ 256`). Pure arithmetic on the landed `fail_count_split`/`matching_F_bound`.
2. **ℕ-packaging + `exists_separating_base`:** take `F := ⌊c̄₀·|V|²⌋`, `ι = {(u,v):u≠v}` (`|ι| ≤ |V|²`), `W = V×V`. The
   hypothesis `|ι|·Fᵐ < |W|ᵐ ⟺ |V|²·c̄₀ᵐ < 1` holds at `m = O(d log q)`. Yields a matched base `P : Fin m → V×V` with
   `∀ u≠v, ∃ j, ¬fail (u,v) (P j)`. Per-pair good-anchor existence (so the bad set is a strict subset) = **`exists_hgood`** (NV).
   *(Sub-task: a `c̄₀ᵐ` smallness → ℕ inequality helper; the only genuinely-new combinatorics, ~`Nat.one_lt_pow`/log bound.)*
3. **`fail` ⟺ ¬(bridge separation):** define `fail (u,v) (t,t₀)` as the negation of the bridge capstone
   **`ScratchBridgeD.jointIsoCount_ne_of_chiSep_pair`**'s criterion. Its hypotheses are ALL now supplied: `χ(I_u)≠χ(I_v)` +
   config-nondeg (`I_u,I_v≠0`) from the criterion; `hcorru/hcorrv` (corr=0) from **C-corr** (`corr_zero_of_anchor`, free on good
   anchors where `Q(t₀−u),Q(t₀−v)≠0` — already in `beta_full_count_closed`'s good-anchor predicate); `hv/hw` from **C-basis**
   (`exists_orthoAnisotropic_basis`). Then `¬fail ⟹ jointIsoCount Q u {t,t₀} ≠ jointIsoCount Q v {t,t₀}` IS the bridge capstone.
   **★ Coordinate/field seam (the main wiring care, decide first — see top-of-doc PICK UP HERE):** the bridge + `ZProfileSeparates`
   live in `Fin(p^d)`/`ZMod p`; `c`/`c0`/`β`/NV live in abstract `[Field K]`/`V`. Recommended: lift the bridge+Crux to abstract
   `K` first (dissolves the seam + handles `q=pᵉ`), rather than the per-pair `affineE` relabel.
4. **Assemble `ZProfileSeparates`:** base `T := image of P` (the `≤ 2m = O(d log q)` points `{t_j, t₀_j}`); for each
   `u≠v`, the witnessing `j` gives `S = {t_j, t₀_j} ⊆ T` with `jointIsoCount Q u S ≠ jointIsoCount Q v S`, so
   `zProfileSeparates_of_zSep` (LANDED) ⟹ `ZProfileSeparates Q T`. Then Layer B (`ScratchCrux` + idx 1248) ⟹ the seal.

*Maintenance: this doc is the live proof target — keep §1's module map current as scratch modules port into the build, and
update §11's audit/spike outcomes + the §11.1 route decision as they resolve. Build history + superseded routes are frozen
in the archive (linked in the intro). Keep route-doc §9.9.18b/c the empirical anchor and this doc the proof target. Live
capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`PublicTheoremIndex.md:1248`); `VO⁻₄(3)` sealed
(`ScratchBM3Glue.vo4minus_seal`).*
