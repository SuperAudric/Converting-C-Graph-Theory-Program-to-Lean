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
> **▶▶ CURRENT STATE — read this, then §13 STATUS, then `ScratchPairSep.lean` (PICK UP HERE).** The entire generalization is
> reduced (axiom-clean, `ScratchCrux.lean`: **D1** + **D2-bridge** + `isotropySeparates_of_zProfileSeparates`) to the single
> predicate **`ZProfileSeparates Q T`** (the joint `Z(S)`-profile separates pivots at a bounded base = **D3d**). Two big
> developments since:
> - **D3d is WEIL-FREE** (the exact-vs-Weil question is RESOLVED in favour of *no Weil*). The seal's observable is the
>   **pair** joint-isotropic count `Z_u({t,t'})` (NOT the singleton — `Z_u({t})` is binary, a verified correction). Its
>   separating invariant `χ(det G₂(u;t,t₀))` is `χ` of a **quadratic** in the probe, and the relevant per-pair character sum
>   **factors through scalar values into additive Gauss sums** — proved general as `pairCharSum_factor_gen`. Probe
>   `Probe_D3dPairCount`: `c₀ ≤ 0.49 < 1` bounded, anchor existence robust (`sep@1anchor ≈ 100%`).
> - **Lean build underway in `ChainDescent/ScratchPairSep.lean`** (axiom-clean, NOT in build): **increment 1** (Gauss bridge
>   `quadChar_addChar_sum` + factoring `pairCharSum_factor_gen`) and **increment 2 foundation** (`pairForm`/`pairForm_apply`/
>   `detG2_eq_pairForm` = the pair invariant is a quadratic form at a shift; `pairCombine` = two-pivot integrand in
>   form+linear+const shape; `sum_addChar_quadForm_translate`) are DONE. **EXACT NEXT STEP = finish the `M(y,z)` closed form**
>   (complete the square via `sum_addChar_quadForm_linear` at `r=1` + evaluate via `sum_addChar_quadForm` + the degenerate
>   locus), then the `c₀<1` bound (increment 3, one ℂ-magnitude step) → anchor existence → averaging ⟹ `ZProfileSeparates`.
>   Full detail + the remaining-increment math: §13 (the "INCREMENT 2 FOUNDATION" block + the "CORRECTION" block, which
>   records why the singleton route was abandoned — do NOT re-walk it).
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
  so `|M|=q^{d/2}`). Open tail = the degenerate-`(y,z)` locus (axes ∪ conic = main term) + increment-3 `c₀`. See §13.
- **`ScratchMatching.lean`** (NEW 2026-06-24, compiles axiom-clean, NOT in build) — the **increment-4/5 combinatorial core**:
  **`exists_separating_base`**, the matching-trick first moment as a pure finite-counting theorem (`fail : ι → W → Prop`,
  `∀g #{w:fail g w}≤F`, `|ι|·Fᵐ<|W|ᵐ ⟹ ∃ base P:Fin m→W, ∀g ∃j ¬fail g (P j)`). Consumes the single analytic input `c̄₀<1`
  (instantiate `W=V×V`, `ι={(u,u'):u≠u'}`) ⟹ separating base of size `O(d log q)`; anchor existence dissolves (anchor = the
  other matched coordinate). See §13's "MATCHING TRICK CONFIRMED" block.
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
- **(e) half-spin** — spinor geometry, different incidence. Medium–high.
- **(f) Suzuki–Tits** — the exceptional outlier; ⚠ **not "small"** (the `Sz(q)` geometry is genuinely special).
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

### 11.6 Step group 4 — structural wiring (citations + glue) — DESIGN THE SEAM EARLY

This is the **load-bearing** step — it produces the rigid-or-Cameron conclusion for the schurian residue (NOT, per
AUDIT-S finding 3, a "discharge of `hSmallAutThin`": the per-family `wittFree` route is a *parallel* seal route, and the
seam is a cited classification case-split that routes the abstract residue `S` to its concrete `affineScheme(Q)`). Target
pinned by **AUDIT-S (§11.0)**; this step executes it.

- **Cite Ponomarenko** for (a) the 1-dim cyclotomic slice (→ `reachesRigidOrCameron_affineSlice`). (citation)
- **The seam vehicle (AUDIT-S finding 3, recommended option (a)).** Build the cited reduction capstone
  `reachesRigidOrCameron_viaSchurianRank3Affine`: a single carried predicate (Skresanov/Liebeck/Cameron) whose conclusion
  is **the seal disjunction for the residue `S` directly** — its forms-graph obligation discharged by the per-family
  `IsotropySeparatesAtBase` + `reachesRigidOrCameron_viaIsotropySeparates_wittFree`. This carries the scheme-iso/transport
  *inside* the citation, so **no new `SchemeEquiv` infrastructure is needed** (option (b) — a real `SchemeEquiv` + a
  "seal disjunction transports along scheme iso" lemma — is the fallback if a cleaner separation is wanted). Real glue,
  low math risk; the `wittFree` capstone already removed Witt from each family's critical path.
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
- **Remaining for increment 2 (only the degenerate locus):** the **degenerate-`(y,z)` locus** where `F` drops rank — by the
  verified fact that *every* `pairForm Q a` is degenerate (`a ∈ radical`), this locus is the whole axes `{y=0}∪{z=0}` plus the
  pencil's discriminant conic, and is the probe's `|T|` MAIN TERM (not an edge case). Then sum over `(y,z)` (the
  `pairCharSum_factor_gen` outer sum) ⟹ the increment-3 `c₀` bound. **The nondegenerate-locus closed form is DONE.**

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

*Maintenance: this doc is the live proof target — keep §1's module map current as scratch modules port into the build, and
update §11's audit/spike outcomes + the §11.1 route decision as they resolve. Build history + superseded routes are frozen
in the archive (linked in the intro). Keep route-doc §9.9.18b/c the empirical anchor and this doc the proof target. Live
capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`PublicTheoremIndex.md:1248`); `VO⁻₄(3)` sealed
(`ScratchBM3Glue.vo4minus_seal`).*
