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
> **▶▶▶ THE LIVE FRONTIER = §11** — generalizing from the single sealed instance to the full schurian residue
> (`hSmallAutThin` for every small-Aut non-geometric schurian rank-3 family, modulo `{G3}`). §11 is self-contained
> (endpoint discipline, the kernel reframe, the route fork, the gated ordering). The one open research problem is the
> **uniform coarse-invariant injectivity kernel** (§11.1); everything else is engineering or citation.
>
> **▶ Witt is OFF the seal's critical path** (`relationRefinesIsotropy_similitude` discharges the bridge's easy half
> Witt-free). Witt returns only as *one option* for the generalization's kernel extraction (Route 3, §11.1) — gated by
> AUDIT-W, not mandatory.

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
- ⚠ `FormsGraphConcrete.lean` holds the OLD `QProfileSeparatesAtBase` / M3-reduction route — superseded by Lemma A/B (archive).

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
> general Weil, that is a contained sub-build, else fall back to Route 3 (Witt). **Next = begin the crux in Lean: state
> `IsotropySeparatesAtBase` for the constructed `{frame ∪ probes}` base + the (R1)+(R3) reduction scaffold, isolating the
> crux as the single open lemma.**

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

*Maintenance: this doc is the live proof target — keep §1's module map current as scratch modules port into the build, and
update §11's audit/spike outcomes + the §11.1 route decision as they resolve. Build history + superseded routes are frozen
in the archive (linked in the intro). Keep route-doc §9.9.18b/c the empirical anchor and this doc the proof target. Live
capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (`PublicTheoremIndex.md:1248`); `VO⁻₄(3)` sealed
(`ScratchBM3Glue.vo4minus_seal`).*
