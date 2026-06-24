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
> deferred-decisions stage 1 (every decision real, IR-solver not yet run) the graph residue is **rigid or Cameron** —
> i.e. to discharge `hSmallAutThin` for the small-Aut non-geometric **schurian** rank-3 residue. The single `VO⁻₄(3)`
> instance is sealed (§1, `vo4minus_seal`); this section is the generalization program. **Scope:** the schurian residue only — the
> non-schurian wall is the IR-solver's job (separate thread, `project_option2_f2_gap`). `SchurianScheme` is *carried*
> (`orbitalScheme H`); whether it is a scope hypothesis or a citation obligation is settled in **AUDIT-S (§11.0)**, not by a
> bespoke proof.
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
- **AUDIT-A — CascadeAffine's `ZMod p` dependence (gates the abstract-field refactor, §11.1-field).** Read `CascadeAffine.lean`
  + `GaussCount.lean` and catalogue every essential use of `ZMod p` that is NOT already abstract over `[Field K]`:
  the scheme index `Fin (p^d)`, `affineE`, the affine/similitude group, `frobPerm` (field automorphisms), and the
  `Invertible (2:ZMod p)` / `ringChar ≠ 2` assumptions. **Question to answer:** can the whole chain be restated over a
  variable `[Field K] [Fintype K] [DecidableEq K]` (with `V := Fin d → K`, scheme on `Fin (Fintype.card K ^ d)`,
  `frobPerm := FiniteField.frobenius`)? Mathlib's `quadraticChar`/`gaussSum` API is already abstract-finite-field, so the
  toolkit side is likely cheap; the scheme side is the risk. **Deliverable:** a refactor cost estimate + a go/no-go on
  abstract-`K`. If GO, the "all q prime" and "prime powers" line items MERGE into one.
- **AUDIT-W — the exact Witt statement needed (gates Route 3, §11.1-kernel).** Pin down precisely which form of Witt's
  theorem the frame-rigidity argument consumes (Witt extension/transitivity for finite-field quadratic forms; the
  hyperbolic-decomposition). Check Mathlib for partial coverage (`QuadraticForm.Isometry`, `Matrix.... `, the
  `BilinForm` isometry API). **Deliverable:** a Mathlib-contribution size estimate for Witt, and a yes/no on "Route 3's
  kernel proof is uniform over `q` and reusable across the polar families." This is the number that decides Route 1 vs 3.

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

### 11.2 Risk-gate — prove the math before the engineering

The count-assembly bridge, form-bundling, and field generalization are all **low-risk engineering that only pays off if
the uniform kernel has a proof.** So the ordering is risk-gated, not merely dependency-ordered:

1. **GATE (research):** a paper-level, probe-validated argument for the chosen kernel route (SPIKE-K outcome promoted to a
   convincing uniform proof sketch). **Nothing heavy is built until this gate passes.**
2. Then the engineering lifts (bridge, bundling, field) and the per-family sweep.

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
3. **`q` prime all `(ε,m)` — CONDITIONAL, not the default.** If AUDIT-A is GO and SPIKE-K shows the inversion is
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

This is the **load-bearing** step (it actually discharges `hSmallAutThin`). Its *target statement* is pinned up front in
**AUDIT-S (§11.0)** — §11.6 EXECUTES that seam, it does not design it (a wrong target shape wastes the kernel, so the
design must precede the families, not follow them).

- **Cite Ponomarenko** for (a) the 1-dim cyclotomic slice. (citation)
- **Execute the classification transport (target fixed by AUDIT-S).** Skresanov/CFSG gives "any small-Aut non-geom
  schurian rank-3 scheme `≅ affineScheme (similitudeGroup Q)` for one of these `Q`, **up to scheme equivalence**." The
  non-trivial Lean glue = transporting the *abstract* residue to *your concrete* `Q` (the iso/up-to-equivalence matching),
  then composing the per-family `reachesRigidOrCameron_viaIsotropySeparates_wittFree`. Real glue, low math risk. (The
  `wittFree` capstone already removed `OrbitIsIsotropyClass`/Witt from each family's critical path — a real simplification
  vs. the older framing in the archive.)
- **`SchurianScheme` — per AUDIT-S's verdict:** if it is a **scope hypothesis**, it is free here; if it is an
  **obligation** (prove the stage-1 residue is schurian), it is discharged by **citation** (CFSG/Skresanov), NOT a bespoke
  Lean proof. Resolve which in AUDIT-S before this step.
- **Assemble:** per-family results + classification ⟹ `hSmallAutThin` ⟹ the **full** seal modulo `{G3 + cited}` (no
  `modulo {family}` residual — endpoint discipline, §11 header).

### 11.7 Consolidated probe / confirmation checklist (gates, in order)

| # | Probe / confirm | Gates | Risk if skipped |
|---|---|---|---|
| AUDIT-S | Skresanov seam target statement + `SchurianScheme` = hypothesis vs citation | every family's target (§11.6) + AUDIT-W | grind families toward the wrong statement |
| AUDIT-A | CascadeAffine `ZMod p` dependence → abstract-`K` go/no-go | field-gen vehicle (§11.3-4) | build GaloisField needlessly (big) |
| AUDIT-W | exact Witt statement + Mathlib coverage | Route 1 vs 3 (§11.1) | mis-price the route fork |
| SPIKE-K | **char-sum-FREE probe:** coarse-invariant `(sqclass det G, level-pattern)` injectivity + base-size scaling over `(ε,m,q)`, **`q ≥ 5`**; + paper route-comparison | kernel route + the §11.2 gate | build on an unprovable kernel; miss the `q≥5` info-loss |
| base-O(log n) | confirm `|T_Q| = O(d + log q) = O(log n)` (not the false `≈ d+2`) | §11.3-5 + capstone `bound` | base silently outside the individualization budget |
| GATE | promote SPIKE-K winner to a convincing uniform proof sketch | ALL heavy builds | months of misdirected formalization |
| HUNT | citation search for (e) half-spin / (f) Suzuki-Tits WL-dim/base | §11.4 bespoke-vs-cite | redundant bespoke proofs |
| descent | confirm the `R' → ℤ` descent (char-0 `R'` w/ primitive `p`-th root) for `F(D,c)` | §11.3-1 | a silent gap in the closed form |

### 11.8 Net ordering

**`AUDIT-S` (seam target FIRST)** → `AUDIT-A` + `AUDIT-W` (parallel) → **`SPIKE-K`** (coarse-invariant injectivity at
`q≥5` + base scaling) → **GATE** → [if Route 1: count-assembly bridge incl. `R'→ℤ` descent; if Route 3: build Witt] →
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
