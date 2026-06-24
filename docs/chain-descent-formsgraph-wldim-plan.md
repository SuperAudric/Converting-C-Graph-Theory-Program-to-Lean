# Proof plan — bounded WL-dimension for the affine forms-graph families (the seal's node-4 content)

> **What this is.** A concrete proof plan for the sharpened open frontier (route-doc §9.9.18b/c): prove **bounded
> Weisfeiler–Leman dimension** (= bounded individualization base ⟹ `hSmallAutThin`) for the affine forms-graph rank-3
> SRG families that constitute node-4-for-the-seal — affine polar `VO^ε_{2m}(q)`, alternating forms, half-spin, and
> Suzuki–Tits. By the Skresanov reduction (§9.9.18) these (plus the cited 1-dim cyclotomic slice) are the *entire*
> small-Aut non-geometric schurian rank-3 residue; the probe (`Probe_FormsGraphs`, §9.9.18c) shows they shatter at a
> bounded base. This plan turns that empirical shatter into a proof target with a landed engine and one crux lemma.

---

## STATUS (read first)

> **▶▶▶ WITT REMOVED FROM THE CRITICAL PATH (2026-06-20, axiom-clean, full build green).** The capstone's Witt
> deliverable `OrbitIsIsotropyClass` ("the heaviest piece", Mathlib-absent) is **off the seal's critical path.**
> Ported into `CascadeAffine.lean §OrthogonalForm` (`PublicTheoremIndex.md:1243-1248`), all axiom-clean: the easy-half
> predicate `RelationRefinesIsotropy` is **discharged Witt-free outright** (`relationRefinesIsotropy_similitude`, no
> hypothesis, via similitude-invariance `isoClass_similitude_invariant` + `affineScheme_relOfPair_eq_iff`); the
> separation bridge `separatesAtBase_of_isotropySeparates_weak` needs only that easy half (fiberwise partition); and
> the new capstone **`reachesRigidOrCameron_viaIsotropySeparates_wittFree`** seals the `VO^ε` residue carrying ONLY a
> bounded base + the Gauss target `IsotropySeparatesAtBase Q T`. The hard Witt direction is needed only for the
> cosmetic rank-3 identification, which the seal (working at any rank) never uses. **CONSEQUENCE: discharging the M3
> route-1 kernel `QProfileSeparatesAtBase` seals `VO⁻₄(3)` modulo `{G3}` ALONE.** Everywhere below that says "the
> capstone also needs `OrbitIsIsotropyClass` (Witt, a separate parallel track)" is SUPERSEDED — Witt is no longer the
> seal's obligation. (The Witt-carrying `reachesRigidOrCameron_viaIsotropySeparates` / `separatesAtBase_of_isotropySeparates`
> are kept axiom-clean but superseded.)
>
> **▶▶▶ STEP-4 BUILD UNDERWAY (2026-06-20) — the live frontier is §10.8 (full milestone plan); start there.** The
> route-1 step-4 inversion is being built via the **Lemma A / Lemma B split** (§10.6): Lemma A = "isotropic-incidence
> count = explicit Gram-function (nondeg configs)", Lemma B = "counts recover `u`", composing to prove
> `IsotropySeparatesAtBase Q T₉` directly (the live route — supersedes the `QProfileSeparatesAtBase` framing). **Landed,
> axiom-clean (WIP scratch, NOT in build — see §10.5):** A-M1, A-M2 (`ScratchLemmaA.lean`); B-M1, B-M2-bridge
> (`ScratchLemmaB.lean`). **★ A-M3 ✅ COMPLETE via ROUTE B (2026-06-21, all axiom-clean):** `levelset_fourier` →
> `levelset_fourier_prod` → `levelset_fourier_split` (D1 bulk) → `s0_boundary_collapse` (`s=0` → `q^d`) → **`levelset_count_eq`**
> (the assembled closed form: `count·q^{m+1} = |V| + ∑_{s≠0}…` modulo the two Gauss sums). **★ A-M4a ALL GAPS 1–5 DONE
> (2026-06-21, axiom-clean) — config side ASSEMBLED:** `configForm`/`polar_configForm_single`, `configForm_nondegenerate`,
> `configForm_exists_orthoBasis`, `configGaussSum_eval`, `prod_quadChar_eq_det` (gap-5 crux), and the basis-free wrap-up
> **`configGaussSum_eq_det`** (`∑_ρ ψ(s·QR ρ) = χ(s)^n·χ(D)·gaussSum^n`, config-dependence only through the invariant `D`).
> **▶▶▶ `VO⁻₄(3)` SEALED (2026-06-21, axiom-clean) — B-M3 + WIRING + SEAL ALL DONE via Approach 1.** `vo4minus_seal`
> (`ChainDescent/ScratchBM3Glue.lean`) proves the Witt-free capstone's conclusion for the bundled minus-form
> `Qbun = x₀x₁+x₂²+x₃²` at the size-9 base `T₉`, modulo cited `{G3}` — carrying NO `hSmallAutThin`, NO Witt. Chain:
> `isoSep : IsotropySeparatesAtBase Qbun T₉` (B-M1 `incidence_agree_V` → restricted counts agree → bridge
> `restricted_bridge` → decided `sigF_injective` over `Finset (Fin 81)`, ~20s kernel `decide`, no `native_decide`) →
> `reachesRigidOrCameron_viaIsotropySeparates_wittFree`. All 4 scratch modules (ScratchLemmaA/B + ScratchBM3Bridge/Glue)
> axiom-clean `[propext, Classical.choice, Quot.sound]` (verified `lake env lean` + `lake build` oleans). **ONLY remaining
> step = PORT** the 4 scratch modules into `build.sh`/`lakefile.toml` + regen `PublicTheoremIndex.md` + green build (no new
> math). See §10.13 completion block. Tier-2 (M5 all q/d, families d/e/f, Skresanov, char-2) unchanged. The A-side
> (`configGaussSum_eq_det`) is the generalization asset for M5, not on this instance's critical path.
> **▶ The full Tier-2 generalization roadmap (revised) is now §11** — run `AUDIT-A`/`AUDIT-W`/`SPIKE-K` + the §11.2
> research GATE before any heavy build; the kernel's Route-1-vs-Route-3 choice and the abstract-`[Field K]` field
> generalization are the two pivotal decisions.
>
> **▶▶ HANDOFF (2026-06-18) — READ §9 (milestone roadmap) + §10 (the kernel handoff) FIRST; the notes below are the
> landed history.** State of the Gauss work: **M0–M2 DONE, M3 reduction DONE, all axiom-clean, full build green.** The
> ENTIRE remaining Gauss-work content is ONE open predicate **`QProfileSeparatesAtBase Q T`** (`FormsGraphConcrete.lean`)
> = "fine isotropy-counts at the symmetry-broken base `T = frameBase∪{2e₃}` recover the `Q`-profile." It is
> **probe-validated (`VO^-_4(3)`, 81/81) but UNPROVED** — the genuine uncited crux. `isotropySeparates_of_qProfileSeparates`
> + `coords_determine` reduce the seal to it; M4 is then pure wiring but **BLOCKED** on it (carrying it as a certificate
> is RULED OUT by the quality bar). **The two viable routes to discharge it are fully expanded in §10:** **(1)** explicit
> Gauss/incidence computation of the joint isotropic counts `Z(S)` (Witt-free, all toolkit present, RECOMMENDED) — the
> open step is a concrete character-sum inversion (§10.1 step 4); **(3)** structural perp-graph + Witt frame-rigidity
> (cleaner but blocks on building Witt). Key constraint (M3): `isoClass` is **shell-blind**, so the pointwise-count
> machinery (M2 `multiCharSum`) is off-path — the recovery is the joint `Z(S)`. Witt `OrbitIsIsotropyClass` (B.1c-i) is a
> separate parallel track the capstone also needs.
>
> **★ REFORMULATION LANDED (2026-06-18, axiom-clean, build green) — the frame-locked predicates are SUPERSEDED;
> the live target is now count-injectivity at a SYMMETRY-BROKEN base.** New block in **`CascadeAffine.lean`
> §OrthogonalForm** ("Stage B.1c (CORRECTED)"), all three decls `[propext, Classical.choice, Quot.sound]`:
> - **`SeparatesAtBase Q T`** — the corrected separation predicate: one-round difference-relation count-injectivity
>   at an *arbitrary* base `T` (the landed engine `discrete_affineScheme_of_twoRoundDiffSeparates` already accepts
>   any `T`; nothing was frame-specific). `SimilitudeFrameSeparates Q` = the mis-shaped `T := frameBase` instance.
> - **`reachesRigidOrCameron_viaSymmetryBrokenBase Q T hcard hsep`** — the seal from any bounded base `T` with
>   `SeparatesAtBase Q T`. Drops `coords_determine` / `Q`-profile recovery entirely (wrong for minus-type). NO `hSmallAutThin`.
> - **`IsotropySeparatesAtBase Q T`** (the **Gauss endpoint**) — pure isotropy-class count-injectivity at `T`, NO
>   opaque relations; **`separatesAtBase_of_isotropySeparates`** (Witt bridge, arbitrary `T`) lifts it to
>   `SeparatesAtBase`; **`reachesRigidOrCameron_viaIsotropySeparates`** composes to the seal.
>
> The three frame-locked predicates (`SimilitudeFrameSeparates`, `CountsDetermineFrameQ`, `IsotropyCountsRecoverFrameQ`)
> are tagged **⚠ SUPERSEDED** in-source (kept, axiom-clean, compose — but unprovable as stated for `VO^-`). **After
> this reformulation the open content is exactly two inputs:** `OrbitIsIsotropyClass Q` (Witt, B.1c-i) and a concrete
> **`IsotropySeparatesAtBase Q T`** for a symmetry-broken `T` (`≈ d+2`, e.g. `frameBase ∪ {p}`) — the Gauss build's
> target. **★ k-fold count assembly LANDED (2026-06-18, axiom-clean): `countk_eq_charsum` + `countk_eq_sum_charsum`
> in `ScratchGauss.lean`** — the count `#{x:∀j, f_j x=c_j}·qᵏ = ∑_{r:ι→F} ψ(−∑r_j c_j)·∑_x ψ(∑r_j f_j x)`, whose inner
> sum (with `f_j x = Q(x−t_j)`) is `sum_addChar_multiQuad`. **★ quadratic specialization LANDED (2026-06-18, axiom-clean):
> `sum_addChar_multiQuad_zero` (the `R=∑r_j=0` boundary, reducing to a linear form) + `sum_addChar_linearMap`
> (`∑_z ψ(φ z)=|V|·[φ=0]`)** — so the inner sum `S(r)` is evaluated for ALL `r` (`R≠0`→`multiQuad`, `R=0`→these two),
> and with `countk_eq_sum_charsum` the multi-point Q-count is in CLOSED FORM. **★ inclusion–exclusion engine LANDED
> (2026-06-18, axiom-clean): `count_pi_setValued`** (`#{z:∀j, h_jz∈A_j} = ∑_{c∈∏A_j} #{z:∀j, h_jz=c_j}`, value-SET
> counts = sum of value-POINT counts) — with `h_jz=Q(z−t_j)` it turns isotropy-class counts (each = a `Q`-value-set)
> into the pointwise counts the toolkit closes. The Mathlib-only Gauss toolkit is now COMPLETE
> (A/A2/Ak/B/C/D1/multiQuad/multiQuad-zero/linearMap/setValued). **★ isotropy DICTIONARY LANDED (2026-06-18, axiom-clean, in
> CascadeAffine §OrthogonalForm): `isoClass_eq_zero_iff` (class 0 ⟺ `w=0`), `isoClass_eq_two_iff` (class 2 ⟺
> anisotropic `Q w≠0`, pure value condition), `isoClass_eq_one_iff` (class 1 ⟺ `w≠0 ∧ Q w=0`), `isoClass_ne_two_iff`
> (coarse split ⟺ `Q w=0`).** These characterize each isotropy class as a `Q`-value-set condition (only class 0/1 is
> origin-refined). **★ PORT LANDED (2026-06-18, build green): the toolkit is now
> `ChainDescent/GaussCount.lean`** (a real `namespace ChainDescent` leaf, Mathlib-only, registered in `build.sh` +
> `lakefile.toml`; the former `ScratchGauss.lean` deleted). 18 axiom-clean lemmas. **★ CONSUMER MODULE CREATED + step (1) LANDED
> (2026-06-18, build green): `ChainDescent/FormsGraphConcrete.lean`** (imports `GaussCount` + `CascadeAffine`,
> registered in `build.sh` + `lakefile.toml`) with **`count_transport`** (axiom-clean) — the count transport
> `Fin (p^d) ↔ V` along `affineE`, moving the `IsotropySeparatesAtBase` counts into the vector space `V = Fin d → ZMod p`
> where the Gauss point counts live. **★ step (2) value-set part LANDED (2026-06-18,
> axiom-clean): `qvalue_count_transport`** — chains `count_transport` + `count_pi_setValued` into one bridge:
> `#{z : ∀j, Q(z̄−t_j)∈A_j} = ∑_{c∈∏A_j} #{x : ∀j, Q(x−t_j)=c_j}`, landing the affine `Q`-value-set count on the
> pointwise `Q`-counts the Gauss toolkit closes. **★ M0 PROBE DONE (2026-06-18, `/tmp/m0probe.py`): COARSE counts
> SUFFICE (no origin correction needed) + base `T = frameBase ∪ {2e₃}` (size 6) has injective Q-profile ⟹ M3 = "counts
> recover Q-profile → `coords_determine`".** See §9 (milestone roadmap) for the full M0–M5 plan.
> **★ M1 DONE (2026-06-18, axiom-clean): conversion core** (`isotropy_count_transport`, `isoSetOf`/`qSetOf` +
> `mem_isoSetOf_iff`, `coarse_eq_sum_iso`). **★ M2 DONE (2026-06-18, axiom-clean): Fourier hinge** —
> `multiCharSum_eq_sum_count` + `sum_addChar_quadForm_smul_ne_zero` (note: M3 found `multiCharSum` needs *pointwise*
> counts, which `isoClass` doesn't give — shell-blind; reusable but off the kernel path). **★ M3 REDUCTION DONE
> (2026-06-18, axiom-clean): `isotropySeparates_of_qProfileSeparates`** reduces the seal target to one predicate
> `QProfileSeparatesAtBase` (counts ⟹ Q-profile) via `coords_determine`. **KERNEL `QProfileSeparatesAtBase` OPEN** = the
> joint `Z(S)`-incidence extraction (the genuine uncited crux; see §9 M3). NEXT = M3-kernel (heavy) **or** M4 carrying it.
>
> **★ GAUSS BUILD (B.1c-ii) — the affine-quadric POINT-COUNT FORMULA LANDED (2026-06-18, axiom-clean).** Built in
> **`GraphCanonizationProofs/ChainDescent/ScratchGauss.lean`** (WIP module; imports ONLY Mathlib so it builds in
> isolation, cheap; verified via `lake env lean ChainDescent/ScratchGauss.lean`, all decls
> `[propext, Classical.choice, Quot.sound]`). Mathlib has the pieces (`gaussSum_sq`, `quadraticChar_card_sqrts`,
> `equivalent_weightedSumSquares`, `AddChar.sum_mulShift`) but NOT the assembled affine-quadric point count — now built.
> **DONE (the full exponential-sum core + the assembled count):** Brick A `count_eq_charsum` (count = double char sum),
> B1 `sum_addChar_sq` (`∑ψ(x²)=gaussSum`), B2 `sum_addChar_smul_sq` (`∑ψ(a·x²)=χ(a)·gaussSum`), helper `addChar_sum`,
> B3 `sum_addChar_quadForm` + basis-explicit `sum_quadForm_eval` (`∑ψ(Qx)=(∏χwᵢ)Gᵈ`, the multivariable core), scaling
> `sum_addChar_quadForm_smul` (`∑ψ(s·Qx)=χ(s)^d·∑ψ(Qx)`), and **Brick C `card_quadForm_eq`** — THE point count:
> `#{x:Qx=c}·q = #V + (∑_{t≠0} ψ(−tc)·χ(t)^d)·∑_xψ(Qx)`. **ALSO DONE:** D1 `sum_addChar_quadForm_linear`
> (complete-the-square `∑ψ(r·Qw+polar Q w a')=ψ(−r⁻¹Qa')·∑ψ(r·Qw)`), A2 `count2_eq_charsum` (two-condition count),
> helpers `quad_sub`/`polar_sum_right`, and **MULTI-POINT `sum_addChar_multiQuad`** (`∑_z ψ(∑ⱼrⱼQ(z−tⱼ)) =
> ψ(const)·∑_z ψ(R·Qz)`, `R=∑rⱼ≠0`, collapsing to D1) — the engine for the symmetry-broken-base count. **The Gauss
> toolkit (A/A2/B/C/D1/multiQuad) is now COMPLETE** (13 axiom-clean lemmas); remaining = the k-fold count assembly +
> the injectivity argument at the symmetry-broken base.
>
> **⚠ KEY FINDING (2026-06-18) — the PAIRWISE plan for Brick D FAILS; corrects (ii) below + §3.** Computing the
> pairwise common-isotropic-neighbour count via A2+D1+Gauss collapse: `#{w:Qw=0 ∧ Q(w−a)=0} = q²+S(1)/q` (d=4),
> **INDEPENDENT of the anisotropic shell of `a`** (VO^-_4(3): 6 for both Qa=1 and Qa=2). Reason: a similitude of
> factor μ preserves the cone {Q=0} and maps shell {Q=1}→{Q=μ}, so any count from the cone + a SINGLE point is
> similitude-invariant ⟹ shell-blind. So the §3 Route-A "hyperplane-section count depends on χ(Qa)" claim is **WRONG**
> (χ(Qa) cancels). **Recovery MUST use the JOINT count over the WHOLE frame at once** (the fixed frame breaks the
> similitude symmetry: a `g` moving `a` across shells also moves the `eᵢ`) — a `(d+2)`-fold char sum (A2 generalized;
> each inner sum via D1). **NEXT:** (i) RESOLVE whether `IsotropyCountsRecoverFrameQ` (a bounded-round joint isotropy
> count) is true / correctly shaped — probe shows the SCHEME discretizes (full 2-WL), but the predicate is one specific
> joint count; verify it suffices before the heavy build. (ii)–(iv) the joint count, C-even, bridge. **[(i) NOW
> RESOLVED — see the box immediately below; it changes the plan.]**
>
> **⚠⚠ OPEN QUESTION RESOLVED — the standard-frame B.1c predicates are MIS-SHAPED; fix = symmetry-broken base
> (2026-06-18, finite probe over VO^ε_4(3), `/tmp/isoprobe*.py`).** Four findings:
> 1. **`IsotropyCountsRecoverFrameQ` / `CountsDetermineFrameQ` / `SimilitudeFrameSeparates` are FALSE for VO^-_4(3)**
>    at the standard frame `{0,e₀,…,e_d}`: `u=(0,0,1,2)`, `u'=(0,0,2,1)` have IDENTICAL one-round isotropy/relation
>    counts to the frame but different Q-profiles (`Q(u−e₂)=1` vs `2`). Cause: `Q=x₀x₁+x₂²+x₃²` is symmetric in
>    `x₂,x₃`; the count (coarser than orbits) is blind to it at the symmetric frame. (VO^+_4(3) is FINE at the
>    standard frame — the defect is minus-type frame symmetry.)
> 2. The SCHEME genuinely **discretizes** (iterated 1-WL from the frame → 81 singletons in 2 rounds, separates `u,u'`).
>    Bounded WL-dim HOLDS; only the one-round-count-at-symmetric-frame predicate is wrong. Probe `Probe_FormsGraphs`'s
>    base-5 for q=3 was an *iterated*-WL base, not a one-round-count base.
> 3. **The project engine `discrete_of_kRoundRelationSeparates` consumes exactly the ONE-ROUND count** (CascadeAffine
>    :1918-1924; k-independent — k only proves the count is a `warmRefine` invariant). So it CANNOT discharge VO^- at
>    the standard frame even though `warmRefine` IS `Discrete` there — the count route is strictly weaker than iterated WL.
> 4. **FIX:** the one-round count IS injective at a slightly larger, symmetry-broken base. A **well-chosen (greedy)**
>    one-round base is small and grows slowly: VO^ε_4(3) → **4**, VO^±_4(5) → **6** (both types). Frame-based (standard
>    frame + extra points) is a bit larger: VO^-_4(3) → 6, VO^+_4(5) → 7, matching `Probe_FormsGraphs`'s `[5,5,6,7]`
>    for q=[2,3,4,5] (so that probe measured the *one-round* base). Net: the one-round base is `≈ d+2` with a slow
>    `q`-dependence — bounded and small. (Uniform-in-`q` proof: a `q`-growing but `O(d+log q)`-ish base; first target
>    q=3,d=4 → frame+1 = size 6, or a greedy size-4.)
>
> **CONSEQUENCE:** the landed B.1 checkpoint capstones (`reachesRigidOrCameron_via{IsotropyCounts,CountsDetermineFrameQ,
> SimilitudeForm}`, `PublicTheoremIndex.md:1221-1233`) are axiom-clean but have **unprovable hypotheses as stated**
> (tied to the symmetric frame) — they need REFORMULATION with a base `T = frameBase ∪ {p}`. The "recover Q-profile then
> `coords_determine`" architecture is wrong for minus-type (front-half false); the correct target is **direct count-
> injectivity at the bigger base** → `discrete_of_kRoundRelationSeparates` → `Discrete` → `SeparatesAtBoundedBase` →
> seal (no `coords_determine`). **B.0 (`reachesRigidOrCameron_viaOrthogonalForm`, isometry `O(Q)`) is UNAFFECTED** —
> there the relation IS the Q-value (depth-1). **NEXT:** (i) reformulate the B.1c predicate around a symmetry-broken
> base; (ii) prove count-injectivity there = a `(d+2)`-point character-sum count (A2 generalized + D1 per inner sum) —
> the genuine content, now TRUE; (iii) Brick C-even (validates C); (iv) bridge + basis for `VO^ε_4(3)`; then PORT.
> char-2 deferred (§5 R2′). **This also flags §2(ii)/§3's "discreteness at `T` from the count" as needing the
> symmetry-broken base — update §3.**

> **▶▶ HANDOFF box (2026-06-18 morning) — PARTLY SUPERSEDED. Read the two ⚠/⚠⚠ boxes ABOVE first: they are the live
> state.** This box's "chain confirmed end-to-end / checkpoints EXHAUSTED / next action = heavy build B.1c-ii via
> `IsotropyCountsRecoverFrameQ`" is WRONG — that predicate (and `CountsDetermineFrameQ`/`SimilitudeFrameSeparates`) was
> found FALSE at the standard frame (mis-shaped); the corrected target is count-injectivity at a *symmetry-broken* base,
> and the Gauss toolkit for it is now built (`ScratchGauss.lean`). The decl inventory + Witt/Gauss framing below remain
> accurate; the "what's open / next action" framing is replaced by the ⚠⚠ box. Kept for the decl map + history.
>
> **What's done.** All conditional capstones and isolation checkpoints for the node-4 forms-graph residue are LANDED,
> axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green (`bash scripts/build.sh`, ~82s). They live in
> **`CascadeAffine.lean` §OrthogonalForm** (`PublicTheoremIndex.md:1207, 1210-1233`). The seal for the rank-3 SRG `VO^ε`
> residue (`affineScheme (similitudeGroup Q)`) is reduced **end-to-end** to two isolated, named, heavy-build predicates:
>
> ```
> OrbitIsIsotropyClass Q        (B.1c-i, Witt)     ┐
> IsotropyCountsRecoverFrameQ Q (B.1c-ii, Gauss)   ┘→ CountsDetermineFrameQ → SimilitudeFrameSeparates
>                                                     →[coords_determine, viaSpielman, LANDED]→ SEAL
> ```
>
> **What's open = exactly two independent heavy Mathlib builds** (everything else is proved and composes; the chain is
> confirmed):
> - **B.1c-i — `OrbitIsIsotropyClass Q`** via **Witt's theorem** (the `GO(Q)`-orbits = isotropy classes ⟹ rank-3).
>   Witt is ABSENT in Mathlib; this is the heaviest piece. §8 B.1c-i.
> - **B.1c-ii — `IsotropyCountsRecoverFrameQ Q`** via **quadratic Gauss-sum / affine-quadric point counts** (isotropy-
>   class counts recover the frame `Q`-profile). Mathlib has `ZMod.gauss_sum` + quadratic-character pieces but not the
>   assembled affine-quadric point-count formula. §8 B.1c-ii.
>
> **Next action.** Checkpoint/isolation work is EXHAUSTED — do not add more wrappers. The next increment is a *genuine
> heavy build*: **recommend B.1c-ii at `VO^ε_4(3)`** (`d=4`, `q=3` prime so `F_q = ZMod q`, char ≠ 2 — the cleanest;
> richest probe data, base `[5,5,6,7]`). The back-half `coords_determine` (B.0) is landed and reused; the residual
> subtlety is the **non-isotropic shell** (§3) and **char-2** (§5 R2′, defer). These two builds are independent — they
> can be done in either order / separate sessions, then composed via the landed `reachesRigidOrCameron_viaIsotropyCounts`.
>
> **Orientation pointers.** §3 = the two mathematical routes (A counts / B perp-graph) + the non-isotropic shell;
> §5 = risks incl. the two Mathlib blockers (R2 Witt, R2b Gauss) + char-2 (R2′); §7 = why this is NOT the open SRG-WL
> problem (read before doubting tractability); §8 = the B.1c build scoping. Route-doc §9.9.18b/c = the empirical anchor
> (`Probe_FormsGraphs`). Quality bar: axiom-clean, no `sorry`/`axiom`, `native_decide` banned; develop new Lean in a
> scratch file (`lake env lean ChainDescent/Scratch*.lean`, seconds) then port into CascadeAffine (~50s build) — that
> was this work's iteration loop. Nothing committed (user commits).

**★ STAGE B.1 + RESEARCH-CORE CHECKPOINT CONFIRMED (2026-06-18, axiom-clean, build green).** Landed
(CascadeAffine.lean §OrthogonalForm Stage-B.1 block, `PublicTheoremIndex.md:1218-1226`): `similitudeGroup`
(`GO(Q) = {g | ∃ μ, Q(g x) = μ·Q x}`), `neg_mem_similitudeGroup`, `isometry_le_similitude`, the named count crux
`SimilitudeFrameSeparates`, the conditional capstone **`reachesRigidOrCameron_viaSimilitudeForm`**, and — the new
**checkpoint** — `FrameCountsAgree`, `CountsDetermineFrameQ`, `similitudeFrameSeparates_of_countsDetermineFrameQ`,
and **`reachesRigidOrCameron_viaCountsDetermineFrameQ`**.

**The chain is now confirmed END-TO-END, modulo one front-half predicate:**
> `CountsDetermineFrameQ` (= Witt + Gauss) —[`coords_determine`, **LANDED** B.0]→ `SimilitudeFrameSeparates`
> —[`discrete_affineScheme_of_twoRoundDiffSeparates` + `viaSpielman`, **LANDED**]→ **seal** for the rank-3 SRG
> `VO^ε` residue.

So the research core is **sound**: the heavy-but-known machinery, once built, *provably closes the seal* — and the
B.0 back-half `coords_determine` is confirmed to be exactly the right shape and to compose.

**★ WITT-BOUNDARY CHECKPOINT also landed (2026-06-18, axiom-clean) — the open content split along Witt | Gauss.**
`isoClass`, `OrbitIsIsotropyClass` (Witt deliverable), `IsotropyFrameCountsAgree`, `IsotropyCountsRecoverFrameQ`
(Gauss deliverable), `isotropyFrameCountsAgree_of_frameCountsAgree` (plumbing), `countsDetermineFrameQ_of_orbitIsIsotropyClass`,
and the capstone **`reachesRigidOrCameron_viaIsotropyCounts`** (`PublicTheoremIndex.md:1227-1233`). This reduces
`CountsDetermineFrameQ` to the **pure isotropy-only** Gauss deliverable `IsotropyCountsRecoverFrameQ` ("isotropy-class
counts recover the frame `Q`-profile" — no opaque scheme relations), carrying the Witt deliverable `OrbitIsIsotropyClass`.
So B.1c-ii's exact target shape is now **confirmed and isolated** before any heavy build.

**The full confirmed chain:** `OrbitIsIsotropyClass` (Witt) + `IsotropyCountsRecoverFrameQ` (Gauss) →
`CountsDetermineFrameQ` → `SimilitudeFrameSeparates` (via `coords_determine`) → **seal**. The entire open content is
now the two heavy builds, each a clean named predicate at its natural boundary. **Remaining = Stage B.1c** = discharge
**B.1c-i** (`OrbitIsIsotropyClass`, via Witt's theorem) and **B.1c-ii** (`IsotropyCountsRecoverFrameQ`, via Gauss-sum
point counts). Detailed scoping in **§8**. Multi-session research-formalization. Nothing committed.

**★ STAGE B.0 LANDED (2026-06-18, axiom-clean, build green) — the orthogonal-form infrastructure + a complete
depth-1 affine-orthogonal seal.** `reachesRigidOrCameron_viaOrthogonalForm` (CascadeAffine.lean §OrthogonalForm,
`PublicTheoremIndex.md:1217`): for any quadratic form `Q` on `F_p^d` with **nondegenerate polar form**, the affine
scheme of the **isometry group** `O(Q)` discretizes at the basis-frame `{0,e₁,…,e_d}` (size `d+1`) and seals, via
depth-1 separation — the orbit-of-difference determines `Q(v−t)`, which recovers the form coordinates
(`coords_determine`, the crux's reusable back-half), nondegenerate ⟹ determines `v`. **Carries NO `hSmallAutThin`.**
Lands the shared quadratic-form infrastructure (`isometryGroup`, `polar_eq_of_sub`, `coords_determine`, `frameBase`)
and the **Witt-free** recovery. **Honest scope (§3/§7):** this is `O(Q)` (the *finer* orthogonal scheme), **NOT yet
the rank-3 SRG `VO^ε`** — that is the **similitude** group `ΓO(Q)` (Stage B.1), where nonzero `Q`-values fuse,
depth-1 collapses to isotropy bits, and the genuine two-round **count** crux (§3 Route A) is required.
`coords_determine` is reused verbatim as B.1's count back-half. **Next = Stage B.1.** Nothing committed.

**★ STAGE A LANDED (2026-06-18, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green).** The conditional
capstone `reachesRigidOrCameron_viaAffineFormScheme` (CascadeAffine.lean, between the §SGate2 and §AffineScheme
sections; `PublicTheoremIndex.md:1207`) is built. It carries exactly the two pieces the reduction identifies —
`hbase : IsBase … T` (the free group base) and `hFormCert : RelCountsDetermineOrbit … T` (the **only open content**) —
and composes the landed engine + base + seal (`cellsAreOrbits_of_relCountsDetermineOrbit` →
`twinsRealizedByResidualAut_iff_cellsAreOrbits` → `separatesAtBoundedBase_of_twinsRealized` →
`reachesRigidOrCameron_viaSpielman`). **Carries NO `hSmallAutThin`** — node 4 is discharged for this residue, not
assumed. The route is validated end-to-end; the open content is now exactly the one predicate `hFormCert`. **Next =
Stage B** (discharge `hFormCert` for `VO^ε_4(q)`; §3, §4). Nothing committed (user commits).

**(Historical framing, pre-Stage-B — superseded by the HANDOFF box above; kept for the calibration argument.)**
**The target is now extremely concrete** — not "all SRGs", but four explicit affine/classical-group families whose
automorphism group `G^(2)` is given structurally by Skresanov and whose base the probe measured at `≈ d+1` (flat).
**The reduction is mostly landed; the open content was framed as ONE crux lemma — `RelCountsDetermineOrbit (affineScheme G₀) T`
at the group base** (now refined to the two B.1c builds, see HANDOFF), fed into the already-built depth-`k` separation
engine. **Calibration (read §7 before starting):
that lemma is UNCITED, genuine content you must prove — but it is NOT the open "WL-dim of SRGs" research problem.** The
engine has already reduced "bounded WL-dimension" to a finite, geometry-specific separation statement; the structure
(Skresanov), the base (handed by the group), and the answer+mechanism (the probe) are all known, so what remains is a
known-target classical-finite-geometry lemma (Witt-frame / intersection-number), unpublished because unneeded — a
different difficulty class from the black-box SRG problem. The realistic Lean increment is a **conditional capstone**
`reachesRigidOrCameron_viaAffineFormScheme` carrying the certificate as a probe-validated hypothesis (Stage A, wiring
now); the full discharge is a classical-geometry + Mathlib-quadratic-form effort, stageable family-by-family.

**Closes (modulo citations + this proof):** node-4-*for-the-seal*. Combined with Skresanov (residue is affine) + C3
(seal scoped to schurian, §9.9.18a), proving this discharges `hSmallAutThin` for the schurian residue. The genuinely
uncited *non-schurian* wall (IR-solver row 4) is untouched — by design, outside the seal (§9.9.18a).

---

## 1. The target theorem (uniform form)

> **Theorem (to prove).** Let `X = affineScheme G₀` be a primitive rank-3 schurian SRG on `V = F_q^d`, where
> `G₀ ≤ ΓL(V)` is a classical *similitude* group preserving a nondegenerate form `f` (quadratic/bilinear/Hermitian),
> and `d` is bounded (the small-Aut regime: `|Aut| = n^{Θ(d)}` poly ⟺ `d = O(1)`). Then `X` individualizes to a
> **discrete** coloured configuration at a base of size `≤ d+1 = O(1)`. Hence `X` has **bounded WL-dimension**, so
> `BoundedMinMult`/`hSmallAutThin` holds for `X` (the seal's node-4 obligation, for this residue class).

Why this is the seal's node-4 content: §9.9.18 (Skresanov) ⟹ every small-Aut non-geometric schurian rank-3 residue is
one of these affine families (or the cited 1-dim cyclotomic); §9.9.18a (C3) ⟹ the seal's scope IS the schurian residue.
So this theorem + the cyclotomic citation = node-4-for-the-seal, modulo the CFSG identification {Cameron, Liebeck,
Skresanov}.

---

## 2. The reduction — two halves, one open

Decompose `b(X)` (the WL/individualization base) for `X = Inv(G^(2))`, `G^(2) = V ⋊ G₀` (Skresanov):

**(i) The group base is FREE and `O(1)`.** Take `T = {0, e₁, …, e_d}` (origin + a basis of `V`). An affine map
`x ↦ g₀x + t` fixing `0` has `t=0` (linear); fixing a basis `{e_i}` pointwise forces `g₀ = 1`. So `(G^(2))_T = {1}`,
i.e. **`T` is a group base**, `|T| = d+1`. In Lean: `IsBase (schemeAdj X) _ T` holds; or use the landed
`exists_greedy_base_le_log` for an `O(log n)` base with no frame computation. Either gives the `IsBase`/bounded-`|T|`
inputs of `separatesAtBoundedBase_of_twinsRealized` for free. **Nothing open here.**

**(ii) The separation certificate is the OPEN content.** Discreteness at `T` is *not* automatic from `(G^(2))_T = {1}`
— that gives singleton *orbits*, but 2-WL must *see* them (no 2-closure deficiency at the extension `X_T`). The exact
open obligation is the engine's separation hypothesis at `T`:
> `hsep`: for all `u,u'`, if the **two-round relation-count profile** agrees
> (`∀ ρ b, #{z≠u : (∀t∈T, relOfPair t z = ρ t) ∧ relOfPair u z = b} = #{z≠u' : … u' …}`), then `u = u'`.
This is exactly the input of the **landed** `discrete_of_twoRoundRelationSeparates` (k=1) / `discrete_of_kRoundRelationSeparates`
(general `k`) (CascadeAffine.lean). Equivalently `RelCountsDetermineOrbit X T` (which, since `(G^(2))_T={1}`, collapses
to count-equal ⟹ equal). **This is the only open piece.**

**(iii) Compose (free).** `hsep` ⟹ `Discrete(warmRefine X_T)` (engine) ⟹ `SeparatesAtBoundedBase X (d+1)` (with the
(i) `IsBase`, via `separatesAtBoundedBase_of_twinsRealized` — note `Discrete ⟹ TwinsRealizedByResidualAut` trivially,
or use the engine's `Discrete` output directly) ⟹ the seal capstone. **Landed wiring.**

So: **free base (i) + landed engine (iii); the whole proof is the certificate (ii).**

---

## 3. The crux lemma — "the count profile recovers the form coordinates"

The probe pins the mechanism. A *binary* isotropy profile w.r.t. `T` would need `|T| ≥ log_q(q^d) = d` points just to
have enough profiles, and could not separate at `O(1)` — yet the probe shatters at `≈ d+1`. So the separation is *not*
from the direct (rank-3, binary) relations; it is from the **two-round COUNTS**, which recover the *field-valued* form.

> **Crux Lemma (per family, uniform skeleton).** Let `B` be the nondegenerate (bi)linear form associated to `f`. After
> individualizing `T = {0, e₁,…,e_d}`, the two-round relation-count profile of a vertex `v` determines `B(v, e_i) ∈ F_q`
> for every `i`. Since `B` is nondegenerate, `(B(v,e_i))_{i=1}^d` determines `v`. Hence the count profile is injective
> (`hsep` holds).

There are **two routes** to the certificate. Route A is elementary and Witt-free (the safe Lean path); Route B is more
geometric and is the right *mental model* (it explains why the bulk is easy), but leans on Witt's theorem, which Mathlib
**lacks** (verified 2026-06-18 — see §5 R2). Both meet at the same residual difficulty: the **non-isotropic shell**.

**Route A — explicit count-injectivity (elementary, Witt-free; the Lean default).** For affine polar `VO^ε` the count
`N_{i,b}(v) := #{z : Q(z − e_i) = 0 ∧ relOfPair v z = b}` (common "isotropic-from-`e_i`" points at relation `b` to `v`)
is an explicit function of `B(v, e_i)` via the orthogonal geometry's intersection numbers (the number of isotropic
points in the "tangent" configuration of `v, e_i` depends on whether/how `v ⊥ e_i`). Showing `N_{i,·}(v)` is injective
in `B(v,e_i)` discharges the lemma. This is classical, bounded combinatorics in the polar space — and avoids Witt.

**Route B — perp-graph + Witt frame-rigidity (the geometric picture; explains the difficulty inversion).** You do *not*
have to prove abstract count-injectivity from scratch; there is a directly geometric decomposition:
- **Individualize `0`.** `N(0)` = the nonzero isotropic vectors. The key identity: for isotropic `x,y`,
  `Q(x−y) = Q(x)+Q(y)−B(x,y) = −B(x,y)`, so **`x ~ y ⟺ B(x,y) = 0`**. Hence the subgraph induced on `N(0)` **IS the
  collinearity (perp) graph of the polar space, read straight off the rank-3 adjacency — no counting.**
- **The polar space is frame-rigid (Witt's theorem).** Individualizing a hyperbolic frame / apartment (`O(d)` isotropic
  points) trivialises its isometry-stabiliser *and* determines each isotropic point by its perp-pattern to the frame. So
  `0 + frame` (`O(d)` points) discretises the **isotropic skeleton** via the *direct* adjacency.
- **The non-isotropic shell** is then pinned by its adjacency/relation pattern to the now-discrete isotropic skeleton.
  **This is the genuinely fiddly bit** (and where Route A and Route B meet): binary adjacency `w ~ x_i ⟺ B(w,x_i)=Q(w)`
  recovers `B(w,x_i)` only *modulo the unknown scalar `Q(w)`*. Expect to need either a couple of extra base points, or
  one round of the engine's count (Route A) restricted to the non-isotropic shell.

**The difficulty inversion (why this reads harder than it is).** The hard-*looking* part — the isotropic bulk — is the
*easy* part (direct perp-graph + Witt). The residual work is the **non-isotropic shell**, a narrow, located problem.

**Per-family status of the crux lemma:**
- **(c) affine polar `VO^ε_{2m}(q)`** — quadratic form `Q`, bilinear `B(x,y)=Q(x+y)−Q(x)−Q(y)`. Mathlib `QuadraticForm`
  has exactly this. **Cleanest target; do first.**
- **(d) alternating forms `A(d,q)`** — vertices = alternating matrices = `Λ²(F_q^d)`; adjacency = rank-2 difference;
  the associated form is the alternating (symplectic) `B`. Same skeleton, `B` symplectic. **Second.**
- **(e) half-spin `VD_{5,5}(q)`** — spinor geometry; the "form" is the triality/spinor norm. Same *spirit* (a
  nondegenerate spinor pairing recovers coordinates) but heavier geometry. **Third; may defer.**
- **(f) Suzuki–Tits `VSz(q)`** — the Suzuki ovoid, **not a form-graph** (Sz(q) is a twisted group, not classical
  similitude). The form skeleton does NOT apply. **Separate argument** — either (α) a direct count in the ovoid
  geometry, or (β) fall back to the generic schurian bound: `(G^(2))_T={1}` at an `O(1)` base + a separability/no-
  deficiency argument specific to Sz(q). Honest caveat: Suzuki is the residual hard single family; flag it.

The lemma is **uniform** for the form-based families (c)–(e); (f) is the outlier.

---

## 4. The Lean formalization plan

**Reusable, landed (no rebuild):**
- Engine: `discrete_of_twoRoundRelationSeparates` / `discrete_of_kRoundRelationSeparates` / `kRoundProfileCount_eq`
  (consumes `hsep`, gives `Discrete`). `RelCountsDetermineOrbit` / `cellsAreOrbits_of_relCountsDetermineOrbit` (orbit form).
- Free base: `IsBase`, `exists_greedy_base_le_log`, `separatesAtBoundedBase_of_twinsRealized`,
  `TwinsRealizedByResidualAut`.
- Affine substrate: `affineScheme G₀` / `affineG` / `affinePermFin` — **already general in `d` and `G₀ ≤ GL_d(F_p)`**
  (verified). The cyclotomic instance (`G0cyc`/`G0pow`) is the 1-dim template to mirror.
- Mathlib: `QuadraticForm`, `LinearMap.BilinForm` (nondegeneracy), `GaloisField`, `Basis`, `Module.finBasis` — available.

**New (the build):**
1. **The form scheme instance.** Define the affine form scheme as `affineScheme G₀` with `G₀ =` the matrix similitude
   group `ΓO(Q)` (resp. `ΓSp`, `ΓU`), OR (lighter) define the Cayley scheme directly from a Mathlib `QuadraticForm`
   and prove it `SchurianScheme` via similitude-transitivity. **Dependency:** Witt-type transitivity (the similitude
   group is transitive on each form-value level set, fusing nonzero values via scalars to 2 orbits ⟹ rank 3). Check
   Mathlib for Witt's theorem / `QuadraticForm` isometry-transitivity; if absent, this is the main new infrastructure.
2. **The crux certificate lemma** (§3): the two-round count profile at `T` recovers `B(v,e_i)`; conclude `hsep`.
   The combinatorial-geometry counting. Family-specific; uniform skeleton for (c)–(e).
3. **The capstone** `reachesRigidOrCameron_viaAffineFormScheme`: compose (i)+(ii)+(iii) → `SeparatesAtBoundedBase` →
   the seal (via the landed `…viaSymmetricRecovery`/`schemeRecoveredByDepth_of_separatesAtBoundedBase`). Carries
   {G3 + the affine-form structure}; **no `hSmallAutThin`** (it is *discharged* for this family).

**Staging (build order):**
- **Stage A — the wiring + conditional capstone (cheap, do first). ✅ DONE (2026-06-18, axiom-clean, build green).**
  `reachesRigidOrCameron_viaAffineFormScheme` (CascadeAffine.lean, `PublicTheoremIndex.md:1207`) carries the certificate
  as a *named hypothesis* `hFormCert : RelCountsDetermineOrbit S.toAssociationScheme T` plus the free group base
  `hbase : IsBase … T` (probe-validated, like `clebschZ4_closure` carried δ′). Route validated end-to-end; the open
  content is isolated to the one predicate `hFormCert`.
- **Stage B.0 — orthogonal-form infrastructure + depth-1 `O(Q)` seal. ✅ DONE (2026-06-18, axiom-clean, build green).**
  `reachesRigidOrCameron_viaOrthogonalForm` + `coords_determine` + `isometryGroup` + `polar_eq_of_sub` + `frameBase`
  (CascadeAffine.lean §OrthogonalForm, `PublicTheoremIndex.md:1210-1217`). The **isometry** group `O(Q)`, sealed via
  depth-1 (`discrete_affineScheme_of_jointSeparates`) — the orbit-of-difference determines `Q(v−t)`, recovering form
  coords. Witt-free. **Caveat:** `O(Q)` is the *finer* orthogonal scheme, **not** the rank-3 SRG `VO^ε`. Lands the shared
  form infrastructure + `coords_determine` (reused by B.1).
- **Stage B.1 — the similitude group `GO(Q)` + the node-4 conditional capstone. ✅ DONE (2026-06-18, axiom-clean).**
  `similitudeGroup` + `neg_mem_similitudeGroup` + `isometry_le_similitude` + `SimilitudeFrameSeparates` (the named
  count crux) + `reachesRigidOrCameron_viaSimilitudeForm` (CascadeAffine.lean §OrthogonalForm Stage-B.1 block,
  `PublicTheoremIndex.md:1218-1222`). The genuine rank-3 SRG `VO^ε` residue (`affineScheme (similitudeGroup Q)`)
  seals once `SimilitudeFrameSeparates Q` holds. Open content isolated to that one predicate. **Carries NO `hSmallAutThin`.**
- **Stage B.1c — discharge `SimilitudeFrameSeparates` (the two-round count crux). OPEN; the deep research core.** §3
  Route A: the count `N_{i,b}(v)` recovers `B(v,e_i)`; back-half = the landed `coords_determine`. Start `d=4`,
  `VO^ε_4(q)` generic in `q` (richest probe data, base `[5,5,6,7]`). Use **Route B** as the picture but the formal
  proof goes via **Route A** counts; residual = the **non-isotropic shell** (plan a small `k` or 1–2 extra base
  points). **Two Mathlib blockers (§5 R2):** (i) **Witt's theorem** — needed to characterize the `GO(Q)`-orbits (=
  the scheme's relations) so the counts can be computed at all; (ii) **quadratic Gauss-sum / affine-quadric point
  counts** — the intersection numbers as functions of `B(v,e_i)`. Both are substantial Mathlib-level builds.
- **Stage C — alternating / half-spin** (reuse the skeleton with the symplectic / spinor `B`).
- **Stage D — Suzuki–Tits** (separate plan needed).

---

## 5. Risks, and the pragmatic fallback

- **R1 — the counting lemma is real work.** Computing intersection numbers as functions of `B(v,e_i)` and proving
  injectivity is classical but nontrivial to formalize. *Mitigation:* Stage A lands the wiring regardless; Stage B can
  start from explicit count formulas for `VO^ε_4(q)` (small `d`).
- **R2 — Witt theory is ABSENT from Mathlib (verified 2026-06-18), and it bites Stage B.1c (NOT B.0).**
  `Mathlib/LinearAlgebra/QuadraticForm/` has `Isometry`/`IsometryEquiv`/`Radical`/`Basis`/`Dual` but **no Witt
  decomposition and no Witt extension theorem** (the only "Witt" files are `Order/BourbakiWitt`, unrelated, and
  `RingTheory/WittVector`, ring-theoretic). **Sharpened by the B.0/B.1 split:** B.0 (`O(Q)`, depth-1) is **Witt-free** —
  it uses only the *easy* direction (orbit ⟹ `Q`-value, by invariance), so it landed. **B.1c is NOT Witt-free**: under
  `GO(Q)` the relations are the *orbits*, and to compute the two-round counts at all one must **characterize the
  `GO(Q)`-orbits** = the isotropy classes — which is exactly Witt's transitivity (the *hard* direction). So Route A for
  the similitude scheme needs Witt for the orbit characterization, on top of the point-counting. Building Witt's
  extension/transitivity theorem in Mathlib is the first prerequisite for B.1c. (Route B's frame-rigidity needs the same
  Witt theorem — so there is no Witt-free route to B.1c.)
- **R2b — quadratic Gauss-sum / affine-quadric point counts (the second B.1c blocker).** The intersection numbers
  `N_{i,b}(v)` are point counts on affine quadrics over `F_q` (`#{z : Q(z−e_i)=0 ∧ …}`), whose values are governed by
  the quadratic character / Gauss sums and the form type `ε`. Mathlib has `ZMod.gauss_sum` and quadratic-character
  pieces but not the assembled affine-quadric point-count formula uniform in `q`. This is the genuine combinatorial-
  geometry core and a substantial build in its own right. *Mitigation:* start at fixed small `d=4`, `VO^ε_4(q)`, where
  the count formulas are explicit; the back-half (`coords_determine`) is already landed and Witt-free.
- **R2′ — characteristic 2.** The probe spans `q = 2,4` (char 2) and `q = 3,5` (char ≠2). In char 2 the bilinear form is
  alternating (`B(x,x)=0`) and `Q` is **not** recoverable from `B` alone — the Route-A/B identities (`Q(x−y)=−B(x,y)`,
  `B(w,x_i)=Q(w)`) still hold but the "recover `Q(w)`" step needs the quadratic form directly, not just `B`. Budget the
  char-2 shell argument separately; do char-≠2 (`q=3`) first.
- **R3 — Suzuki–Tits is not a form-graph.** *Mitigation:* treat (f) separately; worst case it remains a single flagged
  family with empirical (probe) support, while (c)–(e) are proven — still a major reduction of the residue.
- **R4 — `k` (round count).** The crux is a one-round count, so `discrete_of_twoRoundRelationSeparates` (k=1) should
  suffice; if a single round only partially recovers `B`, escalate to `discrete_of_kRoundRelationSeparates` (small `k`).
  Note (engine ceiling, §9.9.15): the count profile is `k`-independent, so if k=1 fails the lever is a **larger base**
  (more frame points), not deeper `k` — the frame `T` already has `d+1` points, which is the natural fix.

**Pragmatic fallback (always available):** Stage A's conditional capstone `…viaAffineFormScheme` carrying
`hFormCert` as a probe-validated hypothesis is itself a real deliverable — it makes node-4-for-the-seal
`modulo {G3 + Liebeck + Skresanov + the affine-form certificate}`, with the certificate empirically confirmed
(§9.9.18c) and reduced to a single combinatorial predicate per family. This mirrors how the affine cyclotomic slice
was first carried (cited 2-sep) before the δ′ discharge.

---

## 6. Honest scope

- **What it closes:** with the crux lemma proved for (c)–(e) [+(f) or flagged], `hSmallAutThin` is *discharged* for the
  schurian node-4 residue — node-4-for-the-seal becomes `modulo {G3 + the CFSG identification (Cameron/Liebeck/Skresanov)
  + the affine-form certificate}`, all citations/proofs, no open wall. The empirical shatter (§9.9.18c) becomes a theorem.
- **What it does NOT close:** the non-schurian wall (IR-solver row 4, §9.9.18a) — a separate object, outside the seal by
  the C3 scoping. And the CFSG identification stays cited (like G3).
- **Relation to the rank-counting boundary (§9.9.9a):** consistent — the recovery is in the 2-WL *extension* `X_T`
  (where the depth-`k` engine lives), not the scheme-level rainbow engine (inapplicable at rank 3).

---

## 7. Difficulty calibration — why this is NOT the open SRG-WL-dimension problem

A fresh reader's natural worry (correct in part): *"the crux lemma is uncited, so it is open research, not formalisation."*
Honest calibration, from the Stage-B/C scoping handoff (2026-06-18):

**What is TRUE in that worry (do not overclaim against it):**
- The crux lemma is **uncited** — no reference to formalise from. It is genuine content you must *prove*, not look up.
  "Routine" was the wrong word; treat it as **concrete**, not easy.
- Bounded WL-dimension of the affine forms-graphs is genuinely **unpublished** (the C1 literature pass, §9.9.18b, found no
  citation).
- Uniformity over all `q` (+ the Skresanov Table-7 small-degree exceptions, §5 R4-adjacent) and the Suzuki outlier are
  real.

**What is WRONG in that worry — why this is a different difficulty class:**
The open SRG-WL problem is hard because the SRG is a **black box** (unknown automorphisms/geometry). Here every black-box
element is removed:
1. **The structure is KNOWN (Skresanov).** The residue is `affineScheme G₀` with `G₀` an explicit classical similitude
   group and an explicit nondegenerate form — you have the geometry, not an unknown SRG.
2. **The base is HANDED, not searched.** `T = {0,e₁,…,e_d}` is the group base (`(G^(2))_T={1}`, §2(i)) — no need to
   discover a good base or argue one exists.
3. **The WL machinery is ALREADY DONE.** The landed engine (`discrete_of_twoRoundRelationSeparates` /
   `discrete_of_kRoundRelationSeparates` / `kRoundProfileCount_eq`) has *already* reduced "bounded WL-dimension" to a
   finite, checkable, geometry-specific statement — the count profile at `T` separates vertices. **No WL-dimension theory
   remains to develop.** This is the whole point of building the engine first: it converts the open WL problem into
   classical finite geometry.
4. **The probe gives the ANSWER and the MECHANISM.** `Probe_FormsGraphs` (§9.9.18c) shows discreteness at base `≈ d+1` and
   the mechanism (counts recover the field-valued form, not binary isotropy). You are *verifying a known target*, not
   searching.

**So the honest framing:** the crux is *concrete uncited classical finite geometry about an explicit family with a handed
base* — unpublished because nobody needed it, not because it resists technique. **The real cost is the Lean formalisation
of finite-geometry intersection numbers, not the mathematics.** The genuine residual *mathematical* difficulty is narrow
and located: the **non-isotropic shell** (§3, the Route-A/B meeting point) and char-2 (§5 R2′). Recommended order
de-risks the wiring before the geometry: **Stage A first** (carry `hFormCert`, prove the route closes, get the exact
`hsep` shape), then attack the shell with the answer already known.

---

## 8. Stage B.1c scoping — discharging `CountsDetermineFrameQ` (the one open predicate)

The checkpoint (§ STATUS) confirms everything composes; the *entire* remaining content is one predicate:

> **`CountsDetermineFrameQ Q`** — agreeing two-round difference-counts at the basis frame ⟹ same `Q`-value profile
> (`Q ū = Q ū'` and `Q(ū−e_i) = Q(ū'−e_i)` ∀ basis `e_i`).

This decomposes into two independent Mathlib-level builds (B.1c-i, B.1c-ii), feeding the landed back-half.

### B.1c-i — Witt's theorem (orbit characterization). The relations ARE the counts' alphabet.
The counts in `FrameCountsAgree` are phrased via `relOfPair … = the GO(Q)-orbit index of the difference`. To
reason about them at all, one must know **what the orbits are**: `GO(Q)`-orbit of `w` is determined by, and
determines, the isotropy class `(w = 0 / Q w = 0 / Q w ≠ 0)`.
- **Easy direction** (orbit ⟹ isotropy, by `Q`-invariance) is Witt-free — already used in B.0.
- **Hard direction** (same isotropy class ⟹ same orbit, i.e. `GO(Q)` is transitive on nonzero isotropic vectors
  and on each `Q ≠ 0` shell up to the similitude scalar) **is Witt's transitivity / extension theorem.**
- **Deliverable:** `relOfPair (affineE 0) (affineE w) = relOfPair (affineE 0) (affineE w')` ↔ `isoClass w = isoClass w'`,
  giving exactly **rank 3** (`{0, isotropic, anisotropic}`) — so the scheme is the SRG `VO^ε`.
- **Mathlib status:** ABSENT (no Witt decomposition/extension; §5 R2). This is the larger of the two builds —
  Witt's theorem for quadratic forms over finite fields, plus the similitude-scalar fusion. Scope: the
  hyperbolic-decomposition + extension-of-isometries development (~Mathlib-contribution size).
- **Checkpoint-able first:** state the orbit characterization as a carried predicate `OrbitIsIsotropyClass Q` and
  prove `CountsDetermineFrameQ` reduces to an isotropy-only count statement — confirms B.1c-ii's target shape
  before B.1c-i is built. (Recommended next concrete increment — it is checkpoint work, not heavy build.)

### B.1c-ii — quadratic Gauss-sum / affine-quadric point counts. Counts ⟹ field values.
With the orbits = isotropy classes, the two-round count `N(u; ρ, b)` becomes a count of `z` by the isotropy
pattern of `(z̄ − t̄)_{t∈frame}` and `(z̄ − ū)`. The deliverable: these counts **recover the field value** `Q(ū − t̄)`
(not just its isotropy bit). Mechanism (§3 Route A): the count of common isotropic neighbours of `e_i` and `u`
is an explicit function of `B(ū, e_i)` (hence of `Q(ū − e_i)` via polarization), via the affine-quadric
intersection numbers.
- **Mathlib status:** partial — `ZMod.gauss_sum`, quadratic-character pieces exist; the assembled **affine-quadric
  point-count formula** (number of solutions of `Q(x) = c` on `F_q^d`, by type `ε` and parity of `d`) is **not**
  packaged. This is the genuine combinatorial-geometry core.
- **Scope reducer:** fix `d = 4`, `VO^ε_4(q)` first (explicit count formulas; richest probe data). The **non-isotropic
  shell** (recovering `Q(ū)` itself, where `B(ū,e_i) = Q(ū)` is known only modulo the unknown `Q(ū)`, §3) is the
  fiddly residual — budget a small `k` or 1–2 extra frame points.
- **char-2 caveat (§5 R2′):** do `q = 3` first.

### Recommended order (de-risk shape before heavy build)
1. **(checkpoint, light) ✅ DONE (2026-06-18, axiom-clean).** `OrbitIsIsotropyClass Q` carried; `CountsDetermineFrameQ`
   reduced to the isotropy-only `IsotropyCountsRecoverFrameQ Q` (`countsDetermineFrameQ_of_orbitIsIsotropyClass`,
   capstone `reachesRigidOrCameron_viaIsotropyCounts`, `PublicTheoremIndex.md:1227-1233`). B.1c-ii's exact target is
   confirmed and B.1c-i's output plugs in — before building Witt.
2. **(heavy)** B.1c-ii for `VO^ε_4(3)`: the affine-quadric point counts ⟹ `IsotropyCountsRecoverFrameQ`.
3. **(heaviest)** B.1c-i: Witt's theorem ⟹ `OrbitIsIsotropyClass`, discharging the carried predicate.
4. Generalize `d`, then `q` (incl. char 2), then classes (d)/(e); Suzuki (f) separate (not a form).

**[⚠⚠ SUPERSEDED 2026-06-18 — see the ⚠⚠ box in STATUS. This §8 framing — "`IsotropyCountsRecoverFrameQ` is the
B.1c-ii target, recover Q-profile then `coords_determine`" — is WRONG: that predicate is FALSE at the standard frame
(`VO^-`, one-round count shell-blind via frame symmetry). The corrected target is direct count-injectivity at a
symmetry-broken base (`≈ d+2`), via the Gauss toolkit now built in `ScratchGauss.lean`. Witt (step 3, B.1c-i
`OrbitIsIsotropyClass`) is still needed. Read STATUS, not this paragraph, for the live plan.]**
~~All checkpoint work is now exhausted — the open content is irreducibly the two heavy builds (B.1c-ii Gauss,
B.1c-i Witt), each isolated as a clean named predicate. The next increment is a genuine heavy build (recommend
B.1c-ii at `VO^ε_4(3)`), not further isolation.~~

**Pragmatic end-state if the heavy builds are deferred:** `reachesRigidOrCameron_viaCountsDetermineFrameQ`
already makes node-4-for-the-seal `modulo {G3 + Cameron/Liebeck/Skresanov + CountsDetermineFrameQ}`, with
`CountsDetermineFrameQ` a single, concrete, probe-validated, finitely-checkable predicate — the sharpest honest
isolation of the node-4 forms-graph residue.

---

## 9. Remaining roadmap to completion of the Gauss work (milestones)

> **Scope.** "Completion of the Gauss work" = discharge `IsotropySeparatesAtBase Q T` for a concrete `VO^ε` (target
> `VO^-_4(3)`) and feed `reachesRigidOrCameron_viaIsotropySeparates`. The capstone *also* needs `OrbitIsIsotropyClass`
> (Witt, B.1c-i) — a **separate parallel track**, not Gauss work. Generalization over `q`/`d`, char-2, and Suzuki (f)
> are follow-ons (M5).
>
> **Process rule (to avoid per-lemma doc churn): batch all lemmas of a milestone, then do ONE
> build + index-regen + STATUS/MEMORY update at the milestone boundary.** Each milestone below is one work session.

**Built (the connective tissue, all axiom-clean):** the reformulation (`SeparatesAtBase` / `IsotropySeparatesAtBase`
/ `reachesRigidOrCameron_viaSymmetryBrokenBase` / `…viaIsotropySeparates` / Witt bridge `separatesAtBase_of_isotropySeparates`);
the full Gauss toolkit (`GaussCount.lean`, 18 lemmas: count layer A/A2/Aₖ/`count_pi_setValued`, 1-D + multivariable
Gauss, `card_quadForm_eq`, `multiQuad`/`multiQuad_zero`/`linearMap`); the isotropy dictionary (`isoClass_eq_*`); the
consumer bridges (`count_transport`, `qvalue_count_transport`).

**Pipeline (corrected after M3's shell-blind finding — see §9 M3 / §10):**
`fine isotropy counts —[M1 ✓]→ coarse Q-zero-pattern counts —[1.2 incl–excl]→ joint isotropic counts Z(S)
—[1.3 = ∑ multiQuad]→ char-sums in the Gram —[1.4 EXTRACTION = the open kernel]→ Q-profile —[coords_determine ✓ M3]→ u=u'.`
(The earlier "→ pointwise Q-counts → M2 Fourier hinge" leg is a DEAD END: `isoClass` is shell-blind, so the counts never
give pointwise `Q=1` vs `Q=2`; `multiCharSum`/M2 are valid lemmas but off this path. See §10.)

### Milestone 0 — probe & blueprint ✅ DONE (2026-06-18, `/tmp/m0probe.py` over `VO^-_4(3)`)
**Findings (these refine M1 and M3 below):**
1. **`frameBase` (size 5) FAILS both fine and coarse** — twin `(0,0,1,2)~(0,0,2,1)`. Cause: the `x₂↔x₃` isometry
   *permutes the frame setwise*, so it is invisible to the count-signature (which is `Stab_setwise(T)`-invariant)
   even though it IS visible to `u`'s own Q-profile. The fix is a base with trivial setwise stabilizer.
2. **★ COARSE counts SUFFICE.** At every separating base found, the coarse split (`Q=0` vs `Q≠0`, pure `Q`-value, NO
   origin correction) separates exactly when fine does. **⟹ M1 drops the origin correction entirely** (work with the
   coarse/value-set counts; fine-count agreement ⟹ coarse-count agreement by summing).
3. **Two working bases:** greedy **size-4** `{0, e₃, e₂, (0,1,1,2)}`; **frame+1 size-6** `T = {0,e₀,e₁,e₂,e₃, 2e₃}`
   (= `frameBase ∪ {2e₃}`). Both coarse-separate.
4. **★ Blueprint — recommend the size-6 base.** At size-6, `u ↦ (Q(u−t))_{t∈T}` is **injective (81/81)**; at size-4 it
   is NOT (63/81). So **M3 reduces to: counts recover the Q-profile `(Q(u−t))_{t∈T}` → the landed `coords_determine`
   gives `u`** (the extra point `2e₃` breaks the frame's setwise symmetry so the *counts* recover the profile). This
   reuses `coords_determine` inside the `IsotropySeparatesAtBase` proof (not at the capstone, which stays count-based).

### Milestone 1 — the conversion (isotropy counts → pointwise Q-counts) ✅ DONE (2026-06-18, axiom-clean)
**Conversion core landed in `FormsGraphConcrete`** (M0: coarse suffices, no origin correction): `isotropy_count_transport`
(transport the fine count `Fin(p^d)→V`); the dictionary `isoSetOf`/`qSetOf` + `mem_isoSetOf_iff` (`isoClass∈isoSetOf b
↔ Q∈qSetOf b`, the coarse split is a pure `Q`-value condition); **`coarse_eq_sum_iso`** (`count_pi_setValued` at the
isotropy value-type: coarse `Q`-value-set count = sum of fine isotropy counts over refining `σ`-profiles ⟹ fine-count
agreement transfers to coarse). Coarse→pointwise is the landed `qvalue_count_transport`. **Deferred to M3's first step**
(entangled with the recovery): folding the base `T`(Finset)+`u` into one family and the single `x=ū` count adjustment.

### Milestone 2 — the Gauss closed form ✅ DONE (2026-06-18, axiom-clean) — cleaner **Fourier-inversion** architecture
Instead of inverting the full closed form in M3, the hinge is **`multiCharSum_eq_sum_count`** (`GaussCount`): the dual
of `countk_eq_sum_charsum`, `∑_x ψ(∑_j r_j·f_j x) = ∑_c ψ(∑_j r_j·c_j)·#{x:∀j, f_j x=c_j}` (partition by value-tuple).
**Consequence: all pointwise counts agree ⟹ all multi-point Gauss sums `S(r)` agree** — and `S(r)` already carries the
Gram via the landed `sum_addChar_multiQuad` (`S(r) = ψ(Gram-expr)·∑_x ψ(R·Q x)`). Plus **`sum_addChar_quadForm_smul_ne_zero`**:
the global value `∑_x ψ(R·Q x) ≠ 0` (from `∑_x ψ(Q x) ≠ 0`, carried), so it cancels. Net M2 output for M3:
**count-agreement ⟹ `ψ(Gram-expr_u) = ψ(Gram-expr_{u'})` for all `r`.** The `SeparatingLeft` bridge / explicit `∏χ·Gᵈ`
form turned out OFF the critical path (`∑ψ(Qx)≠0` + the orthogonal basis are carried, discharged concretely in M4).

### Milestone 3 — the injectivity (THE CRUX) — REDUCTION DONE, kernel ISOLATED (2026-06-18)
**Reduction landed (axiom-clean, `FormsGraphConcrete`):** `isotropySeparates_of_qProfileSeparates` reduces
`IsotropySeparatesAtBase Q T` to the single predicate **`QProfileSeparatesAtBase Q T`** ("counts recover the
`Q`-profile over the basis frame"), via the landed `coords_determine` (Q-profile + nondeg ⟹ vector) + `affineE.symm`
injective. So the entire remaining Gauss-work content is that one predicate, probe-validated at the corrected base.

**⚠ KERNEL `QProfileSeparatesAtBase` NOT RESOLVED — the genuine uncited content; the exact gap (probe-pinned, M3
probe `/tmp/m3probe.py`):** the counts see only the `Q`-zero pattern — **`isoClass` is shell-blind**: `Q(ū−t)=1` and
`=2` give *identical* pairwise common-isotropic counts (`Z({u,t})=6` for both). So the recovery is irreducibly the
**joint** incidence content `Z(S) = #{x : Q(x−t)=0 ∀t∈S}` over all sub-frames `S` (these DO determine `u`, 81/81),
NOT a pointwise `Q`-count. **Correction to the M2 plan:** the `multiCharSum` Fourier hinge assumed *pointwise* counts,
which `isoClass` does not provide — so it does not directly discharge the kernel. The right machinery is still the
multiQuad toolkit, but assembled as **coarse-count ⟹ `Z(S)` agreement (inclusion–exclusion) → `Z(S) = ∑_{s:S→K} S(s)`
(a sum of `multiQuad`s) → joint extraction ⟹ Q-profile.** That joint extraction is the open kernel.

**Resolution paths (for `QProfileSeparatesAtBase`) — only two are viable; full detail in §10.**
**(1) the explicit Gauss/incidence computation** of `Z(S)` over the sub-frames + injectivity (= §3 Route A; Witt-free
for the kernel; all toolkit present; recommended). **(3) the structural perp-graph + Witt frame-rigidity argument**
(= §3 Route B; cleaner but blocks on building Witt in Mathlib). **Option (2) — carrying it as a probe-validated
certificate — is RULED OUT by the project quality bar:** an empirical, uncited predicate is not a citable hypothesis, so
it cannot stand as the deliverable (it would merely relabel the open content). *Risk: HIGH (the kernel is the crux).*

### Milestone 4 — the concrete `VO^-_4(3)` instance + capstone, in `FormsGraphConcrete` — **BLOCKED on the M3 kernel**
The wiring (low-risk): `Q = x₀x₁+x₂²+x₃²` over `ZMod 3` + polar-nondegeneracy; the concrete base `T = frameBase ∪ {2e₃}`
(size 6, M0.3) + `IsBase` (or `exists_greedy_base_le_log`); instantiate `isotropySeparates_of_qProfileSeparates` (M3) to
get `IsotropySeparatesAtBase`; feed `reachesRigidOrCameron_viaIsotropySeparates` ⟹ a concrete sealed `VO^-_4(3)`
*modulo {Witt `OrbitIsIsotropyClass`, G3}*. **But this requires `QProfileSeparatesAtBase Q T` as a real (proved) input —
which is the open M3 kernel (§10).** Since Option (2) (carry it) is ruled out, **M4 cannot complete until the kernel is
discharged** (or until Route 3 supplies the discreteness another way). M4 is otherwise just wiring once the kernel lands.

### Milestone 5 — generalization (follow-on, post-Gauss-work)
General `q` (char ≠ 2) then general `d`; then classes (d) alternating / (e) half-spin (reuse skeleton, symplectic/spinor
`B`); char-2 (`q=2,4`) and Suzuki (f) are separate arguments. The Witt track (`OrbitIsIsotropyClass`, B.1c-i) runs in
parallel and is required for a fully-sealed-modulo-citations instance.

---

## 10. HANDOFF — discharging the M3 kernel `QProfileSeparatesAtBase` (the two viable routes)

> **Read this first if you are picking up the Gauss work.** Everything else (M0–M2, the M3 reduction, M4 wiring) is
> built and axiom-clean; the *entire* remaining Gauss-work content is the one predicate **`QProfileSeparatesAtBase Q T`**
> (`FormsGraphConcrete.lean`). This section is the concrete plan for the only two viable routes. They map exactly onto
> this doc's older §3 Routes A/B, now sharpened by the M3 findings.

### 10.0 What the kernel is, precisely
For `Q = x₀x₁+x₂²+x₃²` over `ZMod 3` and `T = frameBase ∪ {2e₃}` (size 6): prove **fine isotropy-count agreement at
`T` ⟹ `Q`-profile agreement** (`Q ū = Q ū'` and `Q(ū−eᵢ)=Q(ū'−eᵢ)` ∀ basis `eᵢ`). Then `isotropySeparates_of_qProfileSeparates`
(landed) + `coords_determine` (landed) finish `IsotropySeparatesAtBase`, and the capstone seals (modulo Witt + G3).

**The M3 structural facts that constrain any route (probe-pinned, reproducible — §10.3):**
- The counts see ONLY the `Q`-zero pattern (`isoClass` is **shell-blind**: `Q(ū−t)=1` and `=2` give *identical*
  pairwise common-isotropic counts). So no route can read `Q(ū−t)` off a *single* base point, and the pointwise-`Q`-count
  machinery (`multiCharSum`, M2) is OFF-PATH.
- The recovery is irreducibly the **joint isotropic-incidence counts** `Z(S) := #{x : Q(x−t)=0 ∀t∈S}` over sub-frames
  `S ⊆ T∪{u}`. The full collection `{Z(S)}` DOES determine `u` (81/81). The work is computing and inverting them.

### 10.1 Route 1 (= §3 Route A) — explicit Gauss/incidence computation. **RECOMMENDED** (Witt-free for the kernel).
Build, in order (all tools are landed unless flagged):
1. **The fold** (deferred from M1). Express the `IsotropySeparatesAtBase` count over `T∪{u}` (with `z≠u`) as a
   `count_pi_setValued` instance: fold `T` (a `Finset`) + the `u`-slot into one `Fintype` index `ι = ↥T ⊕ {⋆}`, with
   the single `x=ū` correction (one point). Output: fine-count agreement ⟹ **coarse `Q`-zero-pattern count agreement**.
   *Tools:* `coarse_eq_sum_iso`, `isotropy_count_transport`, `count_pi_setValued`. *Effort: moderate (Finset/Fintype
   bookkeeping + the `x=ū` term).*
2. **Coarse ⟹ `Z(S)`.** The coarse joint distribution determines the marginals `Z(S)` (sum over the off-`S` pattern
   bits — Möbius/inclusion–exclusion over the subset lattice; `x=u` correction is deterministic). *Effort: moderate,
   pure combinatorics.*
3. **`Z(S)` closed form.** `Z_u(S)·q^{|S|} = ∑_{s:S→K} S(s)` where `S(s)=∑_x ψ(∑_{t∈S} s_t·Q(x−t))`, split on
   `R=∑_t s_t`: `R≠0 →` `sum_addChar_multiQuad` (`S(s)=ψ(Gram-expr(s))·∑_x ψ(R·Qx)`); `R=0 →`
   `sum_addChar_multiQuad_zero` + `sum_addChar_linearMap`. Yields `Z_u(S)` as a character sum in the Gram entries
   `{Q(t), polar Q t t' : t,t'∈S}` — which, for `S∋⋆`, include `Q(u)` and `polar Q u t` (`t∈S∩T`). *Tools: all landed.
   Effort: moderate–heavy (the `s:S→K` sum + the global value `∑_x ψ(R·Qx)`, see §10.2).*
4. **The extraction / injectivity — THE OPEN STEP.** Show `{Z̃_u(S)}_S` determines the `Q`-profile (note: `Z̃` over
   `z≠u`, not raw `Z` — see §10.3(A)). **De-risk DONE (2026-06-20, §10.3):** the inversion holds (81/81) but is genuine
   joint affine-quadric intersection-number injectivity — **no closed-form / linear / single-partner shortcut**, and
   **size-3 incidences are structurally required** (pairwise is always shell-blind). The one structural aid: it
   **factors per-coordinate** — `Q(u−e_i)` is determined by the disjoint triple-count vector through `e_i` (§10.3(F)).
   The closed form and the `polar`-substitution are validated (§10.3(C/D)). *This is the genuine uncited content — a
   substantial analytic effort, not a mechanical inversion.* `decide`/`native_decide` are out (§10.3).

### 10.2 Route 1 prerequisites (also needed by M4; build regardless)
- **A concrete character target ring `R'` + primitive `ψ`.** Need `R'` a domain with a primitive additive character
  `ψ : ZMod 3 → R'` (`ψ.IsPrimitive`). Candidates: `ℂ`, or the cyclotomic `ℤ[ζ₃]`/`ℚ(ζ₃)`. Mathlib `AddChar`/`ZMod`
  primitivity lemmas exist; pick the one with the easiest `IsPrimitive` + nonzero Gauss value.
- **The orthogonal basis for `Q = x₀x₁+x₂²+x₃²`** (for the diagonalization lemmas `sum_quadForm_eval` /
  `sum_addChar_quadForm_smul`). `x₀x₁` is hyperbolic — complete the square: e.g. `v₀=(1,1,0,0)` (`Q=1`), `v₁=(1,2,0,0)`
  (`Q=1·2=2≠0`), `v₂=e₂` (`Q=1`), `v₃=e₃` (`Q=1`); CHECK `IsOrthoᵢ` (pairwise `polar=0`) and `Q(vᵢ)≠0`. (Polar:
  `B(x,y)=x₀y₁+y₀x₁+2x₂y₂+2x₃y₃`.)
- **`∑_x ψ(Q x) ≠ 0`** (the cancellable global value). Over `ℂ`, `|gaussSum|²=q` so it is nonzero; needs the Mathlib
  gaussSum magnitude (`gaussSum_mul_gaussSum…`) or a direct evaluation via `sum_quadForm_eval` (`= (∏χ(vᵢ))·Gᵈ`, `G≠0`).
- **Polar-nondegeneracy of `Q`** (for `coords_determine` in the landed reduction): `B` above is nondegenerate over `F₃`
  — easy (`Q.polarBilin.Nondegenerate`).

### 10.3 The probes — reproduction spec (the `/tmp/*.py` are ephemeral; rebuild from this)
`V = F₃⁴` (81 pts); `Q(x)=x₀x₁+x₂²+x₃² mod 3`; `iso(w)=0 if w=0 else 1 if Q(w)=0 else 2`; `coarse(w)=0 if Q(w)=0 else 1`.
Bases: `frameBase={0,e₀,e₁,e₂,e₃}` (size 5), `T=frameBase∪{(0,0,0,2)}` (size 6). Count-signature of `u` = the multiset
over `z≠u` of `((cls(z−t))_{t∈T}, cls(z−u))`. Key reproducible findings: (i) frameBase signature has a twin
`(0,0,1,2)~(0,0,2,1)` (both fine & coarse); (ii) at `T`, coarse-signature is injective (81/81) AND coarse-agreement ⟹
`(Q(u−t))_{t∈frame}` agreement (no counterexample); (iii) pairwise `Z({u,t})=6` for both `Q(u−t)∈{1,2}` (shell-blind),
but `{Z(S)}` over all `S⊆T∪{u}` is injective in `u` (81/81).

**★ ROUTE-1.4 DE-RISK DONE (2026-06-20, `/tmp/m4probe{,2,3}.py`).** Findings that scope the open kernel:
- **(A) Provable target = `Z̃` over `z≠u`, NOT raw `Z` over all `x`.** `rawZ_u(S) − Z̃_u(S) = [Q(u−t)=0 ∀t∈S′]` = the
  *shell-blind* iso-bit indicator (the `x=u` term). The count-antecedent controls only `Z̃`; the Gauss closed form
  computes `rawZ`, so the proof must track the `x=u` correction. `Z̃` (z≠u) is injective in `u` (81/81).
- **(B) Size-3 incidences are STRUCTURALLY required.** `{Z̃_u(S):|S′|≤2}` is NOT injective; `{|S′|≤3}` IS (42 sets;
  greedy minimal = **10 sets, max `|S′|=3`**). Pairwise is *always* shell-blind (similitude fuses the shells of a
  single difference), independent of base — a genuine lower bound. So the proof needs the **4-point joint incidences**
  (`u`-slot + 3 base points).
- **(C/D) The closed form + Gram substitution are VALIDATED numerically.** `Z_u(S)·q^{|S|} = ∑_{r:S→F₃} ∑_y ψ(∑_b r_b
  Q(y−b))` (the `countk`/multiQuad form) matches `rawZ`; and `Z_u(S) = #{y : Q(y)=0 ∧ ∀t∈S′, polar(y,u−t)=−Q(u−t)}`
  (the `y=z−u` substitution) matches. The Gauss toolkit computes the right object.
- **(F) ★ The recovery FACTORS per-coordinate (the key structural aid).** `Q(u−e_i)` is determined by the vector of
  triple-counts *through* `e_i`, `{Z̃_u({e_i,t′,⋆}) : t′∈T}`: shells `1` and `2` give **disjoint** value-vectors
  (0 cross-shell collision). So an eventual proof can recover each frame coordinate separately, then `coords_determine`.
- **(G/H) BUT no clean scalar shortcut.** No linear functional (e.g. `∑_{t′} Z̃`), and no *single* partner `t′`,
  separates shell 1 from shell 2 — both are shell-blind or overlap. Recovery needs the full disjoint *vector*. Also the
  triple count is *not quite* a function of `(Q(a),Q(b),polar(a,b))` alone (degenerate-config exceptions). **⟹ the
  inversion 1.4 is genuine joint affine-quadric intersection-number injectivity — no closed-form/linear collapse.**
- **Decide/`native_decide` are OUT:** the antecedent quantifies `σ` over the full function type `Fin(p^d)→Fin 3`
  (reformulating to `T`-profiles still ≈10⁹ ops; `native_decide` banned). The proof must be analytic.

**Net:** route 1 is viable and the toolkit fits, but **step 1.4 is the deep research core, not a mechanical inversion**
— budget a substantial analytic effort. The handles for it: the per-coordinate factoring (F) + the validated closed
form (C/D) + the `z≠u` correction (A) + the size-3 lower bound (B). The clean architecture is §10.6.

### 10.6 Step-4 attack — the Lemma A / Lemma B architecture (2026-06-20, `/tmp/m4{anal,arch,deg,final}.py`). **VIABLE.**
The step-4 inversion splits into two pieces; the analytic crux is bounded and **Witt-free**.

- **Lemma A (the analytic crux) — the isotropic-incidence count in closed form, on NONDEGENERATE-Gram configs.** For a
  configuration `{v₀,…,v_m}` whose difference `B`-Gram `(B(v_i−v₀, v_j−v₀))_{i,j}` is **nondegenerate**, the count
  `N = #{y : Q(y−v_j)=0 ∀j}` is an **explicit function of that Gram** (probe-verified: `count = f(B-Gram)` on all
  nondegenerate-Gram configs, single-valued; value sets are tiny — `{6}` for `m=1`, `{1,2}` for `m=2`, `{0,1,2}` for
  `m=3`). **The argument is elementary + Witt-FREE:** translate to `y₀+W` with `W = (span of the differences)^⊥`;
  nondegenerate Gram ⟹ `V = U ⊥ W` (Mathlib `BilinForm` orthogonal complement / `isCompl`, NO Witt extension); then
  `N` = an affine-quadric count of `Q|_W` (toolkit **`card_quadForm_eq`**), whose discriminant is `disc Q / disc Gram`
  by discriminant-multiplicativity over `⊥` (elementary block-determinant, NOT Witt cancellation), and whose value is a
  quadratic-character / Gauss-sum expression. **Crucial:** the *explicit* route is Witt-free, whereas the abstract
  "same Gram ⟹ same count via an ambient isometry" route would need **Witt cancellation** (Mathlib-absent) — so Lemma A
  must be done explicitly, which is exactly what the toolkit supports.
- **★ The degenerate cases are AVOIDED BY BASE CHOICE (refined 2026-06-20, `/tmp/m4{gap,base}.py`).** Caveat to the
  naive "drop degenerate": with the size-6 base, **290/3240 pairs are separated only by a config that is degenerate for
  one of the two vertices** — and whether `{u}∪S'` is nondegenerate *depends on `u`*, so the `u`-`u'` comparison can
  pit a Lemma-A value against an unknown degenerate value. The "nondegenerate-masked signature is injective" fact is
  true but the mask is `u`-dependent, so it does **not** by itself let the proof drop degenerate configs. **The fix:
  enlarge the base.** With the **size-9 base** `T₉ = frameBase ∪ {(0,0,0,2), (1,1,1,1), (1,2,1,2), (1,0,1,0)}`, every
  pair `u ≠ u'` is separated by a config whose Gram is **nondegenerate for BOTH** `u` and `u'` (probe: all 3240 pairs).
  So with `T₉`, only the clean nondegenerate Lemma A is ever needed — degenerate configs never enter the comparison.
  (`T₉` is still a bounded base, size `9 ≈ 2d+1`; coarse counts still suffice.)
- **Lemma B (the recovery) — clean.** Given Lemma A (counts ↦ config-Gram data), recover `u`: the nondegenerate-Gram
  count signature determines the configuration Gram (a finite, explicit `F`-table fact — tiny value sets), and the Gram
  determines `u` (polar nondegeneracy; probe: `B(u,t)` over `t∈T` determines `u` — clean linear algebra, a mild
  generalization of the landed `coords_determine`).

**Gaps + tools (all bounded, no fundamental obstruction):**
1. *Lemma A:* affine-quadric count of `Q|_W` on the nondeg orthogonal complement. Tools: Mathlib orthogonal-complement
   (`LinearMap.BilinForm.orthogonal`, nondeg ⟹ `isCompl`), toolkit `card_quadForm_eq` / `sum_quadForm_eval` /
   multiQuad, Gauss-sum magnitude (`gaussSum_sq`). **Sub-gap to check:** a Mathlib lemma for `disc(Q) = disc(Q|_U)·disc(Q|_W)`
   over an orthogonal decomposition (block-determinant; may need a small bridge lemma). The real analytic effort, but
   structured, general (reusable across the `VO` families), and Witt-free.
2. *Lemma B:* the `F`-table (finite, explicit — `decide`-feasible at this size since it is over Gram tuples in `F₃`, not
   the 81-point cone) + Gram→`u` (generalize `coords_determine` to the polar-coordinate row). Clean.
3. *Plumbing:* the M1 "fold" + inclusion–exclusion connecting the abstract `IsotropySeparatesAtBase` antecedent to the
   `{Z̃(S)}` over the nondegenerate-Gram sub-collection (with the `z≠u` correction, §10.3(A)). Moderate.

**Verdict: step 4 is VIABLE** — a substantial but bounded multi-session analytic build (Lemma A is the crux), Witt-free,
fully toolkit-supported, with the degenerate cases eliminated. No fundamental obstruction was found. Combined with this
session's Witt removal, discharging Lemma A + B seals `VO⁻₄(3)` modulo `{G3}` alone.

### 10.7 Lemma A — IMPLEMENTATION STARTED (2026-06-20, `ChainDescent/ScratchLemmaA.lean`, all axiom-clean)
The plan's steps A1–A6 are landing bottom-up (WIP scratch module, `lake env lean`-verified, not yet in the build):
- **A1 `isoIncidence_eq_linearConds`** ✓ — `Q w = 0 ⟹ (Q (w−a j)=0 ↔ polar Q w (a j) = Q (a j))`, so the count is
  over affine-linear conditions. (Via `polar_eq_of_sub`.)
- **A4-core `map_add_of_polar_zero`** ✓ — `polar Q w x = 0 ⟹ Q (w+x) = Q w + Q x` (the homogenizing identity).
- **A3 `count_coset`** ✓ — given any realizing `w₀`, the count = count over `Uᗮ` of `x` with `Q (w₀+x)=0`
  (bijection `w ↦ w−w₀`, polar bilinearity).
- **A4-link `polar_w0_perp`** ✓ — `w₀ = ∑ c k • a k ⟹ polar Q w₀ x = 0` for `x ∈ Uᗮ` (via `polar_sum_right`).
- **★ A1+A3+A4 combined `reduction_to_levelset`** ✓ — **the count is a HOMOGENEOUS level-set count**
  `#{x ∈ Uᗮ : Q x = −Q w₀}`, given a spanning solution `w₀ = ∑ c k • a k`. The linear term has vanished; this is the
  conceptual heart of Lemma A and the exact input shape `card_quadForm_eq` wants.

- **A-M2 ✅ DONE** (`spanning_w0_exists` + `reduction_to_levelset_nondeg`, axiom-clean): the spanning `w₀` exists for
  invertible config Gram (`IsUnit G.det`, witness `(Q∘a) ᵥ* G⁻¹`), so the count is unconditionally the homogeneous
  level-set on nondegenerate configs.

- **A-M3 increment 1 ✅ DONE (2026-06-21, `levelset_fourier`, axiom-clean) — the Route-B Fourier setup.** The level-set
  count `#{x : (∀ j, polar Q x (a j)=0) ∧ Q x = c}`, scaled by `q^{m+1}`, is a double character sum indexed by
  `Option (Fin m)` (`none` = quadratic dual `r none`, `some j` = linear duals), with the `m` linear duals collapsed by
  bilinearity (`polar_sum_right`) into one linear term `polar Q x (∑ j, r (some j) • a j)`. Via `countk_eq_sum_charsum`
  (the inner sum is over ALL of `V` — **no subspace `Uᗮ` formed**, the Route-B payoff).
- **A-M3 increment 2a ✅ DONE (2026-06-21, `levelset_fourier_prod`, axiom-clean) — `(s, ρ)` reindex.** Splits the
  `Option (Fin m) → F` dual into the quadratic dual `s` and the linear duals `ρ` (`Equiv.piOptionEquivProd`); the count
  is now `∑_s ∑_ρ ψ(−s·c)·∑_x ψ(s·Q x + polar Q x (∑ⱼ ρⱼ•aⱼ))`, the exact shape the `s`-split consumes.

- **A-M3 increment 2b ✅ DONE (2026-06-21, `levelset_fourier_split`, axiom-clean) — the `s`-split (D1 on the bulk).**
  Split `∑_s` at `s=0`: the `s=0` boundary is left as `∑_ρ ∑_x ψ(polar Q x (∑ⱼ ρⱼ•aⱼ))` (collapse → 2c); the `s≠0`
  bulk evaluated via **D1 `sum_addChar_quadForm_linear`** (each `s` as `Units.mk0 s`): inner `x`-sum becomes
  `ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))·∑_x ψ(s·Q x)`.
- **A-M3 increment 2c ✅ DONE (2026-06-21, `s0_boundary_collapse`, axiom-clean) — the `s=0` boundary `= q^d`.** Via
  `sum_addChar_linearMap` (`φ_ρ = (polarBilin Q).flip (∑ⱼ ρⱼ•aⱼ)`) the inner sum is `|V|·[φ_ρ=0]`, and `φ_ρ=0 ⟺ ρ=0`
  using **only the config-Gram nondegeneracy** (`IsUnit G.det`): `φ_ρ(aᵢ)=0` gives `(G *ᵥ ρ)ᵢ=0`, `G` invertible ⟹ `ρ=0`.
  (Sharper than expected — no full `Q`-nondegeneracy needed.)
- **★ A-M3 ✅ COMPLETE (2026-06-21, `levelset_count_eq`, axiom-clean) — the assembled closed form.** For nondeg config
  Gram: `count·q^{m+1} = |V| + ∑_{s≠0} ψ(−s·c)·(ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))·∑_x ψ(s·Q x)) summed over ρ`. **Everything that
  remains for Lemma A is A-M4** = evaluating the two Gauss sums; see §10.11 (scoping).

**Remaining for full Lemma A — A-M4 (scoped in §10.11):** evaluate the global `∑_x ψ(s·Q x)=χ(s)^d·W` (scaling, fixed
basis of `Q`) and the config-Gram `∑_ρ ψ(−s⁻¹·Q(∑ⱼ ρⱼ•aⱼ))` (Gauss sum of `QR=Q.comp L` on `Fin m→F`), reducing
`count` to a **function of `(m, discr QR, c_lev)`** (`discr QR = 2^{−m} det G`). The recommended A-M4a deliverable is the
**well-definedness** (count = `f(m, discr QR, c_lev)`), which needs NO `gaussSum_sq` / explicit-integer reduction and is
exactly what B-M3 consumes.

No new obstruction surfaced while implementing; the reduction to a homogeneous level-set went through cleanly and
axiom-clean. The remaining A2/A5/A6 are linear-algebra/basis lifts, not new mathematics.

### 10.8 FULL MILESTONE PLAN for step 4 (Lemma A + Lemma B + assembly), beginning to end (2026-06-20)
> **▶ FRESH READER — START HERE.** Landed & axiom-clean (WIP scratch, §10.5): the WHOLE A-side — Lemma A (A-M1…A-M4a,
> all 5 gaps, `ScratchLemmaA.lean`, 17 decls) + B-M1 + B-M2-bridge (`ScratchLemmaB.lean`). **NEXT = B-M3** — the last
> step; **its full handoff (gaps, tools, 3 spike-ranked approaches) is §10.13.** Then ASM. The capstone needs NO Witt
> (§10.5). The A-M3/A-M4 milestone detail below is now build-history; the live frontier is §10.13. Read §10.6
> (architecture) + §10.3 (probe facts) for background.

The target is `IsotropySeparatesAtBase Q T₉`, consumed by the Witt-free capstone
`reachesRigidOrCameron_viaIsotropySeparates_wittFree` (CascadeAffine §OrthogonalForm) ⟹ sealed `VO⁻₄(3)` mod `{G3}`.
**Use the size-9 base `T₉ = frameBase ∪ {(0,0,0,2),(1,1,1,1),(1,2,1,2),(1,0,1,0)}`** throughout (§10.6: it makes every
pair separable by a both-nondegenerate config, so degenerate Lemma A is never needed). Each milestone ≈ one work
session; **batch a milestone's lemmas, then ONE build + index + doc cycle at the boundary** (process rule).

**Conventions fixed for the whole build (record once, reuse):**
- `θ(u) := (Q (affineE.symm u), fun t => polar Q (affineE.symm u) (affineE.symm t))` — the **Gram parameters** of `u`
  against the base. `θ(u)` determines `u` (polar nondegeneracy; the `coords_determine` mechanism).
- The working count is `Z̃` over `z ≠ u` (NOT raw `Z`); raw `Z = Z̃ + [u in the config's isotropic set]`, and the
  correction is the shell-blind `x=u` term (§10.3(A)). Lemma A computes raw `Z`; B-M1 carries the correction.
- Coarse counts (`Q=0` vs `Q≠0`) suffice (M0); fine→coarse is the landed `coarse_eq_sum_iso`.

#### Lemma A — the isotropic-incidence count = explicit Gram-function (nondegenerate configs only)
- **A-M1 ✅ DONE** (`ScratchLemmaA.lean`, axiom-clean): the homogeneous reduction `reduction_to_levelset` (A1 linear
  conditions + A3 coset + A4 linear-term-vanish) — count `= #{x ∈ Uᗮ : Q x = −Q w₀}` given a spanning `w₀ = ∑ cₖ aₖ`.
- **A-M2 ✅ DONE** (`ScratchLemmaA.lean`, axiom-clean): `spanning_w0_exists` (hypothesis `IsUnit G.det` for the Gram
  matrix `G i j = polar Q (a i) (a j)`; witness `c := (Q∘a) ᵥ* G⁻¹`, via `Matrix.vecMul_vecMul` /
  `nonsing_inv_mul` / `vecMul_one`) + **`reduction_to_levelset_nondeg`** — combines A-M1∘A-M2: for invertible config
  Gram, the count is unconditionally the homogeneous level-set `#{x ∈ Uᗮ : Q x = − Q w₀}` (`w₀ = ∑ cₖ aₖ` explicit).
- **A-M3 (the next session's target) — ROUTE B (full-space char-sum), chosen + spike-validated (§10.10).** Do **NOT**
  restrict `Q` to the subspace `↥Uᗮ`. `reduction_to_levelset_nondeg` already outputs the count as a **filter over the full
  `V`**: `#{x : (∀ j, polar Q x (a j)=0) ∧ Q x = c}` (`c = −Q w₀`). Char-sum *that* directly over `V` (via the existing
  `GaussCount` toolkit), never forming `↥Uᗮ`:
    - `count·q^{m+1} = ∑_{s∈F, r∈F^m} ψ(−s·c) · ∑_x ψ(s·Q x + ∑_j r_j·polar Q x (a_j))`;
    - by bilinearity `∑_j r_j·polar Q x (a_j) = polar Q x a*` with `a* = ∑_j r_j a_j` — a **single** linear term — so the
      inner `x`-sum is **D1 `sum_addChar_quadForm_linear`** (`s≠0`) / **`sum_addChar_linearMap`** (`s=0`), both landed;
    - the residual `r`-sum is a Gauss sum of the **config-Gram form `QR(r) = Q(∑_j r_j a_j)` on the concrete space `Fin m → F₃`**
      (Gram `= G`) — handled by `sum_addChar_quadForm_smul`/`sum_quadForm_eval`; the full-space `W = ∑ψ(Q x)` uses the **fixed
      concrete** orthogonal basis `{e₀+e₁, e₀−e₁, e₂, e₃}` of `Q` (computed once, no existence lemma).
  This matches **Lemma B's object** (the config Gram `G` on `Fin m → F₃`, which B-M3 already reasons about), reuses the
  toolkit, and **handles `m=4` uniformly** (subtype route would need a separate `dim Uᗮ = 0` case; spike: `m=4` nondeg configs
  DO occur). The only *existence* fact still needed is an orthogonal basis of `QR` — but its entries never appear (see A-M4).
- **A-M4 — collapses to a 14-row table (§10.10 finding (5)): `N = N(m, det G, c_lev)`, no per-config diagonalization.**
  Spike (0 MULTI over all nondeg configs): the count depends **only** on `(m, det G, c_lev)` — the orthogonal basis of `QR`
  is needed for *existence* only, since `∏_i χ(QR(v_i)) = χ(det G)·χ(2)^?` is basis-independent (discriminant is well-defined
  up to squares; `χ` kills the change-of-basis `det²`). So A-M4 needs: (a) `det G` from the config Gram; (b) `c_lev = −Q w₀`,
  `Q w₀ = ½·(Q a)ᵀ G⁻¹ (Q a)`; (c) the `F₃` quadratic-Gauss-sum magnitude (`gaussSum_sq`: `|G|²=3`). Output: **Lemma A** =
  the 14-row table `N(m, det G, c_lev)` (`m=1→6`; `m≥2 → {0,1,2}`; full table in §10.10). Both `det G` and `c_lev` are
  explicit functions of `θ(u)`, so this is exactly the input B-M3 wants.

#### Lemma B — the counts recover `u`
- **B-M1 + B-M2 bridge ✅ DONE** (`ChainDescent/ScratchLemmaB.lean`, all axiom-clean): plumbing antecedent → `V`-side
  incidence agreement, plus the `y=0` correction to Lemma A's full count.
  - `coarse_incidence_agree` — the core: from the fine isotropy-count antecedent, the isotropic-incidence count
    `Z̃_w(S') = #{z≠w : Q(z̄−w̄)=0 ∧ ∀t∈S', Q(z̄−t̄)=0}` agrees (`u`↔`u'`) for `S'⊆T`. **Fiberwise partition by the
    isotropy profile** — same technique as `separatesAtBase_of_isotropySeparates_weak`; the "isotropic on `S'∪{⋆}`"
    consistency test is `w`-independent (bundles fine→coarse AND the incl–excl marginalization in one step).
  - `incidence_to_V` — transport + translate in ONE bijection `z ↦ z̄−w̄`: `Z̃_w(S')` (over `Fin(p^d)`) `= #{y≠0 :
    Q y=0 ∧ ∀t∈S', Q(y−(t̄−w̄))=0}` over `V`, with config differences `aₜ = t̄−w̄`.
  - `incidence_agree_V` — capstone: the `V`-side count agrees `u`↔`u'`. This is Lemma A's count **minus the `y=0`
    term** (the `z≠u` correction), in Lemma-A coordinates.
  - **B-M2 bridge ✅ DONE** (`ScratchLemmaB.lean`, axiom-clean): `cone_count_zero_split` (the `y=0` correction —
    Lemma A's full count `= ` the `y≠0` restricted count `+ [∀t∈S', Q aₜ=0]`, the Gram-determined indicator) +
    **`fullcount_agree_modulo_corr`** (capstone) — from the antecedent, the FULL Lemma-A-shaped counts agree modulo
    the correction: `fullcount_u(S') + corr_{u'} = fullcount_{u'}(S') + corr_u`. Ready to consume Lemma A's
    `fullcount = f(Gram)` (A-M4) in B-M3.
  - **Only remaining glue** (truly mechanical, deferred to B-M3 at the Lemma-A application): reindex `S'`(Finset) →
    Lemma A's `Fin m` argument (`Finset.equivFin` / `reduction_to_levelset_nondeg` instantiated at `m = S'.card`).
- **B-M2** — *Gram parametrization + both-nondeg selection.* Express each config's `Z(S)` (via Lemma A) as `f(θ(u))`;
  the config Gram and its nondegeneracy (`det ≠ 0`) are explicit functions of `θ(u)` and the fixed base. Establish the
  both-nondeg separation property of `T₉` (the §10.6 fact, as a finite check). Output: for both-nondeg `S'`,
  `count_u(S') = f_{S'}(θ(u))`.
- **B-M3 — *injectivity ⟹ `IsotropySeparatesAtBase`.* ▶ FULL HANDOFF: §10.13 (gaps, tools, 3 spike-ranked approaches).**
  Obligation: the restricted-count signature is injective over the 81 base points (`incidence_agree_V` already reduces the
  antecedent to this). **Spike-updated picture (`/tmp/spike_bm3.py`, supersedes the cautions here):** (i) a **minimal
  separating set is just 6 size-2 subsets** ⟹ the finite check is tiny; (ii) the **per-coordinate structural route is
  REFUTED** (cross-coord collision) — recovery is joint; (iii) recommended = **direct kernel `decide` over the 6-set**
  (no Lemma A; gate on a kernel-feasibility micro-spike since `native_decide` is banned), with the **Lemma-A-reduced
  `decide`** (count → `F(detG,c_lev,corr)`, the §10.12 bridge) as the robust fallback. `coords_determine` is needed only
  for a structured route, not for a pure `decide` over `u`.

#### Assembly
- **ASM** — instantiate `Q = x₀x₁+x₂²+x₃²` over `ZMod 3`, base `T₉`, `T₉.card ≤ 9`; compose B-M3 ⟹
  `IsotropySeparatesAtBase Q T₉`; feed `reachesRigidOrCameron_viaIsotropySeparates_wittFree` ⟹ **sealed `VO⁻₄(3)`
  mod `{G3}`.** Then port **both `ScratchLemmaA.lean` + `ScratchLemmaB.lean`** → a real module (likely a new
  `ChainDescent/FormsGraphLemmaA.lean` + integrate into `FormsGraphConcrete.lean`; register in `build.sh`/`lakefile`),
  regenerate `PublicTheoremIndex.md`, doc cycle.

**Dependencies:** A-M1✓→A-M2→A-M3→A-M4 (Lemma A); B-M1 ⟂ (independent plumbing); B-M2 needs {A-M4, B-M1};
B-M3 needs B-M2; ASM needs {A-M4, B-M3}. Lemma A (A-M2..A-M4) and B-M1 can proceed in parallel.

**Identified gaps / knowledge recorded here (was unmentioned):**
1. **Degenerate Lemma A is avoided only by the size-9 base** `T₉` (size-6 needs degenerate configs for 290 pairs). This
   is a hard constraint on the base choice — record `T₉`, not the size-6 base, as the live target. (Corrects §10.6.)
2. **The `z≠u` correction** (`Z̃` vs raw `Z`) must be threaded through B-M1; the correction term is the shell-blind
   `x=u` indicator.
3. **B-M3's injectivity is `decide`-feasible — DE-RISKED (§10.10 + §10.13 spikes).** `N = N(m, det G, c_lev)` factors
   through the **tiny** `F₃` Gram-tuple space (≤729), and §10.13's spike found a **minimal separating set of just 6 size-2
   subsets** — so the endpoint is a small finite check, NOT the feared `81²×configs`. **Per §10.13, the per-coordinate
   structural route (§10.3(F)) is REFUTED (recovery is joint); the recommended route is a direct kernel `decide`** (gate on
   a kernel-feasibility micro-spike; `native_decide` banned). Full B-M3 plan/approaches: **§10.13**.
4. **`coords_determine` must be generalized** from the standard frame to the polar-coordinate row `θ` over `T₉`
   (B-M3) — a mild lift of the landed lemma.
5. **A-M3's subspace machinery is AVOIDED — superseded by Route B (§10.10).** The single biggest Mathlib lift (restrict
   `Q` to `↥Uᗮ` + orthogonal anisotropic basis of a *subtype*) is **not taken**: Route B char-sums the
   `reduction_to_levelset_nondeg` output directly over the full `V`, and the `(m, det G, c_lev)` collapse means even the
   config-form basis is needed for *existence* only (its entries never appear). No subtype instances, no computed basis.
6. **Char-2 / other `q` / other families** are out of scope here (M5); this plan is `VO⁻₄(3)` only.

### 10.10 A-M3 tactic spike — ROUTE B chosen + validated (2026-06-21, `/tmp/spike_routeB.py`)
Spike to pick the A-M3 count-evaluation tactic (the user steer: match Lemma B's object). Over `VO⁻₄(3)`, base `T₉`, all
`(u, S')` with nondegenerate config Gram (12942 configs). **Reproduction spec** (rebuild the ephemeral script from this):
`V=F₃⁴`, `Q=x₀x₁+x₂²+x₃²`, `polar(x,y)=Q(x+y)−Q x−Q y`; `fullcount(u,S')=#{y : Q y=0 ∧ ∀t∈S', Q(y−(t̄−ū))=0}`; config
diffs `aₜ=t̄−ū`, Gram `Gᵢⱼ=polar(aᵢ,aⱼ)`; `w₀=∑cⱼaⱼ` with `G c=(Q aⱼ)ⱼ`, `c_lev=−Q w₀`; `ψ(t)=ω^t` (`ω=e^{2πi/3}`),
`χ(0,1,2)=(0,1,−1)`, `W=∑_x ψ(Q x)`. Route-B closed form: `fullcount·q^{m+1}=q^d+∑_{s≠0}ψ(−s·c_lev)·χ(s)^d·W·R(s)`,
`R(s)=∑_{r∈F₃^m}ψ(−s⁻¹·Q(∑rⱼaⱼ))`.

**Findings (all green):**
1. **`N` is single-valued per config Gram** — 0 MULTI / 12942 (2837 distinct Grams). Lemma A's premise holds in route-B form.
2. **Route-B closed form reproduces `N` exactly** — 0 mismatches / 12942. The full-space char-sum tactic closes end-to-end
   (D1 + scaling + full-space `W` + config-Gram Gauss sum); **no subspace restriction**.
3. **Config dims `m=|S'|` occurring (nondeg): `{1,2,3,4}`** — `m=4` nondeg configs DO occur (corrects the earlier
   "`n∈{1,2,3}`"). Route B handles `m=4` uniformly; the subtype route would need a separate `dim Uᗮ=0` case. Distinct
   `N` values: `{0,1,2,6}`.
4. **Endpoint (B-M3): all-`S'` `fullcount` signature injective 81/81;** every one of the 3240 pairs is separated by a
   **both-nondeg** `S'` (0 failures) — `T₉` confirmed, degenerate Lemma A never needed.
5. **★ `N` depends ONLY on `(m, det G, c_lev)`** — 0 MULTI, collapsing to a **14-row table** (below). ⟹ A-M3 needs the
   orthogonal basis of the config form for *existence* only (`∏χ(QR vᵢ)=χ(det G)·const`, basis-independent); **no per-config
   diagonalization, no computed basis**. Both `det G` and `c_lev` are explicit functions of `θ(u)`, so B-M3's injectivity
   factors through this table over the tiny Gram-tuple space (`m=1→3`, `m=2→27`, `m=3→729`).

The 14-row Lemma-A table (`m`, `det G`, `c_lev` → `N`): `m=1`: `(1,1)→6,(2,2)→6`. `m=2`: `(1,1)→2,(1,2)→2,(2,0)→1`.
`m=3`: `(1,0)→1,(1,1)→2,(1,2)→0,(2,0)→1,(2,1)→0,(2,2)→2`. `m=4`: `(2,0)→1,(2,1)→0,(2,2)→0`.

**Verdict:** Route B is the A-M3 tactic. It matches Lemma B's config-Gram object, reuses the toolkit, avoids the subtype
machinery (old gap #5) AND the feared kernel `decide` blow-up (old gap #3). A-M3 = char-sum the
`reduction_to_levelset_nondeg` output over `V`; A-M4 = pin `N` to the 14-row `(m, det G, c_lev)` table via discriminant
well-definedness + the `F₃` Gauss-sum magnitude. The remaining genuine Mathlib lift is the *existence* of an orthogonal
basis of a nondeg form on `Fin m → F₃` (`exists_orthogonalBasis`, char ≠ 2) + discriminant-up-to-squares — structural,
one-time, not per-config.

### 10.11 A-M4 scoping — the two Gauss sums + the discriminant collapse (2026-06-21; A-M3 done, this is next)
**State.** A-M3 is COMPLETE: `levelset_count_eq` (axiom-clean) gives, for nondeg config Gram,
`count·q^{m+1} = |V| + ∑_{s≠0} ψ(−s·c)·(ψ(−s⁻¹·Q(∑ⱼρⱼaⱼ))·∑_x ψ(s·Q x))` summed over `ρ`. A-M4 evaluates the two
Gauss sums and reduces `count` to a **function of `(m, discr QR, c_lev)`**.

**A-M4 deliverable (recommended = A-M4a, well-definedness — NO explicit-integer reduction needed).** Prove
`count = f(m, discr QR, c_lev)` (two nondeg configs with equal `(m, discr QR, c_lev)` have equal count), where
`QR := Q.comp L`, `L : (Fin m → F) →ₗ V`, `L ρ = ∑ⱼ ρⱼ•aⱼ` (the config form), and `discr QR = QR.toMatrix'.det = 2^{−m}·det G`.
This is **exactly what B-M3 consumes** (B-M3 then does the finite injectivity over the `(discr, c_lev)`-tuples per `S'`). It
needs the two Gauss sums but **NOT** `gaussSum_sq` or the `F₃` `s`-sum integer evaluation (that is the optional A-M4b, only
if B-M3's injectivity turns out to need concrete integers — likely avoidable).

**The two Gauss sums (both via the landed `GaussCount` toolkit):**
- *Global* `∑_x ψ(s·Q x) = χ(s)^d · W`, `W = ∑_x ψ(Q x)` — config-INDEPENDENT (shared by `u`,`u'`). `sum_addChar_quadForm_smul`;
  `W` via `sum_quadForm_eval` with the **fixed concrete** orthogonal basis `{e₀+e₁, e₀−e₁, e₂, e₃}` of `Q` (all `Q`-values
  `1,2,1,1 ≠ 0`, pairwise polar-orthogonal — a one-time check).
- *Config* `∑_ρ ψ(−s⁻¹·QR ρ) = χ(−s⁻¹)^m · χ(discr QR) · gaussSum^m` via `sum_addChar_quadForm_smul` + `sum_quadForm_eval`
  on `QR`, with the gap-5 collapse `∏ᵢ χ(QR vᵢ) = χ(discr QR)` (below).

**Gaps + tools (all located, Mathlib-present):**
1. **Build `QR` + Gram = `G`. ✅ DONE (2026-06-21, `ScratchLemmaA.lean`, axiom-clean):** `configForm Q a := Q.comp (Fintype.linearCombination (ZMod p) a)`;
   `configForm_apply` (`QR ρ = Q(∑ⱼρⱼaⱼ)`); `polar_configForm` (transports along `L`); **`polar_configForm_single`** (`polar QR eᵢ eⱼ = polar Q aᵢ aⱼ = Gᵢⱼ`).
   `L = Fintype.linearCombination`, `L (Pi.single i 1) = aᵢ` (`linComb_single`).
2. **`QR` nondegenerate ⟸ `IsUnit G.det`. ✅ DONE (2026-06-21, `configForm_nondegenerate`, axiom-clean).** Cleaner than the
   matrix-det route: `IsRefl.nondegenerate_iff_separatingLeft` (associated is symmetric) reduces to `SeparatingLeft`; from
   `∀ y, associated QR x y = 0` get `polar QR x eᵢ = 0` (`two_nsmul_associated` to dodge the `⅟2`-in-`End`), i.e. `G *ᵥ x = 0`,
   and `G` invertible ⟹ `x = 0` (the same `mulVec`/`nonsing_inv_mul` argument as `s0_boundary_collapse`). Needs `[Invertible (2:ZMod p)]`.
3. **Orthogonal basis ⟹ anisotropic. ✅ DONE (2026-06-21, `configForm_exists_orthoBasis`, axiom-clean).** Cleaner than
   planned — Mathlib already packages the radical argument: `exists_orthogonal_basis (associated_isSymm (ZMod p) QR)` gives
   orthogonal `v`, and **`IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft`** (fed gap-2's `SeparatingLeft`) +
   `simp_rw [LinearMap.IsOrtho, associated_eq_self_apply]` yields `∀ i, QR (v i) ≠ 0` directly. Returns the `(v, hv, hw)`
   triple indexed by `Fin (finrank ..)` — exactly the toolkit's index type (no `Fin m` reconciliation needed yet).
4. **The two Gauss sums. ✅ config part DONE (2026-06-21, `configGaussSum_eval`, axiom-clean):**
   `∑_ρ ψ(s·QR ρ) = χ(s)^n · (∏ᵢ χ(QR vᵢ)) · gaussSum^n` (`n = finrank`), composing `sum_addChar_quadForm_smul` +
   `sum_quadForm_eval` (closes by `rfl`). This **isolates `∏ᵢ χ(QR vᵢ)` as the sole config-basis-dependent factor — the
   clean approach point for gap-5.** The global `∑_x ψ(s·Q x) = χ(s)^d·W` is the same `sum_addChar_quadForm_smul`, applied
   at assembly with the fixed `Q`-basis (`hF : ringChar (ZMod 3) ≠ 2`, `[Invertible (2:ZMod 3)]`).
5. **★ The discriminant collapse `∏ᵢ χ(QR vᵢ) = χ(D)` (gap-5, THE CRUX). ✅ DONE (2026-06-21, `prod_quadChar_eq_det`,
   axiom-clean).** Came out as planned. **Design choice that sidestepped the `Fin m`↔`Fin (finrank)` index mismatch:** the
   reference invariant is `D := (BilinForm.toMatrix b₀ (associated QR)).det` with `b₀ = Module.finBasis` (NOT `Pi.basisFun`),
   so `b₀` and `v` share the `Fin (finrank)` index and the change-of-basis matrix `P = b₀.toMatrix v` is square. Steps: (1)
   `toMatrix v (associated QR) = Matrix.diagonal (QR∘v)` (`toMatrix_apply` + `isOrthoᵢ_def` off-diag + `associated_eq_self_apply`
   diag) ⟹ `det = ∏ QR vᵢ`; (2) `toMatrix_mul_basis_toMatrix` ⟹ `P.det·D·P.det = ∏ QR vᵢ`, `P.det ≠ 0` from
   `Basis.toMatrix_mul_toMatrix_flip`; (3) `map_prod` + `map_mul` + `quadraticChar_sq_one` (kills `P.det²`) ⟹ `∏ χ(QR vᵢ) = χ(D)`.
   `D` is a basis-free config invariant (its relation to the `Fin m`-indexed `det G'` is a B-M3 concern, deferred).

**ONE viable approach (recommended).** Do **A-M4a** (well-definedness) in this order: (1) `QR`+Gram, (2) nondeg via `discr=½G`,
(3) anisotropic-basis lemma, (4) the config Gauss sum `= χ(−s⁻¹)^m·χ(discr QR)·gaussSum^m` (the gap-5 collapse is the work), (5)
the global Gauss sum `= χ(s)^d·W` with the fixed `Q`-basis, (6) substitute into `levelset_count_eq` ⟹ `count = f(m, discr QR, c_lev)`.
Then hand `f` to B-M3. Risk is concentrated entirely in gap-5's basis-change-determinant bookkeeping; no fundamental obstruction.

**A-M4b viability — CONFIRMED, and A-M4b is NOT a blocker (2026-06-21).** A-M4b (the explicit 14-row integer table) is bounded
and tool-complete: `W = ∑ψ(Q x) = −9` (d=4: `∏χ = χ(2) = −1`, `gaussSum^4 = (gaussSum²)² = (χ(−1)·3)² = 9`), `gaussSum² = −3`
(`gaussSum_sq`, q=3, `χ(−1)=−1`), and the `s`-sum is a **2-term** sum over `F₃ˣ = {1,2}` with `ψ = ω^•`; for odd `m` the
irrational `gaussSum` cancels against the `χ(s)`-twisted `s`-sum (`gaussSum·(ψ(−c)−ψ(c))` is rational). **But A-M4b's closed
form is not required for the seal:** once A-M4a gives `count = f(m, discr QR, c_lev)` (well-definedness), each needed `f`-value
is obtained from a **single representative count** (a one-shot `decide` over 81 points, ≤14 tuples), and B-M3's injectivity then
runs over the tiny `(discr, c_lev)` Gram-tuple space — no `gaussSum`/`ℤ[ζ₃]` evaluation needed downstream. So **A-M4a is the
load-bearing deliverable**; the A route is viable end-to-end with A-M4b as an optional convenience.

### 10.12 A-M4a config-side ASSEMBLED + B-M3 prep (2026-06-21) — **all A-M4a gaps 1–5 DONE**
**`configGaussSum_eq_det` (axiom-clean) wraps the A-M4a config side:** eliminating the existential basis (gap-3 ∘ gap-4 ∘
gap-5), for nondeg config Gram and unit `s`,
`∑_ρ ψ(s·QR ρ) = χ(s)^n · χ(D) · gaussSum^n`, `D = (BilinForm.toMatrix finBasis (associated (configForm Q a))).det` a
**basis-free config invariant**, `n = finrank`. The config-dependence of the count is now ENTIRELY through `(D, c)`.

**The remaining count-assembly bridge (thin, B-M3's first step or an ASM lemma):** substitute into `levelset_count_eq`,
at scalar `−s⁻¹`, the config sum `configGaussSum_eq_det` + the global `∑_x ψ(s·Q x) = χ(s)^d·W` (`sum_addChar_quadForm_smul`
with a carried fixed `Q`-basis), factoring the `ρ`-constants. Output:
`(count : R')·q^{m+1} = |V| + ∑_{s≠0} ψ(−s c)·χ(s)^d·W·χ(−s⁻¹)^n·χ(D)·gaussSum^n =: F(D, c)` — a function of `(D, c)` only.
Then chain `reduction_to_levelset_nondeg` (sets `c = c_lev = −Q w₀`) + `isoIncidence_eq_linearConds` to land the **isotropic**
count `= F(D, c_lev)`.

**What B-M3 consumes / must do (its own planning increment):**
1. **`count_a = F(D_a, c_lev,a)`** (above) — config-dependence only through `(D_a, c_lev,a)`, both **functions of `θ(u)`**
   (polynomials in the Gram entries `polar Q (t̄ᵢ−ū)(t̄ⱼ−ū)` and `Q(t̄ⱼ−ū)`; `D ↔ det G'` relation = a B-M3 sub-task, the
   `½^m`/finBasis-change factor).
2. **Restricted counts agree** (`incidence_agree_V`, landed) + the `corr` indicator (`cone_count_zero_split`, landed, also
   `(D,c)`-determined) ⟹ a constraint on `(D_u(S'), c_lev,u(S'))_{S'}`.
3. **The finite injectivity** — joint over both-nondeg `S'` (`F` is NOT injective per-`S'`; spike: all-`S'` signature is
   81/81). **DO THE `decide`-FEASIBILITY SPIKE FIRST** (kernel `decide` over the ≤729 `(D,c)`-tuple space vs. a structured
   per-coordinate proof, §10.3(F)) — gates the endpoint.
4. **Recover `θ(u)` ⟹ `u = u'`** via a `coords_determine` generalization to the polar-row `θ`.
Landed B-side inputs ready for B-M3: `incidence_agree_V`, `cone_count_zero_split`, `fullcount_agree_modulo_corr`
(`ScratchLemmaB.lean`).

### 10.13 B-M3 HANDOFF — counts recover `u` (the last step to the `VO⁻₄(3)` instance seal). Spike-informed, 2026-06-21.
> **▶ FRESH READER START HERE for B-M3.** A-side (Lemma A / A-M4a) is COMPLETE and axiom-clean (`ScratchLemmaA.lean`,
> §10.11/§10.12). B-side B-M1 + B-M2-bridge landed (`ScratchLemmaB.lean`). B-M3 is the final piece: prove
> `IsotropySeparatesAtBase Q T₉`, which (via the Witt-free capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree`)
> seals `VO⁻₄(3)` mod `{G3}`.

**The logical chain (what's proved, what remains).**
- `IsotropySeparatesAtBase Q T₉` = `∀ u u', (fine isotropy-count antecedent) → u = u'`.
- **B-M1 (LANDED, `incidence_agree_V`):** the antecedent ⟹ the **restricted** counts agree for every `S' ⊆ T₉`:
  `restricted_u(S') = restricted_{u'}(S')`, where `restricted_w(S') = #{y ≠ 0 : Q y = 0 ∧ ∀ t∈S', Q(y − (t̄−w̄)) = 0}`.
- **B-M3 obligation:** `(restricted_u(S') = restricted_{u'}(S') ∀ S'⊆T₉) ⟹ u = u'` — i.e. **the restricted-count signature
  is injective over the 81 base points.** Everything below is about discharging this one finite implication.

**Spike (`/tmp/spike_bm3.py`, reproduction spec below) — the decisive facts:**
- **(A) `restricted_w(S')` is a function of `(m, detG, c_lev, corr)`** — 0 MULTI over all nondeg configs (18 classes);
  `corr = [∀t∈S', Q(t̄−w̄)=0]` is the `y=0` bit (`cone_count_zero_split`). So per-point counts reduce to cheap `F₃` data.
- **(B) ★ A minimal separating set is just 6 subsets, all of size 2.** The restricted-signature over **6 well-chosen
  `|S'|=2` subsets** is already injective over the 81 base points (full-`S'` signature is 81/81). This is the key
  enabler: the finite check is tiny (`81 × 6 ×` a `2×2` `F₃` count/determinant).
- **(C) ✗ Single-coordinate (structural) recovery is REFUTED.** The "through-`t₀`" counts (`|S'|≤3` containing a fixed base
  point) do NOT determine that coordinate `Q(ū−t̄₀)` — cross-coordinate collision = True. **Recovery is irreducibly joint**
  (consistent with §10.3(F)); the naive per-coordinate route is out. Only joint approaches survive.

**The exact remaining gaps.**
- **B-M3.G1 (THE CRUX) — the finite joint injectivity:** the restricted-signature (over a separating family of `S'`) is
  injective over `Fin 81`. Spike-validated; the question is the **proof method** (decide vs structured) given
  `native_decide` is BANNED — kernel `decide` only.
- **B-M3.G0 (count-assembly bridge, A-side leftover; needed for the reduced decide only):** `fullcount_w(S') = F(D_w(S'),
  c_lev,w(S'))` for nondeg config — the §10.12 substitution of `configGaussSum_eq_det` + global `χ(s)^d·W` into
  `levelset_count_eq`. Turns each 81-point count into cheap `(detG, c_lev)` data.
- **B-M3.G2 — reduce the antecedent + final glue:** B-M1 already collapses the `σ:Fin(p^d)→Fin 3` quantifier to the
  `S'⊆T₉` conditions; the residue is wiring (a `Finset S'→Fin m` reindex for the Lemma-A application, and—if a structured
  route is used—generalizing `coords_determine` (CascadeAffine:2640) to the polar-row `θ`). A pure `decide` over `u` needs
  no `coords_determine`.

**The three approaches (spike-ranked):**
1. **Direct `decide` (no Lemma A) — TRY FIRST.** Decide "restricted-signature over the 6 size-2 separating `S'` is
   injective over `Fin 81`" using the **direct** 81-point counts. Code is short; needs NO A-M4a. **Risk = kernel
   feasibility:** ~`81×6` signature builds × an 81-point `F₃` filter card each (~tens of thousands of kernel reductions;
   `native_decide` banned). **First action: a tiny kernel-`decide` feasibility spike** (e.g. decide one 81-point
   `restricted` count, time it) before committing.
2. **Lemma-A-reduced `decide` (robust fallback).** Prove B-M3.G0, replace each restricted count by `F(detG, c_lev, corr)`
   (a `2×2` `F₃` determinant + a `2×2` solve — ~10× cheaper than an 81-point count) and `decide` over those. Strictly
   smaller per-evaluation; this is where the A-M4a investment pays off if Approach 1's kernel cost is too high.
3. **Structural per-coordinate — REFUTED (spike C).** Do not pursue independent-coordinate recovery; recovery is joint.

**Recommendation.** Try **Approach 1** (direct `decide` over the 6-set) gated on a kernel-feasibility micro-spike; fall
back to **Approach 2** if the kernel chokes. Either way the 6-size-2 separating family (spike B) is the enabler. Caveat:
for Approach 2 the chosen `S'` must be both-nondeg for the compared `u` (Lemma A is nondeg-only); Approach 1 is
nondeg-agnostic (direct counts), so it sidesteps that.

**Reproduction spec (rebuild `/tmp/spike_bm3.py`):** `V=F₃⁴`, `Q=x₀x₁+x₂²+x₃²`, `polar(x,y)=Q(x+y)−Qx−Qy`;
`T₉ = {0,e₀,e₁,e₂,e₃,(0,0,0,2),(1,1,1,1),(1,2,1,2),(1,0,1,0)}`; `restricted_u(S') = #{y≠0 : Qy=0 ∧ ∀t∈S', Q(y−(t−u))=0}`;
config Gram `Gᵢⱼ=polar(tᵢ−u,tⱼ−u)`, `c_lev=−Q(w₀)` with `G·c=(Q(tⱼ−u))ⱼ`, `w₀=∑cⱼ(tⱼ−u)`, `corr=[∀t∈S',Q(t−u)=0]`.
Check (A) `restricted` single-valued per `(m,detG,c_lev,corr)`; (B) greedy-minimal separating set over all `S'⊆T₉`;
(C) through-`t₀` (`|S'|≤3`) signature vs `Q(u−t₀)` cross-coord collision.

**Landed inputs ready for B-M3** (`ScratchLemmaB.lean`, all axiom-clean): `coarse_incidence_agree`, `incidence_to_V`,
`incidence_agree_V`, `cone_count_zero_split`, `fullcount_agree_modulo_corr`. A-side: all of `ScratchLemmaA.lean`
(`configGaussSum_eq_det` is the A-M4a endpoint for Approach 2).

**★★★ B-M3 + WIRING + SEAL COMPLETE (2026-06-21, all axiom-clean `[propext, Classical.choice, Quot.sound]`).** Approach 1
executed end-to-end. The `VO⁻₄(3)` residue is SEALED modulo cited `{G3}`. Two new scratch modules (verified via
`lake env lean` + `lake build` oleans; NOT yet ported into `build.sh`/`lakefile` — that's the only remaining step):
- **`ChainDescent/ScratchBM3Bridge.lean`** (Mathlib-only) — the bridge + decided injectivity:
  - `co_encV` (digit decode = coord `val`, via `finFunctionFinEquiv_symm_apply_val`), `QvoVal`/`Qc_encV`/`Qsh_encV`
    (ZMod-3↔Nat arithmetic; leaf identities by `decide`, `%3` nesting by `omega`), `encV_val_zero`.
  - **`restricted_bridge`** — the abstract `VO⁻₄(3)` restricted count over `Fin 4→ZMod 3` (the Lemma-B object) = the
    pure-`Nat`-predicate count `restrictedF` over `Finset (Fin 81)` at the digit-codes (transport along the *computable*
    `encV = finFunctionFinEquiv`, NOT the opaque `affineE`; `Finset.card_nbij'`).
  - **`sigF_injective`** — `Function.Injective sigF` by kernel `decide` (~20s, no `native_decide`), the 6-size-2 family.
- **`ChainDescent/ScratchBM3Glue.lean`** (imports CascadeAffine + ScratchLemmaB + ScratchBM3Bridge):
  - `Bil`/`Qbun` (the bundled minus-form `x₀x₁+x₂²+x₃²` via `LinearMap.mk₂` → `toQuadraticMap`), `Qbun_apply`.
  - `Bv` (9 base vectors), `T₉ := univ.image (affineE ∘ Bv)`, `hcard9` (`|T₉|≤9`), `Sij_subset`.
  - `vcount_eq` (B-M1's incidence count = `restrictedF` at codes: `∀t∈{·,·}` unfolded, `Qbun→Qvo`,
    `affineE.symm∘affineE=id`), `comp_eq` (per-pair agreement via `incidence_agree_V`).
  - **`isoSep : IsotropySeparatesAtBase Qbun T₉`** — the B-M3 target: antecedent ⟹ (via B-M1) restricted counts agree
    ⟹ `sigF (encV (affineE.symm u)) = sigF (encV (affineE.symm u'))` ⟹ (`sigF_injective`) `encV∘affineE.symm` equal
    ⟹ `u = u'`. NO `coords_determine`, NO A-side, NO `corr`.
  - **`vo4minus_seal`** — `reachesRigidOrCameron_viaIsotropySeparates_wittFree Qbun T₉ hcard9 isoSep`: THE SEAL.
- **Decisions banked:** kernel `decide` over `Finset (Fin 81)` with a `Nat` predicate (~20s) vs the `Pi.fintype` path
  (~321 ms/count → ~5 min, rejected). The bridge adds NO decide cost (elaboration-only); `affineE` opacity dodged by
  *choosing* `T₉ = image affineE` of a concrete vector base.
- **Remaining = PORT only:** move the 4 scratch modules into `build.sh` + `lakefile.toml`, regen `PublicTheoremIndex.md`,
  full green build. (Tier-2 generalization M5 / Skresanov / char-2 unchanged.)

**★ MICRO-SPIKE RESULT (2026-06-21) — APPROACH 1 IS FEASIBLE; commit to it.** (Spike file `ScratchBM3Spike.lean` deleted —
superseded by `ScratchBM3Bridge.sigF_injective`, the real decided injectivity.)
Kernel `decide` of the full restricted-signature injectivity over all 81 base points, using a **kernel-friendly
`Nat`/`List` encoding** (point `n∈0..80` ↔ coords `co n i=(n/3^i)%3`; counts via `List.range 81` + Bool filter; pure
accelerated `Nat.beq`/`Nat.mod` — deliberately NO `Finset`/`Pi.fintype` Quot), phrased as an image-card Bool
`injOver81 := allDistinct ((List.range 81).map sig)` over the **6 size-2 pairs** (T₉ codes
`[(0,9),(27,10),(1,3),(27,70),(9,54),(1,40)]`, from `/tmp/bm3_lean_targets.py`): **succeeds in ~17s** (~8.2s
elaboration + ~8.6s kernel; single counts ~120ms). `native_decide` NOT used. `#eval injOver81 = true` agrees. So the
combinatorial core is kernel-decidable at acceptable cost.
- **What it does/doesn't establish.** It proves the *Nat-encoded proxy* is kernel-feasible. The remaining work for the
  REAL proof is the **bridge** from the abstract restricted count `#{y:Fin d→ZMod p | y≠0 ∧ Qy=0 ∧ ∀t∈S', Q(y−(t̄−ū))=0}`
  (`incidence_agree_V`'s object) to the Nat `restricted` — i.e. transport along the digit equiv
  **`finFunctionFinEquiv : (Fin d→Fin p)≃Fin (p^d)`** (our `co` is exactly its inverse, with `ZMod p = Fin p`) via one
  `Finset.card_bij`/`card_nbij`, matching `Qc`/`Qsh` to `Q`. The bridge adds NO kernel-decide cost (the decide still runs
  on the Nat proxy); it is elaboration-only, mechanical. Deciding the abstract `Finset (Fin d→ZMod p)` counts *directly*
  (the `Pi.fintype` path) was deliberately NOT tested and is expected far slower — **do not** go that way; bridge to Nat.
- **B-M3 plan (committed, Approach 1):**
  1. **Bridge lemma** `restricted_eq_nat`: each abstract restricted count = the Nat `restricted u t1 t2` (via
     `finFunctionFinEquiv`/`co`, `Finset.card_nbij`, `ZMod.natCast`/`Fin` coords). Reusable; one lemma per the count shape.
  2. **The decide** `injOver81 = true` (landed in the spike) ⟹ `∀ u u' : Fin 81, sig u = sig u' → u = u'` (pure Nat/List,
     kernel `decide`, ~17s).
  3. **Glue:** `IsotropySeparatesAtBase Q T₉` ← `incidence_agree_V` (antecedent ⟹ restricted counts agree ∀S'⊆T₉) ⟹ (the
     6 chosen S' ⊆ T₉ agree) ⟹ (via bridge) `sig u = sig u'` ⟹ (decide) `u = u'`. The "agree on all S' ⟹ agree on the 6"
     step is trivial Finset wiring. **No `coords_determine` / no A-side / no `corr` needed** (restricted, not full count).
  4. **ASM:** instantiate `VO⁻₄(3)` (Q = x₀x₁+x₂²+x₃² on `Fin 4→ZMod 3`) + `T₉`, feed
     `reachesRigidOrCameron_viaIsotropySeparates_wittFree`, port `ScratchLemmaB` + the spike's decide into a real module.
  Approach 2 (Lemma-A-reduced decide via `configGaussSum_eq_det`) and the A-side stay as the **generalization (M5) /
  fallback** asset — not on the instance-seal critical path.

### 10.4 Route 3 (= §3 Route B) — perp-graph + Witt frame-rigidity. Cleaner, but blocks on building Witt.
Mental model: individualizing `0`, the induced subgraph on the isotropic cone `N(0)` IS the polar space's collinearity
(perp) graph (`x~y ⟺ B(x,y)=0` for isotropic `x,y`); a hyperbolic frame (apartment) then discretizes the isotropic
skeleton *directly* via the perp-pattern, and the anisotropic shell is pinned by adjacency to it. Steps:
1. **Witt's transitivity/extension theorem for finite-field quadratic forms** — **ABSENT from Mathlib** (the hyperbolic
   decomposition + extension-of-isometries; ~Mathlib-contribution size). **This is the SAME build as the B.1c-i Witt
   track (`OrbitIsIsotropyClass`)** — so Route 3 couples the Gauss work to the Witt track (do them together).
2. The perp-graph identity `x~y ⟺ B(x,y)=0` on the cone (easy: polarization).
3. Frame-rigidity: a hyperbolic frame determines each isotropic point by its perp-pattern (uses Witt, step 1).
4. The non-isotropic shell: pin each anisotropic `w` by its relation to the discrete isotropic skeleton — binary
   adjacency gives `B(w,xᵢ)` only modulo the unknown `Q(w)`; needs 1–2 extra base points or one round of Route-1 counts.

**Verdict / recommendation.** Both routes converge on the **non-isotropic shell** (the located residual). **Route 1 is
recommended for the kernel** because it is Witt-free (the isotropic-incidence counts need no Witt) and every toolkit
lemma is present — the only open piece is the inversion 1.4, which is concrete and probe-de-riskable. **Route 3** is the
better *mental model* and is the natural choice *only if* the Witt track is being built in parallel anyway (then steps
3–4 ride on it). Witt is needed regardless for the capstone's `OrbitIsIsotropyClass`, but Route 1 discharges the kernel
*without* waiting on it.

### 10.5 Module / decl map for a fresh reader
**In the build (registered in `build.sh` + `lakefile.toml`, all axiom-clean, full build green ~33s cached / ~140s cold):**
- **`ChainDescent/GaussCount.lean`** (Mathlib-only leaf) — the Gauss toolkit: `count_eq_charsum`/`count2`/`countk_*`/
  `count_pi_setValued` (counts), `sum_addChar_*` (1-D/multivariable Gauss), **`card_quadForm_eq`** (THE affine-quadric
  level-set count A-M3 consumes), `sum_addChar_multiQuad`/`_zero`/`sum_addChar_linearMap`, `multiCharSum_eq_sum_count`.
- **`ChainDescent/CascadeAffine.lean §OrthogonalForm`** — the capstone chain.
  - **★ THE LIVE CAPSTONE: `reachesRigidOrCameron_viaIsotropySeparates_wittFree`** (`PublicTheoremIndex.md:1248`) —
    seals the `VO^ε` residue from a bounded base + `IsotropySeparatesAtBase Q T`, **NO Witt, NO `hSmallAutThin`**. Its
    Witt-free chain: `RelationRefinesIsotropy` (easy half) ← `relationRefinesIsotropy_similitude` (discharged outright
    via `isoClass_similitude_invariant`); `separatesAtBase_of_isotropySeparates_weak` (the Witt-free bridge).
  - The TARGET predicate **`IsotropySeparatesAtBase Q T`** (`:3102`) = what Lemma A+B must prove (`∀ u u'`,
    fine-isotropy-count agreement ⟹ `u=u'`). `coords_determine` (`:2640`, the Gram→vector back-half),
    `affineScheme_relOfPair_eq_iff`/`orbMk_affine_eq_iff` (orbit ⟺ G₀-orbit of difference), `polar_eq_of_sub`,
    `similitudeGroup`/`neg_mem_similitudeGroup`. ⚠ SUPERSEDED (kept, axiom-clean): the Witt-carrying
    `separatesAtBase_of_isotropySeparates` / `reachesRigidOrCameron_viaIsotropySeparates` + the frame-locked predicates.
- **`ChainDescent/FormsGraphConcrete.lean`** (imports both) — `count_transport`, `isotropy_count_transport`,
  `isoSetOf`/`qSetOf`/`mem_isoSetOf_iff`, `coarse_eq_sum_iso` (M1); `QProfileSeparatesAtBase` +
  `isotropySeparates_of_qProfileSeparates` (the M3 *reduction* — note: this is the OLD `Q`-profile route; the live
  step-4 attack is the Lemma A/B route below, which proves `IsotropySeparatesAtBase` directly).

**WIP scratch (NOT in the build; verify each with `lake env lean ChainDescent/ScratchLemmaX.lean`; PORT at ASM):**
- **`ChainDescent/ScratchLemmaA.lean`** — Lemma A (count = explicit Gram-function on nondeg configs). **A-M1+A-M2 done:**
  `isoIncidence_eq_linearConds` (A1), `map_add_of_polar_zero` (A4-core), `count_coset` (A3), `polar_w0_perp` (A4-link),
  `reduction_to_levelset` (A1∘A3∘A4: count = homogeneous level-set `#{x : (∀j, polar Q x (a j)=0) ∧ Q x = −Q w₀}`
  given a spanning `w₀=∑ cₖaₖ`), `spanning_w0_exists` (A-M2: `IsUnit (Gram).det ⟹ ∃ such w₀`),
  `reduction_to_levelset_nondeg` (the two combined, unconditional on nondeg Gram). **Open: A-M3, A-M4 (see §10.8).**
- **`ChainDescent/ScratchLemmaB.lean`** — Lemma B (counts recover `u`). **B-M1 + B-M2 bridge done:**
  `coarse_incidence_agree` (B-M1 core: fine antecedent ⟹ incidence-count agreement, fiberwise),
  `incidence_to_V` (transport+translate `Fin(p^d)`→`V`), `incidence_agree_V` (B-M1 capstone),
  `cone_count_zero_split` (the `y=0` correction), `fullcount_agree_modulo_corr` (B-M2 bridge capstone: full
  Lemma-A-shaped counts agree modulo the Gram-determined correction). **Open: B-M2 proper (needs A-M4), B-M3, ASM.**

---

## 11. FULL ROADMAP to the schurian-residue seal (modulo `{G3}`) — revised 2026-06-24

> **What this is.** The total remaining work to prove, **unconditionally modulo the `{G3}` citation stack**, that after
> deferred-decisions stage 1 (every decision real, IR-solver not yet run) the graph residue is **rigid or Cameron** —
> i.e. to discharge `hSmallAutThin` for the small-Aut non-geometric **schurian** rank-3 residue. The single `VO⁻₄(3)`
> instance is sealed (§10.13); this section is the generalization program. **Scope:** the schurian residue only — the
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
- **Route 3 — Witt + perp-graph frame-rigidity (§10.4).** Extraction needs the **one-time Witt build** (AUDIT-W, large).
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

1. **Count-assembly bridge (A-side, mostly built — §10.12).** Substitute `levelset_count_eq` + `configGaussSum_eq_det` +
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
  vs. the older §9 framing.)
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

*Maintenance: update §10.8 milestone ticks + §10.5 as stages land; §11 is the forward roadmap (revised 2026-06-24) —
update its audit/spike outcomes and the §11.1 route decision as they resolve. Keep route-doc §9.9.18b/c the empirical
anchor and this doc the proof target. Live capstone `reachesRigidOrCameron_viaIsotropySeparates_wittFree`
(`PublicTheoremIndex.md:1248`); `VO⁻₄(3)` sealed (§10.13, `ScratchBM3Glue.vo4minus_seal`); the Lemma A/B + bridge/glue
build lives in the four scratch modules (port at ASM).*
