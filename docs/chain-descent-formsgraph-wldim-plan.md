# Proof plan — bounded WL-dimension for the affine forms-graph families (the seal's node-4 content)

> **What this is.** A concrete proof plan for the sharpened open frontier (route-doc §9.9.18b/c): prove **bounded
> Weisfeiler–Leman dimension** (= bounded individualization base ⟹ `hSmallAutThin`) for the affine forms-graph rank-3
> SRG families that constitute node-4-for-the-seal — affine polar `VO^ε_{2m}(q)`, alternating forms, half-spin, and
> Suzuki–Tits. By the Skresanov reduction (§9.9.18) these (plus the cited 1-dim cyclotomic slice) are the *entire*
> small-Aut non-geometric schurian rank-3 residue; the probe (`Probe_FormsGraphs`, §9.9.18c) shows they shatter at a
> bounded base. This plan turns that empirical shatter into a proof target with a landed engine and one crux lemma.

---

## STATUS (read first)

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
> recover Q-profile → `coords_determine`".** See §9 (milestone roadmap) for the full M0–M5 plan. NEXT = **M1** (the
> conversion: fine→coarse reduction + `qvalue_count_transport`, no origin correction), batched as one milestone.
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

**Pipeline still to build:**
`isoClass counts —[M1 dictionary+origin]→ Q-value-set counts —[qvalue_count_transport ✓]→ pointwise Q-counts
—[M2 Gauss closed form]→ explicit f(Gram of T∪{u}) —[M3 injectivity]→ u=u'  ⟹  IsotropySeparatesAtBase  —[M4]→ sealed VO^-_4(3).`

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

### Milestone 1 — the conversion (isotropy counts → pointwise Q-counts), in `FormsGraphConcrete`
**Simplified by M0 (coarse suffices — no origin correction).** Steps: (a) the **fine→coarse reduction** — fine-count
agreement (the `IsotropySeparatesAtBase` hypothesis) ⟹ coarse-count agreement, since each coarse value-set count is a
sum of fine counts over the refining `σ`-profiles (`isoClass_ne_two_iff`: `Q=0 ⟺ isoClass∈{0,1}`); (b) the coarse
count is a pure `Q`-value-set count `#{z : ∀t, Q(z̄−t̄) ∈ A_t}` with `A_t ∈ {{0}, {x|x≠0}}`, fed to the landed
`qvalue_count_transport` → pointwise `Q`-counts. Result: coarse-count agreement ⟺ agreement of pointwise `Q`-counts.
*Risk: low.*

### Milestone 2 — the Gauss closed form (pointwise Q-count → explicit Gram-function), in `GaussCount` + `FormsGraphConcrete`
Prereq bridge `(Q.polarBilin).Nondegenerate ⟹ (associated Q).SeparatingLeft` (`two_nsmul_associated` + `Invertible 2`);
the combined inner sum `S(r)` for all `r` (`multiQuad` for `R≠0`, `multiQuad_zero`+`linearMap` for `R=0`); the global
Gauss value `∑_z ψ(R·Qz) = χ(R)^d·(∏χ wᵢ)·Gᵈ`; Brick C-even numeric check; substitute into `countk_eq_sum_charsum`
⟹ pointwise Q-count as an explicit character sum in the Gram entries `B(u,t_j), Q(u)`. *Risk: med (heaviest assembly).*

### Milestone 3 — the injectivity (THE CRUX), in `FormsGraphConcrete`
**Refined by M0 (size-6 base, recover-then-`coords_determine`).** Using the M2 closed form: show coarse-count
agreement ⟹ the `Q`-profile `(Q(u−t))_{t∈T}` agrees (the extra point `2e₃` makes the joint count recover the profile —
this is where the symmetry-broken base is essential), then the **landed `coords_determine`** (Q-profile over the basis
frame + nondegeneracy ⟹ `u`) closes `u = u'`. Conclude `IsotropySeparatesAtBase Q T`. The injective-Q-profile blueprint
(M0.4, 81/81 at size-6) guarantees this route exists. *Risk: HIGH — the recover-the-profile step is the genuine
uncited content (a joint character-sum inversion); de-risked by M0 + reuse of `coords_determine`.*

### Milestone 4 — the concrete `VO^-_4(3)` instance + capstone, in `FormsGraphConcrete`
`Q = x₀x₁+x₂²+x₃²` over `ZMod 3` + polar-nondegeneracy; the concrete base `T = frameBase ∪ {2e₃}` (size 6, M0.3) +
`IsBase` (or `exists_greedy_base_le_log`); instantiate M3; feed `reachesRigidOrCameron_viaIsotropySeparates` ⟹ a concrete sealed
`VO^-_4(3)` *modulo {Witt `OrbitIsIsotropyClass`, G3}*. **This is the headline Gauss-work result.** *Risk: low (wiring).*

### Milestone 5 — generalization (follow-on, post-Gauss-work)
General `q` (char ≠ 2) then general `d`; then classes (d) alternating / (e) half-spin (reuse skeleton, symplectic/spinor
`B`); char-2 (`q=2,4`) and Suzuki (f) are separate arguments. The Witt track (`OrbitIsIsotropyClass`, B.1c-i) runs in
parallel and is required for a fully-sealed-modulo-citations instance.

---

*Maintenance: update STATUS as stages land; keep route-doc §9.9.18b/c the empirical anchor and this doc the proof
target. Capstones recorded in `PublicTheoremIndex.md:1207, 1210-1226` + the remaining-work tracker §3a.*
