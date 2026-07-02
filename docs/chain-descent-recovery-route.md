# The recovery route — proving the forms-graph poly bound the way the canonizer actually works

> **What this is.** The working doc for the **recovery route**: proving the affine-polar forms-graph residue is canonized
> in **polynomial** time by the *existing* chain-descent canonizer, the way it actually stays poly — a **small
> branch-but-resolve tree** (cross-branch automorphism harvest prunes within-orbit siblings), **not** refinement reaching
> orbits and **not** a single path. This is the **recommended** polynomial target (2026-06-30), **retargeted (v2) to the
> mathematically weakest sufficient condition — `T0`: bounded branching ⟹ poly leaf count** (the open content is
> `bᵢ ≤ poly(q)`, far weaker than `CellsAreOrbits`). The C# default mode satisfies exactly this (it branches and resolves).
>
> **Relation to the other route doc.** [`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md)
> pursues poly *through* bounded WL-dimension (`CellsAreOrbits` = refinement reaches orbits). That was found to be the
> **wrong model of the C#** (the canonizer does not rely on refinement reaching orbits) and is now demoted to
> independent-math value. **This doc is the live route.** Where the two overlap, this doc wins for "what the canonizer does."
>
> **Provenance.** The forms-graph plan ([`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md))
> §1 item 1 (the PROVABLE-BOUND INVESTIGATION, Routes A/B/C); the Stage A/B landings (`remaining-work.md` §3a);
> the C# model comparison + the residual-reconciliation probe (this session, 2026-06-30).

---

## STATUS (read first)

> **════════ PICK-UP (2026-06-30, v2 — RETARGETED to the weakest predicate) — READ THIS FIRST ════════**
>
> **What this route is, in one line.** Prove the *existing* canonizer runs in poly time on the forms-graph residue by
> bounding its **leaf count** — NOT by proving cells = orbits. This targets the **mathematically weakest** sufficient
> condition, which is exactly what the C# default mode satisfies. (An earlier version of this doc drifted onto
> `CellsAreOrbits` / cross-branch-harvest predicates that secretly require cells = orbits — a *stronger*, harder,
> likely-only-quasipoly target. Those are now relocated; see "Relocated" below and §2c.)
>
> **Empirical anchor — Phase 0 sweep RUN (2026-06-30, `Phase0_BranchProfile`).** Across `VO^ε_{2m}(q)` (q=2,3,5; d=4,6,8):
> **no flag, full `|Aut|`, `STARVED = 0` everywhere** (D4 holds). **No `d`-driven explosion** — the q=2 d-sweep is single-path
> (`B=1, L=0, leaves=1`) **through d=8**. The **only** branching cell is `VO⁻₄(5)` (`B=3, L=2, leaves=6`, `bᵢ ∈ {2,3} < q=5`);
> plus-type and q≤3 single-path. So in **default (canonical-form-preserving) mode it branches and resolves** where it branches
> at all, and the cost stays poly because `leaves` is small (`≤6`), **not** because the descent is always a single path.
> **GATE verdict: T0 not falsified, positively supported** (small `B,L,leaves`; `bᵢ < q`), but the scaling rests on **one**
> branching datapoint — q≥7 / branching-regime d≥6 are blocked by the **per-node-cost wall** (`VO⁻₈(2)` = ~29 min for a 9-node
> single path), not by any blow-up. Full table + reading: §4 "Empirical anchor". That is the target to formalize.
>
> **Two deliverables — keep separate.**
> - **SEAL** (`reachesRigidOrCameron` modulo `{G3}` — *correctness*): **already BANKED at quasipoly**
>   (`AffinePolarSeal.reachesRigidOrCameron_affinePolar`). Not this route's job.
> - **POLY** (the *cost* claim — this route): cost ≈ `#leaves × depth × per-node`. Depth `= O(d)` and per-node hard-poly are
>   ~landed; the open content is **poly leaf count**.
>
> **THE OPEN TARGET — poly leaf count (the weakest sufficient condition).**
> `leaves = ∏ᵢ bᵢ`, where `bᵢ = #{Stab(Sᵢ)-orbits in the selected cell at level i}`. **`CellsAreOrbits` is the special
> case `bᵢ = 1 ∀i` (single path) — strictly STRONGER and not needed.** The weak target only needs the *product* bounded.
> The arithmetic: `∏bᵢ ≤ Bᴸ` with `B = maxᵢ bᵢ` and `L =` #branching-levels, and since `n = q^d`, **`B ≤ poly(q)` AND
> `L = O(d)` ⟹ `Bᴸ = q^{O(d)} = poly(n)`**. **BOTH factors are open obligations (neither is landed):** `bᵢ ≤ poly(q)` is the
> in-cell orbit-count bound (the `bᵢ ≤ q` "one new Gram coordinate" story is a *heuristic* — it bounds cell-refinement, not
> orbit count, which is a-priori `≤ q^{|Sᵢ|}`, and `model_gap.py` shows the gap grows with `q`); `L = O(d)` is the
> branching-depth bound (NOT given by `defaultSpineChain_reaches_leaf ≤ n`, which bounds single-chain length only). Both are
> *far* weaker than `CellsAreOrbits` and both must be measured (§4, §6 Phase 0) before being assumed.
>
> **════════ FRESH-READER HANDOFF (2026-07-02, current) — read this paragraph first ════════**
> **Where the poly crux stands, in one breath (updated 2026-07-02).** The crux `bᵢ ≤ poly(q)` (per-cell orbit count) is
> a **two-piece** target: **(i) span-dim-1** — `bᵢ ≤ q²`, **PROVEN** (`ScratchSpanDimBound.stabOrbit_cover_card_le_line`);
> **(ii) span-dim ≥ 2** (route A) — `bᵢ = 1`, which (over-narrowing-checked §9.7) *concentrates* branching at
> span-dim≤1 so it also yields `L=O(1)`, `leaves ≤ q²`. Route A = `WallKernelFor(obs)` factoring through `hprof`
> (isotropy over the plane `W`), split into geometric **CORE (I)** + counting **SEAM (II)** — and the CORE + the whole
> reduction are now **LANDED**:
> - **(I) CORE — LANDED, BOTH branches** (`ScratchSpanDim2Geom`/`ScratchConicSpan`, axiom-clean): `hprof ⟹ SameExactGram`
>   generically (`exactGram_of_sameWProfile` + the `hspan` discharge: `hspan_of_two_indep` + the elementary conic count
>   `ScratchConicCount` + the transport `hspan_of_conic`) and on the singleton locus (`exactGram_of_isotropic_complement`),
>   unified by the bare-vertex dichotomy `hspan_or_singleton`.
> - **STEP B — LANDED** (`ScratchBaseAug`): the observable `IsoSetEq` ⟹ `SameExactGram`, both branches, with the (ii)-glue
>   `u_W=u'_W` *derived* (`eq_wComp_of_isotropic_of_anisotropic`).
> - **STEP C reduction — LANDED** (`ScratchPlanePin`): the `zSet` observable resolves cells to orbits
>   (`zSetEq_iff_stabOrbit_anisotropic`, `bᵢ=1`), reducing everything to "1-WL refines `zSet`" (= C^∞ pins `W`).
> - **(II) SEAM — the observable is now settled by probe (§9.7 "PROBE-DRIVEN CORRECTION", 2026-07-02).** The
>   plane-point-pinning line (`ChiProfileSeparatesPlane` → `PlanePinnable`, singleton-anchor χ-profiles) is **REFUTED**
>   (`pin_probe.py`: stalls at the 3-point base for `q≥5`). The correct observable is **ambient colour-CLASS counts**
>   (`recovery_depth_probe.py`: cells = orbits in `r*∈{3,4}`, flat in `d`). **Route A reduces to the single open predicate
>   `ClassCountsSeparateGram`** (`ScratchWLClassCounts`, axiom-clean) = `WallKernelFor (SameClassCounts C Q) Q ↑{a,b}` —
>   the class-count profile separates the exact Gram (the *iterated* observable `ScratchWallKernel` asked for). TRUE per
>   probe. `colorEq_iff_stabOrbit` gives `bᵢ=1` from it. The plane-pinning modules (`ScratchPlanePinInduction`, the
>   `ScratchWLWiring` singleton bridge) are superseded-but-subsumed (their `PinsPlane` is a *consequence* of the correct
>   recovery). NB — this is the **general SRG WL-dim content** for `VO^ε_2(q)`, not a purely elementary 2-dim count.
>
> **▶ READ §9 FIRST for the logical plan + the reasoning (self-contained).** §9 records the (I)/(II) architecture, the
> five insights **with their derivations** (chiefly Insight 1 — *why there is no single-round bypass*, so the WL iteration
> is mandatory and (I) is on the critical path), the landed substrate, and the ordered plan + dead ends. The dated bullets
> in this STATUS are the chronology; §9 is the map.
>
> **▶ CURRENT FRONTIER (2026-07-02) — route A's round-3 crux (Piece 1) is BUILT END-TO-END and reduces to TWO named
> predicates; here is the whole picture.** The **counting mechanism is settled by probe** (round structure
> **r1=3iso → r2=seal `jointIsoCountK`-profile → r3 = the count `T(u;g)=#{z:gram(z)=g,Q(u−z)=0}` reaching ORBITS exactly,
> form-independently**, §9.7 findings 1–5), and the **round-3 observable is now built in Lean, orbit-direct** (five
> `ScratchGramStrat*` modules, all axiom-clean, NOT in build.sh — see the section plan below and the verify-list):
> `bᵢ=1` at the span-dim-2 base = the crux `GramCountsRecoverOrbit` (`SameGramStratCounts ⟹ StabOrbit`), which
> `ScratchGramStratOrbit` **reduces to exactly two named predicates** (`gramCountsEq_iff_stabOrbit_refined`), **both carrying
> a `GoodBase Q a b` antecedent** (`a,b` orth aniso + `(2:K)≠0` + `Q.polarBilin.Nondegenerate`) so they are TRUE and
> dischargeable — NOT the FALSE bare `∀ Q a b` forms (a false predicate can never be discharged toward the unconditional
> seal): **`GramCountsRecoverGram`** (the ONE GENUINELY-OPEN Gauss lemma = "`K` non-degenerate", must be PROVED, probe-true)
> + **`RefinedWittExtends`** (a CITATION of Witt's theorem — acceptable to carry, like the seal cites G3/Babai).
> **★★ UPDATE (2026-07-02, cont.): `GramCountsRecoverGram` is now DISCHARGED to a *classical* cone non-degeneracy, and `hψ`
> is DISCHARGED** (`ScratchGramStratGauss`/`GaussReduce`, axiom-clean). Core = the factorization `countHat_factor`:
> `countHat u t = ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)` (`u`'s Gram in the phase); the reduction constructs a primitive
> char (Mathlib `AddChar.FiniteField.primitiveChar K ℚ`) so `gramCountsRecoverGram_of_isoConeSep` carries no `hψ`.
> **★★★ UPDATE (2026-07-02, cont.): `IsoConeSumSeparatesGram` is now DISCHARGED — PROVED axiom-clean**
> (`isoConeSumSeparatesGram`, `ScratchGramStratConeSep`). The entire Gauss/analytic content of Route A's Piece 1 is done.
> Key lemma = **`isoConeSum_eval_even`** (`ScratchGramStratConeEval`): for **even** ambient dim (the `VO_{2m}` case) the
> quadratic Gauss sum is scale-invariant (`G(s)=χ(s)^n G₁=G₁`), so `|K|·isoConeSum(y)=|V|𝟙[y=0]+G₁(|K|𝟙[Qy=0]−1)`; hence
> `isoConeSum_ne_zero` (nowhere-zero at even dim). Separation then: off-diagonal + diagonal both from *non-vanishing* +
> primitivity (no value needed); flag from the closed form once phases match. **⟹ Route A Piece 1 = `bᵢ=1` modulo ONLY
> the Witt citation `RefinedWittExtends`** (capstone `gramCountsEq_iff_stabOrbit_wittOnly`, axiom-clean, `hψ` constructed).
> **★★★ UPDATE (2026-07-02, cont.): Piece 2 (the WL bridge) LANDED — `ScratchGramStratWLBridge`, axiom-clean.**
> `sameGramStratCounts_of_sameClassCounts`: if the colouring **refines `gramK`** (`ColorRefinesGramK`, the necessary
> fineness residual — `{z:gramK z=g}` = union of colour classes ⟹ `gramStratCount u g = ∑_{g-colours c}(classCount u c 0 +
> classCount u c 1)`, a `u`-indep sum equal under `SameClassCounts`), then `SameClassCounts → SameGramStratCounts`.
> **Assembly capstone `colorEq_iff_stabOrbit_wittOnly`** (`ScratchGramStratWLBridge`, axiom-clean): **`C u = C u' ↔
> StabOrbit` (`bᵢ=1` for the WL colouring)** modulo `{ColorRefinesGramK, IsWLStable, ObsInvariant}` (colouring properties;
> `ColorRefinesGramK` = the clean WL-dim residual, weaker than `C∞=orbits`) + `RefinedWittExtends` (Witt citation). **The
> ENTIRE Gauss/analytic content is proved axiom-clean, `hψ` constructed.**
> **▶ NEW NEXT = Piece 3 assembly** (`leaves_le_prod_concentrated`) + discharge the residuals: `ColorRefinesGramK` (WL
> separates exact Gram to the individualized base — a WL-dim fact, or the doc's deeper round-3-equitability route), the
> standard colouring properties (`IsWLStable`/`ObsInvariant`), and the Witt citation. Odd dim awaits an extension of
> `isoConeSum_eval_even` (even-dim scale-invariance is what makes the cone sum nowhere-zero).
> **[NB — dead ends recorded (do not re-walk): the "Fourier-invert the fibre sums; bulk recovers Gram" attack is EMPTY (the
> marginal is trivially `|K|`·count-transform); the elementary first-moment fails in char `p` (`q|#{Qw=0}`). Gram lives in
> the phase ⟹ ℂ/char route necessary. §9.7.]**
> `RefinedWittExtends` = the Witt citation.
> **[NB — the earlier "frontier = `ClassCountsSeparateGram`" framing (in the paragraphs just above + §9.7 mid-section) is
> SUPERSEDED: that predicate routes through `SameExactGram`+Witt, which is Witt-DEAD at `{a,b}` (orbits 36 ⊋ 27 gram-classes);
> the live spine is the ORBIT-DIRECT `GramCountsRecoverOrbit` chain. Read the section plan below, not the ClassCounts framing.]**
>
> **THE SECTION PLAN (recovery to `bᵢ=1`), 3 pieces — see §9.7 "LEAN BUILD STARTED":**
> - **Piece 1 — the K-non-degeneracy crux.** **1a ✅ LANDED (`ScratchGramStratCount`, axiom-clean):** the round-3 observable
>   (`gramK`/`gramStratCount`/`SameGramStratCounts`), **soundness** (`sameGramStratCounts_of_stabOrbit`), the open crux
>   **`GramCountsRecoverOrbit : SameGramStratCounts ⟹ StabOrbit`**, and the capstone `gramCountsEq_iff_stabOrbit` (⟹ `bᵢ=1`
>   modulo the crux). **★ Targets the orbit DIRECTLY, not `SameExactGram Q {a,b}`+Witt** — because `{a,b}` spans only the
>   2-plane, orbits are *finer* than `SameExactGram` (`36>27`) and `WittExtendsToOrbit Q {a,b}` is FALSE (plane-vertex vs
>   nonzero-isotropic-complement). **1b ✅ LANDED (`ScratchGramStratCharSum`, axiom-clean):** the character-sum identity —
>   `gramStratCount_charsum` (the raw four-constraint Fourier expansion via `countk_eq_sum_charsum`) +
>   `gramStrat_inner_normalize` (inner z-sum in the `(r₀+r₃)Qz + polar z (r₁•a+r₂•b−r₃•u) + r₃Qu` D1-normal form) +
>   `gramStratCount_charsum_normalized` (combined). Pure assembly of the `GaussCount` toolkit (`countk_eq_sum_charsum`,
>   `quad_sub`, polar bilinearity); no new Gauss theory. *(NB — Piece 1a's `gramStratCount` def was switched off
>   `open scoped Classical` to a genuine `DecidableEq K`-based `DecidablePred`, so its filter shares the toolkit's
>   decidability instance; the instance still needs `convert`+`ext` to bridge into `countk`'s.)* **1c(i) ✅ LANDED**
>   (`ScratchGramStratEval`, axiom-clean): the inner z-sum evaluated — `gramStrat_inner_eval_ne` (bulk `ρ:=r₀+r₃≠0`, D1
>   complete-the-square: `= ψ(r₃Qu)·ψ(−ρ⁻¹·Q(r₁•a+r₂•b−r₃•u))·∑_z ψ(ρ·Qz)`; `u` enters via `ψ(r₃Qu)` **and** `Q(r₁a+r₂b−r₃u)`)
>   + `gramStrat_inner_eval_zero` (boundary `ρ=0`, `sum_addChar_linearMap`: `= ψ(r₃Qu)·(|V| if `polarBilin.flip wᵣ=0` else 0)`).
>   **1c(ii) ✅ COMPLETE (`ScratchGramStratInvert`, axiom-clean):** the `g`-profile inversion. `gsum_orthogonality`
>   (`∑_{g:K×K×K} ψ(⟨t,g⟩) = |K|³·𝟙[t=0]`, coordinatewise `AddChar.sum_mulShift`) + `innerZ` (opaque def of the surviving
>   inner z-sum) + `gramStrat_transform_eval` (`(∑_g ψ(⟨s,g⟩)·gramStratCount u g)·|K|⁴ = ∑_r 𝟙[r₀₁₂=s]·|K|³·innerZ_u(r)`,
>   via `charsum_normalized` + orthogonality + `Finset.sum_comm`) + **`sameGramStratCounts_transform`** (payoff:
>   `SameGramStratCounts u u'` ⟹ equal `innerZ` fibre sums ∀`s` — trivial once the transform is evaluated). Clean input to
>   1c(iii). **1c(iii) ✅ REDUCTION LANDED (`ScratchGramStratOrbit`, axiom-clean):** the crux `GramCountsRecoverOrbit` is
>   reduced to **exactly two named predicates**, composition proved (`gramCountsRecoverOrbit_of`), plus the `bᵢ=1` capstone
>   `gramCountsEq_iff_stabOrbit_refined` and the flag-soundness `stabOrbit_imp_span_iff`. **★ Both predicates carry a
>   `GoodBase Q a b` antecedent** (`a,b` orthogonal anisotropic + `(2:K)≠0` + `Q.polarBilin.Nondegenerate`) — ESSENTIAL, not
>   cosmetic: the bare `∀ Q a b` forms are literally FALSE (`b` isotropic ⟹ `W` degenerate ⟹ Witt fails; Gauss probe-truth is
>   only at nondeg orthogonal-anisotropic bases), and a false statement can never be *discharged* — which would permanently
>   block the unconditional-seal goal. With `GoodBase` both are TRUE (vacuous off-base, genuine on-base) and dischargeable;
>   the caller (affine-polar residue, odd `q`) supplies `GoodBase` at every span-dim-2 base.
>   - **`GramCountsRecoverGram`** (**GENUINELY OPEN Gauss** — must be PROVED, probe-true) — `GoodBase → (SameGramStratCounts
>     ⟹ SameExactGram + span-flag)`. Attack: primitive `ψ` → `sameGramStratCounts_transform` (equal `innerZ` fibre sums) →
>     Fourier-invert; **bulk** (`gramStrat_inner_eval_ne`) ⟹ primal Gram, **boundary** (`gramStrat_inner_eval_zero`) ⟹ the
>     `u∈span{a,b}` flag (indicator `polarBilin.flip(r₁a+r₂b−r₃u)=0 ⟺ u∈span{a,b}`).
>   - **`RefinedWittExtends`** (**CITATION of Witt's theorem** — acceptable to carry, like G3/Babai; discharge via a Mathlib
>     Witt build if one appears) — `GoodBase → (SameExactGram + span-flag ⟹ StabOrbit)`. Witt on nondeg `W^⊥`. (Unrefined
>     `WittExtendsToOrbit Q {a,b}` FALSE 36>27; the flag repairs it.)
>   **▶ NEXT = discharge `GramCountsRecoverGram`** (the single OPEN Gauss lemma = "`K` non-degenerate") via the transform +
>   `inner_eval_ne`/`_zero`; and instantiate a primitive additive character. `RefinedWittExtends` = the Witt citation.
> - **Piece 2 — the WL bridge:** `SameClassCounts C ⟹ SameGramStratCounts` (the actual WL colouring's counts refine the
>   gram-strat counts). **★ ORBIT-DIRECT — do NOT route through `ClassCountsSeparateGram`:** that predicate targets
>   `SameExactGram`, and its capstone `ScratchWLClassCounts.colorEq_iff_stabOrbit` carries `WittExtendsToOrbit Q {a,b}`,
>   which is **FALSE** at the span-dim-2 base (orbits `36 ⊋ 27` gram-classes — the exact reason Piece 1a targets the orbit
>   directly). So Piece 2 feeds `SameGramStratCounts` into `gramCountsEq_iff_stabOrbit`, never touching `SameExactGram`/Witt.
>   NB Piece 2 is **coupled math, not plumbing**: the bridge holds at the fixpoint `C∞`, and its content is the finding-5
>   equitability argument = a generalization of Piece 1's K-non-degeneracy to `C∞`'s own strata (cf. the `VO⁺₄(5)` round-4
>   tail where coarse strata need one extra iteration).
> - **Piece 3 — assembly:** compose `SameClassCounts ⟹ SameGramStratCounts ⟹ StabOrbit` (via `gramCountsEq_iff_stabOrbit`,
>   orbit-direct) + `ScratchBoundedMultLeaves.leaves_le_prod_concentrated`. (`ScratchWLClassCounts` still contributes the
>   `iso3`/`classCount`/`IsWLStable` defs + soundness; only its `colorEq_iff_stabOrbit`/`ClassCountsSeparateGram` capstone is
>   Witt-dead at `{a,b}` and superseded.)
>
> **Superseded-but-subsumed (do not build on):** `ScratchPlanePinInduction` (`PlanePinnable`) and the `ScratchWLWiring`
> *singleton bridge* (`pinsPlane_of_planePinnable`, `ReadsSingletonCounts`, the residual `SeparatesPlaneFromComplement`) —
> their singleton-anchor mechanism stalls (`pin_probe.py`). The `ScratchWLWiring` **Core** (`refines_zSet_of_pinsPlane`/
> `colorEq_iff_stabOrbit`: `PinsPlane ⟹ bᵢ=1`) and `ScratchWLClassCounts` (the class-count observable + reduction) survive.
> Full reasoning + all findings + dead ends: **§9.7** (self-contained).
> **Probes** back the direction: `bᵢ=q(q−1)/2` concentrated at span-dim-1 (`forced_triangle_mult.py`); span-dim-2 recovery
> bounded-round `r*∈{3,4}` d-uniform (`recovery_depth_probe.py`). **`L`** is a corollary of route A (route B).
> **Start at:** this HANDOFF → **§9 (the self-contained logical map: architecture + 5 insights + plan + dead ends, esp.
> §9.7 for the Step C attack)** → the "Verify the landed substrate" list (bottom of STATUS). (§8 ITEM A/B is the older
> chronological scoping, now subsumed by §9.) **════════**
>
> **LANDED SUBSTRATE (was "LIVE NEXT TASK") — Phase 0 ✅ + Phase 1 ✅ + Phase 2 FOUNDATION ✅.** (1)
> **Phase 0 — RUN 2026-06-30** (`Phase0_BranchProfile`): T0 not falsified, positively supported — `STARVED=0` everywhere,
> q=2 single-path through **d=8** (`leaves=1`), only `VO⁻₄(5)` branches (`B=3, L=2, leaves=6`, `bᵢ < q`); q≥7 tail blocked by
> the per-node-cost wall (§4). (2) **Phase 1 — LANDED** (`ScratchBoundedBranching.lean`, axiom-clean): the bridge
> `BoundedBranchingDisposition` + `certifiedBoundedTree_of_disposition` ⟹ **`leaves ≤ Bᴸ`** (`CertifiedBoundedTree.leafBound`),
> on the proven tree-combinatorics core `BTree.leaves_le_pow`; `B=1` corner recovered. (3) **Phase 2 — FOUNDATION LANDED**
> (`ScratchBranchingBound.lean`, axiom-clean): `stabOrbit_cover_card_le : #{Stab(S)-orbits} ≤ |K|^{|S|+1}` (orbits ↪
> exact-Gram profiles, mod Witt) ⟹ `degBound` at the **quasipoly** tier (recovery bridge now re-derives banked quasipoly,
> unconditional). (4) **`L = O(d)` — GEOMETRIC CORE + SPAN-GROWTH SOLVED (2026-07-01)** (`ScratchBranchDepth.lean`,
> axiom-clean, 10 thms): `spanning_sameExactGram_determines` (generalised `coords_determineK` to a spanning base) +
> `stabOrbit_singleton_of_spanning` (spanning anisotropic base ⟹ orbit-singletons) + `branchLevels_le_finrank` + the §3
> fixed-point kernel (`stab_fixes_span` ⟹ `nontrivialForks_le_finrank`: **forks into non-trivial orbits ≤ finrank = d**).
> **KEY FINDING:** the two `L` seams collapse to **one** — the span-growth residual (singleton-orbit forks) leaves span
> AND `Stab` fixed, so it IS **cell-discretisation**, which IS the **same WL-orbit defect as the poly crux** (ITEM B). So
> `B` and `L` share one open core; `L`'s remainder is NOT a separate easier target. `L = O(d)` NOT yet closed (genuinely
> open, not "moderate"); cheapest test = iterated `χ(det G₂)` at the `d+1` frame (Stage B.0 probe). (5) **δ′ LEAD SCOPED +
> SUBSTRATE LANDED (2026-07-01)** (`ScratchDominatorForms.lean`, axiom-clean): the δ′ engine is built + discharged on the
> 1-D cyclotomic family; **DIMENSIONAL WALL** — the two-point forced-triangle step gives 2 `Q`-constraints, cannot pin in
> `d≥3` (same wall as the seal's 2-round pair form; discharge was dim-1). Landed the **full-base** pinning
> `spanning_exactQ_determines` (reuses §1); verdict: δ′ restructures but doesn't dodge the WL-orbit defect — needs the
> extension route (`hcatch`) or a multi-point engine, both = the shared core. (6) **BOUNDED-MULT NON-VACUITY ✅ +
> LEAF-BOUND UPGRADE (2026-07-01).** The δ′ *singleton* is walled, but the recovery target only needs bounded *orbit*
> multiplicity. Probe (`forced_triangle_mult.py`): **`bᵢ ≤ q(q−1)/2 = Θ(q²)` — POLY(q), at EXACTLY ONE level (span-dim-1),
> `bᵢ=1` elsewhere, `d`-uniform** (`q=3`: B=3 at d=4,6; `q=3,5,7`→B=3,10,21). So the crux is non-vacuous & empirically poly,
> and branching is *concentrated*. Landed `ScratchBoundedMultLeaves.lean` (axiom-clean): **`leaves_le_prod`** — lifts Phase 1's
> uniform `leaves ≤ Bᴸ` to **per-level** `leaves ≤ ∏ⱼ b(j)` + `leaves_le_prod_concentrated` (branching confined to level-set
> `J` ⟹ `leaves ≤ ∏_{j∈J} b j`), so the probe profile gives `leaves ≤ q(q−1)/2 = poly(n)` directly. (7) **CRUX SPLIT + span-dim-1
> PROVEN + route A scaffold (2026-07-01).** The crux `bᵢ≤poly(q)` splits into **span-dim-1** (`bᵢ≤q²`, **PROVEN**,
> `ScratchSpanDimBound.stabOrbit_cover_card_le_line`) and **span-dim ≥ 2 = route A** (`bᵢ=1`). Route A's direct proof stalls
> (it's the multi-base `s(C)` recovery — Gauss content), but the probe says it's **crackable** (bounded-round `r*∈{3,4}`,
> d-uniform). Route A **increment 1 LANDED** (`ScratchSpanDim2Recovery`): reduces `bᵢ=1` to `WallKernelFor(2-round count)`.
> **(8) ROUTE A RECOVERY — split into geometric CORE (I) + iteration SEAM (II); (I) mostly LANDED (2026-07-01).** obs fixed
> to the seal's `jointIsoCountK` profile; soundness LANDED (`ScratchJointCountInvariant.obsInvariant_jointCountProfile`);
> `d`-cancellation LANDED (`ScratchComplementFactorK.levelset_count_factors_through_chiDet`, reused from seal — the planned
> "complement-factoring" was already built for the seal). **(I) CORE:** `ScratchSpanDim2Geom.exactGram_of_sameWProfile`
> (isoClass profile over `W=span{a,b}` ⟹ exact Gram, `d`-independent) + its `hspan` discharge:
> `ScratchSpanDim2Span.hspan_of_two_indep` (combinatorial bridge) + `ScratchConicCount` (`sum_quadraticChar_sq_sub`,
> `card_binary_form` — the conic count `q−ε`, elementary/no-Gauss). **[SUPERSEDED 2026-07-02: (I) is now fully LANDED
> both branches, Steps B + C-reduction + Route α sub-step done — see the top FRESH-READER HANDOFF + §9.7. The live item is
> now proving `ChiProfileSeparatesPlane`.]** Full plan: §9.
>
> **Relocated (stronger target — valid but harder, likely quasipoly-adjacent; → CellsAreOrbits doc / §2c):** full
> `CellsAreOrbits` + the `WallKernelFor Obs` determiner (the demoted route); and **Route II
> `crossBranchHarvest_reproduces_residual`**, whose hypothesis `hreal` *provably requires* cells = orbits
> (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`) — it is the **|Aut|-computation** deliverable, a *different,
> stronger* goal than poly leaf count. Do not put them on the poly-leaf-count critical path.
>
> **Banked (unaffected):** quasipoly seal `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (in `build.sh`, axiom-clean);
> sub-exp `reachesRigidOrCameron_viaSpielman` (citable). **Durable harness:** `GraphCanonizationProject.Tests/RecoveryReconcileProbe.cs`.
> **════════ END PICK-UP ════════**

**Quality bar:** every Lean theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; no `sorry`, no fresh `axiom`;
`native_decide` banned; full build green when ported. "Poly time" stays a **meta-argument** — the project formalizes no
runtime model, so the structural deliverable is the seal disjunction `reachesRigidOrCameron` (modulo `{G3}`), and "poly"
is the meta-claim that the node count is poly and per-node work is poly.

---

## 1. The claim, and why this is the right route

**The cost model.** Chain descent's cost is `Σ_{nodes} (per-node work)`, **not** the naive product over a fully-explored
IR tree (00-START-HERE §1). Polynomial = three factors:

1. **Poly leaf count — `leaves = ∏ᵢ bᵢ ≤ poly(n)`**, where `bᵢ = #{Stab(Sᵢ)-orbits in the selected cell at level i}`.
   The descent **branches** over the orbits of the selected cell (within-orbit siblings pruned by harvest,
   `CoveredByPathFixingAut`); cross-orbit branches are genuine and compared. **This is the open content** (§4, §6). It is
   *not* "single path": default mode branches (`VO⁻₄(5)`: `leaves = 6`).
2. **Poly branching-depth — `L = O(d)`**, where `L =` the **number of branching levels on any root→leaf path** (nodes with
   `bᵢ > 1`). **NOT landed — only empirical.** `defaultSpineChain_reaches_leaf` bounds the *single-chain length* `≤ n`
   (per-node work over one path), which is **not** `L = O(d)`: in `leaves ≤ Bᴸ` an `L` of only `≤ n` gives `B^n` = exponential.
   `L = O(d)` is a *structural* fact about the forms graph (an `O(d)` base rigidifies `O⁻_d(q)`, after which all cells are
   singletons ⟹ no further branching), measured `Θ(d)` (plan §1 "Probe_FrameWLScaling": frame base `d+1`) but **not** proved
   in Lean. It is **as load-bearing as `bᵢ ≤ poly(q)`** and is a first-class obligation (D1′, §6) — Stage B.0 (`O(Q)`
   discretizes at the `d+1` frame) is the natural lever, but it is not free and `≤ n` does not give it.
3. **Poly per-node.** Every harvest loop in `ChainDescent.cs` is `n`-bounded; no exponential mechanism (plan §1 item 1
   "RESOLVED"). Hard poly ceiling (≈ `n⁵–n⁶`).

**Why poly leaf count is reachable (the arithmetic).** `∏ᵢ bᵢ ≤ Bᴸ` with `B = maxᵢ bᵢ`, `L =` #branching-levels. Since
`n = q^d`, **`B ≤ poly(q)` AND `L = O(d)` together ⟹ `Bᴸ = q^{O(d)} = poly(n)`** — *both* factors are needed (a poly `B`
with `L ~ n` is still exponential, and `L = O(d)` with `B ~ n` is quasipoly). The plausibility argument for `bᵢ ≤ q`
(*individualizing one point adds **one** new Gram coordinate, `≤ q` values*) bounds the **per-step cell refinement**, not the
**in-cell orbit count** directly — by Witt the latter is a-priori `≤ q^{|Sᵢ|} = q^{O(d)}`, and `model_gap.py` shows the
cell-vs-orbit gap **grows with `q`**. So `bᵢ ≤ poly(q)` is a genuine **hypothesis Phase 0 must test against `q`-scaling**, not
a near-proof. What the harvest *does* buy over the `n^{Θ(d)}` frame route is replacing the `n`-way fork at each level by a
`bᵢ`-way fork; whether `bᵢ` is `≤ poly(q)` (poly) or grows faster (quasipoly) is exactly the open measurement.

**Honest scope — strictly weaker than `CellsAreOrbits`, but NOT a sidestep of the WL-vs-orbit axis.** The open content is
**bounded branching** (`bᵢ ≤ poly(q)`), of which `CellsAreOrbits` (`bᵢ = 1 ∀ cells`) is the much stronger special case. So
the recovery route asks for *genuinely less* than the demoted CellsAreOrbits route — but it is still a statement *about*
the orbit-vs-cell relation (it bounds, rather than collapses, the defect). The only route that avoids that axis entirely is
**Route C** (recover `Q` ⟹ `Aut = GO(Q)` known; §7) — bigger, behaviour-changing, the user's last resort. The recovery
route's bet, backed by the probe (`STARVED = 0`, `leaves` small): bounded branching holds on the carved residual families.

---

## 2. The object + the C# mechanism

### 2a. The residue
- **Graph.** `V = K^d` (`K = F_q`, `d = 2m`), adjacency `Q(x − y) = 0` for a nondegenerate quadratic form `Q` of type `ε`
  — the affine-polar forms graph `VO^ε_{2m}(q)`. A translation (Cayley) scheme ⟹ vertex-transitive + schurian.
- **Automorphisms.** The affine similitude group: translations `⋊` `ΓO^ε(Q)` (linear similitudes `Q(gx) = μ(g)·Qx`, with
  field automorphisms; for prime `q`, just `GO^ε(Q)`). `|Aut|` is huge (e.g. `VO⁻₄(3)`: `233280 = 3⁴ · |GO⁻₄(3)|`) — the
  graph is far from rigid, which is *why* the harvest keeps the branching small (few orbits per cell).
- **Skresanov isolation.** By the route-doc §9.9.18 reduction, the small-Aut non-geometric *schurian* rank-3 residue is
  affine, and splits into `{1-dim cyclotomic (cited) + forms-graphs (c)–(f)}`. The recovery core is needed only on (c)–(f)
  `{affine-polar / alternating / half-spin / Suzuki–Tits}`.

### 2b. How the canonizer stays poly — a small branch-but-resolve tree (verified against `GraphCanonizationProject/`)
1. **1-WL refinement** (`WarmPartition.cs`): colour refinement to cells. Cells are coarser than orbits at bounded bases —
   the canonizer does **not** rely on cells = orbits.
2. **All-reps oracle** (`CascadeOracle.cs`): "certifies nothing a priori" — `Classify` returns every vertex of the target
   cell. Orbit structure is recovered a-posteriori, not asserted.
3. **Cross-branch harvest + prune** (`ChainDescent.cs:589 CoveredByPathFixingAut`): after exploring the first representative
   of a cell, the descent harvests verified automorphisms that fix the individualized path pointwise, then **prunes any
   sibling reachable from an explored one via those `Stab(path)`-automorphisms** (its subtree is isomorphic — no canonical
   it omits). This is the engine that collapses the tree.
4. **Deferral selector** (`ChainDescent.cs:251-281`, **on in normal operation** — it changes the canonical form): among
   non-singleton cells, consume one the oracle collapses to a single orbit (symmetric), defer multi-orbit cells, branch a
   real one only when none is symmetric (Phase 2). An *optimization* over the harvest, not the core mechanism.

**The default (canonical-form-preserving) path — what Lean's `spine_branch_independent` certifies — reaches completeness
via the HARVEST (step 3), not the deferral (step 4).** Important consequence (it corrects an earlier framing of this doc):
in default mode the descent **branches but resolves** — `RecoveryReconcileProbe.cs` shows `VO⁻₄(5)` runs
`branchingNodes = 4`, `leaves = 6`, **`branch[resolved] = 4`, `STARVED = 0`**. So the selected cell is *not* always one
orbit there; `SinglePathDisposition` (no branch) describes the **deferral** single-path (`Phase2 = 0`), while the default
canonical-form-preserving path is **branch-but-resolve via the cross-branch harvest**. These are *different bridges* — see §2c.

---

## 2c. The target predicate, and the strength ladder (do not drift upward)

**The live target is the WEAKEST sufficient condition: bounded branching ⟹ poly leaf count.** Everything stronger is
relocated. The strength ladder, weakest → strongest:

| # | predicate | what it gives | who needs it | landed substrate |
|---|---|---|---|---|
| **★ T0** | **bounded branching `bᵢ ≤ poly(q)`** (selected cell has `≤ poly(q)` orbits) | **poly leaf count `∏bᵢ = poly(n)`** — branch-but-resolve | **default mode** (`STARVED=0`, `leaves` small) | **✅ Phase 1 LANDED** — `ScratchBoundedBranching` (`BoundedBranchingDisposition` + `certifiedBoundedTree_of_disposition`; the `leaves ≤ Bᴸ` core `BTree.leaves_le_pow`, axiom-clean) |
| T1 | `∃` a pure cell at each base | single path **via deferral** | deferral mode (`Phase2=0`) | `SelectedCellIsOrbit` parametric in `sel` (the "pick a pure cell" part unbuilt) |
| T2 | `SinglePathDisposition` (the *selected* cell is one orbit) | single path | a *fixed-selector* deferral | `certifiedSinglePath_of_disposition` (`ScratchNodeCountBridge`) — the `B=1` corner of T0 |
| T3 | full `CellsAreOrbits` (∀ cells = orbits) | single path, **+ reproduces |Aut|** | — (false at 1-WL, `|S|≥2`) | `WallKernelFor Obs`; Route II `hreal` |

**Why T0 is the right target.** `T0` is the only rung the C# *default, canonical-form-preserving* mode actually satisfies
(it branches; `T1–T3` all assert no branching). And `T0` is **strictly weaker** than `T3`: it bounds the orbit-vs-cell
defect rather than collapsing it. `T0 → poly` is pure arithmetic (`∏bᵢ ≤ Bᴸ = q^{O(d)} = poly(n)`), so the only *math* is
the structural bound `bᵢ ≤ poly(q)` (§4, §6 Phase 2).

**RELOCATED — the stronger rungs (valid, but harder; likely only quasipoly-adjacent in difficulty):**
- **`T3` full `CellsAreOrbits` + the `WallKernelFor Obs` determiner** → the demoted CellsAreOrbits route
  ([`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md)). Independent-math value (WL-dim 2),
  **not** on the poly-leaf-count critical path.
- **Route II `crossBranchHarvest_reproduces_residual` / `autP_reproduced_of_visibleRealizers`** (Part A): reproduces the
  residual group **and order**, but its hypothesis `hreal` *provably requires* `CellsAreOrbits`
  (`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`) — so it is the **|Aut|-COMPUTATION** deliverable (a *different,
  stronger* goal than canonical-form poly), kept as a reference, not a leaf-count bridge.

**Reusable partial assets (shrink T0's open part):**
- **DRG depth-1 freebie.** The forms graph **is P-polynomial** (diameter-2 SRG), so `theorem_2_HOR_of_pPolynomial`
  (`Scheme.lean`) gives `CellsAreOrbits` at base `{v}` for free ⟹ `b₁ = 1`; the open content is `bᵢ` at `|S| ≥ 2`.
- **Depth-graded recovery** (`RecoverableByDepth`) — the within-orbit pruning (D4) holds to bounded depth.

**Untried leads on `bᵢ ≤ poly(q)` / orbit recovery (run before concluding it's hard):**
- **δ′ dominator-closure** (`dominatorReachable_affine_step`, `CascadeAffine`) — a *non-counting* forced-triangle route
  (closed the `H={±1}`/subfield cyclotomic families). **Never tried on `VO^ε`.** If it bounds the per-cell orbit split it
  feeds T0 directly, no Gauss.
- **Skresanov rank-3 2-closure** — the group-theoretic bound on the orbit-vs-cell defect.
- **`EdgeGeneratesFromSet`** — constructive certificate (`remaining-work.md` §3b).
- **Gauss `χ(det G₂)`** — the analytic determiner; note this proves the *stronger* `bᵢ = 1`, so it overshoots T0 (use only if T0's weaker bound is not separately reachable).

**Dead for THIS residue:** block/imprimitive decomposition (`coversOrbits_of_blockDecomposition`) — vacuous (forms graph is a
*primitive* rank-3 SRG). **Last resort:** Route C (§7); per user, exhaust T0 + the leads first.

---

## 3. What is already proved (the foundation, all axiom-clean)

Two layers are landed: the **poly spine** (the node-count bridge — the recovery route's mechanism, now generalized to
bounded branching: the `B=1` single-path corner `ScratchNodeCountBridge` **and** the T0 bridge `ScratchBoundedBranching`
with `leaves ≤ Bᴸ`, both axiom-clean) and the **seal infrastructure** (Stage A/B — the correctness disjunction, banked at
quasipoly). The remaining open content is the **forms-graph discharge** of the bridge's carried hypotheses (Phase 2:
`bᵢ ≤ poly(q)` and `L = O(d)`) + the concrete-descent realisation seam; the seal layer is reference/banked.

### 3a′. THE POLY SPINE — the node-count bridge (`ScratchNodeCountBridge`, axiom-clean, NOT in build)
The recovery route's mechanism. **Currently landed at the `B=1` (single-path) corner; Phase 1 generalizes it to T0
(bounded-branching `B`).** What exists:
- `SelectedCellIsOrbit adj P sel S` — the **selected** cell is one `Stab(S)`-orbit (the `B=1` per-base condition).
- `SinglePathDisposition = ∀ S, SelectedCellIsOrbit` (= ladder rung **T2**; the structural form of `Phase2=0`, deferral mode).
- `certifiedSinglePath_of_disposition` — ⟹ `CertifiedSinglePath` (`boundedNodes ≤ n` + every consumed cell one orbit).
- `singlePathDisposition_of_cellsAreOrbits` / `selectedCellIsOrbit_of_cellsAreOrbits` — full `CellsAreOrbits` (T3) discharges
  it (the "go through the strong predicate", overshoot angle).
- **Residual (Increment-0):** the `canonAdj`-transport seam — rep-choice invariance of the leaf canonical (analogue of
  `spine_branch_independent`). Depth-1 core landed.

**Phase 1 — ✅ LANDED (`ScratchBoundedBranching.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, NOT in build).**
The **T0** generalization that captures the C# default mode (branch-but-resolve):
- **§1 — the pure tree-combinatorics core (the load-bearing `D3` math):** `BTree` (rose tree) + `leaves`/`branchDepth`/`BoundedDeg`
  + **`BTree.leaves_le_pow : BoundedDeg B t → leaves t ≤ B ^ branchDepth t`** — a tree with node-degree `≤ B` and `≤ L`
  branching levels on any path has `≤ Bᴸ` leaves. Forms-graph-free, reusable.
- **§2 — the disposition:** `SelectedCellOrbitsLE` (selected cell covered by `≤ B` `Stab(S)`-orbits) + `BoundedBranchingDisposition`
  (`= ∀ S`), generalizing `SelectedCellIsOrbit`/`SinglePathDisposition`; monotone in `B`; `selectedCellOrbitsLE_one_of_isOrbit`
  = the `B=1` corner (a mono single-orbit cell is a `≤1`-orbit cover).
- **§3 — the capstone:** `CertifiedBoundedTree` (bundles the disposition `cellsBounded` + the descent tree's `degBound`/`depthBound`)
  with **`CertifiedBoundedTree.leafBound : leaves t ≤ Bᴸ`** (the poly leaf count), and **`certifiedBoundedTree_of_disposition`**
  (generalizes `certifiedSinglePath_of_disposition`). `leaves_le_one_of_certifiedBoundedTree_one` recovers the `B=1` single path.
- **Residual (Increment-1 seam, parallel to Increment-0's `canonAdj`):** that the *concrete* branching descent realizes the
  orbit-branching tree — i.e. `degBound`/`depthBound` follow from the disposition because the tree's node degrees ARE the
  per-base orbit counts — is carried as structure fields, discharged in Phase 4 (the concrete branching descent). The `B=1`
  instance of this seam is the single-path module's landed content.

### 3a. The conditional capstones (the SEAL layer — banked at quasipoly; reference)
- **Stage A — `reachesRigidOrCameron_viaAffineFormScheme`** (idx 1207). The abstract scheme-level capstone for the
  forms-graph residue: carries `hbase : IsBase … T` (the **free** group base `T = {0,e₁,…,e_d}`, `(G^(2))_T = {1}`,
  discharged outright) + `hFormCert : RelCountsDetermineOrbit … T` (**the only open content**). Wiring:
  `cellsAreOrbits_of_relCountsDetermineOrbit` → `twinsRealizedByResidualAut_iff_cellsAreOrbits` →
  `separatesAtBoundedBase_of_twinsRealized` → `reachesRigidOrCameron_viaSpielman`. **Carries NO `hSmallAutThin`.**
- **Stage B (live) — `reachesRigidOrCameron_viaIsotropySeparates_wittFree`** (idx 1248). The concrete forms-graph
  capstone: seals the rank-3 SRG `VO^ε` residue from a **bounded symmetry-broken base** + **isotropy-count injectivity**,
  carrying **NO Witt** (the easy half `RelationRefinesIsotropy` is discharged Witt-free by similitude-invariance,
  `relationRefinesIsotropy_similitude`, idx 1247). The **only** open input is the Gauss target `IsotropySeparatesAtBase Q T`
  (idx 1240). This is the live endpoint.

### 3b. The recovery-core plumbing (Stage A, idx 1203-1206)
- `RelCountsDetermineOrbit` (1203) — the open predicate (two vertices with equal relation-count profile at base `T` lie in
  the same `Stab(T)`-orbit). **Open / GI-adjacent / false for high `s(C)`.**
- `cellsAreOrbits_of_relCountsDetermineOrbit` (1204), `recoversWhileSymmetric_of_relCountsDetermineOrbit` (1205),
  `selfDetectsWhileSymmetric_of_relCountsDetermineOrbit` (1206) — the producers that lift the predicate to the seal.

### 3c. Stage B.0 — the recovery back-half (form coords ⟹ vector), landed
- `coords_determine` (1211) + `polar_eq_of_sub` (1210): if `Q`'s polar is nondegenerate and `Q v`, `Q(v − e_i)` agree on
  the basis, then `v = v'`. The Witt-free back-half — **reusable**.
- `isometryGroup` / `similitudeGroup` (1212/1218), `frameBase` (1215), `reachesRigidOrCameron_viaOrthogonalForm` (1217):
  the isometry scheme `O(Q)` discretizes at the basis-frame and seals via depth-1. **Caveat (the crux gap, §4):** this is
  the *finer* `O(Q)`, not the rank-3 SRG `VO^ε` (= similitude `GO(Q)`, relation = `isoClass`).

### 3d. The Gauss toolkit (the analytic engine, shared with the quasipoly seal)
`GaussCount.lean` (Gauss-sum lemmas incl. `gaussSum_sq_ne_zero`, `sum_addChar_quadForm_ne_zero`); `IsotropicIncidenceCount*`
(`configGaussSum_eq_det`, `card_quadForm_eq`); `ObservableCountBridge*` (`χ(det G₂) ↔ Z_u(S)`); `PairForm`,
`PerAnchorBound.c0_le_threequarters`. **All field-generic** (`FieldGeneric*`). This is exactly the machinery that proved
`IsotropySeparatesAtBase` at the matching base — the poly upgrade reuses it.

### 3e. SUPERSEDED (do not build on — frame-locked, FALSE for `VO^-`)
`SimilitudeFrameSeparates` (1221), `reachesRigidOrCameron_viaSimilitudeForm` (1222), `CountsDetermineFrameQ` (1224),
`IsotropyCountsRecoverFrameQ` (1234), `reachesRigidOrCameron_viaCountsDetermineFrameQ` (1226), `…viaIsotropyCounts` (1237).
A finite probe showed the one-round count is shell-blind at the *symmetric* frame for minus-type (an `e_i`-swap isometry).
The fix — already landed — is the **arbitrary / symmetry-broken base** family (`SeparatesAtBase` 1238,
`reachesRigidOrCameron_viaSymmetryBrokenBase` 1239, `IsotropySeparatesAtBase` 1240). Use those.

---

## 4. The open core, precisely — T0 = bounded branching `bᵢ ≤ poly(q)` **and** `L = O(d)`

**The open core (poly) — TWO coupled obligations, both load-bearing.**

> **T0a (bounded branching factor).** At every partial base `Sᵢ` on the descent path, the **selected cell** (a *relative
> sphere*) splits into `bᵢ ≤ poly(q)` `Stab(Sᵢ)`-orbits — a bound **uniform in `d`**.
> **T0b / D1′ (bounded branching depth).** The number of branching levels (`bᵢ > 1`) on any root→leaf path is `L = O(d)`.
> Together: `leaves = ∏ᵢ bᵢ ≤ Bᴸ = q^{O(d)} = poly(n)`.

Both are needed (a poly `B` with `L ~ n` is exponential; `L = O(d)` with `B ~ n` is quasipoly). **T0b is NOT free from the
spine** — `defaultSpineChain_reaches_leaf` only bounds the single-chain *length* `≤ n`; `L = O(d)` is the structural fact
that an `O(d)` base rigidifies the residue (after which cells are singletons), measured `Θ(d)` but unproved. Treat it as a
peer of T0a, not a footnote. This whole core is the **poly** obligation (the node-count bridge's hypothesis), **NOT** a seal
predicate (`RelCountsDetermineOrbit` / `IsotropySeparatesAtBase` feed the *seal*, banked). It is **strictly weaker** than
`CellsAreOrbits` (`bᵢ = 1 ∀ cells`).

**Why even the weak per-cell bound is non-trivial (the `O(Q)` vs `VO^ε` gap).** The descent runs on the **similitude SRG**
(relation = `isoClass` ∈ {0, isotropic, anisotropic}, *not* the exact `Q`-value). Stage B.0's clean "orbit-of-difference ⟹
exact `Q(v−t)`" mechanism works only on the finer **isometry** scheme `O(Q)` — there `bᵢ = 1` outright. On the coarser
similitude SRG, a cell can hold several orbits (the isotropy class doesn't pin the exact Gram), so `bᵢ > 1` is real and
must be *bounded*. **Crucial point: T0 only asks `bᵢ ≤ poly(q)`, not `bᵢ = 1`** — so the *full* count-determination (which
gives `bᵢ = 1` and is the demoted CellsAreOrbits route) is an **overshoot**. The handles:
- **structural / one-new-coordinate (a HEURISTIC, not a near-proof)** — individualizing the *next* base point adds one Gram
  coordinate (`≤ q` values), so the cell *refines* `≤ q` ways. **Caveat:** this bounds the per-step cell-refinement
  *increment*, not the in-cell **orbit** count `bᵢ` directly — by Witt a cell at base `Sᵢ` can a-priori hold `≤ q^{|Sᵢ|} =
  q^{O(d)}` orbits, and `model_gap.py` shows the cell-vs-orbit gap **grows with `q`**. So `bᵢ ≤ q` is a *plausible target to
  test*, not an argument that nearly proves it; Phase 0 must measure `bᵢ` against `q`-scaling before this is leaned on.
- **untried non-counting leads** — δ′ dominator-closure (`dominatorReachable_affine_step`), Skresanov 2-closure,
  `EdgeGeneratesFromSet` (§2c). These could bound `bᵢ` without the analytic machinery.
- **DRG freebie** — `b₁ = 1` free (forms graph P-polynomial).
- **(overshoot, reserve)** the `χ(det G₂)` determiner (`WallKernelFor`, demoted route) — proves the stronger `bᵢ = 1`.

**Empirical anchor (Phase 0 — metrics INSTRUMENTED + FULL SWEEP RUN, 2026-06-30).** `RecoveryReconcileProbe.cs` reports
`B = MaxBranchFactor`, `L = MaxBranchPathDepth`, per-node `branchFactors`/`nodesByDepth` (in `DescentStats`); the
`Phase0_BranchProfile` sweep (default mode) measured:

| graph | n | d | q | leaves | B | L | branchFactors | `STARVED` |
|---|---|---|---|---|---|---|---|---|
| VO^ε₄(2), VO^ε₆(2), VO^ε₄(3) | 16–81 | 4,6 | 2,3 | 1 | 1 | 0 | [] | 0 |
| VO^ε₈(2) | 256 | **8** | 2 | 1 | 1 | 0 | [] | 0 |
| **VO⁻₄(5)** | 625 | 4 | **5** | **6** | **3** | **2** | [2@d3,2@d3,2@d3,3@d2] | 0 |
| VO⁺₄(5) | 625 | 4 | 5 | 1 | 1 | 0 | [] | 0 |

**GATE verdict — T0 NOT falsified, positively supported (within the feasible range):**
- **No `d`-driven explosion.** The q=2 `d`-sweep is single-path (`B=1, L=0, leaves=1`) **through d=8** — `leaves` flat in `d`,
  full `|Aut|` recovered (e.g. `VO⁻₈(2)`: `|Aut|=101072240640`). The D1 (`L=O(d)`) obligation is met *trivially* (`L=0`) at q=2.
- **The lone branching cell is `VO⁻₄(5)`:** `B=3, L=2, leaves=6`, `bᵢ ∈ {2,3}` — and **`bᵢ < q=5`**, direct support for T0a
  (`bᵢ ≤ poly(q)`). Branching is **minus-type + q≥5**; plus-type and q≤3 are single-path. `STARVED=0` ⟹ **D4 holds everywhere**.
- **The limiter is the per-node-cost wall, not blow-up:** `VO⁻₈(2)` took **~29 min for a 9-node single path** (~3 min/node) —
  pure generic-harvest cost at n=256/d=8, no rigid core (`STARVED=0`). So `B`-vs-`q` at **q≥7** and `L`-vs-`d` in a *branching*
  regime (q≥5, d≥6 ⟹ n≥15625) are **unmeasured — blocked by per-node cost, not by any explosion.** This is exactly the
  Route-C (constructive-Witt harvest, §7) axis: it would lower per-node cost and unlock the scaling measurements; the
  IR-solver would not (no rigid core here).
- **Honest residual:** the scaling claim rests on **one** branching datapoint. T0 is *consistent with and supported by* the
  data, but `bᵢ ≤ poly(q)` and `L = O(d)` are confirmed only at small `(q,d)`; the q≥7 tail is the open empirical gap.

**Aside — the seal's own bounded-base tightening (optional, separate).** Tightening the *seal* (not poly leaf count) to a
bounded base is `IsotropySeparatesAtBase`-as-determiner — a fixed-`d`-poly / quasipoly deliverable, different from and
weaker-payoff than the harvest poly. Not the T0 target.

---

## 5. The C# ↔ Lean bridge (the empirical validation)

The route is implementation-faithful: the open Lean target (T0) is exactly what the canonizer's counters measure. The
correspondence (T0's `BoundedBranchingDisposition` — LANDED in `ScratchBoundedBranching.lean`; `SinglePathDisposition`/T2 the
`B=1` corner):

| C# (`CanonResult.cs` / `ChainDescent.cs`) | Lean | meaning |
|---|---|---|
| `MaxBranchFactor` (`B`), `MaxBranchPathDepth` (`L`), `BranchFactors` | **T0 `BoundedBranchingDisposition`** (`bᵢ ≤ B`) → `leaves ≤ Bᴸ` | **the open target** — `B ≤ poly(q)` **and** `L = O(d)` (both measured directly) |
| `LeafCount` poly | `leaves ≤ Bᴸ = poly(n)` | the bottom-line cost number |
| `ClassifyStarved` / `BranchStarved` = 0 | **D4** within-orbit pruning (no stuck residue) | branching is by *orbit*, not by rep |
| `Phase2Nodes = 0` (deferral) | rung **T1/T2** (`SinglePathDisposition`) | the *deferral* single-path corner (`B=1`) |
| `GeneratorsHarvested`, `ResolvedByRecursion` | `StabilizerAt` orbit + `covered_sound` | a-posteriori orbit recovery (the prune) |

**Empirical validation (`RecoveryReconcileProbe.cs`, the REAL canonizer; Phase-0 sweep RUN 2026-06-30 — table in §4):**
- `ClassifyStarved = BranchStarved = 0` in **every** case, **both** modes; no flag, full `|Aut|` recovered ⟹ **D4 holds**.
- **Default mode (T0-relevant):** branching is `q`- and type-DEPENDENT — single-path (`B=1, L=0`) for q≤3 *and* for q=2 through
  **d=8** *and* for plus-type; the only branching cell is `VO⁻₄(5)` (`B=3, L=2, leaves=6`, `bᵢ ∈ {2,3} < q`). So `bᵢ > 1`
  occurs but stays small and `< q` where seen; T0 ≠ single path in general, but `leaves` stays small.
- **Deferral mode:** `Phase2=0`, `leaves=1` everywhere (incl. all branching cells) — the T1/T2 single-path corner.
- **Open scaling tail (per-node-cost-blocked, not blow-up):** `B`-vs-`q` at q≥7 and `(leaves, L)`-vs-`d` in a branching regime
  (q≥5,d≥6) are unmeasured — `VO⁻₈(2)` alone took ~29 min (a single path), so larger cells need the Route-C per-node speedup.

The remaining seam (Increment-0, `ScratchNodeCountBridge`): the **`canonAdj`-transport** — rep-choice invariance of the leaf
canonical. Depth-1 core landed; meta-plumbing, not the research core.

---

## 6. Plan of attack (phased) — target T0, poly leaf count

The deliverable = poly leaf count `∏ᵢ bᵢ ≤ poly(n)` (§4). Decomposition: **D1** branching-depth `L = O(d)` (**empirical, NOT
landed** — `defaultSpineChain_reaches_leaf` only gives single-chain length `≤ n`; a peer obligation to D2, see §4 T0b/D1′) ·
**D2** per-level `bᵢ ≤ poly(q)` (the open math) · **D3** `∏bᵢ ≤ Bᴸ = poly(n)` (arithmetic) · **D4** within-orbit pruning
(recovery) · **D5** lex-min = canonical (~landed + `canonAdj` seam).

**Phase 0 — GATE (empirical). ✅ DONE 2026-06-30 (not falsified, positively supported).** `Phase0_BranchProfile` (probe
reports `B`, `L`, per-node `BranchFactors`/`BranchDepths`, `NodesByDepth` in `DescentStats`) ran a `q`-sweep (d=4: q=2,3,5) +
`d`-sweep (q=2: d=4,6,8 ⟹ n=16,64,256). Verdict (full table §4 "Empirical anchor"):
- **D2 (`bᵢ ≤ poly(q)`):** the only branching cell `VO⁻₄(5)` has `B=3, bᵢ ∈ {2,3} < q=5` — supportive; q≤3 + plus-type single-path.
- **D1 (`L = O(d)`):** q=2 single-path (`L=0`) through **d=8** ⟹ `leaves` flat in `d`; the one nonzero `L` (=2, at q=5,d=4) is `< d`.
- **Gate result:** no super-poly blow-up in `leaves`, `B`, or `L` anywhere measured; `STARVED=0`, full `|Aut|` throughout.
- **Residual (NOT a falsification — a measurement limit):** scaling rests on one branching datapoint; q≥7 and branching-regime
  d≥6 are blocked by the **per-node-cost wall** (`VO⁻₈(2)` ≈ 29 min, single path), the Route-C (§7) axis. Re-run with a
  constructive-Witt per-node harvest to extend the table.

**Phase 1 — the bridge (Lean). ✅ DONE (`ScratchBoundedBranching.lean`, axiom-clean, NOT in build).**
**`BoundedBranchingDisposition adj P sel B`** (selected cell `≤ B` `Stab(S)`-orbits at every base) +
**`certifiedBoundedTree_of_disposition`**: `bᵢ ≤ B` + branch-depth `L` ⟹ **`leaves ≤ Bᴸ`** (`CertifiedBoundedTree.leafBound`),
on the self-contained tree-combinatorics core **`BTree.leaves_le_pow`**. `certifiedSinglePath`'s `B=1` corner recovered
(`leaves_le_one_of_certifiedBoundedTree_one`). Forms-graph-free, as planned. **The two realisation hypotheses** in
`certifiedBoundedTree_of_disposition` — `degBound` (the descent tree branches `≤ B`, from the disposition) and `depthBound`
(`≤ L` branching levels) — are the **Increment-1 seam** (the concrete branching descent; Phase 4), carried as structure
fields exactly as the `B=1` single-path module carries its `canonAdj` seam.

**Phase 2 — discharge D2 (`bᵢ ≤ poly(q)`) + D1 (`L = O(d)`) for the forms graph (Lean; the open math). ◑ FOUNDATION LANDED.**

- **✅ The foundational reduction + a-priori bound — `ScratchBranchingBound.lean` (axiom-clean, NOT in build).** Reusing the
  demoted route's geometric model (`Similitude`/`StabOrbit`/`SameExactGram`, `ScratchOrbitBaseCase`/`ScratchWallKernel`), the
  branching factor `bᵢ = #{Stab(S)-orbits}` **injects into exact-Gram profiles** `(Q t, (polar Q t s)_{s∈S})` (via soundness
  `stabOrbit_imp_sameExactGram_of_anisotropic` + carried Witt `WittExtendsToOrbit`), giving the **unconditional**
  `stabOrbit_cover_card_le : #{Stab(S)-orbits} ≤ |K|^{|S|+1}` (`card_gramProfiles_le` counts the profiles). This discharges
  the Phase-1 `degBound` at the **quasipoly** tier (`B = |K|^{|S|+1}`, `|S|=O(d)` ⟹ `leaves ≤ |K|^{O(d²)}`) — i.e. the
  recovery bridge now **re-derives the banked quasipoly, unconditionally (mod Witt)**. This is the foundation every poly
  approach needs (orbits are counted via Gram profiles).
- **★ The poly crux, now PRECISE.** `B ≤ poly(q)` ⟺ **the selected cell (one refinement class) cuts the `|K|^{|S|}` Gram
  profiles down to `poly(q)`** — the WL-orbit defect, the open research crux (same object as the seal core, at a small base).
  The "one new Gram coordinate ⟹ `bᵢ ≤ q`" story is a *heuristic*, not a near-proof (§4): it bounds the cell-refinement
  increment, not the in-cell orbit/profile count. **Untried non-Gauss leads for the per-cell cut:** **δ′ dominator-closure**
  (`dominatorReachable_affine_step`, never tried on `VO^ε`), **Skresanov 2-closure**, **`EdgeGeneratesFromSet`**. DRG freebie
  gives `b₁ = 1`. Gauss `χ(det G₂)` proves the *stronger* `bᵢ=1` (overshoot; reserve).
- **★ D1 (`L = O(d)`) is a distinct obligation** = the 1-WL refinement **discretizes the forms graph in `O(d)` levels** (so
  branching stops after `O(d)` forks). Geometric handle: at a base whose polar-images span (`coords_determineK`, landed),
  the exact Gram determines the vertex, so orbits are singletons — the "frame completes the descent" fact; connecting it to
  1-WL discretization is the moderate remaining piece. Empirically `L=2` at `d=4` (Phase 0).

**Phase 3 — D4 within-orbit recovery.** Same-orbit siblings are pruned (the harvest finds the map). The orbit-existence is
the *free* direction; reuse `RecoverableByDepth` / the harvest substrate. (This is where the landed Part A machinery is
genuinely useful — for *pruning*, not for the leaf-count bound.)

**Phase 4 — assembly + the `canonAdj`-transport seam + meta-poly.** Rep-choice invariance of the leaf canonical (depth-1 core
landed in `ScratchNodeCountBridge`); assemble D1–D5; "poly" stays the meta-claim over the structural `CertifiedBoundedTree`.

**Later — other families (Layer C):** alternating / half-spin reuse the skeleton; char-2 + Suzuki bespoke. **PORT** at the end.

*(The SEAL is banked at quasipoly — `reachesRigidOrCameron_affinePolar`. Stronger rungs T1–T3 / `WallKernelFor` / Route II
are relocated (§2c) — valid but harder, likely quasipoly-adjacent; not the T0 critical path.)*

**Definition of done (recovery route, affine-polar):** `BoundedBranchingDisposition` (with `B = poly(q)`) proved for the
family ⟹ `certifiedBoundedTree_of_disposition` gives the poly leaf-count object ⟹ the `canonAdj` seam closes ⟹ structural poly
object complete; the C# `STARVED = 0` + small `leaves` is the empirical witness. The SEAL is separately banked
(`reachesRigidOrCameron_affinePolar`, quasipoly). "Poly" remains the meta-claim over the bounded node count + poly per-node.

---

## 7. Route C — the constructive-oracle alternative (recorded fallback)

**Route C (constructive-Witt oracle).** Sidestep `RelCountsDetermineOrbit` *entirely*: **recover `Q` algebraically** from
the rank-3 relations (the two non-identity relations *are* the isotropy types — Stage B.0 `coords_determine` content), then
`Aut = GO(Q)` is a **known** group with explicit generators, canonicalized by standard poly group algorithms
(Schreier–Sims) through the existing `ITransversalOracle` seam. Complexity elementary; correctness depth = form-recovery
(carry it as a hypothesis, prove the downstream canonicalization closes). **It does not depend on the open core** — it works
whether or not the count crux holds, because the form exists unconditionally and geometric recovery bypasses both refinement
and counting.

**Cost-benefit.** Route C is a **larger build + a behavioural change** (needs the form-recovery oracle / a constructive Lean
recovery), and the user prefers to avoid the C# oracle risk. It is the **fallback if T0 stalls** — i.e. if Phase 0 shows
`leaves` super-poly, or `bᵢ ≤ poly(q)` hits a genuine obstruction across all of Phase 2's leads (structural + δ′ + Skresanov
+ EdgeGenerates + Gauss). Keep it in view; do not build it until T0 is exhausted (per user).

**Where this sits.** The banked quasipoly seal (`reachesRigidOrCameron_affinePolar`) is the floor; the recovery route (T0,
poly leaf count) is the upgrade to poly; Route C is the heavier guaranteed-poly alternative. Pursue in that order.

---

## 8. Pointers + HANDOFF (2026-07-01)

> **════════ FRESH READER — PICK UP HERE ════════**
> **State (2026-07-01):** Phase 0 ✅, Phase 1 (`leaves ≤ Bᴸ`) ✅, Phase 2 FOUNDATION (a-priori `B ≤ |K|^{|S|+1}`, quasipoly)
> ✅ — quasipoly end-to-end through its own bridge, mod Witt. **Since then the poly crux has been SPLIT and half-proved:**
> **ITEM A = `L=O(d)`** — geometric core + span-growth **SOLVED** (`ScratchBranchDepth`); reduced to the shared cell-
> discretisation core (= route A below). **ITEM B = `bᵢ≤poly(q)`** — δ′ walled (`ScratchDominatorForms`), but revived as
> bounded orbit-multiplicity: **span-dim-1 `bᵢ≤q²` PROVEN** (`ScratchSpanDimBound`), leaf bound lifted to per-level
> (`ScratchBoundedMultLeaves`), and **span-dim ≥ 2 (route A) reduced** (`ScratchSpanDim2Recovery`) to one Gauss predicate.
> **THE SINGLE LIVE ITEM: route A's exact-Gram recovery at the span-dim-2 base. RE-SCOPED (2026-07-01):** the
> complement-factoring is done (reused from the seal — `ScratchComplementFactorK` harvests the `d`-cancellation from
> `levelset_count_eqK`/`configGaussSum_eq_detK`); the observable is fixed to the seal's `jointIsoCountK` sub-config profile
> and its **soundness (`ObsInvariant`) is now LANDED** (`ScratchJointCountInvariant`), so route A reduces to the single open
> predicate **`WallKernelFor (jointCountProfile Q S₀ ·) Q ↑S₀`** (the `χ(det)`-profile + `O(1)` iterations recovering the 3
> exact-Gram coordinates, `d`-uniformly). The recovery splits into a **geometric CORE (I) — LANDED**
> (`ScratchSpanDim2Geom.exactGram_of_sameWProfile`: the isoClass profile over the plane `W=span{a,b}` determines the exact
> Gram, `d`-independently) — and the **iteration SEAM (II)** (WL-stable ⟹ profile-over-`W`, the frontier). See ITEM B
> "INCREMENT 2" / "THE EXACT-GRAM RECOVERY PLAN" below and the top-of-doc FRESH-READER HANDOFF. All twenty-five modules axiom-clean.
>
> **▶ ITEM A — `L = O(d)` (branch-depth; the more tractable). ◑ GEOMETRIC CORE LANDED (2026-07-01).** Obligation: the
> 1-WL descent discretizes the forms graph in `O(d)` levels, so branching stops after `O(d)` forks
> (`certifiedBoundedTree`'s `depthBound`). **LANDED** (`ChainDescent/ScratchBranchDepth.lean`, axiom-clean, NOT in build):
> (1) `spanning_sameExactGram_determines` — the doc's "first concrete step": generalises `coords_determineK` from the
> standard frame `{Pi.single i 1}` to an **arbitrary base with `span = ⊤`** (nondeg polar + exact Gram to `S` ⟹ vertex
> determined; only the polar half is used). (2) `stabOrbit_singleton_of_spanning` — composing with soundness: at a
> **spanning anisotropic** base every `Stab(S)`-orbit is a **singleton** (the "`O(d)` base rigidifies `O^ε_d`" backbone).
> (3) `branchLevels_le_finrank` / `branchLevels_le_dim_forms` — the **`O(d)` arithmetic**: `L` independent branch-vectors
> ⟹ `L ≤ finrank K V = d`, feeding Phase 1's `depthBound` with `L := d`.
>
> **SPAN-GROWTH SEAM — SOLVED (2026-07-01, §3 of the module).** The fixed-point kernel: an `S`-fixing similitude is
> linear ⟹ fixes all of `span S` ⟹ a vertex `w ∈ span S` is a **fixed point** (singleton orbit)
> (`stab_fixes_span`/`stabOrbit_trivial_of_mem_span`). Contrapositive: a **non-trivial** orbit lies **outside** `span S`
> (`notMem_span_of_stabOrbit_ne`), so individualizing it **strictly grows the span**
> (`span_lt_span_insert_of_stabOrbit_ne`). With the strict-chain count (`strictChain_le_finrank`, axiom-clean), **the
> number of forks into non-trivial orbits on any path is `≤ finrank = d`** (`nontrivialForks_le_finrank`). So span-growth
> is discharged for the forks that grow the span — it was NOT independent tech debt but a provable geometric fact.
>
> **★ THE TWO SEAMS ARE ONE — the remainder collapses to cell-discretisation (KEY FINDING 2026-07-01).** After
> span-growth, `L = (non-trivial-orbit forks, ≤ d, PROVED) + (singleton-orbit forks, T)`. A singleton-orbit fork enters a
> `{w}` with `w ∈ span S`: this leaves **both** `span S` and `Stab(S)` unchanged, so it can be a fork **only** because the
> coarser refinement *cell* split (1-WL sees new isotropy data `isoClass(Q(·−w))` the orbit structure does not). Hence
> `T` = the cell-vs-orbit defect = **cell-discretisation**, which is the **same WL-orbit defect as the poly crux ITEM B**
> (`B ≤ poly(q)`), now surfacing at the level of branch *depth*. **Consolidation:** the recovery route's two open factors
> (`B` and `L`) share **one** open core — bound the cell/orbit relationship on `VO^ε` by `poly(q)`. `L`'s residual is not
> a separate, more-tractable target; closing the poly crux (ITEM B) also closes `L`.
>
> **CELL-DISCRETISATION — SCOPING (2026-07-01).** Precise obligation: at a base approaching `span = ⊤`, the 1-WL cells
> reach orbit-resolution (singletons — `stabOrbit_singleton_of_spanning` makes orbits singletons at `span=⊤`, so cells
> = orbits ⟺ cells singleton there) within `O(d)` extra levels. The content = **the isotropy-class profile recovers the
> exact-Gram profile** at a (near-)spanning base — a *full-base* instance of `WallKernelFor Obs` (`ScratchWallKernel`),
> the seal's open kernel. Two honest consequences: **(i)** it is NOT cheaper than the seal core in general (same defect),
> so `L = O(d)` is genuinely open, not "moderate" as earlier framed — correcting the STATUS/§4 wording; **(ii)** but at a
> **spanning** base it is *more constrained* than the seal's *bounded*-base kernel (`WallKernel` was refuted at a bounded
> base, §6 Increment 3), so the spanning instance may crack where the bounded one didn't — the lead is the **iterated
> `χ(det G₂)` observable** (the seal's crack) evaluated at the `d+1` frame (Stage B.0 / `Probe_FrameWLScaling`, plan §1):
> does it discretise in `O(d)` levels at the spanning frame? That probe (empirical) is the cheapest next test for `L`.
> Empirical anchor: `L=2` at `d=4`, `L=0` for q=2 through `d=8` (Phase 0) — consistent with fast discretisation.
>
> **▶ ITEM B — `B ≤ poly(q)` (the poly crux; the research core).** Obligation: `certifiedBoundedTree`'s `degBound` at the
> **poly** tier. **Precise form (landed reduction):** `stabOrbit_cover_card_le` (`ScratchBranchingBound.lean`) gives
> `#orbits ≤ |K|^{|S|+1}` via orbits ↪ exact-Gram profiles; poly ⟺ **the selected cell cuts the `|K|^{|S|}` profiles to
> `poly(q)`** (the WL-orbit defect — same object as the seal core, at a small base).
>
> **δ′ DOMINATOR-CLOSURE LEAD — SCOPED + SUBSTRATE LANDED (2026-07-01).** The δ′ forced-triangle engine is fully built
> (`CascadeAffine` §S-bridge-δ: `DominatorReachable`, `dominatorReachable_of_rank`, affine criterion
> `affineScheme_interNum_eq_one_of_unique`, seal consumer `separatesAtBoundedBase_of_dominatorClosure`) and **already
> discharged end-to-end** on the 1-D cyclotomic family (`dominatorReachable_G0pow_neg` / `reachesRigidOrCameron_viaG0powNeg`,
> via cross-ratio). **★ THE DIMENSIONAL WALL (scoping finding):** the δ′ *step* (`DominatorReachable.step`) pins `γ` from
> just **two** points = **two** scalar `Q`-constraints; two quadratics cut a codim-`≤2` (`≈ q^{d−2}`-point) subvariety of
> `K^d`, **not** a singleton for `d ≥ 3`. So the raw two-point forced triangle **cannot pin on `VO^ε`** (`d≥4`) in the
> scheme's own colours — the SAME wall that forced the seal onto the 2-round `χ(det G₂)` pair form, and exactly why the
> successful discharge is the **dimension-1 line** and the rainbow variant "cannot reach the rank-3 SRG core". **Landed**
> (`ChainDescent/ScratchDominatorForms.lean`, axiom-clean): `polar_eq_qSub` + `spanning_exactQ_determines` — the **full-base**
> pinning (exact-`Q` profile to a `span=⊤` base determines the vertex; the affine isometry scheme's `huniq` at a spanning
> base, reusing §1's `spanning_sameExactGram_determines`) + `twoPoint_insufficient_unless_spans` (the two-point premise is
> the non-spanning projection). **VERDICT:** δ′ **restructures** the crux as an inductive closure but does **not** dodge it —
> on `VO^ε` it needs either (a) the **extension** relations (`reachesRigidOrCameron_viaExtensionDominatorClosure`, carries
> `hcatch`) or (b) a **multi-point** pinning engine (full-base, landed here); both reduce to the **same** WL-orbit defect as
> the crux. What δ′ buys: the full-base pinning is unconditional geometry, isolating the open content to the **fusion**
> (rank-3 similitude vs exact `Q`-value) — the 2-round count the seal handles. **Next δ′ move (if pursued):** either extend
> the engine with a multi-point step (turns `spanning_exactQ_determines` into a real closure on the isometry scheme, then
> tackle fusion), or run the `χ(det G₂)`-at-`d+1`-frame probe (shared with ITEM A). **Fallbacks:** Skresanov 2-closure,
> `EdgeGeneratesFromSet`. Gauss `χ(det G₂)` proves the stronger `bᵢ=1` (overshoot; reserve). If all stall → Route C (§7).
>
> **★ BOUNDED-MULTIPLICITY REVIVAL — NON-VACUITY CHECK PASSED (2026-07-01, `forced_triangle_mult.py`).** The δ′ *singleton*
> (`interNum=1`) target is walled (2-pt cut → `q^{d−2}` POINTS). But the recovery target only needs the *orbit* multiplicity
> `bᵢ = #{Stab(S)-orbits in the WL cell} ≤ poly(q)` — and the wall bounds POINTS, not orbits (the `q^{d−2}` filter points form
> few orbits under the large residual stabiliser). **Measured** (`bᵢ` = max orbits-per-cell over greedy-anisotropic base
> levels, `VO^ε` sound isoClass model, `q∈{3,5,7}`, `d∈{4,6}`, both `ε`): **`bᵢ ≤ q(q−1)/2 = Θ(q²)` — POLY(q), and it
> occurs at EXACTLY ONE level** (`|S|=2`, the span-dim-`0→1` transition); `bᵢ=1` at every other level (`CellsAreOrbits`
> *holds* at span-dim `0,1` and `≥2`, failing only at span-dim-1). **`d`-uniform** (`q=3`: identical `B=3` at `d=4` and `d=6`).
> This is the SAME defect the WallKernel refutation saw (orbits `12,30,56` vs cells `10,11,11` at `|S|=2`) — now seen to
> **recover at `|S|=3`**. **Consequences:** (i) the crux `B ≤ poly(q)` is **non-vacuous and empirically poly** — `bᵢ ≤ q(q−1)/2`;
> (ii) branching is **concentrated at one level**, so `L` (branchDepth = #`≥2`-forks) is `O(1)` here, and Phase 1's *existing*
> `leaves ≤ Bᴸ` gives `leaves ≤ q(q−1)/2 = poly(n)` directly; (iii) the interNum-level δ′ stays walled — the useful
> bounded-multiplicity lives at the **orbit** level (Phase 1's `BoundedBranchingDisposition`). So the open crux SHARPENS from
> "`B ≤ poly(q)`?" to the concrete, probe-backed **"`bᵢ ≤ q(q−1)/2`, concentrated at span-dim-1"**. Vacuity-trap caution
> (`BoundedConfusionMultiplicity` steer): the bound is a *non-trivial* `Θ(q²)` (not 0, not `q^{|S|}`), and the full per-level
> distribution is reported — not a tuned pass/fail.
>
> **★ SPAN-DIM-1 BOUND `bᵢ ≤ q²` — PROVEN (2026-07-01, the provable half).** Landed `ScratchSpanDimBound.lean` (axiom-clean):
> `stabOrbit_cover_card_le_line` — if `span S ⊆ K·a` (finrank ≤ 1) then, mod Witt, the space is covered by `≤ |K|² = q²`
> `Stab(S)`-orbit reps, so `bᵢ ≤ q²` at any span-dim-1 base, **unconditionally**. Mechanism (`polar_eq_of_mem_span_singleton`):
> `polar Q t` is linear, so on the line `polar Q t s = c_s·polar Q t a` — the whole `S`-profile collapses to
> `(Q t, polar Q t a) ∈ K²`, sharpening Phase 2's `|K|^{|S|+1}` to `|K|^{finrank(span S)+1}` at `finrank=1`. Upper-bounds the
> probe's `q(q−1)/2 < q²`. This makes the *branching-level factor* poly with no open hypothesis.
>
> **REMAINING HALF — the concentration (open, but sharply located + empirically TRUE).** `leaves = ∏bᵢ`; the span-dim-1 bound
> caps the one big factor. Poly needs branching **confined** to `O(1)` such levels, i.e. **`bᵢ = 1` at span-dim `≥ 2`**
> (`CellsAreOrbits` off span-dim-1). Key reframe: this is a **WallKernel** statement, but at span-dim `≥ 2` where the probe
> shows it **HOLDS** — *not* the span-dim-1 instance that was refuted (that refutation *is* the `q²` defect this bound covers).
> So the open content is a **positive, empirically-true** WallKernel-at-span-dim-`≥2`, the WL-orbit defect located where it is
> true. Two attack routes: **(A)** prove `bᵢ=1` at span-dim `≥ 2` directly (2 independent anisotropic directions + 1-WL
> iteration recover exact-Gram — candidate lever: the seal's 2-round `χ(det G₂)` observable, does it discretise at span-dim 2?);
> **(B)** `L = O(1)` structurally — branching ⟹ span-dim `≤ 1` (route A contrapositive), and span grows past dim 1 within
> `O(1)` forks (`nontrivialForks_le_finrank`, `ScratchBranchDepth`) ⟹ `O(1)` branching levels; needs the Phase-4 descent model.
> Both routes reduce to route A's positive WallKernel-at-span-dim-`≥2`. **Viability:** strictly better-posed than the generic
> crux (located + true + `q²`-bounded elsewhere); if A stalls, the `χ(det G₂)`@span-dim-2 probe is the cheap next test.
>
> **★ ROUTE A ATTEMPTED (2026-07-01) — direct proof STALLS, but the DIRECTION is CRACKABLE.** Scoping verdict: route A is
> the **multi-base recovery** `JointProfileRecoversAt` at `|T|≥2` — the open `s(C)` content in general (`cellsAreOrbits`
> single-base is free, `cellsAreOrbits_schemeAdj_singleton`; multi-base is the gap). The probe's non-monotone pattern
> confirms it: recovery holds at `|T|=1`, **fails at `|T|=2`** (span-dim-1, the `q²` defect), **holds at `|T|≥3`**
> (span-dim-2). The seal discharges this only **per-instance via `decide`/Gauss** (`IsotropySeparatesAtBase` →
> `sigF_injective`, ~20s/instance, overshooting to *discreteness*), not as a general family bound; and the geometric
> shortcut (isoClass→exact) hits the **Gauss-counting wall** (isoClass is 3-valued; exact recovery needs the count). So no
> elementary proof. **BUT the direction check `recovery_depth_probe.py` is strongly positive:** at a span-dim-2 base, 1-WL
> recovers the orbits in **`r* ∈ {3,4}` rounds** (VO⁻:3, VO⁺:4) — **flat in `d`** (q=3: `r*=3` at both `d=4,6`) and in `q`;
> and the orbit count there is `q²(q+1) = Θ(q³)`, **d-uniform**. So route A is a **bounded-round (`O(1)`), d-uniform,
> `Θ(q³)`-orbit** recovery — the *crackable* verdict (had `r*` grown with `d`, it would be the frontier). **The real proof
> path:** instantiate the seal's **2-round pair-form `χ(det G₂)`** count-separation at a span-dim-2 base as a **d-uniform
> family** argument (not per-instance `decide`) — the `r*`-flat + orbit-count-d-uniform evidence says the pair-form should
> separate the `Θ(q³)` orbits uniformly in `d`. Reuses `PairForm`/`GaussCount`. **Route B note:** B (`L=O(1)`) is NOT
> independent — it needs A's "branching ⟹ span-dim ≤ 1" to confine forks; given A, a span-dim-1 fork into a non-trivial
> orbit *grows* span to dim-2 (`span_lt_span_insert_of_stabOrbit_ne`), so the span-dim-1 phase contributes `O(1)` branching
> levels ⟹ `L=O(1)`. So A is the single gate; B is its cheap corollary.
>
> **▶ PLAN OF ATTACK — the span-dim-2 family instantiation (STARTED 2026-07-01, `ScratchSpanDim2Recovery.lean`).** Target:
> `bᵢ=1` at a span-dim-2 anisotropic base `S ⊇ {0,a,b}` for `VO^ε`, all `d` — i.e. the 2-round isotropy-count profile at `S`
> separates the `Stab(S)`-orbits (= exact-Gram classes `(Q v, polar v a, polar v b)`). NOT a plug-in of the seal's
> `IsotropySeparatesAtBase` (that targets *discreteness* at a *spanning* frame via per-instance `decide`); this is
> orbit-separation at a *bounded* base, `d`-uniform. Steps: **(1)** state the target geometrically + the count-separation
> predicate `SpanDim2CountSeparates` (2-round isotropy-count profile ⟹ same exact-Gram); **(2)** soundness (orbit ⟹ same
> count) is FREE (any graph-invariant is orbit-constant); **(3)** reduce `bᵢ=1` to `SpanDim2CountSeparates` via the cell↔count
> bridge (`twoRoundProfileCount_eq`/`discrete_of_twoRoundRelationSeparates` restricted to orbit-level); **(4)** the `d`-uniform
> **key lever** — the orthogonal complement `⟨a,b⟩^⊥` (dim `d−2`) contributes a **`v`-independent Gauss factor** to every
> count, so it *cancels* in the separation comparison, reducing the count to a **fixed `d`-independent** local count over
> `⟨a,b⟩` (⟹ decidable / uniform character sum). This complement-factoring is the crux that makes it a *family* (not
> per-instance) argument, and is exactly what the `r*`-flat / orbit-count-`d`-uniform probe predicts. **(5)** the residual local
> count-separation is the named Gauss core (`PairForm`/`GaussCount`), now `d`-independent.
>
> **INCREMENT 1 — LANDED (2026-07-01, `ScratchSpanDim2Recovery.lean`, axiom-clean).** The reduction scaffold (steps 1–3),
> generalising `ScratchWallKernel`'s observable pattern to a function-valued `obs : V → β`: `ObsInvariant` (obs is
> `Stab(S)`-invariant) + `stabOrbit_imp_obsEq` (soundness, FREE) + capstone **`obsEq_iff_stabOrbit`** (`ObsInvariant` +
> `WallKernelFor obs` + Witt ⟹ **`obs t = obs t' ↔ StabOrbit`**, i.e. `bᵢ=1`), bundled as `SpanDim2Recovers`. So route A =
> `WallKernelFor (fun t t' => obs t = obs t') Q ↑S` for `obs` = the 2-round count — soundness and the reduction are proved;
> the Gauss core is the single carried predicate.
>
> **INCREMENT 2 — the complement-factoring. ★ MAJOR RE-SCOPE (2026-07-01): the count-factoring is ALREADY BUILT (for the
> quasipoly seal); the `d`-cancellation is now HARVESTED, and the genuine remaining route-A content is RELOCATED to the
> iterated/sub-config observable.** Checking what exists (`IsotropicIncidenceCountK`) revealed the seal already did the
> `V = U ⊕ Uᗮ` split (`reduction_to_levelsetK`) and the closed-form count (`levelset_count_eqK`:
> `count·|K|^{m+1} = |V| + ∑_{s≠0}∑_ρ ψ(−sc)·(ψ(−s⁻¹·Q(∑ρa))·∑_x ψ(s·Q x))`), where the **`d`-dependence is exactly the
> two config-independent factors `|V|=|K|^d` and the global Gauss sum `∑_x ψ(s·Q x)`**, and the config-dependence collapses
> — via `configGaussSum_eq_detK` — to the single scalar **`χ(det G_config)`**. So the complement-factoring I was about to
> build is done. **LANDED (2026-07-01):**
> - `ScratchComplementFactor.lean` (axiom-clean) — the abstract-`V` orthogonal split (`map_sub_split`:
>   `Q((v₁+v₂)−(u₁+u₂)) = Q(v₁−u₁)+Q(v₂−u₂)`, + `exists_decomp_of_isCompl`); the general-`V` bridge to the geometric
>   `StabOrbit`/`SameExactGram` world (the seal's `map_add_of_polar_zeroK` is the `Fin d → K` instance).
> - `ScratchComplementFactorK.lean` (axiom-clean) — **`levelset_count_factors_through_chiDet`**: the `d`-cancellation,
>   reused: two configs with the same `χ(det G_config)` give the **same** (scaled) level-set count at every level `c`,
>   **uniformly in `d`** (the `|V|` and global-Gauss `d`-factors are common ⟹ cancel; config enters only via `χ(det)`).
> - `ScratchJointCountInvariant.lean` (axiom-clean) — **the FREE half for the concrete observable.** The seal's
>   `jointIsoCountK` is `Stab(S₀)`-invariant: `isoClassK_similitude` (a similitude preserves the isotropy class,
>   `Q(gw)=μ·Qw`, `μ≠0`) ⟹ `jointIsoCountK_similitude_fix` (a base-fixing similitude preserves the joint count, via the
>   bijection `z ↦ g z`) ⟹ **`obsInvariant_jointCountProfile`** (`ObsInvariant (jointCountProfile Q S₀) Q ↑S₀` for the
>   sub-config profile `S' ⊆ S₀`). So `obsEq_iff_stabOrbit` now reduces route A at a span-dim-2 base `S₀` to the **single
>   open predicate `WallKernelFor (jointCountProfile Q S₀ ·) Q ↑S₀`** (+ carried Witt) — soundness fully discharged.
>
> **★ THE RE-SCOPE (the honest consequence — corrects the "one count ⟹ exact Gram" framing above).** Because a single
> isotropy count is only **`χ(det)`-valued** (2-valued in the config — this is precisely why the *seal* needed a *matching*
> of many pairs + `c₀≤¾` union to reach frame discreteness), route A's *exact-Gram* recovery `(Q u, polar u a, polar u b)`
> at a span-dim-2 base **cannot come from one count**. It needs (a) the count **profile over the sub-configs** `S ⊆ {0,a,b}`
> (= `ZProfileSeparatesK` at the small base `{a,b}`, targeting the exact Gram to `{a,b}` rather than the full frame), and
> (b) the **iterated** observable — the `χ(det G₂)` 2-WL fixpoint, matching the probe's `r*∈{3,4}` rounds — not the single
> round. The single-round content is now pinned + `d`-cancelled; **the remaining route-A content = the iteration's
> `d`-uniform convergence** (the probe says `r*` is flat in `d`, so crackable).
>
> **★ THE EXACT-GRAM RECOVERY PLAN (2026-07-01) — split into a tractable geometric CORE + the iteration SEAM.** The
> `WallKernelFor` target factors:
> - **(I) Geometric recovery core — LANDED (`ScratchSpanDim2Geom.exactGram_of_sameWProfile`, axiom-clean).** The isoClass
>   profile of `u` over the *whole plane* `W = span{a,b}` determines `(Q u, polar u a, polar u b)`, `d`-**independently**,
>   with **no Gauss/Witt/iteration**. Mechanism: the difference `Q(u−w) − Q(u'−w) = polar Q (u'−u) w + (Qu − Qu')` is
>   **affine** in `w` (`norm_diff_affine` — the quadratic parts cancel); on the common isotropic set `Z = {w∈W : Q(u−w)=0}`
>   it is `0`; if `Z` **affinely spans** `W` (carried hyp `hspan`), the affine functional `polar Q (u'−u) ·` vanishes on all
>   of `W` ⟹ `polar u a = polar u' a`, `polar u b = polar u' b`, `Q u = Q u'`. So the information is provably present at
>   span-dim-2. Carries only `hspan` (the conic affinely spans `W`). NB: needs **no** `W`-nondegeneracy (the affine
>   argument is direct).
>   - **`hspan` DISCHARGE — combinatorial half + the conic count both LANDED (axiom-clean).**
>     - **Combinatorial bridge** (`ScratchSpanDim2Span.hspan_of_two_indep`): `hspan` follows from "`Z` has **three
>       non-collinear points**" (two independent difference vectors span the 2-dim `W`) — form-independent linear algebra.
>     - **The conic count** (`ScratchConicCount`, done **ELEMENTARILY — no Gauss sums**): the crux character sum
>       **`sum_quadraticChar_sq_sub`** `∑ₓ χ(x²−a) = −1` (`a≠0`), proved via `quadraticChar_card_sqrts`
>       (`#{z:z²=b}=χ(b)+1`) + the hyperbola bijection `(x,z)↦(x−z,x+z)` (`#{x²−z²=a} = #{uv=a} = q−1`); then
>       **`card_binary_form`** `#{(x,y) : w₁x²+w₂y²=c} = q − χ(−w₁w₂⁻¹)` (`= q − ε`, `ε=±1`) for `c≠0`. This *replaces* the
>       planned `card_quadForm_eq`/`gaussSum_sq` route — far cleaner.
>     - **Both-nonzero solution — LANDED (2026-07-01, `ScratchConicCount`, axiom-clean).** `card_sq_eq_le_two`
>       (`#{y:y²=k}≤2`) + **`exists_both_nonzero_solution`**: for `q=|F|≥7` the count `q−ε≥6` exceeds the `≤4` axis
>       solutions, so `∃ (x₀,y₀)` with `w₁x₀²+w₂y₀²=c` and `x₀≠0,y₀≠0`. This is the analytic heart; the three explicit
>       non-collinear solutions are `(±x₀,±y₀)` (differences `(−2x₀,0),(0,−2y₀)` independent, `2x₀y₀≠0`).
>     - **A1 — (I) interface WEAKENED (2026-07-01, `ScratchSpanDim2Geom`, axiom-clean).** `exactGram_of_sameWProfile`'s
>       hypothesis is now the one-directional `∀w∈W, Q(u−w)=0 → Q(u'−w)=0` (the proof only ever used `.mp`), so (II) need
>       only propagate *one* isotropic-containment, not full-plane agreement.
>     - **Assembly + transport — LANDED (2026-07-01, `ScratchConicSpan`, axiom-clean).** `map_ortho_comb`
>       (`Q(x•a+y•b)=x²Qa+y²Qb`) + `indep_smul_pair` + **`exists_three_indep_levelset`** (three non-collinear points of the
>       plane `Q`-level set `{v:Qv=c}` from the both-nonzero solution) + the transport capstone **`hspan_of_conic`**: given
>       `a,b` orthogonal anisotropic and a decomposition `u = u_W + u_⊥` (`u_W∈W=span{a,b}`, `u_⊥∈Wᗮ`) with `Q u_⊥ ≠ 0`
>       (`c=−Q u_⊥ ≠ 0`) and `q≥7`, `Z(u)={w∈W:Q(u−w)=0}` **affinely spans `W`** — i.e. the `hspan` hypothesis of
>       `exactGram_of_sameWProfile` holds. Level identity `Q(u−w)=Q(u_W−w)+Q u_⊥` via `map_sub_split`; `Z(u)=u_W−L_c`.
>     - **(i-a) Decomposition-discharge — LANDED (2026-07-01, `ScratchConicSpan`, axiom-clean).** `exists_orthogonal_decomp`
>       (every `u` splits `u = u_W + u_⊥`, `u_W∈W`, `u_⊥∈Wᗮ`, via the *explicit projection* `u_W = (polar Q u a/polar Q a a)•a
>       + (polar Q u b/polar Q b b)•b` — no `IsCompl`/restrict machinery) + the bare-vertex capstone **`hspan_or_singleton`**:
>       for any `u`, **either** the singleton locus (`Q(u−u_W)=0`, `u−u_W∈Wᗮ`) **or** `Z(u)` spans `W` (`hspan`). So (I)
>       applies to a bare vertex, with the case split routed exactly to where (ii) attaches.
>     - **(ii) Singleton sub-case — SCOPED + core LANDED (2026-07-01, `ScratchConicSpan`, axiom-clean).** NOT a gap — it
>       recovers *more easily* than the generic case. In the singleton locus (`Q u_⊥ = 0`) the exact Gram to `{a,b}`
>       **collapses onto `u_W`**: `Q u = Q u_W`, `polar Q u a = polar Q u_W a` (complement isotropic + polar-orthogonal to
>       `W`). Core **`exactGram_of_isotropic_complement`**: two singleton-locus vertices with the same `W`-component
>       (`u_W = u'_W`) have the same exact Gram — no spanning. **Remaining (ii)-specific:** the small bridge `u_W = u'_W`
>       from `hprof` + singleton (`u_W ∈ Z(u')` by `hprof`, and `Z(u') = {u'_W}` when the plane form is anisotropic — a
>       `χ(−QaQb⁻¹)=−1` conic fact, reuses `ScratchConicCount`); then the shared (II) seam (observable ⟹ `hprof`), same
>       base-augmentation content as the generic branch. So (ii) is fully parallel, `q∈{3,5}` tail folds in.
> - **(II) The observable → geometric-profile SEAM. [SUPERSEDED 2026-07-02 — largely BUILT; see §9.7 for the current
>   state.]** The chosen path was base-augmentation (sub-option (b)): Step B (`ScratchBaseAug`) discharged `IsoSetEq ⟹
>   SameExactGram` (both branches, incl. the (ii)-glue), the Step C reduction (`ScratchPlanePin`) reduced to "1-WL refines
>   `zSet`", and the Route α sub-step (`ScratchPlaneSep`) reduced that to the single open predicate
>   `ChiProfileSeparatesPlane` (the `d`-independent 2-dim χ-accumulation). What remains: prove `ChiProfileSeparatesPlane`
>   + the 1-WL-computability wiring. The `r*∈{3,4}` fixpoint is now understood as this 2-dim accumulation (§9.7).
 **NEXT (updated 2026-07-01):** A1 (weaken (I)) ✅ + the both-nonzero solution (`exists_both_nonzero_solution`) ✅ are
> LANDED. Remaining in A2 = the `W`-level **assembly** (3 non-collinear points via `exists_orthoAnisotropic_basis`) +
> **transport** (`u=u_W+u_⊥` decomposition, level identity via `map_sub_split`) + the `c=0`-anisotropic singleton sub-case.
> Then Step B (base-augmentation reduction `Obs_aug ⟹ SameExactGram`) + attack (II) "C^∞ pins W" (the plane-pinning closure).
>
> **▶ THE MODEL SEAM (Phase 4, applies to both items).** The geometric work (`StabOrbit`/`SameExactGram` over
> `QuadraticForm K V`, where `ScratchBranchingBound` + the base cases live) connects to Phase 1's *abstract*
> `BoundedBranchingDisposition` (over `AdjMatrix n`/`OrbitPartition`) via the seal's `affineE` endpoint transport — the same
> bridge the seal uses. Deferred to Phase 4 assembly; carried as the `CertifiedBoundedTree` realisation fields for now.
>
> **Verify the landed substrate (all axiom-clean, NOT in `build.sh`; `bash scripts/build.sh` for the in-build banked seal).**
> The **round-3 crux chain (Piece 1a→1c(iii)) is the frontier** — build it with
> `lake build ChainDescent.ScratchGramStratCount ChainDescent.ScratchGramStratCharSum ChainDescent.ScratchGramStratEval ChainDescent.ScratchGramStratInvert ChainDescent.ScratchGramStratOrbit`.
> Full list — `lake build` the twenty-five scratch modules — Phase 1 `ScratchBoundedBranching` (`leaves≤Bᴸ`), Phase 2 `ScratchBranchingBound`
> (`#orbits≤|K|^{|S|+1}`), `ScratchBranchDepth` (`L=O(d)` core + span-growth), `ScratchDominatorForms` (δ′ walled +
> `spanning_exactQ_determines`), `ScratchBoundedMultLeaves` (`leaves_le_prod` per-level bound), `ScratchSpanDimBound`
> (`bᵢ≤q²` @span-dim-1, PROVEN), `ScratchSpanDim2Recovery` (route-A scaffold: `bᵢ=1` ⟸ `WallKernelFor(2-round count)`),
> `ScratchComplementFactor` (abstract-`V` orthogonal split `map_sub_split`), `ScratchComplementFactorK`
> (`levelset_count_factors_through_chiDet` — the `d`-cancellation, reusing the seal's `levelset_count_eqK`/`configGaussSum_eq_detK`),
> `ScratchJointCountInvariant` (`obsInvariant_jointCountProfile` — soundness of the seal's `jointIsoCountK` sub-config profile),
> `ScratchSpanDim2Geom` (`exactGram_of_sameWProfile` — the geometric recovery CORE: isoClass profile over `W=span{a,b}` ⟹ exact Gram, `d`-independent),
> `ScratchSpanDim2Span` (`hspan_of_two_indep` — the `hspan` combinatorial bridge: three non-collinear isotropic points ⟹ `hspan`),
> `ScratchConicCount` (`sum_quadraticChar_sq_sub` `∑ₓχ(x²−a)=−1` + `card_binary_form` `#{w₁x²+w₂y²=c}=q−ε` — the conic count, elementary, no Gauss; + `exists_both_nonzero_solution` — count ⟹ both-nonzero solution, `q≥7`),
> `ScratchConicSpan` (`exists_three_indep_levelset` — three non-collinear plane level-set points; `hspan_of_conic` — the A2 transport capstone: `Z(u)` spans `W` for generic `c≠0`; `exists_orthogonal_decomp` + `hspan_or_singleton` — i-a bare-vertex dichotomy singleton-∨-hspan; `exactGram_of_isotropic_complement` — ii singleton-locus recovery core),
> `ScratchBaseAug` (Step B — `IsoSetEq` observable + `sameExactGram_of_isoSetEq_generic`/`_singleton_anis`: `IsoSetEq ⟹ SameExactGram` both branches, no counting; `eq_wComp_of_isotropic_of_anisotropic` — the derived (ii)-glue),
> `ScratchPlanePin` (Step C reduction — `zSet` observable + `zSet_invariant` + `wallKernel_zSet_anisotropic` + `zSetEq_iff_stabOrbit_anisotropic`: `bᵢ=1` for `zSet`, reducing route A to "1-WL refines `zSet`"),
> `ScratchPlaneSep` (Step C Route α sub-step — `plane_count_sep` [the seal's per-pair lever fires for plane points] + `ChiProfileSeparatesPlane` [the isolated open accumulation kernel] + `count_profile_separates_of_kernel` [kernel ⟹ count profile injective on `W`]),
> `ScratchPlanePinInduction` (Step C inductive reformulation — `SeparatedBy`/`pinStep`/`pinIter`/`PinClosure`/`PlanePinnable` [the pinning closure = the corrected, *inductive* accumulation target, replacing the one-shot `ChiProfileSeparatesPlane`] + `chiProfileSeparatesPlane_of_pinnable`/`count_profile_separates_of_pinnable` [closure ⟹ one-shot ⟹ count profile injective on `W`; anchors reachable-in-order, which the wiring needs]),
> `ScratchWLWiring` (Step C 1-WL-computability wiring, SUPERSEDED-but-subsumed by class counts — Core SURVIVES: `PinsPlane`/`ReadsSingletonIsotropy` ⟹ `refines_zSet_of_pinsPlane` ⟹ `colorEq_iff_stabOrbit` [C pins W ⟹ `bᵢ=1`]; Bridge `pinsPlane_of_planePinnable` uses the refuted singleton mechanism — see §9.7 correction),
> `ScratchWLClassCounts` (Step C CORRECTED observable — `iso3`/`classCount`/`SameClassCounts`/`IsWLStable` + **`ClassCountsSeparateGram`** [= `WallKernelFor (SameClassCounts C Q)`, the class-count/iterated observable, the TRUE frontier replacing the refuted `PlanePinnable`] + `wallKernel_of_wlStable`/`colorEq_iff_stabOrbit` [⟹ `bᵢ=1`] + `sameClassCounts_of_stabOrbit` [soundness FREE]),
> `ScratchGramStratCount` (Step C Piece 1a — the round-3 observable `gramK`/`gramStratCount`/`SameGramStratCounts` + soundness `sameGramStratCounts_of_stabOrbit` [via `gramK_isometry`/`polar_isometry`] + the crux `GramCountsRecoverOrbit` [K-non-degeneracy: profile ⟹ orbit, targets orbit DIRECTLY not `SameExactGram`+Witt] + `gramCountsEq_iff_stabOrbit` [⟹ `bᵢ=1` modulo crux]; `gramStratCount` now genuine-`DecidableEq` not `Classical`),
> `ScratchGramStratCharSum` (Step C Piece 1b — the character-sum identity: `gramStratCount_charsum` [raw four-constraint Fourier expansion via `countk_eq_sum_charsum`] + `gramStrat_inner_normalize` [inner z-exponent = D1 normal form `(r₀+r₃)Qz+polar z (r₁•a+r₂•b−r₃•u)+r₃Qu`] + `gramStratCount_charsum_normalized` [combined]; pure `GaussCount` assembly; the count↔`gramStratCount` bridge uses `convert`+`ext` to absorb the `∀(j:Fin 4)`-instance mismatch),
> `ScratchGramStratEval` (Step C Piece 1c(i) — inner z-sum evaluated: `gramStrat_inner_eval_ne` [bulk `ρ=r₀+r₃≠0`, D1 `sum_addChar_quadForm_linear`: `=ψ(r₃Qu)·ψ(−ρ⁻¹Q(r₁a+r₂b−r₃u))·∑ψ(ρQz)`] + `gramStrat_inner_eval_zero` [boundary `ρ=0`, `sum_addChar_linearMap`: `=ψ(r₃Qu)·(|V| if `polarBilin.flip wᵣ=0` else 0)`]),
> `ScratchGramStratInvert` (Step C Piece 1c(ii) ✅ COMPLETE — `gsum_orthogonality` [`K³` char orthogonality `∑_{g:K×K×K} ψ(⟨t,g⟩)=|K|³·𝟙[t=0]` via coordinatewise `AddChar.sum_mulShift`; collapse each coord sum with explicit `have`s since `← mul_sum` fails in `simp_rw`] + `innerZ` [opaque def of the surviving inner z-sum, so `mul_sum` can't distribute into it] + `gramStrat_transform_eval` [the evaluated g-transform: `(∑_g ψ(⟨s,g⟩)·gramStratCount u g)·|K|⁴ = ∑_r 𝟙[r₀₁₂=s]·|K|³·innerZ_u(r)`] + `sameGramStratCounts_transform` [SameGramStratCounts ⟹ equal innerZ fibre sums ∀s]),
> `ScratchGramStratOrbit` (Step C Piece 1c(iii) ✅ REDUCTION — the crux reduced to two named predicates, **both carrying a `GoodBase Q a b` antecedent** [`a,b` orth aniso + `(2:K)≠0` + `Q.polarBilin.Nondegenerate`] so they are TRUE/dischargeable, NOT the FALSE bare `∀ Q a b` forms: `GramCountsRecoverGram` [GENUINELY OPEN Gauss, must be PROVED, probe-true: GoodBase → SameGramStratCounts ⟹ SameExactGram + span-flag] + `RefinedWittExtends` [CITATION of Witt's theorem, acceptable-to-carry: GoodBase → SameExactGram + span-flag ⟹ StabOrbit, Witt on nondeg W^⊥] + `gramCountsRecoverOrbit_of`/`gramCountsEq_iff_stabOrbit_refined` [⟹ bᵢ=1 mod the two] + `stabOrbit_imp_span_iff` [flag orbit-sound ⟹ RefinedWittExtends is the tight converse]).
> `ScratchGramStratGauss` (Step C Piece 1c — the DISCHARGE CORE, factorization: `countHat` [g-Fourier of the count] + `isoConeSum` [`∑_{w:Qw=0} ψ(polar w y)`, the classical cone sum] + `countHat_eq_isoSum` [`countHat u t = ∑_{z:Q(u−z)=0} ψ(⟨t,gramK z⟩)`] + **`countHat_factor`** [`= ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)`; Gram in the phase] + `countHat_eq_of_sameGramStratCounts` [trivial]; needs no Gauss brick/primitivity/IsDomain — any CommRing/ψ),
> `ScratchGramStratGaussReduce` (Step C Piece 1c — the REDUCTION, `hψ` DISCHARGED: `gramK_eq_iff_sameExactGram` + **`IsoConeSumSeparatesGram`** [the isolated cone non-degeneracy, GoodBase+even-dim antecedent, purely `isoConeSum`] + `gramCountsRecoverGram_of_isoConeSep` [constructs primitive char via `AddChar.FiniteField.primitiveChar K ℚ` ⟹ `GramCountsRecoverGram` carrying NO `hψ`] + `gramCountsEq_iff_stabOrbit_of_isoConeSep` [⟹ `bᵢ=1` mod `IsoConeSumSeparatesGram` + `RefinedWittExtends`]).
> `ScratchGramStratConeEval` (Step C Piece 1c — the CLOSED FORM: **`isoConeSum_eval_even`** [even dim ⟹ scale-invariant Gauss sum `G(s)=G₁` ⟹ `|K|·isoConeSum(y)=|V|𝟙[y=0]+G₁(|K|𝟙[Qy=0]−1)`; via `𝟙[Qw=0]=|K|⁻¹∑ψ(sQw)`, split s=0 [`sum_addChar_linearMap`] / s≠0 [Brick D1 + C-scale `sum_addChar_quadForm_smul`], reindex `s↦−s⁻¹` involution] + **`isoConeSum_ne_zero`** [nowhere-zero at even dim: `G₁≠0` + integer factor `∈{|K|−1,−1}`] + `associated_separatingLeft_of_polarBilin_nondeg`).
> `ScratchGramStratConeSep` (Step C Piece 1c — **`IsoConeSumSeparatesGram` DISCHARGED**: **`isoConeSumSeparatesGram`** [PROVED: off-diagonal `polar u a/b` + diagonal `Qu` from `isoConeSum_ne_zero`+primitivity (no value needed); flag from closed form once phases match, `𝟙[y_u=0]=𝟙[y_u'=0]` at `t₀=1`] + capstone **`gramCountsEq_iff_stabOrbit_wittOnly`** [`bᵢ=1` modulo ONLY the Witt citation `RefinedWittExtends`, axiom-clean, `hψ` constructed]).
> `ScratchGramStratWLBridge` (Step C **Piece 2 — the WL bridge**: `ColorRefinesGramK` [colouring ≥ as fine as `gramK`, necessary residual] + **`sameGramStratCounts_of_sameClassCounts`** [`ColorRefinesGramK`+`SameClassCounts` ⟹ `SameGramStratCounts` via `gramStratCount u g=∑_{g-colours}(classCount 0+classCount 1)`, `Q(u−z)=0⟺iso3∈{0,1}`, `card_eq_sum_card_fiberwise`] + assembly **`colorEq_iff_stabOrbit_wittOnly`** [`C u=C u' ↔ StabOrbit`, `bᵢ=1`, modulo `{ColorRefinesGramK, IsWLStable, ObsInvariant, RefinedWittExtends}`]).
> **★ CORRECTION recorded (do not re-walk):** the "Fourier-invert fibre sums; bulk recovers Gram" attack is EMPTY (the r₃-marginal is trivially `|K|`·count-transform); the elementary first moment fails in char `p` (`q|#{Qw=0}`). Gram lives in the phase ⟹ ℂ/character route necessary.
> **Probes (`GraphCanonizationProofs/`):** `pin_probe.py` (REFUTES the singleton closure: stalls at 3/`q²` for `q≥5`; plane 1-WL stalls at 4 classes), `round2_probe.py`/`round2_closedform.py`/`round3_probe.py` (round-structure: r2=seal `jointIsoCountK`, r3=orbits form-indep), `forced_triangle_mult.py` (non-vacuity: `bᵢ≤q(q−1)/2`), `recovery_depth_probe.py`
> (route-A direction: `r*∈{3,4}` d-uniform). Both memory-light; run under `ulimit -v` (WL is `O(n²)`, OOM risk at large `n`).
> **THE LIVE STEP (updated 2026-07-02):** the round-3 crux chain (Piece 1a→1c(iii)) is BUILT and reduces `bᵢ=1` to two
> named predicates (see the CURRENT FRONTIER paragraph at the top of this STATUS + the section plan). **The single open
> Gauss lemma is `ScratchGramStratOrbit.GramCountsRecoverGram`** (`SameGramStratCounts ⟹ SameExactGram + span-flag`); prove
> it from `ScratchGramStratInvert.sameGramStratCounts_transform` (equal `innerZ` fibre sums) + the inner-sum evaluations
> `ScratchGramStratEval.gramStrat_inner_eval_ne`/`_zero` (bulk ⟹ primal Gram, boundary ⟹ span-flag), and instantiate a
> primitive additive character (deferred, as the seal defers it). The other predicate `RefinedWittExtends` (known-true, Witt
> on nondeg `W^⊥`) stays carried. **[The pre-orbit-direct "sub-config `ZProfileSeparatesK` / `ClassCountsSeparateGram`"
> framing is SUPERSEDED — see the CURRENT FRONTIER note.]**
> **Then read:** this STATUS + §1 (cost model) + §2c (strength ladder) + §4 (the open core) + §6 (phased plan) + §8 (ITEM A/B).
> **════════ END PICK-UP ════════**
- **SEAL endpoints (banked at quasipoly; reference):** `reachesRigidOrCameron_viaIsotropySeparates_wittFree` (idx 1248,
  input `IsotropySeparatesAtBase Q T` idx 1240) and the abstract twin `reachesRigidOrCameron_viaAffineFormScheme` (idx 1207,
  input `RelCountsDetermineOrbit` idx 1203). The in-build seal is `AffinePolarSeal.reachesRigidOrCameron_affinePolar`.
- **Reusable Lean assets:** `coords_determine` (1211), `relationRefinesIsotropy_similitude` (1247, Witt-free),
  `GaussCount` / `IsotropicIncidenceCount*` / `ObservableCountBridge*` / `PairForm` / `PerAnchorBound`, all field-generic
  (`FieldGeneric*`). **Do NOT build on** the SUPERSEDED frame-locked predicates (§3e).
- **C# canonizer:** `GraphCanonizationProject/ChainDescent.cs` (harvest `:589`, deferral `:251-281`), `CascadeOracle.cs`
  (all-reps), `WarmPartition.cs` (1-WL), `CanonResult.cs` (`CascadeStats` — the `ClassifyStarved` completeness counter).
- **Harness (durable):** `GraphCanonizationProject.Tests/RecoveryReconcileProbe.cs` — runs `VO^ε` through the real canonizer
  in both modes, reports the completeness counters. Run:
  `dotnet test GraphCanonizationProject.Tests/*.csproj --filter "FullyQualifiedName~RecoveryReconcileProbe"`.
- **Crackability probes (information-is-there evidence):** `GraphCanonizationProofs/wall_*.py` (documented in
  `chain-descent-cellsareorbits-route.md` §6).
- **Forms-graph plan (seal/quasipoly build + Routes A/B/C arc):** `chain-descent-formsgraph-wldim-plan.md` STATUS + §1 item 1.
- **Modulo set / what's left map:** `chain-descent-remaining-work.md` §3a. **Demoted WL-dim route:**
  `chain-descent-cellsareorbits-route.md`. **Cross-session detail:** `[[project_formsgraph_wldim_viability_2026-06-28]]`.

---

## 9. Route A — the plan, and *why it is what it is* (self-contained; a fresh reader reconstructs the reasoning here)

> **Why this section exists.** §8 is a chronological handoff (dated bullets); this section is the **logical** one — the
> architecture, the insights **with their derivations**, and the ordered plan, written so a new reader reaches the same
> conclusions without re-walking the dead ends (chiefly: *why there is no single-round bypass*). Assumes the cost model
> of §1–§4. Everything below is landed axiom-clean `[propext, Classical.choice, Quot.sound]` unless marked OPEN; none is
> in `build.sh`.

### 9.1 The target (what route A must prove)
`bᵢ = 1` at a span-dim-2 anisotropic base `S ⊇ {0,a,b}` (`a,b` orthogonal anisotropic, plane `W = span{a,b}`): the 1-WL
refinement cell equals one `Stab(S)`-orbit. Via the scaffold `ScratchSpanDim2Recovery.obsEq_iff_stabOrbit` this reduces
to **`WallKernelFor Obs`**: `Obs(u) = Obs(u') ⟹ SameExactGram Q {a,b} u u'` — i.e. `Q u = Q u'`, `polar u a = polar u' a`,
`polar u b = polar u' b` — after which the carried Witt extension upgrades `SameExactGram` to same-orbit. `Obs` is
*whatever 1-WL computes* after individualizing `S` (the stable colouring `C^∞`).

### 9.2 The (I)/(II) split
Everything factors through the geometric quantity **`hprof`** = "`u`'s isotropic set in `W` is contained in `u'`'s":
`∀ w∈W, Q(u−w)=0 → Q(u'−w)=0`.
- **(I) geometric core** — `hprof ⟹ SameExactGram`. **LANDED (both branches, §9.4).**
- **(II) the seam** — `Obs(u)=Obs(u') ⟹ hprof`. **OPEN — the sole remaining open math of route A.**

### 9.3 The five insights that fix this architecture (each with its derivation)

**Insight 1 — there is NO single-round bypass; the iteration is mandatory; therefore (I) is on the critical path, not a shortcut to avoid.**
One naturally hopes to read `SameExactGram` straight off a single round — either off the counts (Gauss-direct) or off a
single-round isotropy profile (geometric-direct) — skipping the (I)/(II) machinery. **Both fail for the same reason.**
`ScratchComplementFactorK.levelset_count_factors_through_chiDet` proves a single joint isotropy count depends on the
configuration **only through `χ(det G_config)`**, a **2-valued** quantity. A bounded profile of such counts over the
sub-configs of `{0,a,b}` therefore carries `O(1)` bits, whereas the orbits to be separated number `Θ(q³)` (the
`q²(q+1)` orbit count at span-dim-2, `recovery_depth_probe.py`). The conic count (`ScratchConicCount`) does **not**
rescue this — it counts a level set, it adds no bits to the *observable*. So no single round separates; the information
only appears after WL **iteration** (`r*∈{3,4}` rounds, flat in `d`). **Consequence:** the real fork is *how to obtain
the iterated information*, **not** geometric-vs-Gauss — and (I), which converts the *iterated* profile into the exact
Gram, is the genuine finisher.

**Insight 2 — the plane `W` is orbit-rigid, so `hprof` (the isotropy profile over `W`) is exactly what the iteration should deliver.**
`ScratchBranchDepth.stab_fixes_span`: an `S`-fixing similitude fixes all of `W = span{a,b}` pointwise, so every plane
point is a singleton `Stab(S)`-orbit. The plane is thus legitimately "determinable," and the natural content the WL
iteration propagates is: the rigid plane-colours fold into `u`'s stable colour, i.e. `isoClass(u−w)` becomes known for
`w∈W` — which **is** `hprof`. This is why (I)'s hypothesis is stated over the whole plane.

**Insight 3 — (I) needs *less* than full-plane agreement (so (II) has a smaller target).**
`ScratchSpanDim2Geom.exactGram_of_sameWProfile`'s proof uses `hprof` only via the `.mp` direction and only at points of
`Z(u) = {w∈W : Q(u−w)=0}`. So (A1) the interface was weakened to the one-directional form above. (II) need only propagate
*one* isotropic-containment over the spanning set `Z(u)`.

**Insight 4 — base-augmentation is a proof device that reduces (II) to a `d`-independent plane-pinning and avoids formalizing a `k`-round WL operator — but it does NOT remove the counting engine.**
Define the *augmented single-round* observable `Obs_aug(u) := (isoClass(u−w))_{w∈W}` (individualize the whole plane).
Then **(II-easy)** `Obs_aug(u)=Obs_aug(u') ⟹ hprof` is trivial (`isoClass` determines whether `Q(·)=0`, via
`isoClassK_ne_two_iff`), so (II-easy) + (I) gives `WallKernelFor Obs_aug` with **no counting**. The remaining
**(II-hard)** is "the 1-WL-stable colouring `C^∞` at `{0,a,b}` refines `Obs_aug`" = **"C^∞ pins the plane `W`"**
(assigns each `w∈W` a recoverable colour). Because `C^∞` is a *refinement fixpoint*, "C^∞ refines `Obs_aug`" needs **no
round-counting** — only that `W` is pinned in `C^∞`. And "pin `W`" is a **2-dimensional, `d`-independent** statement
(matching `r*`-flat-in-`d`), into which the landed complement-factoring (`ScratchComplementFactorK`, cancels the `d−2`
complement to a count over `K²`) and the conic count plug. **Honest boundary:** "pin `W`" does *not* follow from
orbit-rigidity alone (WL is coarser than orbits — a singleton *orbit* need not be a singleton *colour*), so the counting
engine is still required. Base-augmentation **reshapes** the round-counting obligation into a `d`-independent plane-pinning
closure; it does not dissolve the math.

**Insight 5 — the singleton locus recovers *more easily*, so it is a separate branch, not a gap.**
When `u`'s complement component `u_⊥` is isotropic (`Q u_⊥ = 0`, forcing level `c=0`; on an anisotropic plane
`Z(u)={u_W}`, a singleton where (I)'s spanning fails), the exact Gram **collapses onto `u_W`**: `Q u = Q u_W` and
`polar u a = polar u_W a` (the complement is isotropic *and* polar-orthogonal to `W`). So two singleton vertices with the
same `W`-component share the exact Gram (`ScratchConicSpan.exactGram_of_isotropic_complement`). `hspan_or_singleton`
routes `u` to the generic (I) branch or this one.

### 9.4 The landed substrate (the (I)-level geometry, both branches)
The chain, generic branch: `ScratchConicCount` (`card_binary_form` `#{w₁x²+w₂y²=c}=q−ε`, `exists_both_nonzero_solution`
for `q≥7`) → `ScratchConicSpan.exists_three_indep_levelset` (three non-collinear plane level-set points) →
`hspan_of_conic` (transport `Z(u)=u_W−L_c` via `ScratchComplementFactor.map_sub_split`, produces `hspan`) →
`ScratchSpanDim2Span.hspan_of_two_indep` → `ScratchSpanDim2Geom.exactGram_of_sameWProfile` (the core, `hprof ⟹ SameExactGram`).
Bare vertex: `ScratchConicSpan.exists_orthogonal_decomp` (explicit projection, no `IsCompl`) + `hspan_or_singleton`
(dichotomy). Singleton branch: `exactGram_of_isotropic_complement`. **Step B (observable → SameExactGram, both branches):**
`ScratchBaseAug` — `IsoSetEq` + `sameExactGram_of_isoSetEq_generic` + `sameExactGram_of_isoSetEq_singleton_anis` +
`eq_wComp_of_isotropic_of_anisotropic` (the (ii)-glue). **Step C reduction (observable resolves cells to orbits, mod
"1-WL refines `zSet`"):** `ScratchPlanePin` — `zSet` + `zSet_eq_iff_isoSetEq` + `zSet_invariant` (soundness via
`stab_fixes_span`) + `wallKernel_zSet_anisotropic` + `zSetEq_iff_stabOrbit_anisotropic` (the scaffold instantiation,
`bᵢ=1` for `zSet`). Soundness of the (count) observable: `ScratchJointCountInvariant.obsInvariant_jointCountProfile`.
`d`-cancellation (reused from the seal): `ScratchComplementFactorK.levelset_count_factors_through_chiDet`.

### 9.5 The ordered plan (what to do next)
> **[SUPERSEDED as the plan 2026-07-02 — this Step A/B/C plan predates the ORBIT-DIRECT pivot; its Step C ("C^∞ pins `W`")
> and Assembly targeted `SameExactGram`/`ClassCountsSeparateGram`, which is Witt-DEAD at `{a,b}` (36>27). The CURRENT plan
> is §9.7's "LEAN BUILD STARTED" (Pieces 1a→1c(iii), all landed and orbit-direct) + the top-of-doc CURRENT FRONTIER. Read
> this §9.5 for the (I)-geometry history only.]**
- **Step A — DONE.** A1 weaken (I) to one-directional `hprof`; A2 the full (I)-level geometry for **both** branches
  (generic `hspan_of_conic` + singleton `exactGram_of_isotropic_complement`), plus the bare-vertex dichotomy
  `hspan_or_singleton`.
- **Step B — the base-augmentation reduction (II-easy). ✅ DONE (2026-07-01, `ScratchBaseAug`, axiom-clean).** Observable
  `IsoSetEq Q W u u'` = "same isotropic set in `W`"; `IsoSetEq ⟹ SameExactGram` banked for **both** branches, no counting:
  generic `sameExactGram_of_isoSetEq_generic` (via (I) + `hspan_of_conic`); singleton
  `sameExactGram_of_isoSetEq_singleton_anis` (on an anisotropic plane). **The (ii)-glue is now DONE** — the match
  `u_W = u'_W` is **derived** from `IsoSetEq` via `eq_wComp_of_isotropic_of_anisotropic` (`Z(u)={u_W}` from the level
  identity + anisotropy), not carried. So both branches close down to the single Step C seam.
- **Step C — the crux: "C^∞ pins `W`" (II-hard) = the `d`-independent plane-pinning. ◑ FIRST STEPS LANDED + reduced;
  counting OPEN.** **Reduction LANDED (2026-07-01, `ScratchPlanePin`, axiom-clean):** take the observable to be the
  isotropic set `zSet(u) = {w∈W : Q(u−w)=0}` itself. Then `zSet u = zSet u' ⟺ IsoSetEq` (`zSet_eq_iff_isoSetEq`);
  `zSet` is `Stab{a,b}`-invariant (`zSet_invariant`, via `stab_fixes_span` — the plane is fixed pointwise);
  `WallKernelFor zSet` holds on an anisotropic plane (`wallKernel_zSet_anisotropic`, from Step B both branches); and the
  scaffold gives **`zSetEq_iff_stabOrbit_anisotropic`: `zSet u = zSet u' ↔ StabOrbit` (`bᵢ=1`) for the `zSet` observable**
  (mod Witt). **So the ENTIRE remaining route-A content is now the single statement "1-WL-stable at `{0,a,b}` refines
  `zSet`" (= C^∞ pins `W`)** — `zSet` is `Stab`-invariant but not a-priori 1-WL-computable; the plane points must be
  pinned by the iteration. **The open counting:** prove it by a **span-induction closure over `W`** (`0,a,b` pinned → all
  of `W`), each step a fixed 2-dim count over `K²` — complement-factoring (`ScratchComplementFactorK`) removes the `d−2`
  complement, the conic/pair-form count (`ScratchConicCount`/`PairForm`/`GaussCount`) separates the new plane point.
  **This is where the remaining open math lives.** Fallback if the closure stalls: an explicit `k`-round WL operator with
  a `d`-uniform `O(1)`-round bound (heavier; base-augmentation exists to avoid it).
- **`c=0`-hyperbolic tail (small, deferred).** The singleton branch assumes an *anisotropic* plane; `Q u_⊥ = 0` on a
  *hyperbolic* plane still has `Z(u)` spanning (2 lines), so it folds into the **generic** branch once a `c=0`-spanning
  lemma (the `L_0` = 2-lines count) is added. Not on the Step C critical path.
- **Assembly.** Re-instantiate `obsEq_iff_stabOrbit` on the WL-stable observable (the current scaffold is wired to the
  single-round `jointCountProfile`, which Insight 1 shows is insufficient — this swap is required); compose to the poly
  leaf count via `ScratchBoundedMultLeaves.leaves_le_prod_concentrated`.

### 9.6 Dead ends recorded (do not re-walk)
- **Gauss-direct / geometric-direct single-round recovery** — refuted by Insight 1 (`levelset_count_factors_through_chiDet`
  ⟹ `χ(det)`-valued ⟹ `O(1)` bits vs `Θ(q³)` orbits). Any "skip the iteration" idea dies here.
- **`WallKernelFor(jointCountProfile)` (single round) as the route-A predicate** — the scaffold reduces to it, but it is
  *insufficient at a bounded base* (same refutation; `ScratchWallKernel` "redirected 3c" note). The iterated observable
  is required.
- **Deriving the decomposition via `IsCompl`/restrict-nondegenerate** — unnecessary; `exists_orthogonal_decomp` does it
  directly by explicit projection (the diagonal plane Gram gives closed-form coefficients).

### 9.7 Step C — over-narrowing check, the 2-dim reframe, and the attack routes (2026-07-01)

**Over-narrowing verdict: NOT over-narrowed.** Three risks checked:
- **bᵢ=1 is the *efficient* target, not an overshoot vs the weaker `bᵢ≤poly(q)`.** `bᵢ=1` at span-dim≥2 *concentrates*
  all branching at span-dim≤1 (the span grows monotonically; once at span-dim≥2 with `bᵢ=1` you never branch again), so
  `L=O(1)` and `leaves ≤ q²` **directly** — no separate `L=O(d)`. The relaxation `bᵢ≤poly(q)` *re-introduces* `L=O(d)`
  (branching at every level; the product needs the depth bound), which collapses to the *same* cell-discretisation core.
  So `bᵢ=1` kills `B` and `L` at once — it is the right target, confirmed by the probe (branching concentrated at
  span-dim-1).
- **Iteration is genuinely required** (Insight 1, airtight): one count = 1 bit (`χ(det)`), separating `Θ(q³)` plane
  orbits needs `Θ(log q)` bits. Not a missed single-round shortcut.
- **Anisotropic-plane restriction is removable** (not fundamental): it is an artifact of `hspan_of_conic` covering only
  `c≠0`; the `c=0`-hyperbolic case (`Z` = 2 lines, still spans) folds into the generic branch once the 2-lines count is
  added.

**★ THE 2-DIM REFRAME (the key handle).** Via the *landed* complement-factoring
(`ScratchComplementFactorK.levelset_count_factors_through_chiDet`), every count that would pin a plane point **factors
through the plane, the `d−2` complement cancelling**. So "1-WL refines `zSet`" reduces to a **`d`-independent,
2-dimensional count-separation**: pin the points of `W ≅ K²` by their complement-factored count-profiles. This is a
*bounded, concrete* individualization of the 2-dim plane `VO^ε_2(q)` from `{0,a,b}` — **NOT** the general SRG
WL-dimension wall. The probe's `r*∈{3,4}`-flat-in-`d` **is** this 2-dim problem being `d`-uniform. (NB: on an anisotropic
plane the *within-plane* counts are translation-homogeneous, so the separating counts are the **base-config** counts —
`jointIsoCountK` to `{0,a,b,w}`-type configs, which depend on `w`'s Gram to the base — `χ(det)`-valued per round,
accumulating over rounds. This is why the base points, not the plane's internal structure, drive the separation.)

**Attack routes.**
- **Route α — span-induction pinning closure (PREFERRED; avoids a general WL operator).** Grow a pinned set `P ⊆ W`
  (base `{0,a,b}`); each step pins a new plane point by its count-profile to `P` (complement-factored → a fixed `K²`
  count via `ScratchConicCount`/`PairForm`). Closure over the 2-dim `W` terminates. **Load-bearing lemma:** a plane
  point is determined by its `χ(det)`-profile over enough base-configs (the accumulation).
- **Route β — explicit `k`-round WL operator (fallback).** Define the iterated colouring; prove `O(1)`-round convergence
  `d`-uniformly. Heavier (needs the round-count bound + a WL framework).
- **Reusable levers (all landed):** `jointIsoCountK_ne_of_chiSep_pair` (seal's per-round pair separation),
  `ScratchComplementFactorK` (`d`-cancellation to `K²`), `ScratchConicCount` (plane counts), `PairForm`/`GaussCount`,
  `PerAnchorBound` (the per-anchor fraction bound the seal uses to assemble many anchors).
- **First sub-step (Route α) — ✅ LANDED (2026-07-02, `ScratchPlaneSep`, axiom-clean).** The per-round separator
  **fires for plane points**: `plane_count_sep` = the seal's `jointIsoCountK_ne_of_sep` at `u,v := w,w'` — two plane
  points whose `χ(pairForm)` to a base pair `{t,t₀}` differ have **different** joint isotropy counts (each base pair =
  one `χ`-bit). The **accumulation is isolated** as one clean open predicate `ChiProfileSeparatesPlane` (the
  `χ(pairForm)`-profile over base pairs separates the plane), and the reduction `count_profile_separates_of_kernel`
  proves: kernel ⟹ the 2-round joint-count profile is injective on `W`. **So route A now reduces to the single open
  predicate `ChiProfileSeparatesPlane`** (+ the deferred 1-WL-computability wiring). Route α **has legs** — the lever
  applies verbatim; the residue is the `d`-independent 2-dim accumulation.

**The honest hard part.** The `O(1)`-round convergence — *how* a bounded number of `χ(det)`-bit rounds accumulate
`Θ(log q)` bits to pin the plane — is not yet analytically pinned; the probe is the evidence, the proof is the frontier.
Route α makes it a concrete `K²` induction (the seal's per-anchor + union assembly, at the plane level) rather than an
abstract WL-dimension claim — the best available handle. This is a genuine Gauss build; there is **no** purely-structural
scaffold left (the structural reduction is already complete in `ScratchPlanePin` — "1-WL refines `zSet`" is the residue).

**Post-sub-step status (2026-07-02):** the accumulation is now the **single named open predicate**
`ScratchPlaneSep.ChiProfileSeparatesPlane` — "the `χ(pairForm)`-profile over base pairs separates the plane." Proving it
is the seal's per-anchor + union assembly re-run at the `d`-independent plane level (reuse `PerAnchorBound` /
`BadAnchorCount` / the matching trick, but over `W ≅ K²` instead of the `O(log n)` frame).

**★ SCOPING CORRECTION + INDUCTIVE REFORMULATION (2026-07-02, `ScratchPlanePinInduction`, axiom-clean).** The one-shot
`ChiProfileSeparatesPlane Q S₀ W` is subtly the **wrong** target — its truth is hostage to `S₀`:
- `S₀ = {0,a,b}` (the actual span-dim-2 base): **FALSE.** O(1) base pairs give O(1) `χ`-bits, and Insight 1 (each count is
  `χ(det)`-valued = 2-valued) says O(1) bits cannot separate the `Θ(q²)` plane points.
- `S₀` large enough to hold: the anchor points must themselves be **pinned / 1-WL-colour-distinct** — because
  `jointIsoCountK Q w {t,t₀}` is 1-WL-visible **iff** `t,t₀` are colour-distinguished. That is the "wiring", and it is an
  **induction** (the pinned set grows round by round), *not* a deferrable footnote. So the one-shot form couples (1) and
  (2) in a way that risks proving the wrong lemma (a magic `S₀` the wiring can't supply).

The fix is the **pinning closure** (Route α, now formalised): `PlanePinnable Q W a b` = "the closure anchored at `{0,a,b}`,
where each round `pinStep` adds every `w ∈ W` that is `SeparatedBy` (one-round `χ(pairForm)` separation) the *already-pinned*
anchors from all of `W`, reaches **all** of `W`." (`pinStep`/`pinIter`/`PinClosure`/`PlanePinnable`, with `SeparatedBy.mono`
/`.symm` and the extraction `sep_of_mem_pinIter`.) It composes with everything built:
`chiProfileSeparatesPlane_of_pinnable` (`PlanePinnable` + a ≤3-pair `hbase`, discharged by base individualisation, +
`S₀ ⊇ pinned` ⟹ the one-shot `ChiProfileSeparatesPlane`) and `count_profile_separates_of_pinnable` (end-to-end ⟹
`jointIsoCountK` profile injective on `W`). **What this buys:** the closure certifies the anchors are *reachable in order*
— exactly what the wiring needs (each pinned anchor is individualised in turn, so counts to it are 1-WL increments), which
the one-shot `S₀` did not.

**★ THE 1-WL-COMPUTABILITY WIRING — LANDED (2026-07-02, `ScratchWLWiring`, axiom-clean).** Item (2), built on a minimal
explicit 1-WL interface (so the standard-WL content is named, the open residual surfaced):
- **Core payoff (abstract `V`):** `IsColorSingleton`, `PinsPlane C W` (= "`C^∞` pins the plane", every plane point a
  colour-singleton), and the interface field `ReadsSingletonIsotropy` (WL reflects `Q(·−w)=0` to a colour-singleton `w` —
  standard 1-WL: a count against a singleton colour-class is `1`/`0`). Then `refines_zSet_of_pinsPlane` (⟹ `C` refines
  `zSet`) → `stabOrbit_of_colorEq` (WL-colour equality ⟹ same orbit, via `zSetEq_iff_stabOrbit_anisotropic`) →
  `colorEq_iff_stabOrbit` (+ soundness = `ObsInvariant` ⟹ the full **`C u=C u' ↔ StabOrbit`, `bᵢ=1`** for the WL colouring).
  *This is the wiring's deliverable: once `C` pins the plane, the WL cells ARE the `Stab`-orbits.*
- **Bridge (`V=Fin d→K`):** `pinsPlane_of_planePinnable` — `PlanePinnable` + `ReadsSingletonCounts` (the count analogue
  interface field, standard 1-WL) + base individualisation (`hbaseIndiv`, free from the descent) ⟹ `PinsPlane`, by an
  induction on the closure level (`colorSingleton_of_mem_pinIter`: fresh points are separated from other plane points by
  `plane_count_sep` + `ReadsSingletonCounts`, and from the complement by the residual below).
- **★ NEW FINDING — the honest residual, now NAMED: `SeparatesPlaneFromComplement`** (plane points get a different
  `C`-colour from every non-plane vertex). This is the genuine remaining WL-dimension content: the plane's orbit-rigidity
  (Insight 2) does **not** make its points colour-singletons *versus the complement* (WL is coarser than orbits), yet a
  *global* singleton is what both the induction (an anchor must be read via `ReadsSingletonCounts`) and the payoff
  (`refines_zSet_of_pinsPlane`) require. The base-augmentation framing glossed exactly this ("pin `W` does not follow from
  orbit-rigidity", Insight 4's honest boundary); it is now a first-class Lean predicate, needed at *every* induction level.

**The residual set to close route A (updated):** (1) prove `PlanePinnable` (the Gauss accumulation as a growing closure
over `W≅K²` — the frontier); (2a) discharge the two standard-1-WL interface fields (`ReadsSingletonIsotropy` /
`ReadsSingletonCounts`) in a minimal WL-colour framework (Route β — bookkeeping); (2b) prove
`SeparatesPlaneFromComplement` (the real residual WL-dimension content — the plane-vs-complement colour separation).

**★★ PROBE-DRIVEN CORRECTION (2026-07-02) — `PlanePinnable` is REFUTED; the mechanism is colour-CLASS counts, not
plane-point pinning (`ScratchWLClassCounts`, `pin_probe.py`).** When I went to *prove* `PlanePinnable`, a probe
(`GraphCanonizationProofs/pin_probe.py`) settled the model first, and it is **decisive against the singleton-anchor
closure:**
- The `SeparatedBy`-closure (pin `w` once separated from all of `W` by `χ(pairForm)` to *pinned singleton* anchors)
  **STALLS at the 3-point base for every `q ≥ 5`** (pins 3/`q²`). Even bare 1-WL *on the isolated plane* stalls at 4
  colour classes. So **`PlanePinnable` (via the singleton `PinClosure`) is FALSE for `q ≥ 5`** — plane-point pinning by
  singleton-anchor `χ`-profiles is the **wrong mechanism**. (This matches `ScratchWallKernel`'s standing note: the
  single-round `WallKernel`/`SameSquareClass` is *refuted at a bounded base* — "orbits 12,30,56 vs profile stuck ≈10".)
- What actually delivers `bᵢ=1` (`recovery_depth_probe.py`, re-confirmed): **ambient 1-WL refining by counts to colour
  CLASSES** recovers the exact-Gram orbits in `r*∈{3,4}` rounds, flat in `d`. The missing power is *counting `z` against
  each evolving colour class*, not against a few fixed singleton anchors. `PlanePinnable`/`ChiProfileSeparatesPlane` only
  ever count to singleton anchors, so they cannot reach it.

**Corrected target — `ScratchWLClassCounts` (LANDED, axiom-clean).** The observable is the **class-count profile**:
`classCount C Q u c k = #{z : C z = c ∧ iso3 Q (u−z) = k}` and `SameClassCounts C Q` the induced relation (a graph
invariant — `sameClassCounts_of_stabOrbit`, soundness FREE via `iso3` similitude-invariance). With `C` 1-WL-stable
(`IsWLStable`, the fixpoint/equitable property of `C^∞`), the open content is the single predicate **`ClassCountsSeparateGram
C Q S`** = `WallKernelFor (SameClassCounts C Q) Q S` — the class-count profile separates the exact Gram. This is the
*iterated / colour-class* instance `ScratchWallKernel` explicitly asked for, and it is **TRUE** (probe: cells = orbits),
unlike `PlanePinnable`. `wallKernel_of_wlStable` + `colorEq_iff_stabOrbit` give **`C u = C u' ↔ StabOrbit`, `bᵢ=1`** via
the scaffold `obsEq_iff_stabOrbit`.

**Status of the plane-pinning modules.** `ScratchPlanePinInduction` (`PlanePinnable`) and the `ReadsSingletonCounts`
bridge in `ScratchWLWiring` are now **superseded as the route** (their singleton-anchor mechanism stalls). They remain
axiom-clean and logically valid; the **Core** of `ScratchWLWiring` (`refines_zSet_of_pinsPlane` / `colorEq_iff_stabOrbit`:
`PinsPlane` ⟹ `bᵢ=1`) **survives and is subsumed** — `PinsPlane` (plane points are colour-singletons in `C^∞`) is a
*consequence* of the correct recovery (plane points are singleton orbits, and `C^∞` recovers orbits), not the route to it.
`SeparatesPlaneFromComplement` likewise is subsumed into the ambient class-count recovery.

**The frontier is now `ClassCountsSeparateGram`** — the WL-dimension statement that ambient class-count 1-WL separates
exact-Gram classes at a span-dim-2 base, uniformly in `d`. Probe-true (`r*∈{3,4}` flat in `d`). Then compose via
`leaves_le_prod_concentrated`. **[SUPERSEDED 2026-07-02 by Piece 1a — the frontier is now the ORBIT-DIRECT crux
`GramCountsRecoverOrbit` (`ScratchGramStratCount`), NOT `ClassCountsSeparateGram`.** The latter targets `SameExactGram`
and its capstone needs `WittExtendsToOrbit Q {a,b}`, which is FALSE here (orbits `36 ⊋ 27` gram-classes). Read the
"LEAN BUILD STARTED" section-plan below (Pieces 1–3) as the current spine; `ClassCountsSeparateGram` survives only as the
observable/soundness layer.]**

**★★ ROUND-STRUCTURE PROBE (2026-07-02, `round2_probe.py` / `round2_char.py`) — the attack `β1` (bounded-round) deepened;
KEY: WL rounds use MULTIPLICITIES the seal's `χ(det)` theory does not cover.** Per-round class counts on `VO^ε_4(q)` at
base `{0,a,b}`:

| | r1 (3iso) | r2 | r3 | r4 | orbits |
|---|---|---|---|---|---|
| `VO⁻₄(3)` | 11 | 32 | **36** | — | 36 |
| `VO⁻₄(5)` | 11 | **81** | **150** | — | 150 |
| `VO⁻₄(7)` | 11 | 103 | **392** | — | 392 |
| `VO⁺₄(5)` | 11 | 66 | 148 | **150** | 150 |

Findings: (1) **3-stage bootstrap**, `r1=11` flat in `q`; `r*` = **3 (minus) vs 4 (plus)** — form-dependent, so β1 must
prove *bounded-round convergence*, NOT "round 3 = Gram". (2) **Stratified yield WORKS but is multi-step:** counting `u`
against the round-2 strata separates *all* same-r2/different-Gram pairs by round 3 for minus type, but `VO⁺₄(5)` leaves 2
pairs unseparated at round 3 (217/219), finished at round 4.

**(3) ★★ ROUND 2 CLOSED FORM — NAILED (2026-07-02, `round2_closedform.py`): round 2 = the seal's `jointIsoCountK`-profile
over sub-configs `S ⊆ {0,a,b}`, EXACT partition equality in all cases** (`r2 = Zprof`: `32/81/103/66/32`). Derivation:
round 2 is the *fine* isotropy-count profile at base `{0,a,b}` with pivot `u`; the anisotropic-to-`u` (`k=2`) counts add no
`u`-info (they are a constant minus the `k∈{0,1}` counts), and by inclusion–exclusion (the
`qProfileSeparatesAtBaseK_of_zProfileSeparatesK` pattern) the fine profile ⟺ the `Z`-count profile
`Z(u;S)=#{z≠u : Q(z−u)=0, Q(z−t)=0 ∀t∈S}` = `jointIsoCountK`. By the seal's bridge
(`levelset_count_eqK`/`configGaussSum_eq_detK`) each factors through `χ(det G_config)`, so **round 2 has the closed form
`(χ(det G_{{u}∪S}))_{S⊆{0,a,b}}` and is FULLY SEAL-REUSABLE.** [**Correction:** the previous "round 2 is *incomparable* to
`χ(det)`" claim was an ARTIFACT of a wrong candidate in `round2_char.py` — it used `χ(pairForm)` on the *wrong* vectors and
omitted the config Grams (incl. the triple `{u,a,b}`); the correct config-Gram `χ(det)` = `jointIsoCountK` matches round 2
exactly. There is no "new incomparable WL-multiplicity object" at round 2.] Round 2 is **stuck below Gram** (`81<125`) —
exactly as the seal's single-round is known to be at a *bounded* base.

**(4) So the genuinely-new, poly-specific content is ROUND 3, precisely located.** Round 3 counts `z` (isotropic to `u`)
stratified by `z`'s *round-2 class* = `z`'s `χ(det)`-profile to `{0,a,b}`. As a sum: `#{z : Q(u−z)=0, z ∈ σ}` where `σ`
is a `χ(det)`-defined stratum — i.e. a **mixed Gauss sum `Σ_z 𝟙[Q(u−z)=0]·(character-function of z's base-Gram class)`**.
This is what the seal does *not* do (it individualises more points → `O(log n)` frame → quasipoly; WL counts against the
`χ(det)`-strata at a *bounded* base instead). It is structured and Gauss-tractable — NOT an opaque multiplicity. **The
β1/hybrid crux lemma:** *these mixed `𝟙[isotropic]·χ(base-Gram)` sums separate the exact Gram of `u` in `O(1)` iterations,
uniformly in `d`* — probe-true, the real poly-vs-quasipoly content. Rounds 1–2 are seal-characterised (closed form);
round 3 is the new work. `round2_probe.py`/`round2_char.py`/`round2_closedform.py` are durable.

**(5) ★★ ROUND 3 CHARACTERISED (2026-07-02, `round3_probe.py`) — the mechanism reaches ORBITS, form-independently, and
the plus-tail is fully explained.** The round-3 observable `T(u;g) = #{z : gram(z)=g, Q(u−z)=0}` (count `z` isotropic-to-`u`
stratified by `z`'s Gram-to-base `g=(Qz,polar z a,polar z b)∈K³`) **separates the orbits EXACTLY** — `T_exact`-classes
`= #orbits` (`36/150/392`) for **both minus AND plus, in ONE step, form-INDEPENDENT.**
- **Character-sum form:** `T(u;g) = q⁻⁴ Σ_{s,t₀,t₁,t₂} ψ(−t·g) ψ(s·Qu) · G(s+t₀; t₁a+t₂b−su)`, `G(α;w)=Σ_z ψ(αQz+polar(z,w))`.
  Completing the square in `z`, `u` enters **only through its DUAL Gram** (`s²Q*(u) + s·polar*(u,a) + s·polar*(u,b)`) — which
  sees the complement `W^⊥`. That is *why* `T` separates finer than the **primal** gram-to-`{a,b}`: the latter is itself
  **coarser than orbits** (`27<36`, `125<150`) because `{a,b}` spans only the 2-plane `W`, so it misses the complement
  structure (whether `u_⊥=0`, `Q(u_⊥)`) that distinguishes plane-vertices — which *are* singleton orbits (`stab_fixes_span`) —
  from non-plane vertices sharing the same plane-Gram. **The clean, form-independent Gauss target:** the transfer kernel
  `K(u_dualgram, g)` is **non-degenerate** (the profile `{T(u;g)}_g` inverts to `u`'s dual Gram = its orbit) — a Fourier
  non-degeneracy of the `𝟙[isotropic]×gram` kernel.
- **The plus-tail EXPLAINED (and it is NOT a real obstruction):** the *actual* WL round 3 counts against the round-2
  (`χ(det)`) strata, which are slightly **coarser** than exact-Gram strata. For `VO⁺₄(5)` this coarseness collides **exactly
  2 orbit-pairs** (`T_r2 = 148 ≠ 150`), split at round 4; minus type and `VO⁺₄(3)` are fine at round 3. So `r*=4` is purely a
  *strata-coarseness* artifact — it **vanishes** against exact-Gram strata (`T_exact = 150` for `VO⁺₄(5)` too).

**⟹ STRATEGY UPDATE: the HYBRID beats pure β1.** The form-dependent round count (`3` vs `4`) is *only* a strata-granularity
effect, so tracking exact rounds is the wrong framing. The clean route: prove the **form-independent** fact "counting against
Gram-strata separates orbits" (= `K` non-degenerate, a Fourier/Gauss non-degeneracy — reuses `GaussCount` + the seal's
`levelset_count_eqK`), then a **fixpoint argument** (the stable `C∞` is equitable; if it were coarser than orbits, the
round-3 count *against its own strata* would strictly refine it — contradiction — so `C∞ = orbits`). This discharges
`ClassCountsSeparateGram` without any form-dependent round-counting. **The single remaining Gauss lemma: `K` non-degenerate.**
`round3_probe.py` is durable.

**★★ LEAN BUILD STARTED (2026-07-02) — the section plan + Piece 1a landed (`ScratchGramStratCount`, axiom-clean).** Plan
for closing `bᵢ=1` at the span-dim-2 base:
- **Piece 1 — the K-non-degeneracy lemma (the Gauss crux).** **1a ✅ LANDED** (`ScratchGramStratCount`): the round-3
  observable `gramK Q a b u = (Q u, polar u a, polar u b)`, `gramStratCount u g = #{z : gramK z = g ∧ Q(u−z)=0}`,
  `SameGramStratCounts`; **soundness** `sameGramStratCounts_of_stabOrbit` (orbit ⟹ same profile, free via the
  isometry-reindex `gramK_isometry`/`polar_isometry`); the crux `GramCountsRecoverOrbit : SameGramStratCounts ⟹ StabOrbit`;
  capstone `gramCountsEq_iff_stabOrbit` (soundness + crux ⟹ `bᵢ=1`). **★ Targets the orbit DIRECTLY — NOT via
  `SameExactGram Q {a,b}` + Witt**, because `{a,b}` spans only the 2-plane so the orbit is *finer* than `SameExactGram`
  (`36 > 27`; `WittExtendsToOrbit Q {a,b}` is FALSE — the plane-vertex vs nonzero-isotropic-complement collision). This
  correctly routes around the vacuity the `SameExactGram`+Witt scaffold would hit at this base. **1b ✅ LANDED**
  (`ScratchGramStratCharSum`, axiom-clean): the character-sum identity — `gramStratCount_charsum` (raw four-constraint
  Fourier expansion via `countk_eq_sum_charsum`), `gramStrat_inner_normalize` (inner z-exponent = `(r₀+r₃)Qz +
  polar z (r₁•a+r₂•b−r₃•u) + r₃Qu`, the D1 normal form, via `quad_sub` + polar bilinearity), `gramStratCount_charsum_normalized`
  (combined). Pure `GaussCount` assembly, no new Gauss theory. **Build notes (reusable):** (i) Piece 1a's `gramStratCount`
  def was switched off `open scoped Classical` → genuine `DecidableEq K` `DecidablePred` (still builds axiom-clean), so its
  filter shares the toolkit's decidability instance; (ii) even so, `countk`'s `∀ (j:Fin 4)` decidability instance is not
  defeq to a restatement's (matrix-index reduction differs), so the count↔`gramStratCount` bridge needs `convert … using 3`
  + an instance-agnostic `ext` subgoal, not `rw`/`exact`. **1c(i) ✅ LANDED** (`ScratchGramStratEval`): inner z-sum evaluated
  — `gramStrat_inner_eval_ne` (bulk `ρ=r₀+r₃≠0`, D1) + `gramStrat_inner_eval_zero` (boundary `ρ=0`, `sum_addChar_linearMap`).
  **1c(ii) ✅ COMPLETE** (`ScratchGramStratInvert`): the g-profile inversion — `gsum_orthogonality` + `innerZ` (opaque def) +
  `gramStrat_transform_eval` + `sameGramStratCounts_transform` (`SameGramStratCounts ⟹ equal innerZ fibre sums ∀s`).
  **1c(iii) ✅ REDUCTION** (`ScratchGramStratOrbit`): the crux reduces to two named predicates, **both carrying a
  `GoodBase Q a b` antecedent** (`a,b` orth aniso + `(2:K)≠0` + `Q.polarBilin.Nondegenerate`) so they are TRUE and
  dischargeable — NOT the FALSE bare `∀ Q a b` forms (which could never be discharged) — `GramCountsRecoverGram`
  (GENUINELY-OPEN Gauss, must be PROVED, probe-true) + `RefinedWittExtends` (a CITATION of Witt's theorem, acceptable to
  carry) — via `gramCountsRecoverOrbit_of`; `gramCountsEq_iff_stabOrbit_refined` ⟹ `bᵢ=1` modulo the two;
  `stabOrbit_imp_span_iff` shows the flag is orbit-sound. **▶ Piece 1 open content = the single Gauss lemma
  `GramCountsRecoverGram`** (attack: `sameGramStratCounts_transform` + `gramStrat_inner_eval_ne`/`_zero` + a primitive char).
- **Piece 2 — the WL bridge:** `SameClassCounts C → SameGramStratCounts` (the actual WL colouring's counts refine the
  gram-strat counts, via round 2 = seal `jointIsoCountK`). **★ ORBIT-DIRECT — NOT via `ClassCountsSeparateGram`:** that
  predicate targets `SameExactGram` and its capstone carries `WittExtendsToOrbit Q {a,b}`, **FALSE** at this base (orbits
  `36 ⊋ 27` gram-classes — why Piece 1a is orbit-direct). Piece 2 feeds `SameGramStratCounts` into
  `gramCountsEq_iff_stabOrbit`, never touching `SameExactGram`/Witt. **Piece 2 is coupled math, not plumbing:** the bridge
  holds at the fixpoint `C∞` and reduces to the finding-5 equitability argument — a generalization of Piece 1's
  K-non-degeneracy to `C∞`'s own (coarser) strata (cf. the `VO⁺₄(5)` round-4 tail).
- **Piece 3 — assembly:** compose `SameClassCounts ⟹ SameGramStratCounts ⟹ StabOrbit` (orbit-direct via
  `gramCountsEq_iff_stabOrbit`) + `leaves_le_prod_concentrated`. (`ScratchWLClassCounts`'s `colorEq_iff_stabOrbit` /
  `ClassCountsSeparateGram` capstone is Witt-dead at `{a,b}` and superseded; its `iso3`/`classCount`/`IsWLStable` defs +
  soundness are still used.)
**★★ `GramCountsRecoverGram` DISCHARGED to a classical cone non-degeneracy; `hψ` DISCHARGED (2026-07-02, cont.,
`ScratchGramStratGauss` + `ScratchGramStratGaussReduce`, axiom-clean).**

**★ CORRECTION (verified by hand — do NOT re-walk).** The "Fourier-invert the fibre sums; bulk recovers Gram" attack is
**empty as extraction**: the `r₃`-marginal of `sameGramStratCounts_transform` is exactly `|K|`·(the `g`-Fourier transform
of the count), so equal counts give it *for free* — the individual `innerZ_u(r)` that carry the Gram are NOT observable.
Dually the *elementary* first moment (`∑_g g·count u g = N·gramK u`, `N=#{Qw=0}`) **fails in char `p`** (`q|N`, no
cancellation in `K`). Moral: `u`'s Gram lives in the **phase** `ψ(⟨t,gramK u⟩)∈ℂ`, so the ℂ/character route is genuinely
necessary. (⟹ 1b/1c(i)/1c(ii) are correct but not the direct extraction path; the correct core is the factorization.)

**★ CORE = the factorization (`ScratchGramStratGauss`).** `countHat u t := ∑_g ψ(⟨t,g⟩)·gramStratCount u g`
`= ∑_{z:Q(u−z)=0} ψ(⟨t,gramK z⟩)` (`countHat_eq_isoSum`); shift `z=u+w` ⟹ **`countHat_factor`:**
`countHat u t = ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)`, `isoConeSum y := ∑_{w:Qw=0} ψ(polar w y)`. Gram in the phase,
flag/complement in `isoConeSum`. No Gauss brick / primitivity / `IsDomain` needed.

**★ REDUCTION (`ScratchGramStratGaussReduce`, `hψ` DISCHARGED).** `gramK u=gramK u' ↔ SameExactGram Q {a,b} u u'`
(`gramK_eq_iff_sameExactGram`); a primitive char is **constructed** (Mathlib `AddChar.FiniteField.primitiveChar K ℚ`, char
`0≠ringChar K`), so `gramCountsRecoverGram_of_isoConeSep : IsoConeSumSeparatesGram → GramCountsRecoverGram` carries **no
`hψ`**. Capstone `gramCountsEq_iff_stabOrbit_of_isoConeSep` ⟹ **`bᵢ=1` modulo exactly `IsoConeSumSeparatesGram` (Gauss) +
`RefinedWittExtends` (Witt)**.

**★★★ `IsoConeSumSeparatesGram` DISCHARGED — PROVED axiom-clean (2026-07-02, cont., `ScratchGramStratConeEval` +
`ScratchGramStratConeSep`).** The entire Gauss/analytic content of Route A's Piece 1 is now done.
- **`isoConeSum_eval_even`** (`ScratchGramStratConeEval`) — the closed form. For **even** ambient dim (the `VO_{2m}` case)
  the quadratic Gauss sum is *scale-invariant* (`∑_x ψ(s·Qx)=χ(s)^n·G₁=G₁`, `χ(s)^n=1` for even `n`), collapsing the
  `s`-sum to additive orthogonality: `|K|·isoConeSum(y)=|V|·𝟙[y=0]+G₁·(|K|·𝟙[Qy=0]−1)`, `G₁=∑_xψ(Qx)`. Proof = expand
  `𝟙[Qw=0]=|K|⁻¹∑_sψ(s·Qw)`, split `s=0` (linear, `sum_addChar_linearMap`+nondeg) from `s≠0` (Brick D1 + Brick C-scale
  `sum_addChar_quadForm_smul`), reindex `s↦−s⁻¹` (involution). Corollary **`isoConeSum_ne_zero`** (nowhere-zero at even dim,
  `G₁≠0` + integer factor `∈{|K|−1,−1}`).
- **`isoConeSumSeparatesGram`** (`ScratchGramStratConeSep`) — the separation. Off-diagonal (`polar u a/b`) + diagonal (`Qu`)
  both from `isoConeSum_ne_zero` + primitivity *without knowing the value* (the `t₀=0` slice makes `isoConeSum` a common
  nonzero factor; the `(t₀,0,0)` slice gives `isoConeSum(t₀•u)` constant-in-`t₀` & nonzero, and cross-multiplying kills it);
  the **flag** falls out of the closed form once phases match (`𝟙[y_u=0]=𝟙[y_u'=0]`, read at `t₀=1`). NB the earlier
  Kloosterman-zero-set worry EVAPORATED — even-dim scale-invariance makes `isoConeSum` nowhere zero, so no zero-set analysis.
- **Capstone `gramCountsEq_iff_stabOrbit_wittOnly`** (`ScratchGramStratConeSep`, axiom-clean): **`bᵢ=1` modulo ONLY the Witt
  citation `RefinedWittExtends`** (`hψ` constructed internally).

**★★★ PIECE 2 — the WL bridge — LANDED (2026-07-02, cont., `ScratchGramStratWLBridge`, axiom-clean).**
`sameGramStratCounts_of_sameClassCounts` (**`ColorRefinesGramK` C** ⟹ `SameClassCounts → SameGramStratCounts`): with the
colouring at least as fine as `gramK`, `{z:gramK z=g}` is a union of colour classes, so `gramStratCount u g = ∑_{g-colours
c}(classCount u c 0+classCount u c 1)` (isotropy `Q(u−z)=0 ⟺ iso3∈{0,1}`), a `u`-indep class-count sum — equal under
`SameClassCounts`. The refinement hypothesis is *necessary* (trivial colouring sees only isotropy degree) and holds for
`C∞=orbits` (weaker than the goal). **Assembly `colorEq_iff_stabOrbit_wittOnly`**: `C u=C u' ↔ StabOrbit` (`bᵢ=1` for the
WL colouring) modulo `{ColorRefinesGramK, IsWLStable, ObsInvariant, RefinedWittExtends}`. **NEW NEXT = Piece 3 assembly**
(`leaves_le_prod_concentrated`) + discharge residuals (`ColorRefinesGramK` = WL-dim, colouring props, Witt).
**All landed axiom-clean, NOT in build.sh** (10 modules): 1a–1c(iii) (`ScratchGramStrat{Count,CharSum,Eval,Invert,Orbit}`),
factorization+reduction (`Gauss`/`GaussReduce`), closed form + separation (`ConeEval`/`ConeSep`), WL bridge (`WLBridge`).
Predicates keep `GoodBase` (+even dim); separation needs `Even (finrank)` (true for `VO_{2m}`; odd = future).
