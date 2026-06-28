# START HERE — chain-descent graph canonizer

The single entry point for the project. Read this first; it gives the idea, the
current state, and a curated reading order. It replaces the old "simplified
overview" as the onramp (that file is now archived).

> **One rule for reading this project.** Treat every summary — this doc, memory,
> a doc's older prose — as a *hypothesis* to confirm against the primary docs and
> the Lean source. Where they disagree, the source wins, and the doc's own STATUS
> block (top of each `chain-descent-*.md`) is the current state. The
> authoritative, script-maintained record of *what is proved* is
> [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).

---

## 1. The idea, in one read

**Goal.** A polynomial-time **graph canonizer**: relabel a graph's vertices so
that two graphs get the same labelled adjacency matrix exactly when they are
isomorphic. The textbook recipe — take the lexicographically smallest adjacency
matrix over all `n!` labellings — is isomorphism-invariant for free but too slow.
The whole project is about computing that lex-min **without** enumerating `n!`.

**Search space (individualization–refinement).** *Color refinement* (1-WL)
recolours each vertex by the multiset of its neighbours' colours until colours
stabilise; vertices sharing a final colour form a **cell**. Refinement is cheap,
deterministic, iso-invariant, and never wrong — but *incomplete*: it can leave
vertices in one cell that the graph treats differently. When a cell has ≥ 2
vertices, **individualize** one (pin it as smallest) and refine again; the new
information propagates. Every choice is a branch, so this builds the
**IR tree**, whose leaves are full labellings. Naive IR (nauty) is provably
**exponential** on CFI graphs.

**The one idea — true vs. false symmetry.** At a branch cell there are two cases,
and *refinement cannot tell them apart*:
- **True symmetry** — an actual automorphism carries one vertex to another. The
  branches are mirror images: pick any one representative, descend, ignore the
  rest.
- **False symmetry (a genuine decision)** — no automorphism relates them, so the
  choices give different canonicals and must be compared.

A true symmetry can even be **hidden** (CFI "gauge twists" look like genuine
decisions but are not). Exponential blow-up *is* genuine decisions stacking up.
The entire algorithm is organized around cheaply telling a (possibly hidden) true
symmetry from a genuine decision.

**Chain descent.** Descend the IR tree, but at each cell, *before* branching, sort
its vertices into **orbits** (maximal interchangeable groups) and branch on **one
representative per orbit**. One orbit ⇒ no branching, just descend; `k` orbits ⇒
a `k`-way fork, canonize each, take the lex-min. The component that returns a
cell's orbit partition is the **oracle**, and it obeys one rule:

> **Soundness.** Never merge two vertices into one orbit without a *proof* — an
> actual automorphism, verified edge-by-edge, mapping one to the other.

Over-splitting only costs an extra branch (slower, still correct); over-merging
could drop the branch holding the true minimum. So the oracle may be cautious,
never over-confident. It does **bounded** work: when it cannot certify cheaply,
the descent **flags and stops** — it never falls back to brute force. A returned
answer always means "computed cheaply"; a flag means "needs a tool this oracle
lacks." A **polynomial node budget** makes "polynomial-or-flag" a hard guarantee.

**Why polynomial when it works.** Cost is a **sum over descent-tree nodes** of the
oracle's per-node work, and the budget bounds the node count — versus the old
design's *product* (a fully-explored tree). Replacing the product with a sum is
the entire point. Three standard facts keep the rest free: the automorphism group
stores as generators not elements (**T-A**), a base has ≤ `n` levels (**T-B**),
and — the only open factor — work-per-node is polynomial (**T-C**, *the* oracle
problem).

**Worked example — `C₆` (6-cycle `0–1–2–3–4–5–0`).** Refine: one cell `{0..5}`.
Oracle: one orbit? Yes — rotations are verified automorphisms; pick `0`, record
the 6 rotations, descend. Refine with `0` pinned: `{0},{1,5},{2,4},{3}`. Target
`{1,5}`: the reflection through `0` swaps them — one orbit; pick `1`, descend.
Refine: all singletons — **leaf**. The descent was a *single path*, two certified
levels, no genuine decision; the chain gives `|Aut(C₆)| = 6 × 2 = 12`. A *rigid*
graph instead forks honestly (each leaf reached fast, forks don't stack, budget
holds). A graph that piles genuine decisions deep (CFI over a large base)
exhausts the budget and **flags** — no wrong answer, no exponential run.

**What is settled vs. open.** Settled: the algorithm is **correct** (returns an
iso-invariant, complete canonical form or an honest flag — never wrong) and
**budget-bounded** (cannot run exponentially). Open: whether the oracle certifies
orbits cheaply enough that the graphs we *want* canonized fit the budget rather
than flagging — in full generality this *is* **GI ∈ P**, still open.

**Isolation is the method, not a surrender — read this before concluding any piece
is hopeless.** The project's recurring move is to wall an apparently-GI-hard step
into a single named component, which makes *everything around it* unconditional, and
*then* to attack that component. Time and again the apparent hardness has turned out
to be an artifact of lumping together cases that are in fact handled separately, and
it dissolves once those cases are carved off — so "isolate, don't close" describes
**where a piece currently sits, never a verdict that it cannot be closed.** The
remaining hardness has been narrowed, by exactly this carving, down to one residual
wall (the hidden-Johnson / Cameron case), which is why the seal's last leg is the
explicit *"or Cameron"* escape. Closing the isolated core is the live target. (Why
the core is *not* GI ∈ P despite first appearances — the carve-out, and the angle to
close it — is set out in
[`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md) §1A.)

---

## 2. Where the project is now (2026-06-10)

> This section is a map; the authoritative current state is the STATUS block at
> the top of each linked doc plus [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).
> Project quality bar: **every Lean theorem must be axiom-clean**
> (`[propext, Classical.choice, Quot.sound]`), full build green.
>
> **★ LIVE THREAD (2026-06-24) — this §2 prose is the pre-affine-closure map and predates it; for the current frontier
> read [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) STATUS + §13.** Headlines:
> **`VO⁻₄(3)` is SEALED** — `ScratchBM3Glue.vo4minus_seal` (axiom-clean `[propext, Classical.choice, Quot.sound]`) proves
> the rigid-or-Cameron disjunction for the minus-form residue modulo cited `{G3}`, carrying **NO `hSmallAutThin`, NO Witt**
> (Witt off the critical path via `…viaIsotropySeparates_wittFree`). Built from `IsotropySeparatesAtBase Qbun T₉` (Lemma
> A + Lemma B + a `Nat`-bridge + a kernel `decide`); four scratch modules (Lemma A + Lemma B (now `IsotropicIncidenceCount` + `ProfileReduction`), `ScratchBM3Bridge/Glue`)
> verified but **not yet ported** into the build (port = the only remaining step for the *instance*). **The live work is
> now the GENERALIZATION** from this single instance to the full schurian residue (`hSmallAutThin` for all small-Aut
> non-geometric schurian rank-3 families) — the forward roadmap is plan §11. **AUDIT-S done** (per-family target =
> `IsotropySeparatesAtBase Q_fam T_fam`; the genuine new obligation is the cited classification *seam*).
> **§11's scoping is now DONE** (AUDIT-S/A/W, **Route 1 chosen**, **GATE passed**); the live work is **plan §13**:
> the reduction chain (**D1 + D2-bridge**) is **landed in `ChainDescent/ProfileReduction.lean`** (axiom-clean), collapsing the
> whole generalization to a **single open predicate `ZProfileSeparates`**, whose core = **D3d = uniform-`q` bounded
> WL-dimension of the affine forms-graphs**. **D3d is now WEIL-FREE** (exact-vs-Weil resolved): the observable is the
> **pair** count `Z_u({t,t'})` (not the singleton — a verified correction), its invariant `χ(det G₂)` is `χ` of a quadratic,
> and the per-pair sum factors into additive Gauss sums (`pairCharSum_factor_gen`).
> **★★★ INCREMENT 3 CLOSED (2026-06-25, all axiom-clean, full `lake build` green, NOT in build.sh):** the pair route's
> per-anchor `c₀ ≤ ¾ < 1` bound is COMPLETE — capstone **`PerAnchorBound.c0_le_threequarters`** (good anchor + `q≥q₀`/`d≥3` ⟹
> `NS = #{t:χ(I_u)=χ(I_v)} ≤ ¾·|V|`), built across 8 new scratch modules on top of `PairForm` (24 lemmas). The reduction
> backbone `ZProfileSeparates → IsotropySeparatesAtBase → seal` is LANDED (`ProfileReduction` + `…viaIsotropySeparates_wittFree`).
> **SINCE THEN (2026-06-26):** the **bridge** (`χ(det G₂)`↔`Z_u(S)`) is CLOSED END-TO-END (`ObservableCountBridge`/`A`/`B`/`C`/`D`/`Z`,
> all B1a wraps + the ℂ per-pair capstone `jointIsoCount_ne_of_chiSep_pair`); **the ENTIRE increment-4 cleanup is now CLOSED**
> (axiom-clean, `BadAnchorCount`/`b`/`c`/`d`) — input `c` (`good_anchor_fail_le_const`: `#{¬sep}≤15/16·|V|`), bad-anchor `β`
> (B-iii `pencilDetPoly_totalDegree_le≤2d` + B-ii `beta_count_closed` + C-corr `beta_full_count_closed`: `β_full·|K|≤(2d+4)|V|+2|K|`),
> C-basis (bridge's `hv/hw`), and **NV** (`GoodAnchorNonvacuity.exists_hgood`, 14 lemmas — `hgood` non-vacuity for nondeg `Q`/`finrank≥2`/
> `|K|≥7`). So `c̄₀<1` and **β is unconditional** modulo family props; no carried existence hypotheses remain in inc-4. The
> **seam** is SPIKED (`ScratchSeam`, modulo mechanical `htransport`); **char-2+Suzuki** spiked (deferred). **FRONTIER = INCREMENT
> 5** (the matching assembly + bridge wiring); the field/seam typing decision is **RESOLVED** (concern #4 lifted bridge+Crux
> to abstract `K`). **#1 corank tightening ✅ DONE** (`q≳d²`→`q≥256`, `ScratchTBoundCorank.c0_le_threequarters_corank`) **and the
> small-q "Route 0" ✅ DONE** (`q≥256→q≥16`, `ScratchTBoundCorank2.c0_le_threequarters_corank2`). **★ The small-q tail is now
> ✅✅✅ COMPLETE (2026-06-27, Route 2):** capstone **`ScratchRoute2.c0_le_route2`** (`NS ≤ (1−1/(4q²))·|V| < |V|`, odd `|K|≥3`,
> `d≥4`, **NO threshold**) closes the per-anchor `c₀<1` bound with no `q`-floor — 4 axiom-clean modules (`ScratchCountTight`,
> `ScratchRoute2Arith`, `ScratchRoute2`). Coverage: odd `q∈{3,5,7,9,11,13}` → route2, `q≥16` → corank2, `q∈{4,8,16}` char-2 =
> separate Arf track. **hK cleanup ✅DONE (2026-06-27, axiom-clean)** — the bridge's carried `hK : gaussSum²·∑ψ(Q)≠0` is
> discharged internally (`GaussCount.gaussSum_sq_ne_zero` + `sum_addChar_quadForm_ne_zero`). **★★★ INCREMENT 5 ASSEMBLED
> END-TO-END + q=p SEAL REACHED (2026-06-27, `AffinePolarSeal.lean`, 8 decls axiom-clean, NOT in build):** the matching assembly
> closes the affine-polar `VO^ε` residue (q=p, `q≳32d`/`q≥256`) to the **`reachesRigidOrCameron` disjunction modulo `{G3}`,
> Witt-free, no `hSmallAutThin`** — capstone `reachesRigidOrCameron_affinePolar`. **NON-VACUITY THREAD ✅DONE (2026-06-27):**
> the seal now **carries** `T.card ≤ 128·(Nat.log 2 ((p^d)²) + 1) = O(d log p)` (log-free block keystone
> `exists_pow_matching_block`), so the slice is non-vacuous — a genuine **quasipolynomial** WL-base. **PORT + RESTRUCTURE +
> DESCRIBE ✅DONE (2026-06-27/28):** the forms-graph pair-route closure is in `build.sh`, **restructured from 27 `Scratch*`
> files into 14 named modules** (`AffinePolarSeal`, `ObservableCountBridge{,K}`, `PencilTBound`, `PairForm`, `FieldGeneric`,
> `BadAnchorCount`, `Coordinatization`, …; rename map in plan §1), full build green ~109s, axiom-clean; `PublicTheoremIndex`
> re-homed with all 223 decls described. The plan doc was condensed 2225→~1000 lines (build history → the archive).
> **★★★ FRONTIER REFRAMED (2026-06-28) — read the plan STATUS "2026-06-28 REFRAME" banner + §1 item 1 + memory
> [[project_formsgraph_wldim_viability_2026-06-28]].** The matching base is `O(log n)` ⟹ **quasipolynomial**, and that is
> essentially tight for any *individualization/WL* method (frame & count base measured `= Θ(d)`, residue `d` unbounded,
> bounded-WL-dim is open math). **BUT route #5 — running the actual canonizer — found it solves `VO⁻₄(q)` in a SINGLE PATH
> (`leaves=1`, `BranchingNodes=0`, full `|Aut|` recovered): forms graphs are huge-`Aut`, so `n^{|T|}` is the WRONG cost
> model and the descent tree is poly.** The polynomial route is therefore the **RECOVERY / harvest route** (`SchemeRecovered`
> / Stage B.0 `coords_determine`), which **sidesteps the open WL-dim problem.** The real cost is the generic automorphism
> harvest: faithfully poly in `n` at fixed `d`, but with a `d`-factor beyond `n` (infeasible at `d=8`); whether that factor
> is super-poly (a new "Witt" harvest is NECESSARY) or high-poly (already poly, Witt = optimization) is **OPEN and gates the
> build**. **▶ GATING NEXT STEP: analyse the cascade harvest recursion's `d`-complexity in `ChainDescent.cs`.** Floor-lowering
> / q=pᵉ / other families are now LOWER priority (they widen the quasipoly result the recovery route would supersede).
> `reachesRigidOrCameron_viaSpielman` = the citable sub-exp fallback.
>
> **★ REMAINING-WORK TRACKER (2026-06-17): [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md)** —
> the one-screen map of everything left (modulo set, citation replacement, buildable infra, the IR solver). Start there
> for "what's left"; the live finding is that the seal's `modulo {G3 + hSmallAutThin + hcatch + hImprim}` collapses to
> **`modulo {G3 + one s(C)/WL-recovery core}`** — the non-G3 hypotheses are facets of one open object, not four gaps.
>
> **★ CURRENT FRONTIER (2026-06-17, handoff) — read this first; the boxes below are older history.** The seal
> `reachesRigidOrCameron` is assembled and axiom-clean. **A1 is DONE** (`CoherentConfig.lean §CC.11`–`§CC.19`); the **A2
> §4c build-order is COMPLETE** (steps 1–5: kill lemma / bound / halving / `BigConfusionCover` obstruction, `§CC.22`).
> Three things landed *this session* on top of that — **read the live frontier doc
> [`chain-descent-a2-potential-route.md`](./chain-descent-a2-potential-route.md) STATUS + §8 + §9 first:**
> 1. **Citation adjustment, Phases 1–2 (route-doc §8.5):** the faithful-direction capstone
>    **`reachesRigidOrCameron_viaSmallAutShatters`** carries `hSmallAutDiscretizes : ¬IsLarge → ∀ over-`B`, ¬BigConfusionCover`
>    (the *literature-true* Babai/Kivva direction) instead of the CGGP-false `hNeumaier : cover ⟹ large`; fed by the
>    citation-free bridge **`not_bigConfusionCover_of_allSingletonFiber`** (`complete ⟹ ¬cover`, `§CC.22`). Old
>    `…viaNoConfusionCover` kept, superseded.
> 2. **Research pass DONE (route-doc §8.6):** `B(n)` is a **threshold ladder** — *polynomial = OPEN* (the rank-3 base case,
>    not even conjectured); *quasipoly* = Babai/Kivva motion (`O(log n)` group base, WL-realization open); *sub-exp `Õ(n^{1/3})`*
>    = Spielman (citable). **No citation makes the seal polynomial.** Corrected cites: Babai **ITCS 2014** (not STOC), motion
>    **n/8**; Kivva **JCTB 164 (2024)**, a *motion* bound not WL-dim; CGGP = **Cai-Guo-Gavrilyuk-Ponomarenko**. **Eberhard
>    "Hamming sandwiches" (arXiv:2203.03687) DISMISSED** — non-Schurian, can't touch the schurian seal.
> 3. **★ THE LIVE FRONTIER = NODE 4 (route-doc §9).** The poly side decomposes by *line-system structure* into five nodes
>    (§9.0); four are carved/foreseeable, the open crux is **node 4 = a primitive, non-geometric, non-conference SRG**.
>    Anchor **`reachesRigidOrCameron_viaNoCover`** (axiom-clean) proves **node 4 (`hShatter` = `∀ over-`B`, ¬BigConfusionCover`)
>    ⟹ polynomial seal, NO largeness citation.** Node 4's best handle is the **multiplicity reframe (§9.6, user's idea):** node
>    4 ⟺ the confusion-cover *multiplicity* `L = (Σ_{|C|>ρc}|C|)/n` is bounded (`O(1)`) — a *computable* quantity (high `L` =
>    thick line system = Cameron, carved; low `L` = poly via a `1+L`-pin cleanup).
>
> 4. **★ THE THIN-SIDE MACHINE + D1/D2/D3 ATTACK ON NODE 4 — LANDED, axiom-clean (route-doc §9.9.6 + §9.9.7; read those).**
>    The cascade is now PROVED end-to-end down to one computable predicate. Chain (`§CC.20b`, `§CC.22b–d`, `§S-gate2`):
>    **`BoundedMinMult`** (bounded `minMult` per over-`B` base) → `boundedConfusionLoad_of_boundedMinMult` (the §9.6 `(1+L)`-cleanup)
>    → `boundedConfusionMultiplicity_of_boundedMinMult` → `…viaBoundedMultiplicity` → **polynomial seal**. **D1 (cover rigidity)
>    DONE** (`§CC.22c`): confusion-set equivariance + `confusionMultiplicity_perm` — cover-load is `Aut`-invariant (`= L` on the
>    vertex-transitive bare scheme). **D3 dichotomy capstone** `reachesRigidOrCameron_viaBoundedMinMult` carries
>    `hSmallAutThin : ¬IsLarge → BoundedMinMult B M` (sharper than `…viaSmallAutShatters`'s zero-load `¬cover`, which the probe
>    showed rarely holds). Non-vacuity anchor `boundedConfusionMultiplicity_univ` (M=n). Seal `modulo {G3 + hSmallAutThin +
>    hcatch + hImprim}`.
>
> 5. **★ ROW-4 PROBE + NODE-2 BRIDGE — LANDED (2026-06-17, route-doc §9.9.8 + §9.9.9).** (a) The **falsifier hunt**
>    (`A2MonovariantProbe.Probe_Row4Sporadics`): the Paulus `srg(25,12,5,6)`/`(26,10,3,4)` + Chang + conference SRGs from the
>    verified Hanaki catalogue, measured for the Lean `BigConfusionCover`/`minMult` on the 2-WL closure — **42 small-Aut
>    non-geometric SRGs (many `|Aut|=1`) ALL shatter at base ≪ √n; 0 falsifiers**, the sharpest support yet for `hSmallAutThin`.
>    (b) The **node-2 rung bridge** (axiom-clean): `boundedConfusionMultiplicity_of_completeBase` (`§CC.22e` — a bounded *discrete*
>    base ⟹ `BoundedConfusionMultiplicity B M`, sharpening the trivial `M=n` anchor to `M=|T₀|`) + `reachesRigidOrCameron_viaCompleteBase`
>    (`§S-gate2` — a δ′-discretizing thin family seals via `…viaBoundedMultiplicity`, no largeness guard). Honest scope: both are
>    **node 3 / pipeline-validation; node 4 (unbounded `s`) is untouched** — no probe reaches it, no constructible witness exists.
>
> **▶ PICK UP HERE — the open content is now ONE predicate: `hSmallAutThin` = "small-Aut primitive residue ⟹ `BoundedMinMult`",
> i.e. thick (`minMult` unbounded) ⟹ large Aut.** This is the WALL: irreducible (rook is thick, needs √n base, saved only by
> large Aut; δ′ gives √n there) = Babai SRG-structure/CFSG = node 4, no known witness. **Method of attack = route-doc §9.9.7.**
> **★ The DIRECT node-4 attack leads are now ALL CLOSED (2026-06-17; route-doc §9.9.10–§9.9.12) — a fresh reader should NOT
> re-attempt these:** the D2 "stable⟹regular partial-geometry" extraction is refuted as a proof route (§9.9.10), climbing the
> k-WL ladder cannot manufacture a gap (`base_k ≥ b(Aut)` ∀k; the c^k Hamming hypergrid's base shrinks with k, §9.9.11), and the
> Hamming-twist/Doob falsifier hunt is negative (§9.9.12) — so the falsifier record is **0 across every constructible probe** and
> the "engineer a thick small-Aut graph" routes (climb WL / twist Hamming) are exhausted. The wall is now sharply "is the WL-dim
> gap `base − b(Aut)` bounded for the small-Aut residue?", with no constructible falsifier and no current technique. The **live
> work is the carve-around**, not a direct node-4 attack:
> **Recommended next builds:** (a) **the remaining node-2 work — a *uniform* rainbow rank** for a parametric affine/FDF family
> via `dominatorReachable_of_rainbowRank` (δ′→discrete→`minMult=0`; `clebschZ4` = the n=16 instance; the just-landed
> `reachesRigidOrCameron_viaCompleteBase` is its seal-level consumer — generalize `clebschZ4_closure` off n=16); (b) **Spielman
> floor** — a `…viaSpielman` capstone making the seal unconditional-modulo-citations at the sub-exponential threshold (Cameron-free).
> Poly discharge of `hSmallAutThin` for the non-geometric core = long-horizon open frontier. `hcatch` → CFI-1992 exchange;
> `hImprim` → block-tower infra (not a citation).
> Substrate/build home:
> [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md); A2 scoping:
> [`chain-descent-cxt-scoping.md`](./chain-descent-cxt-scoping.md); forward payoff (post-node-4):
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md). The boxes below predate all of this.
>
> **UPDATE (2026-06-11) — the live frontier moved; the build home is now
> [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md)** (see the boxed
> "THE LIVE BUILD" pointer at the end of this section; the module-adjoin doc referenced below is its *history*).
> The seal's open `s(C)` content (G2-B) on the **affine cyclotomic slice is now CLOSED in Lean** modulo {G3 + a cited
> cyclotomic 2-separability result, Ponomarenko arXiv:2006.13592 Thm 1.1} — `reachesRigidOrCameron_affineSlice` &c.,
> axiom-clean, build green. **Key correction:** the *non-affine* residue needs **no new Lean infrastructure** — a
> non-affine residue scheme is `orbitalScheme H` (general constructor) and plugs straight into the already-general seal
> capstones; the lone remaining gap is the *discharge* = the open crux (G2-B, uncited for non-affine). **The destination
> is the S-ring / coherent-configuration separability theory** (the general sufficient condition that closes the
> crux for affine *and* non-affine) — the durable build doc is
> [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md); the affine-slice /
> probe history is [`chain-descent-module-adjoin-plan.md`](./chain-descent-module-adjoin-plan.md) §9.
> The prose below predates this and is the pre-affine-closure map.

**The architecture pivot — "de-classing."** Orbit recovery and oracle firing were
being proved *class by class* (CFI odd-degree, then even; schemes rank 2, 3, 4…).
There are unboundedly many classes, so that ladder never converges. The current
approach ([`chain-descent-declassing.md`](./chain-descent-declassing.md)) proves
recovery **non-class-specifically** behind a generic **saturation engine**, with
per-class results demoted to **witnesses** of abstract predicates. One theorem
(`theorem_2_HOR_of_pPolynomial`) now covers the entire **metric / distance-regular
family** (cycles, Johnson, Hamming, all DRGs). The two oracles (cascade + linear)
are **folded into one** recovery-based harvest; their old distinction is now a
*depth* distinction.

**Built and axiom-clean** (see the docs' STATUS blocks for specifics):
- the canonizer-correctness substrate — direction-invariance (`warm_6_2`) and the
  descent **spine** (`spine_branch_independent`) (top-level `ChainDescent.lean`);
- the **saturation engine** and the de-classed scheme family (`Saturation.lean`,
  `Scheme.lean`);
- the **unified oracle** — `matchOracle` / `matchOracleSeq`: soundness
  unconditional, completeness reduced to a single **depth witness**
  (`CascadeOracle.lean`, `Cascade.lean`);
- **Part A** — the cross-branch stabilizer-chain object (`StabilizerAt` as a
  Mathlib `Subgroup`) with both harvest seams: **soundness** and **completeness**
  (`closure gens = StabilizerAt` under a coverage witness), plus the full
  `order = ∏ basic-orbit sizes` (`Cascade.lean`, "Part A");
- the **de-classed coverage** — `coversOrbits_of_realizers` (general, non-abelian:
  the coverage witness from per-level **path-fixing realizers**, *no* group-structure
  hypothesis — abelian *or* schemes/Cameron) with `coversOrbits_of_residualInvolutive`
  as its exponent-2 corollary (the entire `Z₂^d`-residual class in one theorem,
  sidestepping the `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` structure theorem) (`Cascade.lean`);
- the **CFI cross-branch harvest** (CFI-cov.1–4) — gauge flips → the residual
  vocabulary, the cycle-space `Z₂^β`, the gauge-flip group homomorphism, and the
  full discharge in the **base-resolved regime**: `cfi_residualInvolutive` (Lemma A
  + Lemma B: a residual fixing a gadget-separating `P` is exponent-2) ⇒
  `closure {involutive residual auts} = StabilizerAt S` and `|Aut_S^P| = ∏
  basic-orbit sizes` (`cfi_closure_eq_stabilizerAt_of_pSeparates` /
  `cfi_card_stabilizerAt_of_pSeparates`, `Cascade.lean` / `CFI.lean`).

**The conservation finding that set the current direction.** The within-cell
discretizing oracle was *proven unable* to harvest a multi-step moved orbit
(`lockstep_disc_imp_stab_trivial`). So multi-step hidden symmetry (CFI gauge
twists, `tw ≥ 2`) **must** be harvested **cross-branch** — which is why Part A (a
group object to fold automorphisms into) exists.

**The mechanism (cross-branch harvest).** `coversOrbits_of_realizers` reproduces
*any* residual group — abelian or non-abelian — from the refinement-computable
harvest, with the CFI exponent-2 case a corollary (CFI-cov.4 complete in the
base-resolved regime; C# canonizes CFI(K₄–K₇)). The general polynomiality capstone
`crossBranchHarvest_reproduces_residual` / `autP_reproduced_of_visibleRealizers`
(`Cascade.lean` Part A) reproduces the residual **group and order**, modulo a single
recovery witness. **Localisation** — the gap to full polynomiality — is the
*polynomiality* layer: coverage correctness is unconditional; recovery makes the
harvest refinement-computable (`recoverableByDepth_pPolynomial` exports the metric/DRG
family); per-level recovery is the substrate-conditional WL-dimension discriminator.

**The goal is one theorem — "reaches a rigid or Cameron residual" — now a conditional
seal `modulo {G3 + G2-B}`.** The abstract capstone `reachesRigidOrCameron`
(`Cascade.lean`) wires the trichotomy `¬IsPrimitive ∨ ¬NonCascade ∨ Cameron`; every
rank-≥3 schurian residual is `ReachesRigid ∨ IsCameronScheme`. Landed axiom-clean: leg B
(`AbelianConsumed`, citation-free), depth-graded recovery (G1a), the imprimitive block
leg (G2-A, *earned* `SchemeBlockRecovered`), and the primitivity bridge
`isPreprimitive_iff_isPrimitive`. The **largeness** antecedent is now carried honestly
(`LargenessBridge` identity); the earlier vacuous *no-fusion* "derivation" was excised
(2026-06-07). The "or Cameron" half is **Cameron-hard, not GI-hard** — *whether* a
non-abelian obstruction arises is ≡ **GI ∈ P** (out of scope); *classifying* one as a
Cameron section is the in-scope, finite target. The adversarial fusion battery ran all
three tiers: **no genuine fusion is constructible** — it splits into a separable case
(Tier-0-handled) and a non-decomposable case that is empirically a genuine Cameron
section (no third species). The unconditional block-visibility route to primitivity was
refuted (Shrikhande, depth-graded).

**The single open proposition — G2-B** (2026-06-10, axiom-clean, build green): a
*primitive, small, non-abelian, non-recovering* residual, plus the cited
`PrimitiveCCClassification` (G3, Babai/Sun–Wilmes, solid rank 3/4). Both empirical
falsifiers — the Hanaki–Miyamoto catalogue and the affine `ΓL(1,2^d)` sweep — returned
**0 G2-B witnesses** (empirically strong, uncited). The **2026-06-10 rewiring** sharpened
what G2-B requires: a step-back (recovery depth is `O(log n)`, not `O(1)`, with the
growth living entirely in the *handled* legs while the G2-B residue stays flat, depth ≤ 4)
showed the old recovery predicate over-required — it folded the unbounded **IR-core**
(the multipede term) into the seal. The conservation split
`recovery_depth = base(G) + s(C)(G) + IR_core(G)` (`stablyRecoverable_iff_symmetric_and_bases`)
+ `reachesRigidOrCameron_viaSymmetricRecovery` (keyed on the IR-core-free
`SchemeRecoveredWhileSymmetric`, root group reproduced from the symmetry phase *alone*)
move the IR-core to the **second guarantee** (flag-allowed). The seal's open content is
now the bounded, empirically-`O(1)` **`s(C)` term** (`SelfDetectsWhileSymmetric`) —
strictly weaker than the old obligation. Full chronology and every gap:
[`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md) (authoritative),
[`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.7.5,
[`chain-descent-declassing.md`](./chain-descent-declassing.md) §9.

> **⟶ THE LIVE BUILD (2026-06-11): [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md).**
> The seal-bridge gate reduced the unconditional seal to **two coupled obligations** — (A) `Separable` (Ponomarenko
> Thm 4.1) and (B) the transport `Separable ⟹ recovery` — both needing the same **general coherent-configuration
> separability substrate** the project lacks; the group base (C) was found *free*, and (A)+(B) is now the *whole*
> remaining job. That substrate build (option (i), chosen to pursue the long-standing unconditional goal) has its own
> **durable, self-contained working doc** — read it for the target, the inlined math, and the staged plan. The
> affine-slice / module-adjoin history (the crux `PowAffineSeparates`, the semilinear `ΓL₁` gap, the probes, the
> non-affine NLS residue) is in [`chain-descent-module-adjoin-plan.md`](./chain-descent-module-adjoin-plan.md) — now
> background, superseded as the build home.
>
> **UPDATE (2026-06-12) — a SECOND, citation-free checkpoint now bypasses (A)+(B).** The δ′ dominator-closure engine
> (`reachesRigidOrCameron_viaDominatorClosure`, `CascadeAffine.lean §S-gate2`) reduces the seal to a single
> combinatorial hypothesis `hclo : ∀ v, DominatorReachable S T v` (the `c=1` forced-triangle closure of a bounded
> base exhausts Ω) — **carrying only {G3 + `hImprim` + `hclo`}, no Thm 4.1 citation and no catch-up**. So (A)+(B) is
> now *one* of two paths, and the lighter one. The lone open math is the **single-base closure** (`hclo` for the
> residue family), reframed group-theoretically as `Stab(α)·γ ∩ Stab(β)·γ = {γ}` propagating from a base
> (`dominatorReachable_step_of_stab`). See the live build doc's STATUS block + §5 Stage 3 (δ′ route) for the plan.

**What NOT to do (a proven boundary, 2026-06-10).** Do not attack G2-B by exhibiting it as a **block / scheme
congruence**: `intraCellRelations_eq_singleton_zero_of_primitive` proves the intra-cell block route *identically
vanishes on the primitive floor* (a primitive scheme forces it to `{0}`), so it discharges **only** the imprimitive
case (already handled by `hImprim`). The genuine G2-B is a *non-congruence amorphic WL-fusion* (the Clebsch `S₃`)
that no closed-subset object captures; the live route is the **forward / counting** crux (a base-homogeneous
separability gap broken at base+O(1) extra individualizations), not a block construction. **Note — caveats the
handoff sharpens** ([`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md), the authoritative state):
(1) the largeness bridge is **carried, not derived** (the old vacuous "derivation" was excised, §2–§3 there); (2)
**no re-keying of the rigid predicate closes the seal** (§4.0 there) — closure ⟺ G2-B empty.

---

## 3. Reading order

Read in this sequence; each doc has a STATUS block (its current state) at the top.

**Core (read in full, in order):**
1. **This doc** — the idea + current state.
2. [`chain-descent-strategy.md`](./chain-descent-strategy.md) — the algorithm as a
   whole and the correctness/polynomiality requirements; the propagation substrate.
3. [`chain-descent-calculator.md`](./chain-descent-calculator.md) — the **oracle**
   (the hardest component): the stabilizer-chain model, the hardness map, the
   T-A/T-B/T-C decomposition. *Its §5–§7 describe the pre-declassing two-oracle
   design and are explicitly legacy — read them for the soundness story, not for
   how the oracle now fires.*
4. [`chain-descent-declassing.md`](./chain-descent-declassing.md) — **the current
   architecture**: de-classed recovery + the unified oracle. This supersedes the
   two-oracle / order-model framing in docs 2–3 where they differ. Its §9 is the
   live frontier.
5. [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) — **Part A**,
   the cross-branch stabilizer-chain object and the current work thread.
6. [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) —
   the theorem index; densest file, the ground truth for *what is proved*. Read in
   full. **It is well over 1000 lines — too large for one `Read` call (and even
   300-line pages can exceed the token cap, the rows are dense). Page through it
   with `Read` `offset`/`limit` in ~150-line chunks. Do NOT substitute a `grep`
   during onboarding: a prior summary or this onboarding's prose is exactly the lossy
   compression this file is the ground truth for — confirming a few names with
   `grep` is not reading it, and the gap is invisible unless you read it.**

**Side reading, pulled in as the core docs point to it** (each is a deep-dive or
witness layer, not onboarding):
- cascade oracle → [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
- linear oracle → [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
- orbit-recovery witness theorems → [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
  (the two load-bearing per-class witnesses, Theorem 1 + Theorem 2; the long
  historical narrative is archived)
- deferred decisions → [`chain-descent-deferred-decisions.md`](./chain-descent-deferred-decisions.md)
- harvest-window lemma → [`chain-descent-harvest-window.md`](./chain-descent-harvest-window.md)
- the wall (hidden Johnson) → [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
- oracle-capability seal + **the Exhaustive-Obstruction Lemma (the current forward thread, 2026-06-05)** →
  [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) — the "or Cameron"
  half of the goal; Approach 3 (Cameron-free scheme leg) active — scheme primitivity, the imprimitive ⟹
  refinement-visible bridge, and the group-side `isPreprimitive_iff_isPrimitive` bridge landed; the
  refinement-side decomposition deferred (substrate-conditional), capstone cited
- **THE SEAL HANDOFF — current state + all the gaps to "consumed-or-Cameron" (THE CURRENT HANDOFF, 2026-06-07)** →
  [`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md) — the authoritative handoff. Records the seal's
  state after the **vacuity correction** (the old `∃ gens, closure = SchemeAutGroup` rigid predicate was trivially
  true; replaced by the visible-realizer `SchemeRecovered`), and the four gaps: G1a depth-graded recovery, **G1b
  leg B (abelian) missing — the most actionable**, G2 the leaks (open `s(C)` frontier), G3 the citation. Start here
  for *any* gap. **Subsumes** the Route B handoff below.
- **Route B — the imprimitive branch (SUPERSEDED by the seal handoff; read for the G2-A blow-by-blow only)** →
  [`chain-descent-routeB-handoff.md`](./Archive/ChainDescent/chain-descent-routeB-handoff.md) (archived) — its capstones were found vacuous (see its
  top correction note); the genuine, kept pieces (`hfiber_of_fiberVisibleRealizers`, the conditional chain) are
  catalogued in the seal handoff §4 G2-A / §5.

**Paper-stage / planning docs** (theoretical targets, not yet formalized — read
only if working that thread): `chain-descent-tier3-decomposability.md`,
`chain-descent-tier3-tractable-buildout.md` (its Part A landed → schreier-sims;
Part B is the open roadmap), `chain-descent-tier3a-cascade-composition.md`
(+ `-tier3a-b1-build-plan.md`),
`chain-descent-extended-twist-viability.md`,
`chain-descent-abelian-sufficiency-handoff.md`,
`chain-descent-cfi-gauge-discharge-plan.md` (the CFI-cov.4 gauge-nut build plan; CFI harvest landed; the
base-resolved hypothesis re-wired 2026-06-06 from the vacuous `PSeparatesGadgets` onto the colour-model
`CellSeparatesGadgets`, carried as a witness — the orthogonal visible/cascade leg),
`chain-descent-fusion-battery-plan.md` (the no-fusion battery + the route to *deriving* leg C's largeness).

**Temporary handoffs** (consumed — retained only for build conventions + Lean gotchas, not the work thread):
`chain-descent-partA-handoff.md`. **Its §4 "next target" is obsolete** (that thread — de-classing →
CFI-cov.4 — is done; see [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) §7). Read it
only for §1 (build/verify/doc-sync conventions) and §2 (Lean gotchas).

**Archived (consumed / superseded / historical — moved to [`Archive/ChainDescent/`](./Archive/ChainDescent/), not in the live `docs/` listing):**
`chain-descent-a2iii-plan.md` (A2-iii resolved negatively — Shrikhande refutes unconditional block-visibility),
`chain-descent-routeB-handoff.md` (superseded by the seal handoff; G2-A blow-by-blow only),
`chain-descent-tier2-lean-plan.md` (goal achieved — the Tier-2 axioms it set out to discharge are landed).

---

## 4. The code

Two sides, both under the repo root. Build commands are in [`../README.md`](../README.md).

**C# — the experiment bed** (`GraphCanonizationProject/`). Strategies are tried
here first. `ChainDescent.cs` + `CanonGraphOrdererChainDescent.cs` are the
canonizer; the oracle sits behind the `ITransversalOracle` seam. Tested in
`GraphCanonizationProject.Tests/` (an isomorphism-stability bed + the CFI hard
cases). C# already canonizes CFI(K₄–K₇).

**Lean — the proofs** (`GraphCanonizationProofs/`). The active library is the
**`ChainDescent/` module split**; the top-level `ChainDescent.lean` holds the
direction-invariance and spine invariants that everything imports.

| Module | Proves |
|---|---|
| `ChainDescent.lean` (top level) | direction-invariance `warm_6_2`, the descent **spine** |
| `ChainDescent/Saturation.lean` | the generic saturation engine (`exists_iterate_isFixed_within`) |
| `ChainDescent/Scheme.lean` | the de-classed metric/DRG family (`theorem_2_HOR_of_pPolynomial`) |
| `ChainDescent/Cascade.lean` | Leg A recovery; **Part A** stabilizer-chain object; the seal capstones + leg B + block/depth-graded recovery + §13a single-base recovery |
| `ChainDescent/CascadeAffine.lean` | the depth-`k` scheme-separation engine (§13b/§13c) + the Phase-2 affine beachhead (`affineScheme`, Frobenius, the cyclotomic `s(C)` machinery + the conditional affine-family seal capstones) + the **§S-bridge/§S-gate/§S-gate2** seal wiring of the separability theory (the PV-Thm-3.1 warmRefine bridge B1–B5; the general-CC pointed transport + the citation checkpoint `reachesRigidOrCameron_viaExtensionSeparability`) — split out of `Cascade.lean` (leaf; carries the finite-field imports) |
| `ChainDescent/ClebschConcrete.lean` | the **concrete ℤ₄² amorphic-NLS Clebsch scheme** (hard-coded `AssociationScheme 16` from its colour matrix, axioms by `decide`) + **the first non-affine δ′ closure in Lean** (`clebschZ4_closure` / `clebschZ4_discrete`: `b(X) ≤ 2`, the seal's `hclo` discharged for a real non-affine primitive G2-B residue; axiom-clean, no `native_decide`) |
| `ChainDescent/Separability.lean` | the homogeneous separability substrate: the PV-Thm-3.1 `c=1` forced-triangle calculus (§S.1–§S.16: valencies, indistinguishing number, `saAdj`/`transport`, the sparse theorem's counting lemmas) + the §S.17 `AlgIso`/`Separable` layer |
| `ChainDescent/CoherentConfig.lean` | the **general (multi-fiber) coherent-configuration substrate** (the live build's Stage 0–2): the `CoherentConfig` type, general `AlgIso`/`Separable`/`SeparablePointed`, the Thm-4.1 predicates + cited `Theorem41Statement`, the **constructed point extension** (§CC.8) and the pointed transport core (§CC.9) |
| `ChainDescent/CascadeOracle.lean` | the unified `matchOracle` / `matchOracleSeq` |
| `ChainDescent/LinearOracle.lean` | the linear (abelian/CFI) oracle |
| `ChainDescent/CFI.lean` | CFI gadgets, gauge flips, the `Z₂^β` cycle space, CFI-cov |
| `ChainDescent/Group.lean` | permutation-group scaffolding |

For the Lean↔C# modelling correspondence, the TC-relegation decision, and the
model objects/axiom, see [`GraphCanonizationProofs/ChainDescent/README.md`](../GraphCanonizationProofs/ChainDescent/README.md).
For *what is proved*, see [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).
