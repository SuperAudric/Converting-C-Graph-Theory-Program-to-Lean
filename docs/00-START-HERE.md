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

## 2. Where the project is now

> # ▶▶▶ READ [`chain-descent-handoff-2026-07-14.md`](./chain-descent-handoff-2026-07-14.md) FIRST
>
> It is the **authoritative** state of the canonizer track and supersedes this section wherever they disagree.
> The one-paragraph version:
>
> **①, ② and ③ all have real theorems about the real object, and every remaining gap is a *firing* gap.** The
> canonizer (`Descend.descend`) is sound, iso-invariant, complete, and — once **stall-guarded** (`Stall.guard`) —
> a **single path of ≤ `n+1` nodes on every input** (so no exponential blow-up; the *node count* is unconditional,
> the wall-clock is polynomial iff the supply's per-call cost is — see handoff §3), flagging exactly where neither
> resolver can act. The residue (`Residue.Residue`) is
> **defined** as the complement of a positive capability predicate, so it is not an asserted atom and it **shrinks**
> whenever a resolver gets stronger, with no re-proof.
>
> **▶▶▶ THE TARGET (restated 2026-07-18, user steer): a COMPLETE canonizer** — every input handled,
> polynomially; the flag provably never fires. Poly-or-flag is the *scaffold and measurement instrument*; a
> named residue is only the recorded-exhaustion fallback. **The live plan + full gap enumeration =
> [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §0–§2** — read it right after the
> handoff.
>
> **The object of record** (2026-07-19, extended later the same day): the **fused resolver-aware descent** —
> encode-free refiner + `selNode` (true mutual-stall flag) with the **holonomy key** (`HolKey.lean`, force)
> and the composed consume supply `foldSupply ++ deckSupply ++ deck2Supply ++ **kernelSupply**`.
> `Publication.lean`'s `canonForm?` **is now this real object and the whole ① trio is proven there
> axiom-clean** (no `sorryAx`, zero glue); the remaining `sorryAx` in `canonizer` = ② (fillable per fixed
> cost pin) + ③ + non-vacuity.
>
> **The consume roster and its measured reach** (each landed with guards; do not re-derive — handoff §1
> table + fold-tower STATUS + [[project-c3-kernel-supply-2026-07-19]]): matching (`matchSupply`, depth-`d`
> `deepMatchSupply`/`partialMatchSupply`, pruned/tree-pruned variants), structural folds (`foldSupply` F2a),
> propagation (`deckSupply` F2b — any generator order), second-seed propagation (`deck2Supply` F2c —
> coupled-chaining gauges like the twisted triple `t3`/`ut` AND independent wreath gauges via the
> load-bearing identity-default, measured `wr3`), and the **F₂ kernel supply** (`KernelSupply.lean` C3a
> tranche 1 — recovers CFI cycle-space gauges by structural rail extraction + Gaussian elimination; measured
> on `mp7`, the Fano multipede: the [7,3,4] simplex code recovered, the whole gauge consumed in one call;
> **✅ tranche 2 COMPLETE and IN THE RECORD** since 2026-07-19 — `KernelGauss`/`KernelFlip`/`KernelRef`/
> `KernelTransport`). ★ Note the ① shape: `kernelSupply` is the first record supply that is provably **not**
> `GensEquivariant` (pivot-order-dependent basis = trap #7); ① rides `OrbitPrune.SameOrbits` against an
> equivariant set-level reference, so the executable object carries zero ① obligation — the recommended
> shape for any future supply that must make an internal choice.
> The **frontier**: **C3b `deepenSupply`'s ①c — R1, the WL-completeness crux** (base-graph recovery + lift
> was the earlier C3b plan, now SUPERSEDED by the deepen supply; the C3b state is the CURRENT-STATE block just
> below + the tracker's "▶ CURRENT FRONTIER"), then T1 per-family localisation, F3b Smith/CRT, the W1 recovery
> poly program, and the W2 wall — in that order (remaining-work §2).
> **▶ W2 now has a dedicated, substantially-BUILT track: `docs/chain-descent-w2-solvability-route.md`** (retargets the
> wall from "linear" to *solvable* `Γ`; Tier-A localization + Tier-B reduction + C3-Recover R-a + R-c-nonabelian + the
> extraction bricks L1–L3 landed, **7 `Gauge*.lean` modules**, axiom-clean, in `build.sh`). ★ The **Luks sharpening**
> (§3a) makes Luks-poly a genuine theorem for bounded local `G₀`; L1–L3 (§3b) reduce the whole *solvable* corner to
> **one carried obligation L4** (`Recover` → explicit per-layer linear systems, shared with `ForcingModel.bridge`) —
> **L4 unconditional ⟹ solvable corner empty**, leaving only the non-solvable wall. **Read that doc's ▶▶ HANDOFF block
> (top of STATUS) to pick it up.**
> **✅ C3b LANDED (tranche 1) 2026-07-20 — `ChainDescent/DeepenSupply.lean` `deepenSupply`, in `build.sh`.**
> The constructor for **base** symmetry — what survives after `kernelSupply` certifies the gauge, and what no
> propagation-shaped supply reaches (girth 6 ⟹ a seed forces 1 vertex of 42, at any number of seeds). Ported
> from the C# `HarvestTwists`: **stop propagating — replay a deepening and compare footprints.** Deepen an
> anchor to an all-singleton footprint recording the chosen cell ids; replay that id sequence from every other
> representative; match footprint colours on the coupled component; `permOf` + `IsColAut` verify.
> **MEASURED (`PerformanceTest` §16):** branch cell 28, **756 = 28×27 verified gens (ALL anchors)**, and the gadget
> cell (28) *and* foot cell (14) each collapse to a **SINGLE ORBIT** = the C3 acceptance. C# cross-check on the
> same object: |Aut| = 1344 = 8 × 168 (`FanoMultipedeProbe.cs`).
> **WARNING — ①c needs ALL ANCHORS: single-anchor is measured FALSE** (the **`G8` falsifier**: five
> relabellings give profiles `[2,2,2,2,4,4,4,4]` vs `[1,1,2,2,2,2,2,2]`; `mp7` can't detect it — it fires
> totally, profile `[28]`, so an equivariance falsifier must be PARTIALLY-firing). The landed supply quantifies
> over all anchors.
>
> **▶▶▶ C3b ①c — CURRENT STATE (2026-07-23, TRACK A): read [`chain-descent-deepen-supply.md`](./chain-descent-deepen-supply.md)
> STATUS (authoritative, self-contained).** **`deepenSupply`'s ①c is CLOSED modulo `{Amenable}` ONLY**
> (`deepenSupply_guarded_canonizer_direct`, axiom-clean, full build green). `deepen` now WHOLE-GRAPH-discretizes,
> making `[DISC]`/gate/termination STRUCTURAL (`deepen_discrete` / `gate_of_discrete` / `deepen_succeeds` via the
> `ncol` colour-count measure) — this **ELIMINATED `AnchorFires`** (the last firing hypothesis). The **entire
> reference/R1/R2 apparatus is REMOVED from the build** (`DeepenRef`/`DeepenRefTransport`/`DeepenR1` parked;
> `deepenRefSupply`/`DeepenRefInExec`/`ExecRecoversKMinusCell` deleted; `imgFun` moved to `DeepenSupply`). **The
> SOLE remaining ①c condition, `Amenable`, IS `CellsAreOrbits`** (`CascadeOracle`) — free at discreteness
> (`cellsAreOrbits_of_discrete`), so NOT a GI∈P assumption; its failure is an *exposed* rigid decision
> (`not_amenablePath_imp_rigidObstruction`). **`deepenSupply` stays out of `Publication.canonForm?` until
> `Amenable`/`CellsAreOrbits` totality is populated per family (T1); THE ACTIVE TRACK IS NOW THE RIGID SEAL**
> ([`chain-descent-rigid-seal.md`](./chain-descent-rigid-seal.md) — READ ITS STATUS), which discharges `Amenable`
> per family AND is the other seal. **✅ THE ALGORITHM-R SCAFFOLD + THE FULL `gen`-REDUCTION CHAIN (A)–(D) LANDED
> (2026-07-24, axiom-clean, gate green ~97 modules — authoritative detail = rigid-seal STATUS/§8.2/§10):** the force
> key `leafColKey` + composite `compKey` (`RigidSeal.lean`); **P1** (`ForcingCircuits`), **P3-I**
> (`RigidSolverInterface`), **P3-Sound** (`RigidSolverSound`, soundness FREE ⟹ `①` = one canonical labelling `gen`),
> **P2** (`ForcingModel`), **P3-F₂ core** (`RigidSolveF2`); and the **`gen` chain**: **(A)+(B)** `RigidRREF.lean`
> (canonical F₂ RREF + `rrefCanon_eq_of_span_eq` = RREF is a canonical fn of the subspace), **(C)** `RigidFrame.lean`
> (`framedRREF_transport` = χ-rank frame ⟹ σ-invariant), **(D)** `RigidGen.lean` (`genEquivariant_genOfRef` + capstones
> ⟹ the whole `compKey` `①` closes on `RefEquivariant ref`). ⚠⚠ **The earlier "`SmallAutThinAt` = `hSmallAutThin` at
> the seam" identity is RETRACTED** — `hSmallAutThin` is a STATIC Route-C scheme predicate (false on consumable
> cases); the canonizer's residue is the DYNAMIC `¬HandledS`; they join only via the unbuilt W1 (NOT `↔`). The
> mixed-cell/fusion question is SETTLED — the "Progress" predicate is the already-built sel-rewrite
> `Select.HandledS`/`NodeResolved`. The (A)–(D) chain reduced the rigid linear `①` to *"supply a discrete equivariant
> `ref`."* **▶▶ THE CONCRETE `ref` + `Recover` ARE LANDED (2026-07-26, `RigidRefine.lean`, steps 1–9E, axiom-clean,
> gate green ~97 modules) — authoritative = `chain-descent-rigid-seal.md` STATUS + §8.2.** **Object of record = the
> MIXED-NATIVE aggregate reader `readAgg`** (sorted encoded SET of per-frame RREF-column signatures over an equivariant
> frame set): **① `readEquivariant_readAgg` UNCONDITIONAL** (from `FramesEquivariant` alone — NO uniqueness/rigidity) +
> **② `readSeparatesRigid_readAgg` from `AggFaithful`** (aggregate-indistinguishable ⟹ AUTOMORPHIC; gauge ties provably,
> non-aut separates). **Seal for the mixed reader = `{FramesEquivariant, AggFaithful}`.** ⚠⚠ **DO-NOT-RE-DERIVE:** (1)
> the single-bit `refineByFrame` (Route B′, steps 1–5) does `①` but **cannot discretize** (≤2 classes/cell ⟹ fails the
> multipede); (2) an equivariant order PERM exists ONLY on rigid inputs, so the single-`ord` `structRead` path (steps
> 6b–9C) is **whole-node-rigid = the `ker=0` anchor**, superseded by `readAgg` for the mixed residue; (3) a poly (`<n!`)
> equivariant frame set needs a structural discretizing order = the LINEAR solve (WL won't). **FRONTIER: the POLY frame
> set** — ✅ P1 interface (`seedFrames`/`framesEquivariant_seedFrames`/`card_seedFrames_le`) → ▶ P2 concrete poly seed +
> discretizing solve-completion `orderOf` (carried per-family) · P3 `AggFaithful (seedFrames …)` per-family → P3-ring
> (`Z_{2^k}`) → P4. ⚠ user-flagged open Q (deferred): the rigid solver likely covers MORE than linear residues. Everything from 2026-07-18 through 2026-07-22 below (base-recovery/lift, R1/R2, `deepenRefSupply`,
> `hL1`/`K∖cell`, WL-completeness framing) is **SUPERSEDED PROVENANCE**. Measured (`DeepenStrengthProbe.cs`, 39
> rows): starvation = 0, every checkable row COMPLETE, Chang-A 384/384 (survivor = fusion), expander multipedes rigid.
> ⛔ `KernelBase.lean` (base recovery + lift) **parked** — not in `build.sh`.
> **⚠⚠ STANDING TRAP: `Consume.gens` returns UNVERIFIED candidates** (junk is filtered by `Consume.verified`
> downstream) — any probe reading it directly MUST filter by `IsColAut` first; reading it raw produced a wrong
> "liftability = kernel of `Aut(base) → H¹`" diagnosis that is RETRACTED.
>
> **⛔⛔ SETTLED — do not re-propose a STABILIZER-CHAIN supply.** It must pick a **vertex inside a cell**, and cell
> members are *precisely* what 1-WL cannot distinguish ⟹ no iso-invariant function picks one ⟹ **`①b` AND `①c` fail**
> (both route through `Stall.StallEquivariant`), not merely the flag. ⚠ **Distinguish:** choosing a **cell** *is*
> canonical (`targetColour` transports), so the resolver-aware *selector* of §6.1 is valid — it is the *within-cell
> vertex* pick that is illegal. (Likewise **do not port `matchOracleSet`/`matchOracleSeq`**: the project's own
> `lockstep_disc_imp_stab_trivial` refutes them.)
>
> **⛔ Two claims made and RETRACTED this session — do not re-derive them** (handoff §5):
> 1. *"A perfect key cannot exist"* — **circular** (it presupposes GI ∉ P). Correct: **a perfect key *is* GI ∈ P** —
>    the route's **target**, not a barrier. **Any "X ⟹ GI ∈ P, therefore X is impossible" argument is BANNED.**
> 2. *"Fusion is dissolved"* — **wrong**. Fusion is a dependency of **exposure** (a ring's rigid decisions surface
>    only after `{root, direction}` are consumed; Chang-A has 24 automorphisms certifiable only *after* rigid
>    decisions), **not** a meta-product over orderings — and it has a live bite (§6.1 above).

### 2b. The older map (2026-07-12) — kept for context

> **This section is a map. The authoritative current state is the STATUS block at the top of each linked
> `chain-descent-*.md`, plus [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) for
> *what is proved*. Quality bar throughout: every Lean theorem axiom-clean `[propext, Classical.choice,
> Quot.sound]`, full build green.**

**The model — one INTERLEAVED engine, not two sequential seals.** The canonizer is a **stepwise alternating fixpoint**
`…∘phase2∘phase1…` ([`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11.11; compile
target [`Publication.lean`](../GraphCanonizationProofs/Publication.lean)): at each pairwise vertex relation the **oracle
consumes** it via a *verified* automorphism, or the **rigid solver forces** it if it lies in the current linear
row-space, or it is **deferred**; 1-WL refine between; the solver's kernel feeds *de-fused* symmetry back to the oracle.
The run is **done at mutual stall** — neither move applies — and the flag fires exactly there. The two "seals" are the
two *moves* of this one engine (symmetry consume / rigid force), isolating the **same wall** `hSmallAutThin` (≡
rigid-GI∈P). A purely sequential `phase2 ∘ phase1` is only the **fusion-free special case**.

> **▶ Why the model is interleaved, not sequential (2026-07-12).** The earlier plan ran a standalone **Algorithm A**
> (assume-VT / confinement) to a rigid residue, then handed it to **Algorithm R** — the "RRU" one-shot handoff. That
> **crash-landed on fusion**: Algorithm A pruned on a *threshold-gated* flag without verifying an automorphism, so a
> conditional symmetry *fused* with a rigid decision (Chang-A) could be mispruned — and its soundness needed a
> fusion-mildness theorem that does not exist. Interleaving fixes this structurally (consumption is verify-gated ⟹ a
> rigid residue *stalls*, it is never harvested), de-fuses the abelian case constructively via the solver kernel, and
> narrows the residual risk to "**no non-abelian fusion in a rigid medium**" (IR §11.14) — carried like the seal's "or
> Cameron", not load-bearing on a missing theorem. **RRU is retired** (superseded by the mutual-stall fixpoint); the
> typed `Phase2.Solver` contract in `Phase2Handoff.lean` survives, its `RRU` reachability apparatus does not.

> **▶ PRIORITY LEAN TRACK: the MIXED composition — [`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md).**
> Almost every real residue is **mixed** (consume some symmetry, force/branch the rest). The current Lean `canonForm?`
> is a single deterministic path with no branching/oracle/phases (source-verified) — so the priority is building the
> **branching, interleaved descent** and proving its spec **sound ∧ iso-invariant** (Stage 0a landed: `complete_of_isCanonicalForm`
> makes completeness free). **✅ DONE 2026-07-13** — the branching descent (`Descend.lean`) is built AND proved sound ∧
> iso-invariant; see the trio note below. Composition = a **fold over alternation depth**, not one append.

**What is built, axiom-clean, in `build.sh`.** The canonizer-correctness substrate (direction-invariance `warm_6_2`,
the descent spine `spine_branch_independent`); the **cross-branch harvest** machinery (Part A stabilizer-chain object,
`coversOrbits_of_realizers`, the CFI exponent-2 discharge); **Route C** — all four form families sealed
(`reachesRigidOrCameron_{affinePolar,alternating,halfSpin,suzuki}`, modulo scoped citations), the forms-graph residue at
**quasipolynomial** (`…affinePolar`) with sub-exp floor `…viaSpielman` — a genuine result, **parked off the headline
path**; the mixed-composition **Stage 0a** framework (`ChainDescent.CanonicalForm`); ①a `canon_sound` + the ② cost side
(`descentCost_le`, `≤ n⁴`) against the shared capped object; the `Phase2.Solver`/`Sound`/`IsoInvariant` **contract**
skeleton (`Phase2Handoff.lean`). Plus the **whole mixed-composition stack**: `Descend` (the object) → `Refine` (the
encode-free refiner) → `Consume` + `Force` (both resolver instances) → `PerformanceTest` (the regression gate). The **C#
rigid solver is complete for handoff** (`Option2Solver.cs`, recover→solve→emit→verify, ring-general; every B-step landed).

> **▶ The rigid solver's Lean witness is NOT "P1–P4" any more.** Under the resolver contract, the force route's **only**
> ① obligation is **`KeyEquivariant`** (`Force.lean`): supply a solve-derived vertex key and prove it commutes with
> relabelling. **P1/P3 keep their full content but move from ① to ②** (they determine *how much the key separates* =
> the firing rate). See IR §11.12's re-basing banner before starting that build.

**★★★ THE CORRECTNESS TRIO IS DISCHARGED (2026-07-13) — `ChainDescent/Descend.lean`.** The Lean canonizer is no longer a
single deterministic path: `descend` is **the object** — a *computable*, resolver-parameterized **branching** descent in
the cost monad — and **`isCanonicalFormOpt_canonForm?`** proves it **sound ∧ iso-invariant**, hence a *complete*
isomorphism invariant with an iso-invariant flag. **①a, ①b, ①c all hold for the real object**, modulo exactly two carried
hypotheses (`RefineEquivariant`, **`NarrowTransport`**). It **runs** (`#eval`): the executable and the cost are just the
`value` / `cost` projections of that one definition. It is also proved **NON-VACUOUS** (**`canonForm?_ne_none`** — the
object actually *answers*; the capstone alone is satisfied by a degenerate refiner that flags on every graph).

> **★ THE RESOLVER CONTRACT WAS HARDENED (2026-07-13) — the single "branch covering" contract is RETIRED.**
> **`canonForm?_eq_deferAll_of_covering`** *proves* that a covering resolver is **value-invisible** — it computes exactly
> the exhaustive branch-min — so a single covering contract silently re-imported the retired **`canonMin`** anchor, and
> the **rigid solver could have satisfied it only by already knowing the answer.** The contract is now **`NarrowTransport`**
> (*the narrowed-branch aggregate transports*), fed by **two** routes: **`Covering`** (consume — non-equivariant choice,
> redundant discards) and **`NarrowEquivariant`** (force — structural choice, genuinely-different discards, yielding a
> *different but equally valid* canonical form). **`narrow_eq_branches_of_orbit` proves the two routes have complementary
> firing domains**: equivariant narrowing is *impossible* on an orbit cell, so **force cannot fire on a symmetric cell and
> consume fires exactly there**. **Graphs where neither fires are the residue** — which is why the design does *not*
> collapse into GI ∈ P.

Read [`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md) §1 (the object + the **two-route**
resolver contract) before touching it.

> **★★ THE REFINER IS INSTANTIATED (2026-07-13, `ChainDescent/Refine.lean`, in `build.sh`, axiom-clean).** The
> **encode-free structural round** discharges *both* refiner obligations (`refineEquivariant_encodeFree`,
> `refineSplits_encodeFree`) ⟹ **`Refine.exhaustive_canonizer`: the exhaustive descent is UNCONDITIONALLY a canonical
> form that ANSWERS — no carried hypotheses at all.** ① is now hypothesis-free except for the resolver's
> `NarrowTransport`. **Corrected finding:** "renumber the round's output" (cost-model D7 fork ii) is **not** the fix —
> a *single* `refineStep` at `n = 3` already fails to `#eval`, so the encode must be **dropped entirely**, not
> compressed. `sigKey` is already a sorted `List Nat` and `lexLeList` is already a proved total order, so the round
> ranks the **keys themselves**.

> **★★★ BOTH RESOLVER INSTANCES ARE LANDED — STAGE 3 IS COMPLETE (2026-07-14, axiom-clean, in `build.sh`).**
> - **consume** (`ChainDescent/Consume.lean`, the **`Covering`** route) — keeps one representative per orbit of the
>   branch cell. **★ THE ORACLE IS UNTRUSTED:** parameterized by an arbitrary **`Supply`** with **no proof obligation
>   at all**; the resolver filters it through a *decidable* `IsColAut` check. So **`consume_canonizer` holds for EVERY
>   supply** — a broken oracle costs branches, never correctness. This puts `matchOracle`'s **completeness** entirely
>   on the **②/firing** side and **nothing** on ①. Made provable by **`CoveringAt`** (the *fuel-graded* covering: the
>   covering witness *is* `descend_transport` at an automorphism, so the hypothesis must be able to consume the
>   induction hypothesis).
> - **force** (`ChainDescent/Force.lean`, the **`NarrowEquivariant`** route) — a **combinator**, not a hard-wired
>   solver: **`forceBy key`** keeps the branches of least key. **★ Its entire ① obligation is `KeyEquivariant`** (the
>   key never breaks ties by vertex index) ⟹ **the rigid solver drops in as a stronger `key` and owes nothing else.**
>   P1/P3 are **not** ① obligations — a weak key narrows less, which is *sound* — but **relocation is not
>   elimination**: they keep their full content as **②/firing** obligations, i.e. *how much the key sees*.
> - **★★ COMPLEMENTARY FIRING DOMAINS, NOW MEASURED** (`forceBy_no_narrowing_on_orbit`): on the **rigid** 3-regular
>   `F12` force collapses the root fan-out **12 → 1** (`descentCost` 22477 → 5186); on the **vertex-transitive** `C₇`
>   it **provably cannot fire at all** (7 → 7) and merely pays for its key. Conversely `consume` fires exactly there
>   (C₅/C₆/C₇ cost 2016/4123/7568 → 804/1372/2160). **Graphs where neither fires are the residue** — the architecture
>   is no longer only proved, it is observed.

> **★★★ THE MIXED RESOLVER + THE FIRING PROOFS + HONEST COSTS (2026-07-14, `ChainDescent/Composite.lean`,
> axiom-clean, in `build.sh`).** Three corrections to the picture above:
> - **The mixed object was MISSING.** `descend` takes **one** resolver, so the two separate instances could not
>   model the **interleaved** engine. **`Composite.forceThenConsume`** (force, then consume, at one cell) now does.
>   It is **neither** `Covering` nor `NarrowEquivariant`, so it needed a **third, unifying contract route** —
>   `CoveringOfAt` + `NarrowFnEquivariant` (cover an arbitrary **equivariant intermediate**); the two old routes are
>   its `N = branches` and `N = narrow R` special cases. Sound because **the forced set is a union of orbits** (an
>   equivariant key is constant on orbits), so consume cannot escape it.
> - **★ THE RESOLVERS WERE NEVER PROVED TO FIRE.** `NarrowProper` is satisfied by a resolver that returns the whole
>   cell — *silent uselessness was consistent with the entire proof stack.* Now proved: **consume collapses a
>   symmetric cell to ONE branch** (`consume_singleton_of_cellIsOrbit`; engine = **`orbit_closed`**, the orbit BFS
>   converges) and **a separating key collapses a rigid cell to ONE branch** (`forceBy_singleton_of_separating` —
>   §11.12's P1/P3, stated exactly). ⟹ **the composite removes all branching on BOTH domains**, and
>   **`forceThenConsume_stall`** names the residue: neither the supply connects the cell nor the key separates it.
>   **That is the mutual-stall flag, in Lean.**
> - **★ COSTS ARE NOW HONEST — and the force headline did not survive.** `Key`/`Supply` were cost-free, so `②` was
>   unfalsifiable (a flat `n³` charge for an *arbitrary* key admits an **exponential** resolver; the oracle's own
>   work — **T-C** — was billed **zero**). Both are `CostM` now. **`descentCost` on `F12`: 22477 exhaustive → 26066
>   forced — a NET LOSS.** The old "→ 5186" was the flat-charge artifact. **Firing ≠ paying**, and the waste is
>   structural: the key's look-ahead refinement is *exactly* the one the child recomputes.

**The live Lean frontier** (authoritative "what's left" = [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md)):
**① IS DONE.** What remains is **② and ③**:
1. **② — the cost + the flag (THE gap).** Re-base the node bound onto the *branching* object: the old `n⁴`
   (`CanonForm.descentCost_le`) used the single-path `nbud = n` (assume-VT, `leaves = 1`) and does **not** transfer.
   Replace `descend`'s **fuel-exhaustion `none` — still a PLACEHOLDER** — with the real **mutual-stall** flag. Both
   resolver instances now exist to cost against. **Fuel is per-layer, never threaded** (each resolver is poly-or-flag
   *locally*; do not "optimize" this into a global budget).
2. **③** — `stalled ⟹ residueHiddenJohnson ∨ residueRigidObstruction` (D1 ∨ D2), plus non-vacuity.
3. **The Publication ③ swap** — ⚠ **UPDATED 2026-07-23.** The ① half of the swap is DONE: `Publication.canonForm?`
   is now the **real** fused record object (`fold++deck++deck2++kernel`), and the ① trio is axiom-clean at it —
   the "still an `opaque` stub" claim is obsolete. What remains is the **③ swap**: `Publication.UnhandledResidue`
   is still three `opaque … : Prop` atoms, so `unhandledResidue_nonvacuous` (Publication) stays a `sorry`. But the
   "unprovable in principle" framing is now RECONCILED: `Residue.residue_nonvacuous` **IS proven** (`Residue.lean`,
   for the real `Residue := ¬Handled` definition — provable exactly because `¬Handled` is a definition, not an
   opaque atom). The remaining work is to swap Publication's opaque-atom `UnhandledResidue` onto the real `¬Handled`
   object (mirroring the ① swap), which then makes non-vacuity provable. **That swap is DEFERRED until the rigid
   residue is better determined** (the atoms' final shape depends on the rigid seal); see
   [`chain-descent-rigid-seal.md`](./chain-descent-rigid-seal.md) §9.

**The executable RUNS** — exhaustive canonization of `C₃…C₇` in well under a second per graph, with
`ChainDescent/PerformanceTest.lean` in `build.sh` as a **regression gate** (it `#guard`s iso-invariance,
distinguishing power, and both resolvers' firing behaviour ⟹ a regression fails the build). **⚠ THE STANDING LEAN
TRAP:** any definition of type `… → Colouring n` is compiled at its *type's* full arity, so it re-runs its body on
**every colour lookup** (`Colouring n = Fin n → Nat`); each descent level closes over its parent's, so the cost
multiplies per level. `@[noinline]` does **not** fix it. **Cure: return a non-function-typed value** (`ColData`).
This bit twice (~10⁴× each). **Never define anything of type `… → Colouring n`.**

**The one genuine wall.** `hSmallAutThin` — "small-Aut primitive residue ⟹ bounded WL-recovery" — is open at the
*polynomial* threshold (there it *is* GI ∈ P) and is quarantined behind the mutual-stall flag: by design the canonizer is
**polynomial-or-flag**. The live `UnhandledResidue` is `residueHiddenJohnson ∨ residueRigidObstruction` (D1 ∨ D2);
`residueNonSchurian` (D0) is a **modelling gap, not a genuine unhandled residue** (every symmetry-only residue is
node-4/Schurian or Cameron). "Isolate, don't close" (§1) describes where this sits — the live target, never a verdict
that it cannot close.

> **⚠ EVERYTHING BELOW THIS LINE IS SUPERSEDED ARCHITECTURAL BACKGROUND — do not read it as current state.** The
> de-classing framing, the "single open proposition G2-B", the seal-handoff / general-CC-separability route, and the
> per-increment WL-dimension / node-4 / `s(C)`-core history all predate **both** the Algorithm-A frame **and** its
> successor, the interleaved-fixpoint model above. They are retained only for provenance. The current state is §2 above;
> the authoritative "what's left" is [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md). The
> recovery/harvest machinery these docs describe is still real and in-build (summarized in §2's "what is built"); their
> *architecture* (sequential seals, G2-B as the single open object) is not.

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

> **⚠ SHARPENED 2026-07-14 (`DeepMatchSupply.lean`) — read the theorem's hypotheses.**
> `lockstep_disc_imp_stab_trivial` refutes an oracle whose deepening is an
> **equivariant CHOICE FUNCTION** (`LockstepExpandSeq`). It does **not** refute an
> **exhaustive enumeration**, which makes no choice at all and is therefore
> equivariant for free — the search space of `deepMatchSupply d` is characterised
> purely by **length**, so `σ` maps it onto itself. That oracle *does* harvest the
> multi-step orbit within-cell (measured: `C₄` answers at `d = 1`), at cost
> `n^{O(d)}`. So the theorem's real content is a bound on **choice-based** deepening
> — and it is exactly why a **stabilizer-chain** supply is impossible (its
> within-cell vertex pick is not canonical). "Must be cross-branch" is too strong;
> "must not be a canonical within-cell pick" is the correct reading.

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

**Core (read in full, in order) — the CURRENT frame:**
0. **★ [`chain-descent-handoff-2026-07-14.md`](./chain-descent-handoff-2026-07-14.md) — READ FIRST.** The
   authoritative state of the canonizer: ①/②/③ all proved about the real object; the frontier is **resolver
   strength**; the four open items; the **two retracted claims**; and the trap list. Everything below is context.
1. **This doc** — the idea + current state.
2. [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md) — the endgame frame (§1a: the interleaved
   fixpoint = two moves, one wall), the six `Publication.lean` obligations, and the sequencing (§5).
3. [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) — the **authoritative living tracker** of
   what's left; read its TOP section.
4. [`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md) — the **priority Lean track**: the object,
   the **two-route resolver contract** (§1.3 — read before touching any resolver), and the stage-by-stage state.
   **Stages 0–3 are DONE; ② and ③ are what is left.**
5. [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11 — the **rigid solver**: the
   §11.11 interleaved engine, the §11.12 rigid-seal roadmap (**read its RE-BASED banner first** — the Lean witness is
   no longer "P1–P4"; the force route's only ① obligation is `Force.KeyEquivariant`, and P1/P3 moved to ②), §11.13 ring
   design, §11.14 no-Cameron lead.
6. [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) —
   the theorem index; densest file, the ground truth for *what is proved*. Read in
   full. **It is well over 1000 lines — too large for one `Read` call (and even
   300-line pages can exceed the token cap, the rows are dense). Page through it
   with `Read` `offset`/`limit` in ~150-line chunks. Do NOT substitute a `grep`
   during onboarding: a prior summary or this onboarding's prose is exactly the lossy
   compression this file is the ground truth for — confirming a few names with
   `grep` is not reading it, and the gap is invisible unless you read it.**

**Algorithm substrate (foundational; predates the current frame — read for the correctness/oracle/recovery MECHANICS,
not the architecture, which §2's superseded-background note covers):**
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) — the algorithm as a whole; correctness/polynomiality
  requirements; the propagation substrate.
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) — the **oracle**: the stabilizer-chain model, the
  hardness map, the T-A/T-B/T-C decomposition (§5–§7 are pre-declassing legacy).
- [`chain-descent-declassing.md`](./chain-descent-declassing.md) — de-classed recovery + the unified oracle (its §9
  "live frontier" framing is superseded; read for the de-classing mechanism).
- [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) — **Part A**, the cross-branch stabilizer-chain object.

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

Two sides, both under the repo root. Build notes are in [`../README.md`](../README.md).

**C# — the experiment bed** (`GraphCanonizationProject/`). Strategies are tried
here first. `ChainDescent.cs` + `CanonGraphOrdererChainDescent.cs` are the
canonizer; the oracle sits behind the `ITransversalOracle` seam. Tested in
`GraphCanonizationProject.Tests/` (an isomorphism-stability bed + the CFI hard
cases). C# already canonizes CFI(K₄–K₇).

**Lean — the proofs** (`GraphCanonizationProofs/`). The active library is the
**`ChainDescent/` module split**; the top-level `ChainDescent.lean` holds the
direction-invariance and spine invariants that everything imports.

**★ THE HEADLINE STACK (read these first — this is the canonizer):**

> **⚠ This table is a 2026-07-13/14 snapshot.** The CURRENT full stack table is **handoff §1** — the modules added
> since (`Stall`, `Residue`, `SealBridge`, `SupplyTransport`, `DeepMatchSupply`, `OrbitPrune`, `PrunedSupply`,
> `SealDepthBridge`, `PartialMatch`, `SupplyCost`, `HandledBridge`, `ImprimitiveDischarge`, `Select`,
> `SelectNode`, `FoldSupply`) are listed there with one-line summaries.

| Module | Proves |
|---|---|
| `ChainDescent/CanonicalForm.lean` | the **spec**: `IsCanonicalFormOpt = SoundOpt ∧ IsoInvariantOpt`, and `complete_of_isCanonicalFormOpt` — **completeness and flag-invariance are FREE** |
| `ChainDescent/Descend.lean` | **THE OBJECT** — `descend`, the computable resolver-parameterized **branching** descent in `CostM`. Capstone `isCanonicalFormOpt_canonForm?` ⟹ **①a/①b/①c**. Also the **resolver contract** (`NarrowTransport`, `Covering`/`CoveringAt`, `NarrowEquivariant`), the covering refutation (`canonForm?_eq_deferAll_of_covering`), the non-collapse theorem (`narrow_eq_branches_of_orbit`), and totality (`canonForm?_ne_none`) |
| `ChainDescent/Refine.lean` | the **encode-free refiner** (`encodeFree`/`encodeFreeFast`) — discharges both refiner obligations ⟹ `exhaustive_canonizer` (unconditional canonical form **that answers**) |
| `ChainDescent/Consume.lean` | the **ORACLE resolver** (`Covering` route). Untrusted `Supply` + a decidable `IsColAut` check ⟹ `consume_canonizer` for **every** supply |
| `ChainDescent/Force.lean` | the **RIGID/FORCE resolver route** (`NarrowEquivariant`), as the combinator `forceBy key`. Sole ① obligation: **`KeyEquivariant`**. Concrete firing key `lookaheadKey`. **Firing:** `forceBy_singleton_of_separating` (a separating key ⟹ ONE branch) + the ceiling `keyV_aut_invariant` (an equivariant key is constant on orbits) |
| `ChainDescent/Composite.lean` | **THE MIXED RESOLVER** — `forceThenConsume`, both moves at one cell (the interleaved engine, instantiated). Needed the **third contract route** (`CoveringOfAt`). Capstone `composite_canonizer`; **fires on BOTH domains**; `forceThenConsume_stall` **names the residue** |
| `ChainDescent/PerformanceTest.lean` | the **regression gate** — `#guard`s correctness *and* that each resolver **actually fires on its own domain** (a resolver that regressed to deferring everything fails the build) |

**Supporting / historical:**

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
