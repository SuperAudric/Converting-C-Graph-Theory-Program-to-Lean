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
than flagging — equivalent in full generality to **GI ∈ P**. The project's
contribution is to *isolate* that hard problem in one component, not to close it.

---

## 2. Where the project is now (2026-06-04)

> This section is a map; the authoritative current state is the STATUS block at
> the top of each linked doc plus [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).
> Project quality bar: **every Lean theorem must be axiom-clean**
> (`[propext, Classical.choice, Quot.sound]`), full build green.

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

**The live frontier (2026-06-06).** The cross-branch harvest is now **general**:
`coversOrbits_of_realizers` reproduces *any* residual group (abelian or non-abelian)
from harvested realizers, with the CFI exponent-2 case as a corollary (CFI-cov.4
complete in the base-resolved regime; C# canonizes CFI(K₄–K₇)). The **general
polynomiality capstone** now ties this off: `crossBranchHarvest_reproduces_residual` /
`autP_reproduced_of_visibleRealizers` (`Cascade.lean` Part A) — the descent reproduces
the residual **group and order** from the refinement-computable harvest, modulo a single
recovery witness; the polynomiality-layer analogue of `exhaustiveObstruction_scheme`.
**Localisation** — the gap between this and full polynomiality — is scoped as the
*polynomiality* layer: coverage *correctness* is unconditional; recovery only makes the
harvest refinement-computable (`recoverableByDepth_pPolynomial` exports the whole
metric/DRG family), and *per-level* recovery is the substrate-conditional cascade/WL-dimension
discriminator. The broader project target is *"correctly reaches a rigid or Cameron
residual on all graph classes."* That goal's two outcomes are now both being worked:
**rigid** (cascade/abelian — the recovery + cross-branch mechanism above) and
**Cameron** (the flag region). The "or Cameron" half is the **Exhaustive-Obstruction
Lemma** — and the two claims under "the wall" must be kept apart: *whether* a
non-abelian obstruction arises (≡ **GI ∈ P**, out of scope) versus *classifying* one
that does as a Cameron section (**Cameron-hard, NOT GI-hard** — a finite target,
**now an active thread**: Approach 3, the Cameron-free *scheme leg*, with scheme
primitivity, the imprimitive ⟹ refinement-visible bridge, and the group-side bridge
(`isPreprimitive_iff_isPrimitive`: scheme `IsPrimitive` ⟺ Mathlib `IsPreprimitive`) landed in
`Scheme.lean`; the refinement-side decomposition is deferred as substrate-conditional, capstone cited).
The capstone's **largeness** antecedent has a *no-fusion* track (`Cascade.lean` Part A
`NoFusion`/`autP_reproduced_of_noFusion`, via the order identity `|Aut| = ∏ basic-orbit sizes`), but
**⚠️ that track does NOT genuinely derive largeness — the "derivation" is tautological** (`NoFusion` is
orbit-level coverage, which is vacuously satisfiable; `largenessBridge_viaHarvest` is `IsLarge ⟹ IsLarge`
once that vacuous coverage is stripped — see [`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md)
§2–§3 and [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.7.5). The
genuine "¬consumed ⟹ large" is still open (G2-B). The adversarial battery has
**run, all three tiers** ([`chain-descent-fusion-battery-plan.md`](./chain-descent-fusion-battery-plan.md),
`FusionBatteryExperiment.cs`): **no genuine fusion is constructible** — "fusion" splits into a *separable*
case (Tier-0-handled, where all constructible hidden non-abelian symmetry lives) and a *non-decomposable*
case that is empirically unwitnessable = a genuine Cameron section (no third species), with consumption
governed by candidate-pinning/recovery (orthogonal to abelian-ness). The unconditional block-visibility route
to *primitivity* was refuted (Shrikhande, depth-graded). Tracked in
[`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) (§0.7.5),
[`chain-descent-declassing.md`](./chain-descent-declassing.md) §9, and
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md).

**The goal is now a single theorem (2026-06-06, axiom-clean, `Cascade.lean` Part A).** The oracle-capability
seal is **assembled**: `reachesRigidOrCameron` / `reachesRigidOrCameron_viaHarvest` — every rank-≥3 schurian
scheme residual `ReachesRigid ∨ IsCameronScheme` (reaches a rigid residual via the cascade/abelian oracles, or
is a Cameron section), wiring the landed `exhaustiveObstruction_scheme_nonCascade_trichotomy`. The free inputs
are the cited `PrimitiveCCClassification` (Babai/Sun–Wilmes), the cascade-recovery reduction (leg A,
well-supported), and the primitivity reduction (`¬IsPrimitive ⟹ ReachesRigid` — an open in-scope gap).
Crystallizing the goal this way surfaces the to-do list as a typed hypothesis set. **⚠️ Two caveats the later
handoff sharpens** ([`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md), the authoritative state):
(1) the "largeness bridge discharged" above is **tautological**, not a genuine derivation (orbit-level vacuity,
§2–§3 there) — the real "¬consumed ⟹ large" is open; (2) the open frontier is **G2** (non-recovering ∧
non-Cameron, the `s(C)` boundary), of which the primitivity reduction is one face — and **no re-keying of the
rigid predicate closes the seal** (§4.0 there).

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
   full.

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
  [`chain-descent-routeB-handoff.md`](./chain-descent-routeB-handoff.md) — its capstones were found vacuous (see its
  top correction note); the genuine, kept pieces (`hfiber_of_fiberVisibleRealizers`, the conditional chain) are
  catalogued in the seal handoff §4 G2-A / §5.

**Paper-stage / planning docs** (theoretical targets, not yet formalized — read
only if working that thread): `chain-descent-tier3-decomposability.md`,
`chain-descent-tier3-tractable-buildout.md` (its Part A landed → schreier-sims;
Part B is the open roadmap), `chain-descent-tier3a-cascade-composition.md`
(+ `-tier3a-b1-build-plan.md`), `chain-descent-tier2-lean-plan.md`,
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
| `ChainDescent/Cascade.lean` | Leg A recovery; **Part A** stabilizer-chain object |
| `ChainDescent/CascadeOracle.lean` | the unified `matchOracle` / `matchOracleSeq` |
| `ChainDescent/LinearOracle.lean` | the linear (abelian/CFI) oracle |
| `ChainDescent/CFI.lean` | CFI gadgets, gauge flips, the `Z₂^β` cycle space, CFI-cov |
| `ChainDescent/Group.lean` | permutation-group scaffolding |

For the Lean↔C# modelling correspondence, the TC-relegation decision, and the
model objects/axiom, see [`GraphCanonizationProofs/ChainDescent/README.md`](../GraphCanonizationProofs/ChainDescent/README.md).
For *what is proved*, see [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).
