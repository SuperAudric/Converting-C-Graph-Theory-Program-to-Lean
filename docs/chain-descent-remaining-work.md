# Remaining work — the living tracker (the complete-canonizer plan)

> **What this file is.** The single forward-looking tracker: the target, the full gap enumeration, and the
> ordered plan. It carries **no history** — the pre-2026-07-18 blow-by-blow (seal-era modulo set, citation
> tables, node-4 layers, RRU retirement, the 2026-07-13/14 canonizer updates) is archived at
> [`Archive/ChainDescent/chain-descent-remaining-work-archive-2026-07-18.md`](./Archive/ChainDescent/chain-descent-remaining-work-archive-2026-07-18.md);
> do not build on it without checking the current doc its banner names.
> ⚠ **Stale cross-references:** other docs cite this file's OLD sections (§1 modulo set, §2 citation table,
> §3a research core / §3a.1 layered remainder, §6 RRU note) — those all resolve into the ARCHIVE file above,
> same section numbering.
> **State authority stays elsewhere:** what is built = [`chain-descent-handoff-2026-07-14.md`](./chain-descent-handoff-2026-07-14.md)
> (+ module docs, `PublicTheoremIndex.md`); fold/tower = [`chain-descent-fold-tower-plan.md`](./chain-descent-fold-tower-plan.md);
> Route C = [`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md); recovery/poly =
> [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md); rigid/IR =
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md); citations =
> [`chain-descent-citation-discharge.md`](./chain-descent-citation-discharge.md).

---

## 0. THE TARGET (restated 2026-07-18, user steer — supersedes every "named-residue" done-definition)

**The goal is a COMPLETE canonizer: every input handled, in polynomial time.** A canonizer that flags on a
named residue is the honest *intermediate* — and the final fallback **only if** every identified route to a
gap has been attempted and recorded dead (steers-archive discipline). It is **not** the target, and no plan
or doc may treat a currently-unhandled family as permanently out of scope. ("Polynomial is NOT a wall — it's
the target" has been the standing steer all along; this section makes it the done-definition.)

**The poly-or-flag architecture stays** — it is the scaffold that makes the pursuit honest: ① is unconditional,
② is unconditional-per-node-count with explicit per-mechanism costs, and the flag is the *measurement
instrument* that names each remaining gap (`selNode_stall_iff` = the true mutual stall). Every increment lands
inside it; the residue **deflates monotonically** with no re-proof (`Handled ⟹ HandledS`, `SameOrbits`
transfer). "Complete" = the flag provably never fires.

**The end theorems (the step beyond the algorithm):**
- **Totality:** `canonForm?(record) ≠ none` for every input — assembled as: per-leg `Handled` theorems (one
  per mechanism/family, via the `handled_of_seal`/`_selected` hooks) + the **G3 classification case-split**
  covering the primitive floor (every primitive residue is Cameron → recognition leg / bounded-base → deep
  leg / affine-linear → force+recovery legs) + the `hImprim` consolidation (imprimitive residues reduce to
  the primitive floor through the same firing interfaces).
- **Explicit polynomial cost:** the `SupplyCost` pattern extended to every mechanism (each new supply/key
  lands with its closed-form `c₂`/`keyCost` bound; the end-to-end `descentCost … ≤ costConst · n^costDeg`).
- **Axiom footprint** = `[propext, Classical.choice, Quot.sound]` + at most **{G3}** (citation policy:
  every other citation eventually built in-Lean — register + routes in `chain-descent-citation-discharge.md`).
- Until totality closes, the graded `Publication` shape (①/② + ③a flag ⟹ `¬HandledS` + per-family ③b) is the
  publishable intermediate at every stage.

---

## 1. THE GAP ENUMERATION — everything between the current design and handling every input

Grouped by decision type. Each entry: what it is → the mechanism that should close it → where it is recorded.

### 1C. Consume-side gaps (symmetry present, no built supply certifies it)

- **✅ C1 — mirror∘twisted-matching composite gauges — CLOSED 2026-07-19 (F2c,
  `ChainDescent/Deck2.lean` `deck2Supply`).** Second-seed propagation: the stalled F2b state's own ambiguity
  set (unassigned × viable, equivariantly defined) enumerated as second seeds on the shared stalled state;
  bijectivity gate (`permOf`) + `IsColAut` verify; record capstone `holKey_foldDeck2_selNode_canonizer`.
  Acceptance MET: `ut` end-to-end ANSWERS (~20 min interpreted, `PerformanceTest` §11; `Regression` §14
  gates t3).
- **✅ C2 — wreath-type per-copy gauges (`Z₂ ≀ Z_s`) — CLOSED BY MEASUREMENT 2026-07-19 (no new code).**
  The planned witness was built (`wr3`: 3 copies matched only on mirror-fixed fibers, `Aut ⊇ Z₂³ ⋊ D₃`) and
  the "measure every built supply dead" step FALSIFIED the scope line instead: **`deck2Supply` fires**
  (fold 6 / deck 3 / deck2 → 1; answers end-to-end; `PerformanceTest` §12). Mechanism: the `.getD v`
  identity-default — an *independent* residual ambiguity defaults to identity, and independence is exactly
  what makes that completion an automorphism; verification accepts (and rejects the same default on coupled
  residuals — sound either way). No separate wreath leg is needed.
- **C3 — the general ambiguous-propagation regime — RE-DERIVED 2026-07-19 (the wr3 probe's analysis;
  detail `Deck2.lean` module doc).** Measured deck2 reach: coupled-and-chaining ambiguities (t3) +
  independent gauges (wr3) + every `Z₂`-gauge generated by ≤2-seed-reachable elements (includes all
  sum-zero codes — generated by weight-2 words). **The genuine residual class: gauge = kernel of parity
  checks of arity ≥ 3 with minimum weight ≥ 3** — one assigned wire leaves ≥ 2 candidates at every check
  (pairwise forcing cannot chain) and no weight-≤2 word exists (identity-default invalid) = **CFI
  cycle-space gauges**. Boundary: odd-degree-base CFI already exits via the DEPTH leg
  (`theorem_1_HOR_cfi_oddDeg` ⟹ `deepMatchSupply`); the open witness class is the **symmetric pin-blind
  CFI cover** (multipede-style even-degree base, nontrivial cycle space).
  **✅ (i) WITNESS BUILT + MEASURED 2026-07-19 — `mp7`, the FANO MULTIPEDE (n = 42; `PerformanceTest`
  §13, all `#guard`ed):** 7 foot-pair segments, 7 arity-3 checks = Fano lines (two checks share exactly
  ONE segment — incidence girth 6), 4-vertex CFI gadgets; gauge = ker(incidence) = the [7,3,4] simplex
  code (dim 3, min weight 4 — verified real: the weight-4 flip IS a colour-automorphism). Pin-blind
  (6/42 colours after a pin ⟹ matching supplies structurally dead); fold narrows nothing; deck: the
  gauge seed forces 1 vertex of 42 (girth kills chaining) and even the Z₇-translate seed stalls; deck2:
  689-entry second stage, gauge continuation fails the gate; a THIRD seed (manual deck3) also fails —
  the gadget layer never chains. Force cannot act (single-orbit cells). **TRUE mutual stall of the whole
  stack; the constructor gate is OPEN and the route is DECIDED** (deck_k is dead on this shape at any
  practical k, and growing-weight families kill fixed k in principle).
  **✅ (ii-a) THE KERNEL SUPPLY, TRANCHE 1 LANDED 2026-07-19** (`ChainDescent/KernelSupply.lean`, in
  `build.sh`, compiles clean; wiring gate `Regression` §15, full measured set `PerformanceTest` §14):
  the executable pipeline exactly as designed below, **plus the design lock found during the build —
  the ALL-OR-NOTHING GATE**: a pivot-order-dependent basis with *partial* verification would make the
  emitted subgroup depend on the pivot choice (①c genuinely false); emitting all-or-nothing makes the
  gate ⟺ "every word of `L` verifies" (products of automorphisms) — canonical — so the emitted GROUP
  is a canonical function of `(adj, χ)`. **MEASURED on `mp7`**: rails = exactly the 7 foot pairs;
  basis = dim 3, weights [4,4,4] — *the simplex code recovered from raw structure*; gate passes; root
  gadget cell **28 → 7** (the whole gauge in one supply call); at the pinned node the basis restricts
  to dim 2 = exactly the codewords avoiding the pinned segment; 0 generators on t3/ut/wcyc9.
  **Follow-on state:**
  - **✅ (ii-b) Tranche 2 — the ① proof stack — COMPLETE 2026-07-19, all four parts landed** (four
    modules in `build.sh`, all axiom-clean `[propext, Classical.choice, Quot.sound]`; detail = module
    docs; `kernelSupply` is now IN the record object):
    · **I `KernelGauss.lean`** — `span(kernelBasis) = L`: `dotB_nullBasis` (soundness) +
      `spans_nullBasis` (completeness), via the parity-count engine (`dotOn_eq_countP`,
      `countP_parity_single/_pair`) + the echelon invariant `PivInv` (unit / cross-zeros / `Nodup`
      columns / both directions of same-row-space through the fold). Plus the `Spans` toolkit
      (`xor_closed`, `trans_basis`, `combo`) the reduction consumes.
    · **II `KernelFlip.lean`** — the flip-composition PRODUCT lemma **`flipFunK_xor`**
      (`flip(w⊕w') = flip w ∘ flip w'` for verified flips — the theorem behind the all-or-nothing
      gate): rails are vertex-disjoint (`rails_endpoint_eq`), `emitted_rail_action`,
      ★`touched_moves` (a VERIFYING flip cannot fix a touched vertex — twin
      neighbourhood-disjointness; this closes the identity-default / `uniqueFilter`-ambiguity hole
      for compound words), ★`satP_conj_flip` (the satisfier bijection), `condFun_untouched` +
      `flipGuard_congr`/`satP_congr_touch` (the guard case-analysis pieces).
    · **III `KernelRef.lean`** — the set-level reference `kernelRefSupply` (flips of ALL of `L`,
      same all-or-nothing gate; `allWords`-enumerated, proof-side only) with **gate equivalence**
      (`refGate_of_kernelGate` via the span induction `flip_emits_of_spans` = completeness +
      product lemma, each spanned flip also `Reaches` the kernel group = the P3b license; converse
      via `basis_mem_kernelWords` = soundness) ⟹ **`sameOrbits_kernelRef`**, and
      **`sameOrbits_appendSupply`** (orbit-equality is a congruence for `appendSupply` — the swap
      is licensed inside the record composite).
    · **IV `KernelTransport.lean` — LANDED 2026-07-19, and with it TRANCHE 2 IS COMPLETE.**
      `GensEquivariant kernelRefSupply` + the capstones, all axiom-clean, all built. The stack, in
      the order the difficulty rises:
      (a) `IsoTo σ adj χ adj' χ'` (σ is an isomorphism — the `IsColAut` lemmas of `KernelFlip` §4 are
          its `adj'=adj` case) and the structural conj chain `isAdj_iso`/`twinP_iso`/`twin_iso`/
          `onRail_conj`/`touches_conj`. Rails transport **only up to endpoint order** (the list
          stores each pair at its lower index — an internal labelling σ need not respect): `sPair`,
          `railMap`, `mem_rails_conj` (memberwise) and **`rails_perm_conj`** — a `List.Perm`, not an
          equality, which is what every count argument downstream actually needs.
      (b) word transport. A word is indexed by rail POSITION and σ permutes positions, so
          `transportWordR` re-reads each bit by endpoint lookup (`lookupBit`). Two central lemmas
          carry everything: **`mem_zip_transport`** (the labelled word `rails.zip w` transports as a
          SET of labelled bits — every `any`/`all` in the pipeline is a statement at exactly that
          level) and **`dotB_transport`** (parity, via the Perm + `transport_perm`). Then
          `flipFunK_conj` (railImg by the endpoint-value lemma; guard and satisfier memberwise) and
          `Deck2.permOf_conj` moves emission INCLUDING its failure mode.
      (c) the `inL` bridge, as planned and for the reason predicted: `localRows` is pivot-dependent
          and does NOT transport pointwise, so `L` is re-characterized basis-free as **`Lc`** (`w` is
          killed by every wire-supported functional that kills the local patterns) with
          **`inL_iff_Lc`** riding on part I being sound AND complete, over the embed/restrict
          adjunction **`dotB_embed`** (a `Nodup`-support counting lemma). One thing the plan did not
          foresee: `patOf`'s emitted bit reads the rail's FIRST endpoint, so `patOf_conj` needs the
          bit to be endpoint-order invariant — which is true **only under `patOf`'s own shape
          condition** (single-sided touch both sides + matching touch support), hence
          `patBit_swap_of_shape`. `Lc_transport` then transports memberwise as designed.
      (d) capstones: `kernelSupply_guarded_canonizer` / `kernelSupply_selNode_canonizer`, and
          **`holKey_foldDeck2Kernel_selNode_canonizer`** (+`…Fast`) = ① for the record
          `fold ++ deck ++ deck2 ++ kernel`, via `sameOrbits_appendSupply ∘ sameOrbits_kernelRef`
          against the equivariant reference composite; `handledS_recordSupply` transfers ③.
      **The record object is SWAPPED**: `Publication.lean`'s `canonForm?` now consumes
      `foldSupplyFast ++ deckSupply ++ deck2Supply ++ kernelSupply`, `canonForm?_record` is the new
      capstone, and the ① trio (`canon_sound`/`canon_complete`/`flag_iso_invariant`) stays
      axiom-clean `[propext, Classical.choice, Quot.sound]` — `canonizer`'s `sorryAx` is still
      exactly ②+③+non-vacuity.
    ✅ Theorem-index regen DONE (all 257 `Kernel.*` public rows + 4 private described).
    **Optional, deliberately NOT done (judged low value, recorded so it is a choice and not an
    oversight):** (a) an extended-record `Regression` guard — the existing §15 mp7 guards already
    gate every kernel wiring path, and the record composite is exercised by the same object;
    (b) a `kernelRefGens` firing guard — it is a `2^#rails` enumeration (128 words on mp7, so it
    *would* run, but it is proof-side by construction and nothing executable reads it).
    Non-vacuity is already instantiated: `KernelGate` holds at the `Regression` §15 mp7 guard
    (`kernelGens.length = 3` forces the gate through), and `RefGate` follows by
    `refGate_of_kernelGate`.
  - **(ii-c) = C3b — RE-SCOPED BY MEASUREMENT 2026-07-19 (`PerformanceTest` §15). The target is now
    exact, and the originally-named mechanism is RULED OUT.**
    **What is missing on mp7, measured:** the naive base translation (foot pair `j ↦ j+1`, gadget
    `i ↦ i+1`) **lifts unchanged** — it passes the gate and IS a colour-automorphism. Kernel gens
    alone give a gadget-vertex orbit of **4** (the gauge, exactly as designed); kernel gens **+ that
    one translation** give **28 = the whole branch cell** (and 14 = every foot). ⟹ **mp7 answers at
    the root the moment ONE base-symmetry generator is supplied**; the kernel already covers all the
    rest. That is the whole C3 acceptance, reduced to a single concrete target.
    **⛔ "deck-modulo-the-verified-subgroup" is DEAD as a standalone route** (this was the plan of
    record until measured — do not re-attempt it in that form). §13 measured that the translate seed
    forces **1 vertex of 42**: girth 6 means nothing chains, and quotienting by `K` does not create
    chaining where there is none. Propagation is not the vehicle here at any modulus. (The "force
    uniqueness only up to `K`" idea is still sound *as a licensing pattern* — see the note below —
    it just has nothing to propagate on this family.)
    **▶ THE ROUTE: BASE-GRAPH RECOVERY + LIFT.** The translation is an automorphism of the **base**
    object `kernelSupply` already extracts: rails = the 7 segments, per-vertex wire supports = the 7
    checks, and their incidence IS the Fano plane. So: recover the base incidence structure (already
    computed — `rails`/`wiresOf`/`pats`), obtain generators of ITS automorphism group, and **lift**
    each one to the cover by any gauge-consistent completion; `permOf` + `IsColAut` verify as always.
    **The ① license is the good news, and it is why this route beats the propagation one:** two lifts
    of the same base automorphism differ by an automorphism inducing the identity on the base — i.e.
    by a pure gauge element, i.e. by an element of `K`, which the kernel supply already emits. So the
    lift's choice-dependence is absorbed by `K` and `SameOrbits` closes exactly as in tranche 2
    (reference = ALL lifts; executable = one arbitrary lift ++ kernel; reachability holds *pointwise*
    — for `WordReach` it is enough that each `v` and `ρ'(v)` are connected, so a per-vertex gauge
    element suffices, no single global `k` is needed. That observation is the load-bearing one; it is
    what made the coset obligation provable instead of a graph-dependent assumption).
    **Open design questions to settle FIRST (do not build past these):** (1) how base-automorphism
    generators are obtained — recursion into the canonizer on a much smaller object (14 items here)
    vs. a direct search — and what that does to the cost model / `SupplyCost`; (2) whether base
    recovery is stated generally or per-recognized-family (the retarget's per-family recovery leg);
    (3) whether the lift needs the gate to have passed (probably yes — `K` must be available for the
    license). Acceptance unchanged: `mp7` answers end-to-end.

    ### ⚠⚠ 2026-07-20 — C3b SCOPED AND MEASURED. Q(1)/Q(3) ANSWERED; A NEW, SHARPER GAP FOUND.
    Probe: the base-recovery/lift scratch file has been DELETED (route superseded and parked — see
    below); every number it produced is recorded verbatim in this block, which is now the record. Executable draft = `ChainDescent/KernelBase.lean`
    (NOT in build.sh — see the verdict below before landing it).
    **✅ What the measurement CONFIRMS (do not re-derive):**
    1. **Base recovery works and is faithful, with no new extraction code.** `kernelSupply`'s own
       `rails`/`wiresOf` already contain the base object. Measured on `mp7`: rails = the 7 foot
       pairs, supports = the 7 Fano lines `{i, i+1, i+3}`, base graph = **14 vertices, 2 refinement
       cells** — the Fano incidence (Heawood) graph. The known `Z₇` translation IS a
       colour-automorphism of the *recovered* base graph (`IsColAut bA bRoot.col transBase = true`),
       which is the faithfulness check.
    2. **★ THE LIFT/COSET THEORY IS CONFIRMED QUANTITATIVELY.** Over all `2⁷ = 128` endpoint
       orientations, the `Z₇` translation admits **exactly 8 = |L| = 2³** verified lifts. That is the
       ① license argument — "two lifts differ by a pure gauge element" — measured, not assumed: the
       valid orientations form precisely a coset of the gauge space `L`. Q(3) is therefore **YES**:
       the lift needs `K`, and `baseSupply` is only sound appended AFTER `kernelSupply`.
    3. **⛔ The naive (`lower↦lower`) orientation is USELESS, not merely lossy.** Of 301 deck2 base
       gens, all 301 pass `permOf` but **exactly 1 verifies — the identity**. Orientation must be
       SOLVED, never guessed. (The solve is cheap and already designed: valid orientations are the
       solution set of an *affine* F₂ system whose homogeneous part is exactly the `localRows` system
       `kernelBasis` already solves — same elimination, augmented matrix.)
    **⛔⛔ THE GAP: NO SUPPLY SOLVES THE BASE GRAPH. (Q(1) answered in the negative.)**
    **⚠ RETRACTED SAME DAY — an earlier version of this block claimed the gap was that liftability is
    a KERNEL of `Aut(base) → H¹` and so unreachable by per-generator filtering. That was derived from
    JUNK DATA and is WRONG — do not resurrect it.** The bug: `Consume.gens` returns **UNVERIFIED**
    candidates (junk is filtered by `Consume.verified` downstream, not by `gens`), and the first pass
    never applied `IsColAut` to the BASE gens. Corrected numbers below. **⚠ STANDING TRAP: any probe
    reading `Consume.gens` directly must filter by `IsColAut` first.**
    **Corrected measurement:** of deck2's **301** raw base gens, exactly **1** is a genuine base
    colour-automorphism — the **identity**; **zero** move a rail. fold (49) and deck (7) likewise emit
    no non-trivial base automorphism. So all three supplies **fail to solve the 14-vertex base graph**;
    the earlier "210 non-identity, rail-transitive" figures were junk artifacts.
    **The lift was never the problem.** The `Z₇` control stands (exactly `8 = |L|` verified lifts), and
    the C# cross-check (below) shows the FULL Fano collineation group lifts. There is **no evidence of
    any kernel/`H¹` obstruction** — that diagnosis is withdrawn.
    **▶ C# CROSS-CHECK (2026-07-20, `GraphCanonizationProject.Tests/FanoMultipedeProbe.cs`) — the C#
    canonizer DOES handle `mp7`.** ⚠ First, the fixture trap: `MultipedeGenerator.BuildCirculant(m)`
    applies a **fine colouring** giving every segment its own colour and every gadget cluster its own
    colour, which excludes the base symmetry BY FIAT (`Z₇` maps segment `w ↦ w+1`, different colours) —
    and the existing suite runs only `m = 5,6,8,9,10,12` with `AssertRigid`, i.e. **7 ∤ m**, so the
    non-rigid case was never covered. Run on the SAME object Lean uses (UNIFORM colouring, `m = 7`,
    `n = 42`): **canonical, 4 nodes, depth 3, |residual| = 1344 = 8 × 168 = |L| × |PGL(3,2)|** — the
    whole gauge times the whole collineation group. (Fine-coloured: 1 node, residual 1; `m = 9`
    rigid-base control: residual 9.)
    **▶▶ ✅ C3b LANDED (tranche 1) 2026-07-20 — `ChainDescent/DeepenSupply.lean`, in `build.sh`.**
    ⚠ A first reading guessed the C# success came from nauty-style **leaf-collision** harvesting
    (several leaves ⟹ incompatible with ②'s single path). **Measured and FALSE: `leaves = 1`** —
    one leaf, 4 nodes, depth 3, well inside `n+1 = 43`, and `EnableRigidSolver` ON/OFF is identical
    (so not `Option2Solver` either). ⛔ Do not repeat the leaf-collision guess.
    **The mechanism, ported from `ChainDescent.cs` `HarvestTwists`: stop propagating — REPLAY A
    DEEPENING AND COMPARE FOOTPRINTS.**
    (1) `deepen` individualizes the anchor and repeatedly individualizes the **lowest-id
        NON-singleton sub-cell of the footprint** (the diff against the node colouring, held fixed
        as parent) until the footprint is all-singletons, recording the chosen cell ids — one
        sub-cell, one vertex per level, a **single path**, never a branch over representatives;
    (2) `replay` follows the SAME id sequence from each other representative (unfollowable ⟹ no
        candidate — sound, the representatives just stay separate);
    (3) `twist` matches `r₁`'s colour-`c` vertex to `rⱼ`'s colour-`c` vertex on the coupled
        component, identity off it. 1-WL gives corresponding vertices of isomorphic branches equal
        canonical colours, so under the **all-singletons gate** this is a forced bijection; a
        non-singleton sub-cell is refinement-indistinguishable and admits no iso-invariant match, so
        those are rejected outright;
    (4) `permOf` + `IsColAut` verify — propose/dispose, junk costs firing and never ①.
    **✅ MEASURED (`PerformanceTest` §16, `#guard`ed):** branch cell **28**; the supply yields
    **756 = 28 × 27 verified generators** (all anchors); and the gadget cell (28) **and** the foot cell (14) each collapse to
    a **SINGLE ORBIT — from the deepen gens alone**. Compare §14 (kernel alone → gadget orbit 4, the
    gauge) and §15 (the translation had to be supplied by hand to reach 28). **That is the C3
    acceptance.** Cross-check: C# reports |Aut| = 1344 = 8 × 168 on the same object.
    **WARNING ①c — RETRACTED AND CORRECTED 2026-07-20 (same day). An earlier version of this block
    said "① rides `SameOrbits`, the licensing machinery already exists and is proven". That was
    WRONG as stated — with the single-anchor supply ①c is MEASURED FALSE.**
    > **STOP: THE `G8` FALSIFIER — do not re-introduce a single-anchor variant, and do not attempt a
    > `SameOrbits` proof for one.** Scrambling `G8` by five relabellings, the single-anchor supply
    > gives branch-cell orbit profiles `[2,2,2,2,4,4,4,4]` under two and `[1,1,2,2,2,2,2,2]` under
    > two others — genuinely different partitions (fixed points vs orbits of size 4). Hence ①c is
    > false, and `SameOrbits` against **any** equivariant reference is then false too (an equivariant
    > reference has a labelling-independent orbit relation by definition).
    > **Why `mp7` could not catch it, and the reusable lesson:** `mp7` fires *totally* (whole cell
    > = one orbit), so its profile is `[28]` down any path. **An equivariance falsifier must be run
    > on a PARTIALLY-firing witness** — a totally-firing one is structurally incapable of falsifying.
    **THE FIX, MEASURED: quantify over ALL ANCHORS.** The same five `G8` labellings then all give
    `[2,2,2,2,4,4,4,4]`, and the union fires strictly MORE (it is the richer partition). The landed
    `deepenGens` loops over every anchor, with the per-representative first refinement hoisted so the
    cost is `|cell|` refinements + replays, not `|cell|` squared (trap #2).
    **▶ TRANCHE 2 — ROUTE DECIDED 2026-07-20: (a), the path-independence proof. (b) = recorded fallback.**
    All-anchors removes the *anchor* choice but not the **per-deepening-level vertex choice**
    (lowest-index member of the chosen sub-cell), so the ① route had to be chosen on evidence.
    **The evidence (all measured this day):**
    · **No falsifier for the per-level layer.** Two tie-break rules (lowest- vs highest-index) give
      IDENTICAL branch-cell orbit profiles on `G8` `[2,2,2,2,4,4,4,4]`, `t3`/`wcyc9` `[3,3,3]`, `ut`
      `[3,3,3,3,3,3]`; and **8 labellings x those 4 PARTIALLY-FIRING witnesses all agree** (dedup
      length 1 each) for the landed all-anchors supply. These same tests caught the anchor-layer bug,
      so they demonstrably have teeth.
    · **Path counts measured** (for costing (b)): `G8` [] or [2], `wcyc9` [] (depth 0), `t3` [2,2]=4,
      `ut` [2,3,2,2,2]=48, `mp7` [12,4]=48.
    **WHY (a) WINS — the decisive criterion is the NO-EXPONENTIALS requirement (user steer):**
    (a) is **polynomial by construction** — it IS the landed executable (`|cell|` deepenings +
    `|cell|`-squared replays, bounded refinements each, billed `n⁶`); no budget, no firing cliff.
    (b) cannot avoid an exponential unaided: the deepening tree is a PRODUCT of sub-cell sizes over
    levels (worst case `2^(n/2)`), and it is worse than it first looks because **`replay` also picks
    `members[0]`**, so (b) needs paths-x-paths per pair (~1.7M constructions on `mp7` alone).
    **⚠ HARD REQUIREMENT ON (b) IF IT IS EVER TAKEN:** it must ship with either a PROOF that the
    deepening tree is poly-bounded, or an imposed **budget gate** — enumerate up to `B(n)` leaves and
    EMIT NOTHING beyond it. The budget form stays canonical (the tree branches over ALL vertices of
    the canonically-chosen sub-cell, so it makes no choice; its leaf count is a canonical number and
    "≤ B" a canonical predicate), and exceeding `B` is a firing loss, never an ① loss.
    **▶ ROUTE (a), SCOPED.** Reference `deepenRefSupply` (PROOF-SIDE ONLY, never executed — the
    `kernelRef` `2^#rails` pattern): all anchors x ALL deepening paths x ALL replay paths, same
    all-singletons gate; equivariant because it makes no choices.
    · *Direction 1 (easy):* `exec ⊆ ref` — the canonical path is one of the paths, `WordReach` is
      monotone.
    · *Direction 2 (THE CRUX):* if for anchor `r₁` SOME deepening path `P` and replay path `Q` yield
      a verified twist `t` with `t r₁ = rⱼ`, then `rⱼ` is `WordReach`-able from `r₁` using the
      CANONICAL-path generators. Sketch: `t` is a genuine automorphism, so applying it to the
      canonical deepening from `r₁` transports it to a valid deepening from `rⱼ` with vertex choices
      `t(wᵢ)`; colours are preserved so the CELL-ID SEQUENCE MATCHES, and the only gap is that replay
      picks a different member of the SAME cell. So the crux reduces to: **does the twist construction
      succeed independently of which member of the id-`cid` cell replay picks?** Expected mechanism:
      the ALL-SINGLETONS GATE forces it (it demands the coupled component be fully discretized). That
      is the load-bearing step and it is NOT yet proven.
    **✅ STEP 0 DONE 2026-07-20 — the adversarial hunt came back CLEAN and NON-VACUOUS.** A search over
    400 random graphs on `Fin 8`, comparing the emitted orbit profile under the lowest-index rule vs
    the highest-index rule (rule changed on BOTH sides — anchor deepening AND replay), found **zero**
    mismatches, and **302 of the 400 actually fire** (so the search had real coverage, not a sweep
    over inert graphs). Together with the earlier sweeps, route (a) survives every test available.
    ★ The reframing that made the hunt sharp, and that the proof will use: the executable uses the
    **same selection rule on both sides**, so the conjecture is not "the choice does not matter" but
    "the emitted orbit relation is independent of the rule, *provided the same rule is used on both
    sides*". Note robustness canNOT come from equivariance of the rule — a lowest-index rule does not
    commute with an automorphism `t`, so replay generally reaches a DIFFERENT discrete colouring than
    `t`'s image. It has to come from the **all-singletons gate** making the colour ids canonical 1-WL
    ranks, so the match is between canonically-labelled structures whichever discrete colouring was
    reached. That is the mechanism the crux proof must exploit.
    **✅ TRANCHE 2 PART I LANDED 2026-07-20 — `ChainDescent/DeepenTransport.lean`, in `build.sh`, all
    axiom-clean.** The unconditional half: **every stage of the pipeline transports except the vertex
    pick.** ★ `chooseIdK_transport` is the load-bearing one — the chosen cell id is an INVARIANT `Nat`
    (equal, not conjugated), so the recorded id sequence is labelling-independent, which is exactly
    the "cell-id sequence matches" step of the crux. Also `step_transport` (individualize+refine
    commutes with σ), `mem_coupled_transport`, `allSingletonsK_transport` (invariant `Bool`),
    `classOf_length_transport` (invariant size), `classOf_perm_transport`. ⚠ Lists transport only up
    to `List.Perm` (`classOf` filters `finRange` in INDEX order) — the `rails_perm_conj` lesson.
    **✅ TRANCHE 2 PART II LANDED 2026-07-20 — `ChainDescent/DeepenCrux.lean`, in `build.sh`,
    axiom-clean.** The crux is now DECOMPOSED, STATED in Lean, and its unconditional half is proved.
    **⚠⚠ RETRACTED ARGUMENT (2026-07-20, same day) — kept visible so it is not repeated.** An earlier
    version of this block argued that the emitted relation cannot equal the true `Aut`-orbit relation
    "because a cell's orbit partition is poly-time equivalent to GI, so such a supply would be GI ∈ P".
    ⛔ **That is precisely the argument form BANNED by the standing steer** ("any `X ⟹ GI∈P, therefore
    X impossible` argument is BANNED" — a perfect key *is* GI∈P, the TARGET; the inference is
    circular). It was also unsupported: the companion claim "on hard instances the gate simply fails"
    was **asserted, never measured, and the measurement CONTRADICTS it**. Both withdrawn.
    **What is actually measured:** emitted = true `Aut`-orbit relation on every instance tested — `G8`
    `[2,2,2,2,4,4,4,4]` both sides; 30/30 firing at `n=7`; 19/19 at `n=8`; **`wcyc9` `[3,3,3]` both
    sides (`9!` brute-forced — a genuine CFI-style witness with non-trivial orbit structure)**. And
    the gate **NEVER FAILED**: 0 failing anchors on `t3`, `wcyc9`, `ut`, `mp7` — including `mp7`,
    where deck, deck2 and gauge propagation all fail.
    **Status: the orbit-equality hypothesis is UNFALSIFIED, not refuted** — and not asserted either.
    The predicates are stated gate-conditionally, which is the right shape whichever way it resolves.
    **▶ THE DISCRIMINATING WITNESS THAT IS STILL MISSING — build it FIRST, before any proof attempt:**
    a graph with **non-trivial symmetry** that individualization-refinement **cannot cheaply
    discretize** — i.e. CFI/multipede over a LARGE expander-like base (cf. the C#
    `MultipedeGenerator.BuildRandomRegular`, whose high-treewidth base is documented to resist
    refinement). ⚠ Rigid multipedes do NOT discriminate (trivial `Aut` ⟹ the equality holds
    vacuously); `mp7` does not either (Fano is small, the gate passes). ⚠ Also note the random-graph
    sweeps at `n = 8,9` turned out **degenerate** — branch cells of size ≤ 2 — so they carry far less
    weight than their sample sizes suggest.
    **⟹ ①c reduces to exactly two named predicates** (both in `DeepenCrux.lean`):
    · **`DeepenGateInvariant`** — the gate outcome `GateAt adj χ r` is labelling-invariant. Combined
      with part I (every OTHER stage transports), this is the ENTIRE residue of ①c.
    · **`DeepenForcedMatch`** — gate passes ⟹ the emitted relation IS the true orbit relation.
    **PROVED unconditionally here:** `deepenGens_isColAut` (every emitted generator is a genuine
    colour-automorphism) and `deepenGens_sound` (the emitted orbit relation is CONTAINED in the true
    one — the supply can only under-report orbits, never over-merge) = the `→` direction of
    `DeepenForcedMatch`.
    **Evidence for the two open predicates** (recorded so it is not re-measured): gate outcomes agree
    under the lowest- vs highest-index rules across **200 random `n=8` graphs** (151 with a non-empty
    branch cell), plus `G8` (all 8 anchors pass under both), `t3`, `ut`; and rule-independence of the
    emitted relation over 400 random graphs (0 mismatches, 302 firing) plus 8 labellings x 4
    partially-firing witnesses.
    **⚠ METHODOLOGICAL CAVEAT — the `G8` lesson, restated because it applies to ALL of the above:**
    every one of those measurements comes from instances where the algorithm appears COMPLETE. A
    discriminating test needs an instance where the supply FIRES but is strictly INCOMPLETE, and none
    was found at `n ≤ 8`. **Until such a witness exists the sweeps may be systematically blind** —
    exactly as `mp7` was blind to the anchor-layer bug by firing totally. Finding one is the first
    task of part III, ahead of attempting `DeepenForcedMatch`'s completeness direction.
    **▶ REMAINING = part III: discharge `DeepenGateInvariant` and `DeepenForcedMatch`.**

    ### ▶▶ 2026-07-21 — PART III STARTED: the ALL-PATHS REFERENCE + the easy inclusion (`DeepenRef.lean`, in build)
    The ①c target is restated the way `kernelSupply` closed its own — through `OrbitPrune.SameOrbits`
    against an EQUIVARIANT reference, NOT against `Aut` (this is what retires the retracted GI∈P
    framing). `DeepenRef.lean` builds `deepenRefSupply` = the same deepen/replay/twist pipeline but
    branching over EVERY member of the chosen sub-cell at each level (`deepenAll`/`replayAll`), through
    a shared `twistOf` (extracted into `DeepenSupply` so "an exec generator IS a reference generator"
    is a defeq). Proof-side only, exponential, never shipped.
    **LANDED (axiom-clean):** `deepen_mem_deepenAll` / `replay_mem_replayAll` (the single canonical pick
    `w :: _` is the head branch of the all-picks `flatMap`) ⟹ `deepenGens_subset_ref` ⟹
    `verified_deepen_subset_ref` ⟹ **`wordReach_ref_of_deepen`** — the easy half of `SameOrbits`
    (exec orbits ⊆ ref orbits), via `wordReach_mono`.
    **▶ ADVERSARIAL STEP-0 PASSED (`ScratchPickTest`, since deleted):** the all-picks reference reaches
    the SAME orbit partition as the single canonical pick on every partially-firing witness — `G8` exec
    16 / ref 28 generators but BOTH `[2,2,4]`; `t3` exec 6 / ref **96** but both `[3]`; `wcyc9` both
    `[3]`. The surplus reference generators are already WORDS in the executable's. So the reverse
    inclusion is UNFALSIFIED against the genuine all-picks reference (not just a two-rule comparison).
    **▶ THE RESIDUAL, now two crisp obligations (`DeepenRef.lean` §6), superseding the truth-framed
    `DeepenForcedMatch`:** (R1) the REVERSE `SameOrbits` direction = route (a)'s "the pick is
    interchangeable" (the all-picks reference proves no orbit the single pick misses); (R2)
    `deepenRefSupply` equivariant = the `KernelTransport.gensEquivariant_kernelRefSupply` analog (σ
    permutes the all-picks set bijectively; part I absorbs the one non-transporting pick). **Route (b)**
    restates the crux against this reference, needing only (R2) + a gate-conditional match — never "the
    executable recovers the true orbit". `DeepenGateInvariant`/`DeepenForcedMatch` remain the
    truth-framed statements of the same content in `DeepenCrux`; (R1)/(R2) are the reference-framed form
    that closes ①c through the existing `OrbitPrune` reduction.

    ### ▶▶ 2026-07-21 — R2 ALGEBRAIC CORE LANDED (`DeepenRefTransport.lean`, in build, axiom-clean)
    R2 = `SupplyEquivariant deepenRefSupply`, the exact hypothesis `OrbitPrune.guarded_mixed_canonizer_
    of_sameOrbits` needs of the reference (⟸ `GensEquivariant` via `supplyEquivariant_of_gensEquivariant`).
    **DONE — the hard algebraic step:** `twistOf_transport` — the twist on the relabelled graph is the
    σ-CONJUGATE of the twist here (verification included): `twistOf (relabelAdj σ adj) (transp σ χ)
    (transp σ χ1) (K.map σ) (transp σ χj) = (twistOf adj χ χ1 K χj).map (σ·σ⁻¹)`. Built from
    `imgFun_transport` (colour-match function conjugates, via `List.find?_map`), `Deck2.permOf_conj`, and
    `Consume.isColAut_conj_iff`.
    **▶ REMAINING for R2 (mechanical assembly):** `deepenAll`/`replayAll` leaf-set correspondence under σ
    (induction on fuel via part-I `step_transport`/`chooseIdK_transport`/`mem_coupled_transport` +
    `branches_transport_perm`), lifting `twistOf_transport` to `GensEquivariant deepenRefSupply`.
    ⚠ **Subtlety found + recorded** (`DeepenRefTransport` header): the transported ref calls `twistOf`
    with `coupled (transp χ)(transp χ1)`, only a `List.Perm` of `(coupled χ χ1).map σ` (index order), and
    `find?` is order-dependent — but under the `allSingletonsK` gate the colour-match is UNIQUE, so the
    assembly needs "`twistOf` invariant under a `Perm` of `K` when `allSingletonsK K χ1`", then composes.

    ### ▶▶ 2026-07-20 — HOW STRONG IS IT, MEASURED ON THE C# SIDE (`DeepenStrengthProbe.cs`)
    The Lean-side evidence was 4 structured witnesses, so the strength question was taken to the C#
    `HarvestTwists` across every family the repo can generate (39 rows: CFI K4/K33/Rook3x3/Petersen
    even+odd, circulant multipedes m=4..9 in BOTH colourings, random-regular *expander*-base
    multipedes, Cameron Johnson/Hamming/Kneser, T(8), Chang-A/B). Reproduce with
    `dotnet test --filter "FullyQualifiedName~DeepenStrengthProbe"`.
    · **STARVATION IS ZERO ON ALL 39 ROWS** (`ClassifyStarved` = `BranchStarved` = 0). Class 2 — the
      documented "Route-A provability breaker" — never fired once. This is real support for
      `RruDepthProbe.cs:19-23`'s hypothesis H1 that class 2 is unreachable, now tested well beyond
      the families that hypothesis was formed on. **It is not a proof:** the probe covers the
      generable families, not all graphs.
    · **Every checkable row is COMPLETE** (harvested `|Aut|` == ground truth) — including all 7
      Cameron rows against their closed-form orders. Rows with `CAPPED` truth are unchecked, not
      passed.
    · ⚠ **THE Chang-A "LEAK" RECORD IS STALE — RETRACT IT.** The archive
      (`chain-descent-remaining-work-archive-2026-07-18.md:391`) records "the cascade certifies order
      **24** of `|Aut|=384`". Measured now: **Chang-A is COMPLETE, 384/384**, 17 nodes, 4 leaves,
      zero starvation. What survives is the **fusion** signature, and it is real and reproduced:
      `A_stall < A_full`, i.e. part of the group is certifiable only *after* rigid decisions — the
      user's "360/384 then new symmetry appears" description. **Fusion costs deferral, not
      completeness.** Chang-B shows no fusion (11 nodes, 5 leaves, 96/96).
    · ⚠ **THE EXPANDER-BASE MULTIPEDES DO NOT DISCRIMINATE.** `MP-rr(c6..c10,d3)` — the family this
      doc names as the missing discriminating witness — are all **rigid** (true `|Aut|` = 1) and
      terminate in 1 node. They cannot separate "emitted = true" from "emitted ⊊ true", in either
      colouring. **The part-III witness search must not go here**; the requirement is non-trivial
      `Aut` *and* refinement-resistance, and BuildRandomRegular delivers only the second.
    · ★ **THE ONE GENUINE INCOMPLETENESS FOUND — and it is the C3 gap itself.** The FINE-COLOURED
      Fano multipede (`MP-circ7-typed`, n=42) has type-preserving `|Aut| = 8` (the F₂ gauge) and the
      descent harvests **1, in a single node, with zero harvest calls** — it *presents as locally
      rigid while an order-8 group exists*. Cross-checked both ways because the two instruments
      cannot both be right (refinement cannot discretize a graph with 8 colour-automorphisms):
      ground truth recounted by plain type-preserving backtracking with no WL involved (still 8; the
      rigid m=8 control gives 1), and the canonical form **is stable across 8 relabellings** — so
      this is a harvest miss, **not** a soundness failure. This is exactly what Lean `kernelSupply`
      was built to close, now reproduced on the C# side. It also answers the user's framing: there
      IS a known case where the descent reaches an apparently-rigid state while symmetry remains.
    · **Bearing on part III.** The miss above fires *zero* harvest calls, so it is still not the
      discriminating witness part III needs (one where the supply FIRES and is strictly INCOMPLETE).
      The search stays open, but two candidate directions are now closed by measurement: expander
      multipedes (rigid) and Chang (complete).

    **(superseded, kept for the record) STEP 0 OF (a) WAS ADVERSARIAL:** try to CONSTRUCT a
    witness where the per-level choice matters (two vertices in the chosen sub-cell not related by any
    automorphism of the individualized graph), rather than only sweeping existing witnesses. Absence
    of a falsifier across 5 witnesses is not proof, and the `G8` episode is exactly why. If such a
    witness exists, (a) is dead and the fallback is (b)+budget.
    Until settled `deepenSupply` stays out of `Publication.canonForm?`. `KernelBase.lean` (base recovery + lift) is **superseded by this
    route and parked** — it is not in `build.sh` and is not needed.
    **⚠ PERF, recorded because it recurs:** a first prototype ran **> 1 hour** on `mp7`; the landed
    version measures in ~3 min. Three faults, all standing traps: the twist was a **closure**, so
    each of `IsColAut`'s ~`2n²` applications re-ran `List.contains`/`List.find?` at `O(n)` (**trap
    #1** — cure: materialise as a `Vector`); the per-representative refinement was recomputed once
    per (anchor, `rⱼ`) pair (`|cell|²` warm refinements where `|cell|` suffice); and the `O(n³)`
    `coupled` was computed twice per level and again per pair instead of once and threaded.
  **The original design (as built):**
  · *Extraction* (structural, choice-free — trap #7 clean): rail pairs = same-cell non-adjacent pairs
    whose neighborhoods complement inside every shared gadget cluster (and conflict in none); clusters =
    same-cell gadget vertices with equal rail-pair support (the F3a symmetrized-component toolkit).
    Full enumeration; untrusted (junk recognition costs firing, never ①).
  · *Solve*: variables = rail pairs, checks = clusters; F₂ Gaussian elimination ⟹ kernel basis. Poly,
    computable, no proof obligations on the elimination itself.
  · *Emission* per basis word: flip the word's rail pairs; each gadget vertex ↦ its unique same-cluster
    partner matching the flipped adjacency (`uniqueFilter` — no choice); `permOf` gate; `IsColAut`
    verify (soundness free, as always).
  · *① route — NOT `GensEquivariant`*: the basis is pivot-order-dependent (a genuine trap-#7 choice).
    But the GENERATED GROUP is basis-independent, and flips COMMUTE (a kernel word is the symmetric
    difference of basis words = their product) — so ①/②/③ transfer by the **`SameOrbits` reduction**
    against the set-level reference "all kernel flips" (definable and equivariant because the recovered
    code is canonical; reachability = the P3b/`TreePrune` product-license, `wordReach_of_reaches`).
    This is exactly the "any future supply optimization" reuse the P3c machinery was built for.
  · *Cost*: extraction + elimination `O(n³)`, ≤ n emissions at `O(n²)` — explicit flat bill.
  · *Acceptance*: `mp7` root cells narrow to 1 and `mp7` answers end-to-end with the record + kernel
    supply appended; t3/wr3/ut guards unchanged.
  This is the §11.11 "solver kernel feeds de-fused symmetry back" loop landing consume-side (connects
  to `LinearOracle.lean`; F3b-adjacent — the same recovered system, kernel here, coset ordering there).
- **C4 — large-Aut geometric families (Cameron: Johnson/Hamming/Grassmann; the forms graphs).** Symmetry is
  enormous but localisation at bounded depth fails or costs `n^{O(d)}` with growing `d` (forms base
  `O(log n)` ⟹ quasipoly; Steiner/Latin `Θ(√n)`). → **recognition + coordinatization as a SUPPLY**: recover
  the structure (Route C `IFormStructure` engine; Cameron-scheme recognition for the hidden-Johnson atom),
  emit its known automorphisms as candidates, verify. The untrusted-supply discipline makes recognition
  heuristics *safe* — a wrong recovery costs firing, never ①. This is the poly route that **replaces** the
  deep-oracle ladder on every structured family (see §3 note on `d = Θ(log n)`).

### 1F. Force-side gaps (rigid decisions no built key separates)

- **F1 — module-level Smith/CRT coset ordering (= F3b).** Distinguishable-but-WL-merged copy orderings whose
  invariant is coset data: the multipede double's surviving gauge pair (`MultipedeWitness`, measured,
  off-build) + the C# `K_p□K_p` rook-fiber residual (`null`). → the Smith/CRT canonical-coset key (enters as
  a `Force.Key`; ① = `KeyEquivariant`, the F3a pattern) + the C# `SolveOverA`/extended-Smith wired into the
  lex-min. Gate: confirm the witness genuinely needs the module ordering (close to met — cheaper mechanisms
  measured dead on the double). Also the likeliest force-side regime-change lever if a generic depth-collapse
  is ever needed.
- **F2 — rigid non-linear separation** beyond `lookaheadKey`/`holKey`: rigid graphs whose 1-WL-symmetric
  appearance survives pinning (rigid SRG-land). This is the rigid face of the wall (= W2); the ring solver is
  poly by bounded arity and does not cover it. No mechanism exists; routes live in §1W.

### 1W. The wall — the two faces that remain after 1C/1F close

- **W1 — the schurian/affine face: the forms-graph poly program (LIVE, was "parked").** The seal is BANKED at
  quasipoly (`reachesRigidOrCameron_affinePolar` mod {G3}); the **poly** claim runs through **recovery**, not
  WL: target **T0 = bounded branching / poly leaf count** (empirically supported, `Phase0_BranchProfile`;
  weakest sufficient predicate), mechanism = Route C form-recovery (Lean spine assembled; affine-polar +
  alternating instances sealed; half-spin scoped; Suzuki + char-2/Arf track open). Work items, in order:
  (a) **re-base onto the descent object** — the route-c/recovery docs predate `Descend`/`CostM`/`selNode`;
  recovery must enter as a supply/key of the record object with `SupplyCost` bounds, not as the old
  standalone spine; (b) T0 leaf-count formalization against the real cost model; (c) the remaining family
  instances (half-spin, Suzuki, char-2 needs the Arf/trace substrate); (d) the **transport seam** — firing on
  a graph *realizing* the scheme, not on `schemeAdj` (`RouteCTransport.separatesAtBoundedBase_transport`).
- **W2 — the non-schurian / rigid-non-linear face (IR row 4) + D0.** The genuinely-uncited open core:
  unbounded-`s(C)` residues (generic SRG-land) on the symmetric side, rigid SRG-shaped inputs on the force
  side, plus **D0** (is the reached residue faithfully the `orbitalScheme` model — a modelling obligation).
  Attack routes to run to exhaustion, in rough order of promise: (i) the **iterated/rigid solver** on
  recovery interfaces (the hImprim consolidation steer — `chain-descent-seal-handoff.md` §Update 2026-07-16:
  NOT the deep oracle); (ii) **§11.14** — prove "no non-abelian fusion survives into a rigid medium"
  (negative-witness evidence exists; a proof collapses the rigid residual); (iii) recognition reach — how far
  the C4/W1 recognition legs extend into SRG-land (claw-bounded SRGs at `n^{1/3}` are Spielman-citable;
  what recovers *below* that); (iv) the demoted WL-dim independent-math route
  (`chain-descent-cellsareorbits-route.md`) only if a new idea appears. **Probe program in parallel**: hunt a
  constructible witness that survives all built + planned mechanisms; every dead route recorded in the
  steers archive. Only after this exhaustion does any residue framing become final — and then it is carried
  with its recorded route obituaries, not as a design assumption.
- **W3 — where they meet:** `hSmallAutThin` / rigid-GI. Emptied iff W1 and W2 both close. The endgame-spec's
  "two seals, one wall" frame remains the correct *map*; under §0 the wall is a **target**, not a fixture.

### 1T. Theorem-side gaps (proving the canonizer complete, leg by leg)

- **T1 — per-family localisation** (`Handled` population): `∀ T, CellsAreOrbits` or the lighter `_selected`
  hook discharged per sealed family (first: CFI odd-deg via `theorem_1_HOR_cfi_oddDeg`; depth already
  imports via P2b/P2c). Zero families populated today; this is ③'s content and each leg's totality brick.
- **T2 — cost bounds per new mechanism** (`SupplyCost` pattern: closed-form `c₂`/`keyCost` at land time —
  house rule, not a backlog).
- **T3 — citation discharge** per policy (everything but G3; register + M1–M5 playbook in the discharge doc;
  wiring cautions: G3 only at the Sun–Wilmes threshold, FTPG corrected predicate, Payne–Thas narrowed).
- **T4 — D0** (`SchurianScheme` model faithfulness) — see W2.
- **T5 — the totality assembly** (§0): per-leg `Handled` + the G3 case-split + `hImprim` consolidation ⟹
  `canonForm? ≠ none`; `Publication` evolves from the graded shape to totality as legs close.
- **T6 — statement-level audits** at every wiring point (hypotheses instantiable? non-vacuity `#guard`ed?
  statement = intended claim?) — the 2026-07-16 blocker-audit discipline, applied to each capstone the
  Publication wiring consumes. This is where "any piece might be built insufficiently" is discharged.

---

## 2. THE PLAN — near-term queue, then tracks

**Near-term queue (do in this order; each lands green + guarded before the next):**
1. ✅ **C1 / "F2c"** — DONE 2026-07-19 (`Deck2.lean`; `ut` answers end-to-end — see §1C).
2. ✅ **Publication swap SPIKE** — DONE 2026-07-19, better than scoped: `canonForm?` swapped to the real
   record (fused holKey + fold++deck++deck2) and the WHOLE ① trio filled — `canon_sound`/`canon_complete`/
   `flag_iso_invariant` are `[propext, Classical.choice, Quot.sound]`-clean, no `sorryAx`, no citation
   axioms; zero glue needed (all definitional). `canonizer`'s remaining `sorryAx` = ② + ③ + non-vacuity
   exactly. Record pin provisional by construction (one def + one theorem to strengthen). Statements
   untouched (the finalization steer stands).
3. ✅ **C2 witness** — DONE 2026-07-19, outcome inverted: `wr3` built and measured, `deck2Supply` FIRES
   (identity-default mechanism) ⟹ C2 closed with no new code; C3 re-derived precisely (see §1C).
3b. ✅ **C3 witness** — DONE 2026-07-19: `mp7` (Fano multipede) built and measured, full stack + a
   manual deck3 DEAD (`PerformanceTest` §13, guarded); constructor route DECIDED = the kernel supply.
3c. ✅ **C3 constructor tranche 1** — DONE 2026-07-19 (`KernelSupply.lean` in build; mp7's whole gauge
   consumed in one supply call, 28 → 7 at the root; the all-or-nothing gate = the ①c design lock).
3d. ✅ **C3 tranche 2 — the ① proof stack — DONE 2026-07-19** (all four modules in build, axiom-clean:
   Gauss correctness `KernelGauss`, flip composition `KernelFlip`, reference + `sameOrbits_kernelRef`
   `KernelRef`, σ-equivariance + capstones `KernelTransport`; see §1C C3 ii-b). **`kernelSupply` is IN
   THE RECORD**: `Publication.canonForm?` consumes `fold ++ deck ++ deck2 ++ kernel` and the ① trio is
   axiom-clean at it. ✅ Theorem-index regen also done (257 `Kernel.*` rows described). NOTHING LEFT.
3e. **C3b — BASE-GRAPH RECOVERY + LIFT** (§1C C3 ii-c; RE-SCOPED 2026-07-19 by `PerformanceTest` §15).
   Measured: `mp7` answers at the root the moment ONE base-symmetry generator is supplied (kernel gens
   + the Z₇ translation ⟹ the 28-vertex branch cell is a single orbit). ⛔ The originally-planned
   "deck modulo the verified subgroup" is DEAD standalone (girth 6 ⟹ the translate seed forces 1 of 42;
   quotienting by K creates no chaining). Route: recover the base incidence (rails = segments, wire
   supports = checks — already computed), get its automorphism generators, lift by any gauge-consistent
   completion; ① rides `SameOrbits` because two lifts differ by a pure gauge element ∈ K. Settle the
   three open design questions in ii-c BEFORE building. Acceptance: `mp7` answers end-to-end.
4. **T1 first family** — CFI odd-deg localisation through the weakest hook (de-risk on a C₆-style toy
   first). Output: the first real family in `HandledS` at the record = Publication's handled-half witness.
5. **F1 / F3b** — gate review (the witnesses exist; confirm necessity), then the Smith/CRT key + C# wiring.
   Likely prerequisite: the compiled-eval tranche (interpreted `holKeyFast` is out of range at multipede
   scale).
6. **C# parity tranche** (parallelizable with 1–5): the deckSupply port (~80 lines) + feed the harvest into
   the descent's pruning (§11.11 seam) instead of emitting a total copy order. The C# is the falsifier
   engine — parity is what finds the next C1-shaped hole. Then falsifier sweeps.
7. **W1 kickoff** — read `route-c-plan` + `recovery-route` STATUS, then the re-base design note (recovery as
   record-object supply/key + T0 against `CostM`). This is the biggest research arc; start it while 1–6
   proceed.
8. **W2 program** — begins with the probe program + §11.14 attempt once W1 has momentum; runs to exhaustion
   per §1W.

**Track view:** consume completion (C1→C2→C3, then C4 recognition) · force completion (F1, then F2 via W2) ·
the poly program (W1) · the wall (W2/W3) · theorems interleaved throughout (T1 per leg as it lands, T2 at
land time, T6 at wiring; T3/T5 continuous; Publication updated at each stage).

---

## 3. STANDING CONSTRAINTS (unchanged — machine-checked or settled; do not re-walk)

- **⛔ No stabilizer chain as the guarded object** — no iso-invariant within-cell vertex pick exists ⟹ ①b+①c
  fail. Choosing a CELL is canonical; a vertex within one is not.
- **⛔ "X ⟹ GI∈P, therefore X impossible" is banned** (a perfect key IS the target, not a barrier).
- **⛔ Do not re-unify the contract routes under `Covering`** (value-invisible ⟹ re-imports `canonMin`).
- **P3c does not break the ladder** (measured: `|Aut|`-fold only) — do not re-attempt a per-level collapse by
  strengthening pruning. **`d = Θ(log n)` generic ladder-break: no live route** — and under this plan it is
  **not needed**: every named deep family exits via W1 recovery/recognition; a family needing depth `ω(1)`
  with no recoverable structure lands in W2 and is attacked there.
- **Wreath gauges / "WL-blind non-linear residue" are NOT permanent exclusions** — C2 and W2 respectively
  (corrected 2026-07-18; earlier "correctly in the residue" phrasing meant only "outside the linear leg").
- **Vacuity discipline**: every new predicate needs a discharged instance + `#guard`ed witness in the same
  pass; firing stated graded first; supplies stateless; Lean traps #1/#2 (handoff §7).
