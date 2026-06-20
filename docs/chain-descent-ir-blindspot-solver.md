# The IR-blind-spot solver — canonizing the rigid residue in polynomial time

> **What this is.** The plan for the **rigid-residue solver** that consumes the output of the deferral
> architecture's Phase 2 (`chain-descent-deferred-decisions.md` §7, the "rigid-residue hand-off" slot —
> *named but never built*). Goal: canonize a **rigid** (trivial-`Aut`) residue — including the
> **multipede / IR-blind-spot** that 1-WL cannot discretize — in **polynomial** time, tuned to the exact
> residue. This is the third decision component, sitting in Phase 2, after the cascade (true-symmetry) and
> linear (hidden-abelian) oracles have consumed all symmetry.
>
> **This doc is forward-looking and gated on A2.** The core engine reuses A2's output (a bounded
> distinguishing base). **Pick this up once A2 lands** (`chain-descent-a2-potential-route.md`); the
> headline insight (§2) is that the IR-solver's polynomiality and A2's last open quantity are the **same
> object in two languages**, so progress here is progress there and conversely. Provenance: the deferral
> architecture (`chain-descent-deferred-decisions.md`), the seal's conservation split
> (`chain-descent-general-cc-separability.md`, `PublicTheoremIndex.md`), the canonizer substrate
> (top-level `ChainDescent.lean`).

---

## STATUS (read first)

> **▶▶ RE-BASING (2026-06-20) — READ §11 FIRST; the body below (§1–§10) is the original plan on the *previous*
> A2 skeleton (potential-drop `Φ=(k−1)c`) and remains valid for the *bounded-WL-dim* rigid residue.** Two shifts
> this session, both expanded in the new **§11**:
> 1. **Engine re-base.** A2 pivoted from the potential-drop engine to a **count-injectivity** engine
>    (`discrete_of_kRoundRelationSeparates`, general/landed; the forms-graph build uses it). For a *rigid* residue
>    `RelCountsDetermineOrbit` collapses to that engine's hypothesis verbatim. So the solver's discretization core
>    should be re-based on count-injectivity, not potential-drop (potential-drop stays only as an alt leaf-count bound).
> 2. **The flag set is attackable, not just acceptable — "option 2".** §6 *accepts* the high-WL-dim rigid residue
>    (the multipede) as the flag set. §11 *attacks* it: the multipede is **F₂-linear**, and the existing linear
>    oracle already canonizes the F₂-*symmetry* case (CFI). The new content is to generalize it to F₂-*structure*
>    recovery (no symmetry needed), replacing the WL/unit-propagation descent with **Gaussian elimination** on the
>    descent-extracted F₂ system. **Layer-A viability VERIFIED axiom-/probe-clean (2026-06-20)** — see §11.4.
> The wall is now precisely characterized (§11.1: `b(Aut)` vs `b_WL`); the witness is explicit (§11.2: the
> doubled+matched multipede); the F₂ gap is constructed (§11.4); the honest flag floor moves to the *ring-varying*
> (Lichter) residue (§11.6). **Live thread = §11; Layers A+B+C DONE (mechanism verified on real multipedes; extraction
> prototyped descent-only + SOUND, §11.4a); next concrete step = §11.7 Layer D (the generalized oracle, Lean/C#).**

**Goal.** A polynomial-time canonizer for the rigid residue handed to Phase 2 of the deferral workflow —
a graph (with its coherent-configuration / orbit structure already computed) whose remaining decisions are
all *real* (no path-fixing automorphism relates the choices). The hard sub-case is the **IR-blind-spot**:
rigid (trivial residual `Aut`), yet 1-WL refinement does **not** discretize it at any cheap depth
(multipedes are the canonical example). Cameron sections are **not** the target here — they carry symmetry
and are consumed or flagged in Phase 1; what reaches this solver is genuinely rigid.

**Gating.** The engine's polynomiality is delivered by **A2** (bounded WL-dimension of the residue:
`c(X_{T₀}), k(X_{T₀}) = O(1)` at an `O(1)` base). **Until A2 lands the solver has no polynomial guarantee** —
it degrades to the current exhaustive Phase-2 branching (sound, budget-bounded, may flag). This doc is the
plan to *shrink the flag set to exactly A2's open core* the moment A2 is available.

**State.** *Solver not built.* The prerequisites are landed: the deferral architecture (C#, `EnableDeferral`,
default on; `real_stays_real` proved), the direction-blind canonizer substrate (`warm_6_2`,
`spine_branch_independent`, `canonForm`), the iso-invariant-node template (`forcedNode` + its equivariance
lemmas), and A2's *consumer* chain (`allSingletonFiber_of_card_gt_subset` etc.). **NEW (2026-06-15 — A2 Stage 1a
landed):** the **potential-descent engine the solver reuses is now built and axiom-clean** —
`exists_potential_descent` (the greedy `log`-bound iteration, `§CC.20`), the potential `Φ = (k−1)c`, the
seed-selection predicate `PotentialDrops`, and `exists_small_base_of_potentialDrops`; so the §8 Stage-4 port is
*done* (reuse directly, do not re-port). The **remaining new content** is the canonical greedy selection rule for
the IR phase (§4 — the *witness* of `PotentialDrops`, made iso-invariant) and its wiring to a single-path canonizer.

**Quality bar (unchanged).** Lean side axiom-clean `[propext, Classical.choice, Quot.sound]`, full build
green, no `sorry`, no fresh `axiom`, `native_decide` banned. C# side: sound + iso-invariant (the existing
Phase-2 cross-checks — exhaustive size-5/6 unique-canonical counts, scramble-invariance, Even≠Odd).

**Orientation:** §1 what the residue is and where it sits · §2 the unification with A2 (the headline) ·
§3 why the naive cost is quasipolynomial · §4 the solver design (canonical greedy + direction-blind) ·
§5 the two requirements + the leaf-count subtlety · §6 the flag set = tie-multiplicity = A2 row 4 ·
§7 the SAT/constraint angle (mostly for A2) · §8 build/impl plan · §9 pointers · §10 honest scope ·
**§11 the live thread — option 2: the F₂-structure route for the high-WL-dim rigid residue (the flag-set attack).**

---

## 1. The problem, precisely — what Phase 2 hands in

The deferral workflow (`chain-descent-deferred-decisions.md`) runs in two phases:

- **Phase 1 — symmetry consumption.** Walk the decisions; consume every *unconditional* symmetry
  (cascade certifies an orbit, or the linear oracle harvests a twist), defer every *real* decision. Phase 1
  is **unconditionally polynomial** (both oracles are bounded-work-or-degrade on a single non-branching
  deferred path) — it *cannot* flag.
- **Phase 2 — rigid enumeration.** What remains is a **rigid residue**: every open decision is known-real
  (`real_stays_real`: a real decision stays real under any further individualization), with the orbit
  structure already computed. Current implementation: exhaustive branching with **zero** oracle calls. The
  budget bounds Phase 2 alone; **every flag originates here.**

So the input to this solver is a first-class artifact the old layer-by-layer flow never had: **the complete
rigid residue, orbit-annotated.** "Rigid" means the path-fixing residual group is trivial (`IsBase` /
`StabilizerAt = ⊥`). Three honest sub-regimes reach Phase 2 (`chain-descent-deferred-decisions.md` §6):

1. **Cascade-class / already-discretizing.** Rigid *and* 1-WL discretizes at the base. Canonize for free:
   read the labelling off the rank permutation of the discrete partition. *Not the target.*
2. **IR-blind-spot / multipede.** Rigid, but 1-WL (and even coherent/2-WL at low depth) does **not**
   discretize — `DiscretizesAtBases` fails at bounded depth. **This is the target.**
3. **Hidden Johnson / Cameron.** Unconsumed *non-abelian symmetry* — caught in Phase 1 as un-consumed,
   not rigid. Out of scope here (the seal's "or Cameron" leg).

The key fact the seal records (`recoverableAt_base_iff_discrete`): **at a base, recovery ⟺ discreteness.**
The rigid residue has nothing left to *recover* (no symmetry); the only thing standing between it and a
canonical form is whether refinement **discretizes** it cheaply. That quantity is `DiscretizesAtBases` —
which the seal's conservation split (`stablyRecoverable_iff_symmetric_and_bases`) **deliberately banks** as
the flag-allowed "second guarantee." **This solver is the resolver for that banked term.**

---

## 2. The headline — this solver and A2 are the same quantity in two languages

A2's deliverable (`chain-descent-cxt-scoping.md` §0): bound `c(X_{T₀}), k(X_{T₀}) = O(1)` at an `O(1)` base,
whence `allSingletonFiber_of_card_gt_subset` makes every `T ⊇ T₀` with `|T| > (k−1)c` a **base of `X`** —
i.e. the point extension `X_T` is **complete = discrete**. Unfold what that says operationally:

> **A2 ⟹ a base of size `O(log n)` makes coherent refinement of the residue discrete.**

That *is* "`O(log n)` pinned vertices distinguish the entire remaining structure" — exactly the IR-solver's
precondition. So:

| Seal / A2 language | IR-solver language |
|---|---|
| `c(X_{T₀}), k(X_{T₀}) = O(1)` (bounded WL-dim) | bounded depth + bounded branching to discretize |
| `DiscretizesAtBases` (the banked second guarantee) | the IR-blind-spot resolution problem |
| A2's open **row 4** (unbounded smallest eigenvalue, generic SRG) | the residue this solver must still **flag** |
| potential drop `Φ(T) = c(X_T)` by factor `ρ<1` per seed | the greedy seed-selection rule of the solver |

**Consequence (the reason to write this doc now):** the potential-drop *lemma* that would close A2
(`chain-descent-a2-potential-route.md` §2, `potential_drop`) is *also* the IR-solver's **seed-selection
rule**. Building one is building the other. A poly IR-solver on the residue would constitute A2's row-4
bound; closing A2's row 4 closes this solver's flag set. They are not adjacent — they are identical.

**Caveat — 1-WL vs. coherent (2-WL).** A2 is stated on the **point extension** `X_T` (coherent / 2-WL); the
current canonizer (`ChainDescent.cs`) refines with **1-WL** `warmRefine`. The gap is the known `hcatch`
co-gap (`chain-descent-general-cc-separability.md` §5.1: at a complete extension `WarmTwinsAreFiberTwins ↔
Discrete(warmRefine)`). **Design consequence:** the IR-solver should refine with the *coherent* (2-WL /
`pointExtension`) partition, not bare 1-WL, to inherit A2's guarantee directly — or pin the `hcatch` slack
(a few extra individualizations) to drag 1-WL down to discreteness. Decide this at Stage 1 (§8); the
cheapest correct choice is to run the coherent refinement the A2 substrate already constructs.

---

## 3. Why the naive cost is quasipolynomial (the wall to dodge)

A2 gives a base `T₀` of size `b = O(log n)` that distinguishes everything. The *naive* canonizer — "find a
distinguishing base, enumerate to make it canonical" — has three cost factors. Two are **secretly
quasipolynomial**; only one is genuinely polynomial:

| Factor | Naive count | Honest size |
|---|---|---|
| **Orderings** of the base (`b!`) | `(log n)!` | **quasipoly** — `(log n)! ≈ n^{Θ(log log n)}` |
| **Directions** (`a<b` / `a>b`, direction-agnostic spine) | `2^b = 2^{log n}` | **poly** — `= n` ✓ |
| **Choice** of base set | `C(n, b)` | **quasipoly** — `≈ n^{Θ(log n)}` |

The **direction factor is the one piece that is already polynomial** — the payoff of the project's
direction-blind P-matrix framing (`warm_6_2`, `flipPair_partition_invariant`): a genuine decision is a
*binary direction on a pair*, not a `c`-way choice from a cell, so `b` decisions give `2^b = n` leaves, not
`(cell size)^b`. Ordinary IR (nauty/traces) does **not** get this.

The other two factors are the **Babai quasipolynomial wall** reappearing: naively enumerating "which
`log n` vertices, in which order" is `n^{Θ(log n)}`. The "further optimizations" are not polish — they are
exactly the step that must kill these two factors, and **one move kills both** (§4).

---

## 4. The solver design — canonical greedy base + direction-blind lex-min (single path)

Replace "pick a base, then enumerate" with **iso-invariant greedy base construction**: at each step the
next pin is selected by a rule that is a function of the *graph*, not the *labelling*. Then:

- the **set is determined** (no `n^{Θ(log n)}` selection factor) — there is one canonical base;
- the greedy process **produces them in order** (no `b!` ordering factor);
- the **partition is computed once** (direction-blindness: refinement is independent of the directions, so
  no `2^b` refinement runs), and the lex-min `DirAssignment` is resolved afterward.

**Why iso-invariant selection is *available* here.** The residue is **rigid** (trivial `Aut`), so a
canonical total order on vertices *exists* — no two vertices are interchangeable. The only question is
computing it in poly time, which is what A2 / potential-drop delivers. (Contrast: in a *symmetric* residue
you could not canonically pick "the" vertex of an orbit; rigidity removes that obstruction.)

**The selection rule (the genuine new content).** The project already has the iso-invariant-node template
for the *symmetry* phase: `forcedNode = S₀ ∪ movedSet` is choice-free and relabel-equivariant
(`forcedNode_image`, `forcedNode_relabel`, `movedSet_relabel`). **But `forcedNode` targets `movedSet` (the
residual support), which is *empty* on a rigid residue** — so it is not the IR-phase rule. The IR-phase
rule must instead target the **non-singleton 1-WL/coherent cells** (which persist despite rigidity, because
WL is incomplete) and pick a canonical **splitter**:

> **IR-selection rule (to define and prove iso-invariant):** among the non-singleton cells of the coherent
> partition, take the canonically-first cell `C` (by an iso-invariant cell key — the same cell-id
> machinery the oracles use, `strategy §15 gap 2`), and within it pin the vertex (or pair) that maximally
> drops the potential `Φ(T) = c(X_T)` — the **splitter** of `chain-descent-a2-potential-route.md`'s
> `Shatters`. Ties (≥2 indistinguishable maximal splitters) are the *only* branching (§5, §6).

This rule is exactly the potential-drop seed-selection; its iso-invariance is the IR analogue of
`forcedNode`'s, to be proved the same way (equivariance of `c(X_T)` and the cell key under relabelling).

**Directions.** After the canonical base discretizes the residue, the residual freedom is the direction of
each decision. By direction-blindness the discrete *partition* is identical across directions, so directions
do not re-trigger refinement; the canonical form is the lex-min `DirAssignment` (`canonForm`,
`canonForm_le_canonAdj`). For a rigid residue with a canonical ordered base the directions are pinned by
the greedy order; where they are genuinely free, resolve by **greedy bit-by-bit lex-min** (one pass over
the `≤ b` decision bits), not `2^b` enumeration. *Sub-question to confirm at Stage 2:* that the direction
bits are independently greedily resolvable here (expected for a rigid residue; flag if a counterexample
forces local `2^k` over a `k`-bit coupled block).

**Net shape:** a **single greedy canonical-base path** — pin the canonical splitter, coherent-refine, repeat
until discrete (depth `O(log n)` by A2), then read off the lex-min labelling. No base enumeration, no
ordering enumeration, branching only at ties.

---

## 5. The two requirements, and the leaf-count subtlety (poly vs. quasipoly)

A2 has **two** outputs and the solver needs **both**:

1. **Short base** — depth `b = O(log n)` (the base-size claim).
2. **Bounded branching** — `c(X_{T₀}), k(X_{T₀}) = O(1)`, i.e. bounded *cell sizes along the path*.

**Depth alone is not enough.** If you have only (1) and branch on the *largest* target cell at each level,
the multiplicative drop `Φ(T_i) ≤ ρ^i n` gives a leaf product

```
   ∏_{i<b} Φ(T_i)  ≈  ∏_{i<b} ρ^i n  =  n^b · ρ^{b(b−1)/2}  ≈  n^{(b+1)/2}   (quasipoly)
```

— quasipolynomial *even with a short base*. Polynomiality requires the design rule:

> **Branch on the splitter, not the victim.** Pin the bounded, canonical splitter (which `Shatters`
> guarantees exists); refinement *propagates* and collapses the big indistinguishing-class by a factor `ρ`
> **without** branching `(big cell)`-ways on it. Then per-level branching is `O(1)` (or zero, when selection
> is canonical), and the leaf count is `O(1)^{O(log n)} = 2^{O(log n)} = n^{O(1)}` — polynomial.

So A2's `c, k = O(1)` is not a bonus — it is **load-bearing** for the poly leaf count, and "branch on the
splitter" is what makes the §3 direction factor (`2^{log n} = n`) the *real* count instead of `n^{(log n)/2}`.

---

## 6. The flag set = tie-multiplicity = A2 row 4

With canonical greedy selection the solver branches **only at ties** — two candidate splitters the rule
cannot distinguish at the current coherent-refinement depth, forcing it to try both and lex-min. Hence:

- **Bounded tie-multiplicity ⟹ polynomial** (leaf count `∏ tie-multiplicities`, each `O(1)`, depth
  `O(log n)`).
- **Tie-multiplicity growing with depth ⟹ quasipolynomial** — and *this is exactly A2's open row 4* (the
  unbounded-smallest-eigenvalue **generic SRG**, `chain-descent-a2-potential-route.md` §3, where no
  fast-dropping canonical splitter is known). A tie at depth `d` is precisely "coherent refinement cannot
  distinguish two candidates" = a WL-dimension obstruction at `d`.

So the **flag set shrinks to exactly A2's open core.** The rows A2 already routes elsewhere never reach a
deep tie: geometric → Cameron (carries symmetry, handled in Phase 1), conference → leg B, finite
exceptions → trivially bounded. What can still flag is the generic row-4 residue — *and a genuine row-4
witness with unbounded base would falsify the seal itself* (`chain-descent-a2-potential-route.md` §6, the
off-track falsifier). Standing evidence it is empty: seven 0-witness falsifier sweeps + the A2 monovariant
probe's clean residue/carved split.

---

## 7. The SAT / constraint angle — most useful *on A2 itself*

A SAT/constraint encoding of canonization-as-search is **a reformulation, not new power**: it is
poly-solvable iff the instance lands in a tractable fragment (2-SAT, bounded treewidth/clique-width,
Horn/affine), and *showing it lands there is the poly-resolution theorem*. As a route to **proving**
polynomiality of the generic solver it is therefore **circular** — do not deploy a generic SAT solver and
expect it to manufacture tractability the residue lacks.

**The non-circular use is on A2's bound, not on the canonizer.** The residue's constraint system is
**coherent-configuration-structured**: it is a system of *intersection-number / forced-triangle uniqueness*
constraints (`interNum_eq_one_of_forcedUnique` is literally a uniqueness constraint; `DominatorReachable` is
their closure). So it is *not* a generic SAT instance. A genuine theorem of the form

> **the residue's forced-triangle constraint network has bounded width** (treewidth / clique-width /
> bounded-arity propagation)

would be a *structural* result equivalent to `c(X_T) = O(1)` — a **different proof language** for A2's row-4
bound than the spectral / geometricity invariant the potential-drop route uses. The two need not be equally
hard to prove. **Recommendation:** keep the SAT/constraint framing as an *alternative attack on A2's
`c(X_T)` bound* (a combinatorial-constraint route parallel to the spectral one), **not** as a solver to
bolt onto Phase 2. If A2 closes via the constraint route, the resulting bounded-width network *is* the
poly solver (bounded-width constraint networks solve in poly time), so the two unify at the end anyway.

---

## 8. Build / implementation plan (stages, reuse, risk)

- **Stage 0 — wait for A2 (gating).** Without A2 there is no poly guarantee; the solver = the current
  exhaustive Phase-2 branch. Everything below assumes A2's output (`allSingletonFiber_of_card_gt_subset` /
  `dominatorReachable_of_card_gt_subset` fire on the residue).
- **Stage 1 — coherent refinement in the canonizer (decide the WL level).** Wire the *coherent /
  `pointExtension`* partition into Phase 2 (or pin the `hcatch` slack to keep 1-WL). Reuse: the landed
  `pointExtension` construction + `Sharp (pointExtension X T)`. *Risk: low* (construction landed; the work
  is plumbing it into the C# refinement loop). Resolves the §2 caveat.
- **Stage 2 — the IR-selection rule + its iso-invariance (the genuine new content).** Define the canonical
  splitter rule (§4) on the coherent partition's non-singleton cells; prove relabel-equivariance the
  `forcedNode_relabel` way (equivariance of `c(X_T)` and the cell key). Then prove **single-path
  discretization** under A2 (depth `O(log n)`, branching only at ties). *Risk: medium* — the selection
  rule's well-definedness + tie handling is the crux; getting the predicate right is the vacuity-trap risk
  (cf. `SchemeReproduced`; `chain-descent-a2-potential-route.md` §6).
- **Stage 3 — direction-blind lex-min finish.** Resolve the `DirAssignment` directions by greedy lex-min
  (`canonForm` / `canonForm_le_canonAdj`); confirm independent greedy resolution (§4 sub-question). *Risk:
  low-medium.*
- **Stage 4 — leaf-count / polynomiality theorem.** Prove "branch on splitter ⟹ leaf count `n^{O(1)}`"
  (§5), with the flag set = tie-multiplicity = A2 row 4 (§6). **The `log`-bound induction skeleton is already
  landed** — `exists_potential_descent` (`§CC.20`, the port from `|Aut|` to the potential `Φ = (k−1)c` that A2
  Stage 1a did); reuse it directly. The Stage-4 work is the *leaf-count* bound (tie-multiplicity product) on top
  of that single-path descent. *Risk: medium*, shared with A2's drop lemma.
- **Stage 5 — C# integration + cross-checks.** Replace the exhaustive Phase-2 branch with the
  single-path canonical solver behind the existing `ITransversalOracle`/Phase-2 seam; keep the exhaustive
  branch as the tie/flag fallback. Re-run the Phase-2 cross-checks (exhaustive size-5/6 unique-canonical
  counts, scramble-invariance, Even≠Odd on Petersen/Rook3x3/K6). *Risk: low* (sound by construction; the
  fallback preserves correctness even where the poly path ties out).

**Reuse summary:** the heavy machinery is already landed — `pointExtension` + coherent refinement, the
`c(X_T)` / `Φ` potential and its monotonicity, the `forcedNode` iso-invariance template, the
direction-blind `canonForm`, the `exists_greedy_base` `log`-induction, and A2's consumer chain. The
**new** Lean content is one rule (§4) + two theorems (single-path discretization, leaf-count poly), both
sharing their hard core with A2's drop lemma.

---

## 9. Pointers

**Where it plugs in (deferral / Phase 2):** `EnableDeferral`, `real_stays_real` / `OrbitPartition.mono`
(`CascadeOracle.lean` §C.0); the hand-off slot is `chain-descent-deferred-decisions.md` §7.

**The "at a base, recovery ⟺ discreteness" bridge:** `recoverableAt_base_iff_discrete`,
`forcedNode_recoverable_iff_discrete`, `DiscretizesAtBases` / `discretizesAtBases_iff`,
`stablyRecoverable_iff_symmetric_and_bases` (the conservation split that banks the IR-core) — all
`Cascade.lean`.

**Iso-invariant-node template (to mirror for the IR rule):** `forcedNode`, `forcedNode_isBase`,
`forcedNode_image`, `forcedNode_relabel`, `movedSet_relabel`, `movedSet_eq_nonsingletonCells_of_recoverable`
(`Cascade.lean`).

**A2 output / potential / engine (Stage 1a LANDED):** the engine the solver reuses —
`exists_potential_descent`, `potential` (`Φ = (k−1)c`), `PotentialDrops` (the seed-selection predicate),
`exists_small_base_of_potentialDrops` (`CoherentConfig.lean §CC.20`), and the seal capstone
`reachesRigidOrCameron_viaPotentialDrop` (`CascadeAffine.lean §S-gate2`); the A1 consumer
`allSingletonFiber_of_card_gt_subset` / `dominatorReachable_of_card_gt_subset` /
`reachesRigidOrCameron_viaBoundedExtensionParams` (`§CC.19` / `§S-gate2`); the potential pieces
`indistinguishingNumber`(`_mono`) / `maxValency`(`_mono`) / `pointExtension` /
`interNum_eq_one_of_forcedUnique` (`§CC.10/11/19`); the drop-lemma plan `chain-descent-a2-potential-route.md`
§2–§3 (the IR-selection rule = the witness of `PotentialDrops`).

**Direction-blind canonizer substrate:** `warm_6_2`, `warmRefine_swap`, `flipPair`,
`flipPair_partition_invariant`, `spine_branch_independent`, `DirAssignment`, `canonForm`,
`canonForm_le_canonAdj`, `rankPerm` (top-level `ChainDescent.lean`).

**`log`-bound engine (port DONE — reuse, don't re-port):** `exists_potential_descent` (`CoherentConfig.lean
§CC.20`), the `Φ`-analogue of `exists_greedy_base_aux` / `exists_greedy_base_le_log` (`Cascade.lean`).

**Probe (the evidence, reuse the harness):** `A2MonovariantProbe.cs` (`Probe_CellSizeDropAcrossSRGs`,
`Probe_ScalingResidueVsCarved`) — `Φ` = max cell size drop, residue vs carved.

---

## 10. Honest scope and failure modes

- **Fully gated on A2.** No A2, no poly guarantee — the solver is the exhaustive branch + budget flag. This
  doc's value is the *design that is ready to instantiate the moment A2's bound exists*, plus the
  unification (§2) that makes the two efforts one.
- **Could fail at A2's row 4.** If the generic unbounded-`s` residue admits no uniform fast-dropping
  canonical splitter, ties grow with depth and the solver flags it (quasipoly) — the same boundary the
  seal draws. A *genuine* row-4 counterexample (rigid, small, non-Cameron, unbounded base) would falsify
  the seal (a statement change, itself a result).
- **`Shatters` / selection-rule precision (the Stage-2 crux).** The rule must be strong enough to give the
  drop, weak enough to hold off the geometric locus, and iso-invariant. Too strong = a vacuity trap (the
  project's `SchemeReproduced` history); too weak = no poly bound. Get the predicate right before the
  theorems.
- **Direction-independence sub-question (Stage 3).** Greedy lex-min over `DirAssignment` bits is poly iff
  the bits resolve independently for a rigid residue; a coupled `k`-bit block would cost a local `2^k`.
  Expected fine; confirm.
- **1-WL vs coherent (Stage 1).** If Phase 2 stays on 1-WL, the `hcatch` slack (`O(1)` extra pins) must be
  paid per the build doc; cleaner to refine coherently. A wrong choice here silently reintroduces a gap
  between "A2 guarantees discreteness" and "the canonizer's refinement discretizes."

---

## 11. The live thread — option 2: the F₂-structure route for the high-WL-dim rigid residue

> **What this section is.** The original plan (§1–§10) *accepts* the high-WL-dim rigid residue (the multipede) as
> the flag set (§6). This section *attacks* it. It is self-contained and is the live thread (2026-06-20). Read it
> in order; §11.7 is the milestone tracker (Layers A+B DONE, Layer C next). All probes are reproducible from §11.8.

### 11.0 Where it sits, and the engine re-base
A2 no longer runs on the potential-drop engine (`Φ=(k−1)c`, `exists_potential_descent`); it runs on a
**count-injectivity** engine — `discrete_of_kRoundRelationSeparates` (`CascadeAffine.lean:1916`, **general** over
any `AssociationScheme`, landed, axiom-clean), which consumes "the relation-count profile at a base `T` is injective
across vertices" and outputs `Discrete`. For a **rigid** residue (`Stab(T)` trivial), `RelCountsDetermineOrbit`
(`CascadeAffine.lean:1981`) collapses to that engine's hypothesis *verbatim* (orbits = singletons). So:
- **Re-base the solver's discretization core on `discrete_of_kRoundRelationSeparates`** (count-injectivity), not the
  potential-drop engine. Count-injectivity at `T` literally *is* "T discretizes"; it eliminates §5's leaf-count
  `Φ(T_i)≈ρ^i n` subtlety (no product to bound — just "is the profile injective"). Keep potential-drop only as an
  alternative leaf-count bound if wanted.
- The forms-graph build (`docs/chain-descent-formsgraph-wldim-plan.md`) is the worked example of this engine on the
  *symmetric* (bounded-WL-dim) side; the **Witt-free bridge** technique there (`ScratchWitt.lean`:
  `separatesAtBase_of_isotropySeparates_weak`, a fiberwise partition relating coarse counts to raw relation counts)
  is the **same proof shape** the IR-solver needs to relate coherent-cell counts to the engine's relation counts.

### 11.1 The wall, exactly — two pin-counts, not one
The seal's `O(log n)`-pin bound and the multipede's hardness are about **different quantities**:
- **`b(Aut)`** — pins to kill symmetry (`≤ log|Aut|`); Phase-1 territory. Adding/removing the last symmetry moves
  this by ~1 pin (the near-rigid ≈ rigid continuity).
- **`b_WL`** — pins to make refinement discretize (= count-injective base = WL-dimension); the engine's input.

The whole wall is the **gap `b_WL − b(Aut)`** (the 2-closure deficiency). The multipede is the extreme case:
**`b(Aut)=0` (rigid) yet `b_WL=Ω(n^ε)`** (or `Θ(n)`, §11.4). `b_WL` is *monotone non-increasing* under
symmetry-breaking, so **you can never turn a bounded-WL-dim graph into a multipede by removing symmetry** — the
residue family (bounded `b_WL`) and the multipede (unbounded `b_WL`) are different WL-dimension classes, not
interconvertible by the one-pin operation. The count-injectivity certificate is not *unproven* for the multipede —
it is *false at every bounded base*. (This is why §6's flag is honest: WL/IR provably cannot canonize it cheaply —
Neuen–Schweitzer STOC 2018 exponential IR lower bound.)

### 11.2 The exact witness
**The multipede** (Gurevich–Shelah / Neuen–Schweitzer). Two layers: (i) **CFI F₂-gadgets** over a base graph/incidence
supply WL-hardness — segments `{p⁰,p¹}` (an F₂ value), gadgets enforcing parity; the twist `X̃` is WL-equal to `X`
up to dimension ≈ treewidth (probed in `/tmp/wall_probe2.py`: `X(K_m)` vs `X̃(K_m)` are 1-WL-fooled for all `m`,
2-WL-fooled for `tw≥3` — WL-dim tracks treewidth). (ii) **Rigidification** over a *meager* base (trivial F₂ kernel)
kills CFI's gauge group `Z₂^{|E|-|V|+1}` → rigid → reaches Phase 2 with WL-hardness intact.

**The clean barrier witness — the doubled+matched multipede.** Two copies of a rigid multipede + a perfect matching
of corresponding vertices. `Aut = Z₂` exactly (the copy-swap; rigidity + matching force nothing else). It **separates
the three coordinates** into one constructible object: the copy-swap (permutation symmetry → cascade, one pin), the
F₂ gadget structure (untouched), the rigid WL-hard core (the wall). Use it as the **unit test** that Phase 1 peels
the one symmetry cleanly and the residual cost is exactly the rigid-core cost — i.e. `b(Aut)` and `b_WL` stack
independently. (Note the copy-swap is a *permutation* involution, cascade's job, deliberately not the F₂ kind.)

### 11.3 The mechanism — F₂ structure is conserved across the symmetry boundary
The multipede's segments are F₂ variables; the gadgets are F₂ parity constraints (matrix `H`). The relevant objects:
- **`ker(H)`** = the solutions of the homogeneous system = the **F₂-gauge group**. CFI: `dim ker = k`
  (abelian, harvested by the **existing linear oracle** in Phase 1). Rigid multipede: `dim ker = 0`.
  **⚠ `ker(H)` is only the F₂-gauge part of the symmetry, NOT all of it:** `Aut = ker(H) ⋊ Aut_base(P,L)`, where
  `Aut_base` = the permutation automorphisms of the base incidence. **So `dim ker = 0` does NOT mean rigid** — the
  **doubled+matched multipede** (§11.2) has `dim ker = 0` (block-diagonal `H_M ⊕ H_M`) yet `Aut = Z₂` (the copy-swap,
  a base permutation invisible to `ker`). Option 2 (Gaussian on `H`) discharges `ker`; **`Aut_base` is the cascade's
  job** (Layer D). This corrects the loose "rigid ⟺ `dim ker = 0`" / "`Aut = ker H`" framing.
- **The descent / WL forcing ≈ F₂ unit-propagation** (fix a constraint's last unknown when all others are known) —
  *myopic*, local, stalls on expanders.
- **Gaussian elimination** does row operations unit-propagation cannot; it determines `x` up to `ker(H)`.

So the leaf count is `2^{#decisions}`, and **`#decisions` depends entirely on the engine**: WL → `Θ(b_WL)=Ω(n^ε)`
(the wall); F₂/Gaussian → `dim ker` (= 0 for rigid). **The discontinuity is in the method, not the graph:** the same
F₂ structure manifests as harvestable symmetry in CFI (kernel ≠ 0, linear oracle) and as *no symmetry* in the
multipede (kernel = 0), even though the graphs are one pin apart. **Option 2 = read the *whole* F₂ system, not just
its kernel:** kernel elements = *free* bits (harvest, as today); row-space elements = *forced* bits (propagate by
Gaussian, which WL stalls on). "Generalize the linear oracle from F₂-**symmetry** to F₂-**structure** recovery."

### 11.4 Verified findings (Layer A probe, 2026-06-20 — `/tmp/option2_*.py`)
At the pure-F₂ level (constraint systems as matrices), all three structural claims confirmed:
1. **The decisive gap exists & is constructible.** A **variable-regular degree-4, constraint-size-3 bipartite
   expander** is **RIGID (`dim ker = 0`)** yet its unit-propagation **percolation threshold is `Θ(n)`** (≈0.15n,
   growing). So the descent needs `Θ(n)` pins → `2^{Θ(n)}` leaves, but **Gaussian elimination has 0 free decisions**
   (unique solution). Gaussian strictly beats the descent. *(memory: [[project_option2_f2_gap_2026-06-20]].)*
2. **Confluence = the spine fact** (`spine_branch_independent`): the unit-prop forcing closure is order/direction-
   independent — 1 distinct closure over 8 random orderings.
3. **Circuits — two closures, do not conflate** (corrected). The **descent / unit-prop closure `cl_up`** is
   confluent (= spine) but **NOT a matroid** in general (exchange can fail — the bootstrap-type closure; the same
   non-matroid phenomenon as the prior residue; the probe's "circuit symmetry" only checked single-constraint local
   circuits + passed exchange on an *easy* instance where `cl_up = cl_lin`). The **Gaussian / linear closure
   `cl_lin`** (the full-row-space closure) **is** a matroid — representable over F₂, exchange free. Always
   `cl_up ⊆ cl_lin`; the gap = the WL-hardness. **The plan relies on `cl_lin`, not `cl_up`:** Layer C recovers the
   explicit rows of `H` from local descent circuits (confluence makes them consistent — needs no exchange), then
   Gaussian elimination manufactures the linear matroid. The descent's non-matroidality is precisely *why* Gaussian
   is the tool. Layer C's only requirement: bounded-size local forcing circuits **generate `rowspace(H)`** (they do
   — gadget rows are local circuits, generating by definition). This is the corrected form of "the descent makes the
   global structure partially visible."

### 11.4a Layer C — extraction, prototyped descent-only and SOUND (2026-06-20, `/tmp/option2_layerC_proto.py`)
The extraction recovers `rowspace(H)` **from the descent oracle alone** (no gadget recognition, no peeking at `H`),
then Gaussian → `dim ker`. Validated: rigid (`ker 0`), near-rigid (`ker 1,2`), the soundness trap, the doubled
multipede — every extracted row genuinely in `rowspace(H)` (**SOUND**) and `dim ker` recovered exactly (**CORRECT**).
The algorithm has **three corrections** over the naive "forcing-circuits → rows," all *necessary*:
1. **Cumulative** accumulation up to a **fixed arity bound `D`** (poly `O(n^D)`). Per-size rank is non-monotone
   (probe: size-3-only → full rank, size-4-only → less), so accumulate over all sizes `≤ D`.
2. **Minimality is REQUIRED for soundness** (new finding). Add `support(W)` only if `W` is a forcing-circuit **and no
   proper subset is**. The naive version is UNSOUND: chained size-2 constraints (`x_a=x_b=x_c`) make `{a,b,c}`
   forcing-dependent, yet `e_a+e_b+e_c ∉ rowspace`. Minimality drops it (`{a,b}` already passes). *Why:* `cl_up ≠
   cl_lin` — *minimal* `cl_up`-circuits land in `rowspace`, non-minimal ones need not. Prototype: naive → rows not all
   in `rowspace`; minimal → SOUND across all instances. (For `dim ker`, the rowspace suffices; do **not** try to make
   the extracted rows reproduce the descent's `cl_up` — that needs the actual rows, not just the rowspace.)
3. **`dim ker = 0 ≠ rigid`** — the doubled multipede has extracted `ker = 0`, but the copy-swap `Z₂` permutes the
   constraint set (`Aut_base`) invisibly to `ker` (§11.3 correction). Confirmed in the prototype.

**Scope conditions (state them; they bound the win):** (a) **bounded gadget arity** — `D` is a fixed constant; the
`O(n^D)` cost is poly only for bounded arity (unbounded-arity F₂ structure → the flag floor, §11.6). (b) **WL-easy
base** — extraction + Gaussian discharge the F₂ overlay; the underlying base `(P,L)` must itself be WL-canonizable (it
is for NS multipedes — asymmetric meager graph). A recursively-hard or itself-multipede base is *not* absorbed.
(c) **1-WL** — extraction uses 1-WL forcing probes, where `WL = unit-prop` holds (Layer B); the canonizer's coherent
(2-WL) pass is only *stronger* and also stalls, so the gap argument is robust.

### 11.5 The reframe — option 2's precise marginal value (honest scope)
The probe sharpened *where* Gaussian beats {WL + existing oracle}:
- **Random F₂ systems are EASY** — unit-prop already solves them (forcing# 2–3). Not the wall; no Gaussian needed.
- **Tseitin/expander** (canonical hard XOR): genuinely stalls, **but `forcing# ≈ dim ker`** (ratio ≈1.45, constant).
  Its hardness *is* its kernel = gauge symmetry — already harvested by the existing linear oracle. **Gaussian adds
  nothing here.**
- **The gap regime (`forcing ≫ ker`, `ker` small) = variable-regular / meager structure** (no low-degree peelable
  variables). This is the multipede regime; it is **constructible and not a fine-tuned sliver** (generic var-regular
  expanders land in it). **This is the only regime where option 2 strictly beats the existing pipeline.**

So option 2's content is exactly: **replace unit-propagation with full Gaussian elimination on the descent-extracted
F₂ system.** Existing oracle handles `ker` (symmetry); option 2 handles the *forcing-overhead* `forcing − ker = Θ(n)`
that myopic WL peeling misses.

### 11.6 The flag floor — what option 2 still does *not* close
Gadget-*recognition* is too narrow (multiple formulations reach multipede-like structure with no shared local
signature). Worse, the ceiling recurs: a linear oracle fixed to **F₂** is itself too narrow — **CFI-style
constructions over varying rings** (`Z_{2^k}`) defeat any fixed-field rank operator while staying in P (Lichter,
LICS 2021; FPC+rank ≠ P). So option 2 (F₂ generalization) **absorbs the canonical F₂-multipede** — a large named
chunk of the IR-blind-spot, genuinely shrinking the flag set — but the **ring-varying residue remains the honest
flag floor** (tied to the FPC+rank ≠ P frontier). Two further scope edges (from §11.4a) join the floor: **unbounded
gadget arity** (extraction is `O(n^D)`, poly only for bounded `D`) and a **non-WL-easy / recursively-hard base**
(option 2 discharges the F₂ overlay, not a hard base under it). Cameron is *separately* out of scope: its `O(n)` pins
are `b(Aut)=Θ(n)` (too *much* symmetry, the "or Cameron" leg), the dual corner from the rigid residue.

### 11.7 Milestones (the durable tracker)
- **Layer A — the F₂ gap + structural facts. ✅ DONE (2026-06-20, probe-clean).** §11.4: gap constructed, confluence
  = spine, reversibility = matroid. Reframe (§11.5) established.
- **Layer B — WL = unit-propagation on a REAL graph. ✅ DONE (2026-06-20, `/tmp/option2_layerB.py`).** Faithful
  port of `MultipedeGenerator.BuildMultipede` (the C# Neuen–Schweitzer generator; base biadjacency `A_G` = the F₂
  matrix `H`). **WL-forcing on the real multipede graph = unit-propagation on `H`, EXACTLY** — 50/50 trials on
  circulant (m=6,8,9,11) and random/biregular bases up to 176 vertices, *both directions* (real WL is neither
  stronger nor weaker than unit-prop — the "surprise" risk did not materialize). **Layer A+B tie on one real
  object** (biregular col-deg-4 gadget-deg-3): `dim ker=0` (rigid) + WL==unit-prop + **greedy forcing number grows
  ~linearly** (2,3,3,5,6 over nW=12..60) while `ker=0` → descent pays `2^{Θ(n)}`, Gaussian pays `2^0`. Random
  non-regular stays flat (~3) = easy (confirms the meager/regular requirement). Mechanism + growth-direction
  VERIFIED; asymptotic `2^Ω(n)` magnitude CITED (Neuen–Schweitzer; needs good-expander bases). *(memory:
  [[project_option2_f2_gap_2026-06-20]].)* So the matrix model (§11.3–11.4) genuinely describes the descent, and
  the local circuits are graph-visible — grounding extraction.
- **Layer C — extraction without gadget-recognition. ✅ DONE (2026-06-20, prototyped, `/tmp/option2_layerC_proto.py`).**
  `H` recovered from descent observations alone (cumulative **minimal** forcing-circuits up to fixed arity `D`,
  `O(n^D)`), then Gaussian → `dim ker`. **SOUND + CORRECT** on rigid / near-rigid / soundness-trap / doubled
  instances. Three corrections landed (§11.4a): cumulative accumulation, **minimality required for soundness**,
  `dim ker = 0 ≠ rigid`. Scope: bounded arity, WL-easy base, 1-WL probes (§11.4a). Next = port to Lean/C# in Layer D.
- **Layer D — the generalized oracle (Lean/C#). ⏳, gated on A–C.** Build it against `LinearOracle.lean` / `CFI.lean`:
  determine what the oracle reads *today* (the harvested twist *group* = `ker`) vs. where the **row-space**
  generalization attaches; then "run Gaussian elimination on the extracted `H`, branch only on `ker`." Compose with
  the cascade (which peels permutation symmetry, e.g. the doubled-multipede's `Z₂`). Cross-check on the
  doubled+matched multipede (§11.2) and the §11.8 instances.

### 11.8 Probe reproduction specs (the `/tmp/*.py` are ephemeral — rebuild from this)
- **`wall_probe2.py`** — CFI builder `cfi(base_edges, base_verts, twist_vertex)` (inner vertices = even-subsets of
  incident edges, twist = odd at one vertex; edge vertices `e⁰,e¹`); 1-WL `refine1`, 2-WL `wl2_sig`. Confirms
  `X(K_m)` vs `X̃(K_m)` WL-fooled (1-WL all `m`; 2-WL `tw≥3`), and the gauge group `Z₂^{|E|-|V|+1}`.
- **`option2_layerA.py` / `_layerA2.py` / `_scale.py`** — F₂ matrix model. `gf2_rank` / `ker_dim`; `unit_prop(rows,
  fixed)` = the descent's forcing closure; `perc_threshold` = smallest seed-fraction making the closure complete.
  Constructions: `bipartite_expander(n, d, k)` = variable-`d`-regular, constraint-size-`k` (the **(4,3) rigid
  expander is the headline**: `dim ker=0`, threshold `Θ(n)`); `tseitin_3reg` (forcing ≈ ker, the symmetry case);
  random 3-uniform (easy). Metric to report: **`dim ker` (Gaussian #free) vs unit-prop percolation threshold
  (descent forcing).** Key numbers: (4,3) → ker 0, threshold ≈0.15n; Tseitin → threshold/ker ≈1.45; random → forcing 2–3.
- **`option2_layerC_proto.py`** — the extraction prototype. `Descent.closure(fixed)` = the unit-prop oracle (the ONLY
  graph interface); `passes(oracle, W)` = forcing-circuit test (every member forced by the rest); `extract(oracle, n,
  D)` = cumulative **minimal** circuits up to `D` → candidate rows; soundness = every extracted row `in_span` of the
  true `H`. Run over `bipartite_expander` (rigid / near-rigid via `with_kernel`), the `chain trap` (shows minimality
  is required — naive is unsound), and `doubled` (shows `ker=0 ≠ rigid`, the `Aut_base` `Z₂`). Report: extracted
  `dim ker` vs true, `SOUND`, `CORRECT`.

### 11.9 Decl / pointer map
- **Count-injectivity engine (re-base target):** `discrete_of_kRoundRelationSeparates`,
  `kRoundProfileCount_eq`, `RelCountsDetermineOrbit`, `cellsAreOrbits_of_relCountsDetermineOrbit`
  (`CascadeAffine.lean:1916/1876/1981/1995`).
- **Witt-free fiberwise technique (reuse for coherent↔relation bridge):** `separatesAtBase_of_isotropySeparates_weak`
  (`ScratchWitt.lean`, ported into `CascadeAffine §OrthogonalForm`); see [[project_witt_free_bridge_lead_2026-06-20]].
- **Existing F₂-symmetry oracle (generalize this):** `LinearOracle.lean` / `CFI.lean` (the twist/gauge harvest).
- **Spine / direction-blind substrate:** `spine_branch_independent`, `warm_6_2`, `canonForm` (top-level
  `ChainDescent.lean`) — confluence (§11.4) is `spine_branch_independent` for F₂ forcing.
- **Memory:** [[project_option2_f2_gap_2026-06-20]] (the verified gap + reframe), [[project_witt_free_bridge_lead_2026-06-20]].
