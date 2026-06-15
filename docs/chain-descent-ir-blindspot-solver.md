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

**State.** *Nothing built.* The prerequisites are landed: the deferral architecture (C#, `EnableDeferral`,
default on; `real_stays_real` proved), the direction-blind canonizer substrate (`warm_6_2`,
`spine_branch_independent`, `canonForm`), the iso-invariant-node template (`forcedNode` + its equivariance
lemmas), and A2's *consumer* chain (`allSingletonFiber_of_card_gt_subset` etc.). The **new content** is the
canonical greedy selection rule for the IR phase (§4) and its wiring to a single-path canonizer.

**Quality bar (unchanged).** Lean side axiom-clean `[propext, Classical.choice, Quot.sound]`, full build
green, no `sorry`, no fresh `axiom`, `native_decide` banned. C# side: sound + iso-invariant (the existing
Phase-2 cross-checks — exhaustive size-5/6 unique-canonical counts, scramble-invariance, Even≠Odd).

**Orientation:** §1 what the residue is and where it sits · §2 the unification with A2 (the headline) ·
§3 why the naive cost is quasipolynomial · §4 the solver design (canonical greedy + direction-blind) ·
§5 the two requirements + the leaf-count subtlety · §6 the flag set = tie-multiplicity = A2 row 4 ·
§7 the SAT/constraint angle (mostly for A2) · §8 build/impl plan · §9 pointers · §10 honest scope.

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
  (§5), with the flag set = tie-multiplicity = A2 row 4 (§6). Reuse the `exists_greedy_base_le_log` /
  `exists_greedy_base_aux` `log`-bound induction skeleton (port from `|Aut|` to the cell-size potential —
  the **same port** A2's `potential_drop` does). *Risk: medium*, shared with A2.
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

**A2 output / potential (the engine):** `allSingletonFiber_of_card_gt_subset`,
`dominatorReachable_of_card_gt_subset` (`CoherentConfig.lean §CC.19`),
`reachesRigidOrCameron_viaBoundedExtensionParams` (`CascadeAffine.lean §S-gate2`); the potential
`indistinguishingNumber`(`_mono`) / `maxValency`(`_mono`) / `pointExtension` /
`interNum_eq_one_of_forcedUnique` (`CoherentConfig.lean §CC.10/11/19`); the drop-lemma plan
`chain-descent-a2-potential-route.md` §2–§3.

**Direction-blind canonizer substrate:** `warm_6_2`, `warmRefine_swap`, `flipPair`,
`flipPair_partition_invariant`, `spine_branch_independent`, `DirAssignment`, `canonForm`,
`canonForm_le_canonAdj`, `rankPerm` (top-level `ChainDescent.lean`).

**`log`-bound engine to port:** `exists_greedy_base_aux` / `exists_greedy_base_le_log` (`Cascade.lean`).

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
