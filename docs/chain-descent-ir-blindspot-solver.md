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

> **▶ ENGINE SETTLED + NOT A2-GATED (2026-07-11) — read before §1–§10's A2 gating.** The **live** route is
> option-2 (§11): **exact linear algebra (F₂/ring Gaussian–Smith), poly by bounded arity — NOT gated on A2.**
> §1–§10 is the *superseded* potential-drop plan (A2-gated, stalled at node-4); its "no A2 ⟹ no poly guarantee"
> banner does **not** bind the live route. The engine is a **stepwise alternating fixpoint**
> `… ∘ phase2 ∘ phase1 ∘ phase2 ∘ phase1 …`: the oracle (cascade/linear) *or* the Gaussian/Smith solve each
> resolve **one pairwise vertex relation at a time**, alternating with a 1-WL refine to a fixpoint. At the
> Phase-1 stall (`target == -1`) the solver runs **instead of branching**, and **its kernel is a symmetry
> detector**: a nontrivial kernel-module (F₂, or a ring by §11.13) is a hidden *abelian/linear* symmetry the
> cascade missed because it was fused behind a real decision — **verify it as a genuine automorphism, consume it,
> refine, loop back to Phase 1** (de-fusion). If a relation is forced → determine it; **defer/branch only if BOTH
> stall** (the genuine wall: **non-linear / non-abelian-hidden**; ring-varying is *handled* — `exp(A) ≤ n` native or
> a tower peeled in ≤ n rounds, §11.13a). Only *abelian/linear* hidden
> symmetry is kernel-visible; *non-abelian* fusion stays the cascade's job (§11.14). **Global rigidity is NOT
> required** — the forcing query is local (minimal-circuit → row-space, sound regardless of global rigidity,
> §11.4a); the operative condition is **local rigidity at the relation being forced**, supplied by a
> **consume-before-force** schedule. Soundness + iso-invariance ride on per-step verification + `cl_up` confluence
> (the footing the deferral machinery already stands on), so a bad schedule costs only an *unnecessary-but-sound*
> branch, never correctness. The **fusion-severity bound** ("no harder fusion case can arise"; instrument
> `FusionHarvestProbe`, A_stall vs A_full) is the **efficiency guarantee** for that schedule. **NEXT = design the
> ring first** (§11.13; the F₂ path survives in `Option2ExtractionProbe.cs`, but the Z₄/ring validation was
> ephemeral Python that evaporated — a fresh ring-inference probe anchors B1), then build B1–B3.

> **▶ SEPARATION MEASURED — "SUM NOT PRODUCT" (2026-07-10, C# probe `RruSeparationProbe`; detail
> `[[project_rru_cost_probe_2026-07-10]]`).** The premise of this whole two-phase architecture — that the rigid work
> (Phase 2, node-count / 2^k leaves) and the symmetric work (Phase 1, per-node harvest) can be separated so **neither's
> exponential leaks into the other before it is resolved** — is now measured, not assumed. On `A ⊔ B` (A = rigid
> multipede, 16 leaves; B = symmetric forms graph, 113 harvested generators): with the deferral scheduler ON, the union
> harvests **113 = the SUM** (B's symmetry consumed once, hoisted above A's rigid branching); with it OFF, the union
> harvests **1808 = exactly A_leaves × B_harv, the PRODUCT** (B re-consumed inside every rigid branch), ~100× slower.
> So deferral (`real_stays_real` + hoist-symmetry-above-reals) provably converts product→sum. This holds on the
> refinement-**separable** case; the only way it fails is symmetry+rigidity **entangled in one cell**.
> **The biconditional `no-fusion ⟺ hSmallAutThin` is FALSE (resolved from source 2026-07-10; detail in
> `chain-descent-remaining-work.md` §6 note + `[[project_rru_cost_probe_2026-07-10]]`).** `NoFusion` (defer-all-reals
> harvest = full `Aut`, zero conditional symmetry) ⟹ `hSmallAutThin` (small-Aut ⟹ bounded base) **strictly**; the
> converse fails — Chang-A satisfies `hSmallAutThin` (recovers |Aut|=384 at bounded base) yet violates NoFusion (needs
> ~2 real decisions to do so). So clean separation needs the WEAKER "conditional symmetry bounded", which is **two
> faces**: (small-Aut) `hSmallAutThin` [this §11.11 wall] + (large-Aut) *no hidden-Johnson* [a large Cameron scheme the
> cascade cannot certify at bounded base] — distinct corners, not one predicate. Corollary for the flag: the sound
> trigger is **positive** (`|certified harvested subgroup| > 2^baseMax(n)`, Schreier–Sims-computable, lower-bounds
> |Aut|), NOT the negative "took too long / starved" signal (measured dead: `ClassifyStarved = 0` everywhere; harvest
> depth does not separate rigid from Cameron — CFI(K7) depth 8 > every VO family).

> **▶▶▶ THIS DOC IS THE RIGID HALF OF THE "TWO SEALS, ONE WALL" ENDGAME (frame recorded 2026-07-08).** The
> canonizer has two mirror seals: the **symmetry seal** (non-rigid, handled by **Algorithm A / confinement** —
> route-c-plan §7c) and the **rigid seal** built here (**Algorithm R** — recover the F₂/ring system, solve, flag
> non-linear). They **isolate the same single wall** (§11.11 node-4 unification = `hSmallAutThin` = rigid-GI ∈ P),
> so `UnhandledResidue` collapses toward **one named residue**; §11.14 (no rigid Cameron) tightens it further. The
> **authoritative endgame frame + approved sequencing** is [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md)
> §1a + §5; **the build roadmap for this seal is §11.12** (user-approved: C# B1–B6 + Lean P1–P4, ring-general,
> no new citations). Reuse pricing is DONE (endgame §1a): the symmetric seal's group-harvest does NOT transfer;
> the recovery philosophy + forms/Gauss substrate do; rigid node-4 is handled (D-M0–M4 + `Z₄`). The target is to
> minimize `UnhandledResidue` toward `⊥` (= closing the shared wall), NOT to concede the rigid side.

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
> prototyped descent-only + SOUND, §11.4a). Next concrete step = Layer D, fully designed in §11.10 (C# first — the
> row-space generalization of the deferred/unbuilt C# `LinearOracle`, integrated as a Phase-2 pre-processor). **D-M0
> ✅ DONE (2026-06-20)** — the graph-level probe validated the two seams A/B/C did *not* cover (D1 raw-graph
> decomposition + DQ2 iso-invariance): from raw *scrambled* adjacency the recovered base, `dim ker`, and canonical
> twist-class are all scramble-invariant, and the twist-class **separates** non-isomorphic CFI-twins (matching
> ground truth) — non-vacuous. **D-M1 ✅ DONE (2026-06-20)** — extraction ported to C# against the *real*
> `WarmPartition` refinement (`Option2ExtractionProbe.cs`): extracted `dim ker` = ground truth, scramble-invariant;
> Layer B (WL==unit-prop) confirmed in the genuine machinery. **D-M2 ✅ DONE (2026-06-20)** — canonical twist-class
> `coset_min(c, im A_G)` in C#, scramble-invariant + separating (matches ground truth); the canonical base order is
> free from `WarmPartition`'s cell-ids (no base-canon pass — step removed). **D-M3 ✅ DONE (2026-06-20)** — the
> pre-processor canonizes the rigid multipede **end-to-end** (canonical adjacency matrix), iso-invariant AND complete
> (gauge twin → identical matrix, separating twin differs; coker=0 circulants collapse all twists to one form); the
> coupled directions are resolved by a single linear solve (no F₂-layer IR), closing §4/§10's direction sub-question.
> **D-M4 ✅ DONE (2026-06-20)** — the doubled+matched multipede: the cascade peels exactly the `Z₂` copy-swap
> (`|Aut|=2`, free, scramble-invariant), option-2 owns the rigid core; concerns stack independently. Finding: the
> composition is **fold-via-σ then option-2**, not pin-then-option-2 (D1 misfires on the un-folded residue).
> **★ DESIGN PASS (2026-06-21) — see new §11.11:** the integration hook is `ChainDescent.Search` `target == -1` (the
> deferral Phase-1/Phase-2 boundary, replacing the exhaustive `target = fallback`); the engine is **iterative
> F₂-solve ⊕ 1-WL refine, flag-on-stall**; **`Z_{2^k}` is an F₂ tower** (inside the engine — Lichter doesn't apply, it
> can't individualize); the completeness ceiling = **rigid-GI ∈ P = the seal's `hSmallAutThin` wall** (not refuted by
> no-logic-for-P); route (b) = **F₂→ring via Smith normal form** (ring inference the open piece); and the seal's node-4
> reduction (affine/almost-simple/grid → affine) is the **same "linear = tractable" move** (route §9.9.18).
> **★ SESSION 2026-06-21 (recorded; HANDOFF below):** Z₄ probe DONE (§11.11 — Z₄ handled both levels; native encoding
> forces the full ring, "layer exposure" moot; ring inference = cell-size *insufficient*, must read connectivity §11.13);
> the **build+prove roadmap** is §11.12 (B1–B6 C# / P1–P4 Lean, decisions: ring-from-start, carry-then-discharge bridge,
> model-level, build-first); the **ring design** is §11.13; the **rigid-medium-negates-hidden-Johnson** lead is §11.14
> (abelian hiding vs non-abelian Johnson ⟹ rigid seal may carry *no* "or Cameron").
>
> **▶▶ PICK UP HERE (fresh reader).** All mechanism is validated (D-M0–D-M4 + Z₄), nothing is integrated, no Lean exists.
> The single next action is **B1+B2+B3** (§11.12) — productionize the ring-aware solver and wire it at
> `ChainDescent.Search` `target == -1`, with verify-by-reconstruction; **P1** (L1 extraction-soundness, F₂) can start in
> parallel. **Before D1's ring inference is built**, run the focused **group-recovery sub-probe** (§11.13 open questions:
> recover full `A` from a general-degree gadget relation, iso-invariantly). Reading order for onboarding: this STATUS →
> §11.0–§11.6 (wall + mechanism) → §11.10 (D-M0–D-M4 build) → §11.11 (obstruction/engine/ceiling) → **§11.12 (roadmap) →
> §11.13 (ring) → §11.14 (hidden-Johnson lead)**. Probes: `Option2ExtractionProbe.cs` (12 tests, the C# fixtures);
> `/tmp/*.py` ephemeral (rebuild from §11.8 + §11.11 + §11.13).**

**Goal.** A polynomial-time canonizer for the rigid residue handed to Phase 2 of the deferral workflow —
a graph (with its coherent-configuration / orbit structure already computed) whose remaining decisions are
all *real* (no path-fixing automorphism relates the choices). The hard sub-case is the **IR-blind-spot**:
rigid (trivial residual `Aut`), yet 1-WL refinement does **not** discretize it at any cheap depth
(multipedes are the canonical example). Cameron sections are **not** the target here — they carry symmetry
and are consumed or flagged in Phase 1; what reaches this solver is genuinely rigid.

**Gating — ONLY of the superseded §1–§10 plan (read this).** The §1–§10 plan below delivers polynomiality via
**A2** (bounded WL-dimension: `c(X_{T₀}), k(X_{T₀}) = O(1)` at an `O(1)` base), so *for that plan* "until A2
lands there is no poly guarantee." **The LIVE route is §11 (option 2) and it is NOT A2-gated:** it canonizes the
rigid residue by **exact F₂/ring linear algebra** (Gaussian / Smith), polynomial by **bounded gadget arity**, not
by A2's bounded-WL-dim. A2 is stalled at the node-4 wall; option 2 does not wait on it. A fresh reader should
treat §1–§10 as the *original potential-drop plan* (valid for the bounded-WL-dim residue) and **§11 as the current
attack**; the A2 unification (§2) is a *reformulation* insight, not a blocker on the live build.

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
  Expected fine; confirm. **[RESOLVED for the F₂ residue — §11.10 D-M3: the directions ARE coupled (by the
  F₂ system) but resolved by a single linear solve `A_G·o = c ⊕ coset_min(c)` (unique for rigid), not greedy
  bit-by-bit and not `2^k`. The twist-solve is that resolution.]**
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
- **Layer D — the generalized LinearOracle (C# first, Lean follow-on). ⏳ IN PROGRESS — D-M0 ✅ DONE; D-M1 next. Full design = §11.10.**
  **D-M0 (graph-level end-to-end probe, 2026-06-20, `/tmp/option2_dm0*.py`):** from raw *scrambled* multipede
  adjacency, D1 (recognition-free variable + base-incidence recovery) → D2 (forcing-oracle extraction) → D3/D4
  (canonical twist-class `coset_min(c, im A_G)`) all validated — scramble-invariant, **separating** (merges gauge
  twins, distinguishes genuine ones, matches ground truth), `dim ker` exact, D1/D2 cross-check holds. The two seams
  A/B/C never touched (DQ1 raw-graph decomposition + DQ2 iso-invariance) are now probe-clean. **D-M1 (C# extraction
  vs the real `WarmPartition`, 2026-06-20, `Option2ExtractionProbe.cs`):** ✅ extracted `dim ker` = ground truth,
  scramble-invariant (Circ 6/8/9→0, m=7→3, RandReg(8,6,3)→0); Layer B holds in the genuine refinement. **D-M2
  (Gaussian solve + canonical twist-class, same probe file):** ✅ twist-class `coset_min(c, im A_G)` scramble-invariant
  + separating (matches ground truth); **the canonical base order is free from `WarmPartition` cell-ids — base-canon
  pass removed.** **D-M3 (pre-processor integration, end-to-end canonization, same probe file):** ✅ full canonical
  adjacency matrix, iso-invariant + complete (gauge twin → identical matrix; coker=0 circulants collapse all twists);
  coupled directions resolved by one linear solve (no F₂-layer IR) — closes §4/§10's direction sub-question. **D-M4
  (composition with the cascade, same probe file):** ✅ cascade peels exactly the `Z₂` copy-swap (`|Aut|=2`, free,
  scramble-invariant), option-2 owns the rigid core, concerns stack independently — **composition is fold-via-σ then
  option-2, not pin-then-option-2** (D1 misfires on the un-folded residue). Next = D-M5 (fallback/flag + cross-checks).
  Layer D **is** the *deferred, unbuilt* C# `LinearOracle`, generalized: `TwistConstruction.cs` already does the
  `ker H` half (constructs twists = F₂-symmetry); Layer D adds the **row-space** read (forced decisions) the rigid
  case needs. Integrates as a **Phase-2 pre-processor** — decompose `(base (P,L), twist-class)`, canonize the base via
  the harness, **solve the twist-class by F₂ Gaussian** (bypassing IR for the F₂ layer); branch only on `ker`; the
  cascade handles `Aut_base` (the doubled-multipede `Z₂`). **First step = D-M0** (a graph-level probe validating the
  two seams A/B/C did not cover — D1 raw-graph decomposition + iso-invariance — before any C#). C# pieces D1–D8, Lean
  L1/L2, the iso-invariance closure, risks, milestones D-M0..M6: **§11.10**.

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
- **C# Layer-D substrate (the build target — see §11.10):** `GraphCanonizationProject/ITransversalOracle.cs` (the
  seam; the `LinearOracle` is *deferred/unbuilt*, only `CascadeOracle.cs` is wired), `RefinementFootprint.cs` (the
  descent/forcing observation = the Layer-C oracle), `TwistConstruction.cs` (the `ker`/F₂-symmetry half — generalize
  this to the row-space), `ChainDescent.cs` (the harness; `Classify` at line 268), `MultipedeGenerator.cs` /
  `CfiGraphGenerator.cs` (fixtures), `chain-descent-linear-oracle.md` (the oracle's spec — Layer D generalizes it).
- **Spine / direction-blind substrate:** `spine_branch_independent`, `warm_6_2`, `canonForm` (top-level
  `ChainDescent.lean`) — confluence (§11.4) is `spine_branch_independent` for F₂ forcing.
- **Memory:** [[project_option2_f2_gap_2026-06-20]] (the verified gap + reframe + Layer A/B/C + the Layer-D plan),
  [[project_witt_free_bridge_lead_2026-06-20]].

### 11.10 Layer D — design: the generalized LinearOracle (the build)

> **Read this to start Layer D.** Layers A–C are done (gap real, matrix model = the real descent, extraction sound).
> Layer D turns the validated mechanism into a working canonizer component. It **is** the deferred C# `LinearOracle`,
> generalized from twist-construction (the `ker`/symmetry half, already specced) to row-space reading (forced decisions).

**Grounding — the C# architecture (verified by reading the source, 2026-06-20).** The `LinearOracle` is *designed but
unbuilt* (`ITransversalOracle.cs`: "the deferred LinearOracle … discovering twists from propagation patterns"; only
`CascadeOracle` is wired in `CanonGraphOrdererChainDescent.cs`). **Half its mechanism already exists:**
- **`RefinementFootprint.cs`** = the descent/forcing observation: individualize a target-cell rep, warm-refine, read
  the cell splits = "the decision's coupling." This **is** the forcing oracle Layer C runs on (`closure(fixed)`).
- **`TwistConstruction.cs`** = builds a twist (path-fixing automorphism) from the footprint by canonical-colour
  matching — "for CFI this is the gadget-parity flip." This is the **`ker H` / F₂-symmetry half**.
- **`ITransversalOracle` / `ChainDescent.cs`** = the seam (`Classify` returns orbit-covering reps) + harness
  (composes oracles, harvests automorphisms a-posteriori).

So **Layer D = the row-space generalization**: `TwistConstruction` handles `ker H` (symmetry, twist); Layer D adds the
row-space read (the *forced* decisions) the rigid case needs (`ker = 0` ⟹ no twist to construct ⟹ the existing oracle
finds nothing ⟹ today the multipede *flags*; cf. `chain-descent-linear-oracle.md` intro).

**Recommendation — C# first.** All infrastructure exists; the remaining risk is integration/empirical (canonize real
multipedes, scramble-invariantly, compose with the cascade) — a C# question with a ready cross-check harness. **Lean is
a heavy follow-on:** the multipede is the *non-schurian residue outside the seal's scope* (C3), so its proof is a *new*
poly-or-flag theorem (F₂-Gaussian canonization), not the landed seal machinery — defer until C# validates and the
statement is pinned. (One standalone Lean lemma is worth doing early — L1.)

**Architecture decision — a Phase-2 PRE-PROCESSOR, not a per-node oracle.** For a *rigid* multipede the IR leaves are
all distinct (no automorphism pruning), so a per-node "return one rep" oracle would violate the orbit-covering
soundness contract (`ITransversalOracle.cs`). Clean framing: **decompose the residue into `(base (P,L), twist-class)`**,
canonize the base via the existing harness (WL-easy), and **solve the twist-class by F₂ linear algebra** — bypassing IR
for the F₂ layer entirely. `TwistConstruction` is the `ker`-half; Layer D's solver is the row-space half. IR branching
remains only for the base and the kernel (small), where the harness + cascade already work.

**The C# pieces:**
- **D1 — decision/variable identification.** From the Phase-2 entry partition, the non-singleton cells = F₂ variables
  (binary decisions); recover the `(P,L)` base ↔ F₂-overlay split. *(new; reuse direction-blind framing. Real risk —
  DQ1.)*
- **D2 — extraction.** Drive `RefinementFootprint` as the forcing oracle; run the Layer-C algorithm (cumulative
  **minimal** forcing-circuits up to fixed arity `D`, `O(n^D)`) → `H` over the decisions. *(new; Layer-C port + the
  minimality soundness guard, §11.4a.)*
- **D3 — the twist constants `c`.** Read which parity each gadget enforces (the inhomogeneous part), extending
  `TwistConstruction`'s canonical-colour matching to read a *value*, not just build an automorphism. *(extends
  `TwistConstruction`; DQ3 = stay recognition-free.)*
- **D4 — F₂ Gaussian solve.** Rank and the canonical twist-class. **The twist-class is the coset `c + im(A_G)` =
  the `coker(A_G)` class** (D-M0 finding): `c` itself is gauge/orientation-dependent (flipping a segment adds a column
  of `A_G`), so the iso-invariant content is `c mod im(A_G)`, taken as the lex-min coset rep over the canonical base
  order. It is nontrivial **iff `nV > nW`** (a square base ⟹ `coker = 0` ⟹ *all* twists isomorphic) — this is what
  makes the canonical form *separate* non-isomorphic twins rather than be a vacuous constant. A canonical `ker` basis
  (RREF) only for standalone mode (`ker = 0` in-pipeline). *(new; soundness = the iso-invariance closure below ≡ scope (b).)*
- **D5 — pre-processor integration.** **★ The precise hook is `ChainDescent.Search` `target == -1` (`ChainDescent.cs:243-257`),
  replacing the `target = fallback` exhaustive branch — see §11.11.** Decompose `(base, twist)`, ~~canonize base via harness~~
  **read the canonical base order off `WarmPartition`'s iso-invariant cell-ids** (D-M2 finding — the fine-coloured rigid residue is
  WL-discrete at the cell level, so *no* base-canonization pass is needed inside option 2; harness/cascade branching
  is reserved for genuine `Aut_base`, consumed upstream — see D6), solve twist via D4, emit
  the canonical labelling; IR for the F₂ layer → 0. **In-pipeline `ker = 0` always** — the F₂-gauge symmetry is
  consumed upstream by the linear oracle (`TwistConstruction`) and permutation symmetry by the cascade, so the Phase-2
  residue is genuinely rigid. **So option 2's in-pipeline content is the row-space / *forced* solve ONLY**; the
  `2^{dim ker}` kernel-branching is a *standalone-mode* feature (option 2 run without Phase 1), not part of the
  integrated path. *(new; the wiring.)*
- **D6 — cascade/kernel composition.** `ker H` (gauge) branches/harvested by the existing twist machinery; **`Aut_base`**
  (the doubled-multipede `Z₂`) peeled by the cascade. **★ CORRECTED (D-M4 finding): the composition is FOLD-via-σ then
  option-2, NOT pin-then-option-2.** After the cascade breaks `Z₂` with one pin the doubled residue has *mixed* cells
  (`22×size2, 6×size4` on doubled-Circ6) — split gadget-middles also become size-2, so D1's "size-2 = segment" rule
  **misfires** on the un-folded residue. The cascade harvests the copy-swap `σ` *explicitly* (`|Aut|=2`, verified
  free, orbits `{i, i+n}`); option-2 must use `σ` to **quotient onto one copy** (the rigid core) and then canonize that
  (D-M3 handles it). So D6 = fold via the harvested auto, *then* option-2 — not run option-2 on the pinned graph.
  *(the iso-invariant `σ`-fold quotient is the remaining integration piece here; doubled multipede is the test.)*
- **D7 — fallback/flag (verify-or-flag).** The succeed/flag verdict must be **iso-invariant** (else isomorphic inputs
  split between option-2 and the exhaustive fallback ⟹ completeness violation, §11.11). Discharge: emit the candidate,
  **verify by reconstruction** (rebuild from `(base, H, c, orientation)`, check it matches the input); mismatch — or
  extraction failure (unbounded arity / non-WL-easy base / ring-varying, §11.6) — → exhaustive branch (sound, may flag).
  *(new; the boundary. This is the reduced "item 4" — rigidity itself is Phase-1's contract, not a check here.)*
- **D8 — iso-invariance + cross-checks.** Scramble-invariance, exhaustive size-5/6, Even≠Odd, + a new rigid/doubled
  multipede battery. Iso-invariance is the closure below (canonical base order ⟹ deterministic twist; `canonForm` ∘
  solve), validated empirically first in D-M0. *(new; validation.)*

**Lean follow-on:** **L1 (do early, standalone):** the extraction-soundness lemma — *minimal forcing-circuits generate
`rowspace(H)`* (the `cl_up ⊊ cl_lin` subtlety, §11.4a). Pure F₂/matroid, no graph; anchors the one non-obvious
correctness claim. **L2 (deferred, heavy):** the generalized solver's poly-or-flag/soundness theorem (canonical form
produced; poly for bounded arity). Its statement is the **F₂-Gaussian** one — *not* a `discrete_of_kRoundRelationSeparates`
instantiation: count-injectivity (§11.0 re-base) and Gaussian *coincide in proving discreteness* but the solver's
*mechanism* is row-reduction, not relation-count. **Why it can't reuse the seal machinery (the precise reason):** a
rigid multipede's *orbital* scheme is discrete (trivial `Aut`), but its **2-WL closure is a non-schurian coherent
configuration** (strictly more relations than orbitals — that *is* the WL-hardness) — exactly the object **outside the
seal's schurian-residue scope** (C3). So L2 is a genuinely new F₂-Gaussian-canonization formalization.

**Soundness / iso-invariance — the crux, and its closure.** Canonization (vs. iso-*testing*) needs an iso-invariant
labelling, and this is a *soundness* property, the design's thinnest point. **Closure:** it is **not new machinery** — it
is the existing `canonForm` "lex-min over symmetry branches" pattern with the F₂ solve as a *deterministic per-branch
function*. Factor `ℓ = (base ℓ_B, twist x)`: (1) the harness canonizes the base, branching over base ties = `Aut_base`;
**under scope (b) the base WL-discretizes per branch**, so the WL-colours give a **canonical variable order**; (2) given
that order, `Hx = c` is a coset `x₀ + ker(H)`, and in-pipeline `ker = 0` (D5) ⟹ the twist is **deterministic** — a pure
function of `ℓ_B*`, *no new ties*; (3) overall `= min over Aut_base-branches of (base adjacency + twist-solve)` =
`canonForm` ∘ deterministic-solve. The base-tie × twist interaction the design must respect is exactly the `Aut_base`
branching the harness already does. **Key consequence: scope (b) [WL-easy base] is the *soundness* condition, not a
performance one** — it is what makes the variable order canonical, hence the twist iso-invariant; a recursively-hard
base (base not WL-discrete) is the flag floor and never reaches the twist-solve. So **DQ2 ≡ scope (b)**, not a separate
risk.

**Open design questions / risks:** **DQ1** — base/twist decomposition recovery from the *raw* graph — *the real risk,
and the only seam A/B/C did not cover* (their probes ran on the F₂ matrix with variables/rows given; D1 is raw
adjacency → identify variables + base split, recognition-free per §11.6). Clean for NS multipedes, murkier generally.
**DQ2 = the iso-invariance closure above** (≡ scope (b); base WL-discrete ⟹ canonical order ⟹ deterministic twist).
**DQ3** — reading `c` recognition-free (extend colour-matching). **DQ4** — fallback soundness where the F₂ path flags.

**Milestones:** **★ D-M0 — graph-level end-to-end PROBE. ✅ DONE (2026-06-20, `/tmp/option2_dm0.py` + `_dm0v2.py`).**
Faithful port of `BuildMultipede` (segments, even/odd-subset gadgets, the F₂ matrix `H = A_G`); raw adjacency
**scrambled** (random vertex relabel + random colour-id relabel, so colour names carry no info) → **D1**
(recognition-free: 1-WL, size-2 cells = segments, gadget-cell↔segment-cell incidence = recovered `Ĝ`) → **D2**
(graph-level forcing oracle = individualize + 1-WL; cumulative **minimal** circuits → `H`) → **D3/D4** (read `c` by
per-gadget parity; **canonical twist-class = `coset_min(c, im A_G)`** over the canonical base order). **Results
(all PASS):** (i) base incidence recovered scramble-invariantly, #segments exact; (ii) twist-class scramble-invariant
**and SEPARATING** — on a coker-dim-2 base (`nV=8>nW=6`) it merges the gauge twin (`e₀∈im A_G`, *isomorphic*) and
distinguishes the genuine twin (`e₁∉im A_G`), **matching base-level ground truth exactly** (non-vacuous: invariance +
completeness of the F₂ layer's canonical form); (iii) extracted `dim ker` = ground truth (0 on odd/rigid `m=6,8` +
RandReg(8,6,3); 3 on non-odd `m=7`); (X) D2's `rowspace(H)` = D1's `rowspace(A_G)` (two independent recoveries agree).
**Scope of the probe:** small bases (`nW≤8`), degree-3 gadgets (segments = size-2 cells; the size-2 rule is the
arity-3 instance of "non-singleton-cell" D1), base canonized by a brute IR-lite standing in for the harness/cascade
(scope (b)). Validates the F₂-layer mechanism *and* the iso-invariance/separation soundness crux end-to-end from the
raw graph — the two seams A/B/C never touched (DQ1 + DQ2). Untested below: C# integration (D-M1+) and a genuinely
non-WL-easy base. **D-M1 — extraction in C# vs the REAL refinement. ✅ DONE (2026-06-20,
`GraphCanonizationProject.Tests/Option2ExtractionProbe.cs`).** The forcing oracle drives the genuine `WarmPartition`
(the descent's 1-WL) via the same `p`-pin `ChainDescent.Individualize` uses; cumulative minimal circuits → `H` →
F₂ rank. **Extracted `dim ker` = ground truth on every run, scramble-invariant:** Circulant `m=6,8,9` → 0 (rigid),
non-odd `m=7` → 3, `RandReg(8,6,3)` (nV>nW high-treewidth) → 0; segments recovered recognition-free as the size-2
stable cells (= nW exactly). **Finding (no surprise = the result):** Layer B (WL == unit-propagation) holds in the
*real* C# refinement, not just the Python port — the "WL might be stronger" risk did not materialize in the genuine
machinery. **D-M2 — Gaussian solve + canonical twist-class in C#. ✅ DONE (2026-06-20, same probe file,
`TwistClass_Invariant_And_Separating`).** Twist-class `= coset_min(c, im A_G) ∈ coker(A_G)` over the canonical base
order; `c` read recognition-free (per-gadget parity under an arbitrary orientation, gauge modded out). **Scramble-
invariant AND separating:** on a coker-dim-2 base (`nV=8>nW=6`) all 8 single-gadget twists give a distinct class
(matching `e_g ∉ im A_G`) and the **constructed gauge twin** `supp(col_0)` merges with untwisted (matching `e_T ∈ im`)
— all matching base-level ground truth; `dim ker = 0` ⟹ unique twist. **★ STEP REMOVED (D-M2 finding):** the
canonical base order is **free from `WarmPartition`'s iso-invariant cell-ids** — the fine colouring makes the rigid
residue's base WL-discrete *at the cell level* (each segment its own 2-cell, each gadget its own cell), so there is
**no base-canonization pass inside option 2** (D-M0 used a brute IR-lite; the real machinery does not need it). This
realises scope (b) directly; see the D5 note. **D-M3 — pre-processor integration, canonize end-to-end. ✅ DONE
(2026-06-20, same probe file: `CanonizeEndToEnd_Invariant_And_Complete` + `CanonizeEndToEnd_Circulant_AllTwistsMerge`).**
Full canonical adjacency from: base order (WL cell-ids) + **unique orientation from the twist solve** `A_G·o = c ⊕
coset_min(c)` (rigid ⟹ `ker=0` ⟹ unique `o`, *no* `2^{nW}` enumeration) + middles ordered by subset under that
orientation. **Iso-invariant AND complete:** (coker>0 base) scrambles → byte-identical matrix, the **gauge twin
canonicalises to the SAME matrix** (proof the twist-solve *canonicalises*, not merely classifies) and a separating
twin differs; (coker=0 circulant m=6,8) **all `m` distinct single-gadget-twisted graphs collapse to one identical
canonical form**, scramble-invariant. **★ SUB-QUESTION RESOLVED (D-M3 finding):** this closes §4/§10's *direction-
independence sub-question* (the worry that resolving direction bits could hit a coupled `k`-bit block costing a local
`2^k`). The directions *are* coupled — by the F₂ system — but they are resolved by a **single linear solve** (unique
for rigid), not greedy bit-by-bit and not `2^k`. The twist-solve **is** the poly resolution of that deferred sub-question
for the F₂ residue. **D-M4 — composition with the cascade. ✅ DONE (2026-06-20, same probe file:
`DM4_Cascade_Peels_Z2_Then_Option2_Core` + `DM4_Explore_DoubledMultipede`).** Doubled+matched multipede: the cascade
harvests **exactly** the `Z₂` copy-swap (`|Aut|=2`, free, orbits `{i,i+n}`, scramble-invariant — nothing spurious from
the F₂ structure), `b(Aut)=1`; option-2 owns the rigid core (D-M3). Concerns stack independently (`b(Aut) ⊥ b_WL`, the
§11.2 claim). **★ COMPOSITION CORRECTED (D-M4 finding):** **FOLD-via-σ then option-2**, not pin-then-option-2 — after
one pin the residue has mixed cells (`22×size2, 6×size4`), D1's size-2 rule misfires; the cascade gives `σ` explicitly,
option-2 quotients onto one copy then canonizes (D6). Aside: circulant multipedes canonize cheaply (thin base, not
IR-hard at probe sizes — IR-hardness is asymptotic/high-treewidth, cited); the mechanism is identical regardless.
**D-M5** fallback/flag + full cross-check battery. **D-M6** Lean: L1, then (later) L2.

### 11.11 Obstruction class, the iterative engine, and the completeness ceiling

> Synthesis of the 2026-06-21 design pass. Settles where option-2 plugs in, what "never flag on a rigid residue"
> can and cannot mean, and how it aligns with the seal's node-4 reduction. Supersedes the looser "pre-processor"
> framing in §11.10 D5 and the flag-hook sketch.

**Integration point (the precise hook).** Option-2 is the Phase-2 handler at the deferral boundary in
`ChainDescent.Search`, the **`target == -1` branch** (`ChainDescent.cs:243-257`): every remaining non-singleton cell
is a *real* decision = the Phase-1/Phase-2 boundary. Normal mode currently runs `target = fallback` (exhaustive branch
→ flag); **option-2 replaces that line.** (`RecoveryOnly` is test instrumentation, not a real-use path.) At this point
the residue is **rigid by construction** — Phase 1 consumed all symmetry (`real_stays_real`) — the canonical base order
is `partition.CellOf` (free, D-M2), and any harvested `Aut` (e.g. a doubled `Z₂`) sits in `Automorphisms`. Strictly
better than a flag-hook: no wasted exhaustive branch, runs on *every* rigid residue (circulants included → speedup +
built-in regression), and the soundness-fatal mis-detection (treating a *symmetric* graph as rigid) **cannot arise** —
rigidity is Phase-1's contract, not option-2's job.

**The residual soundness obligation (the reduced "item 4").** Option-2 must correctly canonize the rigid residue *or*
flag, and its succeed/flag **verdict must be iso-invariant** (else isomorphic inputs split between option-2 and the
exhaustive fallback ⟹ completeness violation). Discharge: emit the candidate labelling, then **verify by
reconstruction** — rebuild the graph from `(base, H, c, orientation)` and check it matches the input; mismatch → flag.
Sound (flagging is always safe), iso-invariant (deterministic), bounded. A flag now means "obstruction outside the
handled class" — Phase-1 starvation (a slipped symmetry / Cameron) or a genuinely non-handled residue — never
"IR-blindspot we can't touch."

**The engine: a stepwise alternating fixpoint `… ∘ phase2 ∘ phase1 …`, flag-on-mutual-stall (settled 2026-07-11).**
The oracle (cascade/linear) *or* the Gaussian/Smith solve each resolve **one pairwise vertex relation at a time**;
they alternate, with a 1-WL refine between, to a fixpoint. Per relation: the oracle **consumes** it if a *verified*
automorphism moves it (symmetry); else the solve **forces** it if it lies in the current row-space (rigid); else it is
**deferred** (a genuine free real decision → branch as today, may flag). At the Phase-1 stall (`target == -1`) the
solver runs **instead of** the exhaustive branch, and **its kernel is a symmetry detector**: a nontrivial
kernel-module (F₂, or a ring by §11.13) is a hidden *abelian/linear* symmetry the cascade missed because it was
**fused** behind a real decision — verify it as an automorphism, consume it, refine, and **loop back to Phase 1**
(de-fusion). Only *abelian/linear* hidden symmetry is kernel-visible; *non-abelian* fusion stays the cascade's job
(§11.14).
- **Global rigidity is NOT a precondition.** The forcing query is *local* (minimal-circuit → row-space is sound
  regardless of global rigidity, §11.4a), so the solver never needs the residue globally rigid to attack a relation.
  The operative condition is the weaker **local rigidity at the relation being forced**: the symmetry that relation
  depends on must already be consumed. A **consume-before-force** schedule supplies it; getting the schedule wrong
  forces a relation that still looks free → an *unnecessary but sound* branch (never a wrong answer — `cl_up` is
  confluent, every step is verified). The negative probe "Chang-A's rigid core cannot be handled before its symmetry
  is removed" is exactly this ordering fact (consume must precede force), not a failure.
- **Iso-invariance is inherited, not new.** Each step's resolve/consume/defer verdict is a pure function of the
  (iso-invariant) structure, and each consumed symmetry is verified as a genuine automorphism — the same footing the
  existing deferral machinery already stands on; the fixpoint adds no new choice, hence no new obligation.
- **Cost is polynomial.** Each oracle pass is `O(n⁴)`; ~`n` passes between successful rigid steps and ~`n` rigid steps
  give an `O(n⁶)`-ish interleave — slow, not exponential; the deferral scheduler's product→sum win (killing the
  *exponential* product) is untouched.
- **The fusion-severity bound is the poly guarantee.** For a fixed residue class the fusion is *mild* and bounded
  (`FusionHarvestProbe` A_stall vs A_full; for Chang-A the cascade already harvests the bulk, leaving a small
  conditional remainder). A bound "no harder fusion case can arise" bounds how far consume-before-force must look
  ahead — i.e. it *is* the schedule's polynomial guarantee. This is the deliverable that generalizes the mild Chang-A
  measurement.

This **extends scope (b)** from "WL-easy base" to "**F₂/ring-tower base**" — a multipede whose base is itself a
multipede (of the same or a lower ring) is peeled layer by layer by the alternation.

**The completeness ceiling — three distinct claims (keep them separate).**
1. *"F₂ is the only obstruction to 1-WL"* — **FALSE** (Lichter's CFI-over-`Z_{2^k}` is rigid, 1-WL-hard, not F₂).
2. *"every rigid obstruction is linear over some abelian ring (CFI-type)"* — **CONJECTURE**, strictly broader
   (F₂ ⊊ `Z_{2^k}` ⊊ rings); not believed to capture all of P.
3. *"some rigid obstruction is non-linear"* — **OPEN, no constructible witness** (consistent with the 0-falsifier record).

**`Z_{2^k}` is INSIDE the iterative engine, not the floor (corrects an earlier error in this thread).** `Z_{2^k}` is a
k-layer F₂ tower, carries included: solving mod 2 makes the low-bit sum `S₀` a *known integer*, and the mod-4 layer is a
clean inhomogeneous F₂ system on the high bits (`b₁x+b₁y+b₁z ≡ (c−S₀)/2 mod 2`), and so on (the 2-adic content of Smith
normal form). So **iterative-F₂-*with-individualization* = `Z_{2^k}` solving.** Lichter does *not* refute this: his lower
bound is on **FPC + F₂-rank, which cannot individualize** — it computes the global F₂-rank statically, exactly missing
the 2-torsion; the IR-solver individualizes.

**★ Z₄ PROBE DONE (2026-06-21, `/tmp/z4_probe.py`) — Z₄ (2²) IS HANDLED, both levels.** (A) **Algebra:** iterative F₂
(solve mod 2 → carry `(c−Hx₀)/2` → solve mod 4) recovers the **unique** Z₄ solution of a rigid Z₄ system, matching brute
force, on circulant m=6,8,9. (B) **Graph (native Z₄-multipede:** 4-state segments, gadgets `Σ ≡ 0 mod 4`, rigid by odd
base via Nakayama): cold 1-WL sees only fused 4-cells (the Z₄ gauge hides even mod 2), but **pinning 2 segments' true
values cascades to resolve ALL segments** — 1-WL **realizes Z₄-forcing directly**, with the *same* forcing number as the
F₂ multipede on the base (2 pins, circulant m=6). **★ SHARPENING (corrects the "layer exposure" framing):** for the
*native* encoding there are no layers to expose — **1-WL forces the full ring at once** (full-value pins propagate;
**parity-only / mod-2 info does NOT propagate**). The F₂-tower is the *solving* decomposition (Smith / iterative-F₂ on
the **extracted** Z₄ system), **not** how the graph forces. So native `Z_{2^k}` = the F₂ multipede *one ring up*: ring
inferred from the segment cell-size (`4 ⟹ Z₄`), same forcing/individualization, solve by Smith-normal-form. **Route (b)
validated for Z₄.** *Honest scope:* this is the natural rigid Z₄-multipede; whether Lichter's *specific* FPC+rank-hard
encoding is equally 1-WL-forcing-extractable is a finer open point (it may encode the ring to resist WL harder).

**"Never flag on rigid" = rigid-GI ∈ P = the seal's `hSmallAutThin` wall.** The adaptive IR-solver is **not a logic**, so
Gurevich's no-logic-for-P does *not* imply it must flag — that bites only *fixed* engines (fixed ring, fixed WL-level),
and its content is "**adapt** the ring," which the engine does. Even the known lower bounds are *linear* constructions
(varying the ring), giving zero evidence for a non-linear obstruction. So the ceiling is exactly "rigid-GI ∈ P", which
equals the project's own open wall **`hSmallAutThin`** (small-Aut ⟹ bounded WL-dim), open with no falsifier. Babai/Luks
are plausibly poly on rigid (the Johnson/Cameron blowup is symmetry-sourced, which rigid avoids) — that *is* this wall.

**Route (b): the F₂ → ring generalization (the named next enlargement of the handled class).** Same skeleton over a
different scalar ring: F₂-rank → **Smith normal form**; `coker(A_G)` over F₂ → coker over the module; forcing = ring-unit-
propagation = 1-WL. The Layer-C extraction and the D-M2/D-M3 solve→canonical-form chain carry over verbatim. The **one
new piece is ring inference** — reading `k`/the abelian ring off the gadget structure iso-invariantly (Lichter's point:
the ring varies per instance, so it can't be hard-coded).

**Unification with the seal's node 4 (route §9.9.18 / remaining-work §3a).** The same move resolves node 4: a *schurian*
rank-3 residue has `Aut(X)=G^(2)` a primitive rank-3 group; **Cameron's trichotomy {affine, almost-simple, grid}** +
"node 4 is non-geometric" excludes almost-simple/grid (the geometric **Cameron** leg, carved) ⟹ **affine survives** ⟹
the affine slice ⟹ **solved** modulo `{G3 + Liebeck + Skresanov + cyclotomic-2-sep + finite exceptions}` (the forms-graph
non-cyclotomic separability = the route-1 Gauss work = the open hole). **"Affine = linear-algebraic" is option-2's
"rigid obstruction = linear" seen from the rank-3 side** — the seal reduces node 4 from the rank-3-scheme side, option-2
reduces the multipede from the high-rank side, and **both leave the identical residue**: the **non-schurian / non-linear**
case, which §9.9.18 argues *cannot be a WL-closure residue* and relocates to this solver's flag floor. The two tracks
meet at exactly the same open wall.

**Next concrete step (revised 2026-07-11): design the ring first, then build.** The Z₄/ring validation was an
*ephemeral* Python probe that no longer exists — only the **F₂** path survives (`Option2ExtractionProbe.cs`) — so
"ring-general from the start" (§11.12) must be re-anchored by a **fresh ring-inference probe** (§11.13 open Qs) before
B1. Then the MVP is **B1–B3**: productionize D1/D2/D4 and wire at `ChainDescent.Search` `target == -1` **as the
stepwise alternating engine above** (run-instead-of-branch, consume verified kernel symmetry + refine + loop, defer
only on mutual stall), with **verify-by-reconstruction** the sound succeed/flag gate. Finer open point carried:
whether Lichter's *specific* hard encoding is 1-WL-forcing-extractable like the natural Z₄-multipede.

### 11.12 Build + prove roadmap — the rigid seal (2026-06-21, user-approved)

> The target is a **built** solver (C#, wired + cross-checked) **and** a **proven** soundness theorem (Lean) — the
> Phase-2 analog of the symmetry seal `reachesRigidOrCameron`. Approved decisions: **include the ring from the start**
> (not F₂-only — the ring is the analogous object; separating risks correctness); **carry the forcing-model bridge
> temporarily** but everything is eventually discharged; **model**-level Lean (not graph); **build first**, Lean as a
> design tool until the main proofs start.

> **▶ AMENDMENT (2026-07-11): design-the-ring-first + engine reframe.** "Ring from the start" stands, but its only
> validation (Z₄) was ephemeral Python that evaporated — so **B1 is gated on a fresh ring-inference design pass +
> probe** (§11.13), not begun cold. B2's wiring target is the **stepwise alternating engine** (STATUS banner +
> §11.11): run-instead-of-branch at `target == -1`, consume verified kernel symmetry + refine + loop, defer only on
> mutual stall. B3 (verify-or-flag) is unchanged and remains the soundness lynchpin. The C# state (2026-07-11): the
> F₂ canonizer *works end-to-end inside* `Option2ExtractionProbe.cs` (D-M3) but **nothing in production calls it**,
> and there is **no Smith normal form** anywhere — so B1 is genuine productionization + ring, not a lift.

**The target theorem — the rigid seal.** `canonizesRigidResidue_or_flags`: for a rigid Phase-2 residue, *handles
linear-over-a-ring, flags non-linear*, open content isolated into one hypothesis. It is the mirror of the symmetry seal:

| | handles | the escape | wall |
|---|---|---|---|
| symmetry seal `reachesRigidOrCameron` | symmetry consumption | "or Cameron" | `hSmallAutThin` |
| **rigid seal** (this) | linear-over-ring (CFI/multipede/`Z_{2^k}`) | "or non-linear" | = `hSmallAutThin` |

By the node-4 unification (§11.11) the two flag floors are the **same object**; §11.14 argues the rigid seal's escape is
*strictly tighter* (no "or Cameron" at all). Combined, the two seals isolate **one** wall.

**BUILD track (C#) — empirical validity.** *(The hook is `ChainDescent.Search` `target == -1`, `ChainDescent.cs:243-257`,
replacing the `target = fallback` exhaustive branch; rigidity is guaranteed there by Phase 1, see §11.11.)*
- **B1 Productionize** — lift D1/D2/D4/D5 from `Option2ExtractionProbe.cs` into an `Option2Solver` class; robust D1
  (general arity via the segment/middle bipartition); **ring-aware from the start** (§11.13); behind a config flag.
- **B2 Wire** at `target == -1`: solver succeeds + verifies → set `_bestMatrix`, return; else fall through to the
  existing exhaustive branch. Compose the labelling with the pinned path.
- **B3 Verify-or-flag (D7)** — reconstruct the graph from `(base, H, c, orientation)`, compare to input; mismatch → fall
  through. Makes the succeed/flag **verdict iso-invariant** (the one soundness-critical piece; the reduced "item 4").
- **B4 Fold (D6)** — use harvested `σ` in `Automorphisms` to quotient onto one copy before solving (doubled/`Aut_base`);
  the iso-invariant `σ`-fold. The one non-mechanical C# piece; off the single-multipede path.
- **B5 Cross-checks** — scramble-invariance, exhaustive size-5/6 unique-canonical counts, Even≠Odd, the multipede
  battery (canonizes + scramble-invariant + agrees with the existing canonizer where it already handles), a speedup
  measurement, flag-set-shrink on a flagging fixture. "Prove it works" empirically.
- **B6 Ring** — already designed in (§11.13); the Smith-normal-form solve + ring inference. *Not separately deferred —
  per the decision, built into B1–B5 as the ring-general path.*

**PROVE track (Lean) — the rigid seal.** *New infrastructure: the rigid residue is a NON-schurian coherent configuration,
so the seal's `AssociationScheme`/`CoherentConfig` machinery does not apply (§11.10 L2).*
- **P1 Extraction-soundness (L1)** — minimal forcing-circuits generate `rowspace(H)`. Pure F₂/matroid over `ZMod 2`, no
  graph; Mathlib-direct. **Do first** (concrete, standalone). *Ring version (row-MODULE, not a matroid) is harder — keep
  P1 F₂-first as the stepping stone, generalize after.*
- **P2 Forcing-model bridge** — "1-WL forcing = unit-propagation on the extracted system" (Layer B). **Carry as a model
  hypothesis** for v1 (like the seal's `orbitalScheme`/`SchurianScheme`); discharge later (a WL-formalization effort).
- **P3 Solve + canonical-form correctness** — over the F₂/ring-system model: the linear/Smith solve yields an
  iso-invariant complete canonical labelling (unique for rigid); `coker`/`coset_min` canonicity. The heavy new build.
- **P4 Rigid-seal capstone** — `canonizesRigidResidue_or_flags`: composes P1+P2+P3 + B3's verify-soundness; axiom-clean;
  isolates the `LinearObstruction` hypothesis = the wall. Plus the **parity lemma**: its `¬LinearObstruction` flag floor =
  the symmetry seal's Cameron-complement (the formal node-4 unification; §11.14 sharpens it to "no Cameron carry").

**Carried vs closed (parity with the symmetry seal).** Closed (proven): extraction soundness (P1), the linear/Smith core
+ canonical-form iso-invariance (P3), verify-or-flag soundness (B3). Carried (hypotheses): the forcing-model bridge (P2,
dischargeable) + `LinearObstruction` (the wall, by design — exactly as the symmetry seal carries "or Cameron"). **No new
citations** (no CFSG; unlike the symmetry seal's G3). **Sequence:** B1→B2→B3 (the MVP working solver) with P1 in parallel;
then B4/B5 + P3/P4. Quality bar unchanged (axiom-clean, no `sorry`/`axiom`/`native_decide`, build green).

### 11.13 The ring design (the value-group / Smith-normal-form generalization)

> Decision (§11.12): the solver is ring-general from the start. Validated for Z₄ (§11.11). The ring is **contained** —
> most F₂ machinery carries unchanged.

**The object.** A rigid Phase-2 residue = an **`A`-linear system `M x = c`**: `A` a finite abelian value-group, `M` the
integer incidence (`0/1` for the multipede), solved over `A` by **Smith normal form**. F₂ is just `A = Z/2`. Rigid ⟺
trivial kernel-module. Decompose `A = ⊕ Z/p^k` (structure theorem); solve per prime-power component.

**Ring-INDEPENDENT (reuse the validated F₂ machinery unchanged):** **D2 extraction** recovers `M`'s support / the gadget
relation — *the same over any `A`* (the Z₄ probe confirmed 1-WL forces the full ring with the same forcing number, so the
coupling is identical). Also: the forcing oracle, base-order-from-WL-cell-ids (D-M2), verify-by-reconstruction (B3).

**The three ring-SPECIFIC pieces:**
- **D1 — ring inference, REORDERED to extract→infer.** **★ KEY FINDING (`/tmp/ring_infer_probe.py`, 2026-06-21):** ring
  inference is **relational, NOT statistical.** Cell-size and forcing histograms are **byte-identical** for `Z/4` and
  `Z/2²` (both: 4-cell segments, `{4:6,16:6}` gadgets, identical single-pin splits). The distinction lives in the
  extracted gadget **connectivity** — the negation relation `{(a,−a)}`, whose 2-torsion differs (`Z/4`: `{0,2}`, size 2;
  `Z/2²`: all 4). Iso-invariant (intrinsic to the relation), extraction-level. So **D1 reads `A` from the extracted
  relation, not from cell statistics** — extract first, then infer.
- **D4 — Smith-normal-form solve over `A`.** Kernel-module (= gauge), unique solution (rigid), canonical coset rep =
  `coker` over `A` (the twist-class, generalizing D-M0/D-M2's `coset_min` to a module coset). Rigidity over `Z/p^k` =
  full `F_p` rank per prime component (Nakayama; the Z₄ probe used exactly this). Mathlib has Smith normal form over PIDs
  (Z, then reduce).
- **D5 — order the `|A|` states.** Each segment's states ordered by the group with the solved value as identity; gadget
  inners by value-tuple. Generalizes the F₂ 2-state orientation.

**Open ring-inference questions (the focused next sub-probe, before D1 is built):** (i) recover the **full** group `A`
(not just 2-torsion) from a **general-degree** gadget relation, canonically; (ii) the **canonical state-ordering** tied to
the inferred `A` (so D5 is iso-invariant); (iii) degenerate cases (relation under-determines `A` → canonical choice or
flag). This is the ring analog of the D-M0 separation test. Probe spec: `/tmp/ring_infer_probe.py` (rebuild from §11.8
style) — `build(biadj, A_add, A_n)` native `A`-multipede; the 2-torsion / negation-relation read is the discriminator.

### 11.13a Ring design — the settled, buildable spec + the fresh probe (2026-07-11)

> Written **before B1** per "design the ring first." Supersedes §11.13's sketch as the *buildable* spec; §11.13's
> findings (inference is **relational**, the negation-relation torsion is the discriminator) stand and are the
> foundation. The F₂ path (`Option2ExtractionProbe.cs`) is the base case `A = Z/2`. Ring inference and
> fusion-resolution are designed as **one object** (the kernel-*module* is the de-fusion primitive — STATUS banner).

**The data model.** A rigid Phase-2 residue is an `A`-linear system **`M x = c`** over a finite abelian group `A`:
- **variables** `x_i ∈ A` — the segments (non-singleton real-decision cells);
- **`M`** — the integer gadget-incidence (`0/1`; each row = the segments a gadget constrains), **ring-independent**;
- **constraint** — each gadget enforces `Σ_{i∈g} x_i = c_g` in `A` (`c=0` homogeneous / `c` = twist constants);
- **`A = ⊕_p ⊕_j Z/p^{k}`** — the per-instance value group, inferred from the graph (piece 1 below).

`F₂` = `A = Z/2`. **Rigid ⟺ `ker_A(M) = 0`.** Canonical form = the unique solution's induced labelling; a **hidden
(fused) symmetry = a nontrivial `ker_A(M)`** — the de-fusion primitive of the stepwise engine.

**Split by ring-dependence** (sharpening §11.13):
- *Ring-INDEPENDENT — reuse F₂ machinery verbatim* (the Z₄ probe showed 1-WL forces the full ring with the **same**
  forcing number ⟹ the coupling `M` is ring-agnostic): **D2** extraction of `M`'s support (minimal forcing-circuits,
  §11.4a); the forcing oracle; base-order-from-WL-cell-ids (D-M2); verify-by-reconstruction (B3).
- *Ring-SPECIFIC — the three new pieces:*
  1. **Ring inference `A` — extract-then-infer, relational.** Cell-size/forcing histograms are *identical* for `Z/4`
     and `Z/2²`; the discriminator is the extracted **negation relation** `N = {(a,−a)}` (from the deg-2 gadget
     `x+y=0`) and higher gadget relations. Canonical fingerprint of `A` = the **order-profile** (`{ord(a):a∈A}`,
     i.e. the solution-count of `m·a=0` per `m|exp A`) — a group invariant that separates *all* abelian groups of a
     given order. Read from the extracted state addition/negation, **not** cell statistics. **Open Q (i): can the
     available gadget relations recover the full order-profile canonically (not just 2-torsion)? — the probe below.**
  2. **Smith-normal-form solve over `A`.** Reduce `M` to Smith form over `Z`, then per prime-power component:
     `ker_A(M)` = the gauge/symmetry module; unique solution when `ker_A(M)=0` (rigidity over `Z/p^k` = full `F_p`
     rank per prime, Nakayama — the Z₄ probe's move). Canonical twist-class = the `coker_A(M)` coset rep (module
     generalization of `coset_min`). Mathlib has Smith over PIDs (`Z`); C# per-prime `F_p`-rank + mod-`p^k` lift.
  3. **Canonical state-ordering (D5), tied to `A`.** Each segment's `|A|` states ordered by the group with the
     *solved value as identity* (coset-canonical, iso-invariant once `A` + solution fixed); inners by value-tuple.
     A *wrong* `A` silently mis-orders ⟹ D5's soundness rides on inference (1) being canonical.

**Fusion integration.** The per-relation query over `A` is "forced (in the row-*module*) or free (a `ker_A`
direction)?" A `ker_A(M)≠0` direction is a hidden *abelian* symmetry over `A` — verify as automorphism, consume,
refine, loop (de-fusion). So **designing `A` designs the de-fusion**; non-abelian fusion is not a kernel-module and
stays the cascade's job (§11.14).

**Degenerate / flag (§11.13 open (iii)).** If the extracted relations *under-determine* `A`, inference must make a
**canonical choice or flag** — never guess (a wrong `A` corrupts the ordering). Verify-by-reconstruction (B3) catches
a wrong `A` (reconstruction mismatch → fall through to the exhaustive branch), so under-determined `A` is **sound**
(it flags); the only open question is coverage (how often), a probe measurement.

**The fresh ring-inference probe** (`RingInferenceProbe.cs`, in-repo — replaces the evaporated
`/tmp/ring_infer_probe.py`; algebraic level, since the Z₄ probe already tied graph-forcing to this algebra). Over
`A ∈ {Z/2, Z/4, Z/2², Z/8, Z/2×Z/4, Z/2³, Z/6, Z/9, Z/3², Z/2×Z/8, Z/4×Z/4}`: compute the **order-profile
fingerprint** and the **2-torsion count**, and check (a) the order-profile **separates every same-order pair of
distinct type**; (b) the classic `Z/4 ≠ Z/2²` separates by 2-torsion (2 vs 4); (c) **2-torsion is INSUFFICIENT in
general** — `Z/2×Z/8` and `Z/4×Z/4` share order (16) *and* 2-torsion (4) yet differ in type, separated only by the
full order-profile. **Design consequence (analytically confirmed, codified by the probe): canonical ring inference
must read the full order-profile ⟹ D1 must extract *higher-degree* gadget relations, not just the deg-2 negation
relation.** This is the concrete input to B1's ring-aware D1.

**Which gadget degree? — the observation-budget = exponent result (probe test 2, 2026-07-11).** A degree-`d` gadget
`Σ_{i=1}^d x_i = 0` can *observe* the multiple `(d−1)·a` (force `d−1` of its slots to a common value via shared base
incidence, read the last) — so **gadget degree `d` ⟺ observation budget `B = d−1`**, at which D1 knows the
annihilator counts `c_m = |{a : m·a = 0}|` for `m ≤ B`. The probe measures the minimum budget that pins `A`:
- Some same-order pairs split **early** — `Z/8` vs `Z/2×Z/4` differ already at `c_2` (2-torsion), budget 2 ≪ exp 8.
- But **worst-case pairs agree on every `c_m` below the exponent and split only *at* it**: `Z/2×Z/8` vs `Z/4×Z/4`
  (agree `c_1..c_3`, split at `c_4 = exp`); `Z/9` vs `Z/3²` (odd — *no* 2-torsion signal at all, split at `c_3 = exp`).
- ⟹ **the worst-case observation budget to canonically pin `A` is its exponent `exp(A)`, i.e. gadget degree
  `≈ exp(A)+1`.**

**Design consequence — `exp(A)` is a COST, not a flag floor (corrected 2026-07-11, after the "can `exp(A)` exceed
`n`?" analysis).** Budget `exp(A)` can be reached two ways, and the graph provides whichever its construction uses:
(a) a **single degree-`exp(A)` gadget** (the *native* encoding); (b) a **composition path of depth `≈ log₂ exp(A)`
through bounded-degree gadgets** (the F₂/ring **tower** — observe `2a`, feed it forward to read `4a`, …). **Both are
polynomial:**
- A **native** ring has **`exp(A) ≤ |A| ≤ n`** — a value of order `e` occupies `e` distinct fiber states = `e`
  vertices, so *the exponent cannot exceed the vertex count* (the user's intuition, confirmed). Degree `≤ n`, poly.
  Unbounded *across the family* (Lichter `Z/2^k`, `exp = 2^k`) but every instance has `exp ≤ n`, and large `exp`
  forces a *small base / fiber-heavy* graph (`exp ≤ |A| ≤ n / #base-edges`).
- A **tower** ("compressed" `Z/2^k` as a `k`-bit register, `~2k` vertices) can have `|A| = 2^k > n`, but then the
  graph's *gauge* is elementary-abelian `(Z/2)^k` (exponent 2) — the large exponent lives only in the **solver's
  arithmetic** (Smith over `Z`), and the iterative engine peels it in `depth ≤ n` rounds (§11.11 — "`Z_{2^k}` is
  *inside* the engine, not the floor").

So **ring inference is poly for *any* linear-over-a-ring residue**; `exp(A)` only decides whether the cost appears as
*arity* (native) or *depth* (tower). The `Z/2^k` / ring-*varying* case is a floor only against a **fixed-ring** solver
(Lichter's FPC+rank, which *cannot individualize*); the ring-**general** adaptive solver here handles it, so its
genuine flag floor is the **non-linear** residue (§11.11 pt 3 — open, *no constructible witness*), **NOT** the ring
exponent. (The probe's "budget = exponent" is the correct *single-gadget* cost; the tower is what keeps it poly.)
**Graph-level bridge — CONFIRMED on the forcing mechanism (2026-07-11, `RingMultipedeProbe.cs`, 2 tests green).**
The mechanism is now explicit, not assumed: in a degree-`k` gadget `Σ x_i = 0`, pinning `j` peers to a common value
`v` and the rest to `0` **forces** the last `= −(j·v)` (pure sum-zero propagation, recognition-free) — so forcing
exposes the multiples `{(0..k-1)·v}` and recovers `c_m` for `m ≤ k−1`. Verified: `Z4` recovered `c_1..c_4 = 1,2,1,4`
by forcing alone; `Z/2×Z/8` vs `Z/4×Z/4` split under forcing exactly at degree 5 = `exp+1` (indistinguishable at 4);
`Z/9` vs `Z/3²` at degree 4 = `exp+1`. The **native-`A`-multipede graph generator** is also built + well-formed
(segment-state + gadget-tuple vertices, every tuple sums to 0 in `A`) — the substrate B1's D1 runs on; `F₂` is the
`MultipedeGenerator` case.

**The D-M1 twin — WL-driven extraction, staged (`RingWlExtractionProbe.cs`, RM-1 + RM-2 DONE, 8 tests green,
2026-07-11).** Drives the *real* `WarmPartition` (1-WL) on the scrambled native-`A`-multipede, generalizing
`Option2ExtractionProbe` from F₂ (2-state segments, size-2 cells) to `A` (`|A|`-state segments, size-`|A|` cells):
- **RM-1 (segment recognition + cold fusion):** the `|A|` states of each segment **cold-fuse into one size-`|A|`
  cell** under the genuine refinement (the ring twin of the "cold 1-WL sees fused `|A|`-cells" finding), recovered
  recognition-free as the size-`|A|` cells among segment-coloured vertices, count `= nW`, scramble-invariant
  (`Z2, Z4, Z2², Z3`). Non-vacuous — had WL discretized, the count would be 0.
- **RM-2 (forcing == A-unit-propagation, Layer B over `A`):** pinning a base `S` (individualize one state per
  pinned segment) discretizes the graph's segments **iff** unit-propagation resolves every segment from `S`
  (base `{0,1}` resolves all on the deg-3 circulant; `{0}` resolves only itself), scramble-invariant. Confirms
  resolution is **ring-independent at the support level** (the ring-design split: extraction/support ⊥ ring).
- **★ Finding that shapes D1 (from RM-2):** for `|A| > 2` a *forced* segment shows up as a **broken `|A|`-cell** —
  1-WL singles out the *value* state but leaves the `|A|−1` non-value states symmetric (fused), so "resolved" is
  "the fused cell split", NOT "all states singleton" (which only coincides at F₂). D1 reads the value = *which*
  state singletons out; the residual `(|A|−1)`-cell is expected, not a failure.
- **RM-3 (ring inference recognition-free) — DONE (3 tests).** The ring `A` is recovered from **one degree-3
  gadget's full sum-zero relation** on the real scrambled graph: `Z4`→`1²·4²` (profile `1^1,2^1,4^2`), `Z2²`→
  `1^1,2^3`, `Z2×Z4`→its profile — **exact order-profile, scramble-invariant**, distinguishing `Z4` from `Z2²`.
  **★ Design refinement (stronger than the forcing budget=exp bound):** a degree-3 gadget's tuple-relation is a
  group Latin square, so by **Albert's theorem** (isotopic groups are isomorphic) it determines `A` up to iso, and
  the **order-profile falls out of the row-permutation cycle structure** — `R_x ∘ R_{x'}⁻¹` = translation by
  `(x'−x)`, cycle length `= ord(x'−x)`, an isotopy invariant (hence recognition-free + scramble-invariant by
  construction). So **D1 should infer `A` by reading one gadget's full relation, NOT by forcing-observation**:
  degree 3 suffices for *any* `A` (with `exp ≤ n`), poly (`|A|² ≤ n²` tuples). The budget=`exp` bound (RM /
  `RingInferenceProbe`) governs only the weaker *pin-a-peer* observation; the full-relation read beats it — further
  confirming `exp(A)` is a non-obstruction.
- **Next: RM-4 (kernel-module / rigidity from forcing = the `dim ker` twin).** With segments (RM-1), support/forcing
  (RM-2), and ring `A` (RM-3) recovered on the real graph, RM-4 recovers the kernel-module (rigidity / the hidden-
  symmetry de-fusion detector), completing the D1→D4 chain and handing off to B1 (productionize as `Option2Solver`).

### 11.14 The rigid medium negates the hidden-Johnson/Cameron construction (2026-06-21 lead)

> A theoretical lead (user's insight): does the rigid setting *exclude* a hidden Johnson/Cameron, tightening the rigid
> seal's flag floor below the symmetry seal's? Strongly supported, **conjecture-level** (the crux is unproven).

**The crux: the hiding mechanism is abelian; the Johnson is not.**
- A *hidden* symmetry (one that masquerades as a real decision) is, in every known construction, a **CFI-style gauge**:
  the cycle space `Z₂^β` / `Z_{2^k}^β`, an **abelian, linear** group acting by sign/value flips. The hiding *is* the
  linearity — a module's action looks like independent decisions.
- The Johnson/Cameron obstruction is a **giant alternating** symmetry — **non-abelian**. There is **no known non-abelian
  CFI**: you cannot encode `S_m` as a linear gauge (`S_m` is not a module). So "hidden Johnson" is near-contradictory.

**Which collapses both escapes in the rigid medium:** *hidden* symmetry ⟹ abelian ⟹ the linear oracle's job ⟹ consumed
in Phase 1; *non-abelian* symmetry ⟹ not hideable ⟹ visible (large Aut) ⟹ excluded from a rigid residue by definition.
A rigid Phase-2 residue is free of both — real decisions are terminal, any symmetry is a contradiction.

**The 2×2 synthesis** (the clean picture):

| | abelian / linear | non-abelian / non-linear |
|---|---|---|
| **symmetry** | hidden gauge → Phase-1 *linear oracle* | Johnson/Cameron → Phase-1 *cascade*, or **excluded by rigidity** |
| **structure (rigid)** | multipede / `Z_{2^k}` → **Phase-2 IR-solver ✓ (built)** | **the wall** — §9.9.18 non-schurian, open, **no witness** |

The rigid medium kills the entire **symmetry row**; the IR-solver owns **structure/linear**; the only remainder is
**structure/non-linear**, which §9.9.18 argues *cannot be a WL-closure residue*. This is the deferral-architecture route
to §9.9.18's conclusion and it **explains the 0-falsifier record** (every would-be witness is a symmetry construction).

**Payoff for the seal:** if "rigid ⟹ no hidden Johnson/Cameron" is proven, the **rigid seal carries a strictly tighter
flag floor — no "or Cameron" at all, only "or non-linear."** The symmetry seal needs the Cameron escape (Phase 1 may
starve); the rigid seal sits *after* Phase 1 and provably can't face Cameron.

**The attack (to formalize):** (i) hidden symmetry ⟹ abelian (the gauge is the cycle space); (ii) abelian hidden symmetry
⟹ consumed by the linear oracle; (iii) non-abelian symmetry ⟹ not hideable ⟹ visible ⟹ killed by rigidity. **(i) is the
load-bearing conjecture** ("no non-abelian CFI") — empirically solid, not a theorem. **What it does NOT touch:** the
structure/non-linear cell (still open, still no witness) — the insight removes the symmetry half of the wall only.
**Empirical test (not yet run):** try to hide a non-abelian symmetry as decisions, or rigidify a Johnson base (predict:
the non-abelian symmetry leaks back as residual gauge ⟹ not rigid).

**★ Refined into a standalone target (2026-06-21): [`chain-descent-cameron-entanglement.md`](./chain-descent-cameron-entanglement.md).**
The dual-attack pass sharpened this: the load-bearing duality is *"symmetry separable from structure"* — **abelian
symmetry is separable** (CFI ⟺ multipede; the IR-solver is the rigid dual), **non-abelian is conjecturally integral**
(no rigid-Cameron). The iff "rigid-Cameron exists ⟺ real Cameron exists" is **false** (it would rigidify a non-abelian
symmetry); its failure *separates* the two walls cleanly rather than collapsing them (Cameron = `b(Aut)`, classified;
the wall = structural gap, no witness). The provable target = **"no rigid-Cameron / non-abelian symmetry is
non-separable"** — closes the rigid seal's "or Cameron" and explains why the symmetry seal keeps it. The new doc has the
classification-battery decomposition, the attack menu (Route A geometric-rigidity = best first target, Johnson by hand;
Route B the unifying conjecture), and the step list.

### 11.15 The recovery ↔ co-recovery duality — the first-design "rigid equivalent," now recorded (2026-07-03)

> **What this is.** The symmetry-based **recovery/harvest** method (Cascade / Part A `StabilizerAt` /
> `coversOrbits_of_realizers`; the poly instance for the forms residue is **Route C**) was, at first design, proposed
> *with a rigid mirror* — a dual method for the rigid residue — which was **never written down** because attention went to
> the symmetric version. **Option 2 (§11.0–§11.10) is that mirror, built in 2026-06-20 without recording that it was the
> long-proposed dual.** This subsection records the duality as a first-class principle so the two legs stop looking like
> unrelated efforts. It is a *framing*, not new math; every claim below points at a landed object.

**The one meta-algorithm.** Both legs are the *same* move: **recover the residual algebraic structure from the descent's
cross-branch observations, then finish with EXACT algebra instead of iterating WL.** They differ only in *which* structure
is recovered and *which* exact algebra finishes it. The calculator saw this at design time — it explicitly weighed an
**orbit language vs. a constraint language** (`chain-descent-calculator.md` §2: "none is an orbit language — that mismatch
is why the boolean approach failed structurally"), chose orbits for the symmetric case, and named **XOR/Gaussian the
abelian corner** (§2–§3: "the linear oracle is that abelian corner, done properly"). The rigid corner was split off at the
conservation finding `lockstep_disc_imp_stab_trivial` (the within-cell discretizing oracle *cannot* harvest a moved orbit)
— but only ever recorded as "the linear/discretizing oracle," never as the general **co-recovery** dual of recovery.

**The dual dictionary** (each row: symmetric recovery ↔ rigid co-recovery):

| | **Recovery** (symmetric residue) | **Co-recovery** (rigid residue) |
|---|---|---|
| residual object | automorphism **group** `Aut_S` (stabilizer chain) | forcing / **constraint module** `H` (the rigidity system) |
| generator harvested cross-branch | path-fixing **realizer** (a permutation) | minimal **forcing circuit** (a relation / row of `H`) |
| harvest engine (Lean) | `coversOrbits_of_realizers` / Part A `StabilizerAt` | option-2 **Layer C** extraction → `rowspace(H)` (§11.4a) |
| "free bits" = branching | **orbits** (branch 1/orbit; `bᵢ`=#orbits) | **`ker(H)`** (branch on kernel basis; rigid ⟹ `ker=0` ⟹ single path) |
| exact-algebra finish | **Schreier–Sims** (base+transversals; `|Aut|=∏` orbit sizes) | **Gaussian** (unique solution mod `ker`) |
| WL's approximation, and its defect | cells **⊇** orbits (over-**merge** is the gap) | unit-prop closure `cl_up` **⊆** `cl_lin` (under-**forcing** is the gap) |
| the shared abelian corner | `Aut = Z₂ᵐ` gauge = the **linear oracle** | `H` over F₂ = Gaussian/Z₂ — **CFI ⟺ multipede** meet here |
| flag floor (structure possibly too rich for the fixed solver) | **non-abelian Cameron** (≡ GI∈P; the "or Cameron" leg) | **ring-varying** F₂→`Z_{2^k}` (Lichter, FPC+rank≠P; §11.6) |

The two are dual under the **group ↔ constraint / orbit ↔ forcing** correspondence, and the abelian corner (Z₂ gauge) is
exactly where they coincide — which is *why* XOR "almost worked" on CFI and nothing else (calculator §3): CFI's gauge is a
constraint module *and* an abelian group, so recovery and co-recovery are the same computation there. Off that corner they
split: recovery needs a *group* (Schreier–Sims), co-recovery a *module* (Gaussian/Smith).

**The two realized instances are the two mirror poly routes we are now weighing.**
- **Route C** (recovery-route §7; this residue = the forms graph): recover `Q` (the structure), whence `Aut = GO(Q)` is a
  *known* group ⟹ Schreier–Sims. Symmetric leg. *(De-risked 2026-07-03: `route_c_reconstruct_probe.py` — the isotropic
  cone determines `Q` up to scalar by one linear solve, `vanishDim=1` for ε=±, d=4,6,8, q≤11; no small-`q` exception.)*
- **Option 2** (§11): recover `H` (the structure), whence the "co-group" `ker(H)` ⟹ Gaussian. Rigid leg.
- **Same object, both legs:** Route C's *cone-reconstruction* and option-2's *Layer-C forcing-circuit extraction* are the
  **same kind of step** — recover the defining algebraic substrate from the graph/descent, recognition-free. The ring
  design (§11.13, Smith normal form over `Z_{2^k}`) is a third point on the *co-recovery* axis (which exact algebra
  canonicalizes the recovered module); the flag floor is where no *fixed* exact algebra suffices.

**Why record now (forward value, actionable):**
1. **A unified harvest substrate is available.** `StabilizerAt`/Part A (group harvest) and option-2 Layer C (constraint
   harvest) are the *same* cross-branch generator-collection with different generator types (permutation vs. relation) and
   different soundness proofs (verified automorphism vs. verified forcing circuit). A shared `ResidualStructure` abstraction
   — a group in the symmetric case, a module in the rigid case — would let both seal legs reuse one harvest + soundness
   core, instead of the current parallel builds. This is the concrete engineering payoff of the duality.
2. **It makes §11.14's 2×2 a corollary, not a coincidence.** The "symmetry row killed by rigidity, structure/linear owned
   by the IR-solver, structure/non-linear = the wall" picture *is* this dictionary's flag-floor row read across the
   abelian/non-abelian split. The dual flag floors (Cameron ↔ ring-varying) are the *same* phenomenon — "the recovered
   structure's algebra outruns the fixed exact-solver" — on the two sides.
3. **It tells us Route C's risk is bounded the same way option 2's is.** Option 2's honest floor is *ring-varying /
   unbounded-arity / non-WL-easy base* (§11.6); Route C's mirror floor is *the recovered group being non-classical* — which
   the Skresanov reduction already excludes for the schurian residue. So the duality predicts (and the §2c/§11.6 records
   confirm) that both realized legs sit *strictly inside* their respective flag floors on the carved residues.

**Provenance note.** This is the user's recollection (2026-07-03) that a rigid equivalent of recovery was proposed at first
design and not recorded; the textual corroboration is calculator §2–§3 (orbit-vs-constraint language, the abelian corner)
+ the `lockstep_disc_imp_stab_trivial` split. Option 2 independently rebuilt the rigid leg; this subsection reconciles them.
