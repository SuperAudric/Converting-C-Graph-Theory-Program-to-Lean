# Flip-validation calculator — superseded (design detail behind chain-descent-overview.md)

A supplement to [`chain-descent-strategy.md`](./chain-descent-strategy.md)
covering the polynomial-bound piece of the algorithm — the "calculator" that
decides the lex-min canonical without exponential re-evaluation. The
calculator is the unproven-polynomial component the whole algorithm's bound
rests on.

> **Superseded as the design of record (chain-descent rewrite).** The current
> authoritative design is [`chain-descent-overview.md`](./chain-descent-overview.md);
> the implementation is the chain-descent harness (`ChainDescent.cs`,
> `CascadeOracle.cs`, `CanonGraphOrdererChainDescent.cs`, …). This doc is
> retained as the **design detail** the overview summarizes — the T-A/T-B/T-C
> decomposition, the stabilizer-chain model, the hardness map and tiers, which
> all carry over — plus the **path**: see "A cautionary detour" for the
> nauty-IR wrong turn and "History" for the boolean-class era.

---

## What the calculator is, and what it isn't

The calculator is not a general-purpose canonization algorithm. Its scope:
given the *structured output of the forward pass* (the individualization
sequence and the refined cell structure at each step), decide which labelling
produces the lex-smallest canonical adjacency matrix, without exploring the
exponential individualization tree.

The honest framing, unchanged: **the calculator's polynomial bound is
equivalent in strength to GI ∈ P.** Computing a generating set of `Aut(G)`,
deciding GI, and computing a canonical form are all polynomial-time
equivalent; a polynomial calculator for arbitrary graphs would resolve a
famous open problem. The project's bet is that the *specific structured
input* the forward pass produces may admit a polynomial procedure where
free-form canonization does not. That bet is unproven and this doc is
careful to mark exactly where it is load-bearing.

---

## The current model: the calculator is a stabilizer chain

The single most important result of the 2026-05-21 session.

**The canonical form is an orbit-minimum.** It is `min` over the `S_n`-orbit
of the graph. Orbit-minima need the orbit's *generating structure* — a group.
Every boolean class the project tried (AND-of-XOR, Horn, monotone) is a
*constraint* language: it describes sets of satisfying assignments. None is
an *orbit* language. That mismatch — not a wrong variable basis, not a
fixable detail — is why the boolean approach failed structurally (see
History).

So the calculator's object is **the residual symmetry, represented as a
permutation group** — concretely a *stabilizer chain* (a base of individualised
points, plus a transversal of coset representatives at each level). The
calculator's operation is **lex-leader descent**: walk the chain, and at each
level pick the transversal element that yields the lex-min canonical prefix,
then descend.

Consequences that fall straight out of this model:

- **True symmetries are transversal elements / generators.** When the forward
  pass finds that flipping or rotating a guess lands in an `Aut`-equivalent
  world, that is an element of the residual group. Base + transversals
  generate `Aut(G)` (standard). The forward pass's true-symmetry detections
  are not noise to discard — they are the generating set.
- **False symmetries are the genuine decisions** — the points where
  lex-leader must actually compare canonicals.
- **§6.5 pair rotation returns, re-housed.** It was stripped in the boolean
  era because "enumerate alternatives + pick the min" is a mux/selection and
  broke AND-of-XOR closure. In the group model that operation *is* lex-leader
  descent over a transversal — the calculator's core step, not a hack. §6.5
  comes back not as boolean rotation variables but as **the per-level
  transversal**. The §3.5 cell snapshot (stripped alongside it) comes back as
  the per-level orbit source.
- **XOR was the abelian special case.** Gaussian elimination over `Z₂` is
  exactly Schreier–Sims specialised to elementary-abelian groups. CFI's
  gadget group *is* `Z₂ᵐ`. That is why XOR "almost worked" on CFI and nothing
  else: the project had found the abelian corner of the group model. The
  generalisation from `Z₂`-linear to general permutation groups is the move
  from Gaussian elimination to computational group theory.

---

## The hardness map: tiers and the single hurdle

### Two axes

Canonization hardness has two independent axes:

1. **Cascade** — after individualising a vertex and running refinement, does
   refinement reach *single-orbit* cells? Equivalently: does local
   individualization propagate globally?
2. **Composition factors** of the residual group.

### Three cases

- **Cascade → polynomial, regardless of the group.** Refinement reaches
  single-orbit cells, so every guess is a true symmetry, the chain's
  transversals shrink, and lex-leader descent is a *sum* of polynomial-size
  transversals (not a product). Cycles, C4+K2, **and all Johnson graphs**
  live here.
- **No cascade + abelian factors** (CFI: `Z₂ᵐ`) **→ polynomial** via linear
  algebra (Gaussian elimination over `Z₂`).
- **No cascade + an `Aₖ`-on-subsets factor → the genuine wall.**
  Quasipolynomial (Babai, `2^O(log³n)`); polynomial is open (≡ GI ∈ P).

### Tiers

- **Tier 0 — disjoint / decomposable.** `Aut(G₁ ⊔ … ⊔ G_c) = (∏ Aut(Gᵢ)) ⋊ S_c`.
  Components are independent; the stabilizer chain factors; cost is linear in
  the number of components. The old code's *superpolynomial* blowup on
  disjoint CFI was an artefact — it ran the forward pass over the whole union
  as one cell and made cross-component guesses, manufacturing coupling that
  isn't there. The fix is component decomposition.
- **Tier 1 — 1-WL deficiency, cascade resolves.** 1-WL is blind initially
  (vertex-transitive / strongly regular), but individualization + refinement
  cascades. C4+K2 #56, CFI(Cycle3), Johnson graphs, triangular graphs.
- **Tier 2 — the wall.** No cascade and a non-abelian-simple factor. Not
  exercised by any instance currently in the test bed (see "Construction
  question").

### The single hurdle

Everything reduces to one operation:

> Given a node in the individualization tree (a partial individualization),
> determine **in polynomial time which child leads to the lexicographically
> smallest canonical — without recursively canonizing each child.**

If this is polynomial, you descend one root-to-leaf path (≤ `n` levels, ≤ `n`
children each, polynomial evaluation) → polynomial → GI ∈ P. Storage of the
group is free (see T-A/T-B). Discovering generators, the size of the IR
tree, local-vs-global generators — all either dissolve or reduce to this one
operation. It is the same thing earlier drafts called "canonical-prefix
feasibility" (old "Reason 2").

Inside the bottom-up stabilizer-chain construction, the hurdle has a precise
home: **discover each level's transversal** — the orbit of the level's base
point, i.e. the new coset representatives. This is polynomial when refinement
exposes the orbit (cascade / Tier 1) or the coupling is linear (CFI); it is
the wall otherwise.

---

## The construction question: is the wall reachable?

Tier 2 is the only thing standing between the project and a polynomial bound.
A natural strategy: instead of solving it, prove it never arises from the
forward pass's output. Progress this session:

- **CFI applied to a Johnson base**, and **a Johnson graph with each vertex
  replaced by a CFI graph**, both produce
  `(Z₂ᵐ, refinement-resistant) ⋊ (S_n, cascading)` — a *decomposable*
  semidirect product. You resolve the cascading `S_n` layer first (it does
  not depend on the parity), and the `Z₂ᵐ` layer is then a plain linear
  system. Two polynomial tools, one per factor. **Neither is Tier 2.**
- **Near-theorem:** if `Aut(G)` *is* a Johnson group, then `G`'s edge set is
  `S_k`-invariant, hence a union of Johnson-association-scheme classes, hence
  `G` is a scheme graph — and refinement computes the scheme, so
  individualization cascades. **You cannot hide a Johnson group as the full
  automorphism group of a graph.**
- **CFI is a `Z₂`-hiding gadget.** No `Aₖ`-hiding gadget is known. Hiding a
  non-abelian simple group requires *fusing* refinement-resistance with
  non-abelianness in one non-decomposable obstruction; layered products
  decompose. This asymmetry is real, and it is part of why GI stayed open and
  why Babai works in the abstract String-Isomorphism setting rather than with
  a clean graph family.
- **Detection is not free.** "The forward pass detects every automorphism, so
  nothing can be hidden" assumes its conclusion: detecting all of `Aut(G)` in
  polynomial time *is* GI ∈ P. The forward pass detects automorphisms cheaply
  only when refinement *verifies* them. A hidden Johnson is exactly the case
  where verification is GI-hard. (Verifying a complete, given permutation is
  an automorphism is trivial, `O(n²)`; verifying that a *partial choice*
  leads to an equivalent canonical is the recursion.)
- **Higher-WL lever.** The forward pass uses 1-WL. A `k`-WL forward pass makes
  Johnson-*scheme* cells cascade (Johnson schemes have bounded WL-dimension),
  widening Tier 1. It does **not** cross the true wall, which has unbounded
  WL-dimension.

**Bottom line:** no clean hidden-Johnson graph construction is known — weak
positive evidence that Tier 2 may not arise from the forward pass. But "no
known construction" ≠ "impossible," and Babai needs the quasipolynomial
branch, so it arises *somewhere*. The proof target is: show every obstruction
the forward pass produces decomposes as `(resistant-abelian) ⋊ (cascading)`.
A counterexample would be the first clean hidden-Johnson graph.

---

## Theorems the polynomial bound requires

Three structural theorems — **T-A, T-B, T-C** — are what the calculator's
polynomial bound rests on. They predate the group reframe (they were first
phrased for the boolean calculator); the reframe keeps all three but changes
which are hard.

**Why three, and how they compose.** The calculator does lex-leader descent
down the stabilizer chain. Its cost is, schematically:

```
   total  =  (number of chain levels)
           × (transversal size at each level)
           × (work to discover that level's transversal and lex-select it)
```

For the total to be polynomial, **each of the three factors must be
polynomial** — and each theorem pins exactly one factor:

- **T-A** bounds the *representation* — each level's transversal, and the
  chain as a whole, are polynomial-size.
- **T-B** bounds the *number of levels*.
- **T-C** bounds the *work per level*.

Drop any one and the bound collapses: without T-A the representation is
exponential to even write down; without T-B the descent has
super-polynomially many levels; without T-C each level costs
super-polynomially to walk. All three are required. The reframe's payoff is
that **T-A and T-B become free**, isolating the entire difficulty in T-C.

### T-A — polynomial-size representation (free)

> Each chain level's transversal, and the stabilizer chain as a whole, are
> polynomial-size.

A theorem of computational group theory (Sims): every subgroup of `S_n` —
**whatever its order, up to `n!`** — has a base of `≤ n` points and a strong
generating set of `O(n²)` elements. You never store group *elements*; you
store *generators*. `S_s` acting on `s` points is 2 generators, not `s!`
stored objects. In the boolean era T-A was an open conjecture ("bounded
support per `P` entry"); the group reframe turns it into a citation.

### T-B — polynomially many levels (free)

> The stabilizer chain has polynomially many levels.

A base of a subgroup of `S_n` has `≤ n` points, so the chain has `≤ n`
levels; the genuine decisions (false symmetries) are a subset of those. Also
a citation, not a conjecture.

### T-C — polynomial work per level (the single hurdle)

> Each level's transversal can be *discovered* and *lex-leader-selected* in
> polynomial time.

This is the load-bearing claim, and it is exactly the single hurdle from
"The hardness map." It is polynomial on the easy side (cascade / abelian /
bounded-width) and the open problem otherwise. The asymmetry that pins the
difficulty: **Schreier–Sims builds the whole chain in polynomial time *given
a generating set*** — so the chain *machinery* is not the problem. T-C is
entirely the *missing input*: discovering each level's transversal — the new
coset representatives — when refinement does not expose it for free.

### Note: T-A/T-B/T-C vs. the strategy doc's §6 invariants

T-A/T-B/T-C are calculator-specific and defined only in this doc. They are
distinct from [`chain-descent-strategy.md`](./chain-descent-strategy.md)'s
§6.1–6.5 invariants, which concern the algorithm's *correctness* and its
forward/backward passes. Of those, §6.1 (iso-invariant cell ids — the chain's
reference frame) and the §6.5 *invariant* (every canonical form reachable —
i.e. the per-level transversal must cover the orbit) remain load-bearing for
the calculator's correctness; §6.2/§6.3 were tied to the now-superseded
boolean backward pass.

---

## Implementation

The calculator is implemented as the **chain-descent harness**. The
authoritative end-to-end description is
[`chain-descent-overview.md`](./chain-descent-overview.md) §4–§7; this doc is
the design detail behind it. The code:

- **`ChainDescent.cs`** — the harness: a recursive descent of the
  individualization-refinement tree carrying a polynomial node **budget**. A
  run that exceeds the budget **flags** (`CanonizationFlaggedException`)
  instead of continuing — an honest "not handled", never a wrong answer.
  Automorphisms are harvested from coinciding leaves into a `PermutationGroup`
  — the stabilizer chain of "The current model", here load-bearing: the oracle
  and the pruning both consume it.
- **`ITransversalOracle` / `CascadeOracle.cs`** — the **T-C seam**. At a branch
  node the oracle says which target-cell vertices to descend into. The Phase-1
  `CascadeOracle` certifies nothing a priori, so the harness behaves as a
  budget-bounded IR search; the deferred linear oracle (overview §7) is the
  second implementation that supplies a-priori transversals — the step that
  turns the bounded search into the lex-leader descent of "The current model".
- **`CanonGraphOrdererChainDescent.cs`** — Tier-0 component decomposition plus
  dispatch to the harness.
- **`PermutationGroup.cs`** — `Perm` algebra + Schreier–Sims chain; the
  concrete stabilizer chain. Verified on S₃–S₇, D₄, D18 = Aut(C18), and
  D9≀Z2 = Aut(C9⊔C9).

**Status.** The implementation is **correct** (scramble-invariant + complete)
and **budget-bounded** (polynomial-or-flag — it can no longer run
exponentially). It is **not proven polynomial**: that is T-C. The open
follow-ons:

- the **linear oracle** (overview §7) — a-priori transversal certification for
  the no-cascade-abelian (CFI) case;
- the **Tier-1 polynomial proof** — T-C for the cascade class, which would pin
  the budget `B(n)`;
- the **Johnson / poly-split detector** — flag a run as Tier-2 once a proven
  `B(n)` exists.

This shape was reached via a wrong turn — an earlier unbounded IR-search
calculator — kept below as a cautionary example.

---

## A cautionary detour: the nauty-IR calculator

The path to the current implementation ran through a wrong turn worth keeping
on the record — the failure mode is subtle and easy to repeat.

**What it was.** An earlier calculator — the `GroupCalculator` class, since
deleted — was a top-down recursive **IR search**: branch over a target cell's
vertices, recurse, prune a branch when a harvested automorphism showed it
redundant, take the lex-min leaf. It was **correct** — scramble-invariant and
complete — and it passed the whole test corpus. That is exactly what made it
dangerous: a correct canonizer *looks* like progress toward a polynomial one.

**Why it was a departure.** Correct, but not the intended algorithm, in three
load-bearing ways:

- **Unbounded.** It explored the IR tree to exhaustion. An IR search is
  nauty-shaped, and nauty is exponential worst-case (provably — Neuen &
  Schweitzer); on a hard input the `GroupCalculator` simply ran exponentially.
  A polynomial canonizer must be *polynomial-or-honest-flag*, never silently
  exponential. The IR-search shape had quietly substituted exhaustive
  exploration for T-C — the very hurdle the calculator exists to face.
- **Decorative chain.** It built a `PermutationGroup`, but the search did not
  route through it as a stabilizer chain — the chain was a byproduct, not the
  spine. "The calculator *is* a stabilizer chain" was the model; the control
  flow did not honour it.
- **No seam.** There was nowhere to plug in a-priori transversal certification
  — so no route from the exhaustive search to genuine lex-leader descent.

**How the chain-descent conversion corrected it.** The rewrite kept the
top-down recursion (not a departure — see below) and fixed the three faults: a
polynomial node **budget** makes every run polynomial-or-flag (it can no longer
run exponentially — it flags instead); the `PermutationGroup` chain is
**load-bearing** (the oracle and the pruning consume it); and the
**`ITransversalOracle` seam** is where a-priori certification plugs in — the
deferred linear oracle (overview §7) is what turns the bounded search into the
lex-leader descent of "The current model".

**What was *not* a departure.** Two shipped choices looked like deviations but
were forced-correct, and the chain-descent harness keeps them:

- *Top-down recursion, not literal bottom-up Schreier–Sims construction.* A
  literal bottom-up construction needs each level's transversal *already
  discovered* to take its inductive step (a subgroup does not determine its
  supergroup) — and transversal discovery *is* T-C. Top-down recursion that
  discovers transversals by exploring is what is buildable. Schreier–Sims
  stays inside `PermutationGroup`, organizing discovered automorphisms — the
  analysis lens, not the control flow.
- *Branching over a target cell's vertices, not a single pair.* An early
  attempt branched on one within-cell pair chosen by vertex index; the tree
  shape then depended on the input labelling and **failed scramble-invariance**
  (C4: an edge-first guess discretizes in one step → 2 leaves; a diagonal-first
  guess leaves a 2-cell → 4 leaves). Branching over the whole, iso-invariant
  target cell is the standard correct IR shape, forced by iso-invariance — a
  correctness fact, not a wrong turn.

**The lesson.** "Correct" and "polynomial" are different properties, and an IR
search delivers the first while silently failing the second. The budget is
what makes the gap *visible* — a flag instead of an exponential run — and the
oracle seam is what keeps a route open to closing it.

---

## History: the boolean-class era (superseded)

Kept so the reasoning is not re-tread. The arc, compressed:

**The original bet.** The calculator's per-entry formulas would stay
AND-of-XOR (linear over `Z₂`); LexMin via Gaussian elimination.

**Plateau-A instrumentation** (since removed — it lived in the now-deleted `CanonGraphOrdererFlipValidation`):
- `ProbeRotationsSingleFlip` (Phase 1) — single-flip probing. Headline data
  (n, primaries, coupling candidates): 2K2 `(4,5,4)`, K4 `(4,5,4)`,
  C4 `(4,6,6)`, C4+K2 `(6,13,16)`, CFI(Cycle3) even `(18,149,264)`. CFI's
  coupling density is near-maximal — most P entries depend on many guesses.
- `ProbeXorCouplings` (Phase 2) — XOR-fit per coupling-candidate entry.

**Phase 2 result: ~0% XOR-fit on every graph, including CFI** — both with
rotation variables (v1) and with a clean direction-only basis after §6.5 was
stripped (v2). Ruling out "wrong variable basis" forced a structural
diagnosis.

**Structural impossibility (boolean-era framing).** Two reasons AND-of-XOR
cannot fit: (1) transitive closure without driver tracking is OR-of-ANDs, not
AND-of-XOR; (2) the rank-based canonical reading is non-linear in the P
entries. This session *sharpened* (2): rank itself is **linear** (a count,
`Σ`); the non-linearity is the *selector + matrix-lookup* — the canonical is
`XᵀAX`, a **quadratic** form (the quadratic-assignment problem). Linear
assignment is polynomial; quadratic assignment is NP-hard; canonical labelling
is the latter.

**Horn.** TC's implication shape (`antecedents → consequent`) *is* a Horn
clause — so TC relegation handles the *constraint* side cleanly. But "total
order" is **not Horn-definable** (total orders are not closed under model
intersection), and Horn says nothing about the *objective* (the rank /
QAP readout). Horn fixes a non-problem.

**LP / scalar solvers.** The *constraint* side is LP-friendly (order
constraints are difference constraints — totally unimodular). The *objective*
is QAP-quadratic, non-convex. The LP relaxation over the Birkhoff polytope
equals *fractional isomorphism*, which equals **1-WL**
(Ramana–Scheinerman–Ullman / Tinhofer); Sherali–Adams / Lasserre hierarchies
need `Ω(n)` levels on CFI. No relaxation shortcut exists.

**Why it all pointed to the group reframe.** Boolean and algebraic classes
are *constraint* languages. The canonical is an *orbit-minimum*. An orbit is
a group-action object; it needs a group, not a formula. XOR came closest only
because `Z₂`-vector-spaces *are* groups (abelian ones) — the project had the
abelian special case and mistook it for the general tool.

§6.5 pair rotation was added (a pragmatic fix for C4+K2 with greedy
direction-flip), then stripped (it broke AND-of-XOR closure). It now returns,
re-housed as the per-level transversal — see "The current model."

The boolean-era "Plateau B (DERIVED tracking)" and "Plateau C (tier
representation)" are superseded by the chain-descent calculator (see
"Implementation").

---

## Open questions

In priority order:

1. **Is the wall reachable from the forward pass's output?** (The
   construction question.) Target: prove every obstruction the forward pass
   produces decomposes as `(resistant-abelian) ⋊ (cascading)` — or find a
   counterexample, which would be the first clean hidden-Johnson graph.
2. **The single hurdle** — per-level transversal discovery when refinement
   does not cascade and the group is non-abelian. Polynomially ≡ GI ∈ P.
3. **Restricted-class polynomiality.** Prove decomposability / polynomial
   bound on bounded-degree, bounded rank-width, bounded treewidth. Achievable,
   provable, validates the architecture.
4. **The higher-WL lever** — how far does a `k`-WL forward pass widen Tier 1?
   It absorbs all Johnson-scheme cells; quantify the gain.
5. **Relation to Babai's bound.** If the forward pass's residual obstructions
   are always Johnson-type, matching `2^O(log³n)` via a properly
   group-theoretic calculator is itself a non-trivial standalone result.

---

## What "the calculator is done" looks like

- The chain-descent calculator canonizing Tier 0 / Tier 1 / CFI in *proven*
  polynomial time. (Today: implemented and budget-bounded, but T-C unproven.)
- C4+K2 #56 and CFI(Cycle3) pass; disjoint CFI is linear in #components.
- T-A and T-B cited from computational group theory; T-C either resolved, or
  honestly scoped to a restricted class with the Tier-2 detector flagging the
  rest.
- The CFI family validated against an external canonizer.
- The doc set (overview / calculator / strategy) self-contained for an
  external reader.

Anything short of this is a research checkpoint.

---
## Status snapshot (2026-05-21)

### Model state

- **Settled:** the calculator is a stabilizer-chain lex-leader descent.
  T-A and T-B are free (computational group theory); all difficulty is
  isolated in T-C = the single hurdle = per-level transversal discovery.
- **Settled:** the tier classification (0 / 1 / 2) and the cascade ×
  composition-factor hardness map.
- **Settled:** §6.5 returns re-housed as the per-level transversal; the
  forward-pass record becomes direction-agnostic.
- **Open:** whether Tier 2 arises from the forward pass at all (construction
  question); the single hurdle in general.
---

## Reading order

For someone picking this up cold:

1. [`chain-descent-overview.md`](./chain-descent-overview.md) — the current,
   authoritative design: how the canonizer works, end to end.
2. This doc — the design detail the overview summarizes: the stabilizer-chain
   model, the hardness map and the single hurdle, T-A/T-B/T-C, and the
   construction question.
3. The code — [`ChainDescent.cs`](../GraphCanonizationProject/ChainDescent.cs),
   [`CascadeOracle.cs`](../GraphCanonizationProject/CascadeOracle.cs),
   [`CanonGraphOrdererChainDescent.cs`](../GraphCanonizationProject/CanonGraphOrdererChainDescent.cs),
   and [`PermutationGroup.cs`](../GraphCanonizationProject/PermutationGroup.cs).
4. "A cautionary detour" and "History" here — only for the path: why the
   nauty-IR calculator and the boolean approach were wrong turns.
5. [`chain-descent-strategy.md`](./chain-descent-strategy.md) — the earliest
   generation (the two-pass flip-validation design).

