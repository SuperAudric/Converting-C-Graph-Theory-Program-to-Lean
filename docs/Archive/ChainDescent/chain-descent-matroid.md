# Chain descent — propagation closure as a (candidate) matroid

This is a **working doc**, not a paper. It records an investigation —
modelling the propagation behaviour of warm 1-WL refinement as a matroid (or
weaker threshold structure), aimed at attacking T-C and the Tier-2 wall.

> ⚠ **Status (2026-05-23, final): the matroid framework on commit-set
> closures is CLOSED — neither candidate closure is a matroid.**
> §6 shows the partition-based `cl` satisfies essentially no closure-system
> axiom; §8 shows the TC-based `cl_prov` is a topological closure but
> still not a matroid (M3 refuted via machine-checked `decide`). The only
> route to a matroid framework is via linear-algebraic structure on commits
> (the linear oracle's domain), which is no longer a "generic framework"
> but a different workstream. Sections §1–§5 are kept as historical record
> of the original framing; §6 and §8 are the verdicts.

For the wider project see [`chain-descent-calculator.md`](../../chain-descent-calculator.md)
(the oracle the matroid framework was trying to supply) and
[`chain-descent-hidden-johnson.md`](../../chain-descent-hidden-johnson.md) (the
companion Tier-2 attack from the symmetry side).

---

## 1. Why this framing

The descent's T-C hurdle (calculator §4) is "discover each chain level's
transversal in polynomial time." Concretely, at a branch node we want to know:

- which pair-guesses are *forced* by which others (so we don't branch
  redundantly),
- which combinations of pair-guesses constitute *true symmetries* (so the
  linear oracle, or a successor, can read off a generator).

Both questions are the same question about a **closure operator** on the set of
pair-guesses: given a committed set `S`, what else does warm refinement force?
If this operator behaves like a matroid, we get a lot of structure for free —
representability, minors, circuit spaces, binary/non-binary classification —
and Tier-2 detection slots in as "the matroid is not binary."

This was prompted by the observation (multiple previous sessions, never written
down before now) that propagation under warm refinement appears to follow a
uniform local rule: each derived partition is forced when some threshold over a
fixed pool of other partitions is reached. That rule has matroid-shaped
features. This doc is the attempt to make it rigorous.

---

## 2. The objects

**Ground set `E`.** Unordered pair-guesses on the currently non-singleton cells.
A pair-guess `{u, v}` is a *partition decision* — we are choosing how `u` and
`v` separate, with direction quotiented away by `warm_6_2`. (Oriented
pair-guesses give an equivalent theory; unordered is cleaner.)

**Closure `cl : 2^E → 2^E`.** `cl(S) = { p ∈ E : p's endpoints lie in different
cells after warm-refining the P-matrix with `S` committed }`. Well-defined
because `warm_6_2` makes the result direction-blind.

**Block.** A `cl`-connected component — maximal `B ⊆ E` such that for every
`p, q ∈ B` there is some `S` with `p, q ∈ cl(S) ∖ cl(S ∖ {p, q})`. Informally:
"propagates together."

**Trigger (direct rule).** For `p ∈ E`, a *direct trigger* of `p` is a minimal
multiset of *immediate signature changes* that suffices to split `p`'s
endpoints in one refinement round. The user-visible "`c-of-k`" pattern is a
trigger shape: any `c` of `k` specific other partitions, committed, suffice to
fire `p`.

**Circuit (closure level).** A minimal dependent set in `cl` — minimal `C ⊆ E`
such that `c ∈ cl(C ∖ {c})` for every `c ∈ C`. By definition `|C| = c + 1`
where `c` is the trigger size at the circuit level. (In any *matroid*, the
closure-level `c` for any circuit is `|C| - 1`. The direct-rule `c-of-k` can be
finer; see §5.)

---

## 3. Two possible worlds

We have not yet decided between two framings:

**World A — full matroid.** `cl` satisfies the matroid exchange axiom:

> `y ∈ cl(S ∪ {x}) ∖ cl(S)  ⟹  x ∈ cl(S ∪ {y}) ∖ cl(S)`.

If so, the propagation structure is a matroid, every circuit has direct-rule
`c = k - 1` at the closure level, and the standard matroid toolkit applies
(circuit space, representability, minors).

**World B — threshold-only.** Direct triggers are still `c-of-`k`-shaped, but
`cl` does not satisfy exchange — so the structure is something between a
matroid and a general closure operator. We'd need new vocabulary for it.

**Current state.** The session's tentative judgement (subject to verification)
is **World A holds**, on two grounds:

1. The user observation that "if `x` would determine `y` then `y` would
   determine `x`" — appealing to the reversibility of warm refinement /
   direction-symmetry — is the exchange axiom with `S = ∅`. The general case
   needs an inductive argument (§5).
2. Every concrete case worked through (CFI(C₃), small CFI graphs, the ladder
   below) gives a structure that *is* a matroid — generally the cycle matroid
   of an underlying base graph or a parallel-class block.

Neither is proof. The first really-load-bearing technical step (§7) is proving
or refuting exchange.

---

## 4. The archetypical example: ladder with one cycle-closed side

A "ladder graph with the top of one side connected to its bottom" — two
parallel sides of length `n` with rungs, but one side is closed into an
`n`-cycle. After 1-WL:

- Vertices are coloured by distance to the path-side endpoints; the cycle
  closure distinguishes the two sides.
- The remaining indistinguishability is a *mirror symmetry* (reflection across
  the ladder's centre). Each vertex is paired with exactly one mirror; `|E|`
  equals the number of mirror pairs.

For one mirror-pair partition `e_v` (the decision "`v` and `v̄` split"):

> `e_v` fires whenever **any one** of `{e_{n^←_v}, e_{n^→_v}, e_{n^⊥_v}}` —
> `v`'s inward, outward, and rung neighbours' partitions — has fired.

That's a `1-of-3` *direct* rule. Cascade through the whole ladder gives:
committing any one mirror-pair propagates to all of them. So at the *closure*
level, the block is `U_{1, |E|}` — every singleton independent, every pair
dependent — and the closure-level circuits are size-2 (every pair is parallel).
`U_{1, k}` is binary (cycle matroid of a `k`-edge multigraph).

**Resolution of the apparent `c < k - 1` paradox.** The `1-of-3` is the
*direct propagation rule*, not the closure circuit. Closure circuits here are
size-2; direct-rule reads as "three different size-2 circuits all hitting the
same target", which the algorithm sees as a single `1-of-3` trigger. Both
descriptions are correct; they live at different levels.

**Conjectured universality.** This shape — vertex breaks from its colour class
when a single neighbour-pair splits — is forced by `refineStep_iff`. The
multiset-signature changes exactly when a neighbour's colour changes; the
*minimal* signature change is a single neighbour-pair flip. Caveat: two
opposite flips can *cancel*, leaving the multiset unchanged. The archetypal
case (symmetry / no cancellation) is therefore "1 of `k`," and the universal
statement is "1 of `k`, unless cancellation".

**Open Lean lemma.** Prove: at every warm-refine round, a vertex `v` breaks
from its cell `C` iff the count vector `(|N(v) ∩ D_i|)_i` over the new
sub-cells `D_i` of some neighbour cell differs from at least one other vertex
in `C`'s count vector. This is a multiset-cardinality reformulation of
`refineStep_iff` and a moderate-size lemma; nothing else in this doc rests on
unproved Lean.

---

## 5. The two candidate algorithms

Both were proposed in the session. Algorithm 1 is concrete and polynomial with
one known gap; Algorithm 2 is more elegant but needs nailing down.

### 5.1 Algorithm 1 — iterative rotation-minimisation

For each *first* propagation `P` that fires during the spine pass:

1. Let `g_1, ..., g_t` be the guesses made up to and including the one that
   fired `P`.
2. **Rotation-minimisation.** Cyclically rotate the guess order; observe at
   what position `P` fires. Any guess that ends up *after* `P` in some
   rotation is not in `P`'s trigger — drop it. Repeat until stable. Output: a
   transversal `T`.
3. **Pool expansion.** For each position in `T`, replace that guess with every
   other available pair and re-run; keep the alternatives that also fire `P`.
   Union gives the pool `K`; common size of all transversals is `c`.
4. **Independence.** When characterising the next circuit, treat
   already-characterised circuits' propagations as free (don't count them as
   "needed guesses").

**Cost.** ≤ `|E| = O(n²)` circuits; per circuit ≤ `t · spine_cost` for
rotation and `c · |E| · spine_cost` for pool expansion. With spine = `O(n³)`,
total roughly `O(n⁷)`. Polynomial.

**The known gap.** Step 4 is sound for *isolated* circuits. When circuit `Y`
overlaps a previously-characterised `X` (`Y`'s trigger includes a relation
that was itself a propagation of `X`), the algorithm sees `X`'s downstream
effects as part of `Y`'s trigger and overcounts. Naively repairing this
requires checking every maximal non-propagating subset — `k choose (c-1)`,
potentially exponential.

**The provenance fix (recommended).** The strategy doc's existing
`DERIVED`-record-with-driver structure (strategy §10) already requires tagging
each derived relation with the guess that drove it. Extend `driver` to a
`Set` of drivers (when multiple earlier circuits could each have produced the
same relation). Then:

- In step 2, when testing whether dropping `g_i` kills `P`, also test
  dropping every `g_j` whose driver-set includes `g_i`.
- In step 4, "treat known circuits as free" becomes "in driver-space, expand
  observed triggers to their ultimate drivers before counting."

The exponential blowup collapses to `O(n²)` driver-graph traversal per guess.
The provenance record is already a hard requirement of the linear oracle
(calculator §6); this just sharpens its definition.

### 5.2 Algorithm 2 — certifying via 1-WL discrepancies

Theoretical, not yet rigorous.

When 1-WL refines partition `C` into `C_1, C_2`, the cause is a multiset
discrepancy in some neighbour cell `D` that *itself* split. The discrepancy
identifies the cells whose state contributes to the trigger; inherit their
own triggers; combine.

Naïve combination of dependencies gives an exponentially large Boolean DAG —
this is exactly the dead-end the boolean-class era hit
([`chain-descent-calculator.md`](../../chain-descent-calculator.md) §10.2). The
new ingredient: knowing each propagation is `c-of-k`-shaped lets you maintain
only the threshold form throughout, sidestepping the DAG.

**What needs nailing down.**

1. *Decoding lemma.* Given a 1-WL discrepancy at a split moment, the differing
   multiset elements enumerate exactly the cells contributing to the trigger.
   (Plausible; essentially `refineStep_iff`'s contrapositive.)
2. *Composition lemma.* If a propagation `p` directly depends on cells `D_i`
   each with trigger `T_i`, then `p`'s ultimate trigger is `c-of-k` over `⋃
   T_i`. **This is load-bearing and not obviously true** — the conjunction of
   two `c-of-k` thresholds is not in general itself `c-of-k`. May hold only
   in the binary case (where threshold-of-thresholds = XOR-of-XOR = XOR);
   may fail for non-binary.
3. *Consistency.* Output agrees with Algorithm 1 on the same inputs.

**If composition holds only in the binary case**, then Algorithm 2 is a
Tier-1-only poly-time *certifier*, and Algorithm 1 + an `F_2`-rank check
(§7) is the broader instrument.

---

## 6. Closure-system status of `cl` — negative result (2026-05-23)

After investigating M0–M3 and additional standard closure-system axioms via
explicit small-case construction, the finding is that **`cl` as defined in §2
satisfies essentially no standard closure-system axiom unhypothesised** —
only extensiveness (CL1) survives. Every other tested property has a
machine-verifiable witness against it (all on 4–5-vertex empty graphs with
`χι ≡ 0`).

| Axiom | Holds? | Witness against |
|-------|--------|------------------|
| **CL0** `cl(∅) = ∅` | ✓ (under all-same χι) | — |
| **CL1** extensive `S ⊆ cl S` | ✓ (conjectured, canonical `S`) | — |
| **CL2** idempotent `cl(cl S) = cl S` | ✗ | `S = {(0,1),(2,3)}` (4-vertex) |
| **CL3** monotone `S ⊆ T → cl S ⊆ cl T` | ✗ | M0 counterexample (below) |
| **M3** matroid exchange | ✗ | `S={(0,1)}, x=(0,2), y=(2,3)` (below) |
| **A3** anti-exchange (convex geometry) | ✗ | `S=∅, x=(0,1), y=(0,2)` |
| **Sub** additivity `cl(S∪T) = cl S ∪ cl T` | ✗ | follows from monotone failure |
| **Subsub** subadditivity `cl(S∪T) ⊆ cl S ∪ cl T` | ✗ | `S={(0,2),(1,3)}, T={(0,2),(1,4)}` (below) |

The cl operator is therefore in **no** standard closure-system family
(topological closure, matroid, convex geometry, polymatroid, Moore family,
greedoid, etc.).

### 6.1 The three load-bearing counterexamples

**M0 / CL3 failure** (`cl S ⊄ cl T` despite `S ⊆ T`). With `n=4`, empty
adjacency, `χι ≡ 0`:

- `S = {(0,1)}`: partition `{{0},{1},{2,3}}`. So `(0,2) ∈ cl S`.
- `T = {(0,1), (2,3)}`: the involution `(0 2)(1 3)` is now an automorphism
  of `(adj, Pof T)`, partition becomes `{{0,2},{1,3}}`. So `(0,2) ∉ cl T`.

Adding the `(2,3)` commit *restored* the swap symmetry that `(0,1)` alone
broke, coarsening the partition.

**M3 exchange failure.** With same setup, `S = {(0,1)}, x = (0,2), y = (2,3)`:

- Premise: `y = (2,3) ∈ cl(S ∪ {x}) ∖ cl S`. ✓ (`(2,3)` is forced by
  `{(0,1),(0,2)}` but not by `{(0,1)}` alone.)
- Conclusion needs `x ∉ cl S` — but `x = (0,2) ∈ cl({(0,1)})`. Fails.

**Subadditivity failure** (`cl(S∪T) ⊄ cl S ∪ cl T`). 5-vertex empty graph,
`χι ≡ 0`:

- `S = {(0,2), (1,3)}`: partition `{{0,1},{2,3},{4}}`. `(0,1) ∉ cl S`.
- `T = {(0,2), (1,4)}`: partition `{{0,1},{2,4},{3}}`. `(0,1) ∉ cl T`.
- `S ∪ T = {(0,2), (1,3), (1,4)}`: vertex 0 commits to one target (`u=2`,
  appearing in both S and T — coalesces); vertex 1 commits to two targets
  (`u=3` from S and `u=4` from T — accumulate). Round-1 multisets diverge
  by `.less` count (1 vs 2). `(0,1) ∈ cl(S ∪ T)`.

The mechanism: per-vertex *overlap structure* between S and T is
asymmetric, so individual sigs (which see overlap as a single `.less`
entry) can match while joint sigs (which see overlap as one entry but
non-overlap as two) diverge.

### 6.2 Why this kills the framework as currently defined

The matroid framing was built on the intuition that "if `x` determines `y`,
then `y` determines `x`" — a local symmetry of warm refinement. That local
symmetry is real (single-round count-vector flips are symmetric in their
endpoints), but it does **not** lift to a closure-operator-level structural
property. The reason, made concrete by the counterexamples: warm-refinement's
sensitivity to *graph automorphisms of `(adj, Pof S)`* means committing more
pairs can either create or break automorphisms in non-monotone ways. There's
no closure operator that respects this — closure systems are by definition
monotone.

### 6.3 The fresh-colour escape, and why it's degenerate

The natural fix candidate was: assume `χι` makes every "relevant" pair-guess
endpoint a singleton, breaking the swap symmetries that cause the failure.
This works **structurally**:

| Axiom | Status under fresh-colour |
|---|---|
| M0 | ✓ (`cl_monotone_T_individualised`, actually `cl S = cl T` strictly) |
| M1 | ✓ (`cl_extensive`) |
| M2 | ✓ (`cl_idempotent`) |
| M3 | vacuously ✓ (premise can't be satisfied: `cl(S∪{x}) = cl S` by M0 strong) |

But the resulting structure is **degenerate**: under full fresh-colour `χι`
makes every canonical pair an endpoint-pair of singletons, so `cl(∅)`
already equals the whole ground set. The matroid is rank-0 (every element a
loop), trivially binary, indistinguishable from any other rank-0 matroid.
**Tier-2 detection power: zero** — every graph including a hypothetical
hidden Johnson is classified as binary (Tier-1).

Under *partial* fresh-colour (some endpoints individualised, others not),
the M0 counterexample re-emerges in the unindividualised vertices. The
fresh-colour fix only works at strengths that make it useless.

### 6.4 What survives in Lean

All of the following are **proved** in `ChainDescent.lean` §13, axiom-
checked against the modelling axioms only (no `sorry`, no `native_decide`):

- `cl_extensive` — committed pairs are forced (under fresh-colour on `S`).
- `cl_monotone_T_individualised` — `cl S ⊆ cl T` for `S ⊆ T` (in fact
  `cl S = cl T`) under fresh-colour on `T`.
- `cl_monotone_discrete` — degenerate all-singletons case.
- `cl_idempotent` — `cl(cl S) = cl S` under fresh-colour on `S ∪ cl S`.
- `warmRefine_samePartition_T_individualised` — the strong-form M0.
- `Pof_mono_entry_of_unknown` — entry-wise monotonicity of `Pof` itself
  (a fact about `Pof` independent of refinement).

These are kept as proved-positive content even though the framework
overall is structurally dead — they document the *fresh-colour subset* of
the theory cleanly, and any future revival of matroid-like-structure work
will likely reuse them.

The would-be `cl_exchange` lemma was removed (refutable as above), with a
detailed closure-zoo failure record left in its place as a comment block.

---

## 7. The intended Tier-2 detection scheme (would have required a matroid)

This section is **conditional on the matroid framework working** — which,
per §6, it does not at the cl-on-pair-guesses level. Kept as a record of the
intended structure, in case a future re-defined closure (e.g. cl_prov, §8)
recovers the matroid axioms.

Were the propagation closure a matroid:

- It would be **binary** iff representable over `F_2` iff (Whitney) it has
  no `U_{2,4}`, `F_7`, `F_7*`, `M(K_5)*`, or `M(K_{3,3})*` minor.
- **Binary ⟺ CFI-shaped ⟺ linear oracle handles it.** Tier 1.
- **Non-binary ⟺ a forbidden minor present ⟺ hidden-Johnson signature.**
  Tier 2.

**The poly-time test** (conditional). Algorithm 1 outputs circuits with
`(c, k)` and pool contents. Form the indicator vectors of those circuits
over `F_2` and compute the rank. A binary matroid has rank equal to
`|E| − (number of matroid components)`. Strict inequality would be the
certifying witness of a non-binary minor.

This idea remains the right shape for a Tier-2 detector — it just needs a
matroid to test. The §8 pivot is about constructing one at a different
level.

---

## 8. Provenance-tracking closure `cl_prov` — also not a matroid

The §6 negative result is specific to *cl as defined in §2* (pairs separated
by warm refinement). The natural next layer is to track *provenance* — which
commit drove which derived relation — and ask whether **that** structure is a
matroid. We test the simplest version: `cl_prov(S)` = pair-guesses decided by
transitive closure of `S`'s commits, no 1-WL cascade.

### 8.1 Definition and result

`cl_prov(S) := { p ∈ Egnd n : transitiveClose (commitsToP S) p.1 p.2 ≠ unknown }`

where `commitsToP S` is the partial-order matrix with `.less` at canonical-
direction entries of `S`, `.greater` at the reverses, and `.unknown` elsewhere.

**Closure-axiom status of `cl_prov`** (`ChainDescent.lean` §14):

| Axiom | Status | Note |
|-------|--------|------|
| CL0 `cl_prov ∅ = ∅` | **proved** | `cl_prov_empty` |
| CL1 extensive | **proved** for canonical S | `cl_prov_extensive` |
| CL2 idempotent | **proved** (2026-05-25) | `cl_prov_idempotent` |
| CL3 monotone | **proved** (2026-05-25) | `cl_prov_monotone` |
| **M3 exchange** | **REFUTED** | machine-checked via `decide` (`cl_prov_M3_false`) |

So `cl_prov` is rigorously a **topological closure** (Moore family /
Kuratowski axioms) — *but it is not a matroid*. The intended Tier-2
detection scheme of §7 (binary representability of the matroid) cannot be
applied. The CL2/CL3 proofs use a `LessMono` (single-direction entry
mono) predicate carried through `transitiveClose` under joint
canonical-consistency; the key lemma `canConsistent_no_conflict` rules
out the bad case where `closeStep`'s `.less`-first tie-break would shift
direction (a pair carrying both a `.less`-chain and a `.greater`-chain).
TC idempotence (`transitiveClose_idempotent`) comes from a `numUnknown`
potential argument: each non-fixed-point round strictly decreases the
unknown count, bounded by `n*n`. All axiom-checked: only
`propext, Classical.choice, Quot.sound` (no `refineStep` axioms; the
CL2/CL3 chain is pure TC theory, independent of warm refinement).

### 8.2 The M3 refutation

`n = 5`, `S = {(1,2), (3,4)}`, `x = (2,3)`, `y = (1,4)`:

- `cl_prov(S) = {(1,2), (3,4)}` — no common-vertex chain.
- `cl_prov(S ∪ {x})` includes `(1,4)` via the chain `1 → 2 → 3 → 4`.
- `cl_prov(S ∪ {y}) = {(1,2), (3,4), (1,4)}` — no chain reaching `(2,3)`
  since neither `(2,?)` nor `(?,3)` is decided.

So `y ∈ cl_prov(S ∪ {x}) ∖ cl_prov(S)` (premise) but
`x ∉ cl_prov(S ∪ {y})` (conclusion fails). M3 violated.

Machine-checked in Lean by `decide` (full computation, no axioms beyond
`propext, Classical.choice, Quot.sound` — notably no `refineStep` axioms
since TC closure is independent of warm refinement, and no `native_decide`).

### 8.3 Why this closes the matroid branch

The two natural closure operators on commit-sets — partition-based (§6) and
TC-based (§8) — have both been tested and neither is a matroid:

- `cl` (partition-based): fails CL0–M3 essentially universally.
- `cl_prov` (TC-based): is a clean topological closure but fails M3.

A matroid framework requires M3 (exchange). M3 captures the "if x determines
y then y determines x" symmetry at the closure-operator level, which neither
of these operators exhibits without extra structure.

**The remaining possibility for a matroid framework on commits** would be a
*linear-algebraic* closure: assign each commit a vector in some F-vector
space (e.g., `F_2` for CFI's parity structure), and define closure as linear
span. For CFI specifically this would give the cycle matroid of the base
graph (a binary matroid). For other graph classes it would give other
matroids — non-binary for `A_k`-symmetric hidden constructions, if any
exist.

This is **not a generic framework** — it's specific to the algebraic
structure of the particular graph's automorphism group. Building it is
equivalent to (or strictly harder than) implementing the linear oracle of
[`chain-descent-strategy.md`](../../chain-descent-strategy.md) §10. That is a
substantial project on its own and lives in the linear-oracle workstream,
not in this matroid-framework one.

### 8.4 Verdict on the matroid framework

> **The matroid framework on commit-set closures is dead.**
>
> Neither the partition-based `cl` (§6) nor the TC-based `cl_prov` (§8) is
> a matroid. The fresh-colour escape on `cl` (§6.3) gives all four axioms
> at the cost of structural degeneracy (rank-0). Anything richer (linear-
> algebraic / oracle-driven) is no longer a generic framework — it's the
> linear oracle itself.
>
> The matroid framing's value, retrospectively, has been to crystallise
> *what the Tier-2 detector needs*: a structure where commits form a
> classifiable matroid whose binary/non-binary character distinguishes
> Tier-1 from Tier-2. The conclusion is that no such structure exists at
> the commit-set closure level. Tier-2 detection (if it exists at all)
> lives at a different layer — either the linear oracle (which makes the
> structure F_2-explicit) or one of the other attack routes
> (`chain-descent-hidden-johnson.md`, k-WL widening).

---

## 9. Open work — Tier-2 attack routes (post-matroid)

With the matroid framework on commit-set closures closed (§6, §8), Tier-2
attack moves to the other workstreams:

1. **Linear oracle implementation** ([`chain-descent-calculator.md`](../../chain-descent-calculator.md) §6) — builds the
   `Z₂` Gaussian-elimination oracle for CFI-style decisions. The matroid
   structure of the linear oracle's output IS the binary matroid we wanted;
   classifying it as binary-vs-not-binary IS the Tier-2 detector. This is
   the most directly relevant work given §8's finding.
2. **Hidden-Johnson Piece C** ([`chain-descent-hidden-johnson.md`](../../chain-descent-hidden-johnson.md) §5) —
   complete the cascade-half of the near-theorem (visible Johnson is
   Tier-1). Doesn't address encoded Johnson but is solid finite progress.
3. **k-WL widening** ([`chain-descent-calculator.md`](../../chain-descent-calculator.md) §7) — bound how much
   `k`-WL refinement widens Tier-1; known to absorb visible Johnson schemes,
   doesn't cross the true wall.
4. **Local-rule universality lemma** (§4) — moderate-size Lean lemma about
   how warm refinement splits cells; useful regardless of framework since it
   characterises *what* warm refinement does at each step. Standalone value.

Items previously deferred (Algorithm 2 composition, binary-closure
conjecture, C# Algorithm 1 probe) were conditional on the matroid framework
and are now obsolete — the framework they were premised on doesn't exist.

---

## 10. Cross-references

- [`ChainDescent.md`](../../../GraphCanonizationProofs/ChainDescent.md) — Lean
  proof state. Holds `warm_6_2`, `warmRefine_agree_off'`, the spine
  machinery — the partition-sharing scaffolding this framework sits on.
- [`chain-descent-calculator.md`](../../chain-descent-calculator.md) — the
  oracle this framework is trying to supply. §4 (T-A/T-B/T-C decomposition)
  and §6 (linear oracle) define what a polynomial calculator must do; the
  matroid here is one candidate route. §10.2 records the boolean-class era —
  the matroid framing is the *next* attempt at the same target, with the
  `c-of-k` constraint as the new ingredient.
- [`chain-descent-strategy.md`](../../chain-descent-strategy.md) — algorithm
  spec. §10 ("closure as a guess") prescribes the `DERIVED`-record
  provenance the matroid framework requires for the gap fix; §12 (invariant
  6.2) is the partition-sharing this rests on.
- [`chain-descent-hidden-johnson.md`](../../chain-descent-hidden-johnson.md) —
  the companion Tier-2 attack from the symmetry side. Where this doc tries
  to *detect* a hidden Johnson via matroid structure, that doc tries to
  *rule out* visible Johnson via association-scheme cascades. The two are
  independent and could in principle combine.

---

## 11. Session breadcrumbs (2026-05-23)

What this session contributed:
- Resolved the framing question: unordered pair-guesses as ground set,
  threshold-only stance accepted (later upgraded to "tentatively World A").
- Walked Algorithm 1 through CFI(C₃); confirmed the algorithm produces the
  expected 2-of-3 cycle-matroid circuit.
- Identified the provenance fix for the partial-overlap gap, connecting it
  to the strategy doc's existing `DERIVED`-driver requirement.
- Diagnosed the local-rule-vs-closure-circuit distinction via the ladder
  example; `1-of-3` direct rule produces `U_{1, k}` closure, both binary.
- Mapped matroid axioms onto warm-refinement: M0–M2 free, M3 the load-bearing
  open claim, with a chain-reversal induction sketch.
- Positioned binary/non-binary classification (via `F_2`-rank of circuit
  indicators) as the Tier-2 detection scheme.
- Set the no-known-hidden-Johnson observation as a conjecture of the
  framework rather than a separate piece of evidence.
- **Lean scaffold landed** (later same day): §13 in `ChainDescent.lean`.
  `cl_extensive` proved. `cl_idempotent`, `cl_exchange` stated as sorries
  with proof-obligation docstrings.
- **M0 unhypothesised version REFUTED** (later same day): 4-vertex
  counterexample (above, §6). The "M0 free" claim was wrong. The trivial
  fully-discrete version `cl_monotone_discrete` is proved but vacuous.
- **M0 under T-individualised PROVED** (later same day): via the *stronger*
  `warmRefine_samePartition_T_individualised` — under T-individualised χι
  the warm-refined partitions under `Pof P₀ S` and `Pof P₀ T` literally
  coincide (`samePartition`), so `cl S = cl T` for every `S ⊆ T`, not just
  `⊆`. Proof: induction on refinement round; non-T vertices use
  `signature_eq_of_samePartition` + row-agreement of `Pof S` and `Pof T`
  off `T`-vertices; T-vertices stay singletons via
  `iterate_refineStep_preserves_singleton` and contribute vacuously.
- **M2 under fresh-colour PROVED** (later same day): falls out of M0 strong
  form with `T = cl S`. Under `∀ p ∈ S ∪ cl S, SingletonAt χι p`, M0 strong
  gives `samePartition (warmRefine_S) (warmRefine_{cl S})`, so the sets of
  separated pairs literally coincide. Three lines of Lean.
- **M3 unhypothesised REFUTED** (later same day): with `S = {(0,1)},
  x = (0,2), y = (2,3)` on the 4-vertex empty graph, the premise holds but
  the conclusion's `x ∉ cl S` clause fails. Under fresh-colour, M3 is
  vacuously true (premise can't be satisfied by M0 strong-form constancy).
- **Subadditivity also REFUTED** (same day): `cl(S ∪ T) ⊄ cl S ∪ cl T` in
  general; witness `S = {(0,2),(1,3)}, T = {(0,2),(1,4)}` on 5-vertex empty
  graph. Mechanism: per-vertex overlap structure between S and T is
  asymmetric, so joint sigs accumulate `.less` entries non-symmetrically
  even when individual sigs match.
- **Closure-zoo survey** (same day): tested cl against topological closure,
  matroid, convex geometry / antimatroid, polymatroid, Moore family,
  greedoid. **cl is in none of them.** Only CL1 (extensiveness) survives
  unhypothesised. Recorded in `ChainDescent.lean` §13 comment block and
  here in §6.
- **`cl_exchange` removed from Lean** (replaced by the closure-zoo
  failure record).
- **`cl_prov` (TC-based provenance) tested and FAILS too**: ChainDescent.lean
  §14 defines `cl_prov` via transitive closure, proves CL0 and CL1, refutes
  M3 via decide on `n=5, S={(1,2),(3,4)}, x=(2,3), y=(1,4)`. CL2 and CL3
  proved (2026-05-25) via `LessMono` + `CanConsistent` infrastructure plus
  `numUnknown`-potential TC idempotence — axiom-clean, no `refineStep`
  dependency. `cl_prov` is rigorously a **topological closure** but
  **not a matroid** — the matroid axioms still don't hold.
- **Matroid framework on commit-set closures is now definitively CLOSED**:
  both candidate closures (partition-based `cl`, TC-based `cl_prov`) have
  been tested and neither is a matroid. The remaining option (linear-
  algebraic closure) is the linear oracle itself, not a generic framework.
  See §8.4 for the verdict.

What this session did NOT settle (the deliberately-out-of-scope items):
- Whether a linear-algebraic closure on commits (the linear oracle) is
  buildable and gives a binary matroid for the relevant graph classes.
  That's its own workstream — see `chain-descent-strategy.md` §10.
- Whether the original binary-closure conjecture (now reformulated for the
  linear oracle's output) holds.

The natural next action is to pivot to one of the §9 attack routes —
linear oracle implementation being the most directly relevant.
