# Chain descent — propagation closure as a (candidate) matroid

This is a **working doc**, not a paper. It records a current investigation —
modelling the propagation behaviour of warm 1-WL refinement as a matroid (or a
slightly-weaker threshold structure), with the goal of attacking T-C and the
Tier-2 wall. Sections are organised so the next reader can pick up where the
last session stopped; conjectures and gaps are flagged.

For the wider project see [`chain-descent-calculator.md`](./chain-descent-calculator.md)
(the oracle the matroid framework is trying to supply) and
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) (the
companion attack on Tier-2 from the symmetry side).

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
([`chain-descent-calculator.md`](./chain-descent-calculator.md) §10.2). The
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

## 6. Symmetry, and what existing proofs do / don't give

**Forcing symmetry.** "`x` determines `y` ⟹ `y` determines `x`" is taken as
the bedrock symmetry. It is *not* a direct corollary of `warm_6_2` or
`warmRefine_agree_off` (those are about a single guess's direction-symmetry).
The intuitive argument:

- `x` determines `y` means there is a chain of signature-changes from
  committing `x` to splitting `y`'s endpoints.
- Each signature change is a count-vector flip (§4) that is locally
  symmetric in its two endpoints.
- Chain-reverse each flip and you get a chain from `y` to `x`.

This is the proof shape for exchange too (§7). It is plausible but unproved.

**What we already have in Lean** (`ChainDescent.lean`):

- `warm_6_2` — single-guess direction-symmetry at partition level.
- `warmRefine_agree_off` / `warmRefine_agree_off'` — multi-guess
  partition-sharing when `P`-matrices agree off a singleton-`D` set. The
  **spine** result: all `2^d` branches share one partition.
- `target_direction_blind`, `target_agree_off` — partition-invariant target
  selection composes.

These give us: every guess set `S` induces a well-defined partition (the
*spine partition* at `S`); hence `cl(S)` is well-defined as the set of pairs
separated by that partition. They do *not* give exchange.

**What is missing for the matroid framework:**

| axiom | status (revised 2026-05-23) |
|---|---|
| M0 monotone | **unhypothesised version is FALSE** — counterexample below. Fresh-colour fix `cl_monotone_T_individualised` is **proved** (via the stronger `warmRefine_samePartition_T_individualised` — under T-individualised χι, `cl S = cl T` for any `S ⊆ T`, not merely `⊆`). The trivial all-discrete version `cl_monotone_discrete` is also proved but vacuous. |
| M1 extensive | proved under fresh-colour hypothesis: `cl_extensive` |
| M2 idempotent | sorry (Lean), proof sketch in `ChainDescent.lean` §13 |
| M3 exchange | sorry (Lean), the genuinely open claim |

**M0 counterexample.** `n = 4`, `adj ≡ 0`, `χι ≡ 0`, `S = {(0,1)}`,
`T = {(0,1), (2,3)}`. Under `Pof S`'s asymmetric single commit, vertex 0's
round-1 signature has a `.less` entry, vertex 2's is all `.unknown` — they
split. Under `Pof T`'s symmetric pair of commits the involution
`(0 2)(1 3)` is an automorphism of `(adj, Pof T)`, so vertices 0 and 2 are
kept co-classed by refineStep. So `(0, 2) ∈ cl S \ cl T` — *adding* the
`(2,3)` commit to `S` un-forces the `(0,2)` separation by introducing a new
swap symmetry. So `cl S ⊄ cl T`.

**Why this matters.** The matroid framing on pair-guesses with χι fixed and
*unindividualised* is structurally wrong: the closure operator can shrink
when the input grows, because added commits can *restore* symmetries that
fewer commits broke. This is the opposite of the "more info → finer
partition" intuition.

**The fresh-colour fix.** Individualising the endpoints of `T` to distinct
`χι`-singletons mechanically blocks the swap-symmetry mechanism: the
involution `(0 2)(1 3)` is no longer a colour-preserving automorphism
because `χι 0 ≠ χι 2` and `χι 1 ≠ χι 3` by construction.
`iterate_refineStep_preserves_singleton` then keeps `0,1,2,3` apart
throughout. The candidate fixed statement is `cl_monotone_T_individualised`
in `ChainDescent.lean` §13 — under the hypothesis that every endpoint of
every pair in `T` (the larger set) is already a `χι`-singleton, `cl S ⊆ cl T`.
Not yet proved; this is the natural M0 target post-counterexample.

**Implication for the whole framework.** This may not be a fatal blow — M0
might still hold under fresh-colour individualisation, and that *is* the
matroid-friendly model already used by `warm_6_2` and `warmRefine_agree_off'`.
But it does mean every matroid axiom needs the fresh-colour hypothesis
attached explicitly. The "M0 is free" claim above was wrong.

---

## 7. The Tier-2 detection scheme

Granting World A (matroid):

- The matroid is **binary** iff representable over `F_2` iff (Whitney) it has
  no `U_{2,4}`, `F_7`, `F_7*`, `M(K_5)*`, or `M(K_{3,3})*` minor.
- **Binary ⟺ CFI-shaped ⟺ linear oracle handles it.** Tier 1.
- **Non-binary ⟺ a forbidden minor present ⟺ hidden-Johnson signature.**
  Tier 2.

**The poly-time test.** Algorithm 1 outputs circuits with `(c, k)` and pool
contents. Form the indicator vectors of those circuits over `F_2` and compute
the rank. The matroid is binary iff the rank equals `|E| − (number of
matroid components)`. A strict inequality is the certifying witness of a
non-binary minor — equivalently, of Tier 2.

This is **independent** of whether one can construct a hidden-Johnson graph
explicitly (calculator §7's open construction question); it gives the
canonizer a direct test on the input.

**Caveat.** Binary representability detection from a matroid given by an
oracle is polynomial (Truemper's algorithm); from a generating set of
circuits it is Gaussian elimination, also polynomial. The bottleneck is
having Algorithm 1's output, not the test.

---

## 8. No-known-hidden-Johnson — what to do with it

No graph construction is known that hides an `A_k`-on-subsets factor; this is
real evidence (decades of looking) but not proof. The matroid framework gives
this a precise formulation:

> **Conjecture (binary closure).** For every graph `G`, the propagation
> closure `cl_G` is a binary matroid.

If true: no hidden Johnson exists, the descent's Tier 2 is empty, and chain
descent with linear oracle is polynomial. If false: a counterexample is the
first known hidden-Johnson construction.

This conjecture is a *target* for the framework, not a result of it.

---

## 9. Open work — the next attack

In order:

1. **Lean: prove M0–M2** — short, mechanical, gives the matroid scaffolding.
2. **Lean: attempt M3 (exchange)** via the chain-reversal induction sketched
   in §6. Three possible outcomes:
   - **Proved.** Propagation closure is a matroid. Record as theorem; move
     on to §7's detection scheme.
   - **Proved with extra hypothesis** (e.g. strengthened fresh-colour;
     no-cancellation; quotient by parallel classes). The exact hypothesis IS
     the structural insight; record it.
   - **Refuted with witness.** The counterexample is a structural object
     worth studying — it's where the matroid framing fails and a different
     framework is needed.
3. **Lean: the local-rule universality lemma** (§4 last paragraph) — a
   moderate-size multiset-cardinality reformulation of `refineStep_iff`. Used
   downstream by Algorithm 2's decoding lemma.
4. **Paper / sketch: Algorithm 2's composition lemma** (§5.2 step 2) — does
   composition of `c-of-k` thresholds preserve `c-of-k` shape? Test on small
   binary and non-binary cases; if binary-only, the algorithm is Tier-1
   certifier.
5. **Paper / sketch: the binary-closure conjecture** (§8) — try to prove for
   *graphs producible by the descent's output*, even if not for all graphs.
   Connects to the construction question (calculator §7).
6. **C# implementation probe** — implement Algorithm 1 (with the provenance
   fix) and run on CFI(C₃), CFI(K₄), bowtie-CFI, J(5,2), and disjoint
   mixtures. Empirically verify the matroids predicted by §4 / §7. This is
   the cheapest sanity check on the whole framework.

The exchange axiom (item 2) is the single thing that decides whether this
framework is the right tool at all. Everything downstream depends on it.

---

## 10. Cross-references

- [`ChainDescent.md`](../GraphCanonizationProofs/ChainDescent.md) — Lean
  proof state. Holds `warm_6_2`, `warmRefine_agree_off'`, the spine
  machinery — the partition-sharing scaffolding this framework sits on.
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) — the
  oracle this framework is trying to supply. §4 (T-A/T-B/T-C decomposition)
  and §6 (linear oracle) define what a polynomial calculator must do; the
  matroid here is one candidate route. §10.2 records the boolean-class era —
  the matroid framing is the *next* attempt at the same target, with the
  `c-of-k` constraint as the new ingredient.
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) — algorithm
  spec. §10 ("closure as a guess") prescribes the `DERIVED`-record
  provenance the matroid framework requires for the gap fix; §12 (invariant
  6.2) is the partition-sharing this rests on.
- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) —
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

What this session did NOT settle:
- Whether exchange (M3) actually holds.
- Whether Algorithm 2's composition lemma holds in the non-binary case.
- Whether the binary-closure conjecture holds for graphs the descent
  produces.
- Whether `c < k - 1` (World B) ever genuinely occurs at the *closure
  circuit* level (vs. the direct-rule level, where it clearly does).

The natural next action is M2 (cl_idempotent) or M3 (cl_exchange) — M0 and
M1 are now solid under T-individualised χι. M2 has a per-cell-symmetry
proof sketch; M3 is the genuinely open one.
