# Chain descent — propagation closure as a (candidate) matroid

This is a **working doc**, not a paper. It records an investigation —
modelling the propagation behaviour of warm 1-WL refinement as a matroid (or
weaker threshold structure), aimed at attacking T-C and the Tier-2 wall.

> ⚠ **Status (2026-05-23): the framework as defined is structurally dead.**
> See §6 for the closure-zoo testing showing cl satisfies no standard
> closure-system axiom except extensiveness. The fresh-colour escape (§6.3)
> makes the axioms hold but degenerates the structure (no Tier-2 detection
> power). §8 proposes a pivot to provenance-tracking closure `cl_prov` as
> the candidate revival path; sections §1–§5 are kept as historical record
> of the original framing.

For the wider project see [`chain-descent-calculator.md`](./chain-descent-calculator.md)
(the oracle the matroid framework was trying to supply) and
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) (the
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

## 8. The proposed pivot — provenance-tracking closure

The §6 negative result is specific to *cl as defined in §2* (pairs separated
by warm refinement). A different closure — `cl_prov`, operating at the
**provenance** level — likely *does* satisfy the matroid axioms.

**Sketch.** Strategy doc §10 ("closure as a guess") already prescribes a
`DERIVED`-record-with-driver structure for the linear oracle: each derived
relation carries a pointer back to the commit that drove it. Define:

> `cl_prov(S) =` set of pair-guesses `q ∈ E` such that `q` is *driver-
> determined* by `S` — i.e. there is a chain of `DERIVED` records from `S`'s
> commits to `q`, where each step is either a direct commit or a propagation
> step whose driver is in the chain so far.

This closure operates on **(commits + driver-traced derivations)**, not on
**(separated-pair-guesses)**. The crucial difference: when committing more
pairs "accidentally restores a symmetry" at the partition level (the M0
counterexample), the driver chain doesn't dissolve — the previously-driven
relation is still in `cl_prov(S)` because its driver chain is still valid.
Adding commits can only extend the driver graph, never retract it.

This is exactly the structural property that should give monotonicity (M0)
back. For CFI graphs the driver structure is `F_2`-linear (XOR of parities),
which directly gives binary-matroid representability and the Tier-2 detector
of §7.

**No-known-hidden-Johnson.** No graph construction is known that hides an
`A_k`-on-subsets factor; this remains real evidence (decades of looking) but
not proof. The reformulated conjecture is:

> **Conjecture (binary cl_prov).** For every graph `G`, the provenance
> closure `cl_prov_G` is a binary matroid.

If true: no hidden Johnson exists in the descent's output, and chain descent
with linear oracle is polynomial. If false: a counterexample is the first
known hidden-Johnson construction.

This is a target for the *future framework*, not a result of either it or
the current one.

---

## 9. Open work — the next attack

The §6 finding closes the current matroid framework. The natural next
moves, in rough order:

1. **Scope cl_prov rigorously.** Extend the refinement model in
   `ChainDescent.lean` with `DERIVED`-record provenance. Define `cl_prov`.
   Test M0–M3 on it. This is the biggest single workitem — the current
   `refineStep` is opaque (axiomatised via `refineStep_iff` only), and
   provenance requires opening that up.
2. **Pivot to a different Tier-2 attack route** if cl_prov turns out to
   need substantial new modelling. Options:
   - **Linear oracle implementation**: build the `Z₂` Gaussian-elimination
     oracle for CFI-style decisions; the matroid structure of the linear
     oracle's output is itself the binary-matroid we want to classify.
   - **Hidden-Johnson Piece C**: complete the cascade-half of the
     near-theorem in `docs/chain-descent-hidden-johnson.md` (visible
     Johnson is Tier-1). Doesn't address encoded Johnson but is solid
     finite progress.
   - **k-WL widening**: bound how much `k`-WL refinement widens Tier-1;
     known to absorb visible Johnson schemes.
3. **Local-rule universality lemma** (§4) — moderate-size Lean lemma,
   still useful regardless of the matroid framework, since it characterises
   *what* warm refinement does at each step.

Items 4–6 of the original §9 (Algorithm 2 composition, binary-closure
conjecture, C# Algorithm 1 probe) are conditional on the matroid framework
working as defined and are deferred until either cl_prov is built or a
different framing is adopted.

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
  failure record). The framework as defined is structurally dead.

What this session did NOT settle:
- Whether `cl_prov` (provenance-tracking closure, §8) recovers the matroid
  axioms — the proposed pivot.
- Whether the binary-`cl_prov` conjecture holds for graphs the descent
  produces.
- Whether Algorithm 2's composition lemma holds in the non-binary case.
- Whether `c < k - 1` (World B) ever genuinely occurs at the *closure
  circuit* level (the direct-rule level it clearly does).

The natural next action is **scoping `cl_prov`** (§9 item 1) — or pivoting
to one of the other Tier-2 attack routes (§9 item 2).
