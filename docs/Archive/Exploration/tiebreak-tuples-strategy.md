# Tiebreak-Tuple Rank Strategy

A graph canonization algorithm in the same equivalence-class-strength
territory as nauty/bliss/traces, built without their explicit
branch-and-prune search tree. Tiebreak choices are recorded in separate
rank layers rather than committed to the structural rank; a final
canonical-relabeling step reconciles different choices into a single
canonical output. Where nauty pays exponential cost in tree branching,
this design pays it in canonical-relabeling — same complexity class,
different shape.

The discriminator (sort-based 2-WL) is unchanged from
`CanonGraphOrdererTwoWL.cs`. The tiebreak/rank/comparison machinery
around it is new.

---

## 1. Problem and approach

**Goal.** Deterministic canonical labeling. Two isomorphic inputs
produce identical canonical bytes; two non-isomorphic inputs produce
different bytes.

**The fundamental obstacle.** Refinement-based discriminators (any level
of the WL hierarchy) reach a fixed point at which non-equivalent
vertices may share a type. Canonization requires breaking those ties,
which forces a choice not invariant under input relabeling. Three
families of solutions exist:

  - **Greedy commit.** Pick "first-array-index"; commit to the structural
    rank. Fast, not canonical — different scramblings produce different
    bytes when the tied class isn't a true automorphism orbit.
  - **Branch and prune (nauty).** Try every choice; for each,
    individualize, refine, compare leaf labelings; lex-min. Provably
    canonical, exponential worst case.
  - **Layered ranks (this document).** Record each choice in a *separate
    rank layer*. Reconcile different choice sequences after the fact via
    a canonical layer permutation. Same canonical guarantee on inputs
    where the discriminator separates orbits; same exponential worst
    case on inputs where it doesn't (the L! permutation cost matches
    nauty's branching cost).

The third option's distinguishing claim is *deferred backtracking*: a
provisional tiebreak choice can be supplanted by structural information
that emerges in later refinement rounds, without re-running anything,
because the choice's effects live in their own rank dimension.

---

## 2. Rank tuples

A vertex's rank is

```
rankTuple(v) = (r₀, role₁, role₂, …, role_L)
```

with a parallel boolean per layer

```
reachedByLayer_k(v) = true iff v's role at layer k was set by a cascade
                      (rather than left at the untouched default)
```

  - **r₀** is the 2-WL structural rank computed before any tiebreaking.
    Frozen for the lifetime of a run.
  - **role_k** is v's dense-rank role in the cascade triggered by
    round k's tiebreak. Frozen once round k completes.
  - **L** is the number of completed tiebreak rounds.

The reached flag is what distinguishes "untouched at layer k" from
"reached, with role 0". It dominates role values in the per-tuple
comparison (untouched < any reached value), which keeps role 0
available as a legitimate dense rank.

This is the *only* state the algorithm carries. There are no per-vertex
event identifiers, no separate history vectors, no automorphism group
representation — all of those are derivable from the layered tuple plus
the canonical-relabeling step of §6.

---

## 3. Discriminate

Sort-based 2-WL pair-rank refinement, identical to the existing
TwoWL implementation except:

  - The initial pair signature for cell (u, v) leads with the *full*
    rank tuples of u and v.
  - The vertex update writes only to position L (the latest layer);
    positions 0..L-1 are frozen.

The strict-refinement invariant of the existing TwoWL — previous rank
as the lead component of every signature — extends to tuples: if
`rankTuple(x) < rankTuple(y)` at any step, the relation persists across
subsequent Discriminate calls.

When L = 0 (the initial call before any tiebreak), Discriminate writes
to position 0 — i.e. it computes r₀.

---

## 4. Tiebreak round

A round adds one layer to every tuple and runs one or more *events* to
fill it.

```
TiebreakRound:
  L ← L + 1
  for each v: append role_L = 0; reachedByLayer_L(v) = false
  loop:
    find the smallest tuple-tied class (by current full tuple)
        among vertices with reachedByLayer_L(v) = false
    if no such class with size > 1: break
    pick any vertex w in that class                          // see §5
    rankTuple(w)[L] ← 1
    reachedByLayer_L(w) ← true
    Discriminate                            // refines layer L globally
    for every v whose role_L just changed: reachedByLayer_L(v) ← true
```

Each event marks its target with role 1. The strict-refinement invariant
keeps prior-marked targets at the lead of the dense rank; new marks land
at role 1 by construction; non-target vertices in the cascade fan into
role 2, 3, …; vertices the cascade doesn't reach stay at role 0 with
reachedByLayer_L = false. This is the formal expression of "promote into
the same class": multiple events in the same round share the layer and
their targets share role 1.

In the disjoint-CFI canonical example: round 1 event 1 picks a vertex
in (say) Even, fans Even into roles 1..k_E, leaves Odd untouched.
Round 1 event 2 picks a vertex in Odd, fans Odd into roles 1..k_O.
Both targets share role 1; structurally equivalent vertices in the
two halves end up at matching roles. After this round, every vertex
has been reached and the layer is fully filled.

---

## 5. Target selection

The within-round inner loop picks "any vertex" from the smallest tied
class. The choice is structurally arbitrary *if and only if* the class
is a true automorphism orbit. Two regimes:

  - **True-orbit classes (the easy case).** Every choice yields an
    equivalent cascade. Whatever rule the implementation uses
    (first-array-index is fine), different scramblings produce tuples
    that differ only in *which layer index holds which role*.
    The canonical-relabeling step of §6 reconciles them.

  - **Non-orbit tied classes (the hard case).** 2-WL ties two vertices
    that are not actually automorphic. Different choices yield
    structurally different cascades, so the resulting tuples differ in
    a way that no layer permutation can reconcile. This is precisely
    the case nauty handles with backtracking; this design needs an
    explicit fallback (§9).

Discriminating these two cases without forking is itself the hard
problem nauty solves. This algorithm handles the first case cleanly,
matches 2-WL+individualization strength on the second, and exposes a
clean integration point for backtracking when more is needed.

---

## 6. Canonical relabeling

After the outer loop terminates, every vertex has a tuple of length
1 + L. Two scramblings of the same graph that picked different
first-targets will have produced different layer assignments — but if
the tied classes were true orbits, the tuple multisets across the two
scramblings differ only by a *permutation of layer positions 1..L*.

The canonical-relabeling step finds the permutation π ∈ S_L of layer
positions that minimizes the lex order of the global sorted tuple list,
then applies it.

```
CanonicalRelabel:
  for each π ∈ S_L:
    apply π to layer positions of every tuple (r₀ stays in position 0)
    sort tuples lex (with reached-flag dominance per layer)
    record the resulting bytes as the candidate canonical
  pick the π yielding the lex-smallest candidate
```

Two scramblings of the same graph reach the same lex-smallest under their
respective π's, so they produce the same canonical bytes.

Naively the search is L! candidates — exponential in the number of
tiebreak layers, which is the same complexity class as nauty's
branching. In practice the search prunes hard:

  - Any π under which two layers' role-multisets are equal can be
    treated as equivalent (those layers commute under sort).
  - Layers can be sorted by their role-multiset signatures; π is
    constrained to permutations consistent with the signature order.
  - The search can be pruned the moment its prefix exceeds the
    current best lex order.

---

## 7. Output

```
PermuteByCanonicalRanks:
  apply the canonical π found in §6
  sort vertices by full tuple (reached-flag dominant per layer)
  emit the adjacency matrix permuted to that vertex order
```

Identical to the existing `PermuteByDenseRanks` modulo reading from
tuples and applying π.

---

## 8. Outer loop and termination

```
Discriminate                           // computes r₀, L = 0
while ties remain in the current tuples:
    TiebreakRound                      // extends to L+1, fills it
return PermuteByCanonicalRanks
```

Each TiebreakRound strictly refines the partition: the round's first
event splits at least one tied class. The number of rounds is bounded
by n − (number of distinct r₀ classes), so termination is in O(n)
rounds.

---

## 9. Where this design stops being nauty-comparable

The algorithm is provably canonical on graphs whose tied classes are
true automorphism orbits at every refinement step. CFI graphs at the
2-WL strength level are *not* such graphs — their non-orbit ties are
the entire point of the construction.

Two integration points for handling the hard case:

  - **Strengthen the discriminator.** k-WL with k > 2 separates more
    orbits. Each step up the WL hierarchy costs an O(n) factor in
    refinement state. Bounded benefit — for any fixed k, CFI-(k+1)
    defeats k-WL.

  - **Backtracking as a fallback.** When the canonical-relabeling step
    finds *multiple* π's tied at the lex-smallest candidate, the
    algorithm has detected that the ambiguity isn't reducible by layer
    permutation. At that point, it can fork: re-run from a snapshot
    with a different target choice within an offending class, compare
    results, lex-min. This is nauty in miniature, invoked only when
    needed.

The design deliberately keeps the fast path fast and isolates the slow
path to a single, well-defined trigger condition. Most real-world
graphs hit only the fast path.

---

## 10. Comparison to nauty

| Concern | Nauty | This design |
|---|---|---|
| Discrimination | k-WL color refinement | Sort-based 2-WL (same equivalence) |
| Tiebreak commitment | Mutate the structural rank | Append a layer; r₀ unchanged |
| Choice exploration | Branch over every candidate | Pick one; defer reconciliation |
| Reconciliation | Lex-min over leaves of search tree | Lex-min over permutations of layers |
| Worst-case cost | O(branching!) leaves | O(L!) layer permutations |
| Automorphism pruning | Explicit (orbit pruning) | Implicit (equivalent layers commute) |
| Hard-case fallback | Inherent to the design | Optional, opt-in (§9) |

The two designs encode the same information; nauty puts the choices in
the search tree and the structure in each leaf, this design puts the
choices in rank layers and the structure in the (permuted) tuple list.
Conversion between the two views is straightforward, which is what
makes the §9 fallback clean to bolt on.

---

## 11. Implementation strategy

Three milestones, each independently testable:

1. **Layered tuples + canonical relabeling.** Replace the scalar
   `ranks[]` with `int[][] rankTuples` and `bool[][] reachedByLayer`.
   Implement Discriminate over tuples, TiebreakRound, CanonicalRelabel
   (brute-force L! is fine to start), and the new PermuteByCanonicalRanks.
   This delivers scrambling-invariance on `CfiPair_DisjointUnion_-`
   `DifferentScramplings_ProduceSameCanonical` for K33 and equivalent
   on the existing TwoWL test surface.

2. **Pruned canonical relabeling.** Replace brute-force L! with the
   signature-sorted + prefix-pruned search of §6. Buys back orders of
   magnitude on inputs with many tiebreak rounds.

3. **Backtracking fallback.** Detect multi-π lex-smallest ties; fork
   on offending class; combine results. This is the bridge to full
   nauty-equivalent power for crafted-hard CFI inputs.

Milestones 1 and 2 stay within the existing project's current
performance envelope. Milestone 3 introduces nauty-style worst-case
behavior, gated on inputs that need it.

---

## 12. Open questions

  - **Reached-flag interaction with strict refinement.** The combined
    comparator (untouched dominates, then role) needs to be the lead
    of every Discriminate signature for the strict-refinement
    invariant to hold over reached-or-not. Worth verifying before
    relying on the invariant in correctness arguments.

  - **Canonical relabeling as a partial function.** When two layers
    have identical role-multisets, the layer permutation between them
    is an automorphism of the rank structure — equivalent under sort.
    The search can treat them as a single layer; whether this needs
    to be made explicit in the data structure depends on how often it
    happens on real inputs.

  - **Cost of milestone 1 on already-passing tests.** Tuples grow with
    L; signature size in Discriminate goes from O(1) to O(L). Existing
    small-input tests have L bounded by ≤ n, so the wall-clock cost
    should be a constant factor. Worth measuring on the current test
    suite before milestone 2.
