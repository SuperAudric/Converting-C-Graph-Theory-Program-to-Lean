# Layered Tiebreak with Supplant

A graph canonization algorithm that aims for polynomial time on inputs where
2-WL refinement is orbit-complete on every class it ties. It records each
tiebreak choice in a separate rank dimension; reconciliation between different
choice sequences happens after the fact via a marker-sort step ("supplant"),
not by enumerating choice sequences. The design has a known failure mode
(documented in §8) where a single marker bundles two independent symmetry
choices and the supplant cannot decouple them.

This document is self-contained. The earlier `tiebreak-tuples-strategy.md`
captures the same data structures from a different angle and proposed an L!
canonical-relabeling step; this document refines that step into an O(L log L)
sort under an explicit cascade-independence assumption, and pins down where the
assumption breaks.

---

## 1. Problem

**Canonical labeling.** Given an undirected graph G, produce a byte string
canon(G) such that:
  - Iso: G ≅ H ⇒ canon(G) = canon(H)
  - Non-iso: G ≇ H ⇒ canon(G) ≠ canon(H)

A canonical labeling is harder than just deciding isomorphism — you have to
produce the same labeled graph for every input scrambling.

**Why it's hard.** Refinement-based discriminators (color refinement, k-WL)
reach a fixed point in which non-equivalent vertices may share the same color.
Any further progress needs to *break* a tie — pick one vertex over another —
and that choice is not in general invariant under input relabeling. Three
families of solutions:

1. **Greedy commit.** Pick "first array index"; update the rank in place. Fast,
   not canonical: scramblings produce different bytes when the tied class
   isn't a true automorphism orbit.
2. **Branch and prune (nauty/bliss/traces).** Try every choice; for each,
   individualize, refine, compare leaf labelings; lex-min over leaves.
   Provably canonical, exponential worst case.
3. **Layered tiebreak with supplant (this design).** Record each choice in a
   *separate rank dimension*. Reconcile different choice sequences by sorting
   the dimensions at the end. Polynomial when cascades are independent;
   reduces to (2) in worst case otherwise.

The 2-WL discriminator at the core (sort-based pair-rank refinement, see
`CanonGraphOrdererTwoWL.cs`) is unchanged. Everything in this document is the
machinery around it.

---

## 2. Rank tuples

Every vertex carries a tuple

```
rankTuple(v) = (r₀, role₁, role₂, …, role_L)
```

with a parallel reached-flag per layer ≥ 1:

```
reachedByLayer_k(v) = true iff v's role at layer k changed from its
                      initial 0 due to layer k's cascade
```

  - **r₀** is the structural 2-WL rank computed before any tiebreaking.
    Frozen for the life of the run.
  - **role_k** is v's dense-rank role *within v's prior-tuple class*
    (vertices sharing r₀, role₁, …, role_{k-1}) after round k's cascade.
    Frozen once round k completes.
  - **L** is the number of completed tiebreak rounds.

The reached flag distinguishes "vertex was untouched at layer k" from "vertex
got role 0 (lowest) at layer k". This matters in §3.

The lexicographic comparison on tuples is layer-by-layer; at each layer,
*untouched dominates*: untouched_k < any reached value at layer k. This is
how a vertex outside the cascade's reach sorts before vertices the cascade
reordered.

This is the only state the algorithm carries — no automorphism group, no
search tree, no history vectors.

---

## 3. Discriminate (2-WL over tuples)

Sort-based 2-WL pair-rank refinement, identical in structure to the
existing implementation, with two adaptations:

  - The initial pair signature for cell (u, v) leads with the *full* rank
    tuples of u and v (instead of single integers).
  - The vertex-rank update writes only to position L (the latest layer);
    positions 0..L-1 are frozen.

The strict-refinement invariant — previous rank as the lead component of
every signature — extends to tuples: if `rankTuple(x) < rankTuple(y)` at any
step, the relation persists across subsequent Discriminate calls.

When called with L = 0 (the very first Discriminate), it writes to position 0
and produces r₀.

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
        pick any vertex w in that class                      // see §5
        rankTuple(w)[L] ← 1
        reachedByLayer_L(w) ← true
        Discriminate                              // refines layer L globally
        for every v whose role_L just changed:
            reachedByLayer_L(v) ← true
```

Each event:
  - marks one vertex with role 1
  - runs one Discriminate to cascade
  - flips the reached flag for everyone the cascade visibly touched

Multiple events in the same round share the same layer index L. The
strict-refinement invariant keeps marked vertices at role 1; cascade fans
non-marked vertices in the same prior class into role 2, 3, …; vertices the
cascade doesn't reach stay at role 0 with reachedByLayer_L = false.

---

## 5. Target selection

The within-round inner loop picks "any vertex" from the smallest tied unreached
class. The choice is structurally arbitrary *if and only if* the class is a
true automorphism orbit. Two regimes:

  - **True-orbit class (the easy case).** Every choice yields an
    automorphism-equivalent cascade. Different scramblings produce tuples that
    differ only in *which marker label sits at which layer position*.
    The supplant of §6 reconciles them.

  - **Non-orbit tied class (the hard case).** 2-WL ties two vertices that
    aren't actually automorphic. Different choices yield structurally
    different cascades — different role-multisets, not just different marker
    labels. No marker sort can reconcile them. This is the §8 failure mode.

Discriminating these two cases without forking is itself the hard problem
nauty solves. This algorithm handles the first cleanly and exposes a clean
trigger condition for backtracking when the second case bites.

---

## 6. Supplant: marker sort instead of L! enumeration

The earlier `tiebreak-tuples-strategy.md` proposed canonical relabeling by
enumerating all L! permutations of layer positions and taking the lex-min.
That's correct but exponential.

The supplant insight: when the cascades produced by the L events are
**cascade-independent** — meaning the multiset of role values written by
event i does not depend on the order in which events are interleaved with
event j — the canonical permutation is determined by *sorting the markers*,
not searching them.

Concretely, each event has a canonical signature:

```
sig(event_k) = (sorted multiset of role values it wrote
                across vertices it directly touched)
```

If events are cascade-independent, then:

  - Different scramblings produce the same multiset of (event signature)
    values, just in different layer positions.
  - Sorting events by signature lex order gives a deterministic canonical
    layer ordering.
  - Apply that ordering to the layer indices of every tuple.

Cost: O(L log L) comparisons over O(n)-sized signatures, instead of L!.

```
Supplant:
    for each layer k = 1..L: compute sig(event_k)
    sort layers by sig lex order            // canonical permutation π
    apply π to every tuple's positions 1..L (r₀ stays in position 0)
```

**Cascade-independence is the load-bearing assumption.** §7 walks through a
case where it holds; §8 walks through one where it doesn't.

---

## 7. Worked example: disjoint CFI even ⊔ odd

Consider G = CFI(K4)_even ⊔ CFI(K4)_odd: two CFI graphs on the K4 base, of
opposite parity, joined by a disjoint union (no edges between them).
2-WL cannot distinguish CFI_even from CFI_odd (CFI graphs are designed for
this; K4 has treewidth 3, beyond 2-WL's strength).

**Initial state.** r₀ ties every vertex (no degree distinction; 2-WL stalls
in one big class).

**Round 1.**
  - Event 1: pick first vertex v₁ (say in the even half). Mark
    `rankTuple(v₁)[1] = 1`. Discriminate.
    - Inside the even half, the cascade fans into roles {1, 2, 3, …}
      according to 2-WL distance from v₁.
    - The odd half is disjoint — no path from any odd-half vertex to v₁.
      Their pair colors with v₁ are uniform (all "non-adjacent"); their
      role_1 stays 0; reachedByLayer_1 stays false for them.
  - Event 2: smallest tuple-tied unreached class is now the entire odd half.
    Pick first unreached vertex v₂ (in the odd half). Mark, Discriminate.
    - Cascade fans the odd half into roles {1, 2, 3, …}.
    - Even half is already reached and at non-zero roles; this event doesn't
      perturb them (their pair colors with v₂ are uniform).
  - End of round 1: every vertex has been reached.

**Subsequent rounds.** If 2-WL+IR is orbit-complete within each half (which
holds for CFI on small bases like K4 — the within-CFI(G) automorphism group
acts transitively on each 2-WL color class), residual ties within each half
are orbit ties and get broken by further rounds with structurally arbitrary
picks. Each within-half cascade stays inside its half.

**Cascade-independence.** Event 1 wrote to even-half vertices only; event 2
wrote to odd-half vertices only. Their role multisets are disjoint by
support. Swapping the layer positions (event 2 in layer 1, event 1 in layer 2)
gives a tuple list that, sorted, is identical to the original (modulo the
swap). Supplant reduces the L! search to a 2-element marker sort.

**Canonical output.** The smaller of (event 1's signature, event 2's
signature) under lex order gets layer position 1. If CFI_even and CFI_odd
have distinguishable cascade signatures (which is the *structural* difference
between even and odd CFI — not the within-half vertex coloring 2-WL fails on,
but the multiset of roles produced by individualizing into one), the supplant
deterministically places "even-half marker" before "odd-half marker" (or vice
versa) and the two scramblings produce the same canonical bytes.

This is the regime the design is built for. The algorithm runs in time
O(L · 2-WL-cost) = O(n · n⁴) = O(n⁵) on inputs in this regime.

---

## 8. Known failure case: the bipartite-interconnected double cover

Construct G as follows:
  - Take H = CFI(K4)_even ⋈ CFI(K4)_odd, where ⋈ denotes the *complete
    bipartite* connection between every vertex of CFI_even and every vertex
    of CFI_odd.
  - Then take the disjoint union of two isomorphic copies of H:
    G = H ⊔ H.

G has four classes of vertex: (copy 1, even side), (copy 1, odd side),
(copy 2, even side), (copy 2, odd side). 2-WL ties all four classes if
CFI_even and CFI_odd have matching internal degree distributions.

**Why supplant breaks.** Round 1 event 1 picks "any vertex" from the universal
tied class. The chosen vertex v lies in some specific (copy, side). Four
qualitatively different outcomes:

  - v ∈ (copy 1, even): cascade reaches all of copy 1; copy 2 untouched.
    The marker carries "copy 1, even" semantics.
  - v ∈ (copy 1, odd): cascade reaches all of copy 1; copy 2 untouched.
    The marker carries "copy 1, odd" semantics.
  - v ∈ (copy 2, even): symmetric to first via copy swap.
  - v ∈ (copy 2, odd): symmetric to second via copy swap.

Two distinct symmetries are bundled into a single marker:
  - **Copy symmetry** (copy 1 ↔ copy 2) is a true automorphism orbit; supplant
    can swap it.
  - **Side symmetry** (even ↔ odd within a copy) is *not* an orbit — CFI_even
    and CFI_odd are non-isomorphic graphs. Supplant can't swap it.

If scrambling A picks v ∈ (copy 1, even) and scrambling B picks
v ∈ (copy 1, odd), the two cascades produce structurally different role
multisets within copy 1. The supplant has only one swap to spend on the
discrepancy, but two-dimensional ambiguity to resolve. Result: different
canonical bytes for the same graph.

**The deeper diagnosis.** The supplant is a marker-sort, which is
information-theoretically equivalent to "the marker's identity captures
exactly one piece of choice-information." When a tied class encodes two
independent choices (like (copy, side) here), one marker is one piece of
information short.

**This is the wall.** Detecting that a tied class encodes multiple choices
is a form of the orbit-membership decision problem, which is
GI-hard in general. So the algorithm's polynomial-time claim is not
universal — it's polynomial on inputs where every refinement state's tied
classes are true orbits, and incorrect (silently) on inputs where they
aren't.

**Other constructions in the same equivalence class.** Replacing the
complete bipartite ⋈ with any "uniform attachment" between halves seems to
produce the same failure. For instance, attaching every vertex of CFI_even
and CFI_odd to a single shared central vertex (via a star) bundles the same
two-symmetries-into-one-marker pattern.

---

## 9. Mitigation: detect-and-fall-back

The algorithm should not silently produce wrong bytes. Two detection
strategies:

1. **Multi-π lex-min tie.** After supplant, check whether the marker sort
   resolved every layer ordering deterministically (no ties in event
   signatures). If the sort tied two markers but the resulting tuple
   multisets *also* tie under both orderings, the algorithm is in the §8
   regime and should fall back to enumeration over the offending markers.

2. **Round-1 multi-choice probe.** When the universal tied class is too
   broad to be plausibly a single orbit (e.g., size > some threshold of
   total vertices, or before any structural information has been
   discriminated), pre-emptively run round 1 from multiple starting
   choices and compare. If choices in the same tied class produce
   non-isomorphic cascade signatures, the class isn't an orbit; fall back.

Either path reintroduces L! worst-case cost when triggered, but keeps the
fast path fast on inputs that don't need it. The per-round detection check
is itself polynomial.

---

## 10. Open questions

  1. **Cascade-independence as a checkable property.** Is there a polynomial
     local test that confirms two events' cascades commute, short of
     re-running both orderings? Affine answer would make detect-and-fall-back
     deterministic instead of probabilistic.

  2. **Touched-flag semantics under bipartite cascades.** In disjoint
     constructions the reached flag cleanly separates "in the cascade's
     component" from "outside it." In bipartite-interconnected
     constructions the dense-rank update can flip role values for vertices
     the cascade did not structurally reach, just because their relative
     rank within the prior class shifts. The flag then conflates
     "structurally touched" with "rank-rewritten." A cleaner formulation
     might tie reached-status to "the vertex's pair colors involve a
     marked vertex within distance D," but that re-parameterizes by
     discriminator strength.

  3. **Within-component orbit-completeness for CFI.** The §7 example assumes
     2-WL is orbit-complete on a single CFI(K4)_even instance. This is
     plausible for CFI on small bases but not proven in this project. The
     `CfiPair_DisjointUnion_DifferentScramblings_ProduceSameCanonical`
     test on Cycle3/5/7 and K4 bases (currently failing under the older
     algorithm — see git log for context) is the natural empirical probe.

  4. **Strict-refinement invariant under reached-domination.** The "untouched
     dominates" comparison rule needs to be the lead component of every
     Discriminate signature for the strict-refinement invariant to hold.
     Worth verifying before relying on the invariant in correctness
     arguments.

---

## 11. Where this design sits

  - **Strictly more powerful than greedy 2-WL+individualization on iso
    detection** when cascades are independent: σ-invariance holds in the
    §7 regime; greedy commit fails σ-invariance on the same inputs because
    its single in-place rank update can't represent "the choice was
    arbitrary."

  - **Equivalent to nauty in worst case** under the §9 fallback: enumeration
    over offending markers re-introduces the branching nauty does
    natively.

  - **Not a polynomial-time canonizer for arbitrary graphs.** The §8
    failure case is a clean falsifier of the unconditional polynomial
    claim. The algorithm is polynomial *on a class of graphs* — those
    whose every reachable tied class is a true orbit — and the recognition
    problem for that class is itself (a form of) the GI problem.

The interesting engineering bet is that real-world inputs mostly fall in
the easy class, and detect-and-fall-back keeps the design correct on the
rest at a cost that scales with how adversarial the input is.
