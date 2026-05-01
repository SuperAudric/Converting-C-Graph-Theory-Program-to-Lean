# Layered Tiebreak with Supplant

A graph canonization algorithm that aims for polynomial time on inputs where
2-WL refinement, augmented with pair-individualization, is orbit-complete on
every class it ties. Each tiebreak event individualizes a *pair* (A, B) with
roles low/high — a binary, invertible commitment. Reconciliation between
different scramblings happens after all events run, via a multi-pass
canonicalization ("supplant") that resolves the flip dimension by Z/2 inverse
on role labels, the atom-multiset dimension by forced completion, and the
layer-position dimension by structural sort.

This design supersedes earlier drafts that individualized a single vertex per
event. The single-vertex scheme had a known failure (§8 of those drafts: two
independent symmetry choices bundled into one marker, supplant unable to
decouple them). The pair-event scheme splits each commitment into two
separable axes — *which pair* (resolved by atom canonicalization under the
structured assumption) and *which flip direction* (resolved by Z/2 inverse on
the role labels), eliminating that failure on inputs that satisfy the
structured assumption (§8 below). The earlier `tiebreak-tuples-strategy.md`
captured a related set of data structures from a different angle.

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
Any further progress needs to *break* a tie, and that choice is not in general
invariant under input relabeling. Three families of solutions:

1. **Greedy commit.** Pick "first array index"; update the rank in place. Fast,
   not canonical: scramblings produce different bytes when the tied class
   isn't a true automorphism orbit.
2. **Branch and prune (nauty/bliss/traces).** Try every choice; for each,
   individualize, refine, compare leaf labelings; lex-min over leaves.
   Provably canonical, exponential worst case.
3. **Layered tiebreak with supplant (this design).** Record each choice in a
   *separate rank dimension*; restrict choices to pair-promotions whose two
   axes are separately invertible. Reconcile different choice sequences by
   sorting the dimensions at the end. Polynomial on the structured class;
   reduces to (2) in worst case otherwise.

The 2-WL discriminator at the core (sort-based pair-rank refinement, see
`CanonGraphOrdererTwoWL.cs`) is unchanged. Everything in this document is the
machinery around it.

---

## 2. Pair-tagged rank tuples

Every vertex carries a tuple

```
rankTuple(v) = (r₀, role₁, role₂, …, role_L)
```

  - **r₀** is the structural 2-WL rank computed before any tiebreaking.
    Frozen for the life of the run.
  - **role_k** is one of `{untouched, cascaded(d), low, high}`, where
    `cascaded(d)` is the dense-rank role within v's prior-tuple class
    determined by event k's cascade. Frozen once event k completes.
  - **L** is the number of completed events. Each event consumes exactly one
    layer; there is no separate notion of "round" in this version.

**Lex order on role values:** `untouched < cascaded(0) < cascaded(1) < … < low < high`.
The three ideas this encodes:
  - *Untouched dominates* — a vertex outside the cascade's reach sorts before
    vertices the cascade reordered. Same as in the single-vertex scheme.
  - *Cascaded sorts before tagged* — vertices the cascade pulled into a
    finer rank class sort before the explicitly tagged pair members.
  - *low and high are adjacent* — the flip swap is a Z/2 involution that
    moves only A and B's role values, never any cascaded vertex's value.
    This is the key property that makes flip-canonicalization local to the
    tagged pair (§6.3).

This is the only state the algorithm carries — no automorphism group, no
search tree, no history vectors.

---

## 3. Discriminate (2-WL over tuples)

Sort-based 2-WL pair-rank refinement, identical in structure to the existing
implementation, with two adaptations:

  - The initial pair signature for cell (u, v) leads with the *full* rank
    tuples of u and v (instead of single integers).
  - The vertex-rank update writes only to position L (the latest layer);
    positions 0..L-1 are frozen.

The strict-refinement invariant — previous rank as the lead component of every
signature — extends to tuples: if `rankTuple(x) < rankTuple(y)` at any step,
the relation persists across subsequent Discriminate calls. The integer
dense-rank consumed by 2-WL internally is invariant under the role-value
semantics (the dense-rank treats `(untouched, cascaded(d), low, high)` as
opaque distinct symbols).

When called with L = 0 (the very first Discriminate), it writes to position 0
and produces r₀.

---

## 4. Tiebreak event

```
Event:
    pick pair (A, B) from the current lowest tuple-tied class
    rankTuple(A)[L] ← low
    rankTuple(B)[L] ← high
    Discriminate
    for every v whose role_L moved off untouched as a result:
        v's role_L is one of low, high, cascaded(d)
        record reachedByLayer_L(v) = true
```

Pair selection within the class follows a deterministic rule (e.g., the two
smallest original indices). The flip-canonicalization in §6 neutralizes the
"who is low, who is high" choice under input scrambling; the
atom-canonicalization in §6 neutralizes the "which pair within the orbit"
choice when the class is a single orbit.

L increments by 1 after each event.

---

## 5. Target selection

The pick rule "lowest tuple-tied class, two smallest indices" is structurally
arbitrary if and only if the chosen pair belongs to a single
automorphism orbit-pair. Three regimes:

  - **Within-orbit pair.** Both A and B in the same automorphism orbit.
    Different scramblings produce automorphism-equivalent cascades that
    differ only in flip direction. §6.3 reconciles via Z/2 inverse on the
    pair's role labels.

  - **Cross-orbit pair, structured neighborhood.** A and B are in different
    orbits, but the tied class is "structured" — every internal vertex is
    eventually distinguishable by 2-WL plus enough pair-individualizations.
    Different scramblings collect the same multiset of cascade footprints
    ("atoms"), possibly in different orders and via different specific pair
    picks; §6 canonicalizes the multiset.

  - **Non-structured tied class.** 2-WL plus pair-individualization stalls
    inside some sub-orbit even after exhausting forced completion. The atom
    multiset itself differs across scramblings. §10 detect-and-fall-back is
    required.

The structured assumption — every reachable tied class either is a true orbit
or is structured in the second sense — is the load-bearing premise. §9
formalizes it as a recursive property.

---

## 6. Supplant: layered canonicalization with forced completion

The earlier draft's supplant was a single sort by event signature, sufficient
for §7 (disjoint-component case) but defeated by §8 (bipartite-interconnected
case). Pair-tag events admit a richer canonicalization with three components:
forced completion (6.1), atom classification (6.2), and a multi-pass sort
with flip-canonicalization (6.3).

### 6.1 Forced completion

Different scramblings can complete the algorithm with different layer counts,
because some atoms are *optional* — their information is derivable from a
finer-grained subset that already ran in the same sequence. For
canonicalization to compare scramblings byte-for-byte, every run must
terminate with the same atom multiset.

The forced-completion pass: do not exit when Discriminate first reaches all
singletons. Instead, keep running events until every structurally distinct
candidate pair (A, B) — defined as every distinct 2-WL pair-rank class within
the *original* lowest tuple-tied class at its time of selection — has been
spent as an event. Events whose atom is derivable from prior atoms (their
cascade adds no new information) are still run; they are simply tagged
"redundant" in their atom classification and contribute trivially to the
canonical bytes.

The result: a fixed-cardinality canonical atom multiset across scramblings,
provided the structured assumption holds. The cost upper bound is
O(p · 2-WL-cost) where p is the total count of structurally distinct pairs
visited across all events; on §8-class inputs p is O(n²) in the worst case
(see §11.5).

A simpler post-hoc rebuild — drop redundant events from the log after the
fact instead of running them — gives the same canonical output but is harder
to reason about under the recursive argument in §9, so this design favors
forced completion as primary.

### 6.2 Atom classification

Each completed event is classified by the structural footprint of its
cascade:

```
atomType(event_k) = (
    structural-class of (A, B)'s pre-event tuple-tied class,
    set of other tuple-tied classes the cascade visibly altered,
    within-pair 2-WL pair-rank of (A, B)
)
```

For §8, atoms fall into three types:
  - **within-class** — cascade refines the source class internally, leaves
    other classes' vertex-by-vertex roles at untouched.
  - **cross-class-same-component** — cascade reorders two classes that share
    edges within a connected component.
  - **cross-component** — cascade orders two classes that lie in disjoint
    components.

Each event's atom signature is the type plus a sorted multiset of the
`(low, high, cascaded(d))` role values it wrote, projected per affected
class. Atom signatures are richer than the single-event signatures of the
prior draft, and admit a nested canonical comparison.

### 6.3 Multi-pass sort with flip-canonicalization

Atoms canonicalize from outer (most globally structural) to inner (most
locally structural), with each pass consuming the previous pass's output to
break its own ties:

```
Supplant:
    classify every event by atomType(event_k)
    π ← identity                                           // canonical layer permutation

    for pass in [cross-component, cross-class-same-component, within-class]:
        events_in_pass ← {k : atomType(k) belongs to pass}
        for each event k in events_in_pass:
            cmpKey(k) ← lex-min over { sig(k), sig(k) under flip(low ↔ high) }
        sort events_in_pass by (cmpKey, prior-pass coordinates of (A, B))
        extend π with these events' canonical positions

    apply π to every tuple's positions 1..L (r₀ stays in position 0)
    for each event whose flip-canonicalization chose the flipped column:
        swap low ↔ high in that layer's column across every vertex
```

The "prior-pass coordinates" of a pair (A, B): once an outer pass has
committed canonical layer indices for atoms of its type, every vertex
inherits a canonical class-coordinate (e.g., "copy 1" or "copy 2" for §8
after the cross-component pass canonicalizes). Inner passes use these
coordinates to disambiguate ties between events whose own signatures
match.

**Flip-canonicalization is layer-local.** Swapping low ↔ high within layer
k's column changes A's and B's ranks but does not change the partition
2-WL sees at any subsequent layer (the same vertices remain in the same
equivalence classes; only the integer rank labels shift). Therefore each
layer's flip choice is independent of every other layer's, and the
per-layer lex-min is a global lex-min. This is the property single-vertex
individualization lacked.

Cost: O(L · log L · n) per pass; passes are bounded by the depth of the
structural decomposition (three for §8). Total supplant cost
O(passes · L · log L · n).

### 6.4 Why this works

  - **Flip dimension.** Flip is a Z/2 involution on role labels, partition-
    preserving by construction. Per-layer lex-min over flips is therefore
    optimal globally and computable in O(n) per layer.
  - **Atom-multiset dimension.** Forced completion guarantees the multiset
    of atoms is invariant across scramblings under the structured assumption.
    Different scramblings choose different specific pairs to instantiate
    each atom, but the multiset of (atomType, signature) values matches.
  - **Layer-order dimension.** The multi-pass sort canonicalizes layer
    positions deterministically from outer to inner, with ties at each pass
    broken by coordinates from the prior pass. Under the structured
    assumption, each pass either fully orders its events or ties only on
    iso-equivalent events (which canonicalize identically downstream).
  - **Cascade-dependence at intermediate states.** Different scramble orders
    produce different intermediate partitions. The supplant operates on the
    *final* augmented vertex labels, not on intermediate states; under the
    structured assumption, the final labels match across scramblings up to
    the layer permutation π and the per-layer flip, both of which supplant
    canonicalizes. So intermediate cascade-dependence does not affect
    correctness — only the run-time cost.

---

## 7. Worked example: disjoint CFI even ⊔ odd

Consider G = CFI(K4)_even ⊔ CFI(K4)_odd: two CFI graphs on the K4 base, of
opposite parity, joined by a disjoint union (no edges between them).
2-WL cannot distinguish CFI_even from CFI_odd internally; r₀ ties every
vertex.

**Atom inventory** (structured assumption: 2-WL plus within-CFI(K4)
pair-individualization reaches singletons inside each side):
  - 1 within-class atom per CFI side (assuming a single pair-individualization
    suffices to refine the side to singletons; in practice it may take more,
    each contributing one within-class atom).
  - 1 cross-component atom (orders even before odd or vice versa).

**Scrambling A and scrambling B** pick events in different orders. Forced
completion ensures each run accumulates the same atom multiset.

**Supplant:**
  1. Cross-component pass — one atom; flip-canonicalize → canonical bipartite
     order (CFI_even before CFI_odd if their canonical bytes lex-order that
     way, else reversed).
  2. Cross-class-same-component pass — empty in this construction.
  3. Within-class pass — two atoms with distinguishable signatures (one over
     CFI_even, one over CFI_odd because the two graphs are non-iso).
     Sort by signature; bipartite coordinate from pass 1 disambiguates if
     they ever tie.

Output identical across scramblings. Algorithm runs in
O((events) · 2-WL-cost) = O(n · n⁴) = O(n⁵).

---

## 8. The bipartite-interconnected double cover, under the new design

Construct G as in earlier drafts:
  - H = CFI(K4)_even ⋈ CFI(K4)_odd, where ⋈ is the complete bipartite
    connection between every CFI_even vertex and every CFI_odd vertex.
  - G = H ⊔ H.

G has four hidden orbits in its universal r₀-tied class:
{O1 = copy1-even, O2 = copy1-odd, O3 = copy2-even, O4 = copy2-odd}. The
single-vertex scheme failed here because one marker on (copy?, side?)
bundled two independent symmetry choices.

**Why pair-tag events behave better under ⋈.** A within-orbit pair
(A, B) ⊂ O1 has the property that every O2-vertex X is adjacent to *both*
A and B (⋈ is uniform). X's neighborhood multiset acquires exactly one
(low, edge) entry and exactly one (high, edge) entry under the new tags,
identical for every X ∈ O2. The cascade therefore does not split O2
internally, only bumps O2's class-rank as a unit. Same argument for O3, O4
relative to a within-O1 pair (no edges to copy 2 — they're untouched).
The pair-tag's effect is localized to "split O1 internally; bump O2's
class-rank as a unit; leave the disjoint copy alone."

**Atom inventory under forced completion:**
  - 4 within-class atoms (one per CFI(K4) instance):
      - 2 within-CFI_even (signatures equal — copy1-even and copy2-even are
        graph-isomorphic).
      - 2 within-CFI_odd (signatures equal).
  - 2 cross-class-same-component atoms (one per copy: orders the copy's
    even half against its odd half). Forced completion runs both even when
    they are derivable from the within-class atoms; redundant ones carry the
    "redundant" flag and contribute predictably to the canonical bytes.
  - 1 cross-component atom (orders copy 1 against copy 2).

**Multi-pass supplant:**
  1. Cross-component pass — one atom; flip-canonicalize → canonical copy
     order. Every vertex now has a canonical *copy* coordinate.
  2. Cross-class-same-component pass — two atoms with equal raw signatures
     (since copy 1 and copy 2 are iso). Disambiguate by copy coordinate
     from pass 1. Flip-canonicalize each. Every vertex now has a canonical
     (copy, side) coordinate.
  3. Within-class pass — four atoms in two tied-signature pairs. The two
     CFI_even atoms are tied in raw signature but disambiguated by their
     (copy, side) coordinate from passes 1–2. Same for CFI_odd. Flip-
     canonicalize each.

Output matches across scramblings. The previous failure case is closed,
*conditional on* the structured assumption (each CFI(K4) instance reaches
singletons under pair-individualization).

If the structured assumption fails — e.g., 2-WL plus pair-individualization
stalls inside a single CFI(K4) — then within-class atoms don't fully refine,
the (O1 vs O3) and (O2 vs O4) tied subclasses recur at a deeper level, and
§9's recursive argument either bottoms out (algorithm succeeds at greater
depth) or fails (§10 fall-back triggers).

---

## 9. Recursive singletons argument

The structured assumption can be cast recursively:

> *Claim.* If 2-WL plus pair-individualization can resolve any subgraph G[C]
> (the induced subgraph on tuple-tied class C, plus its boundary structure
> to the rest of G) into canonical singletons, then it can resolve the
> ordering of any pair (A, B) drawn from C against the rest of G.
>
> *Base case.* A 2-vertex subgraph trivially resolves: there are two
> labelings, related by the Z/2 flip, and supplant's flip-canonicalization
> selects the lex-min.
>
> *Inductive step.* Any larger structured subgraph admits a pair-event that
> splits some hidden sub-orbit, reducing the problem to canonicalizing two
> strictly smaller subgraphs (the split halves). Each half falls under the
> induction hypothesis.

The induction is conditional: at each level both halves must themselves be
structured for the next level to inherit it. The CFI ladder (CFI applied to
bases of growing treewidth) is the canonical falsifier — each rung needs
strictly more discriminator strength than the last, so the recursion does
not bottom out at any fixed k-WL.

For inputs whose recursion bottoms out at finite depth (which §8's input
does, conditional on 2-WL handling individualized CFI(K4)), the algorithm
is polynomial. The depth of the recursion times the per-level cost gives a
total polynomial bound.

This argument is a sketch, not a proof. Formalization would require:
  - A precise definition of "structured" that is checkable per-level.
  - A bound on recursion depth in terms of graph parameters.
  - An invariance proof that the canonical bytes produced at each level are
    iso-invariant.

§11 lists these as open.

---

## 10. Mitigation: detect-and-fall-back

The algorithm should not silently produce wrong bytes. Two detection
strategies, refined for the multi-pass supplant:

1. **Pass-internal tie + downstream tie.** If a supplant pass produces a
   tied atom-signature group whose intra-group disambiguation depends on a
   later pass that *also* ties on its own input, the tie is structural, not
   just signature-incidental. Either the tied atoms are truly automorphic
   (no problem) or the input is non-structured at this level (problem). To
   distinguish, compute both orderings of the offending tie group, run each
   through downstream passes, and check whether the resulting tuple
   multisets coincide. If they don't, fall back to enumerating both
   orderings.

2. **Forced-completion non-singleton residual.** If forced completion
   exhausts every structurally distinct candidate pair in the lowest
   tuple-tied class and Discriminate still does not reach singletons within
   that class, the structured assumption fails. Fall back is required. The
   fall-back enumerates the offending tied class as a search tree (nauty-
   style) over the residual ambiguity, then resumes the polynomial path.

Either path reintroduces L! cost on the offending tie groups but keeps the
fast path fast on inputs that don't need it. The per-pass detection check
is itself polynomial.

---

## 11. Open questions

  1. **Cascade-independence checkability.** Is there a polynomial local test
     that confirms two events' cascades commute, short of re-running both
     orderings? The flip dimension is now provably independent (§6.3); this
     question reduces to the atom-set and layer-order dimensions.

  2. **Touched-flag semantics under bipartite cascades.** The reached flag
     still conflates "structurally touched" with "rank-rewritten." Pair-tag
     events reduce but don't eliminate this — A and B's neighbors may
     rank-rewrite even when not in the cascade's structural reach.

  3. **Within-component orbit-completeness for CFI.** §7 and §8 both assume
     2-WL plus pair-individualization is orbit-complete on a single
     CFI(K4) instance. Empirical probe lives in `CfiPair_DisjointUnion_*`
     tests; results from the previous (path-multiset) algorithm don't carry
     over and the tests must be re-run on the pair-event implementation.

  4. **Atom classification iso-invariance.** §6.2 defines atom types
     operationally (by cascade footprint). A more rigorous definition would
     tie atoms to the orbit structure of G, but the orbit structure is the
     GI question. The operational definition's iso-invariance under the
     structured assumption needs proof, not just empirical confirmation.

  5. **Forced-completion polynomial bound.** §6.1 claims the cost is
     O(p · 2-WL-cost) where p counts structurally distinct candidate pairs.
     A concrete polynomial bound on p in terms of n, for the structured
     class, is pending.

  6. **Recursive singletons formalization.** §9's recursion is a sketch.
     Formal definitions of "structured," "depth," and per-level invariance
     are needed to convert it to a proof.

  7. **Strict-refinement invariant under role-value lex order.** The
     `untouched < cascaded(d) < low < high` order needs to be the lead
     component of every Discriminate signature for the strict-refinement
     invariant to hold across passes. Worth verifying explicitly before
     relying on it.

---

## 12. Where this design sits

  - **Strictly more powerful than the single-vertex layered scheme.** The
    bundling failure that defeated the prior draft is closed by pair-event
    Z/2 invertibility plus forced-completion atom canonicalization.

  - **Strictly more powerful than greedy 2-WL+individualization** when
    cascades are independent: σ-invariance holds in the §7 and §8 regimes
    above; greedy commit fails σ-invariance on the same inputs because its
    in-place rank update can't represent "the choice was arbitrary."

  - **Equivalent to nauty in worst case** under the §10 fallback:
    enumeration over offending tie groups re-introduces the branching
    nauty does natively.

  - **Not a polynomial-time canonizer for arbitrary graphs.** The
    structured assumption fails on graph families that need unbounded
    k-WL — those are the GI-hard core. The algorithm is polynomial *on the
    structured class*, with the recognition problem for that class itself
    a form of GI.

The bet: pair-event canonicalization plus multi-pass supplant captures
enough structure that real-world inputs in the intended domain fall in the
structured class, and §10's detect-and-fall-back keeps the design correct
on the rest at a cost that scales with how adversarial the input is.
