# Layered Tiebreak with Supplant — v2

A graph canonization algorithm built around a single principle:

> **Guess A<B → 1-WL refine → supplant the guess if the refinement made
> it redundant.**

Each tiebreak event records a binary, invertible commitment ("A is Low,
B is High") in its own layer of a per-vertex rank tuple. After all events
run, a single post-hoc pass walks the layers from latest to earliest and
removes any whose information turned out to be derivable from the others.
What survives is the minimum set of structural decisions the input
required at this discriminator strength.

This document supersedes [`supplant-strategy-v1.md`](./supplant-strategy-v1.md).
The header of that file lists the v1 → v2 differences.

The C# implementation lives in
[`CanonGraphOrdererSupplant.cs`](../GraphCanonizationProject/CanonGraphOrdererSupplant.cs).

---

## 1. Problem

**Canonical labeling.** Given an undirected graph G with vertex types,
produce a byte string `canon(G)` such that

  - Iso: G ≅ H ⇒ canon(G) = canon(H)
  - Non-iso: G ≇ H ⇒ canon(G) ≠ canon(H).

**The obstacle.** Color refinement (1-WL) reaches a fixed point in which
non-equivalent vertices may share a color. Producing a unique canonical
labeling requires breaking those ties, and the choice of *how* to break
each tie is in general not invariant under input relabeling. The standard
families of solutions:

  - **Greedy commit.** Promote one tied vertex to a singleton by index;
    update the structural rank in place. Fast, but not σ-invariant —
    different scramblings break ties at different physical vertices.
  - **Branch and prune (nauty / bliss / traces).** Recursively try every
    choice, individualize, refine, compare leaf labelings, lex-min. σ-
    invariant by construction, exponential worst case.
  - **Layered tiebreak with supplant (this design).** Record each choice
    in its own rank layer. Don't backtrack. After the loop, drop any
    layer the rest of the rank tuple makes redundant; canonicalize the
    leftover freedoms (Z/2 label swap, layer permutation between iso-
    equivalent pair picks).

The discriminator at the core (1-WL pair-rank refinement, see
[`CanonGraphOrdererOneWL.cs`](../GraphCanonizationProject/CanonGraphOrdererOneWL.cs))
is unchanged. Everything in this doc is the machinery around it.

---

## 2. Per-vertex state: rank tuples

Every vertex carries a tuple

```
rankTuple(v) = (r₀,  role₁(v),  role₂(v),  …,  role_L(v))
```

  - **r₀** is 1-WL fixed-point rank computed before any tiebreaking.
    Frozen for the life of the run.
  - **role_k(v)** is one of `{Untouched, Cascaded(d), Low, High}`.
    Frozen once event k completes.
  - **L** is the number of completed events.

**Lex order on roles:**
`Untouched < Cascaded(0) < Cascaded(1) < … < Low < High`.

The three semantic ideas this encodes:

  - *Untouched dominates*: a vertex outside event k's cascade reach sorts
    before any vertex the cascade rewrote.
  - *Cascaded sorts before tagged*: vertices the cascade refined sit
    between Untouched and the explicitly tagged pair.
  - *Low and High are adjacent in the lex order*: the per-layer flip
    swaps Low ↔ High and touches no Cascaded(d) value, so flip is a Z/2
    involution local to the (A, B) cells of the layer.

Each layer also carries a `LayerKind ∈ {Flip, Supplanted}` set during
post-processing.

This is the only state the algorithm carries. There is no automorphism
group, no search tree, no per-event signature multiset.

---

## 3. Algorithm

```
canon(G, vertexTypes):
    s ← Setup(vertexTypes, G)
    EventLoop(s)
    PostProcessSupplant(s)
    FlipCanonicalize(s)                  -- no-op in v1; see §7
    canonicalRanks ← DenseRank(fullTuple(v) for v ∈ V)
    return PermuteByDenseRanks(G, canonicalRanks)
```

### 3.1 Setup

  - Compute r₀ via 1-WL fixed point on `(vertexTypes, adj)`. Frozen.
  - Initialize empty layer list, empty kind list.

### 3.2 Event loop

```
EventLoop(s):
    while True:
        (A, B) ← StructuralPick(s)
        if no pair:  break
        layer ← new Role[N], all Untouched
        layer[A] ← Low
        layer[B] ← High
        s.Layers.append(layer)
        s.LayerKinds.append(Flip)
        Discriminate(s, A, B)            -- 1-WL on full tuples;
                                           writes Cascaded(d) to others
```

`StructuralPick` returns `null` when every tuple is in a singleton class.

### 3.3 StructuralPick — iso-invariant pair selection

Within the lowest tuple-tied class C (ties broken by smallest tuple key
when multiple classes have size ≥ 2), pick the pair whose **joint
adjacency multiset** is lex-smallest:

```
for each unordered pair {A, B} ⊂ C:
    sig(A, B) ← sorted multiset over u ∈ V of
                ( currentTupleKey[u],
                  min(adj[A,u], adj[B,u]),
                  max(adj[A,u], adj[B,u]) )
pick the pair with lex-min sig
```

The pair signature is symmetric in A and B (we use min/max, not the
ordered pair), so it doesn't depend on which physical vertex is named
"A". Combined with `currentTupleKey[u]` being iso-invariant (dense rank
of an iso-invariant partition), `sig(A, B)` is iso-invariant under input
scrambling.

Within the picked pair, A is assigned Low and B High by ascending vertex
index. That intra-pair choice is **not** iso-invariant — it's the Z/2
freedom that `FlipCanonicalize` is supposed to resolve at the end (see
§7).

### 3.4 Discriminate

```
Discriminate(s, A, B):
    L ← s.L
    preEventKeys ← DenseRank of fullTuple restricted to layers 0..L-2
    currentKeys  ← DenseRank of fullTuple restricted to layers 0..L-1
                                                -- includes the new layer
    repeat:
        sigs[v] ← (currentKeys[v],
                   sorted multiset over u of
                       (2·currentKeys[u] + (u==v?1:0),  adj[v,u]))
        currentKeys ← DenseRank by sigs
    until currentKeys is stable

    DecodeLayerRolesPair(s.Layers[L-1], preEventKeys, currentKeys, A, B)
```

This is plain 1-WL on the integer keys derived from the full tuple. The
"+ (u==v?1:0)" term distinguishes "v has a self-loop" from "v has a
same-rank neighbor".

### 3.5 DecodeLayerRolesPair

For the just-added layer, translate the converged 1-WL partition into
role values:

  - A keeps `Low`, B keeps `High` (set explicitly when the layer was
    appended).
  - For every pre-event class C (vertices with the same `preEventKeys`):
    - Drop A and B.
    - Group the remaining vertices by `currentKeys`.
    - If all remaining vertices share one post-event key, the class did
      not split — they stay `Untouched`.
    - Otherwise, sort sub-classes by ascending post-event key and assign
      `Cascaded(0), Cascaded(1), …` to each in order.

The dense-rank of sub-classes is iso-invariant given iso-invariant input
keys, so the `Cascaded(d)` assignment is iso-invariant up to mirror sub-
class swaps under the per-layer Low ↔ High flip (see §6.2).

### 3.6 PostProcessSupplant

```
PostProcessSupplant(s):
    for k = L-1 down to 0:
        if s.LayerKinds[k] != Flip:  continue
        saved ← copy of s.Layers[k]
        zero out s.Layers[k]              -- everyone Untouched at layer k
        keys ← DenseRank of fullTuple over remaining layers
        if every key is distinct:
            s.LayerKinds[k] ← Supplanted   -- layer stays at all-Untouched
        else:
            s.Layers[k] ← saved            -- restore
```

The greedy direction matters: removing a later layer can only make
earlier layers more, not less, essential. Walking backwards lets each
decision stand without re-checking.

A layer marked `Supplanted` is effectively a no-op column in the rank
tuple — every vertex has `Untouched` there, so it contributes nothing to
sort order or 1-WL signatures.

### 3.7 Output

Dense-rank vertices by the full tuple (after `Supplanted` layers are
zeroed and `FlipCanonicalize` runs); permute the adjacency matrix to
match.

---

## 4. Why this avoids backtracking

The principle the v1 design lost is that *every layer survives the loop
in some form*. There is no "undo" in EventLoop. Three possible fates per
layer, decided post-hoc:

  - **Flip** (the layer carries a true Z/2 freedom): kept; flip-
    canonicalized at the end.
  - **Supplanted** (the layer's information is implied by other layers
    + r₀): zeroed out. The structural fact A<B is now visible from the
    rank tuple without the explicit Low/High at this layer.
  - **(X) load-bearing pair-choice freedom** that 1-WL cannot resolve:
    not detected in v2; produces wrong canonical bytes silently. (See
    §8.)

Because the loop never reverts a guess, "current work done" is preserved
across the entire run. Compare to nauty's branch-and-prune, where each
choice is one root of a tree and only one path is consumed. This design
puts each choice in its own rank coordinate and lets them coexist.

---

## 5. Soundness lemmas

### 5.1 1-WL set partition is invariant under per-layer flip

> *Claim.* Given an input partition P that differs only in the labels
> assigned to two designated vertices A, B (with A=Low, B=High in P, and
> A=High, B=Low in P'), 1-WL fixed-point applied to P and to P' produces
> the same set partition (only the dense-rank labels differ).

*Proof sketch.* 1-WL signatures are functions of multisets of (rank,
edge) pairs over neighbours. The two starting partitions are related by
the Low ↔ High label swap on A and B. By symmetry of the multiset
operation under this swap, every iteration's partition matches up to the
same swap.

**Consequence.** A "flip" of layer k's Low/High labels is a relabeling
of cells of an iso-invariant partition. The flip is observable in the
full tuple's dense rank, but not in the underlying partition.

### 5.2 StructuralPick is iso-invariant up to ties

> *Claim.* If `sig(A, B)` is uniquely minimised over candidate pairs of
> the lowest tied class, the chosen pair is the same orbit-pair across
> any input scrambling. If multiple pairs share the lex-min `sig`, the
> shared-min pairs are an iso-equivalent set, and any deterministic
> tiebreak that depends only on iso-invariant data preserves
> σ-invariance.

The current code breaks ties by physical vertex index, which is **not**
iso-invariant. This is the source of the v2's main known failure mode
(see §8.1).

### 5.3 Post-hoc supplant is sound

> *Claim.* If zeroing layer k leaves every full tuple distinct, the
> dense-rank of the full tuples over layers `{0..L-1}\{k}` produces the
> same canonical permutation as the dense-rank over all layers — i.e.,
> layer k contributed no distinguishing information beyond what the
> other layers provide.

*Proof.* Dense-rank is determined by the equivalence classes of the
full tuple under equality. If removing layer k leaves all tuples
distinct, the equivalence classes are still all singletons. Sorting
singletons by tuple yields the same permutation up to lex order on the
remaining coordinates, which agrees with the original lex order
restricted to those coordinates.

The greedy late→early order is sound by induction: removing layer k
cannot make a later layer's removal change correctness (later layers
were already classified before we touched k).

---

## 6. Worked examples

### 6.1 Path 0–1–2–3 (size 4)

r₀ partition: `{0, 3}` (degree 1), `{1, 2}` (degree 2).

Lowest tied class: `{0, 3}`. StructuralPick picks (0, 3) (only candidate
pair). Layer 1 created with `layer[0] = Low, layer[3] = High`.

Discriminate: vertex 1 is adjacent to 0=Low only; vertex 2 is adjacent
to 3=High only. They split. Sub-class with the smaller post-event key
gets `Cascaded(0)`; the other gets `Cascaded(1)`. Result:

```
Layer 1:  [ Low,  Cascaded(0),  Cascaded(1),  High ]
```

Full tuples: `(0, Low), (1, Cascaded(0)), (1, Cascaded(1)), (0, High)`.
All distinct → loop ends.

PostProcessSupplant: zero layer 1. Tuples become `(0, U), (1, U),
(1, U), (0, U)` — vertices 0 ≡ 3, vertices 1 ≡ 2. Not all distinct.
Restore. Layer 1 stays Flip.

Output: dense-rank assigns 0, 2, 3, 1 (sort order: vertex 0 < vertex 3 <
vertex 1 < vertex 2). Canonical permuted matrix is the standard "path"
layout.

### 6.2 Square (4-cycle) — exposes the layer-permutation gap

r₀: every vertex has degree 2 with the same neighbourhood multiset; r₀
ties all four vertices.

Lowest tied class: `{0, 1, 2, 3}`. StructuralPick over six candidate
pairs computes:

  - Adjacent pair (e.g. (0, 1)): sig multiset = four copies of
    `(0, 0, 1)`.
  - Diagonal pair (e.g. (0, 2)): sig multiset =
    `[(0,0,0), (0,0,0), (0,1,1), (0,1,1)]`.

`(0, 0, 0) < (0, 0, 1)` lex, so diagonal sigs are lex-smaller. Both
diagonals `(0, 2)` and `(1, 3)` have the **same** sig — they're iso-
equivalent.

The current code breaks the tie by iteration order (smallest A first,
then smallest B), so it picks `(0, 2)`. Across scramblings, this picks
**different physical pairs that map to different orig-graph diagonals**.
The two layers that result (after the second iteration picks the
remaining diagonal `(1, 3)`) are in **different creation orders** for
different scramblings.

Final tuples for two scramblings of the square diverge in dense-rank,
producing different canonical bytes. The layer-permutation freedom is
unresolved.

### 6.3 What supplant looks like

Supplant fires when later layers' cascades make an earlier layer's
distinctions redundant. Concretely: a graph where individualizing a
later pair `(C, D)` causes 1-WL to discover that A and B were already in
different orbits (visible in the cascaded values around `(C, D)`) — at
which point the explicit Low/High at the earlier layer carries no extra
information.

For the path and the square, no such cascade-feedback exists; supplant
does not fire. For more structured graphs (the §8 CFI examples in v1's
draft), supplant can fire, but the v2 implementation hasn't been
empirically tested on those.

---

## 7. Implementation status

  - [x] Setup, r₀ via 1-WL fixed point.
  - [x] EventLoop with StructuralPick + Discriminate + DecodeLayerRoles.
  - [x] PostProcessSupplant (greedy late→early, full-layer-zero check).
  - [ ] FlipCanonicalize. The simple per-layer Low↔High swap is unsound
    because Cascaded(d) labels on third parties are derived under one
    direction of the guess — a raw label swap leaves them inconsistent
    with the alternative cascade. A correct implementation re-runs
    Discriminate per flip choice and propagates to subsequent layers
    (their pair picks depend on this layer's Cascaded labels). That is
    brute-force territory and is left as future work; the current code
    has `FlipCanonicalize` as an explicit no-op.
  - [ ] Layer-permutation canonicalization. When StructuralPick ties
    (§6.2), the choice of which pair becomes layer 1 vs layer 2 is not
    iso-invariant. v2 has no mechanism for this.
  - [ ] (X) detection.

### 7.1 Test status (last measured)

| Orderer | Passed | Failed | Skipped |
|---|---:|---:|---:|
| `CanonGraphOrdererPairOrder` (baseline) | 35 | 7 | 2 |
| `CanonGraphOrdererSupplant` (v2)        | 31 | 11 | 2 |

The 7 PairOrder failures are also Supplant failures (CFI disjoint-union
scrambling-invariance, large exhaustive-permutation count). The 4
additional Supplant failures (`KnownGraphs` size 4 / 5,
`AllPermutations` size 4, `AllPermutations_Extended` size 5) are size-4
and size-5 cases where PairOrder's index-based pair pick happens to
produce an iso-invariant choice and v2's structural pick ties on iso-
equivalent pair candidates and breaks them by index non-iso-invariantly.

This is the layer-permutation gap of §8.1 surfacing on small inputs.

### 7.2 What's not yet plumbed

  - `FlipCanonicalize` is a stub.
  - There is no telemetry / diagnostic for "supplant fired on layer k"
    — would be useful to confirm supplant ever actually fires on real
    inputs.
  - No (X) detection: when the input is GI-hard at 1-WL strength, the
    algorithm produces wrong bytes silently.

---

## 8. Known failure modes

### 8.1 Layer-permutation freedom

When StructuralPick's lex-min tie has multiple iso-equivalent pair
candidates, the choice of which pair becomes "first" is the choice of
which layer index they occupy. Across scramblings of the same input,
different physical vertices win the index-based tiebreak, and the
layer-creation order diverges. Final dense-rank canonicals differ.

The 4-cycle example in §6.2 is the minimal failure case. The CFI
disjoint-union failures on K4 / K3,3 / Cycle3..5 are larger-scale
manifestations of the same issue.

**Fix direction.** Two options:

  1. **Brute-force** at the canonicalization step: enumerate all
     orderings of layers within a sig-equivalent group, take lex-min.
     Cost is `Π(group_size!)`; for inputs where the structural pick
     produces few ties, this is small.
  2. **Multi-pass structural sort** (the v1 design): classify each
     layer by structural type (within-class / cross-class / cross-
     component; or some other invariant), sort by class first, then
     break inner ties by sub-class coordinates from earlier passes.
     Polynomial when the classification is rich enough; reduces to
     option 1 on inputs where the classification ties.

### 8.2 Within-orbit Z/2 freedom

When the picked pair (A, B) is within a true automorphism orbit, the
Low/High assignment is a Z/2 freedom that should be resolved by lex-min
over the swap. v2's `FlipCanonicalize` is a no-op, so this freedom is
not resolved: scramblings that pick (A, B) vs (B, A) by physical-index
tiebreak produce different canonicals.

**Fix direction.** Brute-force `2^L` flip combinations, re-running
Discriminate per combination (because subsequent layers' Cascaded(d)
assignments depend on prior layers' flips). With smart sharing of work
across the DFS, the cost is closer to `O(2^L · L · 1-WL-cost)`;
without sharing, `O(2^L · L · n³)`.

### 8.3 (X): cross-orbit ties not 1-WL-resolvable

If the lowest tuple-tied class is a non-orbit tie (vertices that 1-WL
groups but that are not actually in the same automorphism orbit), the
guess A<B introduces information that no later refinement can recover
from. Both directions of the guess produce structurally distinct
cascades. Neither flip nor supplant can reconcile them.

This is the GI-hard case at 1-WL strength. v2 doesn't detect it. nauty
handles it natively (the search tree branches, both options are
explored, lex-min over leaves). v1's §10 sketched a "detect-and-fall-
back" mechanism; v2 has not implemented it.

---

## 9. Why the algorithm is forced into exponential worst case

Three compounding sources:

1. **Number of layers L.** L can grow to `n - (number of r₀ classes)`.
   For inputs with high symmetry (every vertex same degree, regular
   structure, CFI constructions), L is `Θ(n)`.

2. **Layer-permutation freedom.** When StructuralPick ties on `m` iso-
   equivalent pair candidates, the resulting layer ordering has up to
   `m!` valid permutations to canonicalize. For an input with several
   tied classes each admitting iso-equivalent picks, the per-layer
   freedom multiplies.

3. **Per-layer Z/2 freedom.** Each layer (after supplant) has up to two
   valid Low/High assignments, requiring `2^L` enumeration.

**Combined worst-case canonicalization cost:** `O(2^L · m! · 1-WL-cost)`
where `m` is the maximal ties-equivalent group size. For CFI graphs at
1-WL strength, this collapses to nauty's exponential branching — same
complexity class, different shape.

### 9.1 The deeper reason

The algorithm uses **1-WL** as its discriminator. 1-WL cannot tell
whether a tied class is

  - a true automorphism orbit (where Z/2-and-friends freedoms are real
    symmetries: enumeration is *correct* but produces `n!`-many bytes
    that all agree, so we just take any one — the only question is
    *picking* the canonical labels), or
  - a non-orbit tie at 1-WL strength (where the freedoms are structural
    decisions: enumeration *might* produce different canonicals across
    inputs, and we have to lex-min).

Without that distinction, the algorithm cannot avoid enumerating every
freedom: it has no way to recognise which freedoms are "free" and which
are load-bearing.

A stronger discriminator (k-WL for higher k) resolves more tied classes
structurally, reducing L. But by Cai-Fürer-Immerman, for any fixed k,
CFI graphs at treewidth `k+1` defeat k-WL. So no fixed-strength
discriminator escapes the exponential worst case on the GI-hard core.

The way out — input-adaptive discriminator strength climbing the WL
hierarchy as needed — is Babai's territory and not what this design
implements.

### 9.2 Why "supplant" doesn't rescue this

The principle was that supplant would absorb most freedoms into
structural information, leaving only a polynomial cleanup. In practice:

  - Supplant fires only when **later** layers' cascades make an
    **earlier** layer's distinctions redundant. This requires multi-
    layer feedback through 1-WL — which 1-WL can produce only if the
    perturbation reveals structural asymmetry that 1-WL on r₀ alone
    missed. For most inputs, this doesn't happen often.
  - Layer-permutation and Z/2 freedoms are *not* candidates for
    supplant in the v2 sense. They're freedoms within the picked pair,
    not redundant guesses about it.

So supplant reduces L (and per-layer enumeration) only when the input
has multi-layer cascade feedback. On inputs without such feedback (much
of the GI-hard core), supplant is a no-op and the full enumeration
applies.

---

## 10. Forward path

### 10.1 Closing the v1 gaps

The two "documented v1 limitation" fixes that would close most of the
test-suite failures:

  - **Brute-force flip canonicalization**, gated by L. For L ≤ ~12 (the
    practical regime for CFI tests), `2^L · 1-WL-cost` is tractable.
  - **Brute-force layer-permutation canonicalization** within sig-
    equivalent groups. Cost `Π(group_size!)`; usually small in
    practice.

Combined, these turn the algorithm into a "pair-event with bounded
brute-force canonicalization". Strictly more power than greedy 1-WL +
individualization; strictly less efficient than nauty on the cases
where nauty's pruning shines, but with much simpler bookkeeping.

### 10.2 Beyond brute force

To re-claim the original "polynomial on structured inputs" promise, the
algorithm needs a structural sort over layers — the v1 multi-pass scheme
or some equivalent. The challenge is defining the sort key in a way
that is *iso-invariant* and *informative* (distinguishes layers that
need distinguishing). v1's atom classification was a first attempt and
had known gaps (§11.1 in v1).

A different angle: detect the (X) case (non-orbit tie at 1-WL) by some
local check after the cascade and escalate that single layer to 2-WL
discriminator strength. This is the "input-adaptive WL climb" approach,
applied per-layer rather than globally.

### 10.3 Empirical work needed

  - Verify that supplant ever fires on real inputs. The v2 code path is
    in place but no test confirms it activates. Add a counter and a
    test that constructs an input where a later layer should supplant
    an earlier one.
  - Re-run the v1 §7 / §8 worked examples (CFI disjoint unions and
    bipartite-interconnected double covers) on v2 once
    FlipCanonicalize is implemented, to see whether the structured-
    class promise holds for v2.
  - Localize each known failure to one of the three known modes
    (§8.1 / §8.2 / §8.3) so the fix priorities match the failure
    distribution.

---

## 11. Glossary

| Term | Meaning |
|---|---|
| r₀ | 1-WL fixed-point rank on `(vertexTypes, adj)`. |
| Layer | One column of the per-vertex rank tuple, added by one event. |
| Event | Pick a pair (A, B), tag layer with Low/High, run 1-WL refine. |
| Role | Per-vertex per-layer value: `Untouched` / `Cascaded(d)` / `Low` / `High`. |
| Cascade | The 1-WL refinement triggered by an event's Low/High tags. |
| Tied class | Set of vertices sharing a full tuple key. |
| Flip | Per-layer Z/2 freedom: swap A=Low, B=High ↔ A=High, B=Low. |
| Supplant | Decide a layer is redundant and zero it. Post-hoc. |
| Iso-invariant | Unchanged under input vertex relabeling. |
| σ-invariance | Same as iso-invariance (different shorthand). |
| (X) regime | Cross-orbit tie at 1-WL strength — GI-hard, undetected in v2. |
