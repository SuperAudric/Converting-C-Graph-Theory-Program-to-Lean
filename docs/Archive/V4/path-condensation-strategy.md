# Path-Multiset Condensation — Algorithm Strategy

A graph canonization approach based on iteratively refining vertex types by
the structural information of paths leaving them. This document describes
the *strategy* — the conceptual machinery any implementation must contain —
independently of specific data structures, ordering conventions, or
encoding tricks.

The intent: someone reading this should be able to build an algorithm of
the same family with substantially different implementation choices and
end up with equivalent equivalence-class behaviour.

---

## 1. Problem and approach

**Problem.** Given a graph (vertex types + adjacency matrix), produce a
canonical form: a unique relabeling such that any two isomorphic inputs
produce identical output bytes.

**Approach.** Distinguish vertices by their structural roles, then sort.
Two vertices are *structurally equivalent* iff there exists an automorphism
of the graph mapping one to the other. The algorithm assigns each vertex
an integer rank ("type") such that:

  - Equivalent vertices ⇒ equal rank (always — guaranteed by
    construction).
  - Non-equivalent vertices ⇒ different rank (the harder direction —
    achievable in this family up to a refinement-strength limit; see §10).

Once every vertex has a unique rank, sort by rank to produce the canonical
permutation; emit the permuted adjacency matrix.

The key design freedom is *how* to compute structural ranks in polynomial
time. The strategy below answers that.

---

## 2. Distinguishing principle: outgoing path multisets

A vertex's structural role is captured by **the multiset of paths leaving
it**, where "two paths are the same" means they trace structurally
indistinguishable trajectories.

A length-d path from `v` is a sequence `(v = w₀, w₁, …, w_d)` with each
consecutive pair connected by some edge. The "structural trajectory" of a
path is what an observer who knows only the following sees as they walk
it:

  - The current type (rank) of each visited vertex.
  - The edge type (weight, label) between consecutive visited vertices.
  - Which vertices in the sequence coincide — the pattern of revisits and
    self-references.

The third point is what makes this stronger than naïve walk counting. Two
length-3 paths `A₁ → A₂ → A₁ → A₃` and `A₁ → A₂ → A₄ → A₃` differ in their
revisit pattern, so they are different trajectories even when every vertex
has the same type.

Two vertices are *defined as equivalent* iff their multisets of length-d
trajectories agree (under relabeling) at every depth `d` up to a
sufficiently large bound — typically the vertex count.

---

## 3. The recursion that makes this tractable

Direct enumeration of length-`d` paths is exponential. The key
observation:

> Every length-`d` path from `v` to `u` is a length-`(d-1)` path from
> `v` to some intermediate vertex `mid`, followed by one edge from
> `mid` to `u`.

Enumerating over every `mid` (including those not adjacent to `u` —
"no edge" is itself information) recovers every length-`d` path
exactly once. So the multiset of length-`d` paths from `v` to `u` is
fully determined by:

  - The multisets of length-`(d-1)` paths from `v` to each `mid`.
  - The edge from each `mid` to `u`.

Two cells `(v, u)` and `(v', u')` produce equivalent length-`d` path
multisets iff, for every "type" of length-`(d-1)` prefix, they see the
same number of `mid`s with that prefix-type that have a given edge to
the endpoint.

This is the lever that makes a polynomial-time encoding possible:
instead of storing the multisets themselves, store *equivalence classes*
of multisets — one class label per `(d, v, u)` triple. The recursion
produces depth-`d` class labels from depth-`(d-1)` class labels.

---

## 4. Cell-rank table

The core data structure is a 3D table indexed by `(d, v, u)`:

```
R[d, v, u] = an integer label such that
  R[d, v, u] = R[d, v', u']
   ⇔ the length-d path multiset from v to u is structurally equivalent
     to the length-d path multiset from v' to u'.
```

These integers are *dense ranks* derived as follows:

1. For each cell `(d, v, u)`, build a *signature*: a sortable summary
   of the length-`d` path multiset from `v` to `u`.
2. Sort all cells (across all `(v, u)` pairs at fixed `d`) by
   signature.
3. Assign rank 0 to the first cell, rank 1 the next time the signature
   changes, etc. Equal signatures share a rank.

### What goes in the signature

The signature at depth `d` for cell `(v, u)` consists of:

  - **Endpoint slot.** The current type (rank) of `u`. This makes the
    signature sensitive to where the paths terminate.
  - **Intermediate-multiset slot.** The order-insensitive multiset over
    `mid` of the pair `(prefix-rank(v → mid), edge(mid → u))`, where
    `prefix-rank(v → mid)` is some rank associated with the length-
    `(d-1)` path from `v` to `mid` (see §6 for the exact form).

The multiset is order-insensitive in `mid` (so the cell signature does
not depend on how vertices are indexed), but each entry is a tuple, so
the multiset distinguishes "3 mids with edge=1 in prefix-class A" from
"3 mids with edge=1 in prefix-class B".

### Depth zero base case

At depth 0 there is no prefix. The signature is just the endpoint type,
plus a marker that distinguishes the diagonal cell `(u = v)` from
off-diagonal cells. The diagonal marker matters because "the length-0
path stays at `v`" is structurally distinct from "the length-0 path
goes from `v` to a different vertex of the same type" — and the
recursive structure carries this distinction forward.

---

## 5. From-vertex aggregation

The cell-rank table lets us read off, for any vertex `v` at any depth
`d`, the multiset of cell ranks `{R[d, v, u] : u ∈ V}`. This is `v`'s
*outgoing profile* at depth `d`.

Vertex types refresh from this profile via another dense rank:

```
T[d, v] = dense rank of (current type of v, sorted multiset of
                         {R[d, v, u] : u ∈ V}) across all v.
```

Vertices with the same current type and the same outgoing profile
share a `T[d, v]`.

The deepest `d` reachable in polynomial time on this data structure
(typically `n - 1`) gives the most refined profile available; that is
what feeds the next iteration.

---

## 6. History tracking

Naïvely using `R[d-1]` directly as `prefix-rank` in the recursion of
§4 has a subtle weakness: two cells that arrive at the same depth-
`(d-1)` rank can have *disagreed* at some earlier depth, and that
disagreement is not preserved when the next depth's signature uses
only the most-recent rank.

On highly symmetric graphs (cycles, vertex-transitive components,
disjoint unions thereof), this weakness produces multiset coincidences
that prevent the algorithm from separating non-isomorphic vertices it
*had been able* to separate at earlier depths. The earlier separation
is silently lost.

The fix is to track a **history rank** alongside the cell rank:

```
H[d, v, u] = dense rank of (H[d-1, v, u], R[d, v, u]) over all (v, u).
```

By induction `H[d, v, u]` encodes the full trajectory
`(R[0, v, u], R[1, v, u], …, R[d, v, u])`. Two cells share an `H` iff
they agree at *every* depth, not just the latest one.

Use `H[d-1]` rather than `R[d-1]` as `prefix-rank` in the cell-
signature recursion of §4. Use `H[d]` rather than `R[d]` in the
from-vertex aggregation of §5.

The asymptotic cost is the same: history rank is one extra dense-rank
pass per depth, comparable to the existing cell-rank pass.

History tracking is what lets the algorithm separate inputs whose
single-depth profiles happen to coincide due to a graph-cover
relationship — for example, distinguishing a vertex in `2 · Cₙ` from
one in `C₂ₙ` when the union of the two appears as a single graph.

---

## 7. Convergence iteration

Given the current vertex types, the §4–§6 machinery computes a
refined type per vertex. Iterate:

```
loop:
  current types → recompute R / H over all depths → derive new types
  if new types == current types: stop
  else: replace current types with new types and repeat
```

**Termination.** Each iteration either splits a type class or leaves
it intact; classes never merge (the refinement is monotone). At most
`n` iterations are possible — once every vertex is in its own class,
nothing can split.

**At the fixed point.** Vertices sharing a type are *indistinguishable*
by any path-multiset trajectory the algorithm can compute. Whether
they are also genuinely Aut-equivalent depends on the refinement's
strength; see §10.

---

## 8. Tie-breaking and canonical output

After convergence, type classes may still contain multiple vertices.
The canonical permutation must break those ties consistently across
all isomorphic copies of the same input.

### Tie-break strategy

Pick the smallest non-singleton class. Apply some consistent rule that
promotes one specific vertex in that class to a new, distinct rank —
for example, "promote the vertex at the earliest array position to
`rank + 1`, leave the others at `rank`." Re-run convergence; the new
singleton may cause further splits as the refinement propagates the
new asymmetry. Repeat until all classes are singletons.

The promotion rule itself doesn't matter for correctness, only for
the specific canonical bytes produced. Any consistent rule works as
long as it depends only on data preserved under isomorphism after
refinement (i.e., not on raw vertex indices except via the converged
type class).

### Stronger: individualization-and-refinement

For *completeness* on all graphs (not just those within the
refinement's strength bound), the tie-break must explore alternatives:
fork on each candidate vertex of the chosen class in turn, run
refinement on each fork, and combine results consistently — for
example, take the lex-smallest canonical form across forks. This
matches what nauty / bliss / traces do. It is exponential
worst-case but practical on real-world inputs.

### Canonical output

Once every vertex has a unique rank, sort vertices by rank and emit
the permuted adjacency matrix. The result is deterministic in the
input data and invariant under input relabeling.

---

## 9. Pipeline summary

```
input: vertex types T₀, adjacency E
  │
  ├─ initialize: T ← dense_rank(T₀)
  │
  ├─ converge:
  │     repeat until T does not change:
  │       for d = 0..n-1:
  │         build cell signatures from H[d-1, v, mid] + edge[mid, u]
  │         assign R[d, v, u]                 (dense rank of cell sigs)
  │         assign H[d, v, u]                 (rank of (H[d-1, v, u], R[d, v, u]))
  │         assign T_new[d, v]                (rank of (T[v], multiset H[d, v, *]))
  │       T ← T_new[n-1, *]
  │
  ├─ tiebreak:
  │     for target = 0..n-1:
  │       converge with current T
  │       if class `target` has > 1 member:
  │         promote one vertex out (by any consistent rule)
  │
  └─ output: sort vertices by final T, permute E, emit
```

---

## 10. Strength and limits

The strategy above defines a *family* of refinement algorithms. Within
the family, design choices include:

  - The exact form of the cell signature (what goes in the endpoint
    slot, the intermediate-multiset slot, and how they're combined).
  - Whether history is tracked at all and how (joint rank pairs vs
    full vector comparison vs windowed depths).
  - The from-vertex aggregation form.
  - The tie-break rule (simple promotion vs full individualization).

The strongest pure-refinement variant in this family — full history,
ordered cell signature, full multiset aggregation — is bounded by some
constant level `k` of the Weisfeiler–Leman hierarchy. The
Cai–Fürer–Immerman construction builds, for every `k`, a pair of
non-isomorphic graphs that `k`-WL cannot distinguish. So no fixed
instance of this family is a complete canonizer on all graphs.

**Two ways past the WL ceiling.**

**(a) Tuple-based refinement.** Track ranks indexed on `k`-tuples of
vertices instead of pairs. This pushes the failure point up the
hierarchy but still has a fixed limit. Cost: `O(n^k)` state.

**(b) Individualization-and-refinement.** Convert the tie-break loop
from a passive "promote one vertex" pass into an active backtracking
search over candidate individualizations. Worst-case exponential,
typical-case polynomial, complete on all graphs.

(b) is the standard route for production canonizers and is what this
strategy's tie-break section §8 anticipates.

---

## 11. What an alternate implementation must preserve

The forward correctness direction — *isomorphic inputs produce
identical canonical output* — depends only on equivalence-class
behaviour at the rank-table level, not on representation. An alternate
implementation will be correct iff it preserves:

  - **Cell-rank equivalence.** Two cells `(v, u)` and `(v', u')` end up
    with the same `R[d, *, *]` iff their length-`d` path multisets are
    structurally equivalent under relabeling.
  - **History equivalence.** Two cells share an `H[d, *, *]` iff they
    agree at every `R[d', *, *]` for `d' ≤ d`.
  - **From-vertex equivalence.** Two vertices share a `T[d, *]` iff
    their outgoing profiles (under the chosen aggregation) agree, and
    their input types agree.

Free to vary:

  - Storage layout (object graph vs flat int/long buffers vs hash
    tables vs immutable functional structures).
  - Sort direction conventions (ascending vs descending, lexicographic
    order of slot tuples).
  - Whether multiset comparison happens by sort-then-iterate, by
    bag-equality test, by hash, or by signature compute.
  - How the history rank is encoded (joint rank pairs computed
    incrementally vs full vector compared lazily).
  - Whether tie-break uses simple promotion or full individualization.
  - Whether the cell sig encodes the edge in slot A vs slot B vs
    interleaved with prefix rank — as long as the resulting
    equivalence on cell sigs is the one §4 specifies.

Implementations that preserve those equivalences will produce the
same equivalence classes on inputs and will agree on which graphs
canonize together, even if they disagree on the exact bytes of any
individual canonical form.
