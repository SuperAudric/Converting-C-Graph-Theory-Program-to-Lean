# Core Algorithm — notes for `OrbitCompleteAfterConv`

This file captures what the `convergeLoop` in `LeanGraphCanonizerV4` actually
does, in a form aimed specifically at supporting the discharge of
[OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md). For a more general
description of the pipeline see [`docs/algorithm.md`](../docs/algorithm.md);
for the algorithm itself see
[LeanGraphCanonizerV4.lean](LeanGraphCanonizerV4.lean).

---

## What the algorithm computes

Two vertices are considered the same iff there is some indexing of the
remaining vertices for which the multiset of paths leaving each, expressed in
a form like `(VertexType A, idx 1) → (VertexType B, idx 1) ↛ (VertexType A, idx 2)`,
matches between them. In practice, "indexing" is replaced with directly
tracking each visited vertex, then sorting after the fact.

To break ties between candidate indexings: prefer the lexicographically
earliest. When choosing among indexed paths, prioritize the one with the
earliest duplicates — `112` before `123`, regardless of how their suffixes
look. Combined with the earlier-set criteria (vertex type, edge type), this
gives a partial order strong enough to break ties down to a unique
lex-first index assignment per vertex.

Vertices are then compared by their contained path multiset in lex-first
order. The intuition: if you couldn't tell two vertices apart with infinite
string and infinite time to walk the graph and mark every step, then they're
the same.

## Dynamic-programming compression

Naively this is exponential — `n^n` paths of length `n` — but each length-`n`
path between A and B is a length-1 path A→X composed with a length-(n−1) path
X→B. Combined with the indexing scheme, this stores in polynomial space.

Sorting survives the compression: two paths tied at length `k` must be
identical end-to-end, so any disagreement at length `k` propagates upward to
length `k+1, k+2, …`, and the rank doesn't decay.

The output of compression is the data structure tracked by
[`PathState`](LeanGraphCanonizerV4.lean) and the rank tables computed by
`calculatePathRankings`:

  - `BetweenRanks[d, v, u]` — rank of `PathsBetween d v u` among all such
    objects at depth d. Equal ranks ⇔ structurally equal multisets of
    `(edge[mid, u], BetweenRanks[d−1, v, mid])` over `mid`.
  - `FromRanks[d, v]` — rank of `PathsFrom d v` (= multiset over `u` of
    `(type[u], BetweenRanks[d, v, u])`).

`convergeLoop` iterates: refresh vertex types from `FromRanks[n−1, v]`, repeat
until fixed point. Termination is guaranteed within `n` iterations because
each iteration can only split classes, never merge them.

## How this differs from neighbor-color refinement

Compared to plain color refinement (1-WL):

  - Multiple paths that diverge and then re-converge through *different*
    intermediaries are not collapsed.
    `[A1→A2→A3, A1→A4→A3]` is distinguished from
    `[A1→A2→A3, A1→A2→A3]`.
  - Paths that revisit a vertex are differentiated from paths that don't.
    `A1→A2` (line) and `A1→A1` (loop) are separate.

These two properties are what motivated this algorithm over a 1-Weisfeiler Leman-style
implementation, since they trivially distinguish many graphs that 1-WL merges
(uniform graphs in particular).

## Where this sits relative to known refinement hierarchies

The algorithm tracks ranks indexed on `(depth, start, end)` triples — pair
information richer than 1-WL, with edge-type and visited-intermediary
detail. **Whether it coincides with k-WL for some constant k, or is strictly
stronger, is not assumed in this project.** This is the question that
[OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md) needs answered to
decide whether the obligation is provable.

The first concrete step in the discharge plan is therefore not a proof: it's
a **direct CFI test** of the algorithm. Cai–Furer–Immerman pairs are the
standard hard cases for refinement-based algorithms; if path-multiset
refinement collapses a CFI pair, the obligation is false and the algorithm
needs to be augmented (e.g. with individualization-and-refinement). If it
distinguishes every CFI pair we throw at it, the algorithm is empirically
beyond the WL hierarchy and the bisimulation-lift proof attempt is justified.
The CFI generator stub lives at
[GraphCanonizationProject/CfiGraphGenerator.cs](../GraphCanonizationProject/CfiGraphGenerator.cs).

## What's known to matter for the proof

The remaining proof obligation is about the *symmetry between
indistinguishable vertices*, not the exact comparison rules. Specifically:

  - It matters that ties are broken consistently across both inputs of any
    pair-of-graphs comparison; the *direction* of the tie (ascending vs
    descending, edge-type-first vs subpath-rank-first) is irrelevant to the
    completeness statement.
  - It matters that converged ranks classify vertices into structurally
    indistinguishable groups; this is the equitable-partition condition that
    the bisimulation lift in Approach A (Step 2 in the discharge plan) starts
    from.
  - It matters that the iteration terminates, which it does within `n`
    rounds.

Comparison details (e.g. `A1→A2` is sorted as `A A 1 2 → ...`, and various
ties needing the precise descending-ascending dance to remain stable) are
load-bearing for the algorithm's correctness on a specific platform but are
not what the open obligation is about. They're only relevant insofar as they
preserve the fixed-point character of `convergeLoop`.

## Side note
It would not surpise me if there were faster implementations of this algorithm.
Perhaps dropping one of the vertex array indices, or providing an arbitrary backup comparer
for vertices that was never tied. It could that replaces the need for tiebreak,
as long as it never takes precedent over orbit comparisons. 
This may paralelize the tiebreaking within converge cycles so only one loop needed.

## Quick map for the proof effort

If you're working on `OrbitCompleteAfterConv_general`:

  - Forward direction (same orbit ⇒ same converged value) is already proved:
    [`convergeLoop_Aut_invariant`](FullCorrectness/Equivariance/ConvergeLoop.lean).
    This says `convergeLoop` respects automorphisms, including TypedAut.
  - Reverse direction (same converged value ⇒ same orbit) is the open piece.
    Plan and current next step are in
    [OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md).
  - Equitable-partition framing: at the fixed point, vertices grouped by
    converged rank satisfy the local refinement-stability condition. The
    proof's task is showing this partition equals the Aut-orbit partition —
    the open question for this algorithm.
