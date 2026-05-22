# Graph Canonization Algorithm

This document explains the algorithm implemented in `CanonGraphOrdererV4.cs` and `LeanGraphCanonizerV4.lean`. Both files contain the same algorithm; the C# version is the executable reference, and the Lean version is a functional translation intended as a basis for formal proof.

## What it does

Given a labeled graph — an adjacency matrix `edges[i,j]` and a vertex-type array `vertexTypes[i]` — the algorithm produces a **canonical form**: a permuted copy of the adjacency matrix where vertices are placed in a unique, reproducible order. Two isomorphic graphs (one obtainable from the other by renaming vertices) always produce the same canonical matrix.

**Inputs:**
- `vertexTypes[]` — an integer label per vertex; may all be zero if vertices are unlabeled
- `edges[i,j]` — integer edge weights; 0 means no edge; the matrix need not be symmetric

**Output:** A permuted adjacency matrix in canonical order (printed as a string in C#; returned as `AdjMatrix` in Lean).

## Pipeline overview

```
vertexTypes + edges
      │
      ├─ GetArrayRank(vertexTypes)         initial rankings: replace each type with
      │                                    count of strictly smaller values in array
      │
      ├─ InitializePaths(edges)            build PathState once from edges alone;
      │                                    never changed after this point
      │
      ├─ OrderVertices(pathState,          produce a total ranking of every vertex
      │     initialRankings)               ┌─ ConvergeLoop: refine ranks to fixed point
      │                                    └─ BreakTie: resolve remaining symmetries
      │
      └─ LabelEdgesAccordingToRankings     permute the matrix so vertex i lands at
            (orderedRankings, edges)       its ranked position
```

---

## Step 1 — Initial rankings (`GetArrayRank`)

Vertex types are replaced by their rank among all vertex types: each value becomes the count of strictly smaller values in the array. This normalizes input types to a 0-based scale without losing relative order.

Example: `[0, 10, 5, 5, 11]` → `[0, 3, 1, 1, 4]`

---

## Step 2 — Path state (`InitializePaths`)

The path state is a static, edge-derived data structure that is built once and never modified. It stores, for every triple `(depth, from, to)`, the **structural description of all walks of length `depth` from vertex `from` to vertex `to`**.

### The path segment types

A `PathSegment` is one of:
- `bottom(v)` — a zero-length walk that stays at vertex `v`
- `inner(edgeType, subPath)` — the last step of a walk: arrive at the destination via `edgeType` from `mid`, where `subPath` describes all shorter walks from `from` to `mid`

### Recursive construction

```
PathsBetween(depth=0, from, to):
  connectedSubPaths = [bottom(from)]  if from == to
                      []              otherwise

PathsBetween(depth=d, from, to):
  connectedSubPaths = [inner(edges[mid, to], PathsBetween(d-1, from, mid))
                       for every vertex mid]
```

`PathsBetween(d, from, to).connectedSubPaths` is therefore a list of `n` elements — one entry per potential intermediary `mid`. Each entry pairs the last edge taken (from `mid` to `to`) with the entire depth-`(d-1)` walk sub-structure from `from` to `mid`.

This is built for every `(depth, from, to)` triple with `depth` from `0` to `n-1`.

### Why include all intermediaries, not just adjacent ones?

Including every `mid` (even when `edges[mid, to] = 0`) ensures the encoding is complete. Two paths are equal only when they agree on *every* potential intermediary, including "there is no edge here." Edge weight 0 is a valid distinguisher.

`PathsFrom(d, from)` groups all `PathsBetween(d, from, *)` together — it represents the full walk profile of vertex `from` at depth `d`.

---

## Step 3 — Ranking (`CalculatePathRankings`)

To compare path structures efficiently, we assign integer ranks:

- **`BetweenRanks[d, from, to]`** — the rank of `PathsBetween(d, from, to)` relative to all such objects at depth `d`. Two path-between objects receive the same rank if and only if they are structurally equal.

- **`FromRanks[d, from]`** — the rank of `PathsFrom(d, from)` relative to all vertices. Two vertices receive the same rank if and only if they look structurally identical up to depth `d`.

Ranks are computed depth by depth: `BetweenRanks` at depth `d` is filled before `FromRanks` at depth `d`, and both use `BetweenRanks` from depth `d-1` as a sub-structure lookup.

### Rank assignment rule

Sort the objects; walk the sorted list; a new rank starts at position `i` whenever the element at `i` differs from the one before it. Equal elements share the rank of the first member of their group.

Example: sorted `[a, a, b, c]` → ranks `[0, 0, 2, 3]`

### Comparison rules

**Two `PathsBetween` objects** are compared:
1. By their endpoint vertex type — higher type sorts first (larger rank = more distinguished vertex)
2. If equal, by their multiset of path segments — sorted and compared element-wise (order-insensitive)

**Two path segments** are compared:
- `bottom(v)` vs `bottom(w)`: compare vertex types directly
- `inner(edgeA, subA)` vs `inner(edgeB, subB)`: compare by rank of sub-path descending, then edge type descending
- `bottom` vs `inner`: never compared (they never appear in the same list)

**Two `PathsFrom` objects** are compared:
1. By start vertex type
2. By their multiset of `PathsBetween` objects — order-insensitive

The order-insensitive comparison (`OrderInsensitiveListComparison`) sorts both lists and compares them element-wise. This ensures that the order in which `mid` vertices were enumerated does not affect the result.

---

## Step 4 — Vertex ordering (`OrderVertices`)

### Convergence (`ConvergeLoop` / `ConvergeOnce`)

Starting from the initial rankings:
1. Run `CalculatePathRankings`
2. Replace each vertex's rank with `FromRanks[n-1, vertex]` — the deepest available path rank
3. If any rank changed, repeat from step 1
4. Stop when no rank changes (fixed point)

Each iteration can only increase the number of distinct rank values (vertices that were equal can become distinct, but distinct vertices cannot become equal). The loop therefore always terminates within `n` iterations.

After convergence, vertices that still share a rank are **genuinely symmetric**: there exists an automorphism of the graph that maps one to the other. No amount of further refinement can separate them based on graph structure alone.

### Tie-breaking (`BreakTie`)

`BreakTie(rankings, target)` scans the array and promotes the **second** vertex found with rank `target` to `target + 1`. The first occurrence is left at `target`.

This is an arbitrary but consistent choice: it distinguishes the earlier-indexed vertex from the later-indexed one. For a symmetric graph, any choice is equally valid — what matters is that the same choice is made when presented with either labeling of the same graph.

### The full loop (`OrderVertices`)

```
for targetPosition in 0..n-1:
    converge to fixed point
    break tie at targetPosition
```

After the tie at position 0 is broken, convergence may further separate other symmetric groups. Then the tie at position 1 is broken, and so on. By the end, every vertex has a unique rank.

---

## Step 5 — Final labeling (`LabelEdgesAccordingToRankings`)

1. Convert the vertex rankings to **dense ranks**: sort vertices by their ranking value (breaking ties by original index), then assign sequential positions 0, 1, 2…

2. For each position `i` from 0 to `n-1`, find the vertex `j` that currently occupies position `i` in the rank map and swap vertices `i` and `j` in the adjacency matrix.

Each swap exchanges two rows and the corresponding two columns — an isomorphism-preserving relabeling. After all swaps, the vertex that should be at position 0 is at position 0, the vertex that should be at position 1 is at position 1, and so on.

---

## Correctness intuition

Two isomorphic graphs `G` and `H` (with matching vertex types under the isomorphism) produce the same canonical form because:

1. The path structure is purely structural — `PathsBetween(d, from, to)` depends only on edge values and the recursive subpaths, which are identical under any isomorphism.

2. Rankings are invariant to labeling — because comparisons are order-insensitive, the rank of a path structure is unchanged when vertex names change.

3. Convergence reaches the same fixed point regardless of initial labeling — since all information used is structural.

4. Tie-breaking by array position is consistent — symmetrically equivalent vertices end up in the same relative order after convergence, so the tie-break always picks the same one.

The contrapositive also holds: if two graphs produce different canonical forms, they are not isomorphic (they differ in some structural invariant captured by the path ranking).

---

## Example: path graph `0—1—2`

Three different vertex labelings of the same path graph all canonize identically:

| Labeling | edges[0] | edges[1] | edges[2] |
|----------|---------|---------|---------|
| 0─1─2 (original) | `[0,1,0]` | `[1,0,1]` | `[0,1,0]` |
| 2 is the middle  | `[0,0,1]` | `[0,0,1]` | `[1,1,0]` |
| 0 is the middle  | `[0,1,1]` | `[1,0,0]` | `[1,0,0]` |

After canonization, all three produce the same matrix with the degree-2 (middle) vertex first.

---

## Complexity

- `InitializePaths`: O(n³) — fills `n × n × n` path objects, each with `n` segments
- `CalculatePathRankings`: O(n³ log n) per call — sorts O(n²) `PathsBetween` objects each with O(n log n) order-insensitive comparison
- `OrderVertices`: at most `n` convergence rounds × at most `n` iterations each = O(n²) calls to `CalculatePathRankings`
- Total: O(n⁵ log n) in the worst case

For the graphs tested (up to size 9 for counting, 7 for the exhaustive scramble test), this is practical.
