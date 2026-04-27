# Lean vs C# Implementation Comparison

Both `GraphCanonizationProject/CanonGraphOrdererV4.cs` and `GraphCanonizationProofs/LeanGraphCanonizerV4.lean` implement the same graph canonization algorithm. The C# version is the primary executable; the Lean version is a pure functional translation intended as a stepping stone toward formal proof.

## Function / type name mapping

| Lean | C# |
|------|-----|
| `AdjMatrix vertexCount` | `AdjMatrix` (vertex count carried at runtime) |
| `AdjMatrix.swapVertexLabels` | `AdjMatrix.SwapVertexLabels` |
| `AdjMatrix.adjToString` | `AdjMatrix.ToString` |
| `AdjMatrix.Isomorphic` | no equivalent (proof-only) |
| `PathsBetween` | `AllPathsBetween` |
| `PathsFrom` | `AllPathsFrom` |
| `PathState` | `PathState` record |
| `RankState` | `RankState` record |
| `RankState.getBetween` | `betweenRanks[d, from, to]` array indexing |
| `RankState.getFrom` | `fromRanks[d, from]` array indexing |
| `PathSegment.bottom` | `BottomPathSegment` |
| `PathSegment.inner` | `InnerPathSegment` |
| `getArrayRank` | `GetArrayRank` |
| `insertSorted` / `sortBy` | `Array.Sort` |
| `orderInsensitiveListCmp` | `OrderInsensitiveListComparison` |
| `comparePathSegments` | `ComparePathSegments` |
| `comparePathsBetween` | `ComparePathsBetween` |
| `comparePathsFrom` | `ComparePathsFrom` |
| `initializePaths` | `InitializePaths` |
| `assignRanks` | `AssignRanks` |
| `calculatePathRankings` | `CalculatePathRankings` |
| `setBetween` | write into `betweenRanks` array |
| `convergeOnce` | `ConvergeOnce` |
| `convergeLoop` | `ConvergeLoop` |
| `breakTie` | `BreakTie` |
| `orderVertices` | `OrderVertices` |
| `computeDenseRanks` | `ComputeDenseRanks` |
| `labelEdgesAccordingToRankings` | `LabelEdgesAccordingToRankings` |
| `shiftAbove` | `ShiftAbove` |
| `breakTiePromote` | `BreakTiePromote` |
| `getArrayRank` (dense) | `GetArrayRank` (dense) |
| `run` | `Run` (returns `AdjMatrix`); `Run_ToString` is a thin wrapper that takes `EdgeType[,]` and calls `.ToString()` |

---

## Key structural differences

### 1. Path segment sub-path reference style

This is the most significant representational difference.

**C# — object reference:**
```csharp
public sealed class InnerPathSegment(EdgeType edgeType, AllPathsBetween subPath) : PathSegment
{
    public readonly AllPathsBetween subPath = subPath;
}
// Rank lookup during comparison:
betweenRanks[ix.subPath.depth, ix.subPath.startVertexIndex, ix.subPath.endVertexIndex]
```

**Lean — index triple:**
```lean
| inner (edgeType : EdgeType) (subDepth subStart subEnd : Nat) : PathSegment
-- Rank lookup during comparison:
betweenRanks xDepth xStart xEnd
```

C# holds a direct reference to the `AllPathsBetween` object so it can look up the rank from the object's own fields. Lean is purely functional and cannot store object references across function boundaries, so it stores the `(depth, startVertexIndex, endVertexIndex)` triple needed to index into the rank tables instead.

The `betweenRanks` parameter in Lean comparison functions is a `Nat → Nat → Nat → Int` function (a closure over the current rank table), not a 3D array.

### 2. Mutability

**C# — mutable rank arrays:**
```csharp
var betweenRanks = new int[n, n, n];   // allocated once, filled in-place
var fromRanks    = new int[n, n];
// ...
betweenRanks[depth, path.startVertexIndex, path.endVertexIndex] = rank;
```

**Lean — immutable arrays, accumulator folding:**
```lean
let (finalBetween, finalFrom) := (List.range numVertices).foldl
  (fun (accumulated : Array (Array (Array Int)) × Array (Array Int)) depth => ...)
  (emptyBetweenTable, emptyFromTable)
```

Lean threads the rank tables as immutable values through a fold. C# mutates them in place. The result is the same; the style difference is required by Lean's purity.

### 3. Sorting

**C# — standard library sort:**
```csharp
Array.Sort(sorted, compare);
```

**Lean — hand-written insertion sort:**
```lean
def insertSorted {α : Type} (cmp : α → α → Ordering) (newItem : α) : List α → List α
def sortBy {α : Type} (cmp : α → α → Ordering) : List α → List α
```

Lean's `sortBy` is insertion sort, present because it is straightforward to reason about in proofs. Performance is not the goal on the Lean side.

### 4. Graph representation

**C# — wrapper class around a 2D array:**
```csharp
public sealed class AdjMatrix
{
    public readonly int VertexCount;
    private readonly EdgeType[,] _adj;
    public EdgeType this[int from, int to] => _adj[from, to];
    public AdjMatrix SwapVertexLabels(int v1, int v2) { ... }
    public override string ToString() { ... }
}
```

**Lean — dependent type:**
```lean
structure AdjMatrix (vertexCount : Nat) where
  adj : Fin vertexCount → Fin vertexCount → EdgeType
```

Both sides expose an `AdjMatrix` type with the same operations (`SwapVertexLabels`, `ToString`). Lean carries `vertexCount` in the type, making size mismatches a compile-time error and out-of-bounds access impossible (`Fin vertexCount` is bounded by construction). C# carries it at runtime as a public field; size mismatches between `vertexTypes` and `G` are caught by a runtime check at the start of `Run`.

### 5. Isomorphism relation (Lean only)

Lean defines a formal `Isomorphic` inductive relation:

```lean
inductive Isomorphic : AdjMatrix vertexCount → AdjMatrix vertexCount → Prop
  | refl  (G : AdjMatrix vertexCount) : Isomorphic G G
  | swap  (G : AdjMatrix vertexCount) (vertex1 vertex2 : Fin vertexCount)
      : Isomorphic G (swapVertexLabels vertex1 vertex2 G)
  | trans : Isomorphic G₁ G₂ → Isomorphic G₂ G₃ → Isomorphic G₁ G₃
```

This says two graphs are isomorphic if one can be reached from the other via a sequence of vertex-label swaps. C# has no formal notion of isomorphism — correctness is validated by the tests instead.

The long-term goal is to prove in Lean that `run G ≃ G` (the canonical form is isomorphic to the original) and that `run G = run H` whenever `G ≃ H` (isomorphic graphs share a canonical form).

### 6. `convergeLoop` termination

**C# — bounded loop:**
```csharp
private static VertexType[] ConvergeLoop(PathState state, VertexType[] vertexRankings, int fuel)
{
    for (int i = 0; i < fuel; i++) { ... if (!changed) break; }
    return vertexRankings;
}
```

**Lean — structural recursion on a `Nat` fuel parameter:**
```lean
private def convergeLoop (state : PathState) (vertexTypes : Array VertexType) : Nat → Array VertexType
  | 0        => vertexTypes
  | fuel + 1 =>
    let (updatedTypes, changed) := convergeOnce state vertexTypes
    if changed then convergeLoop state updatedTypes fuel else updatedTypes
```

Both use a "fuel" counter to ensure the function provably terminates. Lean requires all functions to be structurally or well-founded terminating; the fuel parameter makes this explicit. The caller passes `n` (vertex count) as fuel, which is always enough since convergence takes at most `n` steps.

### 7. `getArrayRank` implementation

Both sides now produce **dense** ranks: each distinct value maps to a consecutive
ordinal `0, 1, 2, …` with ties preserved. E.g. `[5, 0, 5, 3]` ↦ `[2, 0, 2, 1]`.

**C# — sort-based:**
```csharp
private static VertexType[] GetArrayRank(VertexType[] arr)
{
    var sortedByValue = arr.Select((v, i) => (v, i)).OrderBy(x => x.v).ToArray();
    int counter = 0;
    // walk sorted order; bump counter on each value transition (dense)
}
```

**Lean — sort-based, same algorithm:**
```lean
def getArrayRank (arr : Array VertexType) : Array VertexType :=
  let sorted := sortBy (fun a b => compare a.1 b.1) (...pair-with-index...)
  -- fold through sorted, bumping rank on each value transition (dense)
```

[sparse→dense] Both implementations were previously sparse — C# returned "count of strictly smaller values" (`[5,0,5,3] → [3,0,3,1]`), and Lean had the same shape via a fold-count. Both were switched to dense to keep the `IsPrefixTyping` invariant true at the entry point of `run` (see `BreakTie` shift-above logic in §8).

### 8. `breakTie` and dense-rank gap maintenance

`breakTie target` collapses one symmetry by promoting all-but-one of the value-`target` vertices to `target + 1`. With **dense** ranks, value `target + 1` is already occupied by the next class, so a one-slot gap must be opened first.

**Lean and C# now both:**

1. Count occurrences of `target`. If `< 2`, return unchanged.
2. `shiftAbove target`: bump every value `> target` up by one, opening a gap at `target + 1`.
3. `breakTiePromote`: walk the array and promote all-but-the-first `target` to `target + 1`.

Previously C# performed step 3 only — which worked because **sparse** ranks left a gap of size `≥ k` after every class of size `k`, so promoting could not collide with the next class. The dense form removes that gap, making the explicit `shiftAbove` necessary.

---

## What the Lean file does not include

- Input validation (vertex-count vs matrix-size mismatch) — Lean's type system makes it impossible
- Debug helpers (`LayerToString`) — present in C# for development, omitted in Lean

## What the C# file adds

- `Run_ToString` — a wrapper that accepts a raw `EdgeType[,]` and returns the canonical form as a string (used by tests). Lean's `run` corresponds directly to C#'s `Run`.
- A backward-compat overload `LabelEdgesAccordingToRankings(VertexType[], EdgeType[,])` that mirrors the `AdjMatrix`-typed primary version for tests still using `EdgeType[,]` directly.

## What the Lean file adds

- The `Isomorphic` inductive proposition and the `≃` notation
- The `AdjMatrix` dependent type with size in the type (C# carries it at runtime)
- `RankState.getBetween` / `getFrom` accessor functions (in C# these are direct array accesses)
