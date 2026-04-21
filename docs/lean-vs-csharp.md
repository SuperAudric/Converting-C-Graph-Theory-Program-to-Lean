# Lean vs C# Implementation Comparison

Both `GraphCanonizationProject/CanonGraphOrdererV4.cs` and `GraphCanonizationProofs/LeanGraphCanonizerV4.lean` implement the same graph canonization algorithm. The C# version is the primary executable; the Lean version is a pure functional translation intended as a stepping stone toward formal proof.

## Function / type name mapping

| Lean | C# |
|------|-----|
| `AdjMatrix vertexCount` | `EdgeType[,]` (size implicit) |
| `AdjMatrix.swapVertexLabels` | `SwapVertexLabelling` |
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
| `run` | `Run` |

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

**C# — plain 2D array:**
```csharp
EdgeType[,] edges  // size carried implicitly
```

**Lean — dependent type:**
```lean
structure AdjMatrix (vertexCount : Nat) where
  adj : Fin vertexCount → Fin vertexCount → EdgeType
```

Lean's `AdjMatrix` carries its vertex count in the type, which means size mismatches are a compile-time error rather than a runtime check. `Fin vertexCount` is an index type that is bounded by definition, so out-of-bounds access is impossible.

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

**C# — sort-based:**
```csharp
private static VertexType[] GetArrayRank(VertexType[] arr)
{
    var sortedByValue = arr.Select((v, i) => (v, i)).OrderBy(x => x.v).ToArray();
    // walk sorted order, assigning ranks
}
```

**Lean — count-smaller-values approach:**
```lean
def getArrayRank (arr : Array VertexType) : Array VertexType :=
  arr.map fun value =>
    arr.foldl (fun smallerCount other =>
      if other < value then smallerCount + 1 else smallerCount) 0
```

The Lean version counts, for each element, how many other elements are strictly smaller. This is O(n²) but is simpler to reason about formally. Both produce the same result.

---

## What the Lean file does not include

- Input validation (`ValidateInputs`) — Lean's type system makes out-of-range inputs impossible
- `AdjMatrixToString` output formatting — the Lean `ToString` instance is equivalent
- Debug helpers (`LayerToString`) — present in C# for development, omitted in Lean

## What the Lean file adds

- The `Isomorphic` inductive proposition and the `≃` notation
- The `AdjMatrix` dependent type with size in the type
- `RankState.getBetween` / `getFrom` accessor functions (in C# these are direct array accesses)
