import Mathlib.Tactic
import Aesop
open Nat

namespace Graph

abbrev VertexType := Int
abbrev EdgeType   := Int

/-! ## Adjacency matrix -/

/-- An adjacency-matrix representation of a weighted graph on `n` vertices.
    Input type for the canonizer, replacing raw `EdgeType[,]` arrays. -/
structure AdjMatrix (n : Nat) where
  adj : Fin n → Fin n → EdgeType

namespace AdjMatrix

variable {n : Nat}

/-- Swap two vertex labels in an adjacency matrix (isomorphism-preserving). -/
def swapVertices (i j : Fin n) (G : AdjMatrix n) : AdjMatrix n :=
  { adj := fun u v =>
      let u' := if u = i then j else if u = j then i else u
      let v' := if v = i then j else if v = j then i else v
      G.adj u' v' }

/-! ## Isomorphism -/

inductive Isomorphic : AdjMatrix n → AdjMatrix n → Prop
  | refl  (G : AdjMatrix n)                    : Isomorphic G G
  | swap  (G : AdjMatrix n) (i j : Fin n)      : Isomorphic G (swapVertices i j G)
  | trans {G₁ G₂ G₃ : AdjMatrix n}
      : Isomorphic G₁ G₂ → Isomorphic G₂ G₃   → Isomorphic G₁ G₃

@[inherit_doc] scoped infixl:50 " ≃ " => Isomorphic

def adjToString (G : AdjMatrix n) : String :=
  let rows := List.finRange n
  let rowStrings := rows.map fun i =>
    let rowString := (List.finRange n).map fun j => toString (G.adj i j)
    String.join (rowString.intersperse " ")
  String.join (rowStrings.intersperse "\n")

instance : ToString (AdjMatrix n) := ⟨adjToString⟩

end AdjMatrix

/-! ## Path structures
    These mirror the C# `PathSegment`, `AllPossiblePathsBetween`, `AllPossiblePathsFrom`.

    Key design choice: `PathSegment.inner` stores the sub-path's `(depth, start, end)` indices
    directly rather than a reference to an `AllPossiblePathsBetween` object.  This avoids mutual
    recursion entirely — `PathSegment` is a plain inductive type. -/

/-- A single element of a `connectedSubPaths` list.
    - `bottom v` : depth-0 self-path at vertex `v`.
    - `inner e d s m` : edge of weight `e` prepended to the depth-`d` path from `s` to `m`. -/
inductive PathSegment where
  | bottom (vertexIndex : Nat)                                          : PathSegment
  | inner  (edgeType : EdgeType) (subDepth subStart subEnd : Nat)      : PathSegment
deriving Repr, BEq

/-- All paths of a given length between two specific vertices. -/
structure PathsBetween where
  depth            : Nat
  startVertexIndex : Nat
  endVertexIndex   : Nat
  connectedSubPaths : List PathSegment
deriving Repr

/-- All paths of a given length starting from one specific vertex.
    `pathsToVertex` is ordered by `endVertexIndex` (index = position in list). -/
structure PathsFrom where
  depth            : Nat
  startVertexIndex : Nat
  pathsToVertex    : List PathsBetween
deriving Repr

/-- The full path structure at every depth.
    `pathsOfLength[depth][startVertex]` gives a `PathsFrom`. -/
structure PathState where
  n              : Nat
  pathsOfLength  : Array (Array PathsFrom)

/-- Pre-computed rank lookup tables.
    `betweenRanks depth from to` = rank of all length-`depth` paths from `from` to `to`.
    `fromRanks    depth from`    = rank of all length-`depth` paths from `from`. -/
structure RankState where
  betweenRanks : Nat → Nat → Nat → Int
  fromRanks    : Nat → Nat → Int

/-! ## Helper: ranking -/

/-- Rank each element by the count of strictly smaller elements in the array.
    E.g. `#[0, 10, 5, 5, 11] → #[0, 3, 1, 1, 4]`. -/
def getArrayRank (arr : Array VertexType) : Array VertexType :=
  arr.map fun v => arr.foldl (fun acc w => if w < v then acc + 1 else acc) 0

#eval getArrayRank #[0, 10, 5, 5, 11]  -- #[0, 3, 1, 1, 4]
#eval getArrayRank #[0, 0, 0]           -- #[0, 0, 0]
#eval getArrayRank #[3, 1, 2]           -- #[2, 0, 1]

/-! ## Helper: order-insensitive comparison -/

/-- Stable insertion sort by a comparison function. -/
def insertSorted {α : Type} (cmp : α → α → Ordering) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if cmp x y != .gt then x :: y :: ys else y :: insertSorted cmp x ys

/-- Sort a list by a comparison function (insertion sort). -/
def sortBy {α : Type} (cmp : α → α → Ordering) : List α → List α
  | []      => []
  | x :: xs => insertSorted cmp x (sortBy cmp xs)

#eval sortBy compare [3, 1, 4, 1, 5, 9, 2, 6]  -- [1, 1, 2, 3, 4, 5, 6, 9]

/-- Compare two lists by their sorted contents (order-insensitive multiset comparison).
    Mirrors C# `OrderInsensitiveListComparison`. -/
def orderInsensitiveListCmp {α : Type} (cmp : α → α → Ordering) (l1 l2 : List α) : Ordering :=
  if l1.length != l2.length then
    -- shorter list sorts later (matches C# `arr1.Length < arr2.Length ? 1 : -1`)
    if l1.length < l2.length then .gt else .lt
  else
    (sortBy cmp l1).zip (sortBy cmp l2) |>.foldl
      (fun acc (a, b) => if acc != .eq then acc else cmp a b) .eq

#eval orderInsensitiveListCmp compare [1, 2, 3] [3, 1, 2]  -- .eq  (same multiset)
#eval orderInsensitiveListCmp compare [1, 2, 3] [1, 2, 4]  -- .lt  (3 < 4)
#eval orderInsensitiveListCmp compare [1, 2]    [1, 2, 3]  -- .gt  (shorter list sorts later)

/-! ## Path comparison functions -/

/-- Compare two `PathSegment`s given current vertex rankings and between-ranks.
    Mirrors C# `ComparePathSegments`.

    Sort directions (matching C#):
    - `bottom` : ascending by vertex type
    - `inner`  : descending by sub-path rank, then descending by edge weight -/
def comparePathSegments
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    : PathSegment → PathSegment → Ordering
  | .bottom xi,             .bottom yi =>
      compare (vertexTypes.getD xi 0) (vertexTypes.getD yi 0)
  | .inner xe xd xs xm,    .inner ye yd ys ym =>
      let rx := betweenRanks xd xs xm
      let ry := betweenRanks yd ys ym
      if rx != ry then compare ry rx          -- smaller sub-path rank sorts later
      else if xe != ye then compare ye xe     -- smaller edge weight sorts later
      else .eq
  | _, _ => panic! "Cannot compare bottom and inner PathSegments"

/-- Compare two `PathsBetween` values.  Mirrors C# `ComparePathsBetween`. -/
def comparePathsBetween
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (x y : PathsBetween) : Ordering :=
  let ex := vertexTypes.getD x.endVertexIndex 0
  let ey := vertexTypes.getD y.endVertexIndex 0
  if ex != ey then compare ex ey
  else orderInsensitiveListCmp (comparePathSegments vertexTypes betweenRanks)
         x.connectedSubPaths y.connectedSubPaths

/-- Compare two `PathsFrom` values.  Mirrors C# `ComparePathsFrom`. -/
def comparePathsFrom
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (x y : PathsFrom) : Ordering :=
  let sx := vertexTypes.getD x.startVertexIndex 0
  let sy := vertexTypes.getD y.startVertexIndex 0
  if sx != sy then compare sx sy
  else orderInsensitiveListCmp (comparePathsBetween vertexTypes betweenRanks)
         x.pathsToVertex y.pathsToVertex

/-! ## Smoke tests for comparison functions -/

private def vt : Array VertexType := #[0, 1, 2]
private def br : Nat → Nat → Nat → Int := fun _ _ _ => 0

-- bottom 0 (type 0) < bottom 1 (type 1)
#eval comparePathSegments vt br (.bottom 0) (.bottom 1)  -- .lt
-- same type → .eq
#eval comparePathSegments vt br (.bottom 2) (.bottom 2)  -- .eq
-- inner: equal ranks, larger edge sorts first (compare ye xe where ye=5, xe=2 → .gt)
#eval comparePathSegments vt br (.inner 2 0 0 1) (.inner 5 0 0 1)  -- .gt (xe=2 < ye=5)

end Graph
