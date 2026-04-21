import Mathlib.Tactic
import Aesop
open Nat

namespace Graph

abbrev VertexType := Int
abbrev EdgeType   := Int

/-! ## Adjacency matrix -/

structure AdjMatrix (vertexCount : Nat) where
  adj : Fin vertexCount → Fin vertexCount → EdgeType

namespace AdjMatrix

variable {vertexCount : Nat}

def swapVertices (vertex1 vertex2 : Fin vertexCount) (G : AdjMatrix vertexCount) : AdjMatrix vertexCount :=
  { adj := fun fromVertex toVertex =>
      let mappedFrom := if fromVertex = vertex1 then vertex2 else if fromVertex = vertex2 then vertex1 else fromVertex
      let mappedTo   := if toVertex   = vertex1 then vertex2 else if toVertex   = vertex2 then vertex1 else toVertex
      G.adj mappedFrom mappedTo }

inductive Isomorphic : AdjMatrix vertexCount → AdjMatrix vertexCount → Prop
  | refl  (G : AdjMatrix vertexCount)                                       : Isomorphic G G
  | swap  (G : AdjMatrix vertexCount) (vertex1 vertex2 : Fin vertexCount)   : Isomorphic G (swapVertices vertex1 vertex2 G)
  | trans {G₁ G₂ G₃ : AdjMatrix vertexCount}
      : Isomorphic G₁ G₂ → Isomorphic G₂ G₃ → Isomorphic G₁ G₃

@[inherit_doc] scoped infixl:50 " ≃ " => Isomorphic

def adjToString (G : AdjMatrix vertexCount) : String :=
  let rowIndices := List.finRange vertexCount
  let rowStrings := rowIndices.map fun rowIdx =>
    let colValues := (List.finRange vertexCount).map fun colIdx => toString (G.adj rowIdx colIdx)
    String.join (colValues.intersperse " ")
  String.join (rowStrings.intersperse "\n")

instance : ToString (AdjMatrix vertexCount) := ⟨adjToString⟩

end AdjMatrix

/-! ## Path structures -/

inductive PathSegment where
  | bottom (vertexIndex : Nat)                                    : PathSegment
  | inner  (edgeType : EdgeType) (subDepth subStart subEnd : Nat) : PathSegment
deriving Repr, BEq

structure PathsBetween where
  depth            : Nat
  startVertexIndex : Nat
  endVertexIndex   : Nat
  connectedSubPaths : List PathSegment
deriving Repr

structure PathsFrom where
  depth            : Nat
  startVertexIndex : Nat
  pathsToVertex    : List PathsBetween
deriving Repr

structure PathState where
  vertexCount   : Nat
  pathsOfLength : Array (Array PathsFrom)

structure RankState where
  betweenRanks : Array (Array (Array Int))
  fromRanks    : Array (Array Int)

def RankState.getBetween (rankState : RankState) (depth startIdx endIdx : Nat) : Int :=
  ((rankState.betweenRanks.getD depth #[]).getD startIdx #[]).getD endIdx 0

def RankState.getFrom (rankState : RankState) (depth startIdx : Nat) : Int :=
  (rankState.fromRanks.getD depth #[]).getD startIdx 0

/-! ## Helpers -/

def getArrayRank (arr : Array VertexType) : Array VertexType :=
  arr.map fun value => arr.foldl (fun smallerCount other => if other < value then smallerCount + 1 else smallerCount) 0

def insertSorted {α : Type} (cmp : α → α → Ordering) (newItem : α) : List α → List α
  | []               => [newItem]
  | listHead :: listTail => if cmp newItem listHead != .gt then newItem :: listHead :: listTail else listHead :: insertSorted cmp newItem listTail

def sortBy {α : Type} (cmp : α → α → Ordering) : List α → List α
  | []          => []
  | head :: rest => insertSorted cmp head (sortBy cmp rest)

def orderInsensitiveListCmp {α : Type} (cmp : α → α → Ordering) (list1 list2 : List α) : Ordering :=
  if list1.length != list2.length then
    if list1.length < list2.length then .gt else .lt
  else
    (sortBy cmp list1).zip (sortBy cmp list2) |>.foldl
      (fun currentOrder (elemA, elemB) => if currentOrder != .eq then currentOrder else cmp elemA elemB) .eq

/-! ## Comparison functions -/

def comparePathSegments
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    : PathSegment → PathSegment → Ordering
  | .bottom xVertexIdx,              .bottom yVertexIdx              =>
      compare (vertexTypes.getD xVertexIdx 0) (vertexTypes.getD yVertexIdx 0)
  | .inner xEdge xDepth xStart xEnd, .inner yEdge yDepth yStart yEnd =>
      let xRank := betweenRanks xDepth xStart xEnd
      let yRank := betweenRanks yDepth yStart yEnd
      if xRank != yRank then compare yRank xRank
      else if xEdge != yEdge then compare yEdge xEdge
      else .eq
  | _, _ => panic! "Cannot compare bottom and inner PathSegments"

def comparePathsBetween
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (pathX pathY : PathsBetween) : Ordering :=
  let xEndType := vertexTypes.getD pathX.endVertexIndex 0
  let yEndType := vertexTypes.getD pathY.endVertexIndex 0
  if xEndType != yEndType then compare xEndType yEndType
  else orderInsensitiveListCmp (comparePathSegments vertexTypes betweenRanks)
         pathX.connectedSubPaths pathY.connectedSubPaths

def comparePathsFrom
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (pathX pathY : PathsFrom) : Ordering :=
  let xStartType := vertexTypes.getD pathX.startVertexIndex 0
  let yStartType := vertexTypes.getD pathY.startVertexIndex 0
  if xStartType != yStartType then compare xStartType yStartType
  else orderInsensitiveListCmp (comparePathsBetween vertexTypes betweenRanks)
         pathX.pathsToVertex pathY.pathsToVertex

/-! ## Path initialization -/

def initializePaths {vertexCount : Nat} (G : AdjMatrix vertexCount) : PathState :=
  let vertices := List.finRange vertexCount
  { vertexCount := vertexCount
    pathsOfLength := vertices.toArray.map fun depthFin =>
      vertices.toArray.map fun startFin =>
        { depth            := depthFin.val
          startVertexIndex := startFin.val
          pathsToVertex    :=
            vertices.map fun endFin =>
              { depth            := depthFin.val
                startVertexIndex := startFin.val
                endVertexIndex   := endFin.val
                connectedSubPaths :=
                  if depthFin.val = 0 then
                    if startFin = endFin then [.bottom startFin.val] else []
                  else
                    vertices.map fun midFin =>
                      .inner (G.adj midFin endFin) (depthFin.val - 1) startFin.val midFin.val } } }

/-! ## Ranking -/

-- Assign ranks to a sorted list: rank = index of the first element in the equivalence class.
-- e.g. for sorted [a,a,b,c]: [(a,0),(a,0),(b,2),(c,3)]
private def assignRanks {α : Type} (cmp : α → α → Ordering) (sorted : List α)
    : List (α × Int) :=
  let (reversedList, _) := sorted.foldl
    (fun (pair : List (α × Int) × Option (α × Int)) item =>
      let (revList, lastEntry) := pair
      let rank : Int :=
        match lastEntry with
        | none                      => 0
        | some (prevItem, prevRank) => if cmp prevItem item == .eq then prevRank else Int.ofNat revList.length
      ((item, rank) :: revList, some (item, rank)))
    (([] : List (α × Int)), none)
  reversedList.reverse

private def setBetween (betweenTable : Array (Array (Array Int)))
    (depth startIdx endIdx : Nat) (rank : Int) : Array (Array (Array Int)) :=
  let depthSlice := betweenTable.getD depth #[]
  let startSlice := depthSlice.getD startIdx #[]
  betweenTable.set! depth (depthSlice.set! startIdx (startSlice.set! endIdx rank))

def calculatePathRankings (state : PathState) (vertexTypes : Array VertexType) : RankState :=
  let numVertices := state.vertexCount
  let emptyBetweenTable : Array (Array (Array Int)) :=
    (Array.range numVertices).map fun _ => (Array.range numVertices).map fun _ => (Array.range numVertices).map fun _ => (0 : Int)
  let emptyFromTable : Array (Array Int) :=
    (Array.range numVertices).map fun _ => (Array.range numVertices).map fun _ => (0 : Int)
  let (finalBetween, finalFrom) := (List.range numVertices).foldl
    (fun (accumulated : Array (Array (Array Int)) × Array (Array Int)) depth =>
      let (currentBetween, currentFrom) := accumulated
      let pathsAtDepth  := (state.pathsOfLength.getD depth #[]).toList
      let allBetween    := pathsAtDepth.foldl (fun collectedPaths pathsFrom => collectedPaths ++ pathsFrom.pathsToVertex) []
      let betweenRankFn : Nat → Nat → Nat → Int := fun rankDepth rankStart rankEnd =>
        ((currentBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
      let compareBetween  := comparePathsBetween vertexTypes betweenRankFn
      let updatedBetween  := (assignRanks compareBetween (sortBy compareBetween allBetween)).foldl
                              (fun (betweenAcc : Array (Array (Array Int))) item =>
                                let (pathBetween, rank) := item
                                setBetween betweenAcc depth pathBetween.startVertexIndex pathBetween.endVertexIndex rank)
                              currentBetween
      let updatedBetweenFn : Nat → Nat → Nat → Int := fun rankDepth rankStart rankEnd =>
        ((updatedBetween.getD rankDepth #[]).getD rankStart #[]).getD rankEnd 0
      let compareFrom     := comparePathsFrom vertexTypes updatedBetweenFn
      let updatedFrom     := (assignRanks compareFrom (sortBy compareFrom pathsAtDepth)).foldl
                              (fun (fromAcc : Array (Array Int)) item =>
                                let (pathFrom, rank) := item
                                let depthSlice := fromAcc.getD depth #[]
                                fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex rank))
                              currentFrom
      (updatedBetween, updatedFrom))
    (emptyBetweenTable, emptyFromTable)
  { betweenRanks := finalBetween, fromRanks := finalFrom }

/-! ## Vertex ordering -/

private def convergeOnce (state : PathState) (vertexTypes : Array VertexType)
    : Array VertexType × Bool :=
  let rankState   := calculatePathRankings state vertexTypes
  let numVertices := state.vertexCount
  (List.range numVertices).foldl
    (fun (pair : Array VertexType × Bool) vertexIdx =>
      let (typeArray, changed) := pair
      let newRank := rankState.getFrom (numVertices - 1) vertexIdx
      if newRank != typeArray.getD vertexIdx 0 then (typeArray.set! vertexIdx newRank, true)
      else (typeArray, changed))
    (vertexTypes, false)

private def convergeLoop (state : PathState) (vertexTypes : Array VertexType) : Nat → Array VertexType
  | 0        => vertexTypes
  | fuel + 1 =>
    let (updatedTypes, changed) := convergeOnce state vertexTypes
    if changed then convergeLoop state updatedTypes fuel else updatedTypes

private def breakTie (vertexTypes : Array VertexType) (target : Int) : Array VertexType × Bool :=
  let result := (List.range vertexTypes.size).foldl
    (fun (triple : Array VertexType × Bool × Bool) vertexIdx =>
      let (typeArray, firstAppearance, changed) := triple
      if typeArray.getD vertexIdx 0 == target then
        if firstAppearance then (typeArray, false, changed)
        else (typeArray.set! vertexIdx (target + 1), false, true)
      else (typeArray, firstAppearance, changed))
    (vertexTypes, true, false)
  let (typeArray, _, changed) := result
  (typeArray, changed)

def orderVertices (state : PathState) (vertexTypes : Array VertexType) : Array VertexType :=
  (List.range state.vertexCount).foldl
    (fun currentTypes targetPosition =>
      let convergedTypes := convergeLoop state currentTypes state.vertexCount
      (breakTie convergedTypes (Int.ofNat targetPosition)).1)
    vertexTypes

/-! ## Edge labeling -/

private def computeDenseRanks (numVertices : Nat) (vertexRankings : Array VertexType) : Array Nat :=
  let pairs : List (VertexType × Nat) := (List.range numVertices).map fun vertexIdx => (vertexRankings.getD vertexIdx 0, vertexIdx)
  let cmp : (VertexType × Nat) → (VertexType × Nat) → Ordering :=
    fun pair1 pair2 => if pair1.1 != pair2.1 then compare pair1.1 pair2.1 else compare pair1.2 pair2.2
  let sorted := sortBy cmp pairs
  (List.range sorted.length).foldl
    (fun (positionArray : Array Nat) sortedIdx => positionArray.set! (sorted.getD sortedIdx (0, 0)).2 sortedIdx)
    ((Array.range numVertices).map fun _ => 0)

def labelEdgesAccordingToRankings {vertexCount : Nat}
    (vertexRankings : Array VertexType) (G : AdjMatrix vertexCount) : AdjMatrix vertexCount :=
  let vertices     := List.finRange vertexCount
  let denseRankings := computeDenseRanks vertexCount vertexRankings
  (vertices.foldl
    (fun (accumulated : AdjMatrix vertexCount × Array Nat) currentFin =>
      let (graph, rankMap) := accumulated
      let targetPos := currentFin.val
      match vertices.find? (fun searchFin => rankMap.getD searchFin.val 0 == targetPos) with
      | none          => (graph, rankMap)
      | some sourceFin =>
        let sourceIdx    := sourceFin.val
        let swappedGraph := graph.swapVertices currentFin sourceFin
        let rankAtSource := rankMap.getD sourceIdx 0
        let rankAtTarget := rankMap.getD targetPos 0
        (swappedGraph, (rankMap.set! sourceIdx rankAtTarget).set! targetPos rankAtSource))
    (G, denseRankings)).1

/-! ## Entry point -/

def run {vertexCount : Nat} (vertexTypes : Array VertexType) (G : AdjMatrix vertexCount) : AdjMatrix vertexCount :=
  let vertexRanks  := getArrayRank vertexTypes
  let state        := initializePaths G
  let orderedRanks := orderVertices state vertexRanks
  labelEdgesAccordingToRankings orderedRanks G

end Graph
