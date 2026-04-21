import Mathlib.Tactic
import Aesop
open Nat

namespace Graph

abbrev VertexType := Int
abbrev EdgeType   := Int

/-! ## Adjacency matrix -/

structure AdjMatrix (n : Nat) where
  adj : Fin n → Fin n → EdgeType

namespace AdjMatrix

variable {n : Nat}

def swapVertices (i j : Fin n) (G : AdjMatrix n) : AdjMatrix n :=
  { adj := fun u v =>
      let u' := if u = i then j else if u = j then i else u
      let v' := if v = i then j else if v = j then i else v
      G.adj u' v' }

inductive Isomorphic : AdjMatrix n → AdjMatrix n → Prop
  | refl  (G : AdjMatrix n)               : Isomorphic G G
  | swap  (G : AdjMatrix n) (i j : Fin n) : Isomorphic G (swapVertices i j G)
  | trans {G₁ G₂ G₃ : AdjMatrix n}
      : Isomorphic G₁ G₂ → Isomorphic G₂ G₃ → Isomorphic G₁ G₃

@[inherit_doc] scoped infixl:50 " ≃ " => Isomorphic

def adjToString (G : AdjMatrix n) : String :=
  let rows := List.finRange n
  let rowStrings := rows.map fun i =>
    let rowString := (List.finRange n).map fun j => toString (G.adj i j)
    String.join (rowString.intersperse " ")
  String.join (rowStrings.intersperse "\n")

instance : ToString (AdjMatrix n) := ⟨adjToString⟩

end AdjMatrix

/-! ## Path structures -/

inductive PathSegment where
  | bottom (vertexIndex : Nat)                                     : PathSegment
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
  n             : Nat
  pathsOfLength : Array (Array PathsFrom)

structure RankState where
  betweenRanks : Array (Array (Array Int))
  fromRanks    : Array (Array Int)

def RankState.getBetween (rs : RankState) (d s e : Nat) : Int :=
  ((rs.betweenRanks.getD d #[]).getD s #[]).getD e 0

def RankState.getFrom (rs : RankState) (d s : Nat) : Int :=
  (rs.fromRanks.getD d #[]).getD s 0

/-! ## Helpers -/

def getArrayRank (arr : Array VertexType) : Array VertexType :=
  arr.map fun v => arr.foldl (fun acc w => if w < v then acc + 1 else acc) 0

#eval getArrayRank #[0, 10, 5, 5, 11]  -- #[0, 3, 1, 1, 4]
#eval getArrayRank #[0, 0, 0]           -- #[0, 0, 0]
#eval getArrayRank #[3, 1, 2]           -- #[2, 0, 1]

def insertSorted {α : Type} (cmp : α → α → Ordering) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if cmp x y != .gt then x :: y :: ys else y :: insertSorted cmp x ys

def sortBy {α : Type} (cmp : α → α → Ordering) : List α → List α
  | []      => []
  | x :: xs => insertSorted cmp x (sortBy cmp xs)

#eval sortBy compare [3, 1, 4, 1, 5, 9, 2, 6]  -- [1, 1, 2, 3, 4, 5, 6, 9]

def orderInsensitiveListCmp {α : Type} (cmp : α → α → Ordering) (l1 l2 : List α) : Ordering :=
  if l1.length != l2.length then
    if l1.length < l2.length then .gt else .lt
  else
    (sortBy cmp l1).zip (sortBy cmp l2) |>.foldl
      (fun acc (a, b) => if acc != .eq then acc else cmp a b) .eq

#eval orderInsensitiveListCmp compare [1, 2, 3] [3, 1, 2]  -- .eq
#eval orderInsensitiveListCmp compare [1, 2, 3] [1, 2, 4]  -- .lt
#eval orderInsensitiveListCmp compare [1, 2]    [1, 2, 3]  -- .gt

/-! ## Comparison functions -/

def comparePathSegments
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    : PathSegment → PathSegment → Ordering
  | .bottom xi,         .bottom yi         =>
      compare (vertexTypes.getD xi 0) (vertexTypes.getD yi 0)
  | .inner xe xd xs xm, .inner ye yd ys ym =>
      let rx := betweenRanks xd xs xm
      let ry := betweenRanks yd ys ym
      if rx != ry then compare ry rx
      else if xe != ye then compare ye xe
      else .eq
  | _, _ => panic! "Cannot compare bottom and inner PathSegments"

def comparePathsBetween
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (x y : PathsBetween) : Ordering :=
  let ex := vertexTypes.getD x.endVertexIndex 0
  let ey := vertexTypes.getD y.endVertexIndex 0
  if ex != ey then compare ex ey
  else orderInsensitiveListCmp (comparePathSegments vertexTypes betweenRanks)
         x.connectedSubPaths y.connectedSubPaths

def comparePathsFrom
    (vertexTypes  : Array VertexType)
    (betweenRanks : Nat → Nat → Nat → Int)
    (x y : PathsFrom) : Ordering :=
  let sx := vertexTypes.getD x.startVertexIndex 0
  let sy := vertexTypes.getD y.startVertexIndex 0
  if sx != sy then compare sx sy
  else orderInsensitiveListCmp (comparePathsBetween vertexTypes betweenRanks)
         x.pathsToVertex y.pathsToVertex

/-! ## Path initialization -/

def initializePaths {n : Nat} (G : AdjMatrix n) : PathState :=
  let fins := List.finRange n
  { n := n
    pathsOfLength := fins.toArray.map fun depth =>
      fins.toArray.map fun from_ =>
        { depth            := depth.val
          startVertexIndex := from_.val
          pathsToVertex    :=
            fins.map fun to_ =>
              { depth            := depth.val
                startVertexIndex := from_.val
                endVertexIndex   := to_.val
                connectedSubPaths :=
                  if depth.val = 0 then
                    if from_ = to_ then [.bottom from_.val] else []
                  else
                    fins.map fun mid =>
                      .inner (G.adj mid to_) (depth.val - 1) from_.val mid.val } } }

/-! ## Ranking -/

-- Assign ranks to a sorted list: rank = index of the first element in the equivalence class.
-- e.g. for sorted [a,a,b,c]: [(a,0),(a,0),(b,2),(c,3)]
private def assignRanks {α : Type} (cmp : α → α → Ordering) (sorted : List α)
    : List (α × Int) :=
  let (rev, _) := sorted.foldl
    (fun acc x =>
      let (revList, lastEntry) : List (α × Int) × Option (α × Int) := acc
      let rank : Int :=
        match lastEntry with
        | none           => 0
        | some (prev, r) => if cmp prev x == .eq then r else Int.ofNat revList.length
      ((x, rank) :: revList, some (x, rank)))
    (([] : List (α × Int)), none)
  rev.reverse

private def setBetween (br : Array (Array (Array Int)))
    (d s e : Nat) (rank : Int) : Array (Array (Array Int)) :=
  let da := br.getD d #[]
  let sa := da.getD s #[]
  br.set! d (da.set! s (sa.set! e rank))

def calculatePathRankings (state : PathState) (vertexTypes : Array VertexType) : RankState :=
  let n := state.n
  let zero3 : Array (Array (Array Int)) :=
    (Array.range n).map fun _ => (Array.range n).map fun _ => (Array.range n).map fun _ => (0 : Int)
  let zero2 : Array (Array Int) :=
    (Array.range n).map fun _ => (Array.range n).map fun _ => (0 : Int)
  let (br, fr) := (List.range n).foldl
    (fun (acc : Array (Array (Array Int)) × Array (Array Int)) depth =>
      let (br, fr) := acc
      let pathsAtDepth  := (state.pathsOfLength.getD depth #[]).toList
      let allBetween    := pathsAtDepth.foldl (fun acc pf => acc ++ pf.pathsToVertex) []
      let brFn : Nat → Nat → Nat → Int := fun d s e => ((br.getD d #[]).getD s #[]).getD e 0
      let cmpB          := comparePathsBetween vertexTypes brFn
      let br'           := (assignRanks cmpB (sortBy cmpB allBetween)).foldl
                            (fun (b : Array (Array (Array Int))) item =>
                              let (pb, rank) := item
                              setBetween b depth pb.startVertexIndex pb.endVertexIndex rank)
                            br
      let brFn' : Nat → Nat → Nat → Int := fun d s e => ((br'.getD d #[]).getD s #[]).getD e 0
      let cmpF          := comparePathsFrom vertexTypes brFn'
      let fr'           := (assignRanks cmpF (sortBy cmpF pathsAtDepth)).foldl
                            (fun (f : Array (Array Int)) item =>
                              let (pf, rank) := item
                              let da := f.getD depth #[]
                              f.set! depth (da.set! pf.startVertexIndex rank))
                            fr
      (br', fr'))
    (zero3, zero2)
  { betweenRanks := br, fromRanks := fr }

/-! ## Vertex ordering -/

private def convergeOnce (state : PathState) (vt : Array VertexType)
    : Array VertexType × Bool :=
  let rs := calculatePathRankings state vt
  let n  := state.n
  (List.range n).foldl
    (fun acc i =>
      let (arr, changed) : Array VertexType × Bool := acc
      let newRank := rs.getFrom (n - 1) i
      if newRank != arr.getD i 0 then (arr.set! i newRank, true)
      else (arr, changed))
    (vt, false)

private def convergeLoop (state : PathState) (vt : Array VertexType) : Nat → Array VertexType
  | 0        => vt
  | fuel + 1 =>
    let (vt', changed) := convergeOnce state vt
    if changed then convergeLoop state vt' fuel else vt'

private def breakTie (vt : Array VertexType) (target : Int) : Array VertexType × Bool :=
  let result := (List.range vt.size).foldl
    (fun acc i =>
      let (arr, firstAppearance, changed) : Array VertexType × Bool × Bool := acc
      if arr.getD i 0 == target then
        if firstAppearance then (arr, false, changed)
        else (arr.set! i (target + 1), false, true)
      else (arr, firstAppearance, changed))
    (vt, true, false)
  let (arr, _, changed) := result
  (arr, changed)

def orderVertices (state : PathState) (vt : Array VertexType) : Array VertexType :=
  (List.range state.n).foldl
    (fun vt fullySorted =>
      let vt := convergeLoop state vt state.n
      (breakTie vt (Int.ofNat fullySorted)).1)
    vt

/-! ## Edge labeling -/

private def computeDenseRanks (n : Nat) (vertexRankings : Array VertexType) : Array Nat :=
  let pairs : List (VertexType × Nat) := (List.range n).map fun i => (vertexRankings.getD i 0, i)
  let cmp : (VertexType × Nat) → (VertexType × Nat) → Ordering :=
    fun p1 p2 => if p1.1 != p2.1 then compare p1.1 p2.1 else compare p1.2 p2.2
  let sorted := sortBy cmp pairs
  (List.range sorted.length).foldl
    (fun (arr : Array Nat) i => arr.set! (sorted.getD i (0, 0)).2 i)
    ((Array.range n).map fun _ => 0)

def labelEdgesAccordingToRankings {n : Nat}
    (vertexRankings : Array VertexType) (G : AdjMatrix n) : AdjMatrix n :=
  let fins     := List.finRange n
  let rankings := computeDenseRanks n vertexRankings
  (fins.foldl
    (fun (acc : AdjMatrix n × Array Nat) fi =>
      let (g, ranks) := acc
      let i := fi.val
      match fins.find? (fun fk => ranks.getD fk.val 0 == i) with
      | none    => (g, ranks)
      | some fj =>
        let j      := fj.val
        let g'     := g.swapVertices fi fj
        let rankJ  := ranks.getD j 0
        let rankI  := ranks.getD i 0
        (g', (ranks.set! j rankI).set! i rankJ))
    (G, rankings)).1

/-! ## Entry point -/

def run {n : Nat} (vertexTypes : Array VertexType) (G : AdjMatrix n) : AdjMatrix n :=
  let vt    := getArrayRank vertexTypes
  let state := initializePaths G
  let vt    := orderVertices state vt
  labelEdgesAccordingToRankings vt G

/-! ## Tests -/

private def mkAdj (rows : List (List EdgeType)) (n : Nat) : AdjMatrix n where
  adj i j := (rows.getD i.val []).getD j.val 0

-- ── 3-vertex path graph in three labelings ────────────────────────────────────
-- 0─1─2 with different vertex labelings should all canonize to the same matrix.
-- Scrambling 1: middle vertex is vertex 1 (original)
-- Scrambling 2: middle vertex is vertex 2
-- Scrambling 3: middle vertex is vertex 0

private def path3_1 : AdjMatrix 3 := mkAdj [[0,1,0],[1,0,1],[0,1,0]] 3  -- 0─1─2
private def path3_2 : AdjMatrix 3 := mkAdj [[0,0,1],[0,0,1],[1,1,0]] 3  -- 2 is middle
private def path3_3 : AdjMatrix 3 := mkAdj [[0,1,1],[1,0,0],[1,0,0]] 3  -- 0 is middle

#eval toString (run #[0,0,0] path3_1)
#eval toString (run #[0,0,0] path3_2)  -- should equal above
#eval toString (run #[0,0,0] path3_3)  -- should equal above

-- ── APointed isomorphism test ────────────────────────────────────────────────
-- Two 7-vertex graphs with distinct vertex types; vertices 1,2,3 (all type 1)
-- are structurally symmetric so swapping them should produce the same canonical form.

private def vtPointed : Array VertexType := #[0, 1, 1, 1, 4, 5, 6]

private def g1Pointed : AdjMatrix 7 := mkAdj
  [[0,0,0,1,1,0,0],
   [0,0,1,0,1,0,0],
   [0,1,0,0,1,0,0],
   [1,0,0,0,1,0,0],
   [1,1,1,1,0,0,0],
   [0,0,0,0,0,0,1],
   [0,0,0,0,0,1,0]] 7

-- Same graph with vertices 1 and 2 swapped
private def g2Pointed : AdjMatrix 7 := mkAdj
  [[0,0,1,0,1,0,0],
   [0,0,0,1,1,0,0],
   [1,0,0,0,1,0,0],
   [0,1,0,0,1,0,0],
   [1,1,1,1,0,0,0],
   [0,0,0,0,0,0,1],
   [0,0,0,0,0,1,0]] 7

#eval toString (run vtPointed g1Pointed)
#eval toString (run vtPointed g2Pointed)
#eval toString (run vtPointed g1Pointed) == toString (run vtPointed g2Pointed)  -- true

end Graph
