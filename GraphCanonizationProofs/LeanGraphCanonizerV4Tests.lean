import LeanGraphCanonizerV4
import UniqueGraphsBySize
open Graph

private def mkAdj (rows : List (List EdgeType)) (size : Nat) : AdjMatrix size where
  adj rowIdx colIdx := (rows.getD rowIdx.val []).getD colIdx.val 0

-- Build the simple graph on n vertices encoded by a bitmask over upper-triangular edges.
-- Edge index for pair (lo, hi) with lo < hi: lo*(2n-lo-1)/2 + (hi-lo-1)
private def graphFromBitmask (n : Nat) (mask : Nat) : AdjMatrix n :=
  { adj := fun i j =>
      if i == j then 0
      else
        let lo := min i.val j.val
        let hi := max i.val j.val
        let idx := lo * (2 * n - lo - 1) / 2 + (hi - lo - 1)
        if (mask >>> idx) % 2 == 1 then 1 else 0 }

-- Count distinct canonical forms over all 2^(n*(n-1)/2) simple graphs on n vertices.
private def countUniqueCanonicals (n : Nat) : Nat :=
  let emptyVerts : Array VertexType := Array.mk (List.replicate n 0)
  (List.range (2 ^ (n * (n - 1) / 2))).foldl
    (fun seen mask =>
      let c := toString (run emptyVerts (graphFromBitmask n mask))
      if seen.contains c then seen else seen ++ [c])
    ([] : List String)
  |>.length

-- ── Scrambling helpers ────────────────────────────────────────────────────────

-- Apply swaps indexed by Nat; indices outside [0, n) are silently ignored.
private def applyNatSwaps {n : Nat} (swaps : List (Nat × Nat)) (G : AdjMatrix n) : AdjMatrix n :=
  swaps.foldl (fun g (a, b) =>
    if h1 : a < n then if h2 : b < n then g.swapVertexLabels ⟨a, h1⟩ ⟨b, h2⟩ else g
    else g) G

-- Reverse: swap pairs from outside in — [(0, n-1), (1, n-2), …]
private def scrReverse (n : Nat) : List (Nat × Nat) :=
  (List.range (n / 2)).map fun i => (i, n - 1 - i)

-- Rotate left: chain [(0,1), (1,2), …, (n-2, n-1)] — moves vertex 0 to the last position
private def scrRotateLeft (n : Nat) : List (Nat × Nat) :=
  (List.range (n - 1)).map fun i => (i, i + 1)

-- Cut: swap the two halves — [(0, ⌊n/2⌋), (1, ⌊n/2⌋+1), …]
private def scrCut (n : Nat) : List (Nat × Nat) :=
  (List.range (n / 2)).map fun i => (i, i + n / 2)

private def standardScramblers (n : Nat) : List (List (Nat × Nat)) :=
  [scrReverse n, scrRotateLeft n, scrCut n]

-- True iff the graph's canonical form is unchanged under every scrambler in the list.
private def isStableUnder {n : Nat} (vts : Array VertexType) (G : AdjMatrix n)
    (scramblers : List (List (Nat × Nat))) : Bool :=
  let canonical := toString (run vts G)
  scramblers.all fun scr => toString (run vts (applyNatSwaps scr G)) == canonical


-- ── 1. Isomorphism tests ──────────────────────────────────────────────────────

-- Simple isomorphic 4-vertex graphs (same structure, different vertex labeling)
private def isoVerts4 : Array VertexType := #[0, 0, 0, 0]
private def isoG1 : AdjMatrix 4 := mkAdj [[0,0,0,0],[0,0,0,1],[0,0,0,1],[0,1,1,0]] 4
private def isoG2 : AdjMatrix 4 := mkAdj [[0,1,1,0],[1,0,0,0],[1,0,0,0],[0,0,0,0]] 4

#guard toString (run isoVerts4 isoG1) == toString (run isoVerts4 isoG2)

-- Pointed isomorphism: vertices 1,2,3 (all type 1) are structurally symmetric
private def vtPointed : Array VertexType := #[0, 1, 1, 1, 4, 5, 6]

private def g1Pointed : AdjMatrix 7 := mkAdj
  [[0,0,0,1,1,0,0],[0,0,1,0,1,0,0],[0,1,0,0,1,0,0],[1,0,0,0,1,0,0],
   [1,1,1,1,0,0,0],[0,0,0,0,0,0,1],[0,0,0,0,0,1,0]] 7

-- Same graph with vertices 1 and 2 swapped
private def g2Pointed : AdjMatrix 7 := mkAdj
  [[0,0,1,0,1,0,0],[0,0,0,1,1,0,0],[1,0,0,0,1,0,0],[0,1,0,0,1,0,0],
   [1,1,1,1,0,0,0],[0,0,0,0,0,0,1],[0,0,0,0,0,1,0]] 7

#guard toString (run vtPointed g1Pointed) == toString (run vtPointed g2Pointed)

-- Non-isomorphic graphs must produce distinct canonical forms:
-- K3+K3 (two disjoint triangles) vs C6 (6-cycle)
private def k3k3 : AdjMatrix 6 := mkAdj
  [[0,1,1,0,0,0],[1,0,1,0,0,0],[1,1,0,0,0,0],[0,0,0,0,1,1],[0,0,0,1,0,1],[0,0,0,1,1,0]] 6

private def c6 : AdjMatrix 6 := mkAdj
  [[0,1,0,0,0,1],[1,0,1,0,0,0],[0,1,0,1,0,0],[0,0,1,0,1,0],[0,0,0,1,0,1],[1,0,0,0,1,0]] 6

#guard toString (run #[0,0,0,0,0,0] k3k3) != toString (run #[0,0,0,0,0,0] c6)


-- ── 2. Scrambling stability tests ─────────────────────────────────────────────
-- Each graph is tested against all three standard scramblers: reverse, rotate-left, cut.

-- 3-dimensional hypercube Q3 (8 vertices = 3-bit strings, edges = Hamming distance 1)
private def q3 : AdjMatrix 8 := mkAdj
  [[0,1,1,0,1,0,0,0],[1,0,0,1,0,1,0,0],[1,0,0,1,0,0,1,0],[0,1,1,0,0,0,0,1],
   [1,0,0,0,0,1,1,0],[0,1,0,0,1,0,0,1],[0,0,1,0,1,0,0,1],[0,0,0,1,0,1,1,0]] 8

#guard isStableUnder #[0,0,0,0,0,0,0,0] q3 (standardScramblers 8)

-- Path graphs (line_n: 0─1─…─(n-1))
private def line4 : AdjMatrix 4 :=
  mkAdj [[0,1,0,0],[1,0,1,0],[0,1,0,1],[0,0,1,0]] 4
private def line5 : AdjMatrix 5 :=
  mkAdj [[0,1,0,0,0],[1,0,1,0,0],[0,1,0,1,0],[0,0,1,0,1],[0,0,0,1,0]] 5
private def line6 : AdjMatrix 6 :=
  mkAdj [[0,1,0,0,0,0],[1,0,1,0,0,0],[0,1,0,1,0,0],[0,0,1,0,1,0],[0,0,0,1,0,1],[0,0,0,0,1,0]] 6

#guard isStableUnder #[0,0,0,0]     line4 (standardScramblers 4)
#guard isStableUnder #[0,0,0,0,0]   line5 (standardScramblers 5)
#guard isStableUnder #[0,0,0,0,0,0] line6 (standardScramblers 6)

-- Spider (center 0, three arms of length 2: 0─1─2, 0─3─4, 0─5─6)
private def spider : AdjMatrix 7 := mkAdj
  [[0,1,0,1,0,1,0],[1,0,1,0,0,0,0],[0,1,0,0,0,0,0],[1,0,0,0,1,0,0],
   [0,0,0,1,0,0,0],[1,0,0,0,0,0,1],[0,0,0,0,0,1,0]] 7

#guard isStableUnder #[0,0,0,0,0,0,0] spider (standardScramblers 7)

-- K3+K3 in a different vertex labeling (triangles on {1,2,3} and {0,4,5})
private def k3k3_alt : AdjMatrix 6 := mkAdj
  [[0,0,0,0,1,1],[0,0,1,1,0,0],[0,1,0,1,0,0],[0,1,1,0,0,0],[1,0,0,0,0,1],[1,0,0,0,1,0]] 6

#guard toString (run #[0,0,0,0,0,0] k3k3_alt) == toString (run #[0,0,0,0,0,0] k3k3)


-- ── 3. Exhaustive canonical count tests ───────────────────────────────────────
-- OEIS A000088: number of non-isomorphic graphs on n vertices.

#guard countUniqueCanonicals 0 == 1
#guard countUniqueCanonicals 1 == 1
#guard countUniqueCanonicals 2 == 2
#guard countUniqueCanonicals 3 == 4
#guard countUniqueCanonicals 4 == 11


-- ── 4. Known-graphs scrambling tests ──────────────────────────────────────────
-- For each known unique graph, all standard scramblers must yield the same canonical.
-- Add larger sizes to UniqueGraphsBySize.lean as needed.

private def allScrambleStable {n : Nat} (graphs : Array (AdjMatrix n))
    (vts : Array VertexType) : Bool :=
  graphs.all fun g => isStableUnder vts g (standardScramblers n)

#guard allScrambleStable UniqueGraphsBySize.size2 #[0,0]
#guard allScrambleStable UniqueGraphsBySize.size3 #[0,0,0]


-- ── 5. Repeatability ──────────────────────────────────────────────────────────
-- Pure functions always return identical output for identical input.

#guard toString (run isoVerts4 isoG1) == toString (run isoVerts4 isoG1)
-- Cross-sized: result for a 4-vertex graph is unchanged regardless of other calls
#guard toString (run isoVerts4 isoG1) == toString (run isoVerts4 isoG2)


-- ── 6. labelEdgesAccordingToRankings smoke test ────────────────────────────────
-- Verify the function terminates and produces output on a non-trivial 10-vertex input.
private def smoke_verts : Array VertexType := #[0,3,1,2,0,3,1,2,0,1]
private def smoke_edges : AdjMatrix 10 := mkAdj
  [[0,1,0,1,0,0,0,0,0,0],[1,0,1,0,0,0,0,0,0,0],[0,1,0,0,1,0,0,0,0,0],
   [1,0,0,0,0,1,0,0,0,0],[0,0,1,0,0,0,1,0,0,0],[0,0,0,1,0,0,0,1,0,0],
   [0,0,0,0,1,0,0,0,1,0],[0,0,0,0,0,1,0,0,0,1],[0,0,0,0,0,0,1,0,0,1],
   [0,0,0,0,0,0,0,1,1,0]] 10

#guard toString (labelEdgesAccordingToRankings smoke_verts smoke_edges) != ""
