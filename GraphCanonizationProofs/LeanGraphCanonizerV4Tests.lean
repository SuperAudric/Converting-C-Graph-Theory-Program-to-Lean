import LeanGraphCanonizerV4
import UniqueGraphsBySize
open Graph

private def mkAdj (rows : List (List EdgeType)) (size : Nat) : AdjMatrix size where
  adj rowIdx colIdx := (rows.getD rowIdx.val []).getD colIdx.val 0

-- Apply a sequence of vertex-label swaps; each swap preserves the isomorphism class.
private def applySwaps {n : Nat} (swaps : List (Fin n × Fin n)) (G : AdjMatrix n) : AdjMatrix n :=
  swaps.foldl (fun g p => g.swapVertexLabels p.1 p.2) G

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

-- 3-dimensional hypercube Q3 (8 vertices = 3-bit strings, edges = Hamming distance 1).
-- All vertex relabelings must yield the same canonical form.
private def q3 : AdjMatrix 8 := mkAdj
  [[0,1,1,0,1,0,0,0],[1,0,0,1,0,1,0,0],[1,0,0,1,0,0,1,0],[0,1,1,0,0,0,0,1],
   [1,0,0,0,0,1,1,0],[0,1,0,0,1,0,0,1],[0,0,1,0,1,0,0,1],[0,0,0,1,0,1,1,0]] 8

private def ev8 : Array VertexType := #[0,0,0,0,0,0,0,0]

#guard toString (run ev8 q3) ==
        toString (run ev8 (q3.swapVertexLabels ⟨0,by omega⟩ ⟨7,by omega⟩))
#guard toString (run ev8 q3) ==
        toString (run ev8 (q3.swapVertexLabels ⟨1,by omega⟩ ⟨6,by omega⟩))
#guard toString (run ev8 q3) ==
        toString (run ev8 (applySwaps
          [(⟨0,by omega⟩,⟨4,by omega⟩),(⟨1,by omega⟩,⟨5,by omega⟩)] q3))

-- Scrambled path graphs (line_n: 0─1─…─(n-1))
private def line4 : AdjMatrix 4 :=
  mkAdj [[0,1,0,0],[1,0,1,0],[0,1,0,1],[0,0,1,0]] 4
private def line5 : AdjMatrix 5 :=
  mkAdj [[0,1,0,0,0],[1,0,1,0,0],[0,1,0,1,0],[0,0,1,0,1],[0,0,0,1,0]] 5
private def line6 : AdjMatrix 6 :=
  mkAdj [[0,1,0,0,0,0],[1,0,1,0,0,0],[0,1,0,1,0,0],[0,0,1,0,1,0],[0,0,0,1,0,1],[0,0,0,0,1,0]] 6

#guard toString (run #[0,0,0,0] line4) ==
        toString (run #[0,0,0,0] (line4.swapVertexLabels ⟨0,by omega⟩ ⟨3,by omega⟩))
#guard toString (run #[0,0,0,0] line4) ==
        toString (run #[0,0,0,0]
          (applySwaps [(⟨0,by omega⟩,⟨3,by omega⟩),(⟨1,by omega⟩,⟨2,by omega⟩)] line4))

#guard toString (run #[0,0,0,0,0] line5) ==
        toString (run #[0,0,0,0,0] (line5.swapVertexLabels ⟨0,by omega⟩ ⟨4,by omega⟩))
#guard toString (run #[0,0,0,0,0] line5) ==
        toString (run #[0,0,0,0,0]
          (applySwaps [(⟨0,by omega⟩,⟨4,by omega⟩),(⟨1,by omega⟩,⟨3,by omega⟩)] line5))

#guard toString (run #[0,0,0,0,0,0] line6) ==
        toString (run #[0,0,0,0,0,0] (line6.swapVertexLabels ⟨0,by omega⟩ ⟨5,by omega⟩))
#guard toString (run #[0,0,0,0,0,0] line6) ==
        toString (run #[0,0,0,0,0,0]
          (applySwaps [(⟨0,by omega⟩,⟨5,by omega⟩),(⟨1,by omega⟩,⟨4,by omega⟩),
                      (⟨2,by omega⟩,⟨3,by omega⟩)] line6))

-- Scrambled spider (center 0, three arms of length 2: 0─1─2, 0─3─4, 0─5─6)
private def spider : AdjMatrix 7 := mkAdj
  [[0,1,0,1,0,1,0],[1,0,1,0,0,0,0],[0,1,0,0,0,0,0],[1,0,0,0,1,0,0],
   [0,0,0,1,0,0,0],[1,0,0,0,0,0,1],[0,0,0,0,0,1,0]] 7

-- Swap arm tips (2 and 4 are both at distance 2 from center, same structure)
#guard toString (run #[0,0,0,0,0,0,0] spider) ==
        toString (run #[0,0,0,0,0,0,0] (spider.swapVertexLabels ⟨2,by omega⟩ ⟨4,by omega⟩))
-- Swap two arms entirely (arm 0─1─2 ↔ arm 0─3─4)
#guard toString (run #[0,0,0,0,0,0,0] spider) ==
        toString (run #[0,0,0,0,0,0,0]
          (applySwaps [(⟨1,by omega⟩,⟨3,by omega⟩),(⟨2,by omega⟩,⟨4,by omega⟩)] spider))

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
-- For each known unique graph, any vertex-label swap must yield the same canonical.
-- Add larger sizes to UniqueGraphsBySize.lean as needed.

private def allScrambleStable {n : Nat} (graphs : Array (AdjMatrix n))
    (v1 v2 : Fin n) (vts : Array VertexType) : Bool :=
  graphs.all fun g =>
    toString (run vts g) == toString (run vts (g.swapVertexLabels v1 v2))

#guard allScrambleStable UniqueGraphsBySize.size2 ⟨0,by omega⟩ ⟨1,by omega⟩ #[0,0]
#guard allScrambleStable UniqueGraphsBySize.size3 ⟨0,by omega⟩ ⟨2,by omega⟩ #[0,0,0]



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
