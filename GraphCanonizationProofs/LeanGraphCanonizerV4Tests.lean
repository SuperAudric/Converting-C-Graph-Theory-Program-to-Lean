import LeanGraphCanonizerV4
open Graph

private def mkAdj (rows : List (List EdgeType)) (size : Nat) : AdjMatrix size where
  adj rowIdx colIdx := (rows.getD rowIdx.val []).getD colIdx.val 0

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

-- ── Pointed isomorphism test ─────────────────────────────────────────────────
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
