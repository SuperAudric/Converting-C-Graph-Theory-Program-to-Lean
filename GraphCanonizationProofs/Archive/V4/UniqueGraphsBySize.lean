import LeanGraphCanonizerV4
open Graph

namespace UniqueGraphsBySize

private def mkAdj (rows : List (List EdgeType)) (size : Nat) : AdjMatrix size where
  adj rowIdx colIdx := (rows.getD rowIdx.val []).getD colIdx.val 0

def size2 : Array (AdjMatrix 2) := #[
  mkAdj [[0,0],[0,0]] 2,   -- empty
  mkAdj [[0,1],[1,0]] 2    -- one edge
]

def size3 : Array (AdjMatrix 3) := #[
  mkAdj [[0,0,0],[0,0,0],[0,0,0]] 3,   -- empty
  mkAdj [[0,1,0],[1,0,0],[0,0,0]] 3,   -- one edge (0─1, isolated 2)
  mkAdj [[0,1,0],[1,0,1],[0,1,0]] 3,   -- path (0─1─2)
  mkAdj [[0,1,1],[1,0,1],[1,1,0]] 3    -- triangle (K3)
]

end UniqueGraphsBySize
