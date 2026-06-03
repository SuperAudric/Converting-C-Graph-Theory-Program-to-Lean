/-
ARCHIVED FEASIBILITY PROBE (2026-06-03). Inert reference code: the `#eval`s are
commented out so opening this file triggers no computation. To re-run, uncomment
them and run `lean docs/Archive/ChainDescent/probe.lean`.

Efficient standalone 1-WL probe (no Mathlib, no encode-blowup).

Models the EXACT `hdiscSet` question of `matchOracleSet_cellComplete`:
does `warmRefine` discretize under
  • UNIFORM marking:  D indexed (distinct) + R one shared colour      (= indivWithSet D R)
  • INDEXED marking:  D∪R all distinct                                (= individualizedColouring (D∪R))
We compute the 1-WL PARTITION only (small renumbered colours), which is all
that discreteness depends on — identical partition to the project's `warmRefine`.

Question (depth-bound framing): how much extra *committed/indexed* depth does
the UNIFORM marking cost vs INDEXED, and does the penalty track NON-abelianness
of the marked set's internal symmetry (Kₘ=Sₘ vs Cₘ=Z₂ flips)?
-/

-- insertion sort on Nat (dependency-free, stable enough for a canonical key list)
def insertNat : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys => if Nat.ble x y then x :: y :: ys else y :: insertNat x ys
def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNat xs)

abbrev Adj := Array (Array Nat)          -- adj[v]![u]! ∈ {0,1}
abbrev Col := Array Nat

-- 1-WL signature of v: sorted list of keys (adj-label, neighbour-colour) encoded as one Nat.
def sigOf (n : Nat) (adj : Adj) (col : Col) (v : Nat) : List Nat :=
  sortNat <| (List.range n).map (fun u => (adj[v]!)[u]! * (n + 2) + col[u]!)

-- one refinement round: recolour each vertex by (old colour, signature), renumbered to 0..n-1
def refineOnce (n : Nat) (adj : Adj) (col : Col) : Col :=
  let key : Nat → List Nat := fun v => col[v]! :: sigOf n adj col v
  let keys : Array (List Nat) := (Array.range n).map key
  -- colour[v] = index of first w with equal key  (valid partition labelling)
  (Array.range n).map (fun v =>
    ((List.range n).find? (fun w => keys[w]! == keys[v]!)).getD v)

-- iterate n rounds (1-WL stabilizes within n rounds)
def warmWL (n : Nat) (adj : Adj) (col : Col) : Col :=
  Nat.rec col (fun _ c => refineOnce n adj c) n

def isDiscrete (n : Nat) (col : Col) : Bool :=
  -- all colours distinct ⇔ #distinct = n
  let cs := (List.range n).map (fun v => col[v]!)
  (cs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).length == n

-- initial colourings -------------------------------------------------------
-- D = {0,..,k-1} indexed distinct (colours 1..k); rest colour 0
def colIndexed (n k : Nat) : Col :=
  (Array.range n).map (fun v => if v < k then v + 1 else 0)
-- D = {0,..,k-1} indexed (1..k); R = {k,..,n-1} one shared colour (n+1); [no rest]
def colUniform (n k : Nat) : Col :=
  (Array.range n).map (fun v => if v < k then v + 1 else n + 1)

def uniformDisc (n : Nat) (adj : Adj) (k : Nat) : Bool :=
  isDiscrete n (warmWL n adj (colUniform n k))
def indexedDisc (n : Nat) (adj : Adj) (k : Nat) : Bool :=
  isDiscrete n (warmWL n adj (colIndexed n k))

def minK (n : Nat) (f : Nat → Bool) : Nat :=
  ((List.range (n + 1)).find? f).getD (n + 1)

def table (n : Nat) (adj : Adj) : List (Nat × Bool × Bool) :=
  (List.range (n + 1)).map (fun k => (k, uniformDisc n adj k, indexedDisc n adj k))

-- graph families ----------------------------------------------------------
def adjK (n : Nat) : Adj :=
  (Array.range n).map (fun i => (Array.range n).map (fun j => if i == j then 0 else 1))
def adjC (n : Nat) : Adj :=
  (Array.range n).map (fun i => (Array.range n).map (fun j =>
    if (i + 1) % n == j || (j + 1) % n == i then 1 else 0))

-- ===== validation against the known Lean datapoint: K4 =====
-- expected: table = [(0,F,F),(1,F,F),(2,F,F),(3,T,T),(4,T,T)]   minK=(3,3)
-- #eval table 4 (adjK 4)
-- #eval (minK 4 (uniformDisc 4 (adjK 4)), minK 4 (indexedDisc 4 (adjK 4)))

-- ===== Kₘ : non-abelian Sₘ internal symmetry =====
-- #eval (List.range 5).map (fun m => let n := m+3;
--   (n, minK n (uniformDisc n (adjK n)), minK n (indexedDisc n (adjK n))))   -- K3..K7  → (2,2),(3,3),(4,4),(5,5),(6,6)

-- ===== Cₘ : dihedral, Z₂ flips (abelian involutions) =====
-- #eval (List.range 8).map (fun m => let n := m+3;
--   (n, minK n (uniformDisc n (adjC n)), minK n (indexedDisc n (adjC n))))   -- C3..C10  → all (2,2)
