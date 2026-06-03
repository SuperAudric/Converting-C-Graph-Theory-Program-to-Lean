/-
CFI probe: does the UNIFORM-marked exploration set discretize, and at what
committed depth, for the actual CFI gauge (abelian Z₂^β) case?

Builds CFI(Kₘ) from the spec (orbit-recovery §3), validates (|V(CFI(K3))|=18;
indexed seeds discretize), then measures the matchOracleSet config:
  D seeds indexed (distinct) + remaining recovery vertices uniform + rest colour 0.
-/

-- ---------- efficient 1-WL (small renumbered colours; partition only) ----------
def insertNat : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys => if Nat.ble x y then x :: y :: ys else y :: insertNat x ys
def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNat xs)
abbrev Adj := Array (Array Nat)
abbrev Col := Array Nat
def sigOf (n : Nat) (adj : Adj) (col : Col) (v : Nat) : List Nat :=
  sortNat <| (List.range n).map (fun u => (adj[v]!)[u]! * (n + 2) + col[u]!)
def refineOnce (n : Nat) (adj : Adj) (col : Col) : Col :=
  let keys : Array (List Nat) := (Array.range n).map (fun v => col[v]! :: sigOf n adj col v)
  (Array.range n).map (fun v => ((List.range n).find? (fun w => keys[w]! == keys[v]!)).getD v)
def warmWL (n : Nat) (adj : Adj) (col : Col) : Col := Nat.rec col (fun _ c => refineOnce n adj c) n
def numColours (n : Nat) (col : Col) : Nat :=
  ((List.range n).map (fun v => col[v]!)).foldl
    (fun acc x => if acc.contains x then acc else x :: acc) [] |>.length
def isDiscrete (n : Nat) (col : Col) : Bool := numColours n col == n

-- ---------- CFI(Kₘ) construction ----------
-- base graph Kₘ: neighbours of u = everyone else
def baseN (m u : Nat) : List Nat := (List.range m).filter (fun x => x != u)
def subsetsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let r := subsetsOf xs; r ++ r.map (fun s => x :: s)
def evenSubsetsOf (l : List Nat) : List (List Nat) :=
  (subsetsOf l).filter (fun s => s.length % 2 == 0)

-- vertex descriptors: subset a_S^u  |  endpoint e^b_{u→w}
inductive CV | sub (u : Nat) (S : List Nat) | endp (u w b : Nat)
  deriving BEq, Inhabited

def cfiVerts (m : Nat) : List CV :=
  let subs := (List.range m).flatMap (fun u => (evenSubsetsOf (baseN m u)).map (fun S => CV.sub u S))
  let ends := (List.range m).flatMap (fun u =>
    (baseN m u).flatMap (fun w => [CV.endp u w 0, CV.endp u w 1]))
  subs ++ ends

-- undirected adjacency on descriptors
def adjCV : CV → CV → Nat
  | CV.sub u S, CV.endp u2 w b => if u == u2 then (if (S.contains w) != (b == 1) then 1 else 0) else 0
  | CV.endp u2 w b, CV.sub u S => if u == u2 then (if (S.contains w) != (b == 1) then 1 else 0) else 0
  | CV.endp u1 w1 b1, CV.endp u2 w2 b2 =>
      if u1 == w2 && w1 == u2 && b1 == b2 && u1 != u2 then 1 else 0
  | _, _ => 0

def isSeed : CV → Bool | CV.sub _ [] => true | _ => false

def cfiData (m : Nat) : Adj × Nat × List Nat :=
  let vs := (cfiVerts m).toArray
  let n := vs.size
  let adj : Adj := (Array.range n).map (fun i => (Array.range n).map (fun j => adjCV vs[i]! vs[j]!))
  let seeds := (List.range n).filter (fun i => isSeed vs[i]!)   -- a_∅^u indices
  (adj, n, seeds)

-- ---------- colourings ----------
-- index the first k of `marked` distinctly (1..k); the rest of `marked` one block (BIG);
-- everything else colour 0.  k = |chain.D|, (marked\firstk) = uniform exploration set.
def colMixed (n : Nat) (marked : List Nat) (k : Nat) : Col :=
  let idx : List Nat := marked.take k
  let blk : List Nat := marked.drop k
  (Array.range n).map (fun v =>
    match idx.idxOf? v with
    | some i => i + 1
    | none => if blk.contains v then n + 1 else 0)

def discAt (m : Nat) (markAll : Bool) (k : Nat) : Bool :=
  let (adj, n, seeds) := cfiData m
  -- markAll = true  → recovery set is ALL vertices; false → recovery set is the seeds
  let marked := if markAll then List.range n else seeds
  isDiscrete n (warmWL n adj (colMixed n marked k))

-- ---------- validation ----------
-- #eval let (_, n, seeds) := cfiData 3; (n, seeds.length)          -- expect (18, 3)
-- #eval let (_, n, seeds) := cfiData 4; (n, seeds.length)          -- K4 gadgets: deg3 ⇒ 2^2+6=10 each ⇒ 40, 4 seeds
-- baseline: do INDEXED seeds discretize CFI(K3)?  (k = all seeds, no uniform block)
-- #eval (List.range 4).map (fun k => (k, discAt 3 false k))        -- seeds indexed, increasing k
-- #eval (List.range 5).map (fun k => (k, discAt 4 false k))        -- CFI(K4) seeds indexed

-- ---------- the matchOracleSet measurement ----------
-- recovery set = all vertices; index first k, UNIFORM-block the rest. min k for discreteness.
-- #eval let (_, n, _) := cfiData 3;
--   (n, (List.range (n+1)).find? (fun k => discAt 3 true k))       -- CFI(K3): (18, some 4)
-- #eval let (_, n, _) := cfiData 4;
--   (n, (List.range (n+1)).find? (fun k => discAt 4 true k))       -- CFI(K4): (40, some 5)
-- compare: pure indexed (no uniform block) min recovery depth
def discIndexedOnly (m : Nat) (k : Nat) : Bool :=
  let (adj, n, _) := cfiData m
  isDiscrete n (warmWL n adj ((Array.range n).map (fun v => if v < k then v + 1 else 0)))
-- #eval let (_, n, _) := cfiData 3; (List.range (n+1)).find? (fun k => discIndexedOnly 3 k)
-- #eval let (_, n, _) := cfiData 4; (List.range (n+1)).find? (fun k => discIndexedOnly 4 k)

-- ================= THE DECISIVE HEAD-TO-HEAD =================
-- exploration set R = the seeds; committed D = ∅.  rest = colour 0.
-- colMixed seeds k:  first k seeds indexed (distinct), rest of seeds one uniform block.
--   k = |seeds|  → fully INDEXED exploration (rank-matchable, the C# model)
--   k = 0        → fully UNIFORM exploration (the current matchOracleSet model)
-- #eval let (_,_,seeds) := cfiData 4; "CFI(K4): INDEXED seeds @ D=∅ discrete?"
-- #eval let (_,_,seeds) := cfiData 4; discAt 4 false seeds.length     -- indexed R, D=∅
-- #eval "CFI(K4): UNIFORM seeds @ D=∅ discrete?"
-- #eval discAt 4 false 0                                              -- uniform R, D=∅
-- #eval "CFI(K4): UNIFORM seeds — min committed-indexed seeds to discretize:"
-- #eval let (_,_,seeds) := cfiData 4; (List.range (seeds.length+1)).find? (fun k => discAt 4 false k)
-- monotonicity sanity: indexed-D discrete ⇒ uniform-(D,R) discrete (R⊆ rest).
-- index first k vertices (any), uniform-block the seeds: never worse than indexed-only-k.
-- #eval "CFI(K5, odd deg 4): n, seeds, indexed-seed discretize depth:"
-- #eval let (_,n,seeds) := cfiData 5; (n, seeds.length, (List.range (seeds.length+1)).find? (fun k => discAt 5 false k))
