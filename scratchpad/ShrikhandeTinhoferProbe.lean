/-
PROBE (2026-07-30, not part of `build.sh`, no theorems): which cell does `chooseIdK` pick
on the Shrikhande graph after one individualization?

Shrikhande = Cay(Z4 x Z4, {+-(0,1), +-(1,0), +-(1,1)}), n = 16, vertex-transitive,
|Aut| = 192, |Aut_v| = 12.  After individualizing one vertex the 1-WL cells are
{v}, N(v) (6), rest (9); the 9-cell is NOT a single Aut_v-orbit (it splits 3 + 6, forced:
9 does not divide 12), the 6-cell IS.  So `Tinhofer` for this graph is decided entirely by
which of the two `chooseIdK` names -- i.e. by the colour-id numbering of `warmRefineVec`.

`#eval` only (no `native_decide`, no theorems, nothing imported by `build.sh`).
-/
import ChainDescent.DeepenTinhofer

namespace ShrikhandeProbe

open ChainDescent
open ChainDescent.Deepen

def shrEdges : List (Nat × Nat) :=
  [(0,1), (0,3), (0,4), (0,5), (0,12), (0,15), (1,2), (1,5), (1,6), (1,12), (1,13),
   (2,3), (2,6), (2,7), (2,13), (2,14), (3,4), (3,7), (3,14), (3,15), (4,5), (4,7),
   (4,8), (4,9), (5,6), (5,9), (5,10), (6,7), (6,10), (6,11), (7,8), (7,11), (8,9),
   (8,11), (8,12), (8,13), (9,10), (9,13), (9,14), (10,11), (10,14), (10,15), (11,12),
   (11,15), (12,13), (12,15), (13,14), (14,15)]

def shr : AdjMatrix 16 :=
  ⟨fun i j => if shrEdges.contains (i.val, j.val) || shrEdges.contains (j.val, i.val)
              then 1 else 0⟩

def root : Colouring 16 := (Refine.warmRefineVec shr (fun _ => 0)).col

def v0 : Fin 16 := ⟨0, by decide⟩

/-- The colouring one `step` below the root. -/
def child : Colouring 16 := (step shr root v0).col

/-- The `chooseIdK`-faithful descent, reporting `(picked cid, that cell's members)`. -/
partial def trace (χ : Colouring 16) (fuel : Nat) : List (Nat × List Nat) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match chooseIdK (List.finRange 16) χ with
      | none => []
      | some cid =>
          let cell := (List.finRange 16).filter (fun v => χ v == cid)
          (cid, cell.map (fun (w : Fin 16) => w.val)) :: trace ((step shr χ (cell.headD v0)).col) fuel

-- degree check: 6-regular, so the object really is the Shrikhande graph
#eval (List.finRange 16).map (fun v => (List.finRange 16).foldl
        (fun a u => a + shr.adj v u) 0)
-- the root is a single cell (vertex-transitive, as expected)
#eval ((List.finRange 16).map root).eraseDups
-- the colouring one individualization down: colour of every vertex
#eval (List.finRange 16).map child
-- cell sizes by colour id, ascending in id
#eval (((List.finRange 16).map child).eraseDups.mergeSort (fun (a b : Nat) => a ≤ b)).map
        (fun c => (c, ((List.finRange 16).filter (fun v => child v == c)).length))
-- ★ THE QUESTION: which cell does chooseIdK name, and how big is it?
#eval chooseIdK (List.finRange 16) child
#eval match chooseIdK (List.finRange 16) child with
      | none => []
      | some cid => ((List.finRange 16).filter (fun v => child v == cid)).map (fun (w : Fin 16) => w.val)
-- and the whole faithful descent from that node
#eval trace child 16

end ShrikhandeProbe
