/-
PROBE (2026-07-30, not part of `build.sh`, no theorems, `#eval` only, no `native_decide`).

★★ WITNESS: `VT ⟹ Tinhofer` is FALSE.

G = Cay(Z12 :_5 Z2, S) with S = {(0,1),(1,1),(2,1),(4,1),(7,1)}, vertex (r,s) ↦ 2r+s.
n = 24, 5-regular, VERTEX-TRANSITIVE (24 left translations verified as automorphisms in
`scratchpad/probe_vt_witness.py`, and re-checked by exact pairwise isomorphism search).

Measured there by complete automorphism enumeration:
  |Aut(G)| = 48,  so |Aut_v| = 2 for every v;
  1-WL root is ONE cell  ⟹ `CellsAreOrbits` holds at the root (VT);
  after individualizing ONE vertex the 1-WL cells are  [1,1,2,2,3,3,6,6]
  and the stabiliser orbits are twelve fixed points + six 2-orbits,
  so **EVERY non-singleton cell is mixed** (the 3- and 6-cells cannot be orbits at all:
  orbit sizes divide |Aut_v| = 2; the 2-cells were checked explicitly).

⟹ `CellSingleOrbit` fails for EVERY possible `chooseIdK` outcome, hence `TinhoferPath` is
False whatever the colour-id convention, hence `Tinhofer` is False -- and a backtracking
selector ("pick another cell") has NO legal move at this node either.

This file only confirms that Lean's own `warmRefineVec` yields that same partition, which is
the one place the Python and Lean sides could have disagreed.
-/
import ChainDescent.DeepenTinhofer

namespace VTNotTinhofer

open ChainDescent
open ChainDescent.Deepen

def edges : List (Nat × Nat) :=
  [(0,1), (0,3), (0,5), (0,9), (0,15), (1,10), (1,16), (1,20), (1,22), (2,3), (2,5),
   (2,7), (2,11), (2,17), (3,12), (3,18), (3,22), (4,5), (4,7), (4,9), (4,13), (4,19),
   (5,14), (5,20), (6,7), (6,9), (6,11), (6,15), (6,21), (7,16), (7,22), (8,9), (8,11),
   (8,13), (8,17), (8,23), (9,18), (10,11), (10,13), (10,15), (10,19), (11,20), (12,13),
   (12,15), (12,17), (12,21), (13,22), (14,15), (14,17), (14,19), (14,23), (16,17),
   (16,19), (16,21), (18,19), (18,21), (18,23), (20,21), (20,23), (22,23)]

def g : AdjMatrix 24 :=
  ⟨fun i j => if edges.contains (i.val, j.val) || edges.contains (j.val, i.val) then 1 else 0⟩

def root : Colouring 24 := (Refine.warmRefineVec g (fun _ => 0)).col

def v0 : Fin 24 := ⟨0, by decide⟩

/-- one `step` below the root -/
def child : Colouring 24 := (step g root v0).col

-- 5-regular
#eval ((List.finRange 24).map (fun v => (List.finRange 24).foldl
        (fun a u => a + g.adj v u) 0)).eraseDups
-- the root is a single cell (consistent with vertex-transitivity)
#eval ((List.finRange 24).map root).eraseDups
-- ★ the partition one individualization down: (colour, cell size), ascending in colour id
#eval (((List.finRange 24).map child).eraseDups.mergeSort (fun (a b : Nat) => a ≤ b)).map
        (fun c => (c, ((List.finRange 24).filter (fun v => child v == c)).length))
-- which cell `chooseIdK` names, and its members
#eval chooseIdK (List.finRange 24) child
#eval match chooseIdK (List.finRange 24) child with
      | none => []
      | some cid => ((List.finRange 24).filter (fun v => child v == cid)).map
                      (fun (w : Fin 24) => w.val)
-- every cell, so the "all cells mixed" claim can be matched against the Python orbits
#eval (((List.finRange 24).map child).eraseDups.mergeSort (fun (a b : Nat) => a ≤ b)).map
        (fun c => ((List.finRange 24).filter (fun v => child v == c)).map
                    (fun (w : Fin 24) => w.val))

end VTNotTinhofer
