/-
PROBE (2026-07-30, `#eval` only, no `native_decide`, OUTSIDE the package root — cannot enter
any build).

**QUESTION (user): at the ROOT of a T2 vertex-transitive witness, does `consume` fire?**

The witness (see `scratchpad/probe_vt_witness.py`, `scratchpad/VTNotTinhoferProbe.lean`):
  G = Cay(Z12 :_5 Z2, {(0,1),(1,1),(2,1),(4,1),(7,1)}),  vertex (r,s) ↦ 2r+s,  n = 24, 5-regular.
  VERTEX-TRANSITIVE; |Aut(G)| = 48; |Aut_v| = 2.
  `Tinhofer` is FALSE for it, and in the strong (T2) sense: one individualization down, EVERY
  non-singleton 1-WL cell is mixed, so no selector -- backtracking included -- has a legal move.

Note the root cell IS a single orbit (the graph is VT), so `consume` is *licensed* here; the only
question is whether any supply actually produces enough VERIFIED automorphisms to collapse it.
`Tinhofer` gates `deepenSupply`'s certification, not the other supplies -- so this is exactly the
question T2 does NOT answer.

Measured per supply:
  * `gens`     = candidates emitted (untrusted)
  * `verified` = those surviving the decidable `IsColAut` filter
  * `reps`     = orbit representatives left on the branch cell by `consume`
                 -- **reps = 1 means consume COLLAPSES the root cell = it fires.**
-/
import ChainDescent.DeepenGuard

namespace VTConsumeProbe

open ChainDescent
open ChainDescent.Consume

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

/-- the branch cell at the root -/
def B : List (Fin 24) := Descend.branches root

/-- reps left on the branch cell after consuming with supply `S` -- 1 means it FIRED. -/
def repsOf (S : Supply 24) : Nat :=
  ((B.map (rep (verified S g root))).dedup).length

-- sanity: VT means the root is a single cell of 24
#eval ((List.finRange 24).map root).eraseDups
#eval B.length

-- match
#eval ((gens (Consume.matchSupply (n := 24)) g root).length,
       (verified (Consume.matchSupply (n := 24)) g root).length,
       repsOf (Consume.matchSupply (n := 24)))
-- deck
#eval ((gens (Deck.deckSupply (n := 24)) g root).length,
       (verified (Deck.deckSupply (n := 24)) g root).length,
       repsOf (Deck.deckSupply (n := 24)))
-- foldFast
#eval ((gens (Fold.foldSupplyFast (n := 24)) g root).length,
       (verified (Fold.foldSupplyFast (n := 24)) g root).length,
       repsOf (Fold.foldSupplyFast (n := 24)))
-- kernel
#eval ((gens (Kernel.kernelSupply (n := 24)) g root).length,
       (verified (Kernel.kernelSupply (n := 24)) g root).length,
       repsOf (Kernel.kernelSupply (n := 24)))

end VTConsumeProbe
