import ChainDescent.DeepenGuard
namespace VTSupply1
open ChainDescent ChainDescent.Consume
def edges : List (Nat × Nat) :=
  [(0,1),(0,3),(0,5),(0,9),(0,15),(1,10),(1,16),(1,20),(1,22),(2,3),(2,5),(2,7),(2,11),
   (2,17),(3,12),(3,18),(3,22),(4,5),(4,7),(4,9),(4,13),(4,19),(5,14),(5,20),(6,7),(6,9),
   (6,11),(6,15),(6,21),(7,16),(7,22),(8,9),(8,11),(8,13),(8,17),(8,23),(9,18),(10,11),
   (10,13),(10,15),(10,19),(11,20),(12,13),(12,15),(12,17),(12,21),(13,22),(14,15),(14,17),
   (14,19),(14,23),(16,17),(16,19),(16,21),(18,19),(18,21),(18,23),(20,21),(20,23),(22,23)]
def g : AdjMatrix 24 :=
  ⟨fun i j => if edges.contains (i.val, j.val) || edges.contains (j.val, i.val) then 1 else 0⟩
def root : Colouring 24 := (Refine.warmRefineVec g (fun _ => 0)).col
def B : List (Fin 24) := Descend.branches root
def repsOf (S : Supply 24) : Nat := ((B.map (rep (verified S g root))).dedup).length
-- kernel: F2 Gaussian, cheapest
#eval ("kernel", (gens (Kernel.kernelSupply (n := 24)) g root).length,
                 (verified (Kernel.kernelSupply (n := 24)) g root).length,
                 repsOf (Kernel.kernelSupply (n := 24)))
-- foldFast
#eval ("foldFast", (gens (Fold.foldSupplyFast (n := 24)) g root).length,
                   (verified (Fold.foldSupplyFast (n := 24)) g root).length,
                   repsOf (Fold.foldSupplyFast (n := 24)))
end VTSupply1
