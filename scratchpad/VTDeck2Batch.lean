/- PROBE: a SINGLE `deck2Batch` on the T2 vertex-transitive witness (1/576 of `deck2Supply`).
   If `deck2Batch g root 0 u` yields a VERIFIED automorphism sending 0 ↦ u, then the two-seed
   mechanism finds the translations on the built object, and by vertex-transitivity the same
   holds for every target — i.e. `consume` collapses the root cell. -/
import ChainDescent.DeepenGuard
namespace VTDeck2Batch
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
def F (k : Nat) : Fin 24 := ⟨k % 24, Nat.mod_lt _ (by decide)⟩

/-- candidates from one batch, and how many are genuine colour-preserving automorphisms -/
def batchStats (u : Nat) : Nat × Nat × List Nat :=
  let cs := Deck2.deck2Batch g root (F 0) (F u)
  let ok := cs.filter (fun ρ => decide (IsColAut g root ρ))
  (cs.length, ok.length, (ok.map (fun ρ => (ρ (F 0)).val)).eraseDups)

#eval batchStats 1
#eval batchStats 5
#eval batchStats 12
end VTDeck2Batch
