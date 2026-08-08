import ChainDescent.RecordDeepenCell
import ChainDescent.RestrictedTransport
open ChainDescent

def k2 : AdjMatrix 2 := { adj := fun i j => if i ≠ j then 1 else 0 }
def c5b : AdjMatrix 5 :=
  { adj := fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 1 else 0 }
def kc7 : AdjMatrix 7 := ChainDescent.RestrictedTransport.kcAdj

#eval show IO Unit from do
  IO.println s!"K2  answers = {(RecordDeepenCell.canonFormFast (n := 2) k2).isSome}, cost = {RecordDeepenCell.costFast (n := 2) k2}"
  IO.println s!"C5  answers = {(RecordDeepenCell.canonFormFast (n := 5) c5b).isSome}"
  IO.println s!"K3+C4 (residual witness) answers = {(RecordDeepenCell.canonFormFast (n := 7) kc7).isSome}"
