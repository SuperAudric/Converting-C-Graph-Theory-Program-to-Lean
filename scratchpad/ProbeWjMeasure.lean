import ChainDescent.RecordDeepenCell
import ChainDescent.RestrictedTransport
open ChainDescent

def c5w : AdjMatrix 5 :=
  { adj := fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 1 else 0 }
def k123w : AdjMatrix 6 := TwinFamily.mpAdj TwinFamily.part123
def k2w : AdjMatrix 2 := { adj := fun i j => if i ≠ j then 1 else 0 }
def kc7w : AdjMatrix 7 := RestrictedTransport.kcAdj

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"C5   cost = {RecordDeepenCell.costFast (n := 5) c5w}"
  let t1 ← IO.monoMsNow
  IO.println s!"  C5   ms = {t1 - t0}"
  IO.println s!"K123 cost = {RecordDeepenCell.costFast (n := 6) k123w}"
  let t2 ← IO.monoMsNow
  IO.println s!"  K123 ms = {t2 - t1}"
  IO.println s!"K2   cost = {RecordDeepenCell.costFast (n := 2) k2w}"
  IO.println s!"answers: K2={(RecordDeepenCell.canonFormFast (n := 2) k2w).isSome} C5={(RecordDeepenCell.canonFormFast (n := 5) c5w).isSome} K3+C4={(RecordDeepenCell.canonFormFast (n := 7) kc7w).isSome}"
