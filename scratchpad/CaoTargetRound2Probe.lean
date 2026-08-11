import ChainDescent.CaoTarget
open ChainDescent ChainDescent.CaoTarget
def g : AdjMatrix 7 := ⟨fun i j =>
  if (i.val < 3 && j.val < 3 && i ≠ j) then 1
  else if (i.val ≥ 3 && j.val ≥ 3 && (i.val - j.val = 1 || j.val - i.val = 1 ||
            (i.val = 3 && j.val = 6) || (i.val = 6 && j.val = 3))) then 1
  else 0⟩
#eval (List.finRange 7).map (fun i => ((List.finRange 7).map (fun j => g.adj i j)).sum)
#eval (List.finRange 7).map (fun i => (round2 (initCol2 g)) (i,i))
#eval (List.finRange 7).map (fun i => (round2 (round2 (initCol2 g))) (i,i))
