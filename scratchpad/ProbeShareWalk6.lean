import ChainDescent.RecordDeepenCell

/-!
Scratch probe — two runtime defects in `Select.probeWalk`, measured end-to-end on `C₅`.

`probeWalk` (as built) does, per probed cell:
  · `((cellList χ c).map (keyCost key adj χ)).sum`   — one FULL key evaluation per vertex, for the bill
  · `cellNarrowV key V adj χ c` → `keepMin`          — `kmin?` over `B.map keyV` (a second full pass)
                                                        then `B.filter (keyV · = m)` (a third)
  · `S c adj χ` where `S c = recordSupplyFast ++ deepenCellSupply c` — the CELL-INDEPENDENT record
    harvest is re-run once per probed cell.

`selNodeLazySK` below fixes both, with **identical children** and an **identical bill**:
  · the key is evaluated ONCE per (cell, vertex) into a table, read for the bill and the argmin;
  · the record supply is harvested ONCE per node and appended per cell.

Baseline to compare against (recorded 2026-08-08): `C₅` lazy = 5 212 728 billed / 34 s.
-/

namespace Probe
open ChainDescent
open ChainDescent.Select
open ChainDescent.Consume (Supply gens verified rep IsColAut)
open ChainDescent.Force (Key keyCost keyV keepMin kmin?)

variable {n : Nat}

/-- One key evaluation per vertex, value and cost kept together. -/
def keyTable (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    List (Fin n × List Nat × Nat) :=
  B.map (fun v => (v, key adj χ v))

/-- `keepMin` read off the table — no further key evaluation. -/
def keepMinT (t : List (Fin n × List Nat × Nat)) : List (Fin n) :=
  match kmin? (t.map (fun p => p.2.1)) with
  | none => t.map (fun p => p.1)
  | some m => (t.filter (fun p => decide (p.2.1 = m))).map (fun p => p.1)

/-- The lazy walk with (a) the key shared and (b) the cell-independent left factor hoisted. -/
def probeWalkSK (key : Key n) (Lg : List (Equiv.Perm (Fin n))) (Lc : Nat) (Lgn : Nat)
    (VL : List (Equiv.Perm (Fin n)))
    (T : Select.CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    List Nat → Option (Nat × List (Fin n)) × Nat
  | [] => (none, 0)
  | c :: cs =>
      let tv := T c adj χ
      let allgLen := Lgn + tv.1.length
      -- `List.filter_append`: the left factor's verification is hoisted, the list is unchanged
      let V := VL ++ tv.1.filter (fun g => decide (IsColAut adj χ g))
      let t := keyTable key adj χ (cellList χ c)
      let kept := ((keepMinT t).map (rep V)).dedup
      let bill := (Lc + tv.2) + allgLen * (n * n)
        + (t.map (fun p => p.2.2)).sum + n * n
        + (cellList χ c).length * (V.length * (n * n) + n * n)
      if kept.length ≤ 1 then (some (c, kept), bill)
      else
        let r := probeWalkSK key Lg Lc Lgn VL T adj χ cs
        (r.1, bill + r.2)

def selNodeLazySK (key : Key n) (L : Supply n) (T : Select.CellSupply n) : NodeRes n := fun adj χ =>
  let lv := L adj χ
  let VL := lv.1.filter (fun g => decide (IsColAut adj χ g))
  match probeWalkSK key lv.1 lv.2 lv.1.length VL T adj χ
      ((Descend.nonSingletonColours χ).sort (· ≤ ·)) with
  | (none, pc) => ([], pc)
  | (some (_, kept), pc) =>
      (kept.map (fun v => (v, (Refine.warmRefineVec adj (Descend.indivOne χ v)).col)),
       pc + (kept.map (fun _ => CostModel.WarmRefine.warmRefineCost n)).sum)

end Probe

open ChainDescent


/-- `K₁,₂,₃` (n = 6, two non-singleton cells at the root). -/
def kadj : AdjMatrix 6 := TwinFamily.mpAdj TwinFamily.part123

def builtCost6 : Nat :=
  Select.descentCostS (Refine.encodeFreeFast (n := 6))
    (Select.selNodeLazyC (RecordKey.recordKey (n := 6))
      (RecordDeepenCell.recordSupplyDeepenC (n := 6))) kadj

def sharedCost6 : Nat :=
  Select.descentCostS (Refine.encodeFreeFast (n := 6))
    (Probe.selNodeLazySK (RecordKey.recordKey (n := 6)) (RecordCost.recordSupplyFast (n := 6))
      (fun c => Deepen.deepenCellSupply c)) kadj

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"K123 built  = {builtCost6}"
  let t1 ← IO.monoMsNow
  IO.println s!"  built  ms = {t1 - t0}"
  let t2 ← IO.monoMsNow
  IO.println s!"K123 shared = {sharedCost6}"
  let t3 ← IO.monoMsNow
  IO.println s!"  shared ms = {t3 - t2}"
