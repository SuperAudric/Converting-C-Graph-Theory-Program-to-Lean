/-
Validation + timing for `ChainDescent.CaoFast` (FT2b, the runnable 2-WL closure).
Placed OUTSIDE the package root (cao-propagation §8.3) so it cannot enter any build.
No `native_decide`.  Run: `lake env lean ../scratchpad/CaoFastProbe.lean` from GraphCanonizationProofs/.

Every expected value below is a number this project recorded independently (doc §4.4 step-0c, §14.5c).
-/
import ChainDescent.CaoFast
open ChainDescent ChainDescent.CaoTarget ChainDescent.CaoFast

/-- The number of 2-WL pair classes (the "2-WL rank" the doc quotes). -/
def rank2 {n : Nat} (a : AdjMatrix n) : Nat :=
  ((allPairs n).map (getP (wl2Fast (initVec a)))).eraseDups.length

/-! ### 1. `K₃ ⊔ C₄` — 2-regular, so 1-WL sees ONE cell; 2-WL must split it (§4.4 step-0c). -/
def g7 : AdjMatrix 7 := ⟨fun i j =>
  if (i.val < 3 && j.val < 3 && i ≠ j) then 1
  else if (i.val ≥ 3 && j.val ≥ 3 && (i.val - j.val = 1 || j.val - i.val = 1 ||
            (i.val = 3 && j.val = 6) || (i.val = 6 && j.val = 3))) then 1
  else 0⟩
#eval (List.finRange 7).map (fun i => getP (wl2Fast (initVec g7)) (i,i))   -- expect {0,1,2} | {3,4,5,6}

/-! ### 2. `C₅` and Petersen. -/
def c5 : AdjMatrix 5 := ⟨fun i j => if (i.val+1)%5 = j.val || (j.val+1)%5 = i.val then 1 else 0⟩
#eval rank2 c5                                                             -- expect 3
def pet : AdjMatrix 10 := ⟨fun i j =>
  let a := i.val; let b := j.val
  if a < 5 && b < 5 then (if (a+1)%5 = b || (b+1)%5 = a then 1 else 0)
  else if a ≥ 5 && b ≥ 5 then (if (a-5+2)%5 = b-5 || (b-5+2)%5 = a-5 then 1 else 0)
  else if a < 5 then (if a = b - 5 then 1 else 0)
  else (if b = a - 5 then 1 else 0)⟩
#eval rank2 pet                                                            -- expect 3

/-! ### 3. Shrikhande vs rook 4×4 — same `SRG(16,6,2,2)` parameters (§14.5c: both 3).
★ Shrikhande is the deficient root: 2-WL 3 vs orbitals 4. -/
def shrik : AdjMatrix 16 := ⟨fun i j =>
  let da := (4 + i.val / 4 - j.val / 4) % 4
  let db := (4 + i.val % 4 - j.val % 4) % 4
  if (da,db) = (1,0) || (da,db) = (3,0) || (da,db) = (0,1) || (da,db) = (0,3)
     || (da,db) = (1,1) || (da,db) = (3,3) then 1 else 0⟩
def rook : AdjMatrix 16 := ⟨fun i j =>
  if i = j then 0 else if i.val / 4 = j.val / 4 || i.val % 4 = j.val % 4 then 1 else 0⟩
#eval rank2 shrik                                                          -- expect 3
#eval rank2 rook                                                           -- expect 3

/-! ### 4. CFI over `K₄` (n = 28), plain and twisted (§14.5c: both 10).
edges  0:(0,1) 1:(0,2) 2:(0,3) 3:(1,2) 4:(1,3) 5:(2,3) -/
def eList : Nat → List Nat | 0 => [0,1,2] | 1 => [0,3,4] | 2 => [1,3,5] | _ => [2,4,5]
def inSub : Nat → Nat → Bool
  | 1, 0 => true | 1, 1 => true | 2, 0 => true | 2, 2 => true | 3, 1 => true | 3, 2 => true
  | _, _ => false
def link (tw : Bool) (inner edgev : Nat) : Nat :=
  let v := (inner - 12) / 4; let k := (inner - 12) % 4
  let e := edgev / 2; let bit := edgev % 2
  match (eList v).idxOf? e with
  | none => 0
  | some i =>
      let expected := if tw && e == 0 && v == 1 then !(inSub k i) else inSub k i
      if bit == (if expected then 1 else 0) then 1 else 0
def cfi (tw : Bool) : AdjMatrix 28 := ⟨fun a b =>
  if a.val < 12 && b.val ≥ 12 then link tw b.val a.val
  else if b.val < 12 && a.val ≥ 12 then link tw a.val b.val
  else 0⟩
#eval ((List.finRange 28).map
        (fun i => ((List.finRange 28).map (fun j => (cfi false).adj i j)).sum)).eraseDups  -- [4,3]
#eval rank2 (cfi false)                                                    -- expect 10
#eval rank2 (cfi true)                                                     -- expect 10

/-! ### 5. Timing (measured 2026-08-11; wall includes ~2.5 s Lean startup).
| input | n | d | wall |
|---|---|---|---|
| circulant `C_n(1,5)` | 56  | 29   | 8.5 s  |
| circulant `C_n(1,5)` | 100 | 51   | 16.8 s |
| circulant `C_n(1,5)` | 128 | 65   | 31.7 s |
| pseudo-random (worst case, 2-WL discretizes) | 56 | 3136 | 26.2 s |
Symmetric inputs are key-building-bound (`O(n³ log n)`, the true cost of 2-WL); the near-discrete
worst case is `denseRank`-scan-bound (`O(n²·d)`). -/
def circ (n : Nat) (S : List Nat) : AdjMatrix n := ⟨fun i j =>
  if S.any (fun s => (i.val + s) % n = j.val || (j.val + s) % n = i.val) then 1 else 0⟩
-- #eval rank2 (circ 128 [1,5])   -- 65, ~29 s compute
