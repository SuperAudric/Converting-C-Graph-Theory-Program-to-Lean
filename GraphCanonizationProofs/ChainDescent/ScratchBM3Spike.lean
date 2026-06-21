/-!
# B-M3 kernel-`decide` feasibility micro-spike (NOT a proof; throwaway timing probe).

Question: can the kernel `decide` the restricted-count signature injectivity over the 81 base points
of `VO⁻₄(3)`, phrased as an **image-cardinality** equality, without `native_decide`?

Encoding (kernel-friendly: pure `Nat`/`List`, accelerated `Nat` ops, NO `Finset`/`Pi.fintype` Quot):
  point n ∈ 0..80 ↔ coords `co n i = (n / 3^i) % 3` (FIRST coord fastest).
  `Qc n = c0*c1 + c2² + c3²  (mod 3)`.
  `restricted u t1 t2 = #{ y∈0..80, y≠0 : Qc y=0 ∧ Qsh y u t1=0 ∧ Qsh y u t2=0 }`,
  with `Qsh` = `Qc` of coords `(co y i + co u i + (3 - co tc i)) % 3` (= y − (t̄ − ū)).
Targets validated by `/tmp/bm3_lean_targets.py` (same encoding).
-/

namespace BM3Spike

def co (n i : Nat) : Nat := (n / 3 ^ i) % 3

def Qc (n : Nat) : Nat := (co n 0 * co n 1 + co n 2 * co n 2 + co n 3 * co n 3) % 3

def Qsh (y u tc : Nat) : Nat :=
  let c0 := (co y 0 + co u 0 + (3 - co tc 0)) % 3
  let c1 := (co y 1 + co u 1 + (3 - co tc 1)) % 3
  let c2 := (co y 2 + co u 2 + (3 - co tc 2)) % 3
  let c3 := (co y 3 + co u 3 + (3 - co tc 3)) % 3
  (c0 * c1 + c2 * c2 + c3 * c3) % 3

def restricted (u t1 t2 : Nat) : Nat :=
  ((List.range 81).filter (fun y =>
    (! (y == 0)) && (Qc y == 0) && (Qsh y u t1 == 0) && (Qsh y u t2 == 0))).length

/-- The injective 6-pair separating family (T₉ nat-code pairs), from `/tmp/bm3_lean_targets.py`. -/
def fam : List (Nat × Nat) := [(0, 9), (27, 10), (1, 3), (27, 70), (9, 54), (1, 40)]

def sig (u : Nat) : List Nat := fam.map (fun p => restricted u p.1 p.2)

-- hand-rolled core-Lean distinctness (avoids Mathlib `List.dedup`/`Nodup`; pure `Nat.beq`)
def listEq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && listEq as bs
  | _, _ => false

def memB (x : List Nat) : List (List Nat) → Bool
  | [] => false
  | y :: ys => listEq x y || memB x ys

def allDistinct : List (List Nat) → Bool
  | [] => true
  | x :: xs => (! memB x xs) && allDistinct xs

/-- The full image-card injectivity, as one Bool computation (stage-3 decide target). -/
def injOver81 : Bool := allDistinct ((List.range 81).map sig)

set_option maxHeartbeats 0

-- native sanity (allowed: NOT a proof) — confirms the encoding before kernel timing
#eval restricted 0 0 9          -- expect 6
#eval restricted 40 0 9         -- expect 1
#eval sig 0                     -- expect [6,2,0,3,2,0]
#eval injOver81                 -- expect true

set_option profiler true

-- Stage 1: single counts (kernel)
example : restricted 0 0 9 = 6 := by decide
example : restricted 40 0 9 = 1 := by decide

-- Stage 2: one full signature (kernel)
example : sig 0 = [6, 2, 0, 3, 2, 0] := by decide

-- Stage 3: THE TARGET — the restricted-signature is injective over all 81 base points (kernel)
example : injOver81 = true := by decide

end BM3Spike
