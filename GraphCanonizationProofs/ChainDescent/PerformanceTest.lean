import ChainDescent.Refine
namespace ChainDescent.Refine
open ChainDescent.Descend

def C3 : AdjMatrix 3 := ⟨fun i j => if (i.val + 1) % 3 = j.val ∨ (j.val + 1) % 3 = i.val then 1 else 0⟩
#eval descentCost encodeFreeFast deferAll C3 --280
#eval (canonForm? encodeFreeFast deferAll C3).isSome --true

def C4 : AdjMatrix 4 := ⟨fun i j => if (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val then 1 else 0⟩
#eval descentCost encodeFreeFast deferAll C4  --845
#eval (canonForm? encodeFreeFast deferAll C4).isSome

def C5 : AdjMatrix 5 := ⟨fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 1 else 0⟩
#eval descentCost encodeFreeFast deferAll C5 --2016
#eval (canonForm? encodeFreeFast deferAll C5).isSome

def C6 : AdjMatrix 6 := ⟨fun i j => if (i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val then 1 else 0⟩
#eval descentCost encodeFreeFast deferAll C6 --4123
#eval (canonForm? encodeFreeFast deferAll C6).isSome


def C7 : AdjMatrix 7 := ⟨fun i j => if (i.val + 1) % 7 = j.val ∨ (j.val + 1) % 7 = i.val then 1 else 0⟩
#eval descentCost encodeFreeFast deferAll C7 --7568
#eval (canonForm? encodeFreeFast deferAll C7).isSome

/-! ## Correctness regression (not just liveness)

The `#eval`s above only check that the descent *runs*. These `#guard`s check that it stays *right* — the two
properties the object is proved to have, exercised on real graphs. `Labelled n` is a function (no `DecidableEq`),
so forms are compared through their row-major `flatten`. -/

/-- The canonical form of `adj`, as a comparable value. -/
def form {n : Nat} (adj : AdjMatrix n) : Option (List Nat) :=
  (canonForm? encodeFreeFast deferAll adj).map flatten

-- It never flags — `Refine.exhaustive_canonizer`, exercised.
#guard (form C5).isSome
#guard (form C7).isSome

-- **Iso-invariance (①b/①c).** Relabelling the input must not change the output.
#guard form C5 = form (relabelAdj (Equiv.swap 0 2) C5)
#guard form C5 = form (relabelAdj (Equiv.swap 1 4) C5)
#guard form C6 = form (relabelAdj (Equiv.swap 0 3) C6)
#guard form C6 = form (relabelAdj (Equiv.swap 2 5) C6)

-- **Distinguishing power.** Non-isomorphic graphs must get different forms — a canonizer that returned a
-- constant would pass every test above. `P5` is the 5-path; `C5` the 5-cycle.
def P5 : AdjMatrix 5 := ⟨fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0⟩
#guard form C5 ≠ form P5

end ChainDescent.Refine
