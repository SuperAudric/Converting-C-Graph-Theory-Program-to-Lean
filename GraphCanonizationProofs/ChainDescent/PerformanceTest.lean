import ChainDescent.Refine
import ChainDescent.Consume
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

/-! ## The ORACLE resolver (`Consume.consume`) — it prunes, and it stays right

A real oracle supply: the **rotation** of a cycle (`rotP`). At the root the colouring is constant, so `rotP`
verifies as a colouring-preserving automorphism and the whole cell is one orbit — the descent takes **one** branch
instead of `n`. One level down, the individualized vertex breaks the rotation symmetry, `rotP` **fails
verification**, and the resolver defers. That is the intended behaviour of the whole design, exercised.

Measured (oracle vs exhaustive `descentCost`): `C₅ 2016 → 804`, `C₆ 4123 → 1372`, `C₇ 7568 → 2160`.

Note what is *not* being assumed: the supply is untrusted. `Consume.consume_canonizer` holds for **every** supply,
so these `#guard`s test the *firing*, not the soundness. -/

/-- The cyclic rotation `i ↦ i + 1` of `Fin n`. -/
def rotP (n : Nat) [NeZero n] : Equiv.Perm (Fin n) := Equiv.addRight (1 : Fin n)

open ChainDescent.Consume in
/-- The rotation supply — a genuine automorphism source for cycles, and junk for anything else. -/
def rotSupply (n : Nat) [NeZero n] : Supply n := fun _ _ => [rotP n]

open ChainDescent.Consume in
/-- The canonical form computed with the **oracle** resolver. -/
def formC {n : Nat} [NeZero n] (adj : AdjMatrix n) : Option (List Nat) :=
  (canonForm? encodeFreeFast (consume (rotSupply n)) adj).map flatten

-- **It still answers** (`Consume.consume_canonizer`, exercised).
#guard (formC C5).isSome
#guard (formC C7).isSome

-- **★ THE COVERING PROPERTY, EXERCISED.** `consume` takes the `Covering` route, so it is *value-invisible*: it must
-- compute **exactly** the exhaustive form, only cheaper. A resolver that pruned a branch it should not have would
-- fail here.
#guard formC C5 = form C5
#guard formC C6 = form C6
#guard formC C7 = form C7

-- It still distinguishes, and is still iso-invariant.
#guard formC C5 ≠ formC P5
#guard formC C6 = formC (relabelAdj (Equiv.swap 2 5) C6)

-- **It actually PRUNES.** The root fan-out collapses from `n` branches to one, so the oracle-driven descent is
-- strictly cheaper than the exhaustive one. (Cost is the `②` projection of the same definition.)
open ChainDescent.Consume in
#eval (descentCost encodeFreeFast (consume (rotSupply 5)) C5, descentCost encodeFreeFast deferAll C5)
open ChainDescent.Consume in
#eval (descentCost encodeFreeFast (consume (rotSupply 6)) C6, descentCost encodeFreeFast deferAll C6)
open ChainDescent.Consume in
#eval (descentCost encodeFreeFast (consume (rotSupply 7)) C7, descentCost encodeFreeFast deferAll C7)

end ChainDescent.Refine
