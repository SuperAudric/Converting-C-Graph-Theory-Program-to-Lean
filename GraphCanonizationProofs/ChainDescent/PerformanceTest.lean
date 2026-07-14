import ChainDescent.Refine
import ChainDescent.Consume
import ChainDescent.Force
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

/-! ## The FORCE resolver (`Force.forceBy lookaheadKey`) — the other route

Force fires where consume cannot, and vice versa: **complementary firing domains**
(`Force.forceBy_no_narrowing_on_orbit`). `F12` is a 3-regular graph whose 1-WL leaves a **single cell of all 12
vertices** and whose cells are **not** orbits — the rigid case. `C₇` is vertex-transitive, so every cell *is* an
orbit and force provably cannot narrow at all.

Measured: on `F12` force collapses the root fan-out **12 → 1** (`descentCost` 22477 → 5186); on `C₇` it cannot fire
and merely pays for its key (7568 → 10312). Both are the theory, observed. -/

open ChainDescent.Force in
/-- A 3-regular graph on 12 vertices: 1-WL leaves one cell of size 12, and the cells are not orbits. -/
def F12 : AdjMatrix 12 := ⟨fun i j =>
  let e : List (Nat × Nat) := [(0,1),(0,2),(0,11),(1,3),(1,6),(2,5),(2,10),(3,4),(3,6),(4,8),
                               (4,11),(5,9),(5,10),(6,7),(7,8),(7,9),(8,9),(10,11)]
  if e.contains (i.val, j.val) ∨ e.contains (j.val, i.val) then 1 else 0⟩

open ChainDescent.Force in
/-- The canonical form computed with the **force** resolver. -/
def formF {n : Nat} (adj : AdjMatrix n) : Option (List Nat) :=
  (canonForm? encodeFreeFast (forceBy lookaheadKey) adj).map flatten

-- **It answers** (`Force.lookahead_canonizer`, exercised).
#guard (formF F12).isSome
#guard (formF C7).isSome

-- **Iso-invariance (①b/①c)** — the whole point of `KeyEquivariant`.
#guard formF F12 = formF (relabelAdj (Equiv.swap 0 7) F12)
#guard formF F12 = formF (relabelAdj (Equiv.swap 3 11) F12)
#guard formF C7 = formF (relabelAdj (Equiv.swap 1 4) C7)

-- Still distinguishes.
#guard formF C5 ≠ formF P5

-- **★ IT FIRES ON THE RIGID CASE.** Root fan-out 12 → 1: force narrows a cell that is NOT an orbit.
open ChainDescent.Force in
#guard (narrow (forceBy lookaheadKey) F12 (refineV encodeFreeFast F12 (fun _ => 0))).length = 1
#guard (branches (refineV encodeFreeFast F12 (fun _ => 0))).length = 12

-- **★ IT CANNOT FIRE ON THE SYMMETRIC CASE** (`forceBy_no_narrowing_on_orbit`, observed): every cell of `C₇` is an
-- orbit, so the forced narrowing is the whole cell.
open ChainDescent.Force in
#guard (narrow (forceBy lookaheadKey) C7 (refineV encodeFreeFast C7 (fun _ => 0))).length = 7

open ChainDescent.Force in
#eval (descentCost encodeFreeFast (forceBy lookaheadKey) F12, descentCost encodeFreeFast deferAll F12)
open ChainDescent.Force in
#eval (descentCost encodeFreeFast (forceBy lookaheadKey) C7, descentCost encodeFreeFast deferAll C7)

end ChainDescent.Refine
