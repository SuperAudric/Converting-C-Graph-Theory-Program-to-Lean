import ChainDescent.Refine
import ChainDescent.Consume
import ChainDescent.Force
import ChainDescent.Composite
import ChainDescent.Stall
import ChainDescent.MatchSupply
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
/-- The rotation supply — a genuine automorphism source for cycles, and junk for anything else. It is charged for
its own work (`Supply` is `CostM`-valued: an oracle is untrusted, but not free). -/
def rotSupply (n : Nat) [NeZero n] : Supply n := fun _ _ => ([rotP n], n)

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

Measured: on `F12` force collapses the root fan-out **12 → 1**; on `C₇` it cannot fire at all (7 → 7).

⚠ **It fires, but with `lookaheadKey` it does not PAY** (`descentCost`, honest accounting): `F12` 22477 → **26066**,
`C₇` 7568 → **16192** — both a net loss. The key runs a full warm refinement *per branch*, and that refinement is
exactly the one the child node then recomputes. See `Force.lookaheadKey`'s note; this is a `②` problem, not a `①`
one, and it only became visible once `Key` carried its cost. -/

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

/-! ## ★★ THE MIXED RESOLVER (`Composite.forceThenConsume`) — BOTH moves, and the ANTI-USELESSNESS gate

The guards above test that each resolver *is right*. **These test that each resolver is not silently useless** —
the failure mode `NarrowProper` cannot see, because a resolver that returns the whole cell (never narrowing
anything, deferring every decision) satisfies soundness, totality and properness, and would pass every `#guard`
written before this section.

The composite must narrow the root cell to **exactly one branch on BOTH domains**:

* `C₇` — vertex-transitive: the cell is one orbit, force **provably cannot fire**
  (`Force.forceBy_no_narrowing_on_orbit`), so **consume** must finish it
  (`Composite.forceThenConsume_singleton_of_cellIsOrbit`);
* `F12` — rigid: no two branches are automorphic, so **consume cannot fire** and the **key** must separate the cell
  (`Composite.forceThenConsume_singleton_of_separating`).

A regression in *either* resolver's firing — a key that stops separating, an orbit search that stops converging —
turns one of these from `1` into the full fan-out and **fails the build**. That is the property the proof stack
could not previously state, and the reason these guards exist. -/

open ChainDescent.Composite in
/-- The canonical form computed with the **mixed** resolver: force, then consume. -/
def formM {n : Nat} [NeZero n] (adj : AdjMatrix n) : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (forceThenConsume ChainDescent.Force.lookaheadKey (rotSupply n)) adj).map flatten

-- **It answers** (`Composite.composite_canonizer`, exercised).
#guard (formM C7).isSome
#guard (formM F12).isSome

-- **Iso-invariance (①a/①b/①c)** — the composite is a canonical form, modulo only `KeyEquivariant`.
#guard formM C7 = formM (relabelAdj (Equiv.swap 1 4) C7)
#guard formM F12 = formM (relabelAdj (Equiv.swap 0 7) F12)
#guard formM C6 = formM (relabelAdj (Equiv.swap 2 5) C6)

-- Still distinguishes.
#guard formM C5 ≠ formM P5

-- **★★★ THE FIRING GATE — one branch on BOTH domains.**
-- `C₇` (symmetric): force cannot fire, so this `1` is CONSUME doing its job.
open ChainDescent.Composite in
#guard (narrow (forceThenConsume ChainDescent.Force.lookaheadKey (rotSupply 7)) C7
          (refineV encodeFreeFast C7 (fun _ => 0))).length = 1
-- `F12` (rigid): consume cannot fire, so this `1` is the KEY doing its job.
open ChainDescent.Composite in
#guard (narrow (forceThenConsume ChainDescent.Force.lookaheadKey (rotSupply 12)) F12
          (refineV encodeFreeFast F12 (fun _ => 0))).length = 1

-- For contrast, each resolver ALONE fails on the other's domain — the complementary firing domains, as data.
-- (force on C₇: 7, i.e. no narrowing at all; consume on F12: 12, likewise.)
open ChainDescent.Force in
#guard (narrow (forceBy lookaheadKey) C7 (refineV encodeFreeFast C7 (fun _ => 0))).length = 7
open ChainDescent.Consume in
#guard (narrow (consume (rotSupply 12)) F12 (refineV encodeFreeFast F12 (fun _ => 0))).length = 12

open ChainDescent.Composite in
#eval (descentCost encodeFreeFast
        (forceThenConsume ChainDescent.Force.lookaheadKey (rotSupply 7)) C7,
       descentCost encodeFreeFast deferAll C7)
open ChainDescent.Composite in
#eval (descentCost encodeFreeFast
        (forceThenConsume ChainDescent.Force.lookaheadKey (rotSupply 12)) F12,
       descentCost encodeFreeFast deferAll F12)

/-! ## ★★★ THE STALL GUARD — the descent is UNCONDITIONALLY polynomial, and flags at the residue

`Stall.guard R` flags (returns the empty narrowing ⟹ `aggregate [] = none`) at any node the resolvers leave with
≥ 2 branches. So the descent is a **single path on every input** (`Stall.resolvedAll_guard`, no hypothesis) and
`Stall.descentCost_guard_le` is polynomial **unconditionally**. Deferral is not a cheap mode of a healthy run — it
*is* the failure — so there is no exhaustive fallback to be polynomial *about*. -/

open ChainDescent.Stall ChainDescent.Force ChainDescent.Composite in
/-- The **full** automorphism supply for a cycle: `Aut(Cₙ) = Dₙ = ⟨rotation, reflection⟩`. -/
def dihSupply (m : Nat) [NeZero m] : ChainDescent.Consume.Supply m :=
  fun _ _ => ([Equiv.addRight (1 : Fin m), Equiv.neg (Fin m)], m)

open ChainDescent.Stall ChainDescent.Force in
/-- Guarded **force**: no supply, so its narrowing is equivariant by construction. -/
def gForce {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceBy lookaheadKey)) a).map flatten

-- **It ANSWERS on the rigid case** (the key separates every cell) …
#guard (gForce F12).isSome
-- … and **FLAGS on the symmetric case** — correctly: force provably cannot fire on an orbit cell, so `C₇` is
-- exactly where the force-only route has nothing to say. It stops *cheaply* rather than branching.
#guard ¬ (gForce C7).isSome

-- **★ ①b/①c SURVIVE THE FLAG** (`Stall.guarded_force_canonizer`): the guarded force narrowing is equivariant, so
-- both the answer and the flag are iso-invariant.
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 0 7) F12)
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 3 11) F12)
#guard gForce C7 = gForce (relabelAdj (Equiv.swap 1 4) C7)

open ChainDescent.Stall ChainDescent.Force ChainDescent.Composite in
/-- Guarded **mixed**, with a supply that really does generate `Aut(Cₙ)`. -/
def gMix {m : Nat} [NeZero m] (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey (dihSupply m))) a).map flatten

-- **★★ THE MIXED ROUTE ANSWERS WHERE FORCE ALONE FLAGS.** Consume closes the symmetric cells force cannot touch.
#guard (gMix C5).isSome
#guard (gMix C6).isSome
#guard (gMix C7).isSome
#guard gMix C5 ≠ gMix P5   -- still distinguishing

/-! ### ⚠ THE FLAG'S PRICE, WITNESSED: a NON-EQUIVARIANT supply breaks `①c`

`consume`'s headline is that the supply is **untrusted** — `consume_canonizer` holds for *every* supply, because a
covering resolver is *value*-invisible. **A flag is not value-invisible.** `Stall.stalled` reads
`(narrow R adj χ).length`, which for the mixed resolver depends on how many orbits the supply's generators actually
*prove*. `rotSupply`/`dihSupply` hand back a **fixed** generator list, ignoring `adj` — but `Aut(σ·C₇) = σ·D₇·σ⁻¹`,
so those same generators **fail to verify** on the relabelled graph. Hence `C₇` answers and `σ·C₇` stalls.

The `#guard` below **asserts that failure**, on purpose: it is the **non-vacuity witness for
`Stall.StallEquivariant`**, proving the hypothesis cannot be dropped. Soundness still needs *nothing* from the
supply; the **flag** needs it to be equivariant. That is a genuinely new obligation, and this is its counterexample. -/

open ChainDescent.Stall ChainDescent.Force ChainDescent.Composite in
#guard (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey (dihSupply 7))) C7).isSome
     ≠ (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey (dihSupply 7)))
          (relabelAdj (Equiv.swap 1 4) C7)).isSome

-- Cost: the guarded descent is a single path, so it is cheap on EVERY input — including the ones it flags.
open ChainDescent.Stall ChainDescent.Force ChainDescent.Composite in
#eval (descentCost encodeFreeFast (guard (forceBy lookaheadKey)) F12,      -- answers
       descentCost encodeFreeFast (guard (forceBy lookaheadKey)) C7,       -- flags, and flags CHEAPLY
       descentCost encodeFreeFast (guard (forceThenConsume lookaheadKey (dihSupply 7))) C7,
       descentCost encodeFreeFast deferAll C7)                             -- exhaustive, for scale

/-! ## ★★★ `matchSupply` — the CASCADE ORACLE, structurally: it fixes `①c`, and it is NOT ENOUGH

`Consume.matchSupply` is the cascade oracle's **construct-and-check** colour match (`matchOracle`, §C.4) rebuilt
over `(adj, χ)`. Two results, and the second is the important one.

**★ IT FIXES `①c`.** The demo supplies (`rotSupply`/`dihSupply`) hand back a *fixed* generator list, so they are
**not equivariant** and provably break flag iso-invariance (the `#guard` above witnesses it). `matchSupply` is a
**structural function of `(adj, χ)`**, and iso-invariance is restored — the answer *and* the flag now transport.

**⚠ AND IT IS NOT ENOUGH — one-step colour matching FLAGS ON A 7-CYCLE.** `Consume.cellIsOrbit_matchSupply` fires
only at a **`Discretizing`** node (the cascade oracle's `hdisc` depth witness). Individualizing one vertex of `C₇`
and refining leaves `{0},{1,6},{2,5},{3,4}` — **not discrete** — so the oracle constructs *nothing*, `consume`
cannot fire, force cannot fire on an orbit cell, and the descent stalls. `F12` *does* discretize in one step, and
there it answers.

So `Discretizing` is far stronger than it sounds: **it excludes cycles.** This is exactly why the cascade oracle has
a *multi-step* form (`matchOracleSet`/`matchOracleSeq`, §C.6/§C.8) and exactly what `lockstep_disc_imp_stab_trivial`
says — a one-step discretizing colour match **provably cannot** harvest a multi-step moved orbit, which is where the
cross-branch harvest (and the Cameron / node-4 obstruction) lives. The residue is currently inflated by this gap,
not by anything hard. -/

open ChainDescent.Stall ChainDescent.Force ChainDescent.Composite ChainDescent.Consume in
/-- Guarded mixed with the **structural** cascade-oracle supply — no hand-supplied generators. -/
def gMatch {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) a).map flatten

-- **★ ①c RESTORED.** A structural supply makes answer *and* flag iso-invariant — the demo supplies did not.
#guard gMatch C7 = gMatch (relabelAdj (Equiv.swap 1 4) C7)
#guard gMatch C6 = gMatch (relabelAdj (Equiv.swap 2 5) C6)
#guard gMatch C5 = gMatch (relabelAdj (Equiv.swap 0 2) C5)
#guard gMatch F12 = gMatch (relabelAdj (Equiv.swap 0 7) F12)

-- **It answers where the node DISCRETIZES in one step** …
#guard (gMatch F12).isSome
#guard (gMatch P5).isSome

-- **… and FLAGS on cycles, because they do not.** This is the honest domain of the one-step colour match, and it
-- is the gap the multi-step / cross-branch harvest must close.
#guard ¬ (gMatch C5).isSome
#guard ¬ (gMatch C7).isSome

open ChainDescent.Consume in
-- The diagnosis, pinned: `C₇` is not `Discretizing`; `F12` is.
#guard ¬ Discrete ((lookData C7 (refineV encodeFreeFast C7 (fun _ => 0)) 0).col)
open ChainDescent.Consume in
#guard Discrete ((lookData F12 (refineV encodeFreeFast F12 (fun _ => 0)) 0).col)

end ChainDescent.Refine
