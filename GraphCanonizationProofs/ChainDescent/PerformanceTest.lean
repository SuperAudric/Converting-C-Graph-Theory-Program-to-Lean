import ChainDescent.Regression
import ChainDescent.DeepMatchSupply

/-!
# Performance measurements — **NOT on the build path**

> **This file is deliberately absent from `scripts/build.sh`.** Run it on demand:
> ```
> lake build ChainDescent.PerformanceTest
> ```
> It takes ~1–2 minutes. The **build-gating** checks live in `ChainDescent/Regression.lean`, which is fast (~12 s of
> evaluation) and *is* in `build.sh`.

**Why the split.** These are `#eval` measurements and large-`n` demonstrations, not correctness gates. They were
previously mixed into the regression suite and added ~20 minutes to a ~3-minute build. The cost driver is
`Force.lookaheadKey`: it runs one full warm refinement **per branch**, so a node costs `Θ(|cell| · n³)` — about
**1 s per key evaluation at `n = 12`**. A single root narrowing of the Frucht graph is therefore ~12 s and one
guarded mixed descent ~31 s. Nothing in the *regression* suite needs `n = 12` (see its header), so `F12` lives here.

**The duplicate-refine loss, visible in these numbers.** `lookaheadKey` computes, for each branch `v`, exactly the
refinement the child node then recomputes from scratch — and `matchSupply` computes it a *third* time. That is why
force *fires* on `F12` yet does not *pay* (26066 vs 22477 exhaustive). Fixing it means letting a resolver hand its
look-ahead forward, which is a `descend`-signature change and the first concrete `②` efficiency item.

**A real bug these measurements caught.** `matchSupply` originally called `lookData adj χ v` inside *both* loops of
its pair enumeration, recomputing the refinement for **every pair** — `|cell|²` refinements where `|cell|` suffice.
Materialising them once cut `gMatch F12` from **3.5 minutes to ~4 seconds**. That was an `O(n)` factor in the
*algorithm*, not the test.
-/

namespace ChainDescent.Perf

open ChainDescent ChainDescent.Descend ChainDescent.Refine ChainDescent.Regression
open ChainDescent.Force ChainDescent.Consume ChainDescent.Composite ChainDescent.Stall

/-- The **Frucht graph** — the smallest asymmetric cubic graph. 1-WL leaves one cell of all 12, and the cells are
not orbits. `Regression.G8` covers the same *property* eight times cheaper; `F12` is kept here because it is the
canonical rigid witness and the honest large-`n` cost sample. -/
def F12 : AdjMatrix 12 := ⟨fun i j =>
  let e : List (Nat × Nat) := [(0,1),(0,2),(0,11),(1,3),(1,6),(2,5),(2,10),(3,4),(3,6),(4,8),
                               (4,11),(5,9),(5,10),(6,7),(7,8),(7,9),(8,9),(10,11)]
  if e.contains (i.val, j.val) ∨ e.contains (j.val, i.val) then 1 else 0⟩

def C7 : AdjMatrix 7 := ⟨fun i j => if (i.val + 1) % 7 = j.val ∨ (j.val + 1) % 7 = i.val then 1 else 0⟩

/-! ## 1. The exhaustive baseline — cost grows fast, and it never flags -/

#eval (descentCost encodeFreeFast deferAll C7, descentCost encodeFreeFast deferAll F12)
-- C₇ 7568 · F12 22477

/-! ## 2. `consume` prunes and stays value-invisible (`Covering`) -/

#eval (descentCost encodeFreeFast (consume (dihSupply 7)) C7,
       descentCost encodeFreeFast deferAll C7)
-- 2467 vs 7568 — the oracle fires at the root and defers one level down.

/-! ## 3. `force` FIRES on the rigid case — and does NOT PAY

Root fan-out `12 → 1`, yet `descentCost` **rises**: the key's per-branch refinement costs more than the branching it
saves. `12 · (n³ + n²) = 22464` at the root alone, already more than the entire exhaustive descent. **Firing is not
paying** — and this only became visible once `Key` carried its cost. -/

#eval (narrow (forceBy lookaheadKey) F12 (refineV encodeFreeFast F12 (fun _ => 0))).length  -- 1
#eval (branches (refineV encodeFreeFast F12 (fun _ => 0))).length                            -- 12
#eval (descentCost encodeFreeFast (forceBy lookaheadKey) F12,
       descentCost encodeFreeFast deferAll F12)
-- 26066 vs 22477 — a NET LOSS. See the duplicate-refine note in the header.

/-! ## 4. The STALL GUARD — polynomial on every input, answering or flagging -/

def gForce {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceBy lookaheadKey)) a).map flatten

#eval ((gForce F12).isSome, (gForce C7).isSome)   -- (true, false): answers rigid, flags symmetric
#eval (descentCost encodeFreeFast (guard (forceBy lookaheadKey)) F12,
       descentCost encodeFreeFast (guard (forceBy lookaheadKey)) C7)
-- 26066 · 3137 — note it flags CHEAPLY: a stalled descent stops, it does not branch.

-- `①c` at n = 12: the guarded force narrowing is equivariant, so answer AND flag transport.
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 0 7) F12)
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 3 11) F12)

/-! ## 5. `matchSupply` at n = 12 — the structural oracle, and its limit -/

def gMatch {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) a).map flatten

#eval ((gMatch F12).isSome, (gMatch C7).isSome)  -- (true, false)
-- F12 is `Discretizing` (individualizing one vertex discretizes) so the colour match fires.
-- C₇ is NOT: individualizing one vertex leaves {0},{1,6},{2,5},{3,4}. One step is not enough.
#eval (decide (Discrete ((Consume.lookData F12 (refineV encodeFreeFast F12 (fun _ => 0)) 0).col)),
       decide (Discrete ((Consume.lookData C7 (refineV encodeFreeFast C7 (fun _ => 0)) 0).col)))
-- (true, false)

#guard gMatch F12 = gMatch (relabelAdj (Equiv.swap 0 7) F12)

#eval descentCost encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) F12

/-! ## 6. `deepMatchSupply` — the bounded-depth oracle FIRES on cycles, and **DOES NOT PAY**

`C₇` is where the one-step oracle died: `Aut(C₇) = D₇` has a reflection fixing each vertex, so no single
individualization discretizes (`Discretizing ⟹ trivial point stabilizers`). At `d = 1` the enumeration finds the
pair that reconstructs the rotation and `C₇` **answers**.

**But look at the price.** The search space is every sequence of length `≤ d`, so the supply costs `Θ(n^d)` per
node — and the cost model, which now bills `supplyCost`, shows it plainly:

| | `descentCost` on `C₇` |
|---|---|
| exhaustive (`deferAll`) | **7 568** — and it never flags |
| `guard (forceThenConsume lookaheadKey matchSupply)` | flags (cheaply) |
| `guard (forceThenConsume lookaheadKey (deepMatchSupply 1))` | **949 819** — answers, at **125×** the exhaustive cost |

**Firing is not paying** — the same lesson `lookaheadKey` taught, now at `n^d` scale. This is *not* a soundness or
a `②` problem: `Stall.descentCost_guard_le` is unconditional and the descent is still a single path; the `n^d` is
honestly inside `c₂`. It is a **quality** problem, and it is exactly what the `P3` orbit-pruned fixpoint exists to
remove — enumerate one sequence **per orbit of the group found so far** (legal, because
`rankSwap ψᵥ (g · ψ_w) = g · rankSwap ψᵥ ψ_w`, so pruning modulo a known element leaves the *generated group*
unchanged), which collapses to a **single path per branch** under localisation and turns `n^d` into a **sum**. -/

def gDeep {m : Nat} (d : Nat) (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume lookaheadKey (DeepMatch.deepMatchSupply d))) a).map flatten

#eval ((gMatch C7).isSome, (gDeep 1 C7).isSome)   -- (false, true): depth 1 closes the 7-cycle
#guard gDeep 1 C7 = gDeep 1 (relabelAdj (Equiv.swap 0 3) C7)

#eval (descentCost encodeFreeFast (guard (forceThenConsume lookaheadKey (DeepMatch.deepMatchSupply 1))) C7,
       descentCost encodeFreeFast deferAll C7)
-- 949819 vs 7568 — a NET LOSS of 125×. See the header.

end ChainDescent.Perf
