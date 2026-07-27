import ChainDescent.Regression
import ChainDescent.DeepMatchSupply
import ChainDescent.DeepenSupply
/-!
# Performance measurements — **NOT on the build path**

> **This file is deliberately absent from `scripts/build.sh`.** Run it on demand:
> ```
> lake build ChainDescent.PerformanceTest
> ```
> It takes a long time to run so should be used sparingly. Every statement must earn it's place (some currently
> do not meet this). This is predominantly to check for exponential leaks via timings or #guard clauses that with
> no other place. The **build-gating** checks live in `ChainDescent/Regression.lean`, which is fast (~12 s of
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

--#eval (descentCost encodeFreeFast deferAll C7, descentCost encodeFreeFast deferAll F12)
-- C₇ 7568 · F12 22477

/-! ## 2. `consume` prunes and stays value-invisible (`Covering`) -/

--#eval (descentCost encodeFreeFast (consume (dihSupply 7)) C7,
--       descentCost encodeFreeFast deferAll C7)
-- 2467 vs 7568 — the oracle fires at the root and defers one level down.

/-! ## 3. `force` FIRES on the rigid case — and does NOT PAY

Root fan-out `12 → 1`, yet `descentCost` **rises**: the key's per-branch refinement costs more than the branching it
saves. `12 · (n³ + n²) = 22464` at the root alone, already more than the entire exhaustive descent. **Firing is not
paying** — and this only became visible once `Key` carried its cost. -/

--#eval (narrow (forceBy lookaheadKey) F12 (refineV encodeFreeFast F12 (fun _ => 0))).length  -- 1
--#eval (branches (refineV encodeFreeFast F12 (fun _ => 0))).length                            -- 12
--#eval (descentCost encodeFreeFast (forceBy lookaheadKey) F12,
--       descentCost encodeFreeFast deferAll F12)
-- 26066 vs 22477 — a NET LOSS. See the duplicate-refine note in the header.

/-! ## 4. The STALL GUARD — polynomial on every input, answering or flagging -/

def gForce {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceBy lookaheadKey)) a).map flatten

--#eval ((gForce F12).isSome, (gForce C7).isSome)   -- (true, false): answers rigid, flags symmetric
--#eval (descentCost encodeFreeFast (guard (forceBy lookaheadKey)) F12,
--       descentCost encodeFreeFast (guard (forceBy lookaheadKey)) C7)
-- 26066 · 3137 — note it flags CHEAPLY: a stalled descent stops, it does not branch.

-- `①c` at n = 12: the guarded force narrowing is equivariant, so answer AND flag transport.
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 0 7) F12)
#guard gForce F12 = gForce (relabelAdj (Equiv.swap 3 11) F12)

/-! ## 5. `matchSupply` at n = 12 — the structural oracle, and its limit -/

def gMatch {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) a).map flatten

--#eval ((gMatch F12).isSome, (gMatch C7).isSome)  -- (true, false)
-- F12 is `Discretizing` (individualizing one vertex discretizes) so the colour match fires.
-- C₇ is NOT: individualizing one vertex leaves {0},{1,6},{2,5},{3,4}. One step is not enough.
--#eval (decide (Discrete ((Consume.lookData F12 (refineV encodeFreeFast F12 (fun _ => 0)) 0).col)),
--       decide (Discrete ((Consume.lookData C7 (refineV encodeFreeFast C7 (fun _ => 0)) 0).col)))
-- (true, false)

#guard gMatch F12 = gMatch (relabelAdj (Equiv.swap 0 7) F12)

--#eval descentCost encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) F12

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

--#eval ((gMatch C7).isSome, (gDeep 1 C7).isSome)   -- (false, true): depth 1 closes the 7-cycle
#guard gDeep 1 C7 = gDeep 1 (relabelAdj (Equiv.swap 0 3) C7)

--#eval (descentCost encodeFreeFast (guard (forceThenConsume lookaheadKey (DeepMatch.deepMatchSupply 1))) C7,
--       descentCost encodeFreeFast deferAll C7)
-- 949819 vs 7568 — a NET LOSS of 125×. See the header.

/-! ## 7. `F1` — the fold family end-to-end (`docs/chain-descent-fold-tower-plan.md`)

The Regression §8 guards witness the supply-level separation (`deepMatchSupply 0` dead, `partialMatchSupply 0`
collapses the copies cell, 132× cheaper than `deepMatchSupply 1` which is *also* dead). Here the descent-level
consequence: the guarded mixed descent on the 24-vertex 4-fold cover **answers** with the support-local supply
and **flags** with the full-match one — same `d = 0`, same (trivial) key. `constKey` keeps the force side out of
the measurement (`lookaheadKey` at `n = 24` costs ~8 s per node and is irrelevant to a consume-side demo).
Measured 2026-07-17: the answering descent is ~3.5 min interpreted; the flagging one stalls at the root. -/

def gPartialFold : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume Residue.constKey (PartialMatch.partialMatchSupply 0)))
    Regression.fold4).map flatten

def gDeepFold : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume Residue.constKey (DeepMatch.deepMatchSupply 0)))
    Regression.fold4).map flatten

--#eval (gPartialFold.isSome, gDeepFold.isSome)   -- (true, false): support-local answers, full-match flags

/-! `①c`, observed at `n = 24` at the supply level: the narrowing still collapses to ONE branch on a cross-copy
relabelling (`gensEquivariant_partialMatchSupply` is the proved statement; a second full descent just to re-observe
it would double this file's cost). -/
def fold4Swapped : AdjMatrix 24 := relabelAdj (Equiv.swap 0 7) Regression.fold4
def fold4SwappedRoot : Refine.ColData 24 := Refine.warmRefineVec fold4Swapped (fun _ => 0)

#guard (narrow (consume (PartialMatch.partialMatchSupply 0)) fold4Swapped fold4SwappedRoot.col).length = 1

/-! `deepMatchSupply` needs `d = k − 2 = 2` on a 4-fold cover; at `d = 1` it is still dead and already 132× the
firing supply's cost. -/
--#eval ((narrow (consume (DeepMatch.deepMatchSupply 1)) Regression.fold4 Regression.fold4Root.col).length,
--       Consume.supplyCost (DeepMatch.deepMatchSupply 1) Regression.fold4 Regression.fold4Root.col,
--       Consume.supplyCost (PartialMatch.partialMatchSupply 0) Regression.fold4 Regression.fold4Root.col)
-- (4, 8524800, 64512)

/-! ## 8. `F2a` — the structural fold supply at `s = 3` (`Regression` §10 is the `s = 2` gate)

3 vertical copies of the mirror-tied core, n = 15: the merged `{1,3}` class shows up as a 6-cell, the pendant
copy cell as a 3-cell; refinement-based matching is dead on it while `foldSupply` verifies 9 candidates
(3² seed pairs, diagonal seeds contribute the identity) and collapses it to ONE branch. -/

def vfold3 : AdjMatrix 15 :=
  ⟨fun i j => if (i.val / 5 == j.val / 5 && Regression.vcoreB (i.val % 5) (j.val % 5)) ||
      (i.val / 5 != j.val / 5 && i.val % 5 == j.val % 5) then 1 else 0⟩

def vfold3Root : Refine.ColData 15 := Refine.warmRefineVec vfold3 (fun _ => 0)

--#eval ((Consume.verified (Fold.foldSupply) vfold3 vfold3Root.col).length,
--       (narrow (consume (Fold.foldSupply)) vfold3 vfold3Root.col).length,
--       (narrow (consume (PartialMatch.partialMatchSupply 0)) vfold3 vfold3Root.col).length,
--       (narrow (consume (DeepMatch.deepMatchSupply 0)) vfold3 vfold3Root.col).length)
-- (9, 1, 3, 3): structural fires, both matching supplies dead

--#eval (Consume.supplyCost (Fold.foldSupply) vfold3 vfold3Root.col,
--       Consume.supplyCost (PartialMatch.partialMatchSupply 0) vfold3 vfold3Root.col)
-- (6834375, 12150) — the flat |cell|²·n⁵ bill vs the (dead) matcher's table bill

/-! `①c`, observed at the supply level on a cross-copy relabelling (the theorem form is
`gensEquivariant_foldSupply`). -/
def vfold3Swapped : AdjMatrix 15 := relabelAdj (Equiv.swap 0 5) vfold3
def vfold3SwappedRoot : Refine.ColData 15 := Refine.warmRefineVec vfold3Swapped (fun _ => 0)

#guard (narrow (consume (Fold.foldSupply)) vfold3Swapped vfold3SwappedRoot.col).length = 1

/-! ## 9. `F2b` — arbitrary ARITY and HEIGHT (`Regression` §11 is the gate; plan §4b)

The weighted cycles `C_{3s}` have `Aut = Z_s` with no involutions for odd `s`: every matching/involution
mechanism on both sides is structurally out — the C# `TryDoublingPeel` requires `s % 2 = 0`, so odd part ≥ 7
has NO C# path at any size. `Deck.deckSupply` constructs the order-`s` rotation in one propagation per seed:
arity is arbitrary, and a `Z_{p^k}` deck (tower height `k`) is the SAME single propagation constructing the
order-`p^k` generator — height enters only through `n`. -/

def wcyc15 : AdjMatrix 15 := ⟨fun i j => Regression.wEdge 15 i.val j.val⟩
def wcyc15Root : Refine.ColData 15 := Refine.warmRefineVec wcyc15 (fun _ => 0)

--#eval ((Consume.verified (Deck.deckSupply) wcyc15 wcyc15Root.col).length,
--       (narrow (consume (Deck.deckSupply)) wcyc15 wcyc15Root.col).length,
--       Consume.supplyCost (Deck.deckSupply) wcyc15 wcyc15Root.col)
-- (25, 1, 18984375): all 5² seeds complete to order-5 rotations, ONE branch (flat |cell|²·n⁵ bill)

/-! `Z₉` — odd part 9 ≥ 7 (the case with no C# path) and height 2 (9 = 3²): the harvested generator has
order 9. -/
def wcyc27 : AdjMatrix 27 := ⟨fun i j => Regression.wEdge 27 i.val j.val⟩
def wcyc27Root : Refine.ColData 27 := Refine.warmRefineVec wcyc27 (fun _ => 0)

--#eval (narrow (consume (Deck.deckSupply)) wcyc27 wcyc27Root.col).length
-- 1: the 9-fan collapses; no involution emitter can touch this cell

--#eval ((Deck.deckCandFast wcyc27 wcyc27Root.col ⟨1, by omega⟩ ⟨4, by omega⟩).map
--  (fun g => (decide (g ^ 9 = 1), decide (g ^ 3 = 1), decide (g = 1))))
-- some (true, false, false): a genuine order-9 generator from ONE propagation

/-! The voltage-ring cover — the true tower-gadget shape: rigid 6-vertex core `a,b,d,p₁,p₂,q` (edges `a–d`,
`b–d`, `a–p₁`, `p₁–p₂`, `b–q`), cross edge `(c,a)–(c+1,b)` = voltage 1. Deck `Z₃` exactly; the asymmetric
pendant paths kill the WL reversal ghost AND every reflection, so `Aut` is involution-free. The
involution-based structural supply is dead; the propagation supply collapses the cell. -/
def vringB (s a b : Nat) : Bool :=
  let ca := a / 6; let pa := a % 6; let cb := b / 6; let pb := b % 6
  (ca == cb && ((pa == 0 && pb == 2) || (pa == 2 && pb == 0)
             || (pa == 1 && pb == 2) || (pa == 2 && pb == 1)
             || (pa == 0 && pb == 3) || (pa == 3 && pb == 0)
             || (pa == 3 && pb == 4) || (pa == 4 && pb == 3)
             || (pa == 1 && pb == 5) || (pa == 5 && pb == 1)))
  || (cb == (ca + 1) % s && pa == 0 && pb == 1)
  || (ca == (cb + 1) % s && pb == 0 && pa == 1)

def vring18 : AdjMatrix 18 := ⟨fun i j => if vringB 3 i.val j.val then 1 else 0⟩
def vring18Root : Refine.ColData 18 := Refine.warmRefineVec vring18 (fun _ => 0)

#eval ((narrow (consume (Fold.foldSupply)) vring18 vring18Root.col).length,
       (Consume.verified (Deck.deckSupply) vring18 vring18Root.col).length,
       (narrow (consume (Deck.deckSupply)) vring18 vring18Root.col).length)
-- (3, 9, 1): involutions dead, propagation fires — refinement-free

/-! End-to-end: the FUSED canonizer over `foldSupply ++ deckSupply` (capstone
`foldDeckSupply_selNode_canonizer`) ANSWERS on the involution-free weighted cycle. -/
def gDeckCycle : Option (List Nat) :=
  (Select.canonFormFastS? Residue.constKey
    (Deck.appendSupply Fold.foldSupply Deck.deckSupply) Regression.wcyc9).map flatten

--#eval gDeckCycle.isSome
-- true

/-! ## 10. `F3a` — the n = 30 COMPOSITE fires (`Regression` §12 is the per-half gate; plan §5b)

The two halves were measured separately (force: `holKeyFast` keeps the straight triple `[4, 9, 14]`,
`Regression` §12; consume: `foldSupply` collapses a straight copy cell, §8 above and `Regression` §10);
the composite eval was blocked on the F2a evaluation constant (`FoldFast.lean`, the per-supply-call
membership tables). With it: ONE mixed-resolver step on `U3 ⊔ T3` — force keeps the WL-merged cell's
straight triple (the T-pendants' holonomy signature differs), consume merges the kept triple into one
orbit — narrowing the 6-fan to a SINGLE branch. ~40 s interpreted, dominated by `holKeyFast` (~10 s) and
the n = 30 deck propagations. Soundness of exactly this object is `Fold.holKey_foldDeckFast_selNode_
canonizer` / `Hol.holKey_foldDeck_guarded_canonizer`. -/

--#eval (narrow (forceThenConsume Hol.holKeyFast
--        (Deck.appendSupply Fold.foldSupplyFast Deck.deckSupply)) Regression.ut
--        Regression.utRoot.col).map Fin.val
-- [4]: 6-fan → ONE branch (force 6→3, consume 3→1) — the F3a composite firing, measured

/-! ⚠ **End-to-end on `ut` FLAGS below the root — measured, honest, carried open** (probed 2026-07-18,
not repeated here: ~2 min each). Both `canonFormFastS? holKeyFast (foldFast ++ deck)` and the full stack
with `partialMatchSupply 0` appended flag: the T-component's gauge — per-copy mirrors composed through
the TWISTED matchings — is outside every built supply's reach (fold: the twisted `{1,3}` fibers merge, so
the unique-partner lookup is ambiguous; deck: a commuting copy swap gives every mirror seed ≥ 2 extensions;
matching: the mirror tie survives every pin — 1-WL chirality-blindness). The root composite above is the
F3a claim and it fires; canonizing `T3`'s inside is a CONSUME-side open item (a mirror-composite
constructor), not a force one.
**✅ CLOSED 2026-07-19 by F2c (`ChainDescent/Deck2.lean`, `deck2Supply`) — see §11 below.** -/

/-! ## 11. `F2c` — the second-seed supply closes §10's open item (the T-side gauge)

The stall mechanism, precisely: the T-side gauge (per-copy mirrors composed through the twisted matchings)
**commutes** with every copy swap, so single-seed propagation always retains ≥ 2 viable images at the mirror
class — forcing never reaches uniqueness. `Deck2.deck2Supply` re-reads each stalled propagation's own
ambiguity set (unassigned × viable, `seconds`) as second seeds on the shared stalled state; the added
constraint forces which commuting extension completes, and the mirror composites (`μ³`-type and swap∘mirror)
verify. Cheap cell-level gates are build-gating in `Regression` §14 (t3: fold 3 / deck 3 / deck2 → 1,
171 verified).

**MEASURED (2026-07-19):**
- `t3` alone (n = 15): the F2c record (`holKeyFast` + `foldSupplyFast ++ deckSupply ++ deck2Supply`)
  ANSWERS end-to-end (~20 s) and is relabel-invariant.
- **`ut` (n = 30): the record ANSWERS end-to-end** — where every pre-F2c stack flagged below the root.
  ~20 min interpreted (dominated by the per-node deck2 second stage at n = 30 + `holKeyFast`); soundness of
  exactly this object is `Deck2.holKey_foldDeck2Fast_selNode_canonizer`. The fold family's known
  constructible members now all answer. ⚠ The scope note that first shipped here ("next gap = wreath-type
  per-copy gauges, which one second seed does not resolve") was WRONG — see §12: wreath gauges FIRE. -/

--#eval ((Select.canonFormFastS? Hol.holKeyFast
--    (Deck.appendSupply Fold.foldSupplyFast
--      (Deck.appendSupply Deck.deckSupply Deck2.deck2Supply)) Regression.ut).map flatten).isSome
-- true (~20 min): the §10 open item, closed

/-! ## 12. `F2c` reach is WIDER than designed — the WREATH gauge fires (the identity-default finding)

`wr3` = 3 copies of the `C₄`+pendant core on a copy cycle, matched ONLY on the mirror-FIXED fibers
`{0,2,4}` — so each copy's mirror `(1↔3)` is an INDEPENDENT automorphism: `Aut ⊇ Z₂³ ⋊ D₃`, the
wreath-type gauge the C2 scope line claimed stalls `deck2Supply`. **Measured 2026-07-19: it does NOT
stall — it fires.** The mechanism: `deck2Fun`'s `.getD v` identity-default on unassigned vertices is
load-bearing — an ambiguity component *independent* of the resolved part defaults to the identity, and
independence is exactly what makes that completion an automorphism, which `IsColAut` then verifies (the
same default emits junk on coupled residuals, which verification rejects — sound either way). Root
branch cell = the merged mirror class (6-cell): `foldSupplyFast` 6 (dead — within-copy pairs), `deck` 3
(diagonal chains only), **`deck2Supply` → 1**; node-2 (pendant pinned): deck 2, **deck2 → 1** (96
verified); end-to-end with the F2c record: ANSWERS (~2 min). Guards are here, not in `Regression` —
the root-cell trio costs ~33 s, over the build-gating budget. Scope conclusions → `Deck2.lean` module
doc + remaining-work §1C (the genuine residual = ≥3-ary coupled, min-weight-≥3 gauges — CFI cycle-space
over pin-blind bases; odd-degree CFI is the depth leg's, `theorem_1_HOR_cfi_oddDeg`). -/

def wrB (s a b : Nat) : Bool :=
  let ca := a / 5; let va := a % 5; let cb := b / 5; let vb := b % 5
  if ca == cb then Regression.vcoreB va vb
  else if (ca + 1) % s == cb || (cb + 1) % s == ca then va == vb && va != 1 && va != 3
  else false

def wr3 : AdjMatrix 15 := ⟨fun i j => if wrB 3 i.val j.val then 1 else 0⟩
def wr3Root : Refine.ColData 15 := Refine.warmRefineVec wr3 (fun _ => 0)

#guard (branches wr3Root.col).map Fin.val = [1, 3, 6, 8, 11, 13]
#guard (narrow (consume (Fold.foldSupplyFast)) wr3 wr3Root.col).length = 6
#guard (narrow (consume (Deck.deckSupply)) wr3 wr3Root.col).length = 3
#guard (narrow (consume Deck2.deck2Supply) wr3 wr3Root.col).length = 1

--#eval ((Select.canonFormFastS? Hol.holKeyFast
--    (Deck.appendSupply Fold.foldSupplyFast
--      (Deck.appendSupply Deck.deckSupply Deck2.deck2Supply)) wr3).map flatten).isSome
-- true (~2 min): the wreath witness answers end-to-end

/-! ## 13. `C3` — the FANO MULTIPEDE `mp7`: the TRUE consume residual, measured (2026-07-19)

The witness remaining-work §1C C3 predicted: a symmetric pin-blind CFI cover whose gauge is the kernel
of arity-≥3 parity checks with min weight ≥ 3. Construction: 7 segments (foot pairs, index `2j+b`),
7 checks = the Fano lines `δ(i) = {i,i+1,i+3} mod 7` (any two lines share exactly ONE segment —
incidence girth 6 ⟹ no 2-overlap chaining), each check a 4-vertex CFI gadget (even subsets; index
`14+4i+s`); n = 42. Gauge = ker(incidence) = the [7,3,4] simplex code: dim 3, **min weight 4** — no
weight-≤2 words (deck2's identity-default has nothing valid to default to) and no chaining (one
assigned wire leaves 2 candidates at every gadget).

**MEASURED (all below):** 2 WL-cells; branch cell = the 28 gadget vertices; the weight-4 codeword
flip IS a colour-automorphism (the gauge is real); PIN-BLIND (6 colours of 42 after pinning a foot ⟹
every matching supply is structurally dead — cf. `MultipedeWitness`); fold narrows nothing (28);
deck: the gauge seed constructs NOTHING (forces 1 vertex of 42 — girth 6 kills chaining) and even the
Z₇-translate seed stalls (gauge words avoiding the seed compose ⟹ never unique; only the diagonal
completes, to the identity); deck2: the second stage per first pair is 689 continuations and the gauge
continuation FAILS the bijectivity gate; even a THIRD seed (the manual `deck3` step) leaves the gadget
layer unassigned and fails the gate. Force cannot act (the cells are single `Aut`-orbits:
`Z₂³ ⋊ (Z₇⋊...)` acts transitively on feet and on gadget vertices). **A true mutual stall of the whole
built stack — the C3 constructor gate is OPEN.** Constructor decision recorded in remaining-work §1C:
propagation-shaped mechanisms cannot reach weight-≥3 gauge words; the route is the KERNEL SUPPLY
(structural rail-pair/cluster extraction → F₂ Gaussian elimination → emit basis flips → verify), with
①c via the `SameOrbits` reduction (a Gaussian basis is pivot-order-dependent — trap #7 — but the
GENERATED GROUP is basis-independent; flips commute, so kernel words are products = symmetric
differences of basis words — exactly the P3b/TreePrune license shape). -/

def onLine (i j : Nat) : Bool := j == i || j == (i+1) % 7 || j == (i+3) % 7

def inS (i s j : Nat) : Bool :=
  let a := i; let b := (i+1) % 7; let c := (i+3) % 7
  if s == 1 then j == a || j == b
  else if s == 2 then j == a || j == c
  else if s == 3 then j == b || j == c
  else false

def mpfg (f g : Nat) : Bool :=
  let j := f / 2; let bb := f % 2
  let i := (g - 14) / 4; let s := (g - 14) % 4
  onLine i j && (bb == (if inS i s j then 1 else 0))

def mpB (x y : Nat) : Bool :=
  if x < 14 && 14 ≤ y && y < 42 then mpfg x y
  else if y < 14 && 14 ≤ x && x < 42 then mpfg y x
  else false

def mp7 : AdjMatrix 42 := ⟨fun i j => if mpB i.val j.val then 1 else 0⟩
def mpRoot : Refine.ColData 42 := Refine.warmRefineVec mp7 (fun _ => 0)
def mk42 (x : Nat) : Fin 42 := ⟨x % 42, by omega⟩

#guard ((List.finRange 42).map mpRoot.col).dedup.length = 2
#guard (branches mpRoot.col).map Fin.val = (List.range 28).map (· + 14)

/-- The weight-4 gauge word: flip the foot pairs of `{2,4,5,6}` (= complement of line δ(0));
gadget vertices follow by the unique parity-matched partner. -/
def wSupp (j : Nat) : Bool := j == 2 || j == 4 || j == 5 || j == 6

def gaugeFun (v : Fin 42) : Fin 42 :=
  if v.val < 14 then
    let j := v.val / 2
    if wSupp j then mk42 (2*j + (1 - v.val % 2)) else v
  else
    let i := (v.val - 14) / 4; let s := (v.val - 14) % 4
    let ok := fun s' => (List.range 7).all (fun j =>
      !(onLine i j) || ((inS i s' j) == ((inS i s j) != wSupp j)))
    match (List.range 4).filter ok with
    | [s'] => mk42 (14 + 4*i + s')
    | _ => v

#guard (match Deck2.permOf gaugeFun with
  | some ρ => decide (Consume.IsColAut mp7 mpRoot.col ρ)
  | none => false)

/-! Pin-blindness + the full stack, dead: -/
def mpN2 : Refine.ColData 42 := Refine.warmRefineVec mp7 (indivOne mpRoot.col (mk42 0))
#guard ((List.finRange 42).map mpN2.col).dedup.length = 6
#guard (narrow (consume (Fold.foldSupplyFast)) mp7 mpRoot.col).length = 28
#guard (Deck.deckCandFast mp7 mpRoot.col (mk42 0) (mk42 1)).isNone   -- the gauge seed
#guard (Deck.deckCandFast mp7 mpRoot.col (mk42 0) (mk42 2)).isNone   -- the translate seed

def mfG : Vector (Option (Fin 42)) 42 := Deck.propagateVec mp7 mpRoot.col (mk42 0) (mk42 1)
#guard (List.finRange 42).countP (fun v => (mfG.get v).isNone) = 41  -- girth 6: NOTHING chains
#guard (Deck2.secondsV mp7 mpRoot.col mfG).length = 689

def cont1 (mf : Vector (Option (Fin 42)) 42) (v₁ v₂ : Fin 42) : Vector (Option (Fin 42)) 42 :=
  (Deck.roundVecD mp7 mpRoot.col)^[42]
    (Vector.ofFn (fun v => if v = v₁ then some v₂ else mf.get v))

#guard (Deck2.permOf (fun x => ((cont1 mfG (mk42 2) (mk42 3)).get x).getD x)).isNone
-- the deck2 gauge continuation fails the gate; a THIRD seed (deck3) fails too:
#guard (Deck2.permOf (fun x =>
  ((cont1 (cont1 mfG (mk42 2) (mk42 3)) (mk42 8) (mk42 9)).get x).getD x)).isNone

/-! ## 14. `C3a` — the KERNEL supply RECOVERS AND SOLVES the mp7 gauge (tranche 1, 2026-07-19)

The constructor §13's verdict demanded, measured. `Kernel.kernelSupply` (see `KernelSupply.lean`):
rails = **exactly the 7 foot pairs** (unique-twin detection from raw structure); constraint extraction
+ F₂ elimination recover **the [7,3,4] simplex code** (basis dim 3, weights [4,4,4]); the
all-or-nothing gate passes (3 verified generators); the root gadget cell narrows **28 → 7** — the
ENTIRE gauge consumed in one supply call, no propagation, no depth. The standing 7 = the Z₇
translations: deck stalls on them precisely because the gauge commutes (§13) — that composition is
the C3b follow-on (deck-modulo-the-verified-kernel-group), not a kernel-supply defect. At the pinned
node the recovered basis RESTRICTS to dim 2 = exactly the simplex words avoiding the pinned segment
(the theory's prediction, measured), and the 6-cell target narrows 6 → 3. Harmless elsewhere:
0 generators on t3 / ut / wcyc9. Wiring gate = `Regression` §15. -/

#guard (Kernel.rails Regression.mp7 Regression.mp7Root.col).map (fun p => (p.1.val, p.2.val))
    = [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13)]
#guard (Kernel.kernelBasis Regression.mp7 Regression.mp7Root.col
    (Kernel.rails Regression.mp7 Regression.mp7Root.col)).map (fun w => w.countP id) = [4, 4, 4]
#guard (narrow (consume Kernel.kernelSupply) Regression.mp7 Regression.mp7Root.col).length = 7

def mpPin : Refine.ColData 42 :=
  Refine.warmRefineVec Regression.mp7 (indivOne Regression.mp7Root.col (mk42 0))
#guard (Kernel.rails Regression.mp7 mpPin.col).length = 6
#guard (Kernel.kernelGens Regression.mp7 mpPin.col).length = 2
#guard (branches mpPin.col).map Fin.val = [14, 17, 30, 31, 38, 40]
#guard (narrow (consume Kernel.kernelSupply) Regression.mp7 mpPin.col).length = 3
#guard (Kernel.kernelGens Regression.ut Regression.utRoot.col).length = 0
#guard (Kernel.kernelGens Regression.wcyc9 Regression.wcyc9Root.col).length = 0

/-! ## 15. `C3b` — WHAT IS ACTUALLY MISSING ON `mp7`, measured (2026-07-19)

§14 leaves the Z₇ translations standing. This section pins down **exactly** what a C3b mechanism has
to produce, and it is a single generator.

* The naive base translation — foot pair `j ↦ j+1` (parity bit preserved), gadget `i ↦ i+1` (subset
  type preserved) — **lifts unchanged**: it passes the bijectivity gate and IS a colour-automorphism
  of `mp7`. (It must: `j ↦ j+1` preserves the Fano lines `δ(i) = {i, i+1, i+3}` setwise *and*
  preserves each line's internal `{a,b,c}` labelling, so the incidence parities go across verbatim.)
* Kernel generators alone: the orbit of a gadget vertex is **4** — the gadget's own even-subset quad,
  i.e. exactly the gauge, exactly as designed.
* Kernel generators **+ that one translation**: the gadget-vertex orbit is **28 = the whole branch
  cell**, and the foot orbit is **14 = every foot**.

⟹ **`mp7` answers at the root the moment ONE base-symmetry generator is supplied.** The kernel
supply already covers the entire rest of the group. This is the C3b acceptance, reduced to a target
small enough to design against.

⚠ And it rules a mechanism OUT. "deck modulo the verified subgroup" cannot be the answer *by itself*:
§13 measured that the translate seed forces **1 vertex of 42** — girth 6 means nothing chains, and
quotienting by `K` does not create chaining where there is none. Propagation is not the vehicle here
at any modulus. What the translation *is*, structurally, is an automorphism of the **base** object
the kernel supply already extracts (rails = the 7 segments, wire supports = the 7 checks; their
incidence IS the Fano plane). So the C3b route is **base-graph recovery + lift**, and the lift's
choice-dependence is licensed the same way the Gaussian basis was — two lifts of the same base
automorphism differ by an automorphism inducing the identity on the base, i.e. by a pure gauge
element, i.e. by an element of `K`, which the kernel supply already emits. Design note:
remaining-work §1C C3 (ii-c). -/

def transFun (v : Fin 42) : Fin 42 :=
  if v.val < 14 then mk42 (2 * ((v.val / 2 + 1) % 7) + v.val % 2)
  else mk42 (14 + 4 * (((v.val - 14) / 4 + 1) % 7) + (v.val - 14) % 4)

#guard (match Deck2.permOf transFun with
  | some ρ => decide (Consume.IsColAut Regression.mp7 Regression.mp7Root.col ρ)
  | none => false)

def orbitOf (gs : List (Equiv.Perm (Fin 42))) (x : Fin 42) : List (Fin 42) :=
  (fun s => (s ++ s.flatMap (fun y => gs.map (fun g => g y))).dedup)^[8] [x]

def mpKernelGens : List (Equiv.Perm (Fin 42)) :=
  Kernel.kernelGens Regression.mp7 Regression.mp7Root.col

#guard (orbitOf mpKernelGens (mk42 14)).length = 4                              -- the gauge alone
#guard (orbitOf (mpKernelGens ++ (Deck2.permOf transFun).toList) (mk42 14)).length = 28
#guard (orbitOf (mpKernelGens ++ (Deck2.permOf transFun).toList) (mk42 0)).length = 14

/-! ## 16. `C3b` — the DEEPENING supply CERTIFIES the mp7 base symmetry (tranche 1, 2026-07-20)

`deepenSupply` (`DeepenSupply.lean`) is the port of the C# `HarvestTwists`: deepen an anchor of the
branch cell to an all-singleton footprint recording the chosen cell ids, replay that id sequence
from every other representative, match footprint colours on the coupled component, verify. It is
the answer to what §15 measured as missing — the `Z₇`/`PGL(3,2)` BASE symmetry that survives after
`kernelSupply` certifies the gauge, and that no propagation-shaped supply reaches (girth 6 ⟹ a seed
forces 1 vertex of 42 and nothing chains, at any number of seeds).

Measured here: the branch cell has 28 members; the supply yields **756 = 28 × 27 verified
generators** (every ordered pair of representatives); and the gadget cell (28) and the foot cell (14)
each collapse to a **SINGLE ORBIT** — compare §14, where the kernel alone gives a gadget orbit of 4
(the gauge), and §15, where supplying the translation by hand was needed to reach 28.

⚠ It quantifies over EVERY anchor, not one: with a single anchor ①c is measured FALSE (the `G8`
falsifier — see the `DeepenSupply` header). `mp7` cannot detect that, because it fires totally here;
an equivariance falsifier needs a PARTIALLY-firing witness. Cross-check: the C# canonizer reports |Aut| = 1344 = 8 × 168 on the same
object (`FanoMultipedeProbe.cs`), i.e. gauge × the full Fano collineation group.

⚠ Cost note (~3 min): a first prototype of this measurement ran **> 1 hour**. The cures are the
project's standing traps — materialise the twist as a `Vector` (trap #1: a closure re-ran
`List.find?` on each of `IsColAut`'s ~2n² applications), hoist the per-representative refinement out
of the inner loop, and compute the `O(n³)` `coupled` once per level rather than per pair. -/
def mpDeepenGens : List (Equiv.Perm (Fin 42)) :=
  Deepen.deepenGens Regression.mp7 Regression.mp7Root.col

#guard (Descend.branches Regression.mp7Root.col).length = 28
#guard mpDeepenGens.length = 756
-- ★ THE C3 ACCEPTANCE: both cells are single orbits, from the deepen gens ALONE
#guard (orbitOf mpDeepenGens (mk42 14)).length = 28
#guard (orbitOf (mpKernelGens ++ mpDeepenGens) (mk42 14)).length = 28
#guard (orbitOf (mpKernelGens ++ mpDeepenGens) (mk42 0)).length = 14

/-! ## §18 — the UNION guard is STRICTLY stronger than any member (2026-07-27)

`DeepenGuard` §8 proves the union is never *worse* (`certPath_append_left/right`). This measures that
it is strictly **better**, which no theorem states — and names the mechanism:

> `CertPath` is a **conjunction over the levels of one greedy path**, and different supplies certify
> different levels. So the union can certify a path that **no single member certifies** — the gain is
> emergent, not a maximum over the members.

`t3` is the witness: all four equivariant supplies are SHUT on every branch, `guardSupply` is OPEN on
every branch — firing 0/3 → 3/3 where every individual supply fails. This is the entire justification
for §8, and `certPath_append_*` cannot supply it (monotonicity is not strictness).

⚠ **The price is real and visible**, which is what the billed `certPathCost` (`DeepenGuard` §5a) is
for: the union bills `1385216550` here against `deckSupply`'s `6176250`, a ~224× multiple, because the
union's `supplyCost` is the **sum** of its members'. Under the old flat `n⁴` the trade was invisible.

⚠ Cost note: this lives here rather than in `Regression` precisely because of that — the regression
suite's contract is that it stays fast, and evaluating the union's guard is not cheap even at `n = 5`
(~49 s there, ~95 s here). `Regression` §17a keeps only the free half of the comparison: that
`deck2Supply` alone is shut on `C5`. -/

#guard (Descend.branches Regression.t3Root.col).all (fun v =>
  !decide (Deepen.CertPath (Fold.foldSupplyFast (n := 15)) Regression.t3 15
      (Deepen.step Regression.t3 Regression.t3Root.col v))
  && !decide (Deepen.CertPath (Deck.deckSupply (n := 15)) Regression.t3 15
      (Deepen.step Regression.t3 Regression.t3Root.col v))
  && !decide (Deepen.CertPath (Deck2.deck2Supply (n := 15)) Regression.t3 15
      (Deepen.step Regression.t3 Regression.t3Root.col v))
  && !decide (Deepen.CertPath (Consume.matchSupply (n := 15)) Regression.t3 15
      (Deepen.step Regression.t3 Regression.t3Root.col v)))

#guard (Descend.branches Regression.t3Root.col).all (fun v =>
  decide (Deepen.CertPath (Deepen.guardSupply (n := 15)) Regression.t3 15
      (Deepen.step Regression.t3 Regression.t3Root.col v)))

/-! The smaller `C5` instance of the same phenomenon: `deck2Supply` shut on every branch, the union
open and **substantive** (`certPathCost > 0`, so not the AKRV-vacuous case) on every branch. -/
#guard (Descend.branches (Refine.warmRefineVec Regression.C5 (fun _ => 0)).col).all (fun v =>
  !decide (Deepen.CertPath (Deck2.deck2Supply (n := 5)) Regression.C5 5
      (Deepen.step Regression.C5 (Refine.warmRefineVec Regression.C5 (fun _ => 0)).col v)))
#guard (Descend.branches (Refine.warmRefineVec Regression.C5 (fun _ => 0)).col).all (fun v =>
  decide (Deepen.CertPath (Deepen.guardSupply (n := 5)) Regression.C5 5
      (Deepen.step Regression.C5 (Refine.warmRefineVec Regression.C5 (fun _ => 0)).col v))
  && (0 < Deepen.certPathCost (Deepen.guardSupply (n := 5)) Regression.C5 5
      (Deepen.step Regression.C5 (Refine.warmRefineVec Regression.C5 (fun _ => 0)).col v)))

end ChainDescent.Perf
