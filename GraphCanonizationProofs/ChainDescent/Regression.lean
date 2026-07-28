import ChainDescent.Residue
import ChainDescent.Deck2
import ChainDescent.KernelSupply
import ChainDescent.MatchSupply
import ChainDescent.DeepMatchSupply
import ChainDescent.PrunedSupply
import ChainDescent.TreePrune
import ChainDescent.PartialMatch
import ChainDescent.SelectNode
import ChainDescent.FoldSupply
import ChainDescent.DeckSupply
import ChainDescent.HolKey
import ChainDescent.DeepenGuard
import ChainDescent.FoldFast
import ChainDescent.RecordKey

/-!
# The build-gating REGRESSION suite — cheap, and on the critical path

**This file must stay fast.** Every check here earns its place by catching something a *theorem* cannot:

* **an instance wiring bug** — the theorems quantify over *arbitrary* `key`/`Supply`, so a broken concrete instance
  (`lookaheadKey`, `matchSupply`) satisfies every one of them and still canonizes nothing;
* **a firing regression** — soundness and totality are proved, but `NarrowProper` is satisfied by a resolver that
  returns the *whole cell*, so **"it actually narrows"** can only be *observed*;
* **a measured counterexample** — that a non-equivariant supply really does break `①c`.

**What does NOT belong here** (it lives in `ChainDescent/PerformanceTest.lean`, deliberately **not** in `build.sh` —
run it on demand with `lake build ChainDescent.PerformanceTest`):

* anything already a theorem (`deferAll` answers ⟸ `Refine.exhaustive_canonizer`);
* the same property re-checked on `C₃…C₇` when `C₅` settles it;
* every cost `#eval`, and the `n = 12` Frucht graph.

**Scale discipline (this is where the time went).** `lookaheadKey` costs one full warm refinement *per branch*, so a
node costs `Θ(|cell| · n³)`: **~1 s per key evaluation at `n = 12`**, i.e. ~12 s for a single root narrowing on the
Frucht graph, and ~31 s for one guarded mixed descent. Nothing here needs `n = 12`: force's firing needs a **1-WL
cell that is not an orbit**, and *any* regular non-vertex-transitive graph gives one (1-WL is a single cell on
**every** regular graph). `G8` below is `8` vertices and ~8× cheaper.
-/

namespace ChainDescent.Regression

open ChainDescent ChainDescent.Descend ChainDescent.Refine
open ChainDescent.Force ChainDescent.Consume ChainDescent.Composite ChainDescent.Stall

/-! ## The graphs — as small as the property allows -/

/-- The 5-cycle: vertex-transitive, so **every cell is an orbit** — consume's domain, force's blind spot. -/
def C5 : AdjMatrix 5 := ⟨fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 1 else 0⟩

/-- The 5-path: `Aut = ℤ₂` (the reflection), 1-WL leaves the orbit cells `{0,4}`, `{1,3}`, and individualizing
**discretizes** — so it is `Consume.Discretizing` and the colour-match oracle can actually fire on it. -/
def P5 : AdjMatrix 5 := ⟨fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0⟩

/-- **A cubic graph on 8 vertices that is NOT vertex-transitive**: two triangles `{0,1,2}`, `{3,4,5}`, with `6` and
`7` in no triangle at all. Being **regular**, 1-WL leaves a **single cell of all 8**; not being vertex-transitive,
that cell is **not an orbit** — which is exactly force's domain and consume's blind spot, at `n = 8` instead of the
Frucht graph's `n = 12`. -/
def G8 : AdjMatrix 8 := ⟨fun i j =>
  let e : List (Nat × Nat) :=
    [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,6),(3,6),(6,7),(1,7),(4,7),(2,5)]
  if e.contains (i.val, j.val) ∨ e.contains (j.val, i.val) then 1 else 0⟩

/-- The **full** `Aut(Cₙ) = Dₙ = ⟨rotation, reflection⟩`, handed back as a *fixed* list — hence **not**
equivariant, which is precisely what the `①c` counterexample (§6) needs. -/
def dihSupply (m : Nat) [NeZero m] : Supply m :=
  fun _ _ => ([Equiv.addRight (1 : Fin m), Equiv.neg (Fin m)], m)

/-! ## 1. The object is a canonical form (integration, not re-proof) -/

def form {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast deferAll a).map flatten

/-! **`①b`/`①c`** — relabelling must not change the answer. -/
#guard form C5 = form (relabelAdj (Equiv.swap 0 2) C5)
/-! **Distinguishing power** — a canonizer returning a constant would pass everything above. -/
#guard form C5 ≠ form P5

/-! ## 2. `consume` is VALUE-INVISIBLE (the `Covering` route, exercised) -/

def formC {m : Nat} [NeZero m] (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (consume (dihSupply m)) a).map flatten

/-! It must compute **exactly** the exhaustive form — only cheaper. A resolver that pruned a branch it should not
have would fail here and nowhere else. -/
#guard formC C5 = form C5

/-! ## 3. FIRING — each resolver on its own domain, and on its blind spot -/

/-! 1-WL leaves `G8` as a single cell of 8 (it is regular). -/
#guard (branches (refineV encodeFreeFast G8 (fun _ => 0))).length = 8

/-! **★ force FIRES on a cell that is not an orbit**: `8 → 4`. -/
#guard (narrow (forceBy lookaheadKey) G8 (refineV encodeFreeFast G8 (fun _ => 0))).length = 4

/-! **★ force provably CANNOT fire on an orbit cell** (`forceBy_no_narrowing_on_orbit`, observed): `5 → 5`. -/
#guard (narrow (forceBy lookaheadKey) C5 (refineV encodeFreeFast C5 (fun _ => 0))).length = 5

/-! **★ consume collapses the orbit cell force cannot touch**: `5 → 1`, via the mixed resolver. -/
#guard (narrow (forceThenConsume lookaheadKey (dihSupply 5)) C5
          (refineV encodeFreeFast C5 (fun _ => 0))).length = 1

/-! ## 4. The STALL GUARD — it answers or it flags, and it is a single path either way -/

def gForce {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceBy lookaheadKey)) a).map flatten

/-! Force alone **flags** on a vertex-transitive graph — correctly: it cannot fire on an orbit cell, so it **stops**
instead of branching. `①c` holds either way (both sides flag ⟹ equal). -/
#guard ¬ (gForce C5).isSome
#guard gForce C5 = gForce (relabelAdj (Equiv.swap 0 2) C5)

/-! ## 5. `matchSupply` — the cascade oracle: it repairs `①c`, and ONE STEP IS NOT ENOUGH -/

def gMatch {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) a).map flatten

/-! **The diagnosis, pinned.** `Consume.Discretizing` — the cascade oracle's `hdisc` depth witness — **excludes
cycles**: individualizing one vertex of `C₅` leaves `{0},{1,4},{2,3}`, which is not discrete. `P5` *does*
discretize. This single pair of guards is the whole reason the one-step colour match is not enough. -/
#guard ¬ Discrete ((Consume.lookData C5 (refineV encodeFreeFast C5 (fun _ => 0)) 0).col)
#guard Discrete ((Consume.lookData P5 (refineV encodeFreeFast P5 (fun _ => 0)) 0).col)

/-! **So the structural oracle FLAGS on cycles** (it constructs nothing there) — the gap the multi-step /
cross-branch harvest must close — **and answers where the node discretizes**, with no hand-supplied generators. -/
#guard ¬ (gMatch C5).isSome
#guard (gMatch P5).isSome

/-! **★ `①c` RESTORED.** `matchSupply` is a *structural function of `(adj, χ)`*, hence equivariant — unlike the
fixed-generator demo supplies (§6). -/
#guard gMatch P5 = gMatch (relabelAdj (Equiv.swap 0 3) P5)
#guard gMatch G8 = gMatch (relabelAdj (Equiv.swap 0 5) G8)

/-! ## 6. ⚠ THE COUNTEREXAMPLE — a NON-equivariant supply breaks `①c`

The **non-vacuity witness for `Stall.StallEquivariant`**, asserted on purpose. `dihSupply` hands back a *fixed*
generator list ignoring `adj`, but `Aut(σ·C₅) = σ·D₅·σ⁻¹` — so those generators fail to verify on the relabelled
graph, and `C₅` **answers** while `σ·C₅` **flags**.

Soundness needs **nothing** from the supply (`consume_canonizer` holds for *every* supply, because a covering
resolver is *value*-invisible). **A flag is not value-invisible.** This `#guard` is what proves the hypothesis
cannot be dropped — delete `StallEquivariant` and `①c` is false. -/

def gMix {m : Nat} [NeZero m] (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey (dihSupply m))) a).map flatten

#guard (gMix C5).isSome ≠ (gMix (relabelAdj (Equiv.swap 0 2) C5)).isSome

/-! ## 7. ★★★ `deepMatchSupply` — THE RESIDUE SHRINKS, WITH NO RE-PROOF

`C₄` is the cheapest witness of the whole `P2` thesis. `Aut(C₄) = D₄` has a **reflection fixing vertex 0**, so
individualizing one vertex cannot discretize (`Discretizing` is false) — and `Discretizing ⟹ trivial point
stabilizers`, so the one-step oracle **provably cannot** fire. It flags.

Individualizing **one more** vertex *does* discretize. `deepMatchSupply 1` enumerates every length-≤1 continuation,
so it finds the pair that reconstructs the rotation, and the graph **answers**.

**Nothing was re-proved to get this.** `①a`/`①b`/`①c` and the polynomial bound are quantified over an arbitrary
`Supply`; raising `d` moved the boundary of `Residue.Handled` and nothing else. That is the architecture doing its
job, and it is the point of defining the residue as the complement of a *positive* capability. -/

def C4 : AdjMatrix 4 := ⟨fun i j => if (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val then 1 else 0⟩

def gDeep {m : Nat} (d : Nat) (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume lookaheadKey (DeepMatch.deepMatchSupply d))) a).map flatten

/-! **`d = 0` FLAGS, `d = 1` ANSWERS.** The left component is `matchSupply`'s reach (`separatesAt_zero_iff`); the
right is the bounded-depth oracle's. **Do not delete this guard** — it is the non-vacuity witness that `d` buys
firing, and the only thing separating `deepMatchSupply` from a silently useless generalization. -/
#guard ((gDeep 0 C4).isSome, (gDeep 1 C4).isSome) = (false, true)

/-! `①c` at depth 1: `deepMatchSupply` is equivariant (`gensEquivariant_deepMatchSupply`), so the answer
transports. Measured, not merely proved. -/
#guard gDeep 1 C4 = gDeep 1 (relabelAdj (Equiv.swap 0 1) C4)

/-! **`prunedSupply` gives the SAME answer as `deepMatchSupply`** — the behavioural witness of
`PrunedSupply.sameOrbits_deepMatchSupply` (proved: same orbits ⟹ same guarded canonizer). Reference-matching is a
pure cost win, and this guard proves a wiring bug in it (matching from the wrong reference, or dropping a generator)
would change the answer and fail the build. -/
def gPruned {m : Nat} (d : Nat) (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume lookaheadKey (PrunedSupply.prunedSupply d))) a).map flatten

#guard gPruned 1 C4 = gDeep 1 C4

/-! ## 8. `F1` — the fold family: support-local matching fires where full matching is DEAD

The F_k fold-cover gap (2026-07-16 audit; `docs/chain-descent-fold-tower-plan.md`): on a `k`-fold cover the
copies are 1-WL twins, so `matchCol` — which demands **globally discrete** colourings — needs `d ≥ k − 2`, and
the whole family costs `n^{Ω(k)}`. `partialMatchSupply` matches the **support** instead: a copy transposition is
caught at the depth that discretizes ONE copy, independent of `k`.

Witness: **4 disjoint copies of a 6-vertex 1-WL-discrete (hence asymmetric) core** — the smallest fold on which
`d = 0` separates the two supplies (`k = 3` would let `deepMatchSupply 1` in by elimination). Measured 2026-07-17:
`deepMatchSupply` is dead at `d = 0` (0 verified, no narrowing) **and** `d = 1` (supplyCost 8 524 800, still no
narrowing — PerformanceTest); `partialMatchSupply 0` verifies 16 generators and collapses the cell to ONE branch
at supplyCost 64 512. **Do not delete these guards** — they are the non-vacuity witness that support-locality buys
firing, and the only thing separating `partialMatch` from a silently useless generalization of `matchCol`. -/

/-- Path `0-1-2-3-4-5` plus the chord `1-3` — 1-WL-discrete, so each copy of it is rigid and refinement-visible. -/
def coreE (a b : Nat) : Bool :=
  decide ((a, b) ∈ [(0,1),(1,2),(2,3),(3,4),(4,5),(1,3)]) ||
  decide ((b, a) ∈ [(0,1),(1,2),(2,3),(3,4),(4,5),(1,3)])

def core6 : AdjMatrix 6 := ⟨fun i j => if coreE i.val j.val then 1 else 0⟩

/-- The 4-fold cover (disjoint form): copy = `i / 6`, core vertex = `i % 6`. -/
def fold4 : AdjMatrix 24 :=
  ⟨fun i j => if i.val / 6 = j.val / 6 && coreE (i.val % 6) (j.val % 6) then 1 else 0⟩

/-- Materialized root colourings — `ColData`-backed (standing trap #1: an inline `Colouring`-typed expression
re-runs the refinement on every colour lookup; at `n = 24` that turns these guards from ~2 s into minutes). -/
def core6Root : Refine.ColData 6 := Refine.warmRefineVec core6 (fun _ => 0)
def fold4Root : Refine.ColData 24 := Refine.warmRefineVec fold4 (fun _ => 0)

/-! The demo is honest: the core really is 1-WL-discrete, and the fold's branch cell really is the 4 copies. -/
#guard Discrete core6Root.col
#guard (branches fold4Root.col).length = 4

/-! **Full matching is DEAD at `d = 0`** — pinning one vertex leaves copies 2–4 as mutual twins, nothing is
`Discrete`, `matchCol` constructs nothing: 0 verified generators, no narrowing. -/
#guard (Consume.verified (DeepMatch.deepMatchSupply 0) fold4 fold4Root.col).length = 0
#guard (narrow (consume (DeepMatch.deepMatchSupply 0)) fold4 fold4Root.col).length = 4

/-! **Support-local matching FIRES at `d = 0`** — every copy transposition is identity off two copies, and
pinning one vertex discretizes one of them: 16 verified generators, the cell collapses to ONE branch. -/
#guard (Consume.verified (PartialMatch.partialMatchSupply 0) fold4 fold4Root.col).length = 16
#guard (narrow (consume (PartialMatch.partialMatchSupply 0)) fold4 fold4Root.col).length = 1

/-! The descent-level consequences need no guard here: narrowing to `≥ 2` branches ⟹ the guard flags is
`Stall.resolvedAll_guard` (a theorem, by construction), so `narrow = 4` above already settles that the deep-match
descent **flags** on the fold. The measured end-to-end pair — the same guarded descent with `partialMatchSupply 0`
**answers** with a full canonical form (~3.5 min, `constKey`, n = 24) while `deepMatchSupply 0` flags, plus the
relabelling invariance of the answer — lives in `PerformanceTest` §7 (off the build path; the descent at `n = 24`
is ~80 s even to flag at the root, which would swamp this suite). -/

/-! ## 9. The FUSED selector (`Select.selNode`) — dominance parity, measured

The sel rewrite's behavioural gates. The DOMINANCE theorem (`Select.canonFormS?_selNode_dominates`) proves the
fused object answers with the SAME value wherever the guarded blind object answers; these guards measure the
instantiation through the runnable twin `Select.canonFormFastS?` (= `canonFormS?` at `encodeFreeFast`,
definitionally — `canonFormFastS?_eq`). A wiring bug in `selColour`/`cellNarrow` would break value equality here
and nowhere else.

⚠ The EXPOSURE witness (blind-with-least-rooted-harvest FLAGS, fused-with-all-cells-harvest ANSWERS — the `Z4S`
graph, n = 14) lives in `ChainDescent/SelectWitness.lean`, deliberately OFF the build path (minutes of eval,
like `PerformanceTest`); run it on demand with `lake build ChainDescent.SelectWitness`. -/

def gSel {m : Nat} (a : AdjMatrix m) : Option (List Nat) :=
  (ChainDescent.Select.canonFormFastS? lookaheadKey matchSupply a).map flatten

def gSelDeep {m : Nat} (d : Nat) (a : AdjMatrix m) : Option (List Nat) :=
  (ChainDescent.Select.canonFormFastS? lookaheadKey (DeepMatch.deepMatchSupply d) a).map flatten

/-! **Value-exact dominance, measured**: where the blind object answers, the fused object answers identically. -/
#guard (gSel P5).isSome
#guard gSel P5 = gMatch P5
#guard (gSelDeep 1 C4).isSome
#guard gSelDeep 1 C4 = gDeep 1 C4

/-! **Flag parity** where the blind object flags with the same supply (`C5`: one cell, nothing resolvable at
`d = 0` — the fused selector changes which cells are PROBED, never what a probe can prove). -/
#guard ¬ (gSel C5).isSome

/-! **`①c`, behavioural, for the fused object** (its theorem form is `Select.selNode_canonizer` /
`selNode_match_canonizer`). -/
#guard gSel P5 = gSel (relabelAdj (Equiv.swap 0 3) P5)

/-! ## 10. `F2a` — the STRUCTURAL fold supply fires where refinement-based matching is DEAD

The fold/tower plan's second move (`docs/chain-descent-fold-tower-plan.md` §4). §8's fold had a
refinement-visible core, so F1's support-local matching sufficed. Here the core is `C₄` + a pendant: its mirror
(1 ↔ 3) **survives every pin on the mirror axis**, so a copy is never discretized and `CatchesAt` fails at every
depth — refinement-based candidate construction is structurally blind (the miniature of the WL-blind multipede
copy). `Fold.foldSupply` reads the fold off the CELL structure instead (fibers = same-cell components, copies =
cross-cell components, fiber-wise swap, involution gate) and does not care.

Witness: 2 copies of the core, one vertical matching edge per fiber (`vfold2`, n = 10). Measured 2026-07-18:
the branch cell is the two pendant copies; `deepMatchSupply 0` and `partialMatchSupply 0` leave it un-narrowed
(the copy swap moves the mirror-tied vertices, singleton on NEITHER side); `foldSupply` verifies 4 generators
and collapses it to ONE branch. **Do not delete these guards** — they are the non-vacuity witness that
structural detection buys firing beyond every matching supply, and the only observation separating `foldSupply`
from a silently useless port. -/

/-- `C₄` (0-1-2-3-0) + pendant 4 on 0 — arithmetic edge predicate (cheap per interpreted lookup). -/
def vcoreB (a b : Nat) : Bool :=
  (a + 1 == b && b ≤ 3) || (b + 1 == a && a ≤ 3) ||
  (a == 0 && b == 3) || (a == 3 && b == 0) ||
  (a == 0 && b == 4) || (a == 4 && b == 0)

/-- 2 copies, a vertical matching edge on every fiber: copy = `i / 5`, core vertex = `i % 5`. -/
def vfold2 : AdjMatrix 10 :=
  ⟨fun i j => if (i.val / 5 == j.val / 5 && vcoreB (i.val % 5) (j.val % 5)) ||
      (i.val / 5 != j.val / 5 && i.val % 5 == j.val % 5) then 1 else 0⟩

def vfold2Root : Refine.ColData 10 := Refine.warmRefineVec vfold2 (fun _ => 0)

/-! The branch cell is the two pendant copies (`4` and `9` = copy-1's pendant), and the within-copy mirror
class `{1,3}` really is merged (a 4-cell) — the blindness is present, not hypothetical. -/
#guard branches vfold2Root.col = [4, 9]

/-! **Refinement-based matching is DEAD** — both supplies leave the copy cell un-narrowed. -/
#guard (narrow (consume (DeepMatch.deepMatchSupply 0)) vfold2 vfold2Root.col).length = 2
#guard (narrow (consume (PartialMatch.partialMatchSupply 0)) vfold2 vfold2Root.col).length = 2

/-! **Structural detection FIRES** — 4 verified candidates (the copy swap from each seed pair), ONE branch. -/
#guard (Consume.verified (Fold.foldSupply) vfold2 vfold2Root.col).length = 4
#guard (narrow (consume (Fold.foldSupply)) vfold2 vfold2Root.col).length = 1

/-! The materialised-table twin (`FoldFast.foldSupplyFast`) — `foldSupplyFast_eq` is the parity THEOREM;
this guard is the wiring smoke test (a broken table would fail here and nowhere else). -/
#guard (narrow (consume (Fold.foldSupplyFast)) vfold2 vfold2Root.col).length = 1

/-! ## 11. `F2b` — the propagation supply catches generators of ANY order (the odd-arity gap)

Every consume-side constructor before it emits INVOLUTIONS only, so a cover whose deck group is cyclic of odd
order — no involutions in `Aut` at all — is beyond `matchCol`, F1, F2a AND the C# (`TryDoublingPeel` is
`s % 2 ≠ 0 → null`; odd part ≥ 7 has no C# path at any size). Witness: the weighted cycle `C₉`, edge weights
(1,2,3) repeating — `Aut = Z₃` exactly (rotations by 3; the weight pattern kills every reflection), WL-stable
at three 3-cells. `Fold.foldSupply` degenerates (no vertical fibers ⟹ its lookup yields the identity) and
cannot narrow; `Deck.deckSupply` propagates every seed to the full rotation and collapses the cell. (On this
small witness a PIN discretizes the cycle, so the matching supplies also fire — the machine-checked separation
here is against the involution-based structural supply; the odd-arity/refinement-free value is
`PerformanceTest` §9 and the plan doc §4b.) **Do not delete** — the non-vacuity witness for `deckSupply`. -/

/-- Weighted cycle `C_N` (`N = 3s`): edge `i — i+1` has weight `i % 3 + 1`; `Aut = Z_s`, involution-free for
odd `s`. -/
def wEdge (N a b : Nat) : Nat :=
  if (a + 1) % N == b then a % 3 + 1
  else if (b + 1) % N == a then b % 3 + 1
  else 0

def wcyc9 : AdjMatrix 9 := ⟨fun i j => wEdge 9 i.val j.val⟩
def wcyc9Root : Refine.ColData 9 := Refine.warmRefineVec wcyc9 (fun _ => 0)

#guard (branches wcyc9Root.col).map Fin.val = [1, 4, 7]

/-! **The involution-based structural supply is DEAD** (identity-only candidates; the cell stays a 3-fan). -/
#guard (narrow (consume (Fold.foldSupply)) wcyc9 wcyc9Root.col).length = 3

/-! **The propagation supply FIRES**: all 9 seed pairs complete — the three order-3 rotations, unreachable by
any involution emitter — and the cell collapses to ONE branch. -/
#guard (Consume.verified (Deck.deckSupply) wcyc9 wcyc9Root.col).length = 9
#guard (narrow (consume (Deck.deckSupply)) wcyc9 wcyc9Root.col).length = 1

/-! `①c`, behavioural (theorem form `gensEquivariant_deckSupply`). -/
def wcyc9Swapped : AdjMatrix 9 := relabelAdj (Equiv.swap 0 5) wcyc9
def wcyc9SwappedRoot : Refine.ColData 9 := Refine.warmRefineVec wcyc9Swapped (fun _ => 0)
#guard (narrow (consume (Deck.deckSupply)) wcyc9Swapped wcyc9SwappedRoot.col).length = 1

/-! **Complementarity, machine-checked**: on the mirror-tied fold the propagation STALLS — the surviving mirror
gives every cross-copy seed two extensions, so no forcing step on the mirror class is ever unique; only the
diagonal seeds complete (to the identity), and the copy cell stays un-narrowed — exactly where `foldSupply`
fires. And vice versa on the cycle. `Deck.appendSupply` covers both families with ONE supply object
(`foldDeckSupply_selNode_canonizer` is its capstone). -/
#guard (narrow (consume (Deck.deckSupply)) vfold2 vfold2Root.col).length = 2
#guard (narrow (consume (Deck.appendSupply Fold.foldSupply Deck.deckSupply)) vfold2 vfold2Root.col).length = 1
#guard (narrow (consume (Deck.appendSupply Fold.foldSupply Deck.deckSupply)) wcyc9 wcyc9Root.col).length = 1

/-! ## 12. `F3a` — the HOLONOMY key separates what 1-WL merges (the force-side gap)

The genuine force residue of the fold family (plan §5b): DISTINGUISHABLE-but-WL-MERGED cells. Witness:
`U3 ⊔ T3` — vfold3's core family (3 copies of the mirror-tied `C₄`+pendant, triangle of vertical matchings)
unioned with its one-pair-twisted variant. Twist parity around the copy triangle makes `T3 ≇ U3`; 1-WL merges
the components (the twist is invisible — the mirror class never splits), so the 6-pendant branch cell holds
TWO orbits; consume cannot resolve it as a matter of principle (no automorphism between non-isomorphic
components), and `lookaheadKey` is blind (pins leave the mirror tie; the histograms agree). `Hol.holKeyFast`
reads the fold's HOLONOMY — composing the vertical matchings around the copy triangle: identity on the U side,
the mirror on the T side — and keeps exactly the straight triple. **Do not delete** — the non-vacuity witness
for the force firing theorem (`keepMin_pairwise_aut_of_separates`'s hypothesis is REAL here: the kept branches
are one genuine orbit, which `foldSupply` collapses — measured at n = 15 in §10's family; the n = 30 composite
eval is only an F2a evaluation-constant away, see plan §5b). -/

/-- The twisted/untwisted vertical 3-fold: copy `c = i / 5`, core vertex `v = i % 5`; `twist01` crosses the
`{1, 3}` fiber edges of the (0,1) copy-pair. -/
def vfoldT (twist01 : Bool) (i j : Nat) : Bool :=
  let ci := i / 5; let vi := i % 5; let cj := j / 5; let vj := j % 5
  if ci == cj then vcoreB vi vj
  else if twist01 && ((ci == 0 && cj == 1) || (ci == 1 && cj == 0)) then
    (vi == 1 && vj == 3) || (vi == 3 && vj == 1) || (vi == vj && vi != 1 && vi != 3)
  else vi == vj

/-- `U3 ⊔ T3`, block-diagonal at 15 (n = 30). -/
def ut : AdjMatrix 30 := ⟨fun i j =>
  if i.val < 15 && j.val < 15 then (if vfoldT false i.val j.val then 1 else 0)
  else if 15 ≤ i.val && 15 ≤ j.val then (if vfoldT true (i.val - 15) (j.val - 15) then 1 else 0)
  else 0⟩

def utRoot : Refine.ColData 30 := Refine.warmRefineVec ut (fun _ => 0)

/-! 1-WL merges the two components' pendant cells — the branch cell spans both. -/
#guard (branches utRoot.col).map Fin.val = [4, 9, 14, 19, 24, 29]

/-! **The 1-WL look-ahead key is DEAD** — it keeps the whole 6-cell. -/
#guard (Force.keepMin Force.lookaheadKey ut utRoot.col (branches utRoot.col)).length = 6

/-! **The holonomy key FIRES**: the U-pendants' signature attains moved-count 0 (straight triangles compose to
the identity), the T-pendants' does not (the twisted triangle moves the mirror pair) — presence-first
encoding, so `keepMin` keeps exactly the straight triple, ONE genuine orbit. -/
#guard (Force.keepMin Hol.holKeyFast ut utRoot.col (branches utRoot.col)).map Fin.val = [4, 9, 14]



/-! ## 13. `P3c` SECOND HALF — the TREE-PRUNED supply answers identically, and the tree really is smaller

`TreePrune.treeSupply` grows the `(branch, sequence)` search space level by level and orbit-prunes each level by a
**seed** group. `sameOrbits_treeSupply` proves it reaches the same orbits as the full enumeration for an *arbitrary
untrusted seed*, so the guarded canonizer is the **same function** — and that is exactly what these guards check
behaviourally, since a wiring bug (pruning an entry whose witness is bogus, or failing to emit the seed) would
change the answer and fail the build.

⚠ **Read the second guard for what the pruning actually buys.** On `C₇` at `d ≤ 2` the full table has `399` rows and
the pruned tree keeps `30`; at `d ≤ 3` it is `2800` vs `202`. Both ratios sit just under `|Aut(C₇)| = |D₇| = 14`, and
that is the honest ceiling: pruning by a **fixed** group divides the enumeration by (at most) its order — it does
**not** turn `n^d` into a sum, because per-level growth is unchanged (`30 → 202` is still a factor of `≈ n`). The
`n^d → sum` collapse would need the *stabilizer chain*, which is ⛔ settled-banned (no iso-invariant within-cell
vertex pick). So this is an `|Aut|`-fold cut — large exactly on the symmetric graphs where the deep oracle is
needed, and worth having — not the quasipoly→poly ladder-break the earlier P3c prose projected. -/

def C7 : AdjMatrix 7 := ⟨fun i j => if (i.val + 1) % 7 = j.val ∨ (j.val + 1) % 7 = i.val then 1 else 0⟩

def gTree {m : Nat} (seed : Consume.Supply m) (K d : Nat) (a : AdjMatrix m) : Option (List Nat) :=
  (canonForm? encodeFreeFast
    (guard (forceThenConsume lookaheadKey (TreePrune.treeSupply seed K d))) a).map flatten

/-! **Same answer as the unpruned oracle** — the behavioural witness of `sameOrbits_treeSupply`. -/
#guard gTree (PrunedSupply.prunedSupply 0) 1 1 C4 = gDeep 1 C4

/-! `①c` for the tree-pruned object: it has **no** equivariance proof of its own (it picks orbit
representatives); iso-invariance is inherited through the `SameOrbits` reduction. Measured. -/
#guard gTree (PrunedSupply.prunedSupply 0) 1 1 C4
     = gTree (PrunedSupply.prunedSupply 0) 1 1 (relabelAdj (Equiv.swap 0 1) C4)

/-! **The tree really is pruned** — `|Aut|`-fold, and it still finds the whole group (`14 = |D₇|`). -/
def c7Root : Colouring 7 := (Refine.warmRefineVec C7 (fun _ => 0)).col
def c7Seed : List (Equiv.Perm (Fin 7)) :=
  (Consume.verified (PrunedSupply.prunedSupply 1) C7 c7Root).dedup

#guard c7Seed.length = 14
#guard ((DeepMatch.deepTable C7 c7Root 2).length,
        (TreePrune.prunedEntries c7Seed 1 c7Root 2).length) = (399, 30)
#guard (Consume.verified (TreePrune.treeSupply (PrunedSupply.prunedSupply 1) 1 2) C7 c7Root).dedup.length
     = (Consume.verified (DeepMatch.deepMatchSupply 1) C7 c7Root).dedup.length

/-! ## 14. `F2c` — the second-seed supply breaks the commuting-gauge stall

The consume-side gap C1 (remaining-work §1C): on the twisted triple cover the global mirror `μ³` (per-copy
mirrors composed through the TWISTED matchings) **commutes** with every copy swap, so every single-seed deck
propagation has ≥ 2 viable extensions at the mirror class and stalls; `foldSupply`'s unique-partner lookup is
ambiguous on the merged twisted fibers; the matching supplies are 1-WL-chirality-blind at every pin. This is
exactly the measured `U3 ⊔ T3` end-to-end flag (`PerformanceTest` §10/§11). `deck2Supply` enumerates the
stalled state's OWN ambiguity set (unassigned × viable) as second seeds — the added constraint forces which
commuting extension completes, and the mirror composites (`μ³`-type and swap∘mirror-type) verify. Witness:
`t3` = the one-pair-twisted triple cover alone (n = 15; `ut`'s T block). **Do not delete** — the non-vacuity
witness for `deck2Supply` and the C1 regression gate. (The end-to-end record on `t3`/`ut` is measured in
`PerformanceTest` §11 — ~20 s per descent, off the build path.) -/

def t3 : AdjMatrix 15 := ⟨fun i j => if vfoldT true i.val j.val then 1 else 0⟩
def t3Root : Refine.ColData 15 := Refine.warmRefineVec t3 (fun _ => 0)

#guard (branches t3Root.col).map Fin.val = [4, 9, 14]

/-! **The involution and single-seed structural supplies are DEAD** — the commuting mirror survives both. -/
#guard (narrow (consume (Fold.foldSupplyFast)) t3 t3Root.col).length = 3
#guard (narrow (consume (Deck.deckSupply)) t3 t3Root.col).length = 3

/-! **The second-seed supply FIRES**: the ambiguity set completes to the mirror composites, and the pendant
cell collapses to ONE branch. -/
#guard (Consume.verified (Deck2.deck2Supply) t3 t3Root.col).length = 171
#guard (narrow (consume (Deck2.deck2Supply)) t3 t3Root.col).length = 1

/-! ## 15. `C3a` — the KERNEL supply wiring gate (the Fano multipede; full set = `PerformanceTest` §14)

`mp7`: 7 foot-pair segments, checks = the Fano lines (girth 6 ⟹ no chaining), gauge = the [7,3,4]
simplex code (min weight 4 ⟹ no identity-default) — the C3 witness on which fold/deck/deck2 and a
manual deck3 are ALL measured dead (`PerformanceTest` §13). `Kernel.kernelSupply` recovers the system
structurally and solves it: rails = the 7 foot pairs, basis = 3 weight-4 words, the all-or-nothing
gate passes, and the root gadget cell narrows 28 → 7 (the WHOLE gauge — the standing 7 = the Z₇
translations, the C3b follow-on: **base-graph recovery + lift**, `PerformanceTest` §15 and
remaining-work §1C C3 ii-c; ⛔ *not* deck-mod-K, which §15 measured dead). These two guards gate the
extraction + elimination + emission + gate wiring end-to-end (~15 s); the narrow/pinned-node/
harmlessness measurements live in `PerformanceTest` §14 (~40 s). **Do not delete** — the non-vacuity
witness for the kernel supply. -/

def mpOnLine (i j : Nat) : Bool := j == i || j == (i+1) % 7 || j == (i+3) % 7
def mpInS (i s j : Nat) : Bool :=
  let a := i; let b := (i+1) % 7; let c := (i+3) % 7
  if s == 1 then j == a || j == b
  else if s == 2 then j == a || j == c
  else if s == 3 then j == b || j == c
  else false
def mpFG (f g : Nat) : Bool :=
  let j := f / 2; let bb := f % 2
  let i := (g - 14) / 4; let s := (g - 14) % 4
  mpOnLine i j && (bb == (if mpInS i s j then 1 else 0))
def mp7 : AdjMatrix 42 := ⟨fun i j =>
  if (if i.val < 14 && 14 ≤ j.val && j.val < 42 then mpFG i.val j.val
      else if j.val < 14 && 14 ≤ i.val && i.val < 42 then mpFG j.val i.val
      else false) then 1 else 0⟩
def mp7Root : Refine.ColData 42 := Refine.warmRefineVec mp7 (fun _ => 0)

#guard (Kernel.kernelGens mp7 mp7Root.col).length = 3
#guard (Kernel.kernelGens t3 t3Root.col).length = 0

/-! ## §17 — `orbKeyG` IS EXECUTABLE, and its guard is NON-VACUOUSLY open (2026-07-27)

The poly-guarded force key shipped `noncomputable`, guarded by a `Classical.dec` placeholder, so **no
`#guard` could exist for it** and every firing measurement lived in Python probes. `DeepenGuard` §5 now
decides `CertPath` by the orbit BFS (`Consume.decidableWordReach`), so the key evaluates and the
behaviour is gated here.

**⚠ Why `certPathCost > 0` is the discriminator, not `CertPath = true`.** By AKRV's rigid collapse
(scoping doc §8.4) a guard can hold with **zero levels to certify** — if one individualization already
discretizes, `chooseIdK` returns `none` immediately and the guard is *vacuously* open. Measured on
`G8`: **4 of its 8 branches are vacuous (cost 0) and 4 are substantive (cost 135168)**. A guard witness
that does not also pin a non-zero `certPathCost` proves nothing, which is the `mp7`-fires-totally lesson
in its cost form. Every OPEN guard below is pinned substantive.

Also recorded: **`deck2Supply` is not a superset of `deckSupply` for this guard** — `C5` certifies under
`deckSupply` at every branch and fails under `deck2Supply` at branch 0. That is the direct argument for
the *union* of the equivariant supplies (scoping doc §7.3 item 4), and it is measured, not assumed. -/

/-! Guard OPEN and SUBSTANTIVE on every branch of `C5` under `deckSupply` (5 branches, cost 13125
each, so ≥ 1 level genuinely certified). -/
#guard (Descend.branches (Refine.warmRefineVec C5 (fun _ => 0)).col).all (fun v =>
  decide (Deepen.CertPath (Deck.deckSupply (n := 5)) C5 5
      (Deepen.step C5 (Refine.warmRefineVec C5 (fun _ => 0)).col v))
  && (0 < Deepen.certPathCost (Deck.deckSupply (n := 5)) C5 5
      (Deepen.step C5 (Refine.warmRefineVec C5 (fun _ => 0)).col v)))

/-! The key therefore FIRES there — a non-empty read, not the `[]` deferral. -/
#guard (Force.keyV (Deepen.orbKeyG (Deck.deckSupply (n := 5))) C5
  (Refine.warmRefineVec C5 (fun _ => 0)).col 0).length = 30

/-! `G8` — a PARTIALLY-firing witness (the recorded equivariance-falsifier shape). Guard open on all
8 branches, but substantive on exactly 4: the vacuity trap above, in the record. -/
#guard ((Descend.branches (Refine.warmRefineVec G8 (fun _ => 0)).col).filter (fun v =>
  0 < Deepen.certPathCost (Deck.deckSupply (n := 8)) G8 8
      (Deepen.step G8 (Refine.warmRefineVec G8 (fun _ => 0)).col v))).length = 4

/-! Guard SHUT on `t3` under `deckSupply` — a real deferral (the key returns `[]`, force does not
act, `①` is untouched). The firing loss `CertPath S ⟹ TinhoferPath`, never the converse, is observable. -/
#guard (Descend.branches t3Root.col).all (fun v =>
  !decide (Deepen.CertPath (Deck.deckSupply (n := 15)) t3 15 (Deepen.step t3 t3Root.col v)))

/-! `deck2Supply` ⊅ `deckSupply` at this guard — the measured case for taking the UNION. -/
#guard !decide (Deepen.CertPath (Deck2.deck2Supply (n := 5)) C5 5
  (Deepen.step C5 (Refine.warmRefineVec C5 (fun _ => 0)).col 0))

/-! ## §17a — the UNION guard is STRICTLY stronger than any member (2026-07-27)

`DeepenGuard` §8 proves the union is never *worse* (`certPath_append_left/right`). These guards measure
that it is strictly **better**, which no theorem states — and the mechanism is worth naming:

> `CertPath` is a **conjunction over the levels of one greedy path**, and different supplies certify
> different levels. So the union can certify a path that **no single member certifies** — the gain is
> emergent, not a maximum over the members.

`t3` is the witness: **all four equivariant supplies are SHUT on every branch** (`foldSupplyFast`,
`deckSupply`, `deck2Supply`, `matchSupply`), and `guardSupply` is **OPEN on every branch**. That is a
firing gain from 0/3 to 3/3 on a witness where every individual supply fails, and it is the whole
justification for §8.

⚠ **The cost is real and now visible**, which is what the billed `certPathCost` (`DeepenGuard` §5a) was
for: on `t3` the union bills `1385216550` against `deckSupply`'s `6176250` — a ~224× multiple, since
the union's `supplyCost` is the **sum** of its members'. Firing bought at an honest price, not a hidden
one. (~13 s of the suite's runtime; in line with the existing kernel guards.) -/

/-! **★ The union-guard measurements live in `PerformanceTest` §18, not here.** Evaluating
`Deepen.guardSupply`'s guard costs ~49 s even at `n = 5` and ~95 s on `t3`, against a suite whose
contract is that it stays fast (the kernel guards, the most expensive thing here, are ~15 s). §18 gates
the stronger claim anyway — that on `t3` **every** member is shut while the union is open — which is
the evidence that §8 buys anything and which `certPath_append_*` cannot supply (monotonicity is not
strictness). The `deck2`-shut half of the comparison is already pinned just above, at no extra cost. -/

/-! ## §18 — the COMPOSED record key strictly out-narrows `holKeyFast` (2026-07-28)

`RecordKey.pairKey` is only worth putting in the record object if the tiebreak actually fires
somewhere the holonomy key does not. `RecordKey.keepMin_pairKey_subset` proves the product never
*widens* the narrowing; nothing proves it ever *shrinks* it, so — exactly as with the union guard —
that half is a measurement.

**`G8` is the witness, and it is decisive:** the root branch cell has 8 members, `holKeyFast` keeps
**all 8** (its holonomy signature is constant there), and `recordKey` keeps **2**. So the composed key
resolves a cell the record's current key leaves completely untouched. Consistent with G8's recorded
orbit structure on that cell (`{4, 2, 2}` — `DeepenSupply`'s falsifier note): an equivariant key
cannot cut inside an orbit, and 2 is an orbit.

⚠ Read the negative results too, since they bound the claim: on `t3` (3 branches) and `wcyc9`
(3 branches) the product keeps everything the holonomy key does — correctly, because those cells are
single orbits and `Force.forceBy_no_narrowing_on_orbit` *forbids* an equivariant key from firing
there. The gain is on mixed cells, which is where it was designed to be.

(~5 s. Cheap because `n = 8`; the `guardSupply` evaluations that made §17a expensive are at `n = 15`.) -/

def g8Root : Refine.ColData 8 := Refine.warmRefineVec G8 (fun _ => 0)

#guard ((Descend.branches g8Root.col).length,
        (Force.keepMin (Hol.holKeyFast (n := 8)) G8 g8Root.col
          (Descend.branches g8Root.col)).length,
        (Force.keepMin (RecordKey.recordKey (n := 8)) G8 g8Root.col
          (Descend.branches g8Root.col)).length) = (8, 8, 2)

/-! The two single-orbit controls, pinned so a future change that "improves" them is caught as the
soundness regression it would be (an equivariant key firing inside an orbit contradicts
`forceBy_no_narrowing_on_orbit`). -/

#guard ((Force.keepMin (Hol.holKeyFast (n := 9)) wcyc9 wcyc9Root.col
          (Descend.branches wcyc9Root.col)).length,
        (Force.keepMin (RecordKey.recordKey (n := 9)) wcyc9 wcyc9Root.col
          (Descend.branches wcyc9Root.col)).length) = (3, 3)

end ChainDescent.Regression
