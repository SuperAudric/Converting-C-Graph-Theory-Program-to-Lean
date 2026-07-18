import ChainDescent.Residue
import ChainDescent.MatchSupply
import ChainDescent.DeepMatchSupply
import ChainDescent.PrunedSupply
import ChainDescent.PartialMatch
import ChainDescent.SelectNode
import ChainDescent.FoldSupply
import ChainDescent.DeckSupply
import ChainDescent.HolKey

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

end ChainDescent.Regression
