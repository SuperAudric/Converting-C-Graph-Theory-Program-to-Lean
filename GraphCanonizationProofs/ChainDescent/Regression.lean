import ChainDescent.Residue
import ChainDescent.MatchSupply
import ChainDescent.DeepMatchSupply
import ChainDescent.PrunedSupply

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

end ChainDescent.Regression
