/-
# Publication.lean — the endgame SHOWCASE skeleton (WIP; NOT in build.sh / defaultTargets)

**What this file is.** The compile-target for the project's final deliverable: a single file whose
`#print axioms` on a handful of headline theorems shows *exactly* the project's trusted base — the Lean
kernel primitives `[propext, Classical.choice, Quot.sound]` plus a short, inspectable list of **named
classical citations** (each a theorem *proved outside the project*). A Lean-literate reviewer audits the
citation list and trusts the machine for everything else.

**★★★ THE FLIP HAPPENED (2026-08-08).** This file compiles with **zero `sorry` and zero custom
axioms**: every theorem below prints exactly `[propext, Classical.choice, Quot.sound]`. The design
note used to say *"when each `sorry` is replaced by a term that plugs into the completed project
theorems, `#print axioms` flips from `[sorryAx, …]` — that flip is done"*. It is done, and **no
citation was consumed to do it** — the eight in §2 stay commented out.
--Much of the comments will need to be cleaned up before publishing, i.e. a reviewer doesn't need to be told how to read

**Why the shape (see the design write-up).** Correctness is **unconditional** (the algorithm is never
wrong — it returns a complete iso-invariant *or an honest flag*), cost is **conditional** (poly-time *or*
it flagged), and the residue predicate appears **only** in a characterization (a flag ⟺ a genuine
obstruction). This is strictly stronger than "canonizes residuals + poly time" and cleanly separates the
three concerns.

**THE FIREWALL (the one rule that keeps this honest).** An `axiom` here may *only* be a genuine classical
theorem a reviewer accepts as known (G3/CFSG, Skresanov, Liebeck, Ponomarenko, FTPG, …). The project's own
**open frontier** must NEVER become an axiom — it silently downgrades "conditional on known results" to
"conditional on our conjecture", and `#print axioms` cannot tell them apart. The release valve is
`UnhandledResidue`: it is *defined to absorb exactly the open cases*, so everything on the handled side
needs only real citations. If a family's poly-ness is still only a *meta* argument (as Route C's is today),
it either becomes a real `cost ≤ poly` proof or it goes inside `UnhandledResidue`. It cannot become an axiom.

Compile standalone (NOT via `lake build`; this file carries `axiom` and temporarily contains `sorry` by design):
  cd GraphCanonizationProofs && lake env lean Publication.lean
Quality note: this is the ONLY file in the project permitted `axiom`. The library stays axiom-clean
`[propext, Classical.choice, Quot.sound]`; the citations are carried there as *hypotheses*, and only HERE
are they instantiated with `axiom` witnesses so `#print axioms` aggregates them into one legible list.

## STATUS (2026-07-17) — the statements here are TARGETS, not finalized design (user steer; blocker-audit item 8).
Finalization is deliberately deferred; read the obligations as the intended shape, not as what the library fills
today.
  · ⚠ END-TARGET RESTATED (2026-07-18, user steer): the goal is a COMPLETE canonizer — `canonForm? ≠ none` on
    every input (③ becomes vacuous, the residue atoms drop). The poly-or-flag + graded-③ shape below is the
    honest INTERMEDIATE each stage publishes through, and the fallback only after recorded route-exhaustion
    (plan: docs/chain-descent-remaining-work.md §0–§2). Nothing below changes until legs close; totality
    tightens the file at the end, not before.
Per-obligation state:
  · ① — ✅ SWAPPED (spike, 2026-07-19; record EXTENDED later the same day with the C3a kernel supply):
    `canonForm?` is the REAL fused record object (holonomy key +
    `foldFast ++ deck ++ deck2 ++ kernel`), and `canon_sound`/`canon_complete`/`flag_iso_invariant` are proven —
    `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no citation axioms (① carries
    nothing, as designed). Zero glue was needed: `Labelled n` ≡ the matrix type, `Iso` ≡ `CanonSpec.GraphIso`,
    `canonFormFastS?_eq` is `rfl`. The record pin is PROVISIONAL (strengthening it = edit `canonForm?` +
    `canonForm?_record`, nothing downstream) — **and that is exactly what happened on 2026-07-28: the force
    key is now `RecordKey.recordKey`** (`holKeyFast` tie-broken by the union-guarded `orbKeyG`), a strict
    strengthening (`keepMin_pairKey_subset`) that cost one `KeyEquivariant` proof and **turns a flag into an
    answer on `Regression.G8`**. ⊘ *"Only ③ + non-vacuity remain `sorry`"* was true when written; both
    are discharged now and the file has **zero** `sorry` — and the object moved again on 2026-08-08,
    to the cell-indexed supply (see the ▶▶ block at the top of §1). The `canonFormFastS?_eq`-is-`rfl`
    remark describes that earlier object; the current one bridges by
    `Select.canonFormLazyHSC?_eq` (`W-j`) then `Select.canonFormS?_selNodeLazyC_eq` (`W-e`), both
    **proved** equations rather than `rfl`.
  · ② — ✅ **SWAPPED AND DISCHARGED 2026-07-28, in one pass with the key swap above.** `canon_poly_or_flag`
    is proved, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** — and on the
    LEFT disjunct, so the cost claim needs no flag escape. `cost` and `costConst`/`costDeg` are no longer
    `opaque`: `cost` is the `CostM` cost projection of the very definition `canonForm?` is the value
    projection of, and the numerals are **`RecordDeepenCell.costConst = 69` /
    `RecordDeepenCell.costDeg = 13`** (they were `RecordKey`'s 57 / 13 until the cell-indexed swap on
    2026-08-08 — the degree did not move; the constant absorbed per-cell supply billing and the
    newly-billed deepen guard), both *computed* (a `ring`-checked expansion,
    `RecordDeepenCell.recordDeepenBound_expand`) rather than guessed.
    Provenance of why this took three shapes to get right: `SupplyCost`'s end-to-end theorems are at
    `lookaheadKey`+`prunedSupply`, which is NOT this file's object (closed by `RecordCost.lean`); and the
    pinned monomial itself was **`n ^ costDeg`, which is false at `n = 0` for the real object at any
    numerals** — see the `costConst`/`costDeg` block below for the measurements. It is now
    `costConst * (n + 1) ^ costDeg`, the same polynomial class, true on every input.
  · ③ — ✅ **DISCHARGED 2026-08-08 (`W-g`), axiom-clean, at the same object as ① and ②.**
    `canonForm?`/`cost` are now `RecordDeepenCell.canonFormFast`/`costFast` — the fused descent at the
    **cell-indexed** supply `fun c => recordSupplyFast ++ Deepen.deepenCellSupply c` — and
    `residue_if_flag` is `recordDeepenCell_full_fast.2.2`. `costConst`/`costDeg` moved with it:
    **69 / 13** (`RecordDeepenCell.recordDeepenBound_expand`, `ring`-checked; the degree is unchanged
    from the previous object, the constant absorbs per-cell supply billing and the newly-billed
    deepen guard). ⚠ Read the ▶▶ block at the top of §1, not the 2026-08-04 provenance under it.
    The residue was RESHAPED (2026-08-04) to make it
    provable *in principle*: the three `opaque` atoms made both ③ obligations undischargeable, and they are
    replaced by one **definition**, `residueRigidObstruction G := ¬ TwinFamily.TinhoferGraph G` (see the
    `UnhandledResidue` block for why D0/D1 were dropped rather than kept as opaque placeholders).
    `unhandledResidue_nonvacuous` and `residue_if_flag` are **both** proved now, axiom-clean, with no
    citation axiom consumed.
    ⛔⛔ **An earlier draft discharged ③ at `canonFormCover?`, a SECOND object. That was WRONG and is
    REVERTED** (user steer, 2026-08-04): `canonForm?` is meaningful only if ①a+①b+①c+②+③ are properties of
    **the same** object — an exhaustive solver and a random solver each carry half and together prove
    nothing. Any sentence below that still implies a two-object showcase is stale; this one governs.
    ⚠ The residue is an **over-approximation** (a CFI graph is not Tinhofer but its obstruction is linear
    and belongs to the rigid resolver): W2's job is to narrow it, not to enlarge it.
    ⚠ The earlier note that the strong reading "flag ⟹ genuine *hardness*" is unreachable **still stands** —
    what is proved is flag ⟹ a genuine *structural obstruction*, which is not the same as hardness.
  · **The 8 citation axioms in §2 are consumed by NOTHING, and are therefore now COMMENTED OUT**
    (2026-08-04, user steer: *"the axioms should get commented out or moved from the file until use"*).
    Every `#print axioms` below is exactly Lean's three, so declaring them changed nothing except to
    invite a reviewer to read them as this file's trusted base. Each `opaque … : Prop` and its full
    citation doc-comment are RETAINED beside the commented `axiom` line, so restoring one for W2/Route C
    is deleting `-- ⏸ ` from a single line. **The paper must still list them as the intended trusted base
    for the parts of the project that are not in this file.**
  · The §1 "mutual stall" prose IS now the flag semantics of a BUILT object (2026-07-18, sel rewrite landed):
    `Select.selNode` flags exactly when NO non-singleton cell resolves (`Select.selNode_stall_iff`), with
    ①+②+③a in one place at the record supply (`Select.selNode_pruned_record`) and the blind object DOMINATED
    value-exactly (`canonFormS?_selNode_dominates`). The Publication swap to the fused object is still deferred
    with the rest of the wiring; the old guarded-blind object (`Stall.stalled` = "the LEAST cell stalled")
    remains available and is strictly weaker (`Residue.Handled ⟹ Select.HandledS`).
  · Axiom WIRING IS DEFERRED for every entry in §2; per-entry cautions are noted inline (G3 threshold, FTPG's
    corrected predicate, Payne–Thas narrowing).
  · Non-vacuity: the handled half is now fillable in principle (`Residue.handled_emptyAdj` — a trivial witness);
    the load-bearing witnesses (a CFI/forms graph handled AT THE RECORD RESOLVERS; a real unhandled instance at
    the same resolvers) remain the target. The library's `residue_nonvacuous` witness uses `constKey`/`emptySupply`
    and does NOT transfer to the record object.
-/
import ChainDescent.Spine
import ChainDescent.Deck2
import ChainDescent.KernelTransport
import ChainDescent.RecordKey
import ChainDescent.RestrictedTransport
import ChainDescent.RecordDeepenCell

namespace Showcase

open ChainDescent

/-! ## 0. Graph isomorphism (on the project's own `AdjMatrix`) -/

/-- Two graphs on the same vertex set are **isomorphic** when some relabelling of `G` is `H`
(reusing the project's `labelledAdj`). Standard graph iso; an equivalence relation. -/
def Iso {n : ℕ} (G H : AdjMatrix n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), labelledAdj π G = H.adj

/-! ## 1. Runtime-Phase objects (STUBS — `opaque`, to be replaced by the real Lean canonizer)

These are the objects the Runtime Phase must *build*. They are `opaque` (sealed, irreducible) so the
obligations below are genuinely open — NOT vacuously true from a placeholder value. Replacing an `opaque`
with the real Lean definition (the descent model + cost accounting) is exactly the Runtime-Phase work.

  · `canonForm? G` — the canonizer's output on `G`: a canonical adjacency (a relabelling of `G`), or
    `none` = an **honest flag** ("this input hides an obstruction I cannot certify cheaply").
  · `cost G`       — the operation count of the descent on `G` = (# descent nodes) × (per-node oracle work),
    a `ℕ` computed from the actual Lean descent. Granularity to be DECLARED in the paper (operation-count
    proxy; each step separately argued poly-size).
  · `UnhandledResidue G` — the STRUCTURAL obstruction predicate (Cameron / hidden-Johnson in the symmetric
    domain; the unhandled IR residue in the rigid domain). Must be an *independent* geometric predicate,
    NOT "the algorithm flagged" (that makes §3 a tautology). See the firewall + the non-vacuity obligation. -/

/-- **★ THE SWAP (spike, 2026-07-19): `canonForm?` is REAL — the fused canonizer of record** (encode-free
refiner; force = the holonomy key; consume = `foldSupplyFast ++ deckSupply ++ deck2Supply ++ kernelSupply`),
i.e. exactly the object the end-to-end acceptance measurements run (`PerformanceTest` §11/§12/§14).
**Extended 2026-07-19 (C3a tranche 2 complete)** with the F₂ kernel supply: `kernelSupply` is not — and
provably cannot be — `GensEquivariant` (its Gaussian basis is pivot-order dependent), so its ① rides the
`OrbitPrune.SameOrbits` reduction against the equivariant set-level reference. ⚠ The record pin is
PROVISIONAL by design — strengthening the record later is this one definition plus `canonForm?_record`
below; nothing downstream changes shape.

**★★★ THE SUPPLY SWAP (`W-g`, 2026-08-08): the supply is now CELL-INDEXED** —
`fun c => recordSupplyFast ++ Deepen.deepenCellSupply c`, read by **`Select.selNodeLazyHC`** (`W-e`
then `W-j`, the same day — the eager `selNodeFastC` and the un-hoisted `selNodeLazyC` remain in the
library as the reference twins). Same fused
descent, same record key; each cell is judged by the generators of descents anchored *in that cell*,
gated by that cell's own guard. This is what makes `③` provable **at the object `①` and `②` are
about** — see the block below §1 for why the node-global form provably cannot carry `①`. The
definition is `RecordDeepenCell.canonFormFast`; `①`+`②`+`③` are its
`recordDeepenCell_full_fast`.

**★ THE FORCE KEY SWAP (2026-07-28): the key is now `RecordKey.recordKey`** = the lex product
`pairKey holKeyFast (orbKeyG guardSupply)` — the holonomy key, tie-broken by the union-guarded orbit
key. `keepMin_pairKey_subset` proves the tiebreak never *widens* the narrowing, so this is a strict
strengthening of the previous pin, and it is **measured non-vacuous**: on `Regression.G8` (a regular,
non-vertex-transitive cubic graph) the previous pin **flags** and this one **answers** — the root cell
of 8 is left untouched by `holKeyFast` and cut to 2 by the product (`Regression` §18). ⚠ The price is
interpreted wall-clock: `t3` (n = 15) goes 12 s → 412 s, so the `PerformanceTest` acceptance
measurements were taken at the *previous* key and do not describe this object until re-run. -/
def canonForm? (n : ℕ) (G : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  RecordDeepenCell.canonFormFast (n := n) G

/-- The object satisfies the full canonical-form spec — **globally and with no hypothesis**.
`Select.selNodeC_canonizer` asks for `KeyEquivariant` plus the new `Select.CellOrbitTransport`, and
the cell-anchored guard supplies the second with no `SupplyEquivariant`, no equivariant reference
supply and no completeness theorem about deepen; `kernelSupply`'s non-equivariance rides
`OrbitPrune.SameOrbits` as before. -/
theorem canonForm?_record (n : ℕ) : CanonSpec.IsCanonicalFormOpt (canonForm? n) :=
  (RecordDeepenCell.recordDeepenCell_full_fast (n := n)).1

/-- **★ `cost` IS REAL (2026-07-28)** — no longer an `opaque` stub. It is the `cost` projection of the
*same* definition `canonForm?` is the `value` projection of (`descendS` is written in `CostM`), so
there is no bridge and no second object: `②` below is a theorem about the object `①` is about. -/
def cost (n : ℕ) (G : AdjMatrix n) : ℕ :=
  RecordDeepenCell.costFast (n := n) G

/-! ### ▶▶ HOW `③` CLOSED — DONE 2026-08-08. Read this block; the 2026-08-04 one below is PROVENANCE.

**`①a`, `①b`, `①c`, `②` and `③` are now all properties of the same object, and that object is what
`canonForm?` and `cost` are defined as.** The file has zero `sorry`.

`ChainDescent/RecordDeepenCell.lean` builds it:

```
Select.selNodeC encodeFreeFast recordKey (fun c => recordSupplyFast ++ Deepen.deepenCellSupply c)
```

— the same fused descent and the same record key, with the supply **cell-indexed**: each cell is
judged by the generators of descents anchored *in that cell*, gated by that cell's own guard. It
carries **every obligation this file states**, axiom-clean, at that one object:

  · `RecordDeepenCell.recordDeepenCell_canonizer` — **`①a`/`①b`/`①c`, global, no hypothesis.**
  · `RecordDeepenCell.descentCostSC_recordDeepen_monomial` — **`②`**, `cost ≤ 69 * (n+1)^13` on
    **every** input, no flag disjunct. The numerals are `RecordDeepenCell.costConst`/`costDeg`,
    which this file's `costConst`/`costDeg` are now defined as: the **degree is unchanged** at 13 and
    the constant moved 57 → 69, `ring`-checked in `recordDeepenBound_expand`. The `+12` is
    **+8** from billing the supply per cell and **+4** from finally billing the deepen guard
    (`Deepen.goodCellCost_bounds_guard` — it had been charging nothing for the `≤ n` `CertPath`
    walks it runs).
  · `RecordDeepenCell.not_tinhoferGraph_of_flag` — **`③`, for every key**, at the tight residue
    `¬ TinhoferGraph` = this file's `UnhandledResidue`.
  · all three together as **`RecordDeepenCell.recordDeepenCell_full`**.

**Why the supply had to become cell-indexed.** `SelectNode.cellNarrow` reads one **node-global**
verified list and probes every cell against it. That is right for `foldSupply`/`deckSupply`/
`deck2Supply`/`kernelSupply`, which harvest from the whole graph. `deepenSupply` is the project's
only **pair-anchored** supply — its generators come from deepening pairs of the *branch* cell — and
each emitted twist is a full automorphism, so it moves vertices in cells no descent visited. The
resulting off-branch verdict is **measured not relabelling-invariant** (`scratchpad/probe_offbranch2/
3.py`: CFI cubic m = 8 and 10, depth 1, an off-branch cell of size 2 counting `(1,1)` under one
labelling and `(2,)` under its own transport, *with the guard open on both sides*). So the
node-global append `recordSupplyFast ++ deepenSupplyCert` — which does carry `③`
(`RecordDeepen.not_tinhoferGraph_of_flag_recordDeepen`) — provably cannot carry `①`, and is not a
candidate. `Select.CellOrbitTransport` replaces `SupplyEquivariant` and the defect goes away.

**And it RUNS.** `canonFormFast`/`costFast` go through **`Select.selNodeLazyHC`**, which walks the
non-singleton cells in increasing colour order, evaluates and bills each on demand, and stops at the
first that narrows to `≤ 1` — building children through `Refine.ColData`, so `canonForm?` is
`#eval`-able, not merely definable. Measured: answers on `K₂`, `C₅`, `K₁,₂,₃` and `K₃ ⊔ C₄`; `C₅`
costs 5 212 728 and `K₁,₂,₃` 20 321 716, against a budget of `69·6^13` and `69·7^13 ≈ 6.7 × 10¹²`.

★★ **`W-j` (2026-08-08) removed the two recomputations that survived inside each probed cell**: the
key had been evaluated three times per vertex (once for the bill via `keyCost`, twice inside
`Force.keepMin` — `keyCost` and `keyV` are `.2` and `.1` of the *same* strict pair), and the
*cell-independent* left factor `recordSupplyFast` was re-harvested, and re-verified, once per probed
cell. `Select.probeWalkH`/`selNodeLazyHC` share the key through a table and hoist the left factor to
once per node. The **bill is unchanged** — `Select.probeWalkH_eq` is an equation — so `②`'s numerals
did not move. Measured: `C₅` 27.6 s → **20.8 s**, `K₁,₂,₃` 74.4 s → **50.4 s**, both at identical
billed costs (5 212 728 / 20 321 716).

⚠ **The residue is unchanged and is still an OVER-approximation** — a CFI graph is not Tinhofer, yet
its obstruction is linear and belongs to the rigid resolver. Narrowing it is W2, not this. **This is
the one thing left to say honestly about `③`:** it is *"a flag means a real structural obstruction"*,
not *"a flag means hardness"*, and the residue is currently wider than the architecture's true gap.

---

⊘ **PROVENANCE — the 2026-08-04 framing, superseded above.** Retained because it records two shapes
that were *not* the answer (the options (iv)/(v) either/or, and the two-object split), and one claim
that is now **REFUTED**: the block below argues at length that a computable guard is CIRCULAR. It is
not. `Deepen.tinhofer_iff_certifiedG` (`DeepenGuardComplete` §5, 2026-08-05) proves the guard
**complete** — `Tinhofer ↔ CertifiedG deepenSupply` — which is precisely the converse the block calls
impossible, and it is what `RecordDeepen` and `RecordDeepenCell` are built on. Read the block for the
history, not for the mathematics.

### ⊘ THE OPEN STEP — why `③` was not yet discharged at THIS object (2026-08-04)

**`canonForm?` must remain ONE object carrying `①a`/`①b`/`①c` + `②` + `③` together.** A canonizer that is
correct-but-covers-nothing, paired with a second one that covers-but-is-not-correct, proves nothing —
the exhaustive solver and a random solver each have one half too. (An earlier draft of this file split
`③` onto a second object; that was wrong and has been reverted.)

**What blocks `③` here.** `③` needs *Tinhofer ⟹ this object answers*, i.e. the consume resolver must fire
at every reached node of a Tinhofer graph. The record supply (`foldFast ++ deck ++ deck2 ++ kernel`) is
not proved to certify a Tinhofer cell. The supply that **is** proved to is `Deepen.deepenSupply`
(`Deepen.deepen_branch_orbit_iff_aut`: at a Tinhofer node its verified generators realise *exactly* the
`IsColAut`-orbit relation), but its firing pattern is index-dependent, so an object using it raw has no
iso-invariant flag.

**⚠ The gap is NOT `R1`, and it is already named.** `Deepen.deepenSupplyGuarded` — deepen's generators
where `Tinhofer` holds, deferring elsewhere — has **`①` with no hypothesis at all**
(`Deepen.deepenSupplyGuarded_canonizer`, via the unconditional
`Deepen.deepen_branchOrbit_transport_guarded`), fires exactly on Tinhofer nodes, and bills a flat `n⁶`
either way. So a single object with `①` + `②` + `③` and Tinhofer coverage **already exists** — it is only
`noncomputable`, because its guard is the `Tinhofer` predicate itself.

**⛔ REFUTED 2026-08-05 — `Deepen.tinhofer_iff_certifiedG` proves exactly the converse this paragraph
calls impossible. Do not act on it; see the 2026-08-08 block above.** ⊘ A COMPUTABLE GUARD IS NOT THE
ANSWER — that route is CIRCULAR (corrected 2026-08-04).** An earlier
draft of this block proposed guarding on `Deepen.CertifiedG Deepen.deepenSupply` (an orbit BFS over
deepen's own verified generators, hence computable). One direction is free and unconditional —
`Deepen.tinhofer_of_certifiedG : CertifiedG S adj χ → Tinhofer adj χ` — but the converse fails on a
quantifier: each level of `CertPath` demands `CellIsOrbit deepenSupply adj ψ` (deepen connecting *every
pair* of ψ's cell), which needs **every anchor of ψ to be good**, i.e. `Tinhofer adj ψ`; path-local
`Tinhofer adj χ` says nothing about a deeper ψ's other anchors. So *"the cell is a single orbit"*
transports while *"deepen certifies it"* does not — and the missing piece is exactly
`Deepen.OrbitComplete`, which **already yields `①c` with no guard at all**
(`Deepen.deepenSupply_canonizer_of_orbitComplete`). The guard needs the very predicate it was meant to
avoid, and is provably invariant only on `TinhoferGraph`, which is where `①` is already proved. (Note
`Deepen.certPath_transport`'s own hypothesis is `SupplyEquivariant`, which `deepenSupply` provably lacks.)

**⊘ ⟹ THE REAL CHOICE — SUPERSEDED 2026-08-08 (neither option was taken; the supply became
cell-indexed instead, giving global `①` *and* the tight residue together).** Both options are costed
in `docs/chain-descent-wind-down.md` §2 W1:
  · **(iv)** append `twinSupply` to the record supply — `①`/`②` stay **unconditional** and this file
    closes to zero `sorry`; the residue weakens from `¬Tinhofer` to `¬(Simple ∧ RootTwins)`. **Not built**;
    every ingredient exists (`KernelRef.sameOrbits_appendSupply` with `twinSupply` in the shared prefix,
    `cellIsOrbit_append_*`, `SelectNode.handledS_of_handled` + `answersS_of_handledS`), and the real cost
    is recomputing `costConst`/`costDeg`.
  · **(v)** point `canonForm?` at `Stall.guard (Composite.forceThenConsume Hol.holKeyFast
    Deepen.deepenSupply)` — the tight residue `¬TinhoferGraph`, `②` unconditional, `①a` unconditional, but
    `①b`/`①c` **proved on the Tinhofer class rather than globally**. ✅ **ALREADY BUILT**:
    `ChainDescent.DeepenTransportOn.deepen_object_package`.
⚠ The trade is *not* "invariant vs non-invariant flag" — (v) **proves** flag-invariance on the class and
claims nothing off it. It is *global `①` with a weak residue* against *class `①` with a tight residue*. -/

/-! ### `UnhandledResidue` — RESHAPED 2026-08-04: a DEFINITION, from what is proved

**Why it had to be reshaped.** The three atoms below were `opaque … : Prop` — sealed, with no definition.
That made **both** ③ obligations unprovable *in principle*, not merely unproved: an opaque `Prop` can be
neither inhabited nor refuted, so `residue_if_flag` had nothing to land in and
`unhandledResidue_nonvacuous` could not produce either witness. The shape was **aspirational** — it
described the residue the *research* was aiming at rather than the one the artifact can exhibit.

**The rule now applied (user steer, 2026-08-04): shape the residue off the examples and showcases that
exist, not off research targets.** So:

  · (D0) `residueNonSchurian`   — **REMOVED.** The file's own note already called it a modelling gap
        rather than a genuine unhandled residue, with the intended end shape dropping it.
  · (D1) `residueHiddenJohnson` — **REMOVED.** Route C / Cameron territory, suspended (wind-down §3).
        Re-adding it as an opaque atom would re-break the handled half of non-vacuity for nothing.
  · (D2) `residueRigidObstruction` — **KEPT, and given a real definition**: the graph is **not
        Tinhofer**. Via `TwinFamily.schurianAt_iff_no_rigidObstruction` this unfolds to *"some
        individualization-reachable colouring carries a rigid obstruction"* — a property of `G` alone,
        iso-invariant, algorithm-independent. **Firewall-clean**: it is not "the algorithm flagged".

**⚠ It is an OVER-APPROXIMATION, and that is the honest direction.** A CFI graph is not Tinhofer, yet its
obstruction is *linear* and belongs to the rigid resolver's domain — so `¬ Tinhofer` currently counts as
residual something the architecture is meant to handle. `residue_if_flag` is still true (a superset on the
right of an implication only makes it easier); what W2 buys is the *narrowing*, at which point the
intended shape is `¬ Tinhofer ∧ ¬ (linear/CFI obstruction)`, or equivalently a second disjunct
`NonLinearRigidObstruction`. **Do not add that disjunct until it has content** — an opaque one would
immediately re-break `unhandledResidue_nonvacuous`'s handled half, which is exactly the trap this reshape
is undoing.

**The flag semantics this rests on** (unchanged): the descent flags exactly at a **mutual stall** — no
resolver fires anywhere. So the bridge to prove is *Tinhofer ⟹ the consume resolver fires*
(`TwinFamily.cellIsOrbit_deepenSupply_of_schurianAt`: at a Tinhofer node the deepening supply certifies
the branch cell, so consume narrows it to one), and `residue_if_flag` is its **contrapositive**. Note this
is a claim about **progress**, not about canonizing to the end — the same shape W2 will have for CFI
(*"does not stall on a CFI residue"*). Canonization to the end is a separate, second object; see
`RestrictedTransport.canonizes_on_tinhofer`. -/

/-- **(D2) The rigid/symmetry obstruction, defined.** `G` carries a rigid obstruction somewhere in its
individualization tree — equivalently, `G` is not a Tinhofer graph. -/
def residueRigidObstruction (n : ℕ) (G : AdjMatrix n) : Prop :=
  ¬ ChainDescent.TwinFamily.TinhoferGraph G

/-- **THE RESIDUE.** One disjunct today, by design (see above). -/
def UnhandledResidue (n : ℕ) (G : AdjMatrix n) : Prop :=
  residueRigidObstruction n G

/-! ### The explicit polynomial — numerals, not an `∃ p : Polynomial …`

Explicit ≫ existential: more honest, avoids formalizing the class P, and the reviewer reads the degree
off the statement. **★ PINNED 2026-07-28** at the object above, from `RecordKey`'s §5 — and neither
numeral is asserted: `RecordKey.recordKeyBound_expand` has `ring` check that the `②` bound polynomial
has degree **13** and coefficients summing to **57** (was 53 until `Deepen.stepCost` was
billed, 2026-08-06 — see `RecordKey.costConst`).

⚠⚠ **THE BOUND IS `costConst * (n + 1) ^ costDeg`, NOT `costConst * n ^ costDeg`** — the `n`-form (as
this file pinned it until 2026-07-28) is **not provable for this object at any numerals**, and the flag
disjunct does not rescue it:

* `Select.descendS` bills **1** for a leaf node, and at `n = 0` every colouring is vacuously
  `Discrete`, so the canonizer costs **1** and *answers* (`canonForm? 0 G ≠ none`, measured) — while
  `costConst * 0 ^ costDeg = 0` for every `costDeg ≥ 1`.
* `costDeg = 0` degenerates the claim to a constant bound, false at `n = 2` (cost `1166` on `K₂`,
  measured 2026-08-06 at the billed key; `1162` before `stepCost` was billed).

Nothing about the guarantee weakens: `(n + 1) ^ 13 ≤ 2 ^ 13 · n ^ 13` for `n ≥ 1`, so this is the same
polynomial class, stated so that it is also true on the degenerate input.

### ⚠⚠ WHAT THE DEGREE DOES AND DOES NOT CERTIFY — read before quoting `costDeg` (2026-08-08)

The bound is a real, unconditional theorem about the object's `CostM` accounting. It is **not** a tight
measurement of the algorithm's asymptotic cost, because several components bill **declared flat**
charges that are deliberate over-estimates rather than derived ones:

  · the deepening harvest bills a flat `n⁶` per cell regardless of that cell's size, where the real
    work is `≈ m² n⁴` and `Σ_c m_c² ≤ n²` — so the family together really costs `n⁶`, not `n⁷`;
  · `Hol.holKeyFast` bills a flat `n⁵`;
  · `Select.selProbeBoundC` charges **every** cell the *maximum* per-cell supply bound `sB` and
    candidate count `gB`, then multiplies by `n`, where the true total is a sum of much smaller terms;
  · `Deepen.goodCellCost` is `n ×` `certPathCost`'s bound, which itself carries the flat `n⁶` inside.

**The consequence, stated plainly: `costDeg` staying at 13 across the 57 → 69 change does NOT show
that the algorithm's true cost polynomial has the same degree it had before.** Both numbers are upper
bounds produced by the same loose accounting, and they can be loose by different amounts. What is
established is exactly two things, and they are what the paper may claim:

  1. an **unconditional polynomial ceiling with explicit numerals**, on every input, answer or flag
     alike — no exponential blow-up is possible; and
  2. that the per-cell supply change did not push *that ceiling* up a degree.

### ⛔⛔ AND WHERE TIGHTENING WOULD HAVE TO HAPPEN — FOUR OF THE FIVE OBVIOUS LEVERS DO NOTHING

⛔ An earlier version of this block advised *"tightening starts with billing the harvest as
`|cell|² · n⁴` and proving `Σ_c |cellList χ c|² ≤ n²`."* **That is the wrong lever — computed
2026-08-08 against `recordDeepenBound_expand`'s own polynomial, it changes neither numeral.**

Two structural facts explain it, and they are worth stating because they prune the search:

  · **`costConst` is the bound polynomial evaluated at `n = 1`** (it is the coefficient sum). So any
    change that merely moves a factor of `n` in or out — e.g. billing a node-level supply once per
    node instead of once per cell — **cannot** change it, however much it improves the polynomial
    for `n ≥ 2`.
  · **`costDeg` is set by a single term**, `(n + 1) · n · (n · kc)` where `kc = RecordKey.recordKeyBound`.
    Setting `kc := 0` drops the whole bound to degree **11**, so *no* consume-side or guard-side
    charge can move the degree.

Measured effect on `(costDeg, costConst)` of each candidate:

| change | result |
|---|---|
| harvest billed `|cell|² · n⁴` instead of flat `n⁶` | **13 / 69 — no change** |
| `goodCellCost`'s nested flat `n⁶` → `n⁴` | **13 / 69 — no change** |
| `Hol.holKeyFast` flat `n⁵` → `n⁴` | **13 / 69 — no change** |
| billing the record supply once per node (`W-j`'s honest-billing variant) | **13 / 69 — no change** |
| **`Deck2.deck2Supply`'s declared charge `n²(1+n²)·n⁵` → `n⁷`** | ★ **11 / 65** |

⟹ **the single lever is `Deck2.deck2Supply`'s declared per-node charge**, and it reaches the degree
through one chain: `deck2` `n⁹` → `RecordKey.guardSupplyBound` `n⁹` → `recordKeyBound = … + n ·
guardSupplyBound` `n¹⁰` → `Select.selProbeBoundC`'s `n · (n · kc)` `n¹²` → `(n+1) ·` → **`n¹³`**.
The charge is `|branches|² · (1 + n²) · n⁵` bounded at `|branches| ≤ n`; tightening it means carrying
the branch-cell size `m` instead of `n`, which is a real derivation, not a re-bracketing.

None of this is required for the two claims above; it is required before anyone reads `13` as the
algorithm's degree. -/

/-- `RecordDeepenCell.costConst = 69` — the coefficient sum of the `②` bound polynomial. -/
def costConst : ℕ := RecordDeepenCell.costConst

/-- `RecordDeepenCell.costDeg = 13` — the degree of the `②` bound polynomial. -/
def costDeg : ℕ := RecordDeepenCell.costDeg

/-! ## 2. The trusted base — CITATIONS ONLY (placeholders; the ONLY custom axioms)

In the real file each of these is the *actual* project predicate (e.g. `ChainDescent.PrimitiveCCClassification`
from `Cascade`, `AffineSchemeTwoClosed` from `RouteCSeam`, `Theorem41Statement` from `CoherentConfig`,
`ConePreservingCollineationIsSemiSimilitude` from `RouteCFormAdapters`, the Ponomarenko cyclotomic 2-sep,
the Liebeck affine-rank-3 classification), carried as a *hypothesis* by the library capstones and discharged
here by the `axiom` witness. The placeholders below document the intended trusted base; wiring them to the
real predicates is a mechanical Publication-Phase step.
If any of them get discharged, they can be removed from this list.

FIREWALL CHECK for this list: every entry is a theorem *proved outside the project* (CFSG / finite-geometry
/ classical-group development). Nothing here is a project conjecture. -/

/-- G3 — the primitive-coherent-configuration / Cameron classification (CFSG-based). The one citation
policy allows to stay cited permanently. Source: Babai ITCS'14 / J.Algebra'15; Kivva JCTB'24; Sun–Wilmes.
⚠ WIRING CAUTION (2026-07-16 audit): the citable threshold is Sun–Wilmes `exp(Õ(n^{1/3}))` (all ranks; rank 3/4
at quasipoly via Babai/Kivva). NEVER instantiate `hClassify` at the `confinementLargeScheme` quasi-poly threshold
`n^{log₂ n}` — at that threshold the statement is Babai's OPEN conjecture, not a citation. -/
opaque PrimitiveCCClassification : Prop
-- ⏸ axiom cameron_classification : PrimitiveCCClassification

/-- Skresanov rank-3 affine 2-closure: the affine scheme of a classical `G₀` has no unexpected
automorphisms (coarse-Aut pinning; underpins all four Route-C families' `|Aut|` side). Source: Skresanov
arXiv:2007.14696 / 2202.03746. -/
opaque AffineSchemeTwoClosed : Prop
-- ⏸ axiom skresanov_two_closure : AffineSchemeTwoClosed

/-- Liebeck affine-rank-3 classification (places the classical instances in the node-4 residue). -/
opaque LiebeckAffineRank3 : Prop
-- ⏸ axiom liebeck_rank3 : LiebeckAffineRank3

/-- Ponomarenko cyclotomic 2-separability (the 1-dim cyclotomic slice). Source: arXiv:2006.13592 Thm 1.1. -/
opaque PonomarenkoCyclotomic2Sep : Prop
-- ⏸ axiom ponomarenko_2sep : PonomarenkoCyclotomic2Sep

/-- Fundamental theorem of projective geometry (cone-preserving collineations are semilinear); needed only
for the `q = pᵉ`, `e > 1` field twist. Source: Artin, *Geometric Algebra*.
⚠ WIRING TARGET = the CORRECTED difference-cone predicate (2026-07-16 fix): the original
`ConePreservingCollineationIsSemiSimilitude` (bare cone-preserving bijection antecedent) was false-as-formalized;
wire only the difference-cone form. (`JointVarietyDeterminesFamily` is PROVED outright — no axiom needed; it is
deliberately absent from this list.) -/
opaque FundamentalThmProjGeom : Prop
-- ⏸ axiom ftpg : FundamentalThmProjGeom

/-- Buekenhout–Shult / Veldkamp–Tits: an abstract polar space of rank ≥ 3 is CLASSICAL (embeds in `PG(d,q)`
with its form). **CORRECTNESS/classicality only — NOT a complexity bound** (R1's poly-time is an in-project
effective-construction obligation, route-c-plan §7a). Used only for `d ≥ 6`. Source: Buekenhout–Shult,
Geom. Dedicata 1974; Tits, *Buildings of Spherical Type*. -/
opaque PolarSpaceRankGe3Classical : Prop
-- ⏸ axiom buekenhout_shult : PolarSpaceRankGe3Classical

/-- Payne–Thas: recognition/coordinatization of a CLASSICAL generalized quadrangle (the `d = 4`, rank-2 case,
outside Buekenhout–Shult). **Correctness only.** The genuine soft spot (non-classical GQs exist), route-c-plan
§7a (e). Source: Payne–Thas, *Finite Generalized Quadrangles*.
⚠ MUST BE NARROWED to a specific characterization theorem before wiring (2026-07-16 audit): there is no general
"classical GQ recognition" theorem — as an unscoped axiom this would be citation-shaped open mathematics. -/
opaque ClassicalGQRecognition : Prop
-- ⏸ axiom payne_thas : ClassicalGQRecognition

/-- Witt's theorem: over a field, `O(Q)` acts transitively on isometric isotropic subspaces / frames of a given
type. Discharges `ConfinementP4.FrameSelectorTransitive` — the assume-VT prune (confinement-P4) is sound because
the residual group is transitive on the selected isotropic-point cell, so the cell is one orbit. **Correctness
only** — a classical group-transitivity theorem (Artin, *Geometric Algebra*), NOT a complexity bound, and NOT the
bounded-WL-dim wall (`JointProfileRecoversAt`). Carried as a scoped citation; a **planned in-project build** (first
pieces done), expected to discharge before publication. -/
opaque WittFlagTransitivity : Prop
-- ⏸ axiom witt_flag_transitivity : WittFlagTransitivity

/-! ## 3. THE OBLIGATIONS — the endgame theorem statements

Each is a `sorry`-stubbed compile target. The `-- discharged by:` note records which completed project
theorem(s) + citation(s) the body (held in another file for conciseness) will plug into. When all `sorry`s are filled, `#print axioms canonizer`
= `[propext, Classical.choice, Quot.sound]` ∪ {the citations actually used}. -/

/-- **①a Soundness (UNCONDITIONAL).** When the canonizer answers, its output is a genuine relabelling of the
input — so equal canonical forms ⟹ isomorphic inputs. -/
theorem canon_sound (n : ℕ) (G : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonForm? n G = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G := by
  -- ★ SWAPPED (spike 2026-07-19): the record's `SoundOpt` half, applied directly — `Labelled n` is
  -- definitionally `Fin n → Fin n → Nat`, so no glue.
  exact (canonForm?_record n).1 G cG h

/-- **①b Completeness (UNCONDITIONAL).** Whenever it answers on both inputs, the canonical forms coincide
iff the graphs are isomorphic — a complete isomorphism invariant. "Never wrong", for every input. -/
theorem canon_complete (n : ℕ) (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat)
    (hG : canonForm? n G = some cG) (hH : canonForm? n H = some cH) :
    Iso G H ↔ cG = cH := by
  -- ★ DISCHARGED (2026-07-13): `ChainDescent.Descend.canonForm?_complete` — EXACTLY this shape, for the real
  -- branching object. Completeness is FREE: `CanonSpec.complete_of_isCanonicalFormOpt` (Stage 0a) says
  -- sound ∧ iso-invariant ⟹ complete, and `Descend.isCanonicalFormOpt_canonForm?` supplies both.
  --
  -- ★★ AND ITS TWO HYPOTHESES ARE NOW BOTH DISCHARGED (2026-07-14) — ① CARRIES NOTHING.
  --   · the refiner: `Refine.refineEquivariant_encodeFree` (the encode-free structural round);
  --   · the resolver contract `Descend.NarrowTransport`, via EITHER of its two routes —
  --       `Consume.narrowTransport_consume` (the ORACLE, `Covering` route; holds for EVERY oracle supply,
  --        because the resolver VERIFIES each candidate automorphism itself), or
  --       `Force.narrowEquivariant_forceBy` (the RIGID/FORCE route; sole obligation `KeyEquivariant`).
  -- Ready-made capstones: `Refine.exhaustive_canonizer`, `Consume.consume_canonizer`,
  -- `Force.force_canonizer` / `Force.lookahead_canonizer` — each gives ①a/①b/①c AND totality (never flags),
  -- with NO carried hypothesis at all.
  --
  -- ⛔ DO NOT restate the resolver contract as the single unconditional `Covering`: a covering resolver is
  -- provably VALUE-INVISIBLE (`Descend.canonForm?_eq_deferAll_of_covering`), which pins the object to the
  -- exhaustive branch-min (the retired `canonMin` anchor) and would force the rigid solver to KNOW THE ANSWER.
  --
  -- ★ SWAPPED (spike 2026-07-19): `Iso` is definitionally `CanonSpec.GraphIso`, so ①b is the free payoff
  -- applied verbatim.
  exact CanonSpec.complete_of_isCanonicalFormOpt (canonForm?_record n) G H cG cH hG hH

/-- **①c The flag is iso-invariant (UNCONDITIONAL).** Flagging is a property of the isomorphism class, not
of the labelling — so "flagged" is a well-defined statement about a graph up to iso. -/
theorem flag_iso_invariant (n : ℕ) (G H : AdjMatrix n) (h : Iso G H) :
    (canonForm? n G = none) ↔ (canonForm? n H = none) := by
  -- ★ SWAPPED (spike 2026-07-19): free from the record's `IsoInvariantOpt` half — a single equation on
  -- `Option`s carries the answer AND the flag; no separate flag obligation.
  exact CanonSpec.flag_iso_invariant_of_isoInvariantOpt (canonForm?_record n).2 h

/-- **② Poly-or-flag (the budget guarantee — the ONLY cost claim).** The descent either runs within the
explicit polynomial budget or it emits an honest flag. No residue predicate appears here. -/
theorem canon_poly_or_flag (n : ℕ) (G : AdjMatrix n) :
    cost n G ≤ costConst * (n + 1) ^ costDeg ∨ canonForm? n G = none :=
  -- ★ DISCHARGED 2026-07-28 — and on the LEFT disjunct, unconditionally: the record object is a
  -- single path of ≤ n+1 nodes by construction (`Select.selNode_children_length_le_one`, structural),
  -- every component is billed (`RecordCost` for the four supplies + the holonomy key,
  -- `RecordKey.supplyCost_guardSupply_le` for the union guard inside `orbKeyG`), and
  -- `RecordKey.descentCostS_selNode_recordKey_monomial` folds those into the pinned monomial.
  -- So the cost half needs no flag escape at all; what the flag is still needed for is ③.
  Or.inl ((RecordDeepenCell.recordDeepenCell_full_fast (n := n)).2.1 G)

/-! ⊘ **PROVENANCE for `canon_poly_or_flag`** (superseded 2026-07-28 by the discharge above; retained
because it records the two shapes that were *not* the answer).

  -- ⊘ THE STATUS BELOW IS SUPERSEDED (2026-07-17; retained for provenance). The guard design (`Stall.lean`)
  -- replaced the verify-consume-monovariant / fuel-placeholder plan: deferral IS the failure mode, the guarded
  -- descent is a SINGLE PATH of ≤ n+1 nodes or it flags (`Stall.resolvedAll_guard`, by construction), and the
  -- explicit polynomial is `SupplyCost.descentCost_pruned_lookahead_le` (end-to-end, for the canonizer of
  -- record, per fixed depth d). Filling this obligation = pinning the record object (fixes costConst/costDeg)
  -- + the opaque swap. See the file STATUS block.
  -- OPEN — this is now the main remaining obligation of ①/②. STATUS (2026-07-13):
  --  · `cost` is the `cost` PROJECTION of the same definition ①a/①b ride on: `ChainDescent.Descend.descentCost`
  --    (`descend` is written in `CostM`, so cost is co-defined with the value — no separate object, no bridge).
  --  · The OLD `n⁴` bound (`CanonForm.descentCost_le`) does NOT transfer: it was proved with `nbud = n`, i.e.
  --    the assume-VT single-path (`leaves = 1`) justification, which the branching/interleaved object breaks.
  --  · The poly guarantee is now the VERIFY-CONSUME MONOVARIANT (each covering-narrowing strictly reduces
  --    residual symmetry; each force reduces free relations; each defer is bounded by the branching bound)
  --    plus the fusion-severity look-ahead — see `docs/chain-descent-cost-model.md` STATUS and
  --    `docs/chain-descent-mixed-composition.md` Stage 4.
  --  · The flag is the MUTUAL STALL, not `base > baseMax` (the threshold-gated assume-VT flag is retired —
  --    it could misprune a fused rigid residue). `descend`'s current `fuel`-exhaustion `none` is a PLACEHOLDER
  --    for that stall test. NB fuel is PER-LAYER, never threaded, so each resolver is poly-or-flag LOCALLY.
  --
  -- ⊘ And the last shape that was wrong: the pinned `costConst * n ^ costDeg` monomial itself. See the
  -- `costConst`/`costDeg` block above — it is false at `n = 0` for the real object, at any numerals.
-/

/-- **③ Flag characterization (where the citations live).** A flag is emitted iff the input genuinely
contains an unhandled obstruction — NOT because the algorithm is weak. This is the theorem that earns the
"or Cameron/hidden-Johnson/IR-residue" escape; its proof consumes the classification citations.
NON-VACUITY OBLIGATION (separate lemma, `unhandledResidue_nonvacuous` below): `UnhandledResidue` is neither
always-true nor defined as "flagged". -/
theorem residue_if_flag (n : ℕ) (G : AdjMatrix n) :
    canonForm? n G = none → UnhandledResidue n G :=
  -- ★★★ DISCHARGED 2026-08-08 (`W-g`). The bridge is *Tinhofer ⟹ the consume resolver fires at every
  -- reached node*, and this is its contrapositive. It became provable **at this object** when the
  -- supply was cell-indexed: `RecordDeepenCell.handledSC_of_tinhoferGraph` shows the target cell
  -- narrows to one branch **on generators anchored in that cell** (`goodCell_of_tinhofer` +
  -- `orbitCompleteAt_of_goodCell`), and `Select.answersSC_of_handledSC` turns that into "never flags".
  -- ⛔ NOT a second-object discharge: `recordDeepenCell_full_fast` carries ①a/①b/①c, ② and ③ of the
  -- *same* definition `canonForm?` and `cost` are now defined as.
  (RecordDeepenCell.recordDeepenCell_full_fast (n := n)).2.2 G

/-- **Non-vacuity of ③ (the documented vacuity-trap guard).** There exist handled graphs (a flag is not
forced) AND unhandled ones (the excluded set is real). Without this, `residue_if_flag` is meaningless.

★ **DISCHARGED 2026-08-04** by `RestrictedTransport.tinhoferGraph_nonvacuous`: the handled witness is
`K₁,₂,₃` (complete multipartite with distinct part sizes, proved Tinhofer natively), and the residual
witness is **`K₃ ⊔ C₄`** — 2-regular, so 1-WL leaves one cell containing a triangle vertex and a
`C₄` vertex, which no automorphism can identify (the triangle count at a vertex is an `Aut`-invariant).
Both are `decide`-checked structural facts about the *graphs*; neither mentions the algorithm. -/
theorem unhandledResidue_nonvacuous :
    (∃ (n : ℕ) (G : AdjMatrix n), ¬ UnhandledResidue n G) ∧
    (∃ (n : ℕ) (G : AdjMatrix n), UnhandledResidue n G) :=
  ⟨⟨6, ChainDescent.TwinFamily.mpAdj ChainDescent.TwinFamily.part123,
     not_not_intro (ChainDescent.TwinFamily.tinhoferGraph_of_multipartite
       (ChainDescent.TwinFamily.isCompleteMultipartite_mpAdj ChainDescent.TwinFamily.part123)
       ChainDescent.TwinFamily.distinctPartSizes_part123)⟩,
   ⟨7, ChainDescent.RestrictedTransport.kcAdj,
     ChainDescent.RestrictedTransport.not_tinhoferGraph_kcAdj⟩⟩

/-! ## 4. THE HEADLINE — one quotable theorem, composed from the obligations

This body is REAL: it shows the composition. Its `#print axioms` is therefore exactly the union of the
obligations' axioms — **which, since 2026-08-08, is exactly Lean's three.** -/

/-- **The canonizer theorem — CORRECTNESS.** For every graph `G`: (i) whenever the canonizer answers on
`G` and any `H`, the outputs coincide iff `G ≅ H` (a complete iso-invariant — never wrong); and (ii) it
runs within the explicit polynomial budget.

★ **Note (ii) is now unconditional** — no residue disjunct. `canon_poly_or_flag` is proved on its LEFT
disjunct, so the escape was never needed; carrying it invited the reading that the cost claim depends on
the residue, which it does not. -/
theorem canonizer (n : ℕ) (G : AdjMatrix n) :
    (∀ (H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
        canonForm? n G = some cG → canonForm? n H = some cH → (Iso G H ↔ cG = cH))
    ∧ cost n G ≤ costConst * (n + 1) ^ costDeg :=
  ⟨fun H cG cH hG hH => canon_complete n G H cG cH hG hH,
   (RecordDeepenCell.recordDeepenCell_full_fast (n := n)).2.1 G⟩

/-! ## 5. The axiom footprint (the deliverable)

**★★★ 2026-08-08 — THE FILE IS CLOSED. Zero `sorry`, zero custom axioms.** Every `#print axioms`
below is exactly `[propext, Classical.choice, Quot.sound]`: `canon_sound`, `canon_complete`,
`flag_iso_invariant`, `canon_poly_or_flag`, `residue_if_flag`, `unhandledResidue_nonvacuous`, and the
composed `canonizer`. All of them are properties of **one** object — `canonForm?` and `cost` are the
value and cost projections of the same `RecordDeepenCell` definition, which `#eval` runs.

**No citation axiom is consumed by anything here**, so the 8 in §2 stay **commented out** rather than
being presented as the trusted base of something proved here (each is one `-- ⏸ ` from restoration
when W2 / Route C needs it). The paper must still state the intended citation base for the parts of
the project that do **not** live in this file.

⚠⚠ **Two things a reader must not over-read, both stated at source above:**
  · `②`'s **degree is a bound, not a measurement** — several components bill declared flat charges
    (see the `costConst`/`costDeg` block). It rules out exponentials; it does not establish that 13
    is the algorithm's true degree.
  · `③`'s residue is an **over-approximation** — `¬ TinhoferGraph` currently counts CFI graphs as
    residual although their obstruction is linear and belongs to the rigid resolver. Narrowing it is
    W2. The claim is *"a flag means a real structural obstruction"*, never *"a flag means hardness"*.

★ Measured (2026-08-08, re-measured at the **lazy** object after `W-e`), so it is not merely
definable: `canonForm? 2 K₂` and `canonForm? 6 K₁,₂,₃` both **answer**; `cost` = **1606** and
**20 321 716** against a budget of `69 · 3^13` and `69 · 7^13 ≈ 6.7 × 10¹²`. ⚠ The figure
38 212 276 that stood here is the **eager** `selNodeFastC` cost and no longer describes this object.

★ It also answers on `C₅` and on **`K₃ ⊔ C₄`** — the `unhandledResidue_nonvacuous` residual witness.
That is expected and is the point of `③`: the design is free to be stronger than what is proved, and
`③` is the instrument that measures how much of that strength has been *established*. ⚠ So the
paper must not write *"the canonizer flags on most interesting inputs"* — the accurate sentence is
***"the canonizer has not yet been proven on most interesting inputs."*** -/

#print axioms canonizer
#print axioms unhandledResidue_nonvacuous
#print axioms residue_if_flag

/-! The `①` trio — `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. -/
#print axioms canon_sound
#print axioms canon_complete
#print axioms flag_iso_invariant

/-! …and `②`, same footprint. -/
#print axioms canon_poly_or_flag


end Showcase
