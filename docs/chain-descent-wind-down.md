# WIND-DOWN — the closing plan

> **STATUS: research phase CLOSED (2026-08-01). This document is authoritative for what
> remains.** Every forward-looking item in every other `chain-descent-*.md` is **SUSPENDED**
> unless it appears in §2 below. Those docs remain accurate as a *record* of what was built
> and what was refuted; they are no longer a plan.
>
> # ✅✅✅ 2026-08-08 — `Publication.lean` IS CLOSED: ZERO `sorry`, ZERO CUSTOM AXIOMS
> `canonForm?` = `RecordDeepenCell.canonFormFast` (the fused descent at the **cell-indexed** supply
> `fun c => recordSupplyFast ++ Deepen.deepenCellSupply c`), `cost` = `costFast`,
> `costConst`/`costDeg` = **69 / 13**, and all of ①a ①b ①c ② ③ are projections of
> **`recordDeepenCell_full_fast`** — one object, as the standing steer requires. Every headline
> theorem prints `[propext, Classical.choice, Quot.sound]`, and the object `#eval`s.
> ⚠ Two caveats travel with it: `②`'s degree is a **bound from declared flat charges, not a
> measurement**, and `③`'s residue is an **over-approximation**. Both are stated at source.
> ✅ **The per-cell plan is COMPLETE** — `W-e` (lazy **billing**, not a lazy selector: the returned
> cost forced every cell, so laziness had to reach the bill) landed the same day. Measured on
> `K₁,₂,₃`: **2.4× faster than the eager cell-indexed object and 1.7× faster than the node-global
> one**, billing 20 % less than node-global — the per-cell design pays no premium at all now.
> **Remaining from the finish list: W2 (CFI), W3 (extraction), W4 (write-up), W5 (archive).**
>
> ### ▶▶ PICKING THIS UP FRESH? GO TO [§2a HANDOFF](#2a--handoff--where-a-fresh-reader-picks-up-2026-08-04).
> It carries the reading order, the gate command and its current numbers, the **`Publication.lean` state
> table**, the measured evidence, and the **sixteen corrections you will otherwise inherit from other
> docs**. ⚠ There is **no open decision** any more — that block is struck through below.
>
> **W1 is ✅ LANDED (2026-08-04)** — `TwinFamily.lean` + `RestrictedTransport.lean`, extended the same day by
> `DeepenComplete.lean` + `DeepenTransportOn.lean`. W4's go/no-go is **MET**.
> Gate **119 modules, ~231–361 s, exit 0** (`bash /workspace/scripts/build.sh`, 2026-08-08).
> **Tinhofer graphs are CANONIZED** (`canonizes_on_tinhofer`), the class is **inhabited and proper**
> (`tinhoferGraph_nonvacuous`), and `Publication.unhandledResidue_nonvacuous` is **discharged**.
>
> ## ⛔ THE OPEN DECISION BELOW IS **SETTLED AND DISCHARGED** (2026-08-08) — see §2a's START HERE block
> Neither (iv) nor (v). `canonForm?` keeps the fused object and gains a **cell-indexed** supply:
> `Select.selNodeC recordKey (fun c => recordSupplyFast ++ Deepen.deepenCellSupply c)`, which carries
> **all three obligations at once**, axiom-clean — `①` global and unconditional
> (`RecordDeepenCell.recordDeepenCell_canonizer`), `②` `cost ≤ 69·(n+1)^13` on every input with no
> flag disjunct (`descentCostSC_recordDeepen_monomial`), `③` at the tight residue `¬TinhoferGraph`
> (`not_tinhoferGraph_of_flag`); packaged as **`recordDeepenCell_full`**, and — since `W-i`/`W-e` — at
> the runnable, lazily-billed definitions as **`recordDeepenCell_full_fast`**. That combination is
> exactly what (iv) and (v) each miss. ✅ **`Publication.canonForm?`/`cost` ARE that object
> (`W-g`), and the file has zero `sorry` and zero custom axioms.** The either/or below is
> **provenance**.

> ⛔ ~~**ONE OPEN DECISION, and it is the only thing between here and a finished `Publication.lean`:**
> which object `canonForm?` should be, i.e. how to close its single remaining `sorry`
> (`residue_if_flag`). **Five candidates, all costed, in §2 W1's *"THE OPTIONS THAT REMAIN"* block —
> and it is now a clean either/or between two of them:**~~
>
> * **(iv)** `recordSupplyFast ++ twinSupply` — `①`/`②` stay **unconditional**, residue weakens to
>   `¬(Simple ∧ RootTwins)`. **Not built**; every piece exists, mechanically clear. *(user preference,
>   2026-08-04)*
> * **(v)** `guard (forceThenConsume holKeyFast deepenSupply)` — residue is the tight `¬TinhoferGraph`,
>   but `①b`/`①c` are proved **on the Tinhofer class** rather than globally. ✅ **FULLY BUILT**
>   (`DeepenTransportOn.deepen_object_package`).
>
> ⛔⛔ **Do not close it by moving the statement to a second object** — tried and reverted; `canonForm?`
> is meaningful only if `①`+`②`+`③` hold of the **same** object.
>
> **▶ R1 is no longer a fog.** It is one named predicate, `Deepen.OrbitComplete`, with the payoff chain
> proved (`deepenSupply_canonizer_of_orbitComplete`), a genuine partial discharge
> (`orbitComplete_of_good_or_trivial`), and a **positive** measurement base (17/17 + 13/13). See §2 W1's
> R1 block. It remains **suspended** as a research item; nothing downstream waits on it.
>
> Remaining after the decision: W2 (CFI), W3 (extraction), W4 (write-up), W5 (archive).

---

## 1. Why the research phase closed

Not because the remaining work is hard, but because the remaining work was assessed and
found to be either **already known**, **known false in the generality needed**, or
**identical to the open problem itself**. Recorded here so the decision is not re-litigated:

| Track | Assessment |
|---|---|
| **Consume / symmetry side** | Reaches Tinhofer graphs, which sit inside the known-easy hierarchy Discrete ⊂ Amenable ⊂ Compact ⊂ Godsil ⊂ Tinhofer ⊂ Refinable (Arvind–Köbler–Rattan–Verbitsky). Landing there is not new ground. |
| **CAO propagation at 2-WL** (`chain-descent-cao-propagation.md`) | ⛔⛔ **THE 2-WL LEG OF THIS ROW IS RETRACTED (2026-08-11) — read that doc's §0.0a.** ~~The target is essentially *"the one-point extension of a schurian coherent configuration is schurian"*, and the identification is exact.~~ **The identification is false in both directions**: the target has the **weaker hypothesis** (CAO — *fibres* are orbits — ⊂ schurian) and the **weaker conclusion** (`Xα`'s *fibres* are orbits ⊂ `Xα` is schurian) ⟹ the two statements are **incomparable**. M–P arXiv:1010.4450 §2.4 correctly names the *object* and §2 correctly gives `Aut(X)α = Aut(Xα)`; neither quote is about schurity. ⟹ **the entire literature leg (M–P per-class, Wielandt, Evdokimov–Ponomarenko's schurity number) is evidence about a different statement and does not bear on the target.** Named witness: **Shrikhande** — non-schurian S-ring (paid ticket), extension fibres `[1,3,6,6]` = exactly `Aut_e`-orbits, i.e. propagation *holds*. ⚠ §4.3 is a statement about a **proof route**, not about the target, and was misquoted here as the latter. **What survives:** the four **1-WL** refutations, and the route refutations §4.1/§4.2/§4.3. **Status at 2-WL is what that doc's STATUS table always said: OPEN, no counterexample.** ▶ Live again 2026-08-11 (user) for **Lean footing**; §13's conversion gap stays suspended. |
| **Force / asymmetry side** | `keySeparatesAll_rawKey` shows separation alone is cheap; the hard object is separation ∧ equivariance, and `forcePick_open_clause_is_poly` pins the entire remaining difficulty to the poly clause. `KEY_scoping.md` §3's tie-group ladder terminates at non-solvable = the wall. The project has machine-checked that its residual difficulty *is* the known hard core. |
| **Linear core extraction (L1–L4, `Gauge*`)** | The solvable corner reduces to per-layer linear systems — which is Luks territory, and the doc's own §3a concedes the Luks sharpening makes it citable rather than novel. |
| **W2 / non-solvable wall** | Untouched. This is the open problem. |

**What this does not diminish:** the verified artifact. `canon_sound`, `canon_complete`,
`flag_iso_invariant` and `canon_poly_or_flag` are proved against the real executable object
with a clean axiom footprint, and no comparable machine-checked canonization *algorithm*
(as opposed to certificate checker) appears in the literature. Finishing that is §2.

---

## 2. THE FINISH LIST — the only live work

Ordered. Each is bounded; if one exceeds its box, drop it and move on rather than
reopening the research.

### W1 — Tinhofer family `Handled` — ✅ **LANDED 2026-08-04** *(box was 2 weeks; took one session)*
Turn [`KeyComplete.handledS_of_reached_tinhofer`](../GraphCanonizationProofs/ChainDescent/KeyComplete.lean#L325)
from a hypothesis-defined class into a **named family**. Today the only `Handled`
populations are that one and `handled_emptyAdj`; everything else
(`handledS_recordSupply`, `handled_of_seal*`) is a transfer or a reduction lemma.

> ## ✅ DELIVERED — [`ChainDescent/TwinFamily.lean`](../GraphCanonizationProofs/ChainDescent/TwinFamily.lean), in `build.sh`, axiom-clean, 0 `sorry`
>
> **The family:** complete multipartite graphs with **pairwise distinct part sizes**
> (`IsCompleteMultipartite` + `DistinctPartSizes`), with `mpAdj` as a constructor so it is visibly
> inhabited at every `n`.
>
> **★★ THE SOCKET IS STATED ON "NO RIGID OBSTRUCTION", NOT ON TWINS** (2026-08-04, second pass —
> the twin/multipartite reading was too weak to carry forward):
>
> | theorem | statement |
> |---|---|
> | `schurianAt_iff_no_rigidObstruction` | `SchurianAt χ ↔ ∀ cid, ¬ RigidObstructionAt χ cid` — the class IS "no rigid obstruction", the exact complement of the rigid resolver's domain |
> | `StepClosed P adj` | *peeling a layer keeps you in the class* — the formal content of your Tinhofer remark, carried as a hypothesis |
> | **`handledS_of_noRigidObstruction`** | ★★★ **THE SOCKET**: step-closed + holds at root + no rigid obstruction ⟹ `HandledS`. **To enlarge the handled region, supply a wider `P` — nothing below changes.** |
> | `mem_of_reaches` | a step-closed class holding at the root holds at every reached node (`Reaches`'s step and `Deepen.step` are the same operation) |
>
> ⚠ **The socket cannot be widened for free**: `SchurianAt` is *not* preserved by `Deepen.step` in
> general — that is CAO propagation, refuted at 1-WL. `StepClosed` is a hypothesis, not a lemma; a
> wider class must prove its own closure.
>
> **The twin/multipartite layer is now one witness feeding the socket, not the claim:**
>
> | theorem | statement |
> |---|---|
> | `handledS_of_multipartite` | the family is `Select.HandledS` — W1's literal target |
> | `isColAut_swap_of_twin` | a same-coloured twin transposition is a colour-preserving automorphism |
> | `twinCells_step` | ★ the invariant is **inherited** — the obligation collapses to the root |
> | `rootCol_eq_of_twin` | ★ **non-vacuity**: a twin pair survives refinement ⟹ root not discrete |
>
> ## ⛔⛔ CORRECTION (2026-08-04, later) — §9's BRIDGE IS STATED AT A **NON-EXECUTABLE** OBJECT
>
> The bridge table below is true and axiom-clean, but it is stated at `(Deepen.orbKey,
> Deepen.deepenSupply)` and **`Deepen.orbKey` is `noncomputable`** — its guard is an `n!` decidability
> instance (`Deepen.instDecidableTinhoferPath = Classical.dec`). Verified by compiler error:
> `#eval` on that canonizer fails with *"depends on `Deepen.orbKey`, which is `noncomputable`"*.
> So §9 alone cannot support the sentence "our verified canonizer answers on every Tinhofer graph" —
> the coverage would come from a different object than `①`/`②` do.
>
> ⚠ **Distinguish two things that were being conflated.** The *hypothesis* `TinhoferGraph` is
> deliberately non-computable and that is **fine** (a classifier need not be decidable to be a useful
> antecedent — cf. defining `residueHiddenJohnson` rather than constructing one). The defect is in the
> **object**: `orbKey` is part of the algorithm.
>
> ## ✅ REPAIRED — `TwinFamily.lean` §10, the publishable form
>
> The force key **drops out entirely**. What resolves a Tinhofer node is consume, and
> `Deepen.deepen_branch_orbit_iff_aut` (landed 2026-07-23, previously unused here) already proves
> `deepenSupply` is a *complete* orbit oracle there. Feeding `SchurianAt`'s automorphism to its `mpr`
> gives `Consume.CellIsOrbit`, hence the **blind** `Residue.Handled` for **every** key — strictly
> stronger than §9's `HandledS`, with nothing `noncomputable` anywhere.
>
> | theorem | statement |
> |---|---|
> | `cellIsOrbit_deepenSupply_of_schurianAt` | the firing lemma: Schurian + `Tinhofer` ⟹ `deepenSupply` certifies the branch cell |
> | **`noStall_of_schurianAt`** | ★★★ **the NODE-LOCAL form — *a Tinhofer residue does not stall*.** Speaks about one reached node, so a resolver that peels a layer and lands here inherits it. This is the shape W2's scope correction asks for. |
> | **`handled_of_tinhoferGraph`** | the blind `Residue.Handled`, for **every** key |
> | **`answers_of_tinhoferGraph`** / **`not_tinhoferGraph_of_flag`** | ★★★ answers; and **if it flags, the input is provably not Tinhofer** — at an object that RUNS |
> | **`answers_poly_of_tinhoferGraph`** | ★★★ **`②` too** — answers *and* `descentCost ≤` an explicit polynomial |
> | `answers_poly_part123` | the concrete non-root-discrete witness, so §10 is non-vacuous |
>
> **Measured:** `#eval` of §10's object on `mpAdj part123` returns `true` (it answers). All seven
> capstones `[propext, Classical.choice, Quot.sound]`.
>
> ## ✅✅ AND `①` IS NOW CLOSED TOO — `ChainDescent/RestrictedTransport.lean`
>
> ~~`①` at §10's object needs `SupplyEquivariant Deepen.deepenSupply` = the parked R1 crux~~ — **not the
> route taken, and R1 is not needed.** (User steer 2026-08-04: don't chase a global R1; the descent's
> invariance on a Tinhofer graph follows from it never taking a wrong step.) That reading is right, and
> the mathematics was **already proved** — it is `Deepen.deepen_branch_orbit_iff_aut`, whose RHS *is* the
> true automorphism-orbit relation. What was missing was **plumbing**: `CanonSpec.IsoInvariantOpt` and its
> spine (`Descend.TransportAt` / `NarrowTransport`) are `∀ adj σ χ`, while the Tinhofer facts hold only on
> (Tinhofer graphs) × (**reachable** colourings). ⚠ The second axis is the one that is easy to miss —
> at an unreachable `χ` a cell need not be an orbit even in a Tinhofer graph.
>
> **`RestrictedTransport.lean` relativizes the spine on both axes, additively — `Descend.lean` is not
> touched and no existing theorem changes.** `TransportOn C` / `NarrowTransportOn C` /
> `descend_transport_on` / `isoInvariantOn` / `complete_on` / `flag_iso_invariant_on`.
>
> ★★ **And the discharge needs NO SUPPLY.** `KeySeparatesAt key adj χ` demands that branch pairs *no
> automorphism links* get different keys; at a `SchurianAt` node every branch pair **is** linked, so the
> predicate is vacuous **for every key** (`keySeparatesAt_of_schurianAt`, six lines). So
> `ForcePick.forceThenPick` — force, keep one, no supply, no verification, **no stall channel** — is
> sound there. `deepenSupply` drops out, and with it the declared flat `n⁶` charge; `②` is the key's cost
> alone.
>
> | theorem | statement |
> |---|---|
> | `descend_transport_on` | the transport induction over (class of graphs) × (reached colourings) |
> | `keySeparatesAt_of_schurianAt` | ★ **"no wrong step to take"** — separation is vacuous at a Schurian node, for every key |
> | `relabelClosed_tinhoferGraph` | `TinhoferGraph` is closed under relabelling (via `cellSingleOrbit_transport_iso`) |
> | **`canonizes_on_tinhofer`** | ★★★ **sound (unconditional) ∧ complete on the class ∧ never flags** |
> | `descentCost_on_tinhofer` | ★★★ **`②`** — explicit polynomial, every input, no hypotheses |
> | `canonizes_on_tinhofer_holKeyFast` | the package at a computable equivariant key |
>
> ⚠⚠ **DO NOT file this as the banned route.** `ForcePick`'s header says *"do not instantiate
> `forceThenPick` at `orbKey`/`orbKeyG` and read the result as a canonizer"* — that warns about
> `KeySeparatesAt` holding for the **wrong** reason (a guarded key returns a constant off its guard while
> genuine separation is still required, so the pick discards genuinely different branches). Here it holds
> for the **right** reason: the cell has no non-automorphic pairs, so there is nothing to separate and
> nothing unsound to discard. Same syntax, opposite semantics.
>
> ⟹ **the claim to publish is now *"Tinhofer graphs are CANONIZED — sound, complete, never flagged,
> within an explicit polynomial budget"*.** The class hypothesis stays the non-computable
> `TinhoferGraph`, which is correct (it is a classifier, not part of the algorithm).
> ▶ **To widen it, supply a wider `C`**: all that is asked is `RelabelClosed C` plus *"every reached
> non-discrete colouring is Schurian"*. A resolver that removes some rigid obstruction enlarges the
> second clause with nothing here re-proved.
> ⚠ `deepenSupply`'s `②` rides a **declared flat `n⁶`** charge (an honest over-estimate of `≤ n` reps ×
> `≤ n` levels × a warm refinement `n³`, plus `≤ n` verifications at `n²`) — *declared*, not derived,
> the same caveat already owed for `holKeyFast`'s flat `n⁵`.
>
> **★★★ THE LITERATURE BRIDGE (§9) — one theorem imports the whole hierarchy.**
> `IndivReach` (individualization closure — **step-closed by construction**, so no CAO-propagation
> obligation appears) + `TinhoferGraph` = *"no rigid obstruction at any individualization-reachable
> colouring"* = the literature's Tinhofer condition in the project's vocabulary.
>
> | theorem | statement |
> |---|---|
> | **`handledS_of_tinhoferGraph`** | ★★★ a Tinhofer graph is `HandledS` — **it progresses at every step** |
> | `answersS_of_tinhoferGraph` | …hence the fused descent never flags on it |
> | **`not_tinhoferGraph_of_flagS`** | ★★★ **THE SHOWCASE**: if the canonizer flags, the input is provably **not Tinhofer** — `③`'s shape against a *named literature class*, not an opaque atom |
> | `tinhoferGraph_of_multipartite` | witness 1 — the twin/multipartite family (exercises the resolvers) |
> | `tinhoferGraph_of_root_discrete` | witness 2 — every 1-WL-discretizing graph |
>
> ★ **Coverage this buys by citation of membership, with no further Lean**: trees and cycles (compact —
> Tinhofer 1986), complete graphs (Birkhoff), matchings `mK₂`, complete multipartite (proved natively),
> and all of `Discrete ⊂ Amenable ⊂ Compact ⊂ Godsil ⊂ Tinhofer` (AKRV), closed under complement and
> `G ↦ mG`. **Per-family Lean proofs do not pay for themselves against this** — decided 2026-08-04.
>
> ⚠ **The hypothesis is deliberately non-computable and that is correct** (user): `TinhoferGraph` is a
> *classifier*, not part of the algorithm — deciding it is ≥ GI on vertex-transitive graphs (AKRV
> Thm 22). What is needed and proved is *"if it IS Tinhofer it progresses"*; the contrapositive is the
> useful direction.
> ⚠⚠ **Witness 2 is vacuous for the resolvers.** On a root-discrete graph `HandledS` holds because
> there is no reached non-discrete node — refinement alone finishes and neither resolver is consulted.
> It is breadth of the *answering* claim, not evidence the architecture does anything. Quoting the
> Babai–Erdős–Selkow "almost all graphs" measure claim without this caveat takes credit refinement
> earned. The witness that exercises the resolvers is multipartite (`not_discrete_part123`).
> ⚠ **Naming is prose, not a theorem**: `IsColAut adj P_F = Aut_F` (AKRV's pointwise stabilizer) is
> standard but not machine-checked here. The paper must say so.
>
> **★★★ AND THE ANSWERS → CANONIZED WALL IS CROSSED (§8) — this was the W0 item.**
> Under `TwinCells` the orbits are generated by **transpositions**, so `(orbKey, deepenSupply)` is not
> needed at all: a **computable** `twinSupply` certifies the branch cell in one `WordReach` step.
>
> | theorem | statement |
> |---|---|
> | `cellIsOrbit_twinSupply` | the branch cell is one orbit of the *verified* twin transpositions |
> | `handled_of_multipartite` | the **blind** `Residue.Handled` — strictly stronger than `HandledS` — **for every key** |
> | `supplyEquivariant_twinSupply` | via `GensEquivariant` (the supply is a structural function of `(adj, χ)`) |
> | **`canonizer_twinSupply`** | ★★★ **`①`**: `IsCanonicalFormOpt` — sound + iso-invariant, hence complete |
> | **`canonized_of_multipartite`** | ★★★ **both halves**: `①` **and** *answers, never flags*, at `holKeyFast` + `twinSupply`, guard in place (so single-path too) |
> | `canonized_part123` | the concrete `K₁,₂,₃` witness, canonized |
> | **`answers_poly_of_multipartite`** | ★★★ **`②` (added 2026-08-04, later)** — answers **and** `descentCost ≤` an explicit polynomial, via `SupplyCost.handled_answers_poly` + the two new bills `supplyCost_twinSupply_le` / `gens_twinSupply_length_le`. **With `canonizer_twinSupply` this family now has `①` ∧ `②` ∧ answers at ONE object** — the only place in the project where all three meet on a named family. |
>
> **★ The structural finding that made it cheap.** `Deepen.step = refineV encodeFreeFast ∘ indivOne`
> and *both halves only split cells*, so `TwinCells` ("every merged pair is a twin pair") is inherited
> by every descendant with **no graph-specific reasoning**. The per-family obligation therefore
> collapses to a **single root-level condition** — everything below the root is free. All the graph
> content lives in one degree computation (`degSum_eq_of_rootCol_eq` + `degSum_multipartite`).
>
> **⚠⚠ WHAT IS NOT CLAIMED — do not quote this as "canonized".** The claim is *answers, never flags*.
> The canonical-form half `①` needs `NodeTransport`, hence `SupplyEquivariant` on the supply;
> `foldSupply`/`deckSupply`/`deck2Supply` carry it, **`deepenSupply` does not** — which is precisely
> why it is held out of `Publication.canonForm?`'s record object. That boundary is **pre-existing and
> untouched**: `handledS_of_reached_tinhofer`, the socket W1 names, is stated at
> `(orbKey, deepenSupply)`. Closing it means either `SupplyEquivariant deepenSupply` or re-basing the
> family onto the record supply via `OrbitPrune.SameOrbits` + `Select.handledS_of_sameOrbits` — the
> second is the live route and is **not** in W1's box.
>
> **⚠ Value, restated.** This family is canonizable by sorting degrees. It is an honest *first*
> population of the predicate and it makes W4's go/no-go formally satisfiable; it is **not** the
> "polynomial where IR solvers are exponential" claim, which remains W2.

~~⚠ **Scoping risk, flagged before starting:** `chain-descent-rigid-seal.md` §9.1 states the
per-family `Tinhofer` discharge is the *same work* as the rigid seal on that family. Scope
this first. If it pulls in the rigid seal, it is out of box — take W2 instead.~~

✅ **SCOPED 2026-08-04 — the risk was pointed at the wrong route, and cannot bite this socket.**
`handledS_of_reached_tinhofer` demands `Deepen.Tinhofer` at **every** reached non-discrete node —
pure consume, no disjunction. A `CellSingleOrbit` failure **is** a `RigidObstructionAt`
(`rigidObstruction_of_not_cellSingleOrbit`, definitional), so a family carrying one anywhere on the
descent does not "need the rigid seal": it **fails the hypothesis outright and is not a candidate**.
Measured agreement — on rigid multipedes `descend_cert` levels are `[0,0,0,…]`, i.e. `TinhoferPath`
holds only *vacuously* (DUAL §8.4, the AKRV rigid collapse). Rigid-seal §9.1's "same work" applies to
the **disjunctive** obligation (`NodeResolved` via consume *or* force; `Handled` via
`handled_of_seal`), which is W2's route, not W1's.

⟹ **W1's real constraint is the opposite one:** the family must be *rigid-obstruction-free along the
descent* (every selected cell a genuine `Aut`-orbit). ⚠ That makes **vacuity**, not the seal, the live
risk — a family whose root refines to discrete satisfies `HandledS` for free and proves nothing
(`Residue.handled_of_root_discrete` is already that ring). **Gate step 0 on it:** the probe must show
non-vacuous descents (≥ 2 certified levels) before any Lean is written.

#### ★★ STEP 0 MEASURED (2026-08-04) — the family passes, and the proof's decomposition is pinned

`scratchpad/probe_w1_multipartite.py` (+ `probe_w1_cellshape.py`), logs
`probe_w1_unreduced_n10.out` / `probe_w1_reduced_n16.out` / `probe_w1_cellshape.out`.

| run | graphs | failures | unknown | budget skips | max levels | verdict |
|---|---|---|---|---|---|---|
| unreduced baseline, n ≤ 10 | 238 | **0** | 0 | 0 | 7 | pass (capped: `TRUNC` rows logged) |
| orbit-reduced, n ≤ 16 | **1766** | **0** | 0 | 0 | **14** | **pass, zero truncations** |

★ What was measured is the **selector-independent** statement — *every* cell at *every* reached node
is a single orbit — which is **strictly stronger** than `Deepen.Tinhofer` and therefore implies it
under **any** selector. ⟹ this **dodges the standing colour-id-order convention limit** (cao-propagation
§7.4/§8.3): nothing reads an id order, and 1-WL's output *partition* is a function of the input
partition alone. **No Lean `#eval` cross-check is owed here** — but it *is* owed the moment anyone
weakens the probe to the selected-cell-only form.

★ **Non-vacuity gate passed**: 1764 of 1766 graphs have ≥ 2 reached non-discrete nodes, max descent
14 levels — so this is *not* the `handled_of_root_discrete` ring in disguise.

★ **CLAIM S — the two-case decomposition is CORRECT** (`probe_w1_cellshape.py`, 248 graphs, **0
violations**): every cell is either (i) inside one part → `Equiv.swap` of twins (cheap: `IsColAut`
is two conjuncts), or (ii) a disjoint union of ≥ 2 **complete, equal-sized** parts → one explicit
part-swap permutation. Counts: 8025 case-(i) cells, 3189 case-(ii). ⚠ Case (ii)'s *complete* and
*equal-sized* clauses are what make the permutation exist — they are the load-bearing part.

★ **The chain to the socket closes with existing lemmas**: `Descend.branches χ` is the target cell's
vertices; `DescentReach.cons`'s side condition (`∃ u ≠ v, χ u = χ v`) is the probe's branch rule; and
`KeyComplete.reaches_of_descentReach` carries every `TinhoferPath` level back into `Descend.Reaches`.
Colour→structure needs no new lever either: `sigKey_eq_iff` + `Refine.refineRound_eq_iff` already give
*equal colour ⟺ equal old colour ∧ equal signature multiset*.

#### ⛔ STEP 0c — COGRAPHS ARE REFUTED (2026-08-04). The family boundary is narrower than "modules".

`scratchpad/probe_w1_cographs.py` → `probe_w1_cographs.out`. Generator validated against the known
cograph counts (1, 2, 4, 10, 24, 66, 180, 522, 1532; P₄ correctly absent). **2340 cographs, n ≤ 9,
0 unknowns, 0 truncations — and 18 FAILURES** (2 at n = 7, 4 at n = 8, 12 at n = 9), every one **at
the ROOT**.

**★ Minimal witness: `K₃ ⊔ C₄` (n = 7)** — cotree `U(J(x,x,x),J(U(x,x),U(x,x)))`, plus its complement.
The graph is **2-regular**, so 1-WL gives a single 7-vertex cell, while `Aut = S₃ × D₄` has **two**
orbits `{0,1,2} | {3,4,5,6}`. Cell ≠ orbit at depth 0. (This is the textbook `C₃ ⊔ C₄` vs `C₇`
colour-refinement blind spot arriving inside the cograph class.)

**★★ And 2-WL fixes it exactly — measured, both witnesses:**

| | 1-WL root | **2-WL root** | exact `Aut` orbits |
|---|---|---|---|
| `K₃ ⊔ C₄` | 1 cell `{0..6}` | **`{0,1,2} \| {3,4,5,6}`** | `{0,1,2} \| {3,4,5,6}` |
| its complement | 1 cell `{0..6}` | **`{0,1,2} \| {3,4,5,6}`** | `{0,1,2} \| {3,4,5,6}` |

⟹ a **third and fourth** independent witness for cao-propagation §13.6(c)'s pattern: the failure is
**refiner strength at the BASE case**, not propagation. Same diagnosis §13.6(2) gave for the CFI nodes.

**▶ Why complete multipartite survives and cographs do not.** The obstruction is 1-WL merging two
*components/modules of equal degree but different shape*. In a complete multipartite graph a vertex's
degree is `n − |part|`, so **equal degree ⟹ equal part size ⟹ conjugate** — the merge cannot happen.
Cographs have no such coupling. ⟹ **the passing family stays multipartite/cluster; cographs are out**,
and any wider candidate must supply its own degree↔orbit coupling.

⚠⚠ **THE OPEN QUESTION IS VALUE, NOT VIABILITY.** Complete multipartite / cluster graphs are
canonizable by sorting degrees; as W4's headline this invites *"you proved it on a class where the
trivial algorithm works."* W1 is now clearly **in box** — but on its own it probably does **not**
satisfy W4's go/no-go, which is why the wind-down calls W2 the higher-value item. Decide before
spending the two weeks.

⚠ **Naming (2026-08-04).** `Deepen.Tinhofer` is **not** the literature's Tinhofer — it differs on
*four* quantifiers (which cell: `chooseIdK`'s vs all; which vertex in it: the `finRange` head vs all;
what must hold: the selected cell is one orbit vs the whole partition `P_F` equals the orbit partition;
which `F`: one descent path vs all). All four weaken it, so **literature-Tinhofer ⟹ project-Tinhofer**
and the covered class is a *superset*. Do **not** change the design to match (it would break
`TinhoferPath`'s single-path recursion, hence `②`). Call it **path-local Tinhofer** and land the
bridge lemma `akrvTinhofer → ∀ reached χ, Deepen.Tinhofer` so the implication is machine-checked.

### W2 — the CFI **layer**, not a CFI family *(box was 2 weeks; ✅ stages 1–2 built 2026-08-08; stage 0's retarget is RETRACTED — read the re-affirmation block FIRST)*

> # ⛔⛔⛔ 2026-08-10 — READ [`chain-descent-force-refinement-channel.md`](./chain-descent-force-refinement-channel.md) BEFORE ANY OF THIS SECTION
>
> **The foundation under W2 is missing, and it explains every dead end below.** Verified at source:
> in the published object **the force key's value never enters a colouring** — force's only channel is
> `Force.keepMin`, *selection inside one cell*. So a force key that cleanly splits a mixed cell into
> three orbit-blocks **accomplishes nothing**: the argmin block is kept and the fact that the others
> were different is discarded. ⟹ *"force separates mixed-orbit cells"* — force's core job — **is not
> expressible as success** in the object as built, and success is binary: whole cell one orbit
> (consume) or key injective on the cell (force).
>
> ★★ That single fact is the common cause of three "independent" walls recorded below: the **≤ 8-value
> cap** on `baseReadPin` (a cap on a *standalone key*, not on a refiner — `refineBy` pairs the read
> with χ and the next 1-WL round propagates it), the **`hrigid`** hypothesis in every rigid firing
> lemma (whole-cell injectivity is the only force success the interface offers), and the **Frucht**
> result of item 3b (12 blocks, *each already a single gauge-orbit* — force needs only to **split**,
> and there is no channel for a split).
>
> ⟹ **Chasing a stronger reader (S3) or a CFI coverage theorem on this interface is building on a
> foundation that cannot express the goal.** The new doc carries the diagnosis, three ranked methods
> (give force a **refinement channel**; use the row space **relationally** via
> `Linked u v := e_u + e_v ∈ rowspace H`, which is order-free, gauge-blind and *decidable*; and the
> **reduction** of CFI cell-separation to base edge-separation, with its ceiling), and **the step-0
> probe that must run first**. Everything below stays accurate as a record of what is refuted.

> # ⛔⛔⛔ SCOPE RE-AFFIRMATION (user, 2026-08-08, later) — W2 IS A **FORCE-SIDE LAYER** THEOREM
>
> **The architecture, restated by the user, and it is what the built contract already says:**
> * the **consume** resolver handles **CAO residues** — cells that *are* orbits;
> * the **force** resolver **splits mixed-orbit cells** so that a CAO node is reached.
>
> That is `Force.forceBy_no_narrowing_on_orbit` + `Descend.narrow_eq_branches_of_orbit` in prose:
> the two routes have **complementary, non-overlapping firing domains**, and force is *forbidden* to
> fire on an orbit cell exactly where consume must.
>
> **Why CFI is the chosen residue family:** the obstruction it *adds* is one force can always
> identify and convert into a solvable form (the F₂ gauge → canonical RREF → equivariant for free,
> poly by Gaussian elimination — [`README.md`](../README.md) ¶"ladder"). And because CFI **keeps the
> base graph's own properties**, the publication theorem is **not** *"canonize every CFI graph"* —
> that would include canonizing every base graph, i.e. GI. It is:
>
> > ### ★★★ **solve the CFI *part* of every CFI graph.**
>
> ### ⟹ THREE CONSEQUENCES, AND THEY CHANGE WHAT STAGE 0 MEANT
>
> **1. Stage 0's CFI-root result is a CONFIRMATION of the design, not a blocker.** Both root cells of
> CFI-over-cubic are **mixed-orbit** (3 certified `Aut`-blocks each). A mixed cell is *precisely*
> force's domain and one where consume is *forbidden* to fire. Measuring *"consume cannot take the
> CFI root"* measured the division of labour working as specified. ⛔ The inference recorded below —
> *"⟹ force-side ⟹ Track R suspended ⟹ do not plan W2 around CFI-over-cubic"* — **inverts the
> intent** and is struck.
>
> **2. ⛔ THE `mp7` RETARGET IS RETRACTED.** It replaces a **layer** theorem with a **family
> membership** theorem — the exact move SCOPE CORRECTION #1 (just below) forbids — and it does not
> even buy the headline it was chosen for: the Neuen–Schweitzer exponential lower bound is proved on
> multipedes that are **rigid** (`DUAL_resolver_scoping.md` §8.2 quotes their `|Aut| = 1`; a
> multipede is rigid ⟺ its base is *odd* ⟺ the biadjacency has **full F₂ column rank**,
> `chain-descent-exhaustive-obstruction.md`). `mp7` has gauge `Z₂³` and **`|Aut| = 1344`** ⟹ it is
> the **even, non-rigid** multipede, i.e. the complement of the NS family. ⚠ And note the general
> form: **no consume-side coverage theorem can ever carry the NS claim**, because consume certifies
> symmetry and that family has none. `mp7` remains a fine *second named family* exercising
> `kernelSupply`; it must never be quoted as the NS sentence.
>
> **3. ★★★ THE REAL BLOCKER, AND IT IS NAMED IN THE SOURCE: the record key has NO SOLVER
> COMPONENT.** `RecordKey.recordKey = pairKey holKeyFast (orbKeyG guardSupply)`, and
> `Deepen.guardSupply = foldSupplyFast ++ deckSupply ++ deck2Supply ++ matchSupply` — **`kernelSupply`
> is deliberately excluded** (`DeepenGuard` §8a: it is provably not `GensEquivariant`).
>
> ⛔ **CORRECTION (2026-08-09) — an earlier version of this line said *"all of the project's F₂
> machinery is on the consume side"*. That is FALSE.** There are **two independent F₂ solvers**, and
> they solve opposite sides of the same matrix:
>
> | | solves for | output | runs today? |
> |---|---|---|---|
> | **consume-side** `Kernel*` (~1200 lines) | what **can** move — the null space `L` (`dim ker > 0`) via rails → parity patterns → Gaussian elimination, each basis vector emitted as a permutation and **verified edge-by-edge** | automorphisms | ✅ **yes** — inside `recordSupplyFast`, at every node |
> | **force-side** `Forcing*` + `Rigid*` (~4400 lines) | what **cannot** move — P1 extracts refinement-as-unit-propagation into rows of `H`; P3-F₂ gives uniqueness when `dim ker = 0`; `RigidRREF` makes the answer canonical (RREF depends only on the subspace, so relabelling-invariance is free); `RigidGen`/`RigidRefine` turn it into a key | a canonical labelling | ❌ **gated and axiom-clean, instantiated in NOTHING** |
>
> ★ That is the architecture exactly: **consume solves the kernel to clear orbit cells; force solves
> where the kernel is empty to split mixed cells.** The surviving claim is the narrow one —
> **the *published object's force key* contains no solver** (`compKey` appears in `RecordKey.lean`
> and `ForcePick.lean` only in **comments**, verified).
> [`RecordKey.lean`](../GraphCanonizationProofs/ChainDescent/RecordKey.lean#L10)'s
> own header says so verbatim: *"`Deepen.orbKeyG guardSupply` **now**, `RigidSeal.compKey`'s solver
> key **later**"*. That "later" is `RigidRREF`/`RigidFrame`/`RigidGen`/`RigidRefine.readAgg` — built
> and axiom-clean — whose `①` (`genEquivariant_genOfRef`) is conditioned on `RefEquivariant ref`,
> i.e. the **poly frame set = Track R P2/P3, which §3 suspends.**
>
> ⟹ **The plan's inconsistency, stated plainly: W2 has been on the finish list while its sole
> enabler has been on the suspended list.** W2-as-intended is not a family proof; it is *"wire a
> solve-derived key component into `recordKey`"*, which is a change to the **published object**
> (re-bill `②`; one new `KeyEquivariant` obligation) and needs exactly one piece of Track R
> un-suspended. That is a user decision, and it is the real W2 go/no-go.
>
> ### ▶ WHAT TO DO, IN ORDER
>
> ### ✅ (i) IS LANDED — 2026-08-08, `SelectCell` §9a + `RecordDeepenCell` §3b
>
> Gate **exit 0 / 237 s**; 15 new declarations, all `[propext, Classical.choice, Quot.sound]`;
> `Publication.lean` untouched and still zero `sorry` / zero custom axioms. Built first try.
>
> | | what |
> |---|---|
> | `Select.CellResolvedAt` | the condition on the key's **survivors** (`keepMin key adj χ (cellList χ c)`), not on the cell |
> | **`cellNarrowC_length_le_one_of_cellResolvedAt`** | the firing lemma — the *original proof verbatim*, weaker hypothesis |
> | `cellResolvedAt_of_cellOrbitAt` → `cellNarrowC_length_le_one_of_cellOrbitAt` | **route 1, consume**; the old theorem is now a corollary ⟹ **nothing regressed** |
> | `CellSeparatedAt` · `keepMin_length_le_one_of_cellSeparatedAt` · `cellResolvedAt_of_cellSeparatedAt` | **route 2, force** — a key injective on the cell resolves it with **no supply**; the only route that can reach a cell carrying no symmetry |
> | `cellResolvedAt_of_keepMin_le_one` | route 2's raw form (`\|keepMin\| ≤ 1`) |
> | **`SomeCellResolved`** · **`handledSC_of_someCellResolved`** | ★ the disjunctive socket |
> | **`RecordDeepenCell.handledSC_of_resolvedCells`** · **`not_all_resolved_of_flag`** | it and its `③` at the **published** object |
> | `someCellResolved_of_resolvableCellAt` · `someCellResolved_of_cellSeparated` | the containment, and the force half's entry point |
>
> ★ **The MIXED case is now expressible for the first time** — key cuts between orbits, supply
> certifies the survivor. It was unreachable from either hypothesis alone, and it is the case a CFI
> gadget cell needs. ⚠ `keepMin_length_le_one_of_cellSeparatedAt` needed only
> `Force.mem_keepMin_iff` + `Descend.lexLeList_antisymm` + `cellList_nodup` — no new import.
>
> ### ⚠ WHAT IS MEASURED ABOUT CFI + FORCE — read before assuming force already covers CFI
>
> * The CFI **gauge** is consumed by the **twist/gauge harvest** — `kernelSupply` in Lean (`mp7`'s
>   whole gauge in one call, `PerformanceTest` §13) and the **linear oracle** in C# (validated through
>   `CFI(K7)`). That is **consume**, not force.
> * **Force's only measured firing witness in the Lean object is `G8`** (`Regression` §18: root cell
>   8 → 2; §19: flag → answer) — a cubic non-VT graph, **not CFI**.
> * The consume guard is open on **26/28 depth-1 CFI cells** and **shut on both root cells**. So the
>   CFI *residue* is consume's and largely works; the *root's mixed-cell split* is force's and is the
>   unbuilt half.
> * ⚠⚠ **There is NO end-to-end measurement of the Lean object on any CFI graph** — `n = 56` is far
>   outside `#eval` reach (`K₁,₂,₃` at `n = 6` costs 50 s; `t3` at `n = 15` cost 412 s interpreted).
>   Every CFI number on record is component-level or from the C# canonizer.
> * ⚠ **CFI graphs are never rigid**: the cycle-space twists are automorphisms, so
>   `Aut ⊇ Z₂^β`, `β = |E| − |V| + 1 ≥ 1` for any base with a cycle. There is no "rigid CFI" to
>   contrast with — the rigid case is the **multipede**, where the linear oracle's own record says it
>   **flags** (`dim ker = 0`, no twist to construct).
>
> **(i) ✅ DONE — Make the socket disjunctive.** `Select.CellOrbitAt`
> demands the **whole cell** be one orbit, so `SomeCellOrbit`/`ResolvableCellAt` are **consume-only**
> and structurally cannot express *"force splits, consume clears"*. ★ But the proof of
> `cellNarrowC_length_le_one_of_cellOrbitAt` only ever applies its hypothesis to **`keepMin`
> survivors** (`h y (keepMin_subset hy) b hbc`) — so weakening the quantifier from `cellList χ c` to
> `keepMin key adj χ (cellList χ c)` is the **same proof**, strictly weaker, and it covers three
> cases instead of one: the present one (via `keepMin_subset`, nothing regresses); **key-only**
> (`|keepMin| ≤ 1` — the only route that can ever reach a **rigid** cell); and the **mixed** case
> (key cuts between orbits, supply certifies the survivor) — which *is* the CFI story. The
> ingredients exist but are stranded at the node-global object: `KeyComplete.KeySeparatesAt`,
> `forcedSet_single_orbit_of_keySeparatesAt`, `Force.forceBy_singleton_of_separating`, and the
> ceiling theorem (*an equivariant key is constant on orbits* ⟹ `keepMin` is a **union of true
> orbits**). ~10 lines, CFI-free, no numeral moves.
>
> ### ◐ (ii) RAN — `scratchpad/probe_w2_keysplit.py` → `.out` (2026-08-09). ONE HALF SETTLED
>
> **The firing condition, pinned by two facts about the built object.** A cell fires iff
> `((keepMin key …).map (rep V)).dedup` has length ≤ 1, and
> * **(F1)** the key is equivariant ⟹ `keyV` is **constant on Aut-orbits** (`Force.lean` §"THE
>   CEILING") ⟹ `keepMin` is a **union of Aut-orbits**;
> * **(F2)** every harvested generator is `IsColAut`-checked ⟹ `H = ⟨V⟩ ≤ Aut` ⟹ `rep V` **never
>   merges across Aut-orbits**.
>
> ⟹ **the cell fires ⟹ `keepMin` is EXACTLY ONE Aut-orbit block, and the harvest is transitive on
> it.** The probe measures the first conjunct — the key's half, no supply model needed.
>
> | witness | root cells | Aut-blocks (sizes) | `holKeyFast` |
> |---|---|---|---|
> | **CFI cubic m=8 pl / tw** (n=56) | 32, 24 | **3** each — `[12,12,8]` and `[12,6,6]` | **1 signature — argmin = the WHOLE cell** |
> | `mp7` (n=42) | 28, 14 | **1** each | 1 signature (cell is one block — consume's case) |
> | MIXED (n=30) | 4,2,2,4,2,8,4,4 | 2,2,1,2,2,3,2,1 | 1 signature throughout |
> | `G8` (n=8) — **validation** | 8 | 3 — `[4,2,2]` | 1 signature, **keeps 8** |
>
> ★★ **VALIDATED AGAINST SHIPPED LEAN.** `Regression` §18's `#guard` pins `holKeyFast` keeping **all
> 8** of `G8`'s root cell; the model reproduces 8. And the model's built-in self-check — (F1), the key
> must be constant on every Aut-block — **never fired** on any witness.
>
> ### ★★★ AND THE REASON IS STRUCTURAL, NOT INCIDENTAL
>
> `holKeyFast`'s walk is over **cross-cell components** ("copies"), and `walkOk` demands **three
> pairwise-distinct** ones. Measured at the root:
>
> | | colours | cross-components | ⟹ |
> |---|---|---|---|
> | CFI cubic m=8 · `mp7` · MIXED | 2 · 2 · 8 | **1** | **no valid walk exists** ⟹ every `holSig` is the all-1s vector ⟹ **`holKeyFast` is STRUCTURALLY INERT** |
> | `G8` | 1 | 8 (singletons) | walks exist, signatures non-trivial — so the machinery *is* exercised, and still keeps all 8 |
>
> ⟹ **at any node whose cross-cell graph is connected, `holKeyFast` cannot be anything but constant.**
> That is a statement about a shipped component, and it means **the CFI root rests entirely on the
> `orbKeyG guardSupply` tiebreak** — `holKeyFast` contributes nothing there.
>
> ### ▶ WHAT REMAINS, AND IT IS NOW ONE BOOLEAN
>
> `RecordKey.keyV_pairKey_of_guard_shut`: where `orbKeyG`'s guard is shut the second component is the
> constant `[]` and `recordKey` **is** `holKeyFast` verbatim. So:
>
> > **if `CertPath guardSupply` is shut at every vertex of both CFI root cells, then `recordKey` is
> > constant there ⟹ `keepMin` = the whole cell = 3 Aut-blocks ⟹ by (F2) no supply can collapse it
> > ⟹ neither cell fires ⟹ the node stalls ⟹ *the published object provably flags on CFI over a
> > cubic base*.**
>
> That is a theorem-shaped negative and it needs exactly one measurement: the guard's verdict.
> ⚠ **Cost, honestly:** `guardSupply = fold ++ deck ++ deck2 ++ match`, and **no Python model of any
> of those four exists** (the probes model only the *deepen* harvest) — so it is four supply models,
> not an adaptation. The Lean route is blocked differently: `CFI.cfiAdjMatrix` is **`noncomputable`**
> (`Fintype.equivFin`), so `#eval`ing the shipped guard needs an `n = 56` computable fixture built
> first, and `deck2` at that size is untested in the interpreter (the recorded 412 s was at `n = 15`).
> ⚠ Aut-blocks come from `Ctx`/`canon` — sound but possibly incomplete, so they are a *refinement* of
> the true orbits. That direction is the safe one here: a coarser truth only makes "argmin = the whole
> cell over ≥ 2 blocks" easier to satisfy, never harder.
>
> **(ii) ORIGINAL PLAN — the supply half, still open.** At the CFI-over-cubic
> root, report the true-orbit **block sizes** of both root cells and whether `recordSupplyFast`'s
> verified generators are transitive on any single block. Because `keepMin` is a union of true orbits
> and `rep` only merges within supply-orbits: **if no block is a single supply-orbit, no equivariant
> key can rescue that node** — and *"the published object provably flags on CFI over a cubic base"*
> becomes a theorem-shaped negative worth publishing. If some block is, the CFI root is live at the
> published object through (i)'s mixed case, with **no** Track R needed. ⚠ Cost: real but bounded —
> no probe models `recordSupplyFast`'s harvest in Python yet.
>
> **(iii) Only then** decide the Track R question in 3.
>
> ### ▶▶▶ THE TARGET CLAIM — *"the residue will not stall if it contains a linear obstruction"*
> *(assessed 2026-08-09 against source; this is W2's statement in its general form)*
>
> **✅ The predicate already exists and needs no invention.** `ForcingModel adj χ H var gForce` (P2,
> `ForcingModel.lean`) **is** *"this node's obstruction is linear"* — the module's own header says
> *"where it fails, the residue is **non-linear** rigid."* Carrying the bridge as a hypothesis is
> therefore **not a gap; it is the definition of "linear"**. The claim is statable today.
>
> **✅ And the disjunctive socket (`CellResolvedAt`) is exactly its shape** — which retroactively
> makes step (i) necessary rather than convenient. But the natural two-case reading (kernel vs rigid)
> is **wrong**, and the gap is where the measured CFI root lives:
>
> | case | what it is | route | status |
> |---|---|---|---|
> | `dim ker > 0`, cell = **one** Aut-orbit | pure gauge slack | **consume** — `kernelSupply` / `deepenCellSupply` certifies it | ✅ built **and fires** (`mp7` 14/14) |
> | `dim ker = 0` (rigid cell) | no slack | **force** — P3-F₂ uniqueness + canonical RREF ⟹ separating key | ◐ `RigidGen.nodeResolved_compKey_genOfRef` exists — but at `Select.NodeResolved`/`selNode` and at `compKey`, under `hdisc` (the reader discretizes) + `hrigid` |
> | **`dim ker > 0`, cell = SEVERAL Aut-orbits** | gauge slack **and** non-automorphic blocks | **mixed** — key isolates one block, supply certifies it | ❌ **nothing built** |
>
> ⛔⛔ **THE THIRD ROW IS THE CFI-OVER-CUBIC ROOT** — measured: the gauge is non-trivial (so it is
> *not* rigid, and `hrigid` fails) **and** each root cell carries **3 Aut-blocks** (so consume cannot
> take it). It is in **neither** of the two clean branches. Any plan that assumes a kernel/rigid
> dichotomy will miss exactly the node W2 is about.
>
> ### ▶ WHAT WOULD HAVE TO CHANGE, in order
>
> 1. **Nothing in the socket** — `CellResolvedAt` already admits all three rows.
> 2. **Wire a solver key into `recordKey`.** The slot exists (`pairKey`; `keyEquivariant_pairKey` is
>    unconditional and `keepMin_pairKey_subset` guarantees no strength loss). Two real costs: `②`
>    re-bills and **the numerals will move** (`costDeg` is set by `recordKeyBound`, so a new key
>    component changes it — it needs its own `keyCost` bound); and `①` needs its `KeyEquivariant`.
> 3. ★ **That `①` gap is NARROWER than "not built".** The chain is
>    `readEquivariant_readAgg` (unconditional given `FramesEquivariant`) → `RigidRefine.refineBy read`
>    is `RefEquivariant` from `ReadEquivariant` alone → `RigidGen.genEquivariant_genOfRef`. And
>    `framesEquivariant_seedFrames` + `card_seedFrames_le` are **built**. So the frame set already has
>    **equivariance ✅ and poly size ✅**; the single missing property is that it **DISCRETIZES**
>    (Track R P2's *"concrete poly seed + discretizing solve-completion `orderOf`"*). ⚠ Note
>    `refineByFrame` has *unconditional* `RefEquivariant` and provably **cannot** discretize (≤ 2
>    classes/cell — it fails the multipede), so equivariance alone is not the bottleneck: **one named
>    property, one named gap.**
> 4. ✅ **LANDED 2026-08-09 — the layer bridge** (`SelectCell` §9b, 4 decls, axiom-clean). Both rigid
>    firing lemmas end in `Select.nodeResolved_of_cellResolved hnd (Or.inr …)`, whose right disjunct
>    is exactly *"the key is injective on `branches χ`"*, and `branches χ` **is** `cellList χ c` at
>    the target colour — so the rigid conclusion reaches the cell-indexed socket by plumbing alone:
>    `cellSeparatedAt_of_branchSeparation` · **`someCellResolved_of_branchSeparation`** ·
>    `nodeResolvedC_of_branchSeparation` · **`handledSC_of_branchSeparation`** (for **every** supply).
>    ⚠ Stated **generically, with no rigid-stack import** — `SelectCell` is upstream of the published
>    object and pulling `Rigid*` into its graph would change the deliverable's imports for no proof
>    benefit. Instantiating at `compKey` is a one-liner wherever the solver key is wired.
> 5. **The third row is mathematics, not plumbing** — but ★ **it is not uncharted**: the project
>    already built the instrument. `structRead`'s single-`ord` path is *"whole-node-rigid = the
>    `ker = 0` anchor, **superseded by `readAgg` for the mixed residue**"*, and
>    `readEquivariant_readAgg` is unconditional from `FramesEquivariant`. So item 5 **is** the
>    recorded **P3 `AggFaithful (seedFrames …)` per-family** obligation, stated at a concrete frame
>    set. ⛔ **Do not try to instantiate `nodeResolved_compKey_genOfRef`'s `hrigid` at a CFI root** —
>    it is *measurably false* there (gauge non-trivial ⟹ not rigid; 3 Aut-blocks per cell). P3-F₂'s
>    **uniqueness** needs `dim ker = 0` and a CFI root has `dim ker > 0`; what stays canonical there
>    is the **RREF of the row space**, which is what `readAgg` reads.
>
> ### ★ AND THE DISJUNCTION WAS NOT NEW — the cell-indexed rewrite had DROPPED it
>
> `Cost.CellResolved key S adj χ := Consume.CellIsOrbit S adj χ ∨ (∀ u w ∈ branches χ, keyV u = keyV w
> → u = w)` has existed all along at the **node-global** layer, and its own header says *"a graph may
> be handled by consume at one cell and by force at the next — that is exactly what the **mixed**
> resolver is for."* The cell-indexed rewrite carried over only the **left** disjunct
> (`CellOrbitAt`), which is why the socket came out consume-only.
>
> ⟹ §9a/§9b **restore** the disjunction at the cell-indexed layer — and go past it: `Cost.CellResolved`'s
> two disjuncts are *"the whole cell is one orbit"* and *"the key separates the whole cell"*, and
> **neither covers the mixed case**, where `keepMin` is a proper sub-union that the supply then
> collapses. `CellResolvedAt` is stated on the survivors, so it covers all three. That is strictly
> stronger than the node-global predicate, not a port of it.
>
> ### ⛔⛔⛔ ITEM 3 — PROBED 2026-08-09 (`probe_w2_linear.py` → `.out`), AND IT INVERTS THE TARGET
>
> ⛔ **First, a correction to my own item-3 scoping.** *"`framesEquivariant_seedFrames` +
> `card_seedFrames_le` are built ⟹ equivariance ✅ + poly ✅, missing only discretizing"* is **FALSE**,
> and `RigidRefine` §9F says so at source: at a gauge colour-aut, `FramesEquivariant` forces the frame
> set to be closed under **left multiplication by the whole gauge group**, left-mult is a **free**
> action, so `|frames| ≥ |G| = 2^β`. **No poly equivariant full-order frame set exists on a gauged
> input — the exponential is forced by the TYPE.** `seedFrames` is **retired** and
> `OrderOfEquivariant` is **target-vacuous** (it holds only on purely rigid inputs). Equivariance and
> poly size are *jointly unattainable* there; "discretizing" was never the missing third.
>
> ### ★★★★ AND THEN THE PROBE INVERTED THE PREMISE: **a gauge can never make a cell mixed**
>
> The gauge (F₂ cycle space) is a **subgroup of `Aut`**. Subgroups only ever *merge* vertices — they
> never create mixedness. Mixedness is several `Aut`-orbits, i.e. the **absence** of automorphisms.
> So *"a cell mixed due to a linear (gauge) obstruction"* is close to a contradiction in terms.
>
> Measured exactly (no search, no budget; every gauge element **verified edge-by-edge** first):
>
> | witness | cell | gauge-orbits | `Aut`-orbits | some `Aut`-block a single gauge-orbit? |
> |---|---|---|---|---|
> | CFI cubic m=8 pl / tw | gadgets 32 | **8** × 4 | **3** — `[12,12,8]` | ⛔ **no** |
> | ” | wires 24 | **12** × 2 | **3** — `[12,6,6]` | ⛔ **no** |
> | CFI over `K₄` (edge-transitive base) | gadgets 16 | **4** × 4 | **1** — `[16]` | ⛔ **no** |
> | CFI over `C₆` | gadgets 24 | **12** × 2 | **1** — `[24]` | ⛔ **no** |
>
> By (F1) the key is constant on `Aut`-orbits, so it **cannot cut inside a block**; by (F2) `rep`
> merges only within harvest-orbits. So the surviving representative count is at least
> `|block| / |gauge-orbit| ≥ 2` **at every cell of every witness**. ⟹ **no key whatsoever — perfect,
> solve-derived, or otherwise — can make a CFI root cell fire on the gauge.** That is a *counting
> fact*, not a difficulty, and it is not what a linear solver is short of.
>
> ★ **What Aut does beyond the gauge is BASE automorphism structure**: on `K₄` (edge-transitive base)
> `Aut` merges all 4 gauge-orbits into **one** block; on the `m=8` cubic, 8 into 3. The linear
> layer sees none of it.
>
> ⚠⚠ **SCOPE CORRECTION (2026-08-10) — the sentence above says *"on the ~~asymmetric~~ cubic"*, and
> that base is NOT asymmetric: the probe prints `|Aut(base)| = 12` for `cubic(8, seed=8)`, `24` for
> `K₄`, `12` for `C₆`. **All four witnesses have a symmetric base; no asymmetric base was ever run.**
> The bound `reps ≥ |block|/|gauge-orbit| ≥ 2` presumes the supply-orbits **are** the gauge-orbits, so
> what is measured is the probe's own hedged wording — *"cannot fire **on the gauge**"* — not *"no key
> of any kind can fire it"*. Over an asymmetric base `Aut(CFI(G))` **is** the gauge, every `Aut`-block
> is a single gauge-orbit, and the counting bound disappears; firing there becomes a question of
> whether the key can separate gauge-orbits (i.e. base edge classes), which is open, not closed.
> ⟹ **The load-bearing half of the retarget survives untouched** (a gauge is a subgroup of `Aut`, so
> it can never *create* mixedness, and the residual mixing is base structure). What does **not**
> survive is the stronger reading that CFI is unreachable for every key.
>
> ⟹ ⛔⛔ **CFI-over-cubic is NOT an instance of the target claim.** Its CFI part — the gauge — is
> exactly what `kernelSupply` already consumes; what is left mixed is the **base graph**, which is
> the base's problem. That is precisely the design's own sentence: *"families like CFI apply a
> difficult residue over the top of an arbitrary graph; it can handle this residue but then hands you
> back the original graph."*
>
> ### ✅✅✅ ITEM 3b — CFI OVER AN **ASYMMETRIC** BASE (`probe_w2_asymbase.py` → `.out`, 2026-08-10)

**The item-3a bound is an artifact of base symmetry, and the layer theorem is measured true.** Same
encoding, same edge-by-edge gauge verification, plus an **exact** `Aut(base)` by backtracking and a
**descent walk** (⚠ root-only is not a pass — every non-singleton cell is re-measured at each reached
node, with the gauge filtered to the elements that preserve χ).

| base | `\|Aut(base)\|` | base 1-WL | root cells | descent, 3 levels past the root |
|---|---|---|---|---|
| `K₄` (control) | 24 | coarse | ⛔ 2 blocked — reproduces item 3a | ⛔ blocked at **all 4** levels |
| asym `m=7`, non-regular | **1** | **discrete** | ✅ **21/21** single gauge-orbit | ✅ **21 / 20 / 21 / 18**, all levels |
| asym `m=8`, non-regular | **1** | **discrete** | ✅ **26/26** single gauge-orbit | — |
| **Frucht** (cubic, asym) | **1** | coarse | ◐ **12 blocks = 12 gauge-orbits**, 18 = 18 | ◐/✅, **never blocked** |

⟹ Three regimes, and only the first is closed:

1. **Base has automorphisms** ⟹ `Aut`-block ⊋ gauge-orbit ⟹ ⛔ **no key can fire** (item 3a, correct).
2. **Base asymmetric but 1-WL coarse** (Frucht) ⟹ `Aut`-block **=** gauge-orbit **exactly**, so the
   `reps ≥ 2` bound is **gone**; firing is a pure **key** question — separate the 12 blocks, i.e.
   *separate the base's vertices*. **Open, not closed.**
3. **Base 1-WL discrete** ⟹ **every** non-singleton cell is a **single** gauge-orbit, at the root and
   at every reached node ⟹ `Select.CellOrbitAt` holds for the gauge ⟹ ✅ **the node fires with the
   supply that already ships** — `Kernel.kernelSupply` **is inside `RecordCost.recordSupplyFast`**
   ([RecordCost.lean:175](../GraphCanonizationProofs/ChainDescent/RecordCost.lean#L175)), and
   `Select.CellOrbitAt` carries **no guard** (no `GoodCell`, no `CertPath`).

★★★ **That is the user's sentence, measured:** *solve the CFI part, hand back the base.* Regime 3 is
the CFI layer being peeled; regimes 1–2 are the base graph's own difficulty, arriving unchanged.

### ▶▶ THE LAYER THEOREM — how it factors, and what lands

✅ **The socket and the instance kit are BUILT** (`SelectCell` §9c, 2026-08-10, axiom-clean):
`wordReach_mono` · **`cellOrbitAt_of_transitiveGens`** · `someCellResolved_of_transitiveGens` ·
**`handledSC_of_transitiveGens`**. A family now discharges its consume half by exhibiting one list `V`
with three properties — **emitted** (`V ⊆ gens (S c)`), **sound** (`IsColAut`), **transitive** on the
cell. `key` is arbitrary: **no key work at all**, which is exactly what regime 3 says.

For CFI take `V` = the F₂ cycle-space flips. The three obligations then are:

| | obligation | status |
|---|---|---|
| **sound** | the flips are colour-automorphisms | ✅ `CFI.cfiFlipAut` (built, stage 3 §15) |
| **transitive** | the gauge is transitive on each cell of a resolved base | ✅ **measured exact**, all cells, all reached nodes (above). ⚠ In Lean it also needs the *cell structure* of `Refine.encodeFreeFast` on a CFI graph — i.e. what 1-WL does there — which is **not** available and `cfiAdjMatrix` is `noncomputable`, so it cannot be `#eval`ed either. ⟹ carry the cell characterization as a hypothesis, or state it for an abstract "resolved base" colouring |
| **emitted** | `kernelSupply`'s harvest emits those flips | ⛔ **`KernelSupply.lean` is a definition module with ZERO theorems.** This is algorithm verification (rails → patterns → localRows → F₂ nullspace → `flipFunK`) and it is **not** a wind-down-sized proof |

⟹ **Honest verdict: the CFI layer theorem does not land as a machine-checked family theorem here.**
What lands — and did — is the socket + instance kit, so the theorem is *one named hypothesis* away and
nobody re-derives the plumbing. Carry **emitted** the way `ForcingModel.bridge` is carried (a measured,
per-family algorithmic fact); the probe is its non-vacuity evidence.

⚠⚠ **AND A TRAP FOUND WHILE PLANNING IT — narrowing the residue to `SomeCellResolved` is NOT small.**
Option **A** picked `ResolvableCellAt` precisely because it is *unsatisfiable on a rigid graph*, which
makes `unhandledResidue_nonvacuous` easy (`G8`, `rand multipede` are residual by construction).
`SomeCellResolved` is **strictly weaker**, so `¬ ∀ SomeCellResolved` is *harder* to witness — and the
object is measured to **answer** on `K₃ ⊔ C₄`, the current witness, which is evidence that
`SomeCellResolved` **holds** there. ⟹ swapping the residue to the disjunctive predicate would put
`unhandledResidue_nonvacuous` back in play. Do not treat it as a re-point.

### ⟹ THE TARGET CLAIM'S REAL HOME IS THE **RIGID** CASE (`dim ker = 0`)
>
> There: no gauge, `Aut` trivial, every cell fully mixed, and the F₂ **forced values** genuinely
> separate. And every hypothesis flips from obstacle to satisfied:
>
> | | at a CFI root (`dim ker > 0`) | at a rigid node (`dim ker = 0`) |
> |---|---|---|
> | consume | the gauge is *inside* `Aut` — merges, never separates | nothing to certify (correctly) |
> | `nodeResolved_compKey_genOfRef`'s `hrigid` | **false** (measured) | **satisfied — it is the hypothesis** |
> | an equivariant order perm | provably does **not** exist (the `2^β` bound) | **exists** — the recorded *"only on rigid inputs"* is a **positive** here |
> | `RigidSolveF2` uniqueness | inapplicable (`dim ker > 0`) | **applies** |
>
> ### ▶▶ STEPS TO *"the resolver fires somewhere when a cell is mixed by a linear obstruction"*
>
> * **S1 — state the predicate.** *"Mixed by a linear obstruction"* = the `ForcingModel` bridge holds
>   **and** the system is rigid on that cell (`dim ker = 0`). Both halves exist: `ForcingModel` (P2)
>   and `RigidSolveF2`'s rigidity. ⚠ It must **not** be read as *"a gauge is present"* — probed above,
>   that reading is empty.
> * **S2 — the route is already plumbed.** `RigidGen.nodeResolved_compKey_genOfRef` gives
>   `NodeResolved` from `hdisc` + `hrigid`, and **item 4** (`SelectCell` §9b,
>   `someCellResolved_of_branchSeparation`) lands it at the **published** object. Nothing new here.
> * **S3 — the one real gap, now much narrower: the discretizing reader IN THE RIGID REGIME.**
>   `hdisc` needs the reader to discretize; `structRead`'s equivariant order exists *exactly* on rigid
>   inputs. This is **not** the retired `seedFrames` problem, which had to work on gauged inputs where
>   it is type-impossible. **This is item 3, correctly scoped.**
> * **S4 — wire (item 2), last**, unchanged: `②` re-bills, numerals move, `①` rides S3.
> * **⚠ Scope sentence to publish with it:** the theorem is *"no stall at a node whose obstruction is
>   linear **and rigid**"*. CFI roots over a **symmetric** base are not covered and cannot be by any
>   key; over an asymmetric base see item 3b, where the counting bound does not apply.
>
> ### ⛔⛔⛔ S3 AS WRITTEN ABOVE IS MIS-AIMED — CORRECTED AGAINST SOURCE 2026-08-10
>
> Read this before starting S3. `RigidRefine.lean`'s own header now carries the same banner.
>
> 1. **⛔ `OrdEquivariant` is not *"satisfied on rigid inputs"* — it is UNSATISFIABLE for `n ≥ 2`.**
>    It quantifies over **all** `adj χ` ([RigidRefine.lean:534](../GraphCanonizationProofs/ChainDescent/RigidRefine.lean#L534)).
>    At the empty graph with the constant colouring every `σ` is a colour-aut, so the definition forces
>    `ord adj χ = σ * ord adj χ`, i.e. `σ = 1`. §9F's milder *"holds only on purely rigid inputs"* is
>    too generous: a `Force.Key` must be **one global function**, so there is no "restrict to the rigid
>    regime" instantiation. ⟹ `readEquivariant_structRead`, `keyEquivariant_compKey_structRead`,
>    `nodeResolved_compKey_structRead`, `keyEquivariant_compKey_skStruct*` are correct lemmas with an
>    **undischargeable** hypothesis. S3's sentence *"`structRead`'s order exists exactly on rigid
>    inputs"* is the `seedFrames` mistake repeated.
> 2. **The live interface is §9F `readAggB`, and its `①` is ALREADY CLOSED, poly, unconditionally** —
>    `keyEquivariant_compKey_readAggB_pin` needs only `refExtractEquivariant_adj`, which is **proved**
>    (step 4). Nothing about *discretizing* is required: `nodeResolved_compKey_readAggB_faithful` asks
>    for no global discreteness. So S3's `hdisc`-shaped target is strictly **harder** than what the
>    stack consumes. The open wall is **`AggFaithfulB`, per-family**.
> 3. **⚠⚠ A HARD CAP ON THE ONLY CONCRETE `baseRead`.** `baseReadPin = encOpt (forcedVal …)` and
>    `encOpt_lt_three` bounds its codomain by `{0,1,2}`; `readAggB` is `encode ∘ sort` of the **image**
>    over the frames, so it takes **at most 8 distinct values on any input, for any frame family
>    whatsoever**. By pigeonhole `AggFaithfulB` is **provably false** at any node with ≥ 9 pairwise
>    non-automorphic branches — every rigid multipede cell of interest. ⟹ §9F's own
>    *"▶ NEXT: a RICH pinning family"* **cannot be satisfied by enlarging `frames`**; richness must come
>    from the **READ** (e.g. pair each per-frame read with an invariant *of the frame*, so the aggregate
>    encodes `frame ↦ value` instead of collapsing it).
> 4. **Every firing lemma in the stack still needs whole-branch-cell `hrigid`.** "Mixed-native" in
>    those module docs means the *reader* does not over-separate gauge pairs; it does **not** mean the
>    firing lemma tolerates a gauge inside the target cell. Row 3 of the case table stands.
> 5. **⚠ The whole rigid reader stack is `noncomputable`** (`forcedVal` decides `rowspace` membership;
>    `readAgg`/`readAggB`/`genOfRef` inherit it). **S4 would cost the published object its
>    executability** — a live property (`#eval` answers on `K₂`/`C₅`/`K₁,₂,₃`/`K₃⊔C₄`). S4's cost list
>    (*"`②` re-bills, numerals move"*) omits this.
> 6. **Calibration, not a refutation** (the *"X ⟹ GI∈P"* argument stays banned): an order-free poly
>    coordinate-separating read for an F₂ code **is** permutation code equivalence, which GI reduces to.
>    So `AggFaithfulB` must be proved **per-family** — as its own docstring already says — and any plan
>    that reads as *"build a general discretizing reader"* is mis-sized.
>
> ### ▶▶ ORDERING: **4 → 3 → 5 → 2** (assessed 2026-08-09)
>
> * **4 first** — done; small, no dependencies, and it makes every later force-side result land at
>   the published object instead of at `selNode`.
> * **3 before 5** — item 5's hypothesis `AggFaithful (seedFrames …)` is stated *at a concrete frame
>   set*, and item 3 is what produces one. `framesEquivariant_seedFrames` + `card_seedFrames_le` give
>   equivariance ✅ and poly size ✅ already; 3 supplies **discretizing**, and only then can 5 be
>   stated at all.
> * **⚠ 2 LAST, not second.** Wiring the solver key changes the **published object**: `②` re-bills
>   and **the pinned numerals move** (`costDeg` is set by `recordKeyBound`, so a new component needs
>   its own `keyCost` bound), and `①` acquires a `KeyEquivariant` obligation that **cannot be
>   discharged until 3 lands**. Wiring first would put an undischargeable obligation into the
>   deliverable and move `costConst`/`costDeg` for nothing. Build the capability, then wire it once
>   it pays.
>
> ⟹ **the claim is reachable in shape, and its force half bottoms out on exactly one unbuilt
> property** (a discretizing equivariant poly frame set = Track R P2). That is the same conclusion as
> before, now named precisely rather than as "Track R".
>
> ⚠ The two-part **anatomy of the CFI obstruction** to carry into any statement: the **gauge**
> (F₂ cycle space) acts by genuine automorphisms ⟹ it is *symmetry*, consume's job, and
> `kernelSupply` already does it (measured, `mp7` 28 → 7); the **mixed-cell split** at the gadget
> cells is force's job and is the unbuilt half. Do not write "the CFI obstruction" as one thing.

> ⚠⚠ **SCOPE CORRECTION (user, 2026-08-04) — state the target as PROGRESS, not completion.**
> W2 reaches at best ***"does not stall on a CFI residue"***. `CFI(unhandled residue)` still reaches
> the unhandled residue once the CFI layer is peeled, so no CFI theorem can claim full completion.
> The honest target is that the canonizer **steps forward whenever the residue is of that type**.
> ★ **Contrast with W1, and this is the structural reason W1 was cheap:** peeling a Tinhofer layer
> leaves a Tinhofer graph — the class is **step-closed** (`TwinFamily.StepClosed`, now the socket's
> hypothesis). CFI is *not* step-closed in that sense; its layer sits on top of an arbitrary base.
> ⟹ W2 must be stated against the socket as a **one-layer progress** lemma, not as a class membership.

The higher-value of the two, because it is the claim that distinguishes the artifact:
**provably polynomial on a family where every practical IR solver is provably exponential**
(Neuen–Schweitzer, STOC 2018). `kernelSupply` already consumes the whole gauge in one call
on `mp7` (Fano multipede, n = 42, measured, `PerformanceTest` §13) — the mechanism works;
what is missing is the theorem that it *always* certifies the branch cell on the family.

> ## ⛔⛔ SCOPE CORRECTION #2 (2026-08-08) — **THE RECORDED ROUTE POINTS AT THE WRONG OBJECT**
>
> ~~Route: `theorem_1_HOR_cfi_oddDeg` → `CascadeOracle` → `handled_of_seal`.~~ **Do not start there.**
> That route was written before the published object existed and it lands at a *different* canonizer,
> which the standing steer forbids:
>
> | | recorded route | the published object |
> |---|---|---|
> | supply | `deepMatchSupply k` | `RecordDeepenCell.recordSupplyDeepenC` = `fun c => recordSupplyFast ++ deepenCellSupply c` |
> | resolver | blind `Descend` | `Select.selNodeLazyHC` (cell-indexed, lazily billed, key shared) |
> | predicate | `Residue.Handled` | **`Select.HandledSC`** |
>
> `HandledBridge.handled_of_seal` yields `Residue.Handled key (deepMatchSupply k)`, and
> **`deepMatchSupply` is not a factor of `recordSupplyFast`** (which is
> `foldSupplyFast ++ deckSupply ++ deck2Supply ++ kernelSupply`). So the conclusion cannot be
> rewritten onto `canonForm?`, and W2 done that way would be a **second-object discharge** — the
> thing this project reverted once already.
>
> ⚠ **This is the same trap that cost `③` ~150 lines** (§2a's general rule: *a new `NodeRes` inherits
> everything `Select.lean` proves generically and nothing `SelectNode.lean` proves specifically*).
> `HandledSC` is a **third** layer on top of that: it is `SelectCell`-specific, so neither
> `Residue.Handled` nor `Select.HandledS` rewrites onto it. Check which layer a theorem is on before
> calling it reusable.
>
> ### ⛔ AND THE ROUTE I FIRST RECORDED WAS ALSO WRONG — `kernelSupply` CANNOT CARRY IT
>
> ~~"Use `kernelSupply`, already the fourth factor of `recordSupplyFast` and the component measured to
> consume the CFI gauge; step 1 is `CellIsOrbit Kernel.kernelSupply adj χ` at a reached CFI node."~~
> **`CellIsOrbit kernelSupply` is measurably FALSE where it matters.** `KernelSupply.lean`'s own
> header records the `mp7` measurement: the root gadget cell goes **28 → 7**, i.e. the gauge is fully
> certified and **the Z₇ translations are honestly left standing** — 7 orbits, not 1. `kernelSupply`
> is a *gauge* constructor; base symmetry is what `deepenSupply` was built for
> (`chain-descent-deepen-supply.md`: "the constructor for base symmetry — what survives after
> `kernelSupply` certifies the gauge"). Caught while scoping, before any CFI Lean was written.
>
> ### ✅ STAGES 1–2 ARE BUILT (2026-08-08, gate exit 0 / 224 s / 119 modules, axiom-clean)
>
> The route that does land goes through **`deepenCellSupply` + its per-cell guard**, and it needed
> two sockets first, both of which are now in the gate:
>
> | stage | where | what |
> |---|---|---|
> | **1 — the resolver socket** | `SelectCell.lean` §9 | `CellOrbitAt` (the per-cell orbit condition at an **arbitrary** cell) · `cellNarrowC_length_le_one_of_cellOrbitAt` (one cell being one orbit of its own generators makes *that* cell fire — no key hypothesis, no `targetColour`) · `SomeCellOrbit` · **`handledSC_of_someCellOrbit`** · `someCellOrbit_of_targetCellIsOrbit` |
> | **2 — the named obligation** | `DeepenCell.lean` §9 + `RecordDeepenCell.lean` §3a | `Deepen.cellOrbitAt_deepenCellSupply` / `cellOrbitAt_append_right` · **`RecordDeepenCell.ResolvableCellAt`** · `handledSC_of_resolvableCells` · `not_all_resolvable_of_flag` · `resolvableCellAt_of_tinhoferGraph` |
>
> **`ResolvableCellAt adj χ := ∃ c ∈ nonSingletonColours χ, GoodCell adj χ c ∧ CellSingleOrbit adj χ c`**
> — a statement about `(adj, χ)` alone: no supply, no key, no resolver. `handledSC_of_resolvableCells`
> turns *"that holds at every reached non-discrete node"* into `HandledSC` at the **published**
> object, hence "never flags". ★ `handledSC_of_tinhoferGraph` is now **derived through it**
> (`resolvableCellAt_of_tinhoferGraph`), so the containment `TinhoferGraph ⊆ resolvable-everywhere`
> is machine-checked and nothing regressed.
>
> ⚠ **It is the supply-side half only.** A cell can also fire because the **key** separates it —
> `cellNarrowC` applies `keepMin key` first. `ResolvableCellAt` is sufficient, never necessary.
>
> ### ★★★ STAGE 0 MEASURED (`scratchpad/probe_w2_resolvable.py` → `probe_w2_resolvable.out`)
>
> BFS depth 1, ≤2 members/node, leafcap 200 000. `GoodCell` is `probe_offbranch5.guard_cell` verbatim
> (`None` = budgeted out, never counted as a pass); `CellSingleOrbit` is union-find over the
> generators `Ctx`/`canon` discovers — sound, so **single-orbit = YES is a positive certificate** and
> NO is only a failure to certify (⛔ never `probe_orbit_oracle`).
>
> | witness | n | cells | good | single | resolvable | all nodes? | target always? |
> |---|---|---|---|---|---|---|---|
> | CFI cubic m=8 pl | 56 | 28 | 26 | 26 | 26 | **N** (root) | N |
> | CFI cubic m=8 tw | 56 | 28 | 26 | 26 | 26 | **N** (root) | N |
> | **mp7 Fano multipede** | 42 | 14 | 14 | 14 | **14** | **Y** | Y |
> | MIXED multipede | 30 | 24 | 18 | 18 | 18 | **Y** | **N** ★ |
> | circ(5) multipede | 30 | 26 | 22 | 22 | 22 | N (root) | N |
> | rand multipede V=6 W=5 | 34 | 8 | 0 | 0 | 0 | N | N |
> | G8 cubic non-VT | 8 | 1 | 0 | 0 | 0 | N | N |
> | S(K5) · S(Petersen) | 15 · 25 | 10 · 14 | all | all | all | Y | Y |
>
> **★ Q2 ANSWERED — THE STAGE-1 WIDENING IS LOAD-BEARING, not cosmetic.** At the **MIXED multipede
> root** the *target* cell (colour 0, size 4) has the guard **shut**, while cells 2 and 7 have it
> **open and are certified single orbits**. Under the old target-cell-only route that node is not
> provably handled; under `SomeCellOrbit` it is. Positive certificates on both halves.
>
> **⛔⛔ Q1 ANSWERED, AND IT IS A NEGATIVE — `ResolvableCellAt` FAILS AT THE CFI ROOT.** Both root
> cells of CFI-over-cubic m=8 (sizes 32 and 24, plain *and* twisted) have the per-cell guard
> **genuinely shut**, and the certified orbit partition splits each into **3 blocks**. ⚠ Re-verified
> at budget **200 000** (667× the sweep's) to rule out a budget artifact: still `False`, not `None`.
> ★ But **26/26 depth-1 cells are good ∧ single**. ⟹ **the CFI *residue* is resolvable; the CFI
> *root* is not**, and the failure is at exactly one node.
>
> ### ⟹ WHAT W2 CAN AND CANNOT BE, RESTATED ON THE MEASUREMENT
>
> 1. **The consume side cannot take the CFI-over-cubic root — WHICH IS THE DESIGN, NOT A DEFECT.**
>    With the guard shut, `deepenCellSupply` emits `[]`; the root cells are **mixed-orbit**, where
>    `forceBy_no_narrowing_on_orbit` says force fires and consume must not. ⛔ ~~That is a
>    rigid/force-side obligation (Track R, §3 suspended) … **W2 is not a consume-side item at the
>    root.**~~ **STRUCK 2026-08-08 (later)** — force *is* where CFI is supposed to land; see the
>    re-affirmation block. ⚠ And the measurement is narrower than this sentence: the probe modelled
>    only `GoodCell` + true orbits, **not** `recordKey` and **not** `recordSupplyFast` (which
>    contains `kernelSupply`, the CFI-gauge component). `G8` is the standing counterexample to the
>    inference — `ResolvableCellAt` = 0/1 there and the object still goes **flag → answer** under
>    `recordKey` (`Regression` §19). *"The published object cannot take the CFI root"* is **not**
>    established; *"`ResolvableCellAt` fails there"* is.
> 2. ⛔ ~~**There IS a reachable positive target: `mp7`, the Fano multipede** … **W2's first Lean
>    target should be the multipede family at `mp7`'s shape, not CFI-over-cubic.**~~ **RETRACTED
>    2026-08-08 (later)** — a family-membership retarget is the move SCOPE CORRECTION #1 forbids, and
>    `mp7` (`|Aut| = 1344`, gauge `Z₂³`) is the **non-rigid** multipede, not the Neuen–Schweitzer
>    family. See the re-affirmation block, consequence 2.
> 3. **The class is proper in both directions** — `rand multipede V=6 W=5` (0/8 cells) and `G8` (0/1)
>    have no resolvable cell at all, so `ResolvableCellAt` is neither vacuous nor trivial.
> 4. ⚠ Depth 1, ≤2 members/node. A family-level claim needs every reached node; this is a
>    feasibility read, not a proof, and the standing "root-only is not a pass" caveat applies in
>    reverse here — it was the **root** that failed.
>
> ### ⚠ AND RESTATE THE PAYOFF BEFORE SPENDING THE BOX
>
> `②` is **already unconditional on CFI graphs** — `descentCostSC_recordDeepen_monomial` has no
> hypothesis and no flag disjunct, so "no exponential blow-up on CFI" is *already a theorem*. What W2
> buys is that the object **answers** there, i.e. it narrows `③`. And because a CFI graph is already
> `¬ TinhoferGraph`, today's `③` is **vacuously true** on it — so W2 is not an added `Handled`
> population, it is a **strengthening of the residue predicate**:
> `¬ TinhoferGraph` → `¬ TinhoferGraph ∧ ¬ (CFI-handled)`. ⛔ Do **not** add that second conjunct as
> an `opaque` atom (§2a: an opaque disjunct re-breaks `unhandledResidue_nonvacuous`'s handled half);
> it must be a definition backed by a real population.
>
> ✅ **That definition now exists and is not opaque**: `RecordDeepenCell.ResolvableCellAt`, with
> `not_all_resolvable_of_flag` as its `③`. The residue it names — *"some reached non-discrete
> colouring has **no** good-anchored single-orbit cell"* — is strictly narrower than `¬ Tinhofer`,
> is a statement about the graph alone, and is **measured non-vacuous in both directions** (`mp7`
> resolvable everywhere; `rand multipede V=6 W=5` and `G8` nowhere). Wiring it into
> `Publication.UnhandledResidue` is a live option that needs **no new mathematics** — but read
> point 1 above first: it does **not** capture CFI-over-cubic, whose root is a force-side node.

### W3 — extraction candidates *(box: 1 week, survey then decide)*
Material that stands alone, independent of the canonizer's fate. Assess each for whether it
is genuinely absent from Mathlib before investing:

- **Stabilizer chain / Schreier–Sims abstract layer** (`Cascade.lean` "Part A",
  `chain-descent-schreier-sims.md` §7) — `StabilizerAt` as a Mathlib `Subgroup`, the
  per-level orbit–stabilizer order recursion, and `order = ∏ basic-orbit sizes` over a base
  sequence. Landed and axiom-clean. Mathlib has no BSGS; this is the strongest candidate.
  (A4, the concrete computable BSGS, is *not* done and is not in scope.)
- **Coherent-configuration round barrier** — `CaoRound.round1_barrier` +
  `round2_barrier_real`: separation cannot occur before round 3, unconditional, from the CC
  axioms alone. Small, self-contained, possibly already known — check the literature before
  claiming it.
- **F₂ linear-algebra layer** — `KernelGauss` RREF correctness, `KernelFlip` composition.
  Check Mathlib coverage first; likely subsumed.

### W4 — write-up decision *(box: 1 week)*
Target venue **CPP or ITP**, framed as *a machine-checked individualization–refinement
canonizer carrying its own correctness and cost bound*. Prior art is certificate checking
(McKay–Piperno reformulated as an independently-verifiable proof system), not a verified
algorithm — that gap is real.

**The paper must state, not bury:**
1. the cost bound is over a **declared operation count** ([`CostModel.lean`](../GraphCanonizationProofs/ChainDescent/CostModel.lean)),
   with no theorem linking it to Lean's evaluation;
2. the 8 citation axioms in `Publication.lean`;
3. ⛔ ~~the residue is non-empty and **the canonizer flags on most interesting inputs**.~~
   **CORRECTED 2026-08-08 (user) — the struck wording is FALSE and must not be published.**
   The residue *predicate* is non-empty (`unhandledResidue_nonvacuous`), but the object does **not**
   flag on the interesting inputs: measured, `canonForm?` **answers** on `K₂`, `C₅`, `K₁,₂,₃` and on
   `K₃ ⊔ C₄` — the residual witness itself — and the recorded 7/7 sweep found no flag either. The
   accurate sentence is ***"the canonizer has not yet been proven on most interesting inputs."***
   ★ **This is by design, not a defect: the design is free to be stronger than what is proved, and
   proving that it is strong is the entire point of `③`.** A flag is a statement about the *proof's*
   reach, never about the input's hardness.
   ⚠ Known flagging witness (user, 2026-08-08, not yet reproduced in Lean): a **multipede the rigid
   handler cannot peel**, which therefore fails **at the root**. Worth landing as a `#eval` witness
   before W4 quotes the flag semantics, so the flag branch is exhibited and not merely defined.

Go/no-go: **the paper needs at least one of W1/W2 to have landed.** Without a named family,
the claim is "correct and never exponential, answers on nothing in particular" — true, and
not enough.

> ## ✅ GO — the gate is MET (2026-08-04). W1 landed; W2 is no longer a prerequisite.
>
> The claim the paper can now make: *a machine-checked IR canonizer carrying its own correctness, its
> own cost bound, **and its own coverage** — where coverage provably includes the literature's Tinhofer
> class, and the flag is evidence about the input* (`not_tinhoferGraph_of_flagS`).
>
> **Add to the "must state, not bury" list above (items 4–7), all of them load-bearing:**
> 4. ~~**Coverage is `answers`, not `canonizes`, outside the twin sub-case.**~~ **SUPERSEDED
>    2026-08-04 by `RestrictedTransport.lean`: Tinhofer graphs are CANONIZED** (sound ∧ complete on the
>    class ∧ never flags ∧ explicit polynomial), via `forceThenPick` with no supply at all. What must
>    still be stated is the *shape* of that `①`: iso-invariance is proved **on the class**
>    (`isoInvariantOn`), not as the global `CanonSpec.IsoInvariantOpt` — the paper must say that
>    completeness is claimed for pairs whose left input is Tinhofer, and why (the spine is relativized
>    on two axes: Tinhofer graphs, and *reachable* colourings).
> 5. **The `almost all graphs` claim is refinement's, not the resolvers'.** On a root-discrete graph
>    `HandledS` is vacuous — no reached non-discrete node — so Babai–Erdős–Selkow buys breadth of the
>    *answering* claim and nothing about the architecture.
> 6. **`IsColAut adj P_F = Aut_F` is prose, not a theorem** — the identification with AKRV's pointwise
>    stabilizer, on which the whole "these are the Tinhofer graphs" sentence rests. Not an `axiom`;
>    nothing in Lean depends on it; the English does.
> 7. **None of this is new mathematics** and the framing must not imply otherwise — the class is
>    known-easy (§1). The contribution is the *verified artifact and its formal coverage*.
> 8. **(added 2026-08-04, later) Say which object each claim is about.** See the object table in §2a —
>    the headline coverage claim is at **`forceThenPick holKeyFast`**, which is *not* `Publication.lean`'s
>    object. A referee will check that coverage and correctness are claimed for the same canonizer, so
>    either point `Publication` here or state plainly that the coverage theorem is about a second,
>    simpler object. **`orbKey` must not appear in any published statement — it is `noncomputable`.**
> 9. **`②` rides a declared flat charge** (`holKeyFast`'s `n⁵`) — an argued over-estimate, not a derived
>    bound. Item 1 already owes this for the cost model generally; say it where the coverage theorem is
>    stated. (The `forceThenPick` route dropped `deepenSupply`'s flat `n⁶`, so this is now the only one.)
> 10. **The `forceThenPick` soundness argument turns on a vacuity, and the file next door warns against a
>    vacuity.** `KeySeparatesAt` is satisfied at a Schurian node because there is nothing to separate;
>    `ForcePick`'s header warns about it being satisfied because a guarded key *deferred*. The paper
>    should draw that distinction explicitly rather than leave a referee to find the warning.
>
> ⚠ `Publication.lean` still showcases `recordKey @ recordSupplyFast`, **not** this class. Pointing its
> theorems here means adding `twinSupply` to the record supply or proving the record supply certifies
> these cells — a change to the published object, not an addition beside it. **User decision, open.**

### W5 — archive
Freeze the repo, final README pass, presentability pass on secondary documents.

---

## 2a. ▶▶ HANDOFF — where a fresh reader picks up (updated 2026-08-08)

> # ⛔⛔⛔ FIRST, A TRACK THIS DOC DOES NOT COVER — **CAO 2-WL propagation is LIVE AGAIN**
> §3 lists *"CAO 2-WL propagation"* as suspended and §2's closing note says do **not** re-open it.
> **Both are superseded**: the 2-WL leg of the closure was **retracted 2026-08-11** (the literature
> statement is *schurian ⟹ schurian*, the target is *CAO ⟹ CAO* — **incomparable**; Shrikhande is the
> witness), and the user re-opened it for Lean footing. It has run continuously since.
>
> ▶▶ **Its record is its own doc: [`chain-descent-cao-carrier-falsifiers.md`](./chain-descent-cao-carrier-falsifiers.md)**
> — read its **`▶▶▶ FRESH PICKUP`** block, not this one, for that track.
>
> > ### ▶ STATE STAMP, 2026-08-16 (supersedes the 08-15 stamp; everything below this box is the 08-13 picture)
> > **No counterexample at 2-WL, and the question is UNDECIDED between two named positions.** The
> > refutation template is `(i) ∘ (ii) ∘ (iii)`: **(ii) is proved** (`FrameTransfer.merge_of_tuple_merge`),
> > **(iii) is quotable in its standard `k`-WL form** (`TupleCov.stableS_wlT`), and **(i) — the collapse
> > — is exactly the open disjunction**: at large `L` the within-copy channel must fail, and either
> > **(A)** the cross-copy channel supplies the orbit (⟹ no mixed cell ever, the construction dies) or
> > **(B)** it supplies nothing the copy lacks (⟹ the ensemble ≡ the poly-size encoding, a CFI payload
> > merges, the construction works). ⛔ **Neither is proved, and the two are observationally equivalent
> > at every computable size** — `M`-2-WL is complete at every reachable `L`, so every measurement that
> > looked decisive was forced.
> > ⚠⚠ An 08-15 stamp said *"(i) is OPEN WITH NO PLAN"* and a later revision of the carrier doc said
> > *"Construction C is dead at 2-WL"*. **Both are withdrawn**: there is now a plan, and it is a
> > decision procedure of verifiable items (carrier doc §6e.4g).
> > ✅✅ **2026-08-16b — items 1, 2 and 3 of that procedure are DISCHARGED IN LEAN.** `RulerLemma.lean`
> > (the Ruler Lemma, carrier-generic, with a non-vacuity witness), `CopyRestrict.lean` (**(LB) as a
> > theorem at every `L` at the real object**, carrying §6b's encoded-edge readout), `CopyProbe.lean`
> > ((P1)/(P2), plus ★ *no mixed cell can be witnessed with a refinement-discrete proper copy*).
> > ✅✅✅ **2026-08-16c — 4a AND 4b DONE. (A) IS A THEOREM AT THE OBJECT, GIVEN ONE DISCRETE COPY.**
> > `Coherence.phi_determined` (**`Φ_E` is 2-WL-available**, unconditional; ⚠ needed `Transposable` —
> > `eRoot` is not a symmetric function). Then the Lean model was **aligned with §3**: `Ensemble.EColr`
> > carried *all* slot colourings (`2^{L²}` — directed copies and self-loop slots), where §3 has
> > **graphs** (`2^C(L,2)`, which is what every probe builds: `L=4 ⟹ N=332`). ★ Checked rather than
> > assumed that nothing was lost: all graphs kept, gauge still transitive, and the **label
> > transposition still an automorphism fixing `m(base)`** (§3.2a's real obligation). With a copy a
> > graph, the two frame symmetries are automorphisms — `twin_blind` (symmetry) and `deg_blind`
> > (irreflexivity) — so **(R) `rulerRefines_of_discrete` and (i) `tagIsolates_of_discrete` are
> > theorems**, giving ★★★★ **`readings_translate_of_wl2G_discrete`: if one copy of `E(L)` has a
> > discrete 2-WL closure, any two payload vertices sharing a closure colour read the frame identically
> > up to a relabelling.**
> > ⚠⚠ **Two inputs remain, and both are inputs rather than the cross-copy channel:** §6e.4a's
> > *"`a` determines `c`"* (translate **readings** vs same-orbit **vertices**), and existence of a
> > refinement-discrete copy (also the theorem's non-vacuity — below `L=6` no graph is rigid).
> > ⟹ ★★★ **(B)'s washout claim is now refuted at the object, conditionally on those two.** ⛔ Still
> > **not** *"Construction C is dead"*.
> > ✅ **The 1-WL results below are unaffected**; every rung-2 negative is about rung 2 only.
> > ✅ Gate **137 modules, ~261 s**; sixteen CAO modules, all axiom-clean.

One-screen version of the 08-13 picture:
> * a `Q₄` carrier is a **designed 1-WL counterexample** (`n = 352`), and the gauge ensemble is a
>   second one at rung 1 (`n = 229,406`, 100 mixed cells);
> * **2-WL reads an edge encoded as a typed common neighbour** (proved + measured), so the frame hides
>   the payload *completely at 1-WL and not at all at 2-WL*;
> * ★★★ the ensemble's 2-WL on a copy **collapses to that copy's own `L²`-vertex encoding** — exact at
>   `L = 4` on every channel — which makes the faithful object **poly-size**;
> * ★★★ **2026-08-14: the encoding's WL gain is BOUNDED, and that is now PROVED in Lean at `k = 2`**
>   (`FrameTransfer.merge_of_tuple_merge`) ⟹ the payload search is **off the critical path**; and the
>   **ensemble is now a graph** (`Ensemble.lean`), so *"`E(L)` has a mixed cell"* is finally expressible.
>   ⛔⛔ **There is still NO counterexample** — four gaps: the collapse, CFI's WL-blindness (literature),
>   T2⁺, and *"any `k`"*. Only the collapse is mathematics.
> * ✅ **Seven CAO modules are gate-listed; the gate is 129 modules, ~254 s.** That doc's **§8a** is the
>   authoritative per-module table and carries the Lean trap list.
> * the one open obligation is the collapse's cross-copy half (that doc's §6e.4), with a written proof
>   plan (§6e) whose Step 1 and base case are done and whose Phase 0 passes at `L = 4` and `L = 5`.
>
> **Lean:** **seven** CAO modules, all gate-listed — `CaoTarget`, `CaoFast`, `CaoEnsemble`,
> `CaoCollapse`, `FrameEncoding`, `TupleWL`, `FrameTransfer`, `Ensemble` (gate **129 modules, ~254 s**).
> ▶ That doc's **§8a** is the authoritative per-module table (what each owns, what each owes) and it
> carries the paid-for Lean trap list. ⚠ `PublicTheoremIndex.md` has **no rows for any of them** — a
> regen is owed and is hazardous (it clobbers the Notes column).


> # ★★★ START HERE — THE STATE, IN ONE SCREEN (2026-08-08)
>
> ### The artifact is closed.
> `Publication.lean` compiles with **zero `sorry` and zero custom axioms**. Seven theorems —
> `canon_sound`, `canon_complete`, `flag_iso_invariant`, `canon_poly_or_flag`, `residue_if_flag`,
> `unhandledResidue_nonvacuous`, `canonizer` — each print exactly
> `[propext, Classical.choice, Quot.sound]`, and **all of them are properties of one object**.
>
> ### The object
> ```
> canonForm? = RecordDeepenCell.canonFormFast
>            = Select.canonFormLazyHSC? recordKey recordSupplyFast deepenCellSupply
>              -- i.e. the cell-indexed supply  fun c => recordSupplyFast ++ deepenCellSupply c
> cost       = RecordDeepenCell.costFast          -- at Select.selNodeLazyHC
> ```
> The fused resolver-aware descent, encode-free refiner, `RecordKey.recordKey` as the force key, and
> the consume supply **cell-indexed**: each cell is judged by generators harvested from descents
> anchored *in that cell*, gated by that cell's own guard. Run by **`Select.selNodeLazyHC`**, which
> walks cells in increasing colour order, evaluates and bills each on demand, and stops at the first
> that fires — with the key evaluated **once** per vertex and the node-level supply factor harvested
> **once** per node (`W-j`). The single capstone is **`RecordDeepenCell.recordDeepenCell_full_fast`**.
>
> | | |
> |---|---|
> | `①a`/`①b`/`①c` | ✅ global, **no hypothesis** (`recordDeepenCell_canonizer`) |
> | `②` | ✅ `cost ≤ 69 * (n+1)^13`, every input, **no flag disjunct** |
> | `③` | ✅ flag ⟹ `¬ TinhoferGraph`, **for every key** (`not_tinhoferGraph_of_flag`). ★ A **narrower** residue is now proved and unwired: `not_all_resolvable_of_flag` at `ResolvableCellAt` (W2 stage 2) |
> | non-vacuity | ✅ `K₁,₂,₃` handled, `K₃ ⊔ C₄` residual |
> | runs | ✅ `#eval` answers on `K₂`, `C₅`, `K₁,₂,₃` (20.8 s / 50.4 s after `W-j`) and on `K₃ ⊔ C₄` |
>
> ### ⚠⚠ The three things that must travel with any quotation of it
> 1. **`②`'s degree is a bound, not a measurement.** Several components bill *declared flat* charges
>    (harvest flat `n⁶` per cell where the real work is `≈ m²n⁴` with `Σ m_c² ≤ n²`; `holKeyFast`
>    flat `n⁵`; `selProbeBoundC` charging every cell the *maximum*; `goodCellCost`'s nested flat
>    `n⁶`). It rules out exponentials; it does **not** establish 13 as the algorithm's true degree.
>    Stated at source in `Publication.lean`'s `costConst`/`costDeg` block.
>    ⛔ **But do NOT infer "so tighten those four" — computed 2026-08-08, none of them moves either
>    numeral.** `costConst` is the bound polynomial at `n = 1`, and `costDeg` is set by the single
>    term `(n+1)·n·(n·kc)`. The **only** lever is `Deck2.deck2Supply`'s declared charge (→ 11 / 65).
>    See the `W-j` block below.
> 2. **`③`'s residue is an over-approximation.** `¬ TinhoferGraph` counts CFI graphs as residual
>    although their obstruction is *linear* and belongs to the rigid resolver. Narrowing it is W2.
>    The claim is *"a flag means a real structural obstruction"*, never *"a flag means hardness"*.
>    ★ A strictly narrower residue **is now proved** (`RecordDeepenCell.not_all_resolvable_of_flag`
>    at `ResolvableCellAt`) and is **not yet wired into `Publication`** — option **A** below.
> 3. **The object answering everywhere is BY DESIGN, not a defect** (user, 2026-08-08). It answers on
>    `K₂`, `C₅`, `K₁,₂,₃` **and on `K₃ ⊔ C₄`** — the residual witness itself. The design is free to be
>    stronger than what is proved; proving that it is strong is the point of `③`. ⛔ W4 must say
>    *"the canonizer has not yet been **proven** on most interesting inputs"*, never *"it flags on
>    most interesting inputs"* (which is false). Known flagging witness, not yet reproduced in Lean:
>    a multipede the rigid handler cannot peel, failing at the root.
>
> ### ▶ What is left
> **W2** — ✅ **stages 1–2 built 2026-08-08** (the `SomeCellOrbit` socket + the named obligation
> `ResolvableCellAt`, both gated and axiom-clean, with the `Tinhofer` population re-derived through
> them), and the **disjunctive socket** followed (§9a/§9b, 2026-08-09) — `CellResolvedAt` on the
> key's **survivors**, admitting consume / force / **mixed**, plus the force route's entry point.
> **Three probes have now run, and between them they RETARGETED W2 twice:**
> 1. ⛔ `ResolvableCellAt` fails at the **CFI-over-cubic root** — which is the design (mixed-orbit
>    cells are force's domain), **not** a blocker; the `mp7` retarget that followed is **RETRACTED**.
> 2. ◐ **`holKeyFast` is structurally inert at the CFI root** (1 cross-cell component ⟹ no valid
>    walk) ⟹ that root rests entirely on the `orbKeyG guardSupply` tiebreak.
> 3. ⛔⛔⛔ **And then the premise inverted: a gauge can NEVER make a cell mixed** — it is a
>    *subgroup* of `Aut`, so it only merges. Measured, **no `Aut`-block at any CFI root is a single
>    gauge-orbit**, so reps ≥ 2 always ⟹ **the gauge alone cannot fire a CFI root cell** (⚠ *"no key
>    of any kind"* was the earlier wording — over-strong, corrected 2026-08-10 in §2 W2's item-3 block:
>    all four witnesses have a **symmetric base**), and
>    **CFI-over-cubic is not an instance of the target claim at all**. Its gauge is what
>    `kernelSupply` already consumes; the remainder is the **base graph**.
>
> 4. ✅✅ **AND THEN item 3b (2026-08-10) PUT CFI BACK ON THE TABLE, in the LAYER form.** All four
>    item-3a witnesses have a **symmetric base**; the `reps ≥ 2` bound needs `Aut > gauge`, which is
>    base symmetry. Measured over asymmetric bases, with a **descent walk** (not root-only):
>    base 1-WL **discrete** ⟹ **every** non-singleton cell is a **single gauge-orbit** at **every**
>    reached node (21/21, 26/26, and all 4 walk levels) ⟹ `CellOrbitAt` holds for the gauge, which
>    `recordSupplyFast` **already contains** (`kernelSupply`), and `CellOrbitAt` carries **no guard**
>    ⟹ ✅ **fires with the shipped object, no key work**. Base asymmetric but 1-WL **coarse**
>    (Frucht): blocks **=** gauge-orbits exactly ⟹ the counting bound is **gone**, firing is a pure
>    **key** question. Base symmetric: ⛔ still blocked. ⟹ *solve the CFI part, hand back the base.*
>
> 5. ⛔⛔⛔ **AND THEN (2026-08-10) THE FOUNDATION UNDER ALL OF IT TURNED OUT TO BE MISSING** —
>    **[`chain-descent-force-refinement-channel.md`](chain-descent-force-refinement-channel.md)**, read
>    it before W2. In the published object **the force key's value never enters a colouring**: force's
>    only channel is `keepMin` (selection inside one cell), so a key that *splits* a mixed cell into
>    orbit-blocks registers as **failure**. Success is binary — whole cell one orbit, or key injective
>    on the cell. ⟹ *"force separates mixed cells"* is **inexpressible as success**, and the ≤ 8-value
>    cap, the `hrigid` hypothesis and item 3b's Frucht result are **one** wall seen three ways.
>    ⛔⛔ **AND ITS §6 PROBE HAS NOW RUN — METHOD 2 IS REFUTED** (`scratchpad/probe_w2_linked.out`,
>    9 witnesses, 2026-08-10). `rowspace H = ker(H)^⊥` ⟹ `Linked u v ⟺ ∀ x ∈ ker H, x_u = x_v`, so it
>    is the **total** relation when `dim ker = 0` (`G8`) and the **equality** relation when
>    `dim ker > 0` (84/84, 56/56, 42/42, 28/28 singleton classes). Every legal read — class size, and
>    the steelman *1-WL on the 2-relation `adj ∪ Linked`* — leaves the non-singleton cells `k → k`
>    with identical sizes on **all 9** witnesses. The kernel **signature** does split them, and
>    splits `CFI(K₄)` where `Aut` merges all 16 gadget vertices into one block — **144/1152/768/6912
>    read-equivariance violations** against edge-verified gauge automorphisms. Choosing a kernel basis
>    **is** choosing a column order: `OrdEquivariant` unsatisfiability again.
>    ⟹ ★ **Gauge-blindness was never the obstacle; naming a class without an order is**, and a
>    relation does not dodge it. Method 1 (the refinement **channel**) survives intact but has **no
>    reader to carry** — do not build its plumbing until some read is *measured* to split a cell.
>    ★ And note (source, `Select.lean:22-23`): the `≤ 1` success bar is what buys `②`'s single path of
>    `≤ n+1` nodes — ⛔ never "fix" the missing partial-success rung by committing to `k > 1` survivors.
>
> ⟹ **TWO live targets, and the cheap one is the CFI LAYER, not S3.** ✅ The socket **and the instance
> kit** are built (`SelectCell` §9a/§9b/**§9c**): a family discharges its consume half by exhibiting
> one **emitted + sound + transitive** generator list. For CFI that is *sound* ✅ (`CFI.cfiFlipAut`),
> *transitive* ✅ (measured), *emitted* ⛔ — `KernelSupply.lean` has **zero theorems**, so carry it as a
> hypothesis like `ForcingModel.bridge`. ▶ **S3 (the rigid regime) remains the other target — but read
> the S3 corrections below before starting it: it is aimed at the wrong generation of the reader.**
> **Read §2 W2's re-affirmation block AND its item-3 block in full before touching it.** · **W3** (extraction) · **W4** (write-up) · **W5**
> (archive). **`W-j` is ✅ LANDED** (below).
>
> ### ✅ `W-j` — LANDED 2026-08-08, `SelectCell.lean` §8 + `RecordDeepenCell.lean` §5
> The per-cell plan's *"nothing outstanding"* was right about its own scope and wrong as a statement
> about the object's runtime. `Select.probeWalk` was correct and the laziness worked, but per
> **probed cell** it still:
> * evaluated the record key **three times per vertex** — once for the bill
>   (`(cellList χ c).map (keyCost key adj χ)`) and twice inside `Force.keepMin` (`kmin?` over
>   `B.map keyV`, then `B.filter (keyV · = m)`). `keyCost`/`keyV` are `.2`/`.1` of the *same* strict
>   pair, so each was a full key computation and Lean shares nothing across them;
> * re-harvested the **cell-independent** left factor `RecordCost.recordSupplyFast` and re-ran its
>   `IsColAut` filter, because `S c = recordSupplyFast ++ deepenCellSupply c` is evaluated whole.
>
> ⚠ The **same** double-evaluation is in the node-global `selNode`/`selNodeFast`, over *every* cell —
> so this was never a cost of the per-cell design, and the recorded per-cell-vs-node-global
> comparisons are both paying it. (`selNode` is **not** changed by `W-j`; only the cell-indexed
> object was repointed.)
>
> | built | where | what |
> |---|---|---|
> | `Select.keyTable` / `keepMinT` / `keepMinT_keyTable` / `keyTable_cost` | `SelectCell` §8 | the key evaluated **once** per vertex, read by the bill *and* the argmin |
> | `Select.SplitSupply` | ” | the supply's node-level / cell-level split, stated as a property so the file needs no new import; the endgame instance is `rfl` |
> | **`Select.probeWalkH`** + **`probeWalkH_eq`** | ” | the hoisted walk, and the proof that it **is** `probeWalk` at the composed supply — both components |
> | `Select.selNodeLazyHC` / `canonFormLazyHSC?` / their `_eq`s | ” | the resolver and top level |
> | `RecordDeepenCell.splitSupply_recordSupplyDeepenC` (`rfl`) · `canonFormFast` · `costFast` · **`costFast_eq`** | `RecordDeepenCell` §5 | the endgame object repointed |
>
> ★ **Because the bill is unchanged, `probeWalkH_eq` is an equation, not an inequality** — `①`, `②`
> and `③` all transfer by `rw` and **`costConst`/`costDeg` do not move** (69 / 13).
> Gate **exit 0, 228 s, 119 modules**; `Publication.lean` unchanged in substance and still zero
> `sorry` / zero custom axioms; all new declarations axiom-clean.
>
> | graph | ns-cells | before `W-j` | after `W-j` | billed cost |
> |---|---|---|---|---|
> | `C₅` (n=5) | 1 | 27.6 s | **20.8 s** (1.33×) | 5 212 728 — **identical** |
> | `K₁,₂,₃` (n=6) | 2 | 74.4 s | **50.4 s** (1.48×) | 20 321 716 — **identical** |
>
> At one cell the gain is entirely key-sharing; the supply hoist only starts paying from two cells and
> scales with the number of cells **probed**.
>
> ### ⛔⛔ AND `W-j` KILLED ITS OWN FOLLOW-UP — THE `②`-TIGHTENING ADVICE ON RECORD IS WRONG
> ~~"the honest-billing variant (charge the record harvest once per **node**) tightens `②`, giving
> back most of the `+8` that took `costConst` 57 → 69"~~ — **FALSE, computed against
> `recordDeepenBound_expand`'s own polynomial.** So is the older advice in §2a's caveat 1 and in
> `Publication.lean`, *"tightening starts with billing the harvest as `|cell|²·n⁴`."*
>
> Two structural facts, and they prune the whole search:
> * **`costConst` is the bound polynomial at `n = 1`** (it *is* the coefficient sum). Moving a factor
>   of `n` in or out — which is exactly what per-node vs per-cell billing does — **cannot change it**,
>   however much the polynomial improves for `n ≥ 2`.
> * **`costDeg` is set by one term**, `(n+1) · n · (n · kc)` with `kc = RecordKey.recordKeyBound`.
>   Set `kc := 0` and the whole bound is degree **11** — so no consume-side or guard-side charge can
>   move the degree at all.
>
> Measured effect on `(costDeg, costConst)`:
>
> | change | result |
> |---|---|
> | harvest billed `\|cell\|² · n⁴` instead of flat `n⁶` | **13 / 69 — no change** |
> | `goodCellCost`'s nested flat `n⁶` → `n⁴` | **13 / 69 — no change** |
> | `holKeyFast` flat `n⁵` → `n⁴` | **13 / 69 — no change** |
> | record supply billed once per node (`W-j2`) | **13 / 69 — no change** |
> | **`Deck2.deck2Supply`'s declared `n²(1+n²)·n⁵` → `n⁷`** | ★ **11 / 65** |
>
> ⟹ **the single lever is `Deck2.deck2Supply`'s declared per-node charge.** Chain: `deck2` `n⁹` →
> `RecordKey.guardSupplyBound` `n⁹` → `recordKeyBound = … + n·guardSupplyBound` `n¹⁰` →
> `selProbeBoundC`'s `n·(n·kc)` `n¹²` → `(n+1)·` → **`n¹³`**. The charge is
> `|branches|² · (1 + n²) · n⁵` at `|branches| ≤ n`; tightening it means carrying the branch-cell
> size `m`, which is a real derivation, not a re-bracketing. **Recorded at source in
> `Publication.lean`'s `costConst`/`costDeg` block. `W-j2` is DEAD — do not build it.**
>
> ★ One **open measurement**, worth having before W4 quotes any performance number: the walk's win
> was measured only at 1–2 non-singleton cells. `probe_offbranch5`'s depth-1 CFI nodes carry
> **28/28/24/26/14/10/14** cells, where the ceiling should be far higher — unverified. `W-j`'s hoist
> is the part that scales with that number, so it is now worth measuring.
>
> ### ▶▶▶ WHAT TO PICK UP — the live options, in the order I would take them
>
> Nothing is half-finished: the gate is green, `Publication.lean` is closed, and every increment
> below is independent of the others. Pick one.
>
> | | option | size | why / why not |
> |---|---|---|---|
> | **A** | **Wire `ResolvableCellAt` into `Publication.UnhandledResidue`** as the narrowed residue, with `RecordDeepenCell.not_all_resolvable_of_flag` as its `③` | small — **no new mathematics**; every piece is proved and gated | It is a real definition (not an `opaque` atom, so it does not re-break `unhandledResidue_nonvacuous`), it is **measured non-vacuous both ways** (`mp7` resolvable everywhere; `rand multipede V=6 W=5` and `G8` nowhere), and it strictly narrows `¬ TinhoferGraph`. ⚠ It does **not** capture CFI-over-cubic — that must be said plainly wherever it is quoted |
> | **B** | **W2 = the CFI LAYER.** ⛔⛔ **FIRST read [`chain-descent-force-refinement-channel.md`](chain-descent-force-refinement-channel.md)** — force has **no refinement channel**, so its core job is inexpressible as success here, and that is the common cause of the ≤ 8-value cap, `hrigid`, and item 3b's Frucht result. ⛔ **Its §6 probe HAS RUN and REFUTED method 2** (`probe_w2_linked.out`) — the channel has no reader, so B's force half is now *"find an equivariant read that splits a mixed cell"*, i.e. the same open property S3 bottoms out on. **B's consume half (the §9c kit + the carried `emitted` hypothesis) is unaffected and is the part that can still land.** ✅ **socket + instance kit built** (§9a/§9b/**§9c**); ✅ **four probes run**; then **the CFI layer instance** (`V` = the gauge flips; *sound* ✅, *transitive* ✅ measured at every reached node, *emitted* = the one carried hypothesis — `KernelSupply.lean` has zero theorems). ⚠ **S3 is the OTHER target and is mis-aimed as written** — see the S3 corrections. ⛔ ~~W2 at `mp7`~~ and ~~W2 at the CFI root~~ are **both retracted** | S3 = the real research box | **Read §2 W2's re-affirmation block AND its item-3 block before starting** — four routes are refuted there, and the target was *inverted* on 2026-08-09: **a gauge can never make a cell mixed** (it is a subgroup of `Aut`), so **CFI-over-cubic is not an instance of the claim at all** and the **gauge alone** cannot fire its root cells (⚠ the earlier *"no key of any kind"* is over-strong — see the 2026-08-10 scope correction in the item-3 block: every witness has a symmetric base). The claim's home is the **rigid** case (`dim ker = 0`), where every hypothesis flips to satisfied |
> | **C** | **W4 write-up** | 1 week | The go/no-go was met at W1. Read W4's must-state list first — item 3 was **corrected 2026-08-08** and items 1/9 now have the sharpened `②` story (only `deck2Supply`'s charge can move the degree) |
> | **D** | measure `W-j`'s hoist ceiling on a many-celled node; land a `#eval` flag witness (the multipede the rigid handler cannot peel) | small each | Both are owed *before* W4 quotes a performance number or the flag semantics |
>
> ⛔ **Do not start**: CFI-over-cubic coverage (force-side, Track R is suspended); `W-j2`
> per-node billing (computed to change neither numeral); anything in §3's suspended table.
>
> ### Reading order for a fresh pickup
> 1. This block, then §2a's `Publication.lean` state table and the **sixteen corrections** below.
> 2. [`chain-descent-percell-plan.md`](chain-descent-percell-plan.md) — **the design record of the
>    object above** (it is no longer a plan; every item is ✅). Its §1–§3a explain *why* the supply
>    had to be cell-indexed, and its §2/§6/§7/§10 carry the retractions.
> 3. `Publication.lean` top-to-bottom — it is the deliverable and its prose is current.
> 4. `RecordDeepenCell.lean` → `SelectCell.lean` → `DeepenCell.lean`, in that order. ★ For **W2**
>    read `SelectCell.lean` **§9a** (`CellResolvedAt` — the *disjunctive* socket, the one to state
>    any CFI theorem against) and **§9b** (the force route's entry point), then
>    `RecordDeepenCell.lean` **§3a/§3b**. ⚠ §9's `SomeCellOrbit`/`ResolvableCellAt` are the
>    **consume-only** predecessors — kept because the `Tinhofer` population rides them, but
>    **unsatisfiable on a rigid graph**, so do not state a CFI theorem there. §2 W2's correction
>    blocks say why **four** earlier routes were wrong.
> 5. `PublicTheoremIndex.md` for anything else.
> 5a. ⛔⛔ **[`chain-descent-force-refinement-channel.md`](chain-descent-force-refinement-channel.md)**
>    — the 2026-08-10 diagnosis (force has no refinement channel), the three ranked methods, and the
>    step-0 probe. **Read it before doing anything in W2.**
> 6. Measured evidence: **`scratchpad/probe_w2_asymbase.out` (item 3b — CFI over an asymmetric base;
>    the layer theorem measured true), `probe_w2_linear.out` (item 3a — the gauge/mixedness inversion,
>    read this one for W2)**, `probe_w2_keysplit.out` (step (ii) — `holKeyFast` inert at the CFI
>    root), `probe_w2_resolvable.out` (W2 stage 0),
>    `scratchpad/ProbeShareWalk*.lean` + `ProbeWjMeasure.lean` (`W-j`),
>    `scratchpad/ProbeAnswers.lean` (what the object answers on).
>
> ---
>
> **▶ How it got here — chronological, 2026-08-04 onward** (provenance; the block above governs):
> * **`Tinhofer ↔ CertifiedG deepenSupply`** (`DeepenGuardComplete` §§0–7) — deepen's poly guard is
>   **complete**, so it transports with **no `SupplyEquivariant`**; `deepenSupplyCert` is a
>   **computable** supply with `①` and **no hypothesis**. ⛔ This **refutes `DeepenCertified` §7**.
> * **`GoodOrIsolated` is equivariant and STRICTLY beats `Tinhofer`** (`DeepenGuardComplete` §9) —
>   2 strict wins in 60 random cubic graphs, the `n=10` one verified by exhaustive `10!` enumeration.
> * **`pairStep`** (`DeepenPair`) — the depth-2 step; **is** the twin refinement (`TWIN = BOTH`);
>   whole `step` interface inherited, blast radius **zero**.
> * **`Deepen.stepCost` is billed** — `certPathCost` charged nothing for the `step` it walks.
>   ⟹ **`RecordKey.costConst` 53 → 57** (degree still 13).
> * ⛔⛔ **`BAD-BIG = 0` is FALSIFIED** (`DeepenComplete` §5.2) — the union-over-anchors question is
>   **re-opened**. Nothing proved breaks; the *expectation* that good-or-rigid covers everything dies.
> * ★★★★★ **DESIGN `B` IS LANDED THROUGH `①` *AND* `③` (2026-08-08)** — three modules, all in
>   `build.sh`, all axiom-clean, gate **119 modules**:
>   `ChainDescent/SelectCell.lean` (**`Select.selNodeC_canonizer`** — `①` for the **cell-indexed**
>   fused resolver from `KeyEquivariant` + the new `Select.CellOrbitTransport`, **no
>   `SupplyEquivariant` anywhere**; plus §4, the stall/`HandledSC`/answers mirror),
>   `ChainDescent/DeepenCell.lean` (**`Deepen.deepenCell_canonizer`**), and
>   **`ChainDescent/RecordDeepenCell.lean`** — the **endgame object**
>   `selNodeC recordKey (fun c => recordSupplyFast ++ deepenCellSupply c)`, carrying
>   **`recordDeepenCell_canonizer`** (`①`, global, no hypothesis) and
>   **`not_tinhoferGraph_of_flag`** (`③`, every key).
>   ★ `SelectNode.lean` is **untouched**: `Select.lean`'s spine is resolver-generic, so `selNodeC` is
>   just another `NodeRes n` and only `NodeTransport` was re-proved.
>   ★★ **`①` and `③` now hold of the SAME object with `①` unconditional** — which neither option
>   (iv) (residue is not `¬Tinhofer`) nor option (v) (`①b`/`①c` class-only) can give. *(`②` followed
>   the same day — see below.)*
>   ★★ The recorded W-d risk was **misdiagnosed and dissolved** — no per-cell analogue of
>   `tinhofer_iff_certifiedG` is needed, because `GoodAnchor` is a property of the anchor's OWN path,
>   already decidable (`goodAnchor_iff_certPath`) and **unconditionally** invariant
>   (`goodAnchor_relabel`). W-d′ likewise: `kernelSupply`'s non-equivariance is a non-event, since
>   `Kernel.sameOrbits_recordSupply` + `supplyEquivariant_recordRefSupply` discharge
>   `cellOrbitTransport_append`'s hypothesis in ~25 lines.
>   ★★★ **AND `②` LANDED THE SAME DAY (W-h, with W-a and W-f folded in)** —
>   `SelectCell` §5 (`selProbeBoundC` / `selProbeCostC_le` / `descentCostS_selNodeC_le`, no firing
>   hypothesis), `DeepenCell` §7a (**`goodCellCost_bounds_guard`** — the guard's `≤ n` `CertPath`
>   walks are now *billed*, closing the recorded `n⁶`-declared-vs-`n⁸`-real hole), and
>   `RecordDeepenCell` §4 ending at **`recordDeepenCell_full` = `①` ∧ `②` ∧ `③` at one object**.
>   `ring`-checked numerals: **`costDeg` 13 unchanged, `costConst` 57 → 69** (+8 per-cell supply
>   billing, +4 guard). ⛔ The prediction that the degree would move was wrong — `recordKeyBound`
>   already reaches `n^10` and the key sets the degree.
>   ★★★ **AND `W-i` LANDED THE SAME DAY** — `Select.cellData` (each cell's supply evaluated **once**
>   per node) / `selNodeFastC` / `canonFormFastSC?`, and
>   the runnable eager form. ⚠ `selNodeFastC_eq` is a **proved** equation, not `rfl` (the table
>   returns `[]` off `nsColours χ`) — everything transfers by rewriting with it. ★ `C₅`
>   **216 s → 41 s**, cost value identical. ⚠ **Superseded for the endgame by `W-e`'s
>   `selNodeLazyC`**, which is what `recordDeepenCell_full_fast` is now stated at; `selNodeFastC`
>   remains as the eager reference.
>   ✅ **W-g and W-e both landed the same day**, so nothing from the per-cell plan is outstanding:
>   `Publication.canonForm?`/`cost` are `RecordDeepenCell.canonFormFast`/`costFast` at
>   `costConst`/`costDeg` = 69/13, and the object is lazily billed.
>
>   ⚠⚠ **AND A STANDING CAVEAT ON `②`** (user, 2026-08-08): the bound is an unconditional theorem
>   about the object's `CostM` accounting, but several components bill **declared flat** charges that
>   over-estimate — the harvest's flat `n⁶` per cell (real `≈ m² n⁴`, `Σ mᵢ² ≤ n²`), `holKeyFast`'s
>   flat `n⁵`, `selProbeBoundC` charging every cell the *maximum* `sB`/`gB`, `goodCellCost`'s nested
>   flat `n⁶`. ⟹ **`costDeg` staying 13 across 57 → 69 does NOT show the algorithm's true cost
>   polynomial kept its degree** — both are upper bounds from the same loose accounting. What is
>   established: an explicit polynomial ceiling on every input (no exponential), and that the
>   per-cell change did not raise *that ceiling*'s degree. Recorded at source in `Publication.lean`'s
>   `costConst`/`costDeg` block.
> * ★★★ **`RecordDeepen.lean`** (in `build.sh`, axiom-clean) — **`③` at the NODE-GLOBAL object**:
>   `not_tinhoferGraph_of_flag_recordDeepen` at `selNode` + `recordSupplyFast ++ deepenSupplyCert`,
>   via supply monotonicity (`handled_append_right`) plus `certifiedG_of_tinhofer`. ⚠ It landed
>   without doc propagation and was referenced in **no** doc, plan or memory before 2026-08-07.
>   ⛔ **CORRECTION (2026-08-08): the inference *"⟹ `③` is not on the critical path"* was WRONG.**
>   The theorem is stated at `selNode` + the node-global supply — the object §3's CFI falsifier kills
>   for `①` — and `Select.HandledS` / `answersS_of_handledS` / `not_handledS_if_flagS` are all
>   `selNode`-specific, so it does not rewrite onto `selNodeC`. Its *argument* transferred; the
>   theorem needed a ~150-line mirror, now in `SelectCell` §4 + `RecordDeepenCell` §3.
>   ★ **General rule this exposed:** a new `NodeRes` inherits everything **`Select.lean`** proves
>   generically (`descendS`, `canonFormS?`, `isCanonicalFormOptS_canonFormS?`, `descentCostS_le_of_le_one`,
>   `descendS_ne_none_reaches`) and **nothing `SelectNode.lean` proves specifically**. The same trap
>   is why `②` needs W-h rather than a numeral recompute.
>
> ⛔ **Two wrong diagnoses recorded so they are not re-derived** (both mine, both retracted):
> (a) *"the fused object cannot carry deepen"* — it can; `①` never needed an equivariant reference;
> (b) *"§9 is a socket, not a gain"* — a population artefact of an all-multipede/CFI sweep.

**Gate is green**: `bash /workspace/scripts/build.sh` → **119 modules, ~231–361 s, exit 0** (measured
2026-08-08; the spread is swap pressure, not a change in the work). ⚠ Use the **absolute** path — the
script `cd`s via `$0`. ⚠ `build.sh` opens with `pkill -f 'lake build'`, which kills **any** shell whose
command line contains that string — never chain a `lake build` and the gate in one command. No `sorry`,
`native_decide` or new axiom anywhere in the gated library.
**`Publication.lean` is NOT gated** (compile it standalone: `cd GraphCanonizationProofs && lake env lean
Publication.lean`); since 2026-08-08 it has **zero** `sorry` and **zero** custom axioms.

### ▶▶ STATE OF `Publication.lean` (2026-08-08) — **CLOSED**; read before touching it
| obligation | state |
|---|---|
| `canon_sound` / `canon_complete` / `flag_iso_invariant` (`①`) | ✅ axiom-clean, unconditional |
| `canon_poly_or_flag` (`②`) | ✅ axiom-clean, on the **LEFT** disjunct |
| `canonizer` | ✅ axiom-clean; its cost conjunct is now **unconditional** (the residue escape was never needed) |
| `unhandledResidue_nonvacuous` | ✅ **DISCHARGED** axiom-clean (`RestrictedTransport.tinhoferGraph_nonvacuous`) |
| **`residue_if_flag` (`③`)** | ✅ **DISCHARGED 2026-08-08** (`W-g`) — `recordDeepenCell_full_fast.2.2`, axiom-clean, at the same object as `①`/`②`. **The file now has zero `sorry`.** |
| `costConst` / `costDeg` | ✅ **69 / 13** — `RecordDeepenCell`'s, `ring`-checked. ⚠ A bound from declared flat charges, **not** a measurement of the algorithm's degree |
| the 8 citation axioms | ⚠ **consumed by NOTHING** and therefore **commented out**; retained for W2/Route C only — the paper must say so. Restoring one is deleting `-- ⏸ ` from a single line |
| **the file as a whole** | ✅ **zero `sorry`, zero custom axioms**; every headline theorem prints `[propext, Classical.choice, Quot.sound]` |

`UnhandledResidue` is now a **definition** (`residueRigidObstruction G := ¬ TinhoferGraph G`), not three
`opaque` atoms. ⛔ **Do not re-add an opaque disjunct** (e.g. `NonLinearRigidObstruction`) until it has
content: an opaque `Prop` makes the *handled* half of `unhandledResidue_nonvacuous` unprovable in
principle, which is the trap the reshape undid.

⛔⛔ **STANDING STEER (user, 2026-08-04): never discharge a `Publication` obligation by relocating it to a
second object.** `canonForm?` is meaningful only if `①a`+`①b`+`①c`+`②`+`③` are properties of **the same**
object — an exhaustive solver and a random solver each carry half and together prove nothing. A
two-object split was tried this session and reverted.

### Read in this order
⚠ This list predates the close and is kept because items 2–5 are still the right background reading.
**The current entry point is the START-HERE block at the top of this section**, whose reading order
supersedes items 0–1 here.
0. **[`chain-descent-percell-plan.md`](chain-descent-percell-plan.md)** — ✅ now the **design record**
   of the published object, not a plan (every item is done). Read before §2's options table, which it
   supersedes.
1. **This document**, §1 (why closed) → §2 W1 (what landed, its boxed corrections, the **options table**
   — now provenance — and the **R1 block**) → §2 W4.
2. [`ChainDescent/TwinFamily.lean`](../GraphCanonizationProofs/ChainDescent/TwinFamily.lean) — module
   doc-block first; §3 the socket, §8 the twin object, §9 the bridge (⛔ `noncomputable`), §10 the
   repaired executable bridge.
3. [`ChainDescent/RestrictedTransport.lean`](../GraphCanonizationProofs/ChainDescent/RestrictedTransport.lean)
   — §1–§6 `①` on a class (Tinhofer graphs are canonized), §7 the non-Tinhofer witness, §8 the
   computable certificate and why it stops short.
4. [`ChainDescent/DeepenComplete.lean`](../GraphCanonizationProofs/ChainDescent/DeepenComplete.lean) —
   the **R1 scoping**: `GoodAnchor` / `OrbitComplete`, the payoff chain, and §5's *good-or-rigid*
   weakening with the measurement that closed the union question.
5. [`ChainDescent/DeepenTransportOn.lean`](../GraphCanonizationProofs/ChainDescent/DeepenTransportOn.lean)
   — `①` on a class **at the deepen object**; §7 packages option (v).
6. `Publication.lean`'s STATUS block, then the table above.
7. `PublicTheoremIndex.md` for what is proved (all `TwinFamily` / `RestrictedTransport` /
   `DeepenComplete` / `DeepenTransportOn` rows are described; ~14 `Showcase` rows and a long tail
   elsewhere carry `—`, a pre-existing backlog, W4/W5 scope).

### The things that landed, in dependency order
| | where | what |
|---|---|---|
| socket | `TwinFamily` §3–§4 | `handledS_of_noRigidObstruction` — step-closed class + no rigid obstruction ⟹ `HandledS`. **Widening the handled region = supplying a wider `P`; nothing below re-proves.** |
| bridge | `TwinFamily` §9 | `handledS_of_tinhoferGraph` + `not_tinhoferGraph_of_flagS`. `IndivReach` is step-closed **by construction**. ⛔ **stated at `noncomputable` `orbKey` — superseded for publication by §10.** |
| wall | `TwinFamily` §8 | `twinSupply` (computable, `SupplyEquivariant`) ⟹ `canonized_of_multipartite` = `①` ∧ answers; **`answers_poly_of_multipartite` = `②`**. All three at one object. |
| **publishable bridge** | `TwinFamily` §10 | **`not_tinhoferGraph_of_flag` + `answers_poly_of_tinhoferGraph` — the bridge at an EXECUTABLE object, with `②`, for every key.** |
| **`①` on the class (force)** | `RestrictedTransport.lean` | **`canonizes_on_tinhofer` + `descentCost_on_tinhofer` — the transport spine relativized to (graph class) × (reached colourings), discharged at `forceThenPick` with NO supply. Additive: `Descend.lean` untouched.** |
| **R1, scoped** | `DeepenComplete.lean` | `GoodAnchor` (the per-anchor condition actually consumed) · **`OrbitComplete`** (the target) · `deepenSupply_canonizer_of_orbitComplete` (`①c` for the raw supply from it alone) · **§5 `orbitComplete_of_good_or_trivial`** + `goodAnchor_transport` |
| **`①` on the class (deepen)** | `DeepenTransportOn.lean` | **`canonizes_on_orbitComplete` — the same relativization at the guarded mixed resolver; §7 `deepen_object_package` = option (v), all four obligations at ONE executable object** |
| **the cell-indexed spine** | `SelectCell.lean` | `CellSupply`/`selNodeC`/**`CellOrbitTransport`** (replaces `SupplyEquivariant`) · §4 the stall/`HandledSC`/answers mirror · §5 `②`'s per-node bill · §6 the eager runnable twin · §7 **lazy billing** (`probeWalk`/`selNodeLazyC`) + lemmas A (`find?_sort_eq_min`) and B (`descendS_val_congr`) · §8 **`W-j`** (`keyTable`/`probeWalkH`/**`selNodeLazyHC`** — the published resolver; key evaluated once per vertex, node-level supply factor once per node, bill unchanged) |
| **the cell-anchored harvest** | `DeepenCell.lean` | `deepenGensOn` · **`GoodCell`** (decidable, *unconditionally* invariant) · §7a **`goodCellCost_bounds_guard`** — the guard is billed, not declared |
| **★ THE PUBLISHED OBJECT** | `RecordDeepenCell.lean` | **`recordDeepenCell_full_fast` = `①` ∧ `②` ∧ `③` at one runnable object.** `W-d′` rides `Kernel.sameOrbits_recordSupply`; `③` rides `goodCell_of_tinhofer` |
| **`W-j` — the shared key + hoisted factor** | `SelectCell` §8 + `RecordDeepenCell` §5 | `keyTable`/`keepMinT` · `SplitSupply` · **`probeWalkH`** + **`probeWalkH_eq`** (an equation in BOTH components ⟹ no numeral moves) · `selNodeLazyHC` · `costFast_eq`. 1.33×/1.48× measured |
| **`W2` stage 1 — the socket** | `SelectCell` §9 | `CellOrbitAt` · `cellNarrowC_length_le_one_of_cellOrbitAt` · `SomeCellOrbit` · **`handledSC_of_someCellOrbit`** — *one* resolvable cell per node suffices, at **any** cell, no `targetColour`. ⚠ **consume-only**; superseded as the W2 socket by §9a |
| **`W2` — the FORCE route's entry point** | `SelectCell` §9b | `cellSeparatedAt_of_branchSeparation` · **`someCellResolved_of_branchSeparation`** · `nodeResolvedC_of_branchSeparation` · **`handledSC_of_branchSeparation`** — the rigid stack's firing lemmas end in `nodeResolved_of_cellResolved (Or.inr …)`, whose disjunct **is** *"the key is injective on `branches χ`"*, so they reach the cell-indexed socket by plumbing. ⚠ Stated **generically — no `Rigid*` import**, so the published object's dependency graph is unchanged |
| **`W2` stage 1b — the DISJUNCTIVE socket** | `SelectCell` §9a + `RecordDeepenCell` §3b | **`CellResolvedAt`** (the condition on the key's *survivors*) · **`cellNarrowC_length_le_one_of_cellResolvedAt`** · route 1 `cellResolvedAt_of_cellOrbitAt` (consume) · route 2 **`CellSeparatedAt`**/`keepMin_length_le_one_of_cellSeparatedAt`/`cellResolvedAt_of_cellSeparatedAt` (force, **no supply**) · **`SomeCellResolved`**/**`handledSC_of_someCellResolved`** · at the published object **`handledSC_of_resolvedCells`**/**`not_all_resolved_of_flag`**. ★ The **mixed** case (key cuts between orbits, supply certifies the survivor) is expressible for the first time |
| **`W2` stage 2 — the obligation** | `DeepenCell` §9 + `RecordDeepenCell` §3a | `Deepen.cellOrbitAt_deepenCellSupply` (`GoodCell` ∧ `CellSingleOrbit` at one cell ⟹ it fires) · **`ResolvableCellAt`** · `handledSC_of_resolvableCells` · **`not_all_resolvable_of_flag`** (a narrower `③`, **not yet wired into `Publication`**) · `resolvableCellAt_of_tinhoferGraph` (so `TinhoferGraph ⊆ resolvable-everywhere` is machine-checked) |

### ⚠ EIGHT OBJECTS — do not mix them up when writing
| object | executable | `①` | `②` | `③` | named coverage |
|---|---|---|---|---|---|
| **`recordKey @ (fun c => recordSupplyFast ++ deepenCellSupply c)` at `selNodeLazyHC`** (`RecordDeepenCell`) | ✅ **runnable and measured** — `canonFormFast`/`costFast`; `C₅` **20.8 s**, `K₁,₂,₃` **50.4 s** (after `W-j`) | ✅ **global, no hypothesis** | ✅ **`69·(n+1)^13`**, every input, no flag disjunct ⚠ see the accounting caveat | ✅ **every key** | ★★★ every Tinhofer graph — **THE OBJECT `Publication.canonForm?` IS**, all three at once (`recordDeepenCell_full_fast`) |
| `recordKey @ recordSupplyFast` (`Publication.lean` today) | ✅ | ✅ global | ✅ | ❌ open | **none** |
| `key @ recordSupplyFast ++ deepenSupplyCert` at `selNode` (`RecordDeepen`) | ✅ | ⛔ **measured false** (`probe_offbranch2/3`) | — | ✅ every key | every Tinhofer graph — ⚠ **`③` only; not publishable, `①` cannot be had here** |
| `holKeyFast @ twinSupply` (`TwinFamily` §8) | ✅ | ✅ global | ✅ | — | complete multipartite, distinct part sizes |
| **`forceThenPick holKeyFast`** (`RestrictedTransport`) | ✅ | ✅ **on the class** | ✅ | ⛔ vacuous (never flags) | ★★★ every Tinhofer graph — CANONIZED |
| `holKeyFast @ deepenSupply`, blind (`TwinFamily` §10) | ✅ | ❌ | ✅ | ✅ | every Tinhofer graph (*answers*) |
| **`guard (forceThenConsume holKeyFast deepenSupply)`** (`DeepenTransportOn` §7) | ✅ | ✅ `①a` global, `①b`/`①c` **on the class** | ✅ global | ✅ | ★★★ every Tinhofer graph — **option (v)** |
| `guard (forceThenConsume lookaheadKey deepenSupplyGuarded)` (`DeepenCertified`) | ❌ | ✅ global | ✅ | ✅ | every Tinhofer graph — **option (i)** |
| `orbKey @ deepenSupply` (`TwinFamily` §9) | ❌ | ❌ | ❌ | ✅ | every Tinhofer graph |

⚠ Rows 3 and 5 are the two publishable Tinhofer-coverage objects and they differ in *kind*: row 3
**canonizes and never flags** (so its `③` is vacuous); row 5 **keeps the honest flag** and carries `③`.
Rows 4, 6, 7 are the record of how it got there — row 4 is still the strongest *blind* `Residue.Handled`
statement (every key), rows 6–7 are `noncomputable` and **must not appear in a published statement**.

### Measured evidence (all in `scratchpad/`, all reproducible)
| probe | result |
|---|---|
| `probe_w1_multipartite.py` → `probe_w1_reduced_n16.out` | **1766 graphs, 0 failures, 0 unknowns, 0 truncations, 14 levels** |
| `probe_w1_cellshape.py` | Claim S — the two-case cell decomposition, 0 violations / 248 graphs |
| `probe_w1_cographs.py` | **cographs REFUTED**, 18 failures, minimal witness `K₃ ⊔ C₄` (now the Lean non-vacuity witness) |
| `probe_verdict_invariance.py` | ★ the **all-anchor** deepen harvest partition **= the true `Aut`-orbit partition, and transports, 17/17** (multipedes, CFI m = 8–14 plain+twisted, rigid multipedes) ⟹ `OrbitComplete` measured true well beyond `Tinhofer` |
| `probe_certkey.py` | *certified-below ⟹ invariant cert*: **0 counterexamples**. ★ But **uncertified** reps give non-invariant certs (CFI m=10 over-splits 7 vs 6) |
| `probe_selfsep.py` → `probe_selfsep.out` | ⛔ *"mixed orbits identify each other"* **refuted as the explanation** — `circ(5)` is exact with M1 15/20, M2 10/20. ⚠ rigid-multipede rows are **vacuous** passes (`non-vacuous-x = 0/4`) |
| `probe_union_need.py` → `probe_union_need.out` | ★★ **BAD-BIG = 0, covered-by-§5 = Y, orbit-uniform = Y on 13/13** ⟹ **no union phenomenon to prove**; and an empirical confirmation of `goodAnchor_transport` |
| Lean `#eval` (2026-08-04) | the **record object answers** on `C₅ C₆ P₅ K₅ 3K₂ K₁,₂,₃ K₃⊔C₄` (7/7) ⟹ no falsifier of `③` at the record object; option (ii) is open, not dead |
| Lean `#eval` (2026-08-08) — **the published object** | `RecordDeepenCell.canonFormFast` answers on `K₂`, `C₅`, `K₁,₂,₃`; `costFast` = **1606 / 5 212 728 / 20 321 716**, wall **— / 20.8 s / 50.4 s** (after `W-j`; 34 s / 87 s before it — the *billed* values are unchanged by `W-j`). It also answers on **`K₃ ⊔ C₄`**, the residual witness, which is expected: `③` bounds what is *proved*, not what the object can do. Reproduce with a two-line file: `import ChainDescent.RecordDeepenCell` then `#eval (RecordDeepenCell.canonFormFast (n := 6) (TwinFamily.mpAdj TwinFamily.part123)).isSome` and the same at `costFast`; run `lake env lean <file>` from `GraphCanonizationProofs/`. ⚠ At the `Showcase` names instead, copy `Publication.lean` and append the `#eval`s — it is not a library module, so `import Publication` fails |
| lazy vs eager vs node-global (2026-08-08) | `K₁,₂,₃`: lazy **20 321 716 / 87 s** · eager cell-indexed 38 212 276 / 210 s · node-global `selNodeFast` 25 346 020 / 148 s ⟹ **2.4× / 1.7× faster**, 20 % less billed than node-global. ⚠ Only 1–2 non-singleton cells exercised |
| **`probe_w2_asymbase.py` → `probe_w2_asymbase.out` (W2 item 3b, 2026-08-10)** | ✅✅✅ **THE ITEM-3a BOUND IS AN ARTIFACT OF BASE SYMMETRY, AND THE LAYER THEOREM IS MEASURED TRUE.** Exact `Aut(base)` by backtracking; gauge verified edge-by-edge; ⚠ **plus a descent walk** — every non-singleton cell re-measured at each reached node, gauge filtered to the χ-preserving elements. Base 1-WL **discrete** (asym `m=7`, `m=8`) ⟹ **every** cell is a **single gauge-orbit** at the root (21/21, 26/26) **and at all 4 walk levels** ⟹ `CellOrbitAt` for `kernelSupply`, which is **inside `recordSupplyFast`**, and `CellOrbitAt` has **no guard** ⟹ **fires today**. **Frucht** (cubic, `\|Aut(base)\|=1`, 1-WL coarse) ⟹ blocks **=** gauge-orbits (12=12, 18=18) ⟹ the `reps ≥ 2` bound **vanishes**; firing is a **key** question, **never blocked**. `K₄` control ⟹ ⛔ blocked at all 4 levels. ⟹ *solve the CFI part, hand back the base* | |
| **`probe_w2_linear.py` → `probe_w2_linear.out` (W2 item 3a, 2026-08-09)** | ★★★★ **A GAUGE CAN NEVER MAKE A CELL MIXED** — it is a **subgroup of `Aut`**, so it only merges. Exact, no search, every gauge element **verified edge-by-edge** first: at every CFI root **no `Aut`-block is a single gauge-orbit** (gadgets 8 gauge-orbits vs 3 `Aut`-blocks; wires 12 vs 3; `K₄` 4 vs **1**; `C₆` 12 vs **1**) ⟹ reps ≥ `\|block\|/\|gauge-orbit\|` **≥ 2 everywhere** ⟹ **the gauge alone cannot fire a CFI root cell** (a counting fact). ⚠ **2026-08-10:** the bound assumes supply-orbits = gauge-orbits and **all four witnesses have a symmetric base** (`\|Aut(base)\| = 12, 12, 24, 12`), so the stronger *"no key of any kind"* is NOT what was measured. The extra merging is **BASE** automorphism structure. ⟹ **CFI-over-cubic is NOT an instance of the target claim**; its home is the **rigid** case | |
| **`probe_w2_keysplit.py` → `probe_w2_keysplit.out` (W2 step (ii), 2026-08-09)** | ★★ **`holKeyFast` is STRUCTURALLY INERT at the CFI root**: the walk needs 3 pairwise-distinct **cross-cell components** and the CFI/mp7/MIXED roots have **1** ⟹ no valid walk ⟹ every `holSig` is all-1s ⟹ argmin = the whole cell. CFI root cells carry **3 Aut-blocks** each (`[12,12,8]`, `[12,6,6]` — **no singleton block**). ⟹ the CFI root rests **entirely** on the `orbKeyG guardSupply` tiebreak. ★ **Validated against Lean**: `Regression` §18's `#guard` (`G8` keeps 8) is reproduced, and the (F1) self-check (equivariant key constant on Aut-blocks) never fired. ⚠ Aut-blocks are a sound *refinement* of the true orbits — the safe direction here |
| **`probe_w2_resolvable.py` → `probe_w2_resolvable.out` (W2 stage 0, 2026-08-08)** | ★ `ResolvableCellAt` at every reached node (depth 1, ≤2/node): **`mp7` 14/14 Y** · `S(K5)`/`S(Petersen)` Y · **MIXED Y but the TARGET cell shut at the root ⟹ the stage-1 widening is LOAD-BEARING** · ⛔ **CFI cubic m=8 pl/tw N at the ROOT** (both root cells guard-shut, re-verified at budget 200 000; 26/26 depth-1 cells pass) · `rand multipede V=6 W=5` 0/8, `G8` 0/1. ⚠ `GoodCell` `None` never counted as a pass; single-orbit is a **positive certificate** only (union-find over `Ctx`/`canon`'s sound gens, ⛔ never `probe_orbit_oracle`) |
| `W-j` — key shared + left factor hoisted (2026-08-08) | `scratchpad/ProbeShareWalk*.lean` predicted it, `ProbeWjMeasure.lean` confirms it at the shipped definitions: `C₅` 27.6 s → **20.8 s** (1.33×), `K₁,₂,₃` 74.4 s → **50.4 s** (1.48×), **billed costs byte-identical** (5 212 728 / 20 321 716). ⚠ The *hoist* half only pays where several cells are probed, i.e. where early cells fail to fire; no small library witness has that shape |

⚠ Read each probe's header before quoting a number — the soundness discipline (positive certificates
only, `None` ≠ `False`, the orbit-reduction licence, ⛔ never `probe_orbit_oracle`) is recorded there.
⚠ The invariance/union probes measure the **ROOT branch cell only**. A family-level claim needs every
*reached* node.
⚠ **Probes must materialise colourings** (`Refine.warmRefineVec`): a `def … : Colouring n` probe ran
>10 min against ~1 min for the same measurement — standing trap #1 is live in probe code too.

### ⛔ SIXTEEN corrections a fresh reader will otherwise inherit
*(1–8 predate 2026-08-08; 9–13 were found on 2026-08-08; **14–16 on 2026-08-09, and 15–16 each
retired a route I was about to build**.)*

14. **⛔ *"All the project's F₂ machinery is on the consume side"* is FALSE** (my own line, corrected
   at source). There are **two** solvers: consume's `Kernel*` solves the **kernel** (what *can* move)
   and **runs today** inside `recordSupplyFast`; force's `Forcing*`/`Rigid*` (~4400 lines) solves
   **uniqueness + canonical RREF** (what *cannot* move) and is **gated, axiom-clean, instantiated in
   nothing**. The surviving narrow claim: the **published object's force key** has no solver
   (`compKey` is comment-only in `RecordKey.lean`/`ForcePick.lean`, verified).
15. **⛔⛔ `seedFrames` IS RETIRED and my *"only DISCRETIZING is missing"* was FALSE.**
   `RigidRefine` §9F: at a gauge automorphism `FramesEquivariant` forces the frame set closed under
   **left-mult by the whole gauge group**, a **free** action ⟹ `|frames| ≥ 2^β`. **A poly
   equivariant full-order frame set is TYPE-IMPOSSIBLE on a gauged input**; `OrderOfEquivariant` is
   target-vacuous. Equivariance and poly size are *jointly* unattainable there.
16. **⛔⛔⛔ A GAUGE CAN NEVER MAKE A CELL MIXED** (`probe_w2_linear.py`). The gauge is a **subgroup
   of `Aut`**, so it only *merges*; mixedness is the **absence** of automorphisms. Measured: at every
   CFI root **no `Aut`-block is a single gauge-orbit**, so surviving reps ≥ `|block|/|gauge-orbit|`
   ≥ 2 ⟹ **the gauge alone fires no CFI root cell** — a counting fact. ⚠ *"no key of any kind"* is
   over-strong (2026-08-10: every witness has a symmetric base; over an asymmetric base `Aut` **is**
   the gauge and the bound vanishes). The
   extra merging is **base** automorphism structure. ⟹ **CFI-over-cubic is NOT an instance of
   *"mixed due to a linear obstruction"***; the claim's home is the **rigid** case (`dim ker = 0`).
1. **rigid-seal §9.1 does NOT block W1** — corrected at source, at `00-START-HERE.md`'s W1 line, and
   at `remaining-work.md` §1T. The socket is pure-consume; a rigid obstruction *fails* its hypothesis.
2. **CAO "known false" is not a located citation** — `cao-propagation.md` §0.0a. Closure stands; the
   refutation wording does not. **Not archived** (user).
3. **W2's target is progress, not completion** — see its scope-correction block.
4. **`Deepen.orbKey` is `noncomputable`** (an `n!` guard, `instDecidableTinhoferPath = Classical.dec`),
   so `TwinFamily` §9's bridge is about a canonizer that **cannot be run**. §10 is the repaired form.
   ⚠ Distinguish this from the *hypothesis* `TinhoferGraph` being non-computable, which is correct and
   fine — a classifier need not be decidable.
5. **⛔⛔ `DeepenCertified` §7's "the theorem this track is aiming at" (the computable guard
   `CertifiedG deepenSupply`) IS CIRCULAR, not a small step** — corrected at source. The sharpest
   statement: guard-open ⟹ `Tinhofer` (`tinhofer_of_certifiedG`, unconditional) and `Tinhofer`
   transports — but *"the cell is a single orbit"* does **not** give *"deepen certifies it at the
   relabelled graph"*, which is `OrbitComplete`. And `OrbitComplete` **already gives `①c` with no guard
   at all** (`deepenSupply_canonizer_of_orbitComplete`). ⟹ the guard needs the very predicate it was
   meant to avoid, and is provably invariant exactly on the class where `①` is already proved
   (`certifiedG_deepenSupply_of_tinhoferGraph`). `certPath_transport`'s own hypothesis is
   `SupplyEquivariant`, which `deepenSupply` provably lacks.
6. **⛔⛔ Never discharge a `Publication` obligation by moving it to a second object** — tried and
   reverted this session; see the `Publication.lean` state block in §2a.
7. **"Partial firing" is NOT "bad anchors"** — a cell with `k` orbits harvests `k` blocks with *every*
   anchor good (`G8`: good = 8/8, 3 orbits). The recorded `G8` single-anchor falsifier is about *which*
   orbit one anchor collapses, not about certification failing.
8. **The `17/17 exact` sweep does not, on its own, evidence a union phenomenon** — 12 of its witnesses
   have all anchors good (`orbitComplete_of_tinhofer` covers them) and the rest are all-singleton-orbit
   (`orbitComplete_of_good_or_trivial` covers them). `probe_union_need.py` is what settled that.
9. **⛔⛔ W2's route via `CascadeOracle` → `handled_of_seal` is at the WRONG OBJECT** — it lands at
   `deepMatchSupply` + the blind `Residue.Handled`, and `deepMatchSupply` is not a factor of
   `recordSupplyFast`. Following it produces a second-object discharge, which is forbidden.
   `chain-descent-cascade-oracle.md` still describes that route with no warning — banner added.
10. **⛔⛔ And `CellIsOrbit kernelSupply` at a CFI node is MEASURABLY FALSE** — the replacement route
   I recorded on 2026-08-07 was also wrong. `KernelSupply.lean`'s own header: on `mp7` the root
   gadget cell goes **28 → 7**; `kernelSupply` certifies the *gauge* and leaves the Z₇ translations
   standing. It is a gauge constructor; base symmetry is `deepenSupply`'s job.
11. **⛔⛔ `ResolvableCellAt` FAILS AT THE CFI-OVER-CUBIC ROOT** (measured, budget 200 000, `False`
   not `None`) while 26/26 depth-1 cells pass. ⟹ the *consume* side cannot take that node — **which
   is the architecture working**: the root cells are mixed-orbit, force's domain.
   ⛔ ~~CFI coverage is a force-side obligation (Track R, suspended). Do not plan W2 around
   CFI-over-cubic.~~ **STRUCK 2026-08-08 (later), user re-affirmation** — force is *where CFI is
   meant to land*, W2 is a **layer** theorem (*solve the CFI part of every CFI graph*), and the
   `mp7` retarget is retracted. The measurement also never modelled `recordKey`/`recordSupplyFast`,
   so it does not bound the **published object**. See §2 W2's re-affirmation block.
12. **⛔⛔ The recorded `②`-tightening advice is wrong** — the harvest-`|cell|²n⁴` refinement,
   `goodCellCost`'s inner `n⁶`, `holKeyFast`'s `n⁵` and per-node supply billing **all leave 13 / 69
   unchanged**. `costConst` *is* the bound polynomial at `n = 1`; `costDeg` is set by one term. The
   only lever is `Deck2.deck2Supply`'s declared charge (→ 11 / 65).
13. **⛔ "The canonizer flags on most interesting inputs" is FALSE** — it answers on every tested
   input including the residual witness `K₃ ⊔ C₄`. Say *"has not yet been **proven** on most
   interesting inputs"*. This is by design; see the START-HERE block's caveat 3.

### ⚠ WHAT IS *NOT* RECORDED ANYWHERE ELSE — read before re-deriving
* `rootCol` does **not** kernel-reduce: `decide` on `rootCol kc 0 = rootCol kc 3` gets **stuck** (trap
  #3). The way round it is `RestrictedTransport.SigRegular` — state regularity as the *multiset of
  incident values*, which is `decide`-able because no descent object appears in it.
* `②` was **not** blocked at `deepenSupply`: it bills a **declared flat `n⁶`**, so `supplyCost … ≤ …` is
  `le_rfl`. The old memory note calling it a "T2 debt, prose only" was wrong.
* Appending a supply to the record is mechanically supported (`cellIsOrbit_append_left`,
  `gensEquivariant_appendSupply`, `certPath_append_left`); the real cost is recomputing
  `costConst`/`costDeg` (53 / 13).

### ▶▶ PUBLICATION REWIRING — the record of how it was scoped (read the boxed RETRACTION below first)

> ⚠ **This subsection is PROVENANCE.** Its conclusion ("option C: showcase a second object") was **acted
> on and then reverted** — see the boxed retraction further down, and the `Publication.lean` state table
> at the top of §2a for where things actually stand. The *scoping* below is still accurate and is why
> the residue had to be reshaped; only its recommendation is void.

**What the two `sorry`s needed (both were open at the time).** Both are blocked on the *same* thing first: `UnhandledResidue` is
`residueNonSchurian ∨ residueHiddenJohnson ∨ residueRigidObstruction`, and all three are
`opaque … : Prop`. An opaque `Prop` with no definition can be neither proved nor refuted, so **both**
`residue_if_flag` and `unhandledResidue_nonvacuous` are unprovable *in principle* as written (the file's
own STATUS says this). Step 1 of any wiring is therefore: **define the atoms.**

W1 supplies a real definition for exactly one of them:
**`residueRigidObstruction n G := ¬ TwinFamily.TinhoferGraph G`** — which unfolds, via
`schurianAt_iff_no_rigidObstruction`, to *"some individualization-reachable colouring carries a rigid
obstruction"*. Structural, iso-invariant, algorithm-independent: it passes the firewall. (D0 the file
already calls a modelling gap whose end shape is to drop it; D1 is Route C / Cameron territory, §3
suspended — neither can be defined honestly now.)

**✅ `unhandledResidue_nonvacuous` is now UNBLOCKED** — `RestrictedTransport` §7's
**`tinhoferGraph_nonvacuous`** is exactly its shape at the structural predicate:

| theorem | statement |
|---|---|
| `rootCol_const_of_sigRegular` | a signature-regular graph refines to **one cell**. ⚠ Needed because `rootCol` does **not** kernel-reduce — `decide` on `rootCol kc 0 = rootCol kc 3` gets stuck (trap #3); regularity sidesteps evaluation entirely |
| `triAt_of_relabel_eq` | the triangle count at a vertex is an `Aut`-invariant |
| **`not_tinhoferGraph_kcAdj`** | ★★★ **`K₃ ⊔ C₄` IS NOT TINHOFER** — 2-regular so the root is one cell holding `0` and `3`; `0` lies on a triangle and `3` does not ⟹ no automorphism links them |
| **`tinhoferGraph_nonvacuous`** | ★★★ the class is **inhabited** (multipartite) **and proper** (`K₃ ⊔ C₄`) |

★ This is the *"real unhandled instance"* the `Publication` STATUS block has wanted since the residue was
first stated. The graph is `probe_w1_cographs.py`'s minimal cograph falsifier, now a **theorem**.

> ## ⛔⛔ RETRACTED (2026-08-04) — THE TWO-OBJECT SPLIT WAS WRONG, AND IS REVERTED
>
> An earlier pass here discharged `residue_if_flag` by moving it onto a **second** object
> (`canonFormCover?`). **That is not a valid publication shape and has been reverted** (user, 2026-08-04):
>
> > `canonForm?` is not a meaningful object unless `①a` sound, `①b` complete, `①c` iso-invariant, `②`
> > poly-or-flag and `③` flag-only-on-the-residue are all properties of **the same** object. An exhaustive
> > solver and a random solver each carry half of this and together prove nothing.
>
> ⛔ **Standing steer: never discharge a `Publication` obligation by relocating it to another object.**
>
> **⛔ AND THE CLAIM THAT FORCED THAT DESIGN WAS FALSE.** It read *"no single object has unconditional `①`
> and proved Tinhofer coverage."* The truth is narrower: **no single *executable* one does yet.**
> `Deepen.deepenSupplyGuarded` (deepen's generators where `Tinhofer` holds, deferring elsewhere) already
> has **`①` with no hypothesis at all** — `Deepen.deepenSupplyGuarded_canonizer`, via the *unconditional*
> `Deepen.deepen_branchOrbit_transport_guarded` — fires exactly on Tinhofer nodes, and bills a flat `n⁶`
> either way. So a single object with `①` + `②` + `③` **already exists**; it is only `noncomputable`,
> because its guard is the `Tinhofer` predicate itself.
>
> ### ⛔⛔ THE COMPUTABLE GUARD WAS ATTEMPTED (2026-08-04) — HALF LANDS, AND THE OTHER HALF **IS** R1
>
> **✅ What landed** (`RestrictedTransport` §8, axiom-clean): **`certifiedG_deepenSupply_of_tinhoferGraph`**
> — on a Tinhofer graph the *computable* certificate `Deepen.CertifiedG Deepen.deepenSupply` is open at
> **every** individualization-reachable node. That is the **firing** half: a computable-guard supply defers
> nowhere on a Tinhofer graph, so it answers there.
>
> **⛔ What does NOT land, and why — a quantifier asymmetry.** `CertPath` walks **one**
> `chooseIdK`/`finRange`-head path, but each of its levels demands `CellIsOrbit deepenSupply adj ψ`, i.e.
> deepen connects **every pair** of ψ's branch cell. `exec_recovers_refgen_on_cell` supplies one pair from
> `hAmen x hx` — the path of the anchor `x` — so a level needs `TinhoferPath` from **every** anchor of ψ,
> which is exactly `Deepen.Tinhofer adj ψ`. Path-local `Tinhofer adj χ` says nothing about a *deeper* ψ's
> other anchors. ⟹ **`Deepen.Tinhofer adj χ → CertifiedG deepenSupply adj χ` does not hold**, so the
> computable guard is **not** provably equivalent to the `Tinhofer` guard, and `deepenSupplyGuarded`'s `①`
> proof does not transfer. §8 above closes the implication only at the **closure** hypothesis
> `TinhoferGraph`, which is not what the guard has available.
>
> **⛔⛔ AND `DeepenCertified` §7's framing is corrected**: it presents the computable guard as a bounded
> next step, but on inspection it reduces to **R1**. `①`'s mixed case needs *"the guard is open at
> `(σ adj, σ χ)` whenever it is open at `(adj, χ)`"* — i.e. **deepen's ability to certify is
> relabelling-invariant**, which is R1's content. Every computable candidate guard is defined from deepen's
> own output and so inherits its index-dependence; the guards that *are* invariant (`Tinhofer`,
> `SchurianAt`) are precisely the noncomputable ones. **Do not re-scope this as "small".**
>
> ### ▶ THE OPTIONS THAT REMAIN (user's call)
> | | object for `canonForm?` | `①` | `②` | `③` | executable |
> |---|---|---|---|---|---|
> | **i** | `guard (forceThenConsume holKeyFast deepenSupplyGuarded)` | ✅ hypothesis-free | ✅ flat `n⁶` | ✅ Tinhofer coverage | ❌ guard is the `Tinhofer` predicate |
> | **ii** | keep the record object | ✅ | ✅ | ❌ open | ✅ |
> | **iii** | R1 (`SameOrbits deepenSupply Ref`), then the computable guard | ✅ | ✅ | ✅ | ✅ |
>
> **i** is ~30 lines and gives all five properties on one object *today*, at the cost of executability —
> which for this project is a real cost and must be stated, not buried. **iii** re-opens suspended
> research. **ii** is the status quo.
>
> ### ▶ OPTION **iv** ADDED (2026-08-04, later) — append a proved-covering equivariant supply to the record
> | | object for `canonForm?` | `①` | `②` | `③` | executable |
> |---|---|---|---|---|---|
> | **iv** | `recordSupplyFast ++ twinSupply` | ✅ unconditional | recompute numerals | `¬(Simple ∧ RootTwins)` | ✅ |
> | **v** | `guard (forceThenConsume holKeyFast deepenSupply)` | ✅ `①a` uncond.; `①b`/`①c` **on the class** | ✅ | `¬TinhoferGraph` | ✅ |
>
> ## ✅✅ OPTION **v** IS NOW FULLY BUILT — `ChainDescent/DeepenTransportOn.lean` (2026-08-04, gate **113 modules / 208 s**)
>
> **`DeepenTransportOn.deepen_object_package`** — one **executable** object,
> `Stall.guard (forceThenConsume holKeyFast deepenSupply)`, carrying all four obligations:
>
> | | what | source |
> |---|---|---|
> | `①a` | sound, **unconditional** | `Descend.soundOpt_canonForm?` |
> | `①b`/`①c` | complete + flag-invariant **on the Tinhofer class** | `canonizes_on_tinhofer_deepen` |
> | `②` | explicit polynomial, **unconditional, every input** | `SupplyCost.descentCost_guard_mixed_le` — the guard is a single path by construction, so no hypothesis |
> | `③` | flag ⟹ the input is **not Tinhofer** | `TwinFamily.not_tinhoferGraph_of_flag` |
> | — | never flags on a Tinhofer graph | `TwinFamily.answers_of_tinhoferGraph` |
>
> **Method: the `RestrictedTransport` move, applied to the guarded mixed resolver.** Its §1–§2.1
> (`TransportOn` / `NarrowTransportOn` / `descend_transport_on` / `isoInvariantOn` / `complete_on` /
> `flag_iso_invariant_on`) are **resolver-generic** and were reused verbatim; what was missing was the §3
> contract discharge for `guard (forceThenConsume …)`. Three pieces, and **only the third touches the
> supply**: (i) the covering half is *unconditional* — `Consume` verifies every candidate, so a discard is
> automorphic to the kept branch (`coveringOfAtOn_guarded`); (ii) the forced set transports from
> `KeyEquivariant` alone; (iii) the **flag** must fire on both sides together
> (`stallEquivariantOn_forceThenConsume`), and that is exactly what `OrbitComplete` buys.
>
> ⚠⚠ **The honest reading of `①b`/`①c`** — state it, do not bury it: completeness is proved for pairs whose
> **left** input is Tinhofer. Off the class the object is still sound (its output is a genuine relabelling),
> but two non-isomorphic non-Tinhofer graphs are not proved to receive different forms. **That is the whole
> trade against option (iv)**, which keeps `①` unconditional but weakens the residue from `¬Tinhofer` to
> `¬(Simple ∧ RootTwins)`. The decision is now a clean either/or between two objects, one of which is fully
> built.
>
> ▶ **To widen (v)'s class, supply a wider `C`**: `canonizes_on_orbitComplete` asks only for
> `RelabelClosed C` and *"`OrbitComplete` at every reached colouring"*. `DeepenComplete` §5's
> **good-or-rigid** weakening is what a wider instance should target.
>
> **iv keeps `①`/`②` unconditional and closes `Publication.lean` to zero `sorry` with no new mathematics.**
> Every piece is built: `twinSupply` is computable + `GensEquivariant` + cost-bounded;
> `KernelRef.sameOrbits_appendSupply` has exactly the shared-prefix shape needed (nest twin as
> `… deck2 ++ (twin ++ kernel)` against `… deck2 ++ (twin ++ kernelRef)`); `cellIsOrbit_append_*` lifts
> coverage; `SelectNode.handledS_of_handled` + `answersS_of_handledS` land `handled_of_rootTwins` at
> `canonForm?`. ⚠ Price, to be stated not buried: `RootTwins ⊊ Tinhofer`, so the flag characterization is
> much weaker than `¬Tinhofer`. **v** is the old option A, now *provable* rather than merely costed —
> `RestrictedTransport`'s relativized spine discharges it — at the cost of `canon_complete` dropping from
> unconditional to class-conditional.
>
> ⚠ **Measured 2026-08-04** (`scratchpad/ProbeN2`-style `#eval`, materialised colourings): the record
> object **answers** on `C₅ C₆ P₅ K₅ 3K₂ K₁,₂,₃ K₃⊔C₄` (7/7), and the record supply narrows the root cell
> to 1 on the cycles where `twinSupply` fires not at all. So **no falsifier of `③` at the record object was
> found** — option **ii** is genuinely open, not dead — and `twinSupply` buys the only *proved* coverage,
> not the widest measured coverage.

### ⛔ `R1` — SCOPED AND PINNED TO ONE PREDICATE (2026-08-04). `ChainDescent/DeepenComplete.lean` (gate is now 113 modules with `DeepenTransportOn`)

An additive scoping module: no new mathematics, it **re-plumbs** what `DeepenTinhofer` proves so the open
question is a theorem statement rather than a step inside a proof.

| theorem | statement |
|---|---|
| `Deepen.GoodAnchor` | the **per-anchor** condition `TinhoferPath adj χ n (step adj χ x)` — what `exec_recovers_cell_orbits` actually consumes |
| `tinhofer_iff_forall_goodAnchor` | `Tinhofer` **is** "every anchor is good", by `Iff.rfl` |
| `exec_recovers_refgen_at` | ★★ a good anchor recovers its **whole orbit** — `exec_recovers_refgen_on_cell` with the global hypothesis removed. Free: the wrapper only ever used `hAmen x hx` |
| **`Deepen.OrbitComplete`** | ★ **THE TARGET** — *"deepen succeeds whenever success is possible"*: its verified generators realise the whole `IsColAut`-orbit relation on the branch cell |
| `orbitComplete_of_tinhofer` | `Tinhofer ⟹ OrbitComplete` — ⚠ the **only** sufficient condition this route gives |
| `branchOrbit_transport_of_orbitComplete` | the relation transports under global `OrbitComplete` |
| **`deepenSupply_canonizer_of_orbitComplete`** | ★★★ **`①c` for the RAW `deepenSupply` from `OrbitComplete` alone** — no guard, no reference supply, nothing `noncomputable`. Proving `OrbitComplete` closes `R1` outright |

**What the scoping settles.** The failsafe half is unconditional on every input
(`wordReach_imp_isColAut`), and every firing fact in deepen's pipeline is structural
(`deepen_succeeds` / `deepen_discrete` / `gate_of_discrete`). Because the leaf is discrete,
`K = coupled χ leaf` is exactly the union of the **non-singleton `χ`-cells**, so every `IsColAut adj χ`
is automatically the identity off `K` — the twist's support is not a side condition. ⟹ the entire gap is
one sentence: *at some level of the anchor's deepening the chosen sub-cell is not a single
stabilizer-orbit, and then deepen's lowest-index pick can diverge from every automorphism's image of the
anchor's pick.*

**▶ §5 (added 2026-08-04) — THE FIRST GENUINE WEAKENING, and the union argument turns out to be a phantom.**

| theorem | statement |
|---|---|
| `OrbitTrivial adj χ u` | `u` is `Aut`-**rigid**: no colour-automorphism moves it |
| **`orbitComplete_of_good_or_trivial`** | ★★ `OrbitComplete` from *"every anchor is good **or** rigid"* — **strictly weaker than `Tinhofer`**, since at a rigid vertex `ρ u = u` and the obligation is `refl` |
| `orbitComplete_of_rigid_cell` | an all-rigid cell is `OrbitComplete` with **no** goodness at all |
| **`goodAnchor_transport`** | ★ **goodness is an ORBIT property** — `tinhoferPath_transport` specialised from a relabelling to an automorphism. So the hypothesis is decided once per orbit |

**✅ AND THE DISCRIMINATING MEASUREMENT IS IN — `scratchpad/probe_union_need.py`, 13 witnesses**
(`G8`, four rigid multipedes, `MIXED`, `circ(5)`, `mp7`, CFI cubic m = 8/10 plain + twisted), root
branch cell: **`BAD-BIG = 0`** (no non-singleton orbit of bad anchors), **`covered-by-§5 = Y`**
everywhere, **`orbit-uniform = Y`** everywhere (an empirical confirmation of `goodAnchor_transport`).

★★ **So there is no separate "all-anchors repair" to prove — `exec_recovers_refgen_at` IS the union
argument.** A good anchor recovers *its own orbit and only its own*; one anchor collapses one orbit and
**which** one is index-dependent (that is precisely the recorded `G8` single-anchor falsifier); quantifying
over **all** anchors gives every orbit its own good anchor, so the union is the true orbit partition, which
is invariant. Nothing beyond §3 + §5 does any work.

⟹ **the open question is no longer "why does the union repair things" but "is every anchor good or
rigid?"** — per-orbit Schurianity along deepen's own path. True on 13/13 including every CFI witness.
⚠ Root branch cell only, as in the earlier sweeps; a family-level claim needs it at every *reached* node.
⚠ `G8` is `good = 8/8` at the root with 3 orbits — **partial firing is not bad anchors**. A cell with `k`
orbits harvests `k` blocks with every anchor good.

**⛔ What still does not weaken**: the *recovery* lemma itself. `OrbitComplete` at a **moving** `u` needs
`GoodAnchor u`; §5 only discharges the vertices that do not move.
⚠ And `branchOrbit_transport_of_orbitComplete` still wants `OrbitComplete` **globally** (`∀ adj χ`), exactly
as `deepen_branchOrbit_transport` wanted global `Tinhofer`. ▶ The natural next step is to relativize it to a
relabelling-closed class × reached colourings — the move `RestrictedTransport.lean` already performed for the
`forceThenPick` spine.

**⚠ But the measured evidence says the truth extends beyond `Tinhofer`.** `G8` is a *partially* firing
witness (so some cell on its descent is not a single orbit ⟹ not `Tinhofer`), yet the **all-anchors**
relation there was measured stable across five relabellings (`[2,2,2,2,4,4,4,4]`) where the single-anchor
relation was measured unstable. The repair all-anchors performs is invisible to a per-anchor induction.

#### ✅ THAT MEASUREMENT WAS ALREADY RUN, AND IT IS POSITIVE (found 2026-08-04 — do not re-commission it)

⛔ An earlier draft of this block proposed *"is deepen's all-anchors branch-cell partition equal to the
exact `Aut`-orbit partition at non-`Tinhofer` nodes?"* as the probe to hand over. **It exists and it
answers yes.**

| probe | result |
|---|---|
| `scratchpad/probe_verdict_invariance.py` | the **all-anchor** harvest partition of the branch cell **equals the true `Aut`-orbit partition, and transports**, on **17/17** structured witnesses — multipedes, CFI over cubic bases (m = 8/10/12/14, plain and twisted), rigid multipedes. ⟹ **`Deepen.OrbitComplete` is measured TRUE well beyond `Tinhofer`** |
| `scratchpad/probe_certkey.py` | *"certified-below ⟹ the greedy cert is iso-invariant"* — **0 counterexamples**. ★ But **uncertified** reps DO produce non-invariant certs (rand multipede V=12 W=8: 2; CFI cubic m=10: 4, where the cert over-splits **7 classes vs 6 orbits**) |

⟹ the per-anchor object (the cert) is **not** invariant at uncertified anchors, while the
union-over-anchors **relation** is exact anyway. **The all-anchors repair is real and unexplained**, and
`OrbitComplete` — not a partial-relation invariance theorem — is the right target. It wants a **union
argument over anchors**, which is exactly what `DeepenComplete`'s per-anchor induction cannot see.

#### ⛔ AND THE "MIXED ORBITS IDENTIFY EACH OTHER" MECHANISM IS *NOT* THE EXPLANATION — `scratchpad/probe_selfsep.py`

User hypothesis (2026-08-04): the repaired cells are mixed orbits where *individualizing any member
reveals and separates its own orbit-mates out*, so replay from a non-mate cannot follow the anchor's id
sequence and yields no candidate. Measured at the root branch cell, per member `x`, with
`child = refine(indiv(col, x))`:

* **M1** — `child` separates `x`'s own orbit from the rest of the cell;
* **M2** — `child` exposes the whole orbit structure of the cell.

**The mechanism is widespread but not sufficient as an explanation.** M1 is full on `G8` (8/8, orbits 3),
`MIXED`, rand multipede V=6 W=5, and **every CFI witness** (32/32, 40/40, 48/48) — but **`circ(5)`
multipede has `harvest-exact=Y` with M1 only 15/20 and M2 only 10/20**, on a cell where all 20 members are
non-vacuous. So exactness survives where the mechanism fails ⟹ **M1 does not explain the repair.**

▶ **What it may still be worth:** nothing measured *refutes* M1 as a **sufficient** condition (every
M1-full witness is exact), and M1 is poly and decidable — one `Deepen.step` per cell member — so it is a
candidate **sound-but-incomplete guard**, strictly weaker than `Tinhofer` and strictly stronger than
nothing. ⚠⚠ **But the sweep cannot confirm sufficiency: it contains no `exact=N` witness at all**, so
"M1 ⟹ exact" is untested in the only direction that would discriminate. Testing it needs a witness where
the harvest is *not* exact, and 17 + 13 witnesses have failed to produce one.

⚠ **Do not read the rigid-multipede rows as evidence**: `rand multipede V=8/10/12` have `|C| = 4` with
**4 singleton orbits**, so `non-vacuous-x = 0/4` — M1 passes there with nothing to separate.
⚠ Reference partitions come from `Ctx`/`canon` (min-over-cell exhaustive), never `probe_orbit_oracle`
(recorded **wrong** — it errs by merging). `probe_selfsep.py` adds a soundness cross-check the recorded
instrument lacks (cert-classes of explored vertices must agree with the generator orbits, else the
partition over-splits and an `exact=Y` verdict would be meaningless); no witness tripped it.
>
> ### ▶ (SUPERSEDED) the step as originally scoped — a COMPUTABLE GUARD, believed *not* R1
> `DeepenCertified` §7 names this as "the theorem this track is aiming at": guard on
> **`Deepen.CertifiedG Deepen.deepenSupply`** — an orbit BFS over deepen's own verified generators, hence
> computable — instead of on `Tinhofer`. Two directions:
> 1. `CertifiedG deepenSupply adj χ → Tinhofer adj χ` — `Deepen.tinhoferPath_of_certPath`. The two
>    predicates walk the **same** `chooseIdK`/`finRange`-head path, differing only in the per-level test
>    (`CellIsOrbit S` vs `CellSingleOrbit`), so this direction is close to immediate.
> 2. `Tinhofer adj χ → CertifiedG deepenSupply adj χ` — deepen certifies its own canonical path at a
>    Tinhofer node, level by level from `deepen_branch_orbit_iff_aut`. **This is the real content.**
>
> With both, the computable guard is *equivalent* to `Tinhofer`, `deepenSupplyGuarded_canonizer`'s `①`
> proof transfers verbatim, and `canonForm?` can be repointed at a **single executable object carrying
> `①`+`②`+`③` with Tinhofer coverage** — the intended statement.
>
> ### ✅ What survived the revert (all still proved, all object-independent)
> * `residueRigidObstruction G := ¬ TwinFamily.TinhoferGraph G` — a **definition** replacing three
>   `opaque` atoms, which had made *both* ③ obligations unprovable in principle. D0/D1 **dropped**, not
>   kept: an opaque disjunct re-breaks non-vacuity's handled half. ⚠ Do **not** add
>   `∨ NonLinearRigidObstruction` until W2 gives it content.
> * **`unhandledResidue_nonvacuous` — DISCHARGED**, axiom-clean, from `tinhoferGraph_nonvacuous`.
>   Independent of the object question, so the revert does not touch it. `Publication` is at **1** live
>   `sorry` (was 2).
> * `canonizer`'s cost conjunct is now **unconditional** — `canon_poly_or_flag` is proved on its LEFT
>   disjunct, so the residue escape was never needed and carrying it invited the reading that the cost
>   claim depends on the residue.
> * **No citation axiom is consumed by any theorem in the file.** The 8 are retained for W2/Route C; the
>   paper must say that rather than present them as the trusted base of what is proved.
>
> ⚠ **The residue is an OVER-APPROXIMATION.** A CFI graph is not Tinhofer, yet its obstruction is linear
> and belongs to the rigid resolver. `residue_if_flag` stays true (a superset on the right of an
> implication only makes it easier); **W2's job is to NARROW it, not enlarge it.**

**⛔ `residue_if_flag` IS STILL OPEN at `canonForm?` — the object analysis below is retained as the record
of how the wrong turn was taken; the correct resolution is the computable guard above, not option C.**
It asks for *flag ⟹ `UnhandledResidue`* at **`Publication.canonForm?` = `recordKey @ recordSupplyFast`**.
"Flag ⟹ ¬Tinhofer" is proved only at `holKeyFast @ deepenSupply`. Getting it at the record object needs
*"Tinhofer ⟹ the record answers"*, i.e. the record supply certifies Tinhofer cells — **not proved, and
it is the consume-completeness question.** Three ways out:

| | change | gains | costs |
|---|---|---|---|
| **A** | point `canonForm?` at `guard (forceThenConsume holKeyFast deepenSupply)` | `residue_if_flag` real + structural; `②` real | `canon_complete` / `flag_iso_invariant` drop from **unconditional** to **conditional on Tinhofer** — a downgrade of the artifact's strongest claim |
| **B** | point it at `forceThenPick holKeyFast` | `①` on the class | ⛔ **`residue_if_flag` becomes VACUOUS** — that object never flags; and off the class it *answers* with a possibly non-canonical form, trading the honest flag for a silently wrong one. **Do not do this.** |
| **C** | keep `canonForm?` = record; showcase a **second** named object for coverage | nothing weakened; `③` graded exactly as the file's own STATUS prescribes — ③a `flag ⟹ ¬HandledS(record)` (already proved, `Select.not_handledS_if_flagS`) at the record, ③b `flag ⟹ ¬TinhoferGraph` (structural) at the deepen object; non-vacuity ✅ | the paper showcases two objects and must say so plainly |

▶ **RECOMMENDED: C.** It is what `Publication.lean`'s STATUS already prescribes ("target the graded
pair"), it keeps `①`/`②` unconditional, and W1 supplies the first genuine ③b. **User's call — not
started.**

>  ▶▶ **2026-08-07 — THE ACTIVE PLAN IS `docs/chain-descent-percell-plan.md`, REWRITTEN.** Keeps
>  `Publication.canonForm?`'s fused object. **Diagnosis, sharpened and measured:** `deepenSupply` is
>  the only **pair-anchored** supply, but `SelectNode.cellNarrow` reads a single **node-global**
>  `verified` list and probes every cell against it — so a cell with no descent of its own is judged
>  by automorphisms harvested elsewhere, and **that verdict is not relabelling-invariant**
>  (`scratchpad/probe_offbranch2.py`: CFI m=8/10, depth 1, off-branch count `(1,1)` vs `(2,)`, with the
>  **guard OPEN on both sides** — `probe_offbranch3.py`). Fix = make consume **cell-indexed and lazy**,
>  which is the architecture's own description. Measured to hold: `probe_offbranch5.py` 9/9
>  GUARD-INV ∧ COUNT-INV, 7 rows non-vacuous; and restriction costs **nothing** (`A-only = 0` over
>  **646** cells, user probe). ⛔ **RETRACTED from the 2026-08-06 version: the "all-cells conjunction
>  guard"** — that followed only from keeping the node-global list. ⛔ Also retracted as evidence:
>  `probe_offbranch.py`'s root-only 30/30 pass (the falsifier is at depth 1; every earlier sweep,
>  17/17 and 13/13 included, shares that root-only scoping). ★ The structural point: a shut guard emits
>  `[]`, so the count is `|cell|` on both sides automatically ⟹ **only the guard's VERDICT must be
>  invariant**, never the harvest — no completeness of deepen-as-an-orbit-oracle is needed anywhere.
>  The **pair caveat** is retained but **demoted to `pairStep`'s own scoping** (plan §9): `pairStep`
>  builds no supply and is decoupled from the critical path.

### ▶ Live decisions, none started

> ## ★★★ 2026-08-05 — **OPTION (vi) EXISTS AND DOMINATES (iv) AND (v). THE EITHER/OR IS OBSOLETE.**
>
> **`ChainDescent/DeepenGuardComplete.lean` (gate 114 modules / 230 s, all 18 decls axiom-clean).**
>
> **`Deepen.tinhofer_iff_certifiedG : Tinhofer adj χ ↔ CertifiedG deepenSupply adj χ`** — deepen's own
> **poly, decidable** certificate is not merely sound (`DeepenGuard` §3) but **complete**. Hence
> `certifiedG_transport`: the guard is relabelling-invariant **with no `SupplyEquivariant`**, routed
> through `tinhofer_transport` instead of through the supply. Hence `deepenSupplyCert`, a
> **computable** supply definitionally equal to `deepenSupplyGuarded` (`deepenSupplyCert_eq_guarded`),
> and **`deepenSupplyCert_canonizer` = `①` with NO hypothesis at a COMPUTABLE object**.
>
> ⛔⛔ **This REFUTES `DeepenCertified` §7's recorded blocker** (*"`Tinhofer adj χ → CertifiedG
> deepenSupply adj χ` is not available … making it executable is `R1`, not a wiring step"*). The note
> assumed one anchor's path is weaker than every anchor's path at a deeper `ψ`. It is not: the level
> above `ψ` asserts `CellSingleOrbit`, and goodness is an **orbit property**
> (`DeepenComplete.goodAnchor_transport`, landed *after* §7 was written), so one member's path spreads
> to the whole cell (`tinhoferPath_spread`) and the fuel is restored by the `ncol` measure
> (`tinhoferPath_fuel_lift`). §7 is now marked provenance in-source.
>
> **What (vi) gives that (iv) and (v) do not:** `①` **unconditional** (not on a class) **and** residue
> exactly `¬Tinhofer` (not weakened) at **one computable object**. (iv) traded residue for global `①`;
> (v) traded global `①` for residue. (vi) pays neither.
>
> ★ **MEASURED 2026-08-05** — guard OPEN on `C₄ C₅ C₇ P₅ G₈ wcyc9 t3 core6 vfold2 fold4`; **SHUT** on
> the constructed falsifier **`C₃ ⊔ C₃ ⊔ C₄`** (2-regular ⟹ 1-WL merges the root into one 10-cell;
> after individualizing an anchor the untouched `C₃ ∪ C₄` cell has **two** stabilizer orbits). There
> the raw supply emits **42** candidate generators and `deepenSupplyCert` correctly emits **0**, and
> the relabelled copy agrees ⟹ **residue non-vacuous, guard non-trivial, invariance confirmed.**
>
> ⚠⚠ **THE ONE HONEST GAP IN (vi) IS `②`, AND IT IS REAL.** `deepenSupplyCert` inherits
> `deepenSupplyGuarded`'s declared cost `n⁶`, which prices deepen but **bills none of the certificate**
> (`≤ n` anchors × `≤ n` levels × one `CellIsOrbit` BFS ≈ `n⁸`). That is exactly the 2026-07-14
> *"`Key`/`Supply` were cost-free ⟹ `②` is unfalsifiable"* finding. **Do not claim `②` for (vi) as it
> stands.** The fix is mechanical and scoped: give `deepenSupplyCert` an honest cost, prove
> `Consume.gens` equality (not full supply equality — `①` reads only `verified`), and re-run the
> branch-orbit transport; `DeepenGuard.certPathCost` + `certPathCost_le` already bound the guard.
>
> **`R1` is untouched and still open.** What closed is the strictly weaker question of whether deepen's
> certificate is *complete* for `Tinhofer`. Global `OrbitComplete` is still not proved.

* **⛔ THE ONE OPEN DECISION — which object `Publication.canonForm?` should be**, i.e. how to close
  `residue_if_flag`. Five candidates, table in §2 W1's *"THE OPTIONS THAT REMAIN"* block. **Superseded
  by (vi) above on the mathematics; the remaining choice is whether to pay (vi)'s `②` bill.** The
  prior either/or, for reference:
  * **(iv)** `recordSupplyFast ++ twinSupply` — `①`/`②` stay **unconditional**, residue weakens to
    `¬(Simple ∧ RootTwins)`. **NOT BUILT.** *User preference, 2026-08-04.* Every piece exists:
    `twinSupply` is computable + `GensEquivariant` + cost-bounded; nest it as
    `… deck2 ++ (twin ++ kernel)` against `… deck2 ++ (twin ++ kernelRef)` so
    `KernelRef.sameOrbits_appendSupply` (shared **prefix**) applies four times; `cellIsOrbit_append_*`
    lifts coverage; `SelectNode.handledS_of_handled` + `answersS_of_handledS` land
    `TwinFamily.handled_of_rootTwins` at `canonForm?`. **The real cost is recomputing
    `costConst`/`costDeg` (53 / 13) via `RecordKey.recordKeyBound_expand`'s `ring`.**
  * **(v)** `guard (forceThenConsume holKeyFast deepenSupply)` — tight residue `¬TinhoferGraph`, but
    `①b`/`①c` are **on the Tinhofer class**. ✅ **BUILT**: `DeepenTransportOn.deepen_object_package`.
  * (i) noncomputable, (ii) status quo, (iii) R1 — see the table.
  ⚠ The trade is *not* "invariant vs non-invariant flag": (v) **proves** flag-invariance on the class and
  claims nothing off it. It is "global `①` + weak residue" vs "class `①` + tight residue".
* ~~`①` at §10 (`SupplyEquivariant deepenSupply`)~~ ✅ **CLOSED** — `RestrictedTransport.lean` relativizes
  `①` to the class instead of strengthening the supply, and `forceThenPick` then removes the supply
  entirely. **`R1` was not needed for THAT**, nor for (v) — see `DeepenTransportOn`.
* **▶ THE CHEAPEST AVAILABLE WIDENING OF (v), scoped and not started.** `canonizes_on_orbitComplete`
  takes the class as a *parameter*; instantiate it at
  `C adj := ∀ χ reached, ∀ u ∈ branches χ, GoodAnchor adj χ u ∨ OrbitTrivial adj χ u`
  (`DeepenComplete` §5). That class **strictly contains** `TinhoferGraph` — it covers the measured
  rigid-multipede cells that have **no** good anchor at all — and it is relabelling-closed: goodness
  transports by `tinhoferPath_transport`, rigidity by `Consume.isColAut_conj_iff`, reachability by
  `RestrictedTransport.reaches_transport`. No new mathematics; nothing downstream changes.
* **Force-before-descent extension** — a *local* edit: weaken `hS : ∀ χ, P χ → SchurianAt adj χ` to
  `SchurianAt ∨ ForceResolves`. Nothing below the socket changes.
* **W2 (CFI)**, **W3 (extraction)**, **W5 (archive)** — unchanged.

⚠ **Do NOT** re-open: per-family Lean proofs of Tinhofer membership (decided against — the bridge
covers them by citation), cographs (refuted). ⛔⛔ **`CAO 2-WL propagation` is NO LONGER on this list**
— retracted 2026-08-11 and live since; see §2a's opening box and
[`chain-descent-cao-carrier-falsifiers.md`](./chain-descent-cao-carrier-falsifiers.md).

---

## 3. SUSPENDED — do not start these

Recorded so a future reader knows they were closed by decision, not forgotten. Their docs
stay in place as the record of what was learned.

| Item | Doc |
|---|---|
| Track R: rigid seal P2 (recover-core read), P3 `AggFaithful`, P3-ring `Z_{2^k}`, P4 | `chain-descent-rigid-seal.md` §8.2 |
| Track W2: the L4 obligation, the solvable corner | `chain-descent-w2-solvability-route.md` §3b |
| ⛔⛔ ~~CAO propagation at 2-WL~~ — **NOT SUSPENDED, retracted 2026-08-11 and live since**; §2a's opening box has the state | `chain-descent-cao-propagation.md` + **`chain-descent-cao-carrier-falsifiers.md`** |
| The 2-WL refiner swap (`n²` → `n³` per round) | same, §13.6 |
| T3 citation discharge (all 8 axioms) | `chain-descent-citation-discharge.md` |
| T5 totality assembly / `Publication`'s remaining `sorry` (now **1**: `residue_if_flag`) | `chain-descent-remaining-work.md` §1T |
| **`R1`** — now a **named predicate with a proved payoff chain and a partial discharge**, still suspended as research. Target = **`Deepen.OrbitComplete`** (`DeepenComplete` §3); proving it globally gives `①c` for the raw `deepenSupply` outright (`deepenSupply_canonizer_of_orbitComplete`) — no guard, nothing `noncomputable`. Already discharged: `Tinhofer ⟹ OrbitComplete`, and §5's strictly weaker **good-or-rigid**. Measured **true 17/17 + 13/13**, incl. every CFI witness. ⛔ Not needed by option (v), which relativizes instead | `DeepenComplete.lean`, `DeepenTransportOn.lean`, `chain-descent-deepen-supply.md` |
| F1 Smith/CRT module-level coset ordering | `chain-descent-remaining-work.md` §1F |
| W1 forms-graph poly program, Route C re-base | `chain-descent-route-c-plan.md` |
| ~~`deepenSupply` cost bound (T2 debt, prose only)~~ ⛔ **NOT A DEBT — it bills a declared flat `n⁶`, so `supplyCost … ≤ …` is `le_rfl`** (`TwinFamily.supplyCost_deepenSupply_le`). The old note was wrong | `chain-descent-remaining-work.md` §1T |
| A4 concrete computable BSGS | `chain-descent-schreier-sims.md` |

**The standing steers still apply to the finish list.** In particular: check non-vacuity
against probe data before building on a predicate; prove a pinned statement rather than
citing it (`costConst * n ^ costDeg` was false at `n = 0`); and consult
[`Archive/ChainDescent/chain-descent-steers-archive.md`](./Archive/ChainDescent/chain-descent-steers-archive.md)
before anything that looks novel — it is almost certainly a recorded dead route.
