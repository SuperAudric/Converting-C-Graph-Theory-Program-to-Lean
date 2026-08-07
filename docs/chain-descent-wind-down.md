# WIND-DOWN — the closing plan

> **STATUS: research phase CLOSED (2026-08-01). This document is authoritative for what
> remains.** Every forward-looking item in every other `chain-descent-*.md` is **SUSPENDED**
> unless it appears in §2 below. Those docs remain accurate as a *record* of what was built
> and what was refuted; they are no longer a plan.
>
> ### ▶▶ PICKING THIS UP FRESH? GO TO [§2a HANDOFF](#2a--handoff--where-a-fresh-reader-picks-up-2026-08-04).
> It carries the reading order, the gate command and its current numbers, the **`Publication.lean` state
> table**, the measured evidence, the **eight corrections you will otherwise inherit from other docs**, and
> the one open decision.
>
> **W1 is ✅ LANDED (2026-08-04)** — `TwinFamily.lean` + `RestrictedTransport.lean`, extended the same day by
> `DeepenComplete.lean` + `DeepenTransportOn.lean`. W4's go/no-go is **MET**.
> Gate **113 modules, ~208–292 s, exit 0** (`bash /workspace/scripts/build.sh`).
> **Tinhofer graphs are CANONIZED** (`canonizes_on_tinhofer`), the class is **inhabited and proper**
> (`tinhoferGraph_nonvacuous`), and `Publication.unhandledResidue_nonvacuous` is **discharged**.
>
> ⛔ **ONE OPEN DECISION, and it is the only thing between here and a finished `Publication.lean`:**
> which object `canonForm?` should be, i.e. how to close its single remaining `sorry`
> (`residue_if_flag`). **Five candidates, all costed, in §2 W1's *"THE OPTIONS THAT REMAIN"* block —
> and it is now a clean either/or between two of them:**
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
| **CAO propagation at 2-WL** (`chain-descent-cao-propagation.md`) | The target is essentially *"the one-point extension of a schurian coherent configuration is schurian."* ⚠ **Softened 2026-08-04 — see that doc's §0.0a for the citations.** The identification is exact (Muzychuk–Ponomarenko arXiv:1010.4450 §2.4 defines `Xα`, and states `Aut(X)α = Aut(Xα)`), and the literature proves schurity of one-point extensions **only per-class**, never generally. But **"known false in general" is not a located citation** — the supporting instance (Wielandt's non-schurian S-ring) refutes the target only if its base CC is schurian, which nobody has checked. The doc's own §4.3 had independently concluded it could only ever be a per-family statement, and §12.5b measures 477 nodes where the unrestricted form fails. Refuted at 1-WL by four witnesses. **Closure stands** (no route to a general theorem); the refutation wording does not. |
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

### W2 — CFI family `Handled` *(box: 2 weeks)*

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
Route: `theorem_1_HOR_cfi_oddDeg` → `CascadeOracle` → `handled_of_seal`.

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
3. the residue is non-empty and the canonizer flags on most interesting inputs.

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

## 2a. ▶▶ HANDOFF — where a fresh reader picks up (2026-08-04)

**Gate is green**: `bash /workspace/scripts/build.sh` → **113 modules, ~208–292 s, exit 0** (measured
2026-08-04; the spread is swap pressure, not a change in the work). ⚠ Use the **absolute** path — the
script `cd`s via `$0`. No `sorry`, `native_decide` or new axiom anywhere in the gated library.
**`Publication.lean` is NOT gated** (compile it standalone: `cd GraphCanonizationProofs && lake env lean
Publication.lean`); it has **exactly one** live `sorry`, `residue_if_flag`.

### ▶▶ STATE OF `Publication.lean` (2026-08-04) — read this before touching it
| obligation | state |
|---|---|
| `canon_sound` / `canon_complete` / `flag_iso_invariant` (`①`) | ✅ axiom-clean, unconditional |
| `canon_poly_or_flag` (`②`) | ✅ axiom-clean, on the **LEFT** disjunct |
| `canonizer` | ✅ axiom-clean; its cost conjunct is now **unconditional** (the residue escape was never needed) |
| `unhandledResidue_nonvacuous` | ✅ **DISCHARGED** axiom-clean (`RestrictedTransport.tinhoferGraph_nonvacuous`) |
| **`residue_if_flag` (`③`)** | ⚠ **THE ONE LIVE `sorry`** — see the boxed W1 correction in §2 for exactly what closes it |
| the 8 citation axioms | ⚠ **consumed by NOTHING**; retained for W2/Route C only — the paper must say so |

`UnhandledResidue` is now a **definition** (`residueRigidObstruction G := ¬ TinhoferGraph G`), not three
`opaque` atoms. ⛔ **Do not re-add an opaque disjunct** (e.g. `NonLinearRigidObstruction`) until it has
content: an opaque `Prop` makes the *handled* half of `unhandledResidue_nonvacuous` unprovable in
principle, which is the trap the reshape undid.

⛔⛔ **STANDING STEER (user, 2026-08-04): never discharge a `Publication` obligation by relocating it to a
second object.** `canonForm?` is meaningful only if `①a`+`①b`+`①c`+`②`+`③` are properties of **the same**
object — an exhaustive solver and a random solver each carry half and together prove nothing. A
two-object split was tried this session and reverted.

### Read in this order
1. **This document**, §1 (why closed) → §2 W1 (what landed, its boxed corrections, the **options table**,
   and the **R1 block**) → §2 W4.
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

### ⚠ SEVEN OBJECTS — do not mix them up when writing
| object | executable | `①` | `②` | `③` | named coverage |
|---|---|---|---|---|---|
| `recordKey @ recordSupplyFast` (`Publication.lean`) | ✅ | ✅ global | ✅ | ❌ open | **none** |
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

⚠ Read each probe's header before quoting a number — the soundness discipline (positive certificates
only, `None` ≠ `False`, the orbit-reduction licence, ⛔ never `probe_orbit_oracle`) is recorded there.
⚠ The invariance/union probes measure the **ROOT branch cell only**. A family-level claim needs every
*reached* node.
⚠ **Probes must materialise colourings** (`Refine.warmRefineVec`): a `def … : Colouring n` probe ran
>10 min against ~1 min for the same measurement — standing trap #1 is live in probe code too.

### ⛔ EIGHT corrections a fresh reader will otherwise inherit
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

>  ▶▶ **2026-08-06 — THE ACTIVE PLAN IS `docs/chain-descent-percell-plan.md`.** Per-cell harvest +
>  per-cell guard, keeping `Publication.canonForm?`'s current fused object. It records (a) the core
>  problem in plain terms, (b) a **wrong diagnosis I retracted** (that the fused object cannot carry
>  deepen — it can; `①` never needed an equivariant reference), (c) the cost analysis showing **no new
>  exponential and no new worst-case factor** (`Σ mᵢ² ≤ n²`), and (d) the **pair caveat**: `pairStep` is
>  indexed by orbitals, not cells, so a per-cell guard must quantify over pairs.

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
covers them by citation), cographs (refuted), CAO 2-WL propagation (§3 suspended list).

---

## 3. SUSPENDED — do not start these

Recorded so a future reader knows they were closed by decision, not forgotten. Their docs
stay in place as the record of what was learned.

| Item | Doc |
|---|---|
| Track R: rigid seal P2 (recover-core read), P3 `AggFaithful`, P3-ring `Z_{2^k}`, P4 | `chain-descent-rigid-seal.md` §8.2 |
| Track W2: the L4 obligation, the solvable corner | `chain-descent-w2-solvability-route.md` §3b |
| CAO propagation at 2-WL: §12.5a mechanism, §13 conversion gap, the `triCount` pin | `chain-descent-cao-propagation.md` |
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
