# WIND-DOWN — the closing plan

> **STATUS: research phase CLOSED (2026-08-01). This document is authoritative for what
> remains.** Every forward-looking item in every other `chain-descent-*.md` is **SUSPENDED**
> unless it appears in §2 below. Those docs remain accurate as a *record* of what was built
> and what was refuted; they are no longer a plan.
>
> ### ▶▶ PICKING THIS UP FRESH? GO TO [§2a HANDOFF](#2a--handoff--where-a-fresh-reader-picks-up-2026-08-04).
> It carries the reading order, the gate command and its current numbers, the measured evidence,
> the **three corrections you will otherwise inherit from other docs**, and the open decisions.
>
> **W1 is ✅ LANDED (2026-08-04)** — `ChainDescent/TwinFamily.lean`. W4's go/no-go is therefore **MET**.
> Remaining: W2 (CFI), W3 (extraction), W4 (write-up), W5 (archive).

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
> 4. **Coverage is `answers`, not `canonizes`, outside the twin sub-case.** Full `①` needs a
>    *certifying equivariant* supply; `twinSupply` provides it only where orbits are generated by
>    transpositions. For general Tinhofer graphs the theorem is `HandledS` ⟹ no flag.
> 5. **The `almost all graphs` claim is refinement's, not the resolvers'.** On a root-discrete graph
>    `HandledS` is vacuous — no reached non-discrete node — so Babai–Erdős–Selkow buys breadth of the
>    *answering* claim and nothing about the architecture.
> 6. **`IsColAut adj P_F = Aut_F` is prose, not a theorem** — the identification with AKRV's pointwise
>    stabilizer, on which the whole "these are the Tinhofer graphs" sentence rests. Not an `axiom`;
>    nothing in Lean depends on it; the English does.
> 7. **None of this is new mathematics** and the framing must not imply otherwise — the class is
>    known-easy (§1). The contribution is the *verified artifact and its formal coverage*.
>
> ⚠ `Publication.lean` still showcases `recordKey @ recordSupplyFast`, **not** this class. Pointing its
> theorems here means adding `twinSupply` to the record supply or proving the record supply certifies
> these cells — a change to the published object, not an addition beside it. **User decision, open.**

### W5 — archive
Freeze the repo, final README pass, presentability pass on secondary documents.

---

## 2a. ▶▶ HANDOFF — where a fresh reader picks up (2026-08-04)

**Gate is green**: `bash /workspace/scripts/build.sh` → **110 modules, ~214 s, exit 0**. 0 `sorry`
outside `Publication.lean` (which still has its 2 by design), no `native_decide`, no new axioms.

### Read in this order
1. **This document**, §1 (why closed) → §2 W1 (what landed) → §2 W4 (the go/no-go, now met).
2. [`ChainDescent/TwinFamily.lean`](../GraphCanonizationProofs/ChainDescent/TwinFamily.lean) — the
   module doc-block is written to be read first; §3 is the socket, §9 the literature bridge.
3. `PublicTheoremIndex.md` for what is proved (all `TwinFamily` rows are described).

### The three things that landed, in dependency order
| | where | what |
|---|---|---|
| socket | §3–§4 | `handledS_of_noRigidObstruction` — step-closed class + no rigid obstruction ⟹ `HandledS`. **Widening the handled region = supplying a wider `P`; nothing below re-proves.** |
| bridge | §9 | `handledS_of_tinhoferGraph` + `not_tinhoferGraph_of_flagS`. `IndivReach` is step-closed **by construction**, which is why this cost ~15 lines and raised no CAO obligation. |
| wall | §8 | `twinSupply` (computable, `SupplyEquivariant`) ⟹ `canonized_of_multipartite` = `①` ∧ answers. |

### Measured evidence (all committed, all reproducible)
`scratchpad/probe_w1_multipartite.py` → `probe_w1_unreduced_n10.out` (238 graphs, capped) and
`probe_w1_reduced_n16.out` (**1766 graphs, 0 failures, 0 unknowns, 0 truncations, 14 levels**);
`probe_w1_cellshape.py` → Claim S, 0 violations / 248 graphs; `probe_w1_cographs.py` →
**cographs REFUTED**, 18 failures, minimal witness `K₃ ⊔ C₄`.
⚠ Read each probe's header before quoting a number — the soundness discipline (positive certificates
only, `None` ≠ `False`, the orbit-reduction licence) is recorded there.

### ⛔ Three corrections a fresh reader will otherwise inherit
1. **rigid-seal §9.1 does NOT block W1** — corrected at source, at `00-START-HERE.md`'s W1 line, and
   at `remaining-work.md` §1T. The socket is pure-consume; a rigid obstruction *fails* its hypothesis.
2. **CAO "known false" is not a located citation** — `cao-propagation.md` §0.0a. Closure stands; the
   refutation wording does not. **Not archived** (user).
3. **W2's target is progress, not completion** — see its scope-correction block.

### ▶ Live decisions, none started
* **`Publication.lean` wiring** — its showcased theorems still use `recordKey @ recordSupplyFast`.
  Pointing them at this class changes the published object. **User's call.**
* **Force-before-descent extension** — a *local* edit: weaken `hS : ∀ χ, P χ → SchurianAt adj χ` to
  `SchurianAt ∨ ForceResolves`. Nothing below the socket changes. This is the natural next widening.
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
| T5 totality assembly / `Publication`'s remaining 2 `sorry`s | `chain-descent-remaining-work.md` §1T |
| F1 Smith/CRT module-level coset ordering | `chain-descent-remaining-work.md` §1F |
| W1 forms-graph poly program, Route C re-base | `chain-descent-route-c-plan.md` |
| `deepenSupply` cost bound (T2 debt, prose only) | `chain-descent-remaining-work.md` §1T |
| A4 concrete computable BSGS | `chain-descent-schreier-sims.md` |

**The standing steers still apply to the finish list.** In particular: check non-vacuity
against probe data before building on a predicate; prove a pinned statement rather than
citing it (`costConst * n ^ costDeg` was false at `n = 0`); and consult
[`Archive/ChainDescent/chain-descent-steers-archive.md`](./Archive/ChainDescent/chain-descent-steers-archive.md)
before anything that looks novel — it is almost certainly a recorded dead route.
