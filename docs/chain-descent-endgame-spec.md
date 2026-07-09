# Endgame spec — the path from here to the finished canonizer

> **What this is.** The single high-level map of *everything the project must reach* to be finished, and
> the workstreams that get there. It is anchored on the concrete compile target
> [`GraphCanonizationProofs/Publication.lean`](../GraphCanonizationProofs/Publication.lean): the "end state"
> is precisely "every obligation in that file is proven, and its `#print axioms` shows only the Lean kernel
> primitives plus named classical citations." This is a *map, not a build log* — it names the pieces and
> their dependencies, not per-increment steps. Detail-heavy pieces (the cost model, the `UnhandledResidue`
> definition) may split into their own files; pointers are left where they will go.
>
> **Companion docs.** Current frontier + what's built: [`00-START-HERE.md`](./00-START-HERE.md),
> [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md),
> [`../GraphCanonizationProofs/PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md).
> Live poly route: [`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md). Citations:
> [`chain-descent-citation-discharge.md`](./chain-descent-citation-discharge.md).

---

## STATUS (read first)

**The end state is pinned; the skeleton compiles.** `Publication.lean` states the finished theorem and its
obligations against the project's real `AdjMatrix` types, with the not-yet-built runtime objects `opaque`
and the obligation bodies `sorry`. It compiles green (`lake env lean Publication.lean`, exit 0), and
`#print axioms canonizer` currently reports `[propext, sorryAx, Quot.sound]`. **Definition of done: that
`sorryAx` is gone and the only non-kernel entries are the citation axioms.**

**Where the work concentrates.** Of the obligations, the unconditional-correctness trio (①a/①b/①c) rests
largely on *already-built* Seal-Phase substrate and is mostly assembly. The weight is in **② (poly-or-flag)**
— which requires the cost model and the "reaches-rigid ⟹ counted poly node budget" bridge, i.e. the point
where **"poly" stops being a meta-argument** — and **③ (flag ⟹ obstruction)**, which requires the
`UnhandledResidue` definition plus consuming both the Seal-Phase and IR-Phase results.

Below should be no more than one progress update entry to prevent this file from reducing to a build increment log. Other changes should be filtered into stable state documentation if needed.
**Progress (the Runtime-Phase cost model + the non-rigid correctness ARCHITECTURE have STARTED).**
Two coupled threads, both in [`chain-descent-cost-model.md`](./chain-descent-cost-model.md) STATUS + route-c-plan
§7b/§7c ([[project_confinement_lemma_2026-07-07]]):

- **The correctness architecture — witness-or-assume-VT (SUPERSEDES R1).** ① on the non-rigid residue is now a real
  algorithm: refine the flag to a **per-node** budget; a Phase-1 over-budget flag ⟹ (confinement lemma) the residue is
  primitive rank-3 ⟹ VT ⟹ assume-VT-prune-and-continue (node-4/Cameron *handled*, single-path poly; `none` only in
  rigid Phase 2). This makes the flag/budget mechanism **load-bearing for correctness** — the cost model shifted from a
  *demonstration* to a *prerequisite*. The whole non-rigid ① reduces to the **confinement lemma** (route-c §7c) —
  **CORE COMPLETE (2026-07-08), all axiom-clean:** P1 (super-poly threshold), P2 (deferral), P3 (real seal), P4 (→ Witt),
  Witt (factored) **ALL WIRED** — `ConfinementWitt.confinement_selectedCellIsOrbit_spine_witt` reduces the ①b core
  `SelectedCellIsOrbit` to ONLY named citations {G3, model=D0, `hImprim`, Witt+Liebeck}. `UnhandledResidue` atoms made
  structural (issue-#1 firewall). Detail: the CURRENT STATE block atop [[project_confinement_lemma_2026-07-07]].

- **The cost model.** Framework landed axiom-clean (`ScratchCostModel.lean`: `CostM` + `budgetedIterate` + `cost_budgetedIterate_le`),
  settling **② unconditional by construction** (all poly content in ③-forward). The **per-node cap** variant
  (`ScratchCostModelPerNode.lean`) gives ② with NO `hstep`. The instance is attached to **`defaultSpineChain`** (proven
  node bound): `spineCappedCanonizer_cost_le` proves **`cost ≤ n⁴` concretely on the real descent** (matches C#
  `16n⁴`), and the cost is **co-defined** (`ScratchCostModelCostedWarmRefine.lean`: `value=warmRefine`,
  `cost=warmRefineCost n`, not a fiat literal — the D1 seam closed).

**Correctness ① state (2026-07-08):** **①a `canon_sound` DONE** (shared object `ScratchCanonFormCapped.CanonForm.canonForm?`,
also carrying ② `descentCost_le`). **①b `canon_complete`: ← direction DONE** (`ScratchConfinementCompleteness.canonForm?_complete_mpr`,
from ①a); **→ direction = X3 = THE INDEX-FREE CUT (2026-07-08 cont.), after three dead routes.** The lex-min reduction
to `CanonFormImagesIsoInvariant` landed but that residual is **FALSE** for the current `canonForm`: `DirAssignment` `σ`
breaks ties only between *equal-colour* vertices, and individualization gives committed vertices *distinct index colours*
(`v.val`), so `σ` never re-orders them ⟹ the lex-min cannot wash out the index ⟹ current `canonForm` is genuinely not
iso-invariant when `D ≠ ∅`. **THE CUT:** commit ONE vertex at a time with an **index-free** colour, ordering the
committed set by canonical descent *level* (not `v.val`). Then the seed transports **literally** under a relabel
(`indivOne (g r) ∘ g = indivOne r`, a function equality — NOT `samePartition`), dissolving the samePartition-vs-literal
gap, and the banked `labelledAdj_rankPerm` value-lift closes it. **`ScratchConfinementX3.lean` P1–P6 all landed
axiom-clean** (`indivOne`/`indivStep1` + literal equivariance, `descentColouring_transport` cross-graph, the value-lift
`labelledAdj_rankPerm_cross`, and `ifCanon_iso_invariant_of_reconcile` for `H = π·G`) — **the invariance mechanism is
proved end-to-end (same-order)**. **(i) DONE** — `oneStepSpineChain` (`ScratchConfinementX3Spine.lean`): index-free
`SpineChain` (via `indivStepOne`+`pickOne`), `oneStepSpineChain_reaches_leaf` (termination transferred off
`defaultSpineChain`), `oneStep_canonForm_isLabelledAdj` (①a free). **(ii-a) DONE** — `oneStep_cell_refines_setIndiv`
(retained but no longer load-bearing after W2). **(ii-b) RESOLVED — the CONVERGENCE/C2-confluence framing is SUPERSEDED
(do NOT build C2); the route is the W-plan (2026-07-08).** The C# selects the *lowest cell-id* (lex-rank of WL-signature)
non-singleton cell — an EQUIVARIANT cell rule — and a FIXED schedule is iso-invariant (deferral = a different schedule
gives a different-but-valid canonical ⟹ cross-schedule confluence is NOT the target). The assume-VT descent runs one
fixed schedule, so ①b→ = **fixed-schedule iso-invariance via a per-level McKay reconciliation with an equivariant CELL
selector**. **W1 ✅** (`ScratchConfinementX3Sel.lean`, axiom-clean): equivariant `selCell`/`selCellRep` + `selCell_transport`
(literal cross-graph cell image) + `selCellRep_both_in_target`; replaces the WRONG `pickOne` (min-index, non-equivariant
cell). **W2 ✅ by GENERALIZATION** (whole confinement chain axiom-clean, 1284 jobs green): the confinement chain's
cell-selection colouring is now an abstract parameter (`χ`/`χsel`) across `ScratchNodeCountBridge`/`ConfinementP4`/`Witt`/`P3`/`Confinement`
(default `indivχ`) — instantiate `sel:=selCell`, `χsel:=` the descent's own colouring ⟹ confinement reads the descent's
colouring (matches the C#, one `WarmPartition`); the samePartition bridge is OBVIATED. **W3 🟡** (`ScratchConfinementX3Recon.lean`):
W3a ✅ (`descentPicks` + `descentColouring` link), W3c-core ✅ (`reconcile_extend` — the single-`b` accumulation crux:
`aₖ∈Stab` fixes earlier picks so one global `b` reconciles, reviving `ifCanon_iso_invariant_of_reconcile`); remaining =
W3b direct termination + the full induction folding `reconcile_extend`. **W4** = feed `hrec` to `ifCanon_iso_invariant_of_reconcile`,
re-instantiate `oneStepSpineChain` with `selCellRep`, rewire `canonForm?`/①b. The old `CanonFormImagesIsoInvariant` is ABANDONED.

**Still unbuilt for done:** **X3 W3/W4** (the ①b → piece — algebraic crux `reconcile_extend` in hand); wire the
witness-case/`nodeOf` into `singlePathDisposition_of_confinement`; discharge the confinement carriers (model=D0,
`hImprim`); assemble full ①; ③-forward (run returns `some`) + the `UnhandledResidue` disjunct *definitions* + the
Publication swap (`canonForm? := CanonForm.canonForm?` onto the FIREABLE `spineCappedCanonizerO`, once, with ③); then
**port the confinement/cost cluster into build.sh**. **Separate BONUS deliverable (option B, not on the `#print axioms`
path):** a *runnable* Lean canonizer — see [`chain-descent-executable-track.md`](./chain-descent-executable-track.md)
(output `#eval`s + ①a-sound; still slow — OPEN).

---

## 1. The end state, and the definition of "done"

The finished project is the theorem `Showcase.canonizer` (and the trio + non-vacuity guard it composes):

- **Correctness is unconditional** — for *every* graph, whenever the canonizer answers, its output is a
  complete isomorphism invariant that is a genuine relabelling of the input (never wrong). It may instead
  emit an honest **flag**.
- **Cost is conditional** — the descent runs within an explicit polynomial budget, *or* it flagged.
- **The flag is characterized** — a flag *implies* the input genuinely contains an **unhandled
  obstruction** (`UnhandledResidue`), not algorithmic weakness (`residue_if_flag`, forward only; the reverse
  is neither needed by the headline nor cleanly true — see §4.1).

**Done ⟺** all six obligations proven **and** `#print axioms` on the headline = `[propext,
Classical.choice, Quot.sound]` ∪ {citation axioms}, where every citation axiom is a theorem *proved outside
the project*. The `#print axioms` line is the machine-checkable "done" gate and the reviewer's entire audit
surface.

**THE FIREWALL (the discipline that keeps "done" honest).** An axiom in the showcase may only be a genuine
external classical result. The project's own *open frontier* must never be axiomatized — it goes inside
`UnhandledResidue` (the excluded side) or is proven. `#print axioms` cannot distinguish a real citation from
a smuggled conjecture, so the firewall is enforced by discipline: every entry in the trusted base must have
a faithful external source (§ the citation register in
[`chain-descent-citation-discharge.md`](./chain-descent-citation-discharge.md)).

---

## 1a. The architecture — TWO SEALS, ONE WALL (the organizing frame; read before §2–§5)

> Recorded 2026-07-08 as the durable high-level plan (a fresh reader should work forwards from here, not
> re-derive it). It reconciles pieces from several routes: the symmetry seal (route-c-plan), the confinement
> lemma (route-c §7c / [`chain-descent-cost-model.md`]), and the rigid solver
> ([`chain-descent-ir-blindspot-solver.md`] §11.11–§11.14). Authoritative detail lives in those docs; this is
> the map that says how they fit and what the target is.

**The one-sentence frame.** The canonizer has two domains — *symmetric* (a residue with automorphisms) and
*rigid* (trivial `Aut`) — each handled by its **own seal**, and the two seals are **mirror images that isolate
the same single wall**. `UnhandledResidue` therefore collapses from three opaque atoms toward **one named
residue**.

**Two algorithms are in play; be explicit about which is the deliverable.**
- **Algorithm A — assume-VT / confinement** (what the Lean ① *proves*, the NON-RIGID deliverable). Per-node
  budget flag; a Phase-1 over-budget flag ⟹ (confinement lemma) primitive rank-3 ⟹ vertex-transitive ⟹
  *assume-VT-prune-and-continue* — node-4/Cameron become **handled** (single-path poly, complete), `none` only in
  the rigid phase. **Lean-provable / axiom-clean**; citation base {G3, Liebeck, Witt, hImprim, D0}. Does **not**
  need Route C or any per-family form recovery.
- **Algorithm R — recovery** (what the C# main currently *runs*, and the RIGID plan's mechanism). Recognize the family,
  recover the structure (Route-C form on the symmetric side; the F₂/ring constraint system on the rigid side),
  canonicalize via the known/solved group. Empirically fast and complete, but its poly-ness is **meta**
  (per-family) — so at the Lean level it either becomes a real `cost ≤ poly` proof or falls into
  `UnhandledResidue` (the firewall forbids axiomatizing it). On the **rigid** side, recovery is the *only* option
  (trivial `Aut` ⟹ assume-VT is vacuous), so the rigid seal is built on Algorithm R.

**★ The Phase-1 deliverable is "Reaches Rigid Unconditionally" (RRU) — the handoff object Phase 2 works forward from.**
Phase 1 (Algorithm A) **never emits `none`**: a Phase-1 flag is *not* a handoff, it is the *trigger* for the assume-VT
step. A flagging residue is vertex-transitive (P1: flag ⟹ large `Aut` ⟹ VT), so the flag is always **consumable** —
assume-VT prunes the orbit, recovers the symmetry, and steps forward, *strictly consuming a symmetry each time*.
Iterating drives every input down to a **rigid** residue `R(G)`. So the Seal Phase's real deliverable is the theorem
**RRU: for every input, Phase 1 terminates at a rigid, iso-invariant residue `R(G)`** — a **proven Seal object** (per-step
soundness = `SelectedCellIsOrbit` / the confinement ①; iterated to a rigid fixpoint, plus endpoint iso-invariance), NOT
an `opaque` predicate that a Phase-2 flag certifies. `R(G)` is exactly what **Phase 2 (Algorithm R, the rigid solver)
consumes**; Phase 2 has no recovery for *its own* flag yet, so **Phase 2 is the sole source of `none`**. Corollary: ①
(correctness) and ② (`cost ≤ n⁴`, `descentCost_le`) being proven against a **total, never-`none`** object is *by design*
— Phase-1 totality is the point, not a vacuity; the `∨ none` disjunct of `canon_poly_or_flag` is reserved for Phase 2.
RRU is the true **switch-over gate**: until it is an explicit proven object, Phase 2 has nothing to forward-reference.
(Do NOT reframe RRU as "a Phase-1 flag hands a `none` to Phase 2" — that inverts the polarity; the flag is consumed, the
handoff is the *proven* rigid residue.) **The boundary is the DEFERRAL scheduler, not the flag threshold** (scoped +
resolved 2026-07-09): a cell is *consumed* (`OrbitPartition` = a path-fixing automorphism relates a pair) or a real
decision is *deferred* (`¬OrbitPartition`), sound by `real_stays_real` (`CascadeOracle.lean`); "nothing left to consume"
= **rigid = `IsBase`** (trivial residual, `card_stabilizerAt_eq_one_iff_isBase`). The flag is a *cost* mechanism confined
to the `¬IsBase` side (P2 `flag_imp_symmetric_spine`), NOT the boundary — so there is no small-Aut/trivial-Aut gap. The
substrate is all built; RRU is an assembly whose first brick is the progress lemma `¬IsBase → ∃` a consumable
`OrbitPartition` pair. Full scoping: `chain-descent-remaining-work.md` item 6 + `[[project_rru_phase_transfer_2026-07-09]]`.

**The two seals (mirror table, IR §11.12).**

| | handles | the escape | wall |
|---|---|---|---|
| **symmetry seal** `reachesRigidOrCameron` | symmetry consumption (Algorithm A / assume-VT) | "or Cameron" | `hSmallAutThin` |
| **rigid seal** `canonizesRigidResidue_or_flags` | linear-over-a-ring: CFI / multipede / `Z_{2^k}` (Algorithm R / F₂→Smith) | "or non-linear" | **= `hSmallAutThin`** |

**The target — minimize `UnhandledResidue`, do NOT concede the rigid side.** The goal is the *best* headline, not
the shortest line. Concretely:
- **`UnhandledResidue` → one named residue.** The two seals' flag floors are the **same object** (IR §11.11
  node-4 unification: the symmetry seal reduces node-4 from the rank-3 side, the rigid solver reduces the
  multipede from the high-rank side, both leave the identical **non-schurian / non-linear** residue). So the
  three `Publication` atoms (D0 non-schurian, D1 hidden-Johnson, D2 rigid) collapse toward **one** predicate.
- **`UnhandledResidue → ⊥` is exactly closing that shared wall** (`hSmallAutThin` = "small-Aut ⟹ bounded WL-dim"
  = rigid-GI ∈ P). That is the project's central open problem — **not reachable with current techniques**, but it
  has **zero constructible falsifiers**, so the honest best headline is "*poly-time complete canonizer whose only
  unhandled inputs are one named residue coinciding with a known GI-hardness frontier, for which no witness
  exists*". If the wall ever falls, `⊥` drops in for free.

**Transfer assessment (answers "does node-4/Cameron → known-solution transfer to the rigid side?").**
- **Rigid node-4 (the F₂/ring-multipede): TRANSFERS / handled.** The F₂→ring (Smith-normal-form) solver canonizes
  it — validated end-to-end (D-M0–M4) *and* for `Z₄` (IR §11.11). `Z_{2^k}` is **inside** the iterative engine,
  not the floor. Lichter's FPC+rank lower bound does **not** bind it: Lichter is individualization-free; this
  solver individualizes.
- **Rigid Cameron: likely ABSENT** (IR §11.14, conjecture-level). Hiding is abelian/linear (a CFI gauge is a
  module action); Johnson/Cameron is non-abelian; there is no non-abelian CFI. So the rigid seal's escape is
  plausibly **tighter than the symmetric one — no "or Cameron" leg at all**. Proving this tightens the headline
  and is what makes the residue collapse to one atom.
- **Residue = the shared wall** (non-linear rigid / non-schurian symmetric = rigid-GI-in-P), no witness.

**What is PARKED (genuine results, off the best-headline critical path — do not delete, do not build on for the
headline):**
- **Route C** (the four form-family *poly* Lean seals, in `build.sh`). Confinement/Algorithm A supersedes it *for
  the headline* — the non-rigid poly comes from assume-VT single-path via `exhaustiveObstruction_scheme` + **G3**,
  not from Route-C form recovery. Route C remains a real, stronger, independent poly result; it is simply not
  required by `canonizer`.
- **The C# main program's current shape.** It runs **Algorithm R with a *global* flag** and **Route-C dispatch**
  for node-4 (affine-polar + Suzuki built; alternating + half-spin `NotImplementedException`). It does **not** yet
  implement the per-node flag or the flag→VT→assume-prune hook the Lean ① proves — a real **C#↔Lean divergence**:
  the Lean is the deliverable; the C# is the testbed. To align it, the rigid work replaces the `target == fallback`
  exhaustive branch at `ChainDescent.Search target == -1` with the option-2 solver (IR §11.11–§11.12), and the
  per-node flag would supersede the global one. (Revertable if needed: C# commits "Main C# build for Route C" and
  "Connected stubs for the other graph family handlers".)

**Where each half's detail lives.** Non-rigid (Algorithm A): route-c-plan §7c + [`chain-descent-cost-model.md`] +
[[project_confinement_lemma_2026-07-07]]. Rigid seal (Algorithm R): [`chain-descent-ir-blindspot-solver.md`]
§11.11 (engine/ceiling), §11.12 (the B1–B6 / P1–P4 roadmap, user-approved), §11.13 (ring/Smith design), §11.14
(no-Cameron lead). The residue-collapse + shared wall: this section + IR §11.11.

---

## 2. The obligation map — what each needs, and what already exists

Anchored on `Publication.lean §3`. "Built" = the supporting object exists in the library; "assembly" = wiring
existing pieces; "new" = a genuinely unbuilt object.

| Obligation | Statement (informal) | Discharged by | State |
|---|---|---|---|
| **①a `canon_sound`** | Output is a relabelling of the input | `SpineChain.canonAdj` (leaf relabelling by the rank permutation) is a `labelledAdj` | **Built substrate; assembly** — once `canonForm?` is defined off the descent |
| **①b `canon_complete`** | Complete iso-invariant when it answers | `spine_branch_independent` + `warm_6_2` (direction-invariance) + `canon_sound` | **Built substrate; assembly** |
| **①c `flag_iso_invariant`** | Flagging is a class property | partition-invariant selector (`target_direction_blind` / the spine) | **Built substrate; assembly** |
| **② `canon_poly_or_flag`** | Poly-time or flag | **Cost model** (new) + the **consumption bridge** "reaches-rigid ⟹ poly node budget ⟹ ¬flag ∧ cost ≤ poly" (new) | **NEW — the main gap; where poly stops being meta** |
| **③ `residue_if_flag`** | Flag → genuine obstruction | **`UnhandledResidue` definition** (new) + `reachesRigidOrCameron_*` consumed (Seal) + IR residual characterization (IR) + citations | **NEW — gated on Seal + IR completion** |
| **non-vacuity** | Handled and unhandled graphs both exist | concrete witnesses (a forms-graph / CFI handled; a hidden-Johnson unhandled) | **NEW — small, but the anti-vacuity guard** |

**Reading of the map.** The correctness trio is close (the hard invariance work — `warm_6_2`,
`spine_branch_independent` — is banked). The distance to done lives in three *new objects*: the **cost
model**, the **consumption bridge** (②), and the **`UnhandledResidue` definition** (③). Everything else is
either built or a citation.

---

## 3. The workstreams (phase-level)

Five workstreams reach the obligations. Names are for this doc's organization only (they are deliberately
absent from `Publication.lean`, whose statements are independent of the route taken).

### Seal Phase — the symmetric-domain seal (Algorithm A), finished and reusable
The `reachesRigidOrCameron` seal is in build. For the **headline**, the non-rigid poly + completeness come from
**Algorithm A (assume-VT / confinement)**, not from Route-C form recovery — the confinement chain consumes
`exhaustiveObstruction_scheme` + **G3** (§1a). So the live non-rigid work is **finishing the confinement /
Algorithm A path** (STATUS block: X3 = the index-free cut — SpineChain-ify + `hrec` + rewire; wire
`nodeOf`/witness-case → `CertifiedSinglePath`; discharge D0/`hImprim`), *not* R1 and *not* Route C:
- **R1 (the Aut-free coordinatizer) is SUPERSEDED** by witness-or-assume-VT (§1a / cost-model §7a): assume-VT is
  single-path poly with no `Aut`-computation, so the meta-circularity R1 was fixing does not arise on the
  headline path.
- **Route C (four form-family poly seals) is PARKED** — a genuine independent result, off the headline critical
  path (§1a). Keep it in build; do not build the headline on it.
- **Cameron shrink → the symmetric obstruction atom.** On the symmetric side assume-VT *handles* Cameron when it
  is **classical** (Witt/Liebeck); the residual symmetric obstruction is the **Cameron-non-classical** case
  (hidden-Johnson / un-coordinatizable geometric, e.g. the `d = 4` GQ). That predicate **unifies with the rigid
  non-linear wall** (§1a / IR §11.11) — the two become one `UnhandledResidue` atom.
- **Consolidate the reusable core** (the recovery / forms / Gauss substrate) and prune the ⊘-superseded seal
  capstones — *before* IR builds on it, so the mess is not compounded.

Output for the endgame: a clean `reachesRigidOrCameron` object + the confinement lemma finished + the structural
symmetric-obstruction predicate (= the shared wall).

### IR Phase — the rigid mirror seal (Algorithm R)
The rigid seal `canonizesRigidResidue_or_flags` is the **mirror of the symmetry seal** (§1a): recover the
F₂/ring constraint system `H` → solve over the ring (F₂-rank → Smith normal form) → canonical coset, and *flag
non-linear*. It is Algorithm R (the only option on the rigid side — trivial `Aut` makes assume-VT vacuous).
**Reuse pricing is DONE** (§1a, not a pending spike): the seal's **group-harvest machinery does NOT transfer**
(nothing to harvest); what transfers is the **recovery philosophy + the shared forms/Gauss substrate**, and the
rigid node-4 (F₂/ring-multipede) is **handled** (validated D-M0–M4 + `Z₄`, Lichter doesn't bind). The build is
the **user-approved roadmap, IR §11.12** — do not re-scope:
- **C# (B1–B6):** productionize the `Option2Solver` (ring-general from the start, IR §11.13), wire it at
  `ChainDescent.Search target == -1` (replacing the exhaustive `target = fallback`), **verify-by-reconstruction**
  makes the succeed/flag verdict iso-invariant (B3, the soundness-critical piece), fold via harvested `σ` (B4),
  cross-checks (B5). This is also what removes the C#↔Lean divergence (§1a).
- **Lean (P1–P4):** P1 extraction-soundness (minimal forcing-circuits generate `rowspace(H)`, pure F₂/matroid,
  **do first** — standalone/Mathlib-direct), P2 forcing-model bridge (carry as a model hypothesis, discharge
  later), P3 solve + canonical-form iso-invariance (the heavy new build), P4 the capstone
  `canonizesRigidResidue_or_flags` — isolates the `LinearObstruction` hypothesis = the wall. **No new citations**
  (unlike G3 on the symmetric side).
- **Tighten the escape (IR §11.14):** prove the rigid medium admits **no hidden Johnson/Cameron** (hiding is
  abelian, Johnson is not) ⟹ the rigid escape is "or non-linear" with **no Cameron carry** ⟹ the residue
  collapses to one atom shared with the symmetric side.

Output for the endgame: the rigid seal + a structural rigid-obstruction predicate = the shared wall (§1a),
minimized toward `⊥`.

**Design note (robust success criterion).** State the IR goal as the *conditional* ("canonized or unhandled
rigid residue"), not "rigid GI ∈ P". The conditional is exactly what ③ formalizes and is robust to a
non-empty residual; "residual empty" is the optimistic case (= closing the shared wall), not the success gate.

### Runtime Phase — the Lean runtime and cost model (the biggest conceptual leap)
Builds the objects `Publication.lean` currently stubs `opaque`, and the bridge that makes ② true:
- **Define `canonForm?`** — the Lean descent model producing `Option (canonical adjacency)` (the flag = `none`).
  Much of the descent model exists (`defaultSpineChain`, `SpineChain.canonAdj`, leaf existence); this wires it
  into the `Option`-valued output and connects it to ①.
- **Define `cost`** and the **cost model** — the operation-count of the descent (# nodes × per-node work) as a
  `ℕ`, with an explicit polynomial bound `costConst · n^costDeg`. **Granularity is a decision to make early**
  (operation-count proxy, each step separately poly-size). *This piece is a candidate to split into its own
  file* — [`chain-descent-cost-model.md`] (TBD) — once its shape is fixed.
- **The consumption bridge (②/③).** Turn the *structural* seal ("the residue reaches rigid or is Cameron")
  into *runtime* statements ("¬flag ∧ cost ≤ poly", "flag ⟹ residue"). This is where "poly" stops being a
  meta-argument: reaches-rigid must imply the descent discretizes in a *counted* poly number of nodes.
- **Pilot early on the banked quasipoly seal.** `reachesRigidOrCameron_affinePolar` already carries an
  explicit base bound `O(d log p)` — the most runtime-bearing finished object in the project. Piloting the
  cost model there validates the whole Runtime-Phase approach *before* Seal/IR are finished, and de-risks the
  latest-placed, highest-risk part of the plan.

Output for the endgame: `canonForm?`, `cost`, and proofs of ①–③ modulo `UnhandledResidue` + citations.

### Publication Phase — assemble the showcase
- Wire the citation placeholders in `Publication.lean §2` to the *actual* library predicates (carried as
  hypotheses in the library; instantiated with `axiom` witnesses only here).
- Fill the obligation bodies (which may live in a separate proofs file, keeping `Publication.lean` a clean
  statement surface) by plugging into the completed library theorems.
- Confirm `#print axioms` = kernel + citations, run the firewall check, discharge the non-vacuity guard.
- The paper: pin the theorem statement (it is `canonizer`), state the granularity of `cost`, list the trusted
  base. Consider an extracted, cleaned showcase subset as the attached artifact.

### Maintenance — cross-cutting
Index freshness (`PublicTheoremIndex.md` is stale for scratch files), dead-code pruning (⊘ capstones,
superseded predicates), test hygiene (exploratory `Probe_*` out of the gating build). Slow now, often faster later.

---

## 4. Cross-cutting design artifacts (the three new objects, called out)

These are the load-bearing *new* pieces; each deserves a fixed shape now even if built later.

1. **`UnhandledResidue` — the firewall valve (the single most important definition). Its shape is now fixed;
   see §4.1.**

2. **The cost model (`cost` + the bound).** Decide granularity early; prefer an explicit polynomial over
   `∃ p : Polynomial`. Pilot on the quasipoly seal. *Split candidate:* its own file once the granularity is
   chosen.

3. **The consumption bridge.** The theorem-level connective from the structural seal to the runtime `canonForm?`
   / `cost` statements. It is the concrete meaning of "the seal implies the algorithm is correct-and-poly", and
   it is currently unbuilt — the honest measure of the gap between "we have `reachesRigidOrCameron`" and "we
   have `canonizer`".

### 4.1 `UnhandledResidue` — the fixed shape and per-atom scoping

**The design decision: define it on the reached residue, as a three-way disjunction with a non-schurian
absorber.** `UnhandledResidue G` is a property of the **residue scheme the descent reaches on `G`** — the
scheme at the deepest cell the descent cannot resolve into orbits. That scheme is an *iso-invariant of `G`*
(the spine theorems `spine_branch_independent` / `SpineChain.eq_default` make the reached residue
labelling-independent), so `UnhandledResidue` is well-defined and structural — yet it is **not** "the
algorithm flagged" (`canonForm? = none`): the flag is a distinct operational event that `residue_if_flag`
*connects* to this structural predicate. The reached-residue choice is preferred for **well-definedness +
iso-invariance** (the descent's reached residue is a canonical object of `G`), but with ③ shipping as the
**forward-only** `residue_if_flag` an intrinsic "`G` contains a hidden-Johnson section somewhere" is *also*
admissible — the reverse `residue → flag` is false either way (a contained section can be individualized
away), and forward-only never needed it. So the reached-residue choice is a definiteness preference, not
forced by ③'s shape.

The shape, now committed in `Publication.lean §1`:
```
UnhandledResidue G  :=  residueNonSchurian G  ∨  residueHiddenJohnson G  ∨  residueRigidObstruction G
```

| Atom | Domain | What it is | Delivered by | Status |
|---|---|---|---|---|
| **(D0) `residueNonSchurian`** | scope | reached residue is **not schurian** ⟹ outside the seal, honestly flagged | Runtime Phase (define the reached residue + its schurian test) | **NEW — but it DISSOLVES the `SchurianScheme` gap** |
| **(D1) `residueHiddenJohnson`** | symmetric | reached residue is the **un-shrinkable Cameron core** (= the concrete `IsCameronScheme` instance minus its handled sub-classes) | **Seal Phase — the Cameron shrink** | **NEW — research; the shrink defines it** |
| **(D2) `residueRigidObstruction`** | rigid | the **IR residual** ("rigid-Cameron-equivalent") | **IR Phase** | **NEW — research; `⊥` if "no rigid-Cameron"** |

**Why (D0) is the important insight.** The `SchurianScheme` model-faithfulness gap ("is the canonizer's actual
2-WL-closure residue equal to the `orbitalScheme H` model?") is flagged project-wide as *documented-infeasible*
to discharge. The endgame **does not need to close it**: if the reached residue is not schurian, it is outside
the seal's scope, so the honest thing is to flag it — which (D0) does by construction. A scary open gap becomes
an honest exclusion (and it coincides with the IR-solver's row-4 non-schurian residue, which is *by design* a
flag, never a seal obligation). The cost is only that non-schurian inputs are "unhandled" — which they
genuinely are.

**Why (D1) is lighter than it looks: the seal is already parameterized on `IsCameronScheme`.** In the library,
`IsCameronScheme : ∀ m, SchurianScheme m → Prop` is a **parameter** threaded through every seal capstone
(`reachesRigidOrCameron`, `SealDisj`, …) — the seal does not fix what "Cameron" means; the caller supplies it.
So the Seal-Phase Cameron shrink is concretely: **instantiate `IsCameronScheme`, then split it**
`IsCameronScheme = IsHandledCameron ∨ IsHiddenJohnson`, prove the handled part *reaches rigid* (so it exits the
Cameron escape), and let `residueHiddenJohnson` be the leftover `IsHiddenJohnson` on the reached residue. (D1)
is thus not a from-scratch predicate — it is the residue of refining an already-abstract parameter.

**How this steps the current form.** `Publication.lean` moved from the vacuous `opaque UnhandledResidue := True`
to a real `def` over three `opaque` atoms (compiles green). Filling each atom is a named phase deliverable; the
disjunction *shape* — crucially the (D0) absorber — is locked without waiting on any of them. The obligations
①–③ + non-vacuity are unchanged.

**Non-vacuity is now LOAD-BEARING (the ③-shape consequence).** ③ ships as the forward-only `residue_if_flag`
(`flag → UnhandledResidue`) — the reverse was dropped to avoid proving false border cases. This is the right
call (the headline only uses the forward direction, via `.mp`; `residue → flag` is false anyway), **but it
removes the automatic vacuity guard the biconditional gave for free**: under `↔`, `UnhandledResidue := True`
was self-refuting ("always flags" is false); under `flag → residue`, `True` satisfies ③ *trivially*. So
`unhandledResidue_nonvacuous` is no longer a nice-to-have — it is the **sole firewall** against a vacuous ③,
and it must name real families on both sides: a **handled** instance (a forms-graph `VO^ε` / a CFI graph ⟹
all three atoms false ⟹ `¬UnhandledResidue` ∧ canonized) *and* an **unhandled** instance (a hidden-Johnson
witness ⟹ (D1)). The handled-and-canonized witness is the load-bearing half — it is what proves the algorithm
actually claims something. Treat it as a hard obligation, not a formality.

---

## 5. Ordering and dependencies

**The approved sequencing (2026-07-08, §1a frame; best headline, not shortest line).** Two mirror seals meeting
at one wall; finish the provable non-rigid half, then throw weight at the rigid seal where the headline ceiling
lives:

1. **Finish the non-rigid half (Algorithm A / confinement)** — nearly done, Lean-provable-clean. Close X3 (the
   index-free cut: SpineChain-ify the single-vertex descent, discharge `hrec` from confinement, rewire
   `canonForm?`); wire `nodeOf`/witness-case → `CertifiedSinglePath`; discharge D0 / `hImprim`; assemble full ①.
   Banks the symmetric milestone and lets the Publication skeleton compile with the rigid seal as the sole hole.
2. **Build the rigid seal (Algorithm R, IR §11.12 roadmap)** — the big thrust. Lean **P1** first (extraction
   soundness, standalone) alongside C# **B1–B3** (the MVP solver wired at `target == -1`, verify-by-reconstruction).
   Then B4/B5 + P3/P4.
3. **Tighten the escape** — prove IR §11.14 (no rigid Cameron) ⟹ `UnhandledResidue` collapses to one atom.
4. **Runtime/Publication** — the cost-model consumption bridge (pilotable now on the quasipoly seal, independent),
   the `UnhandledResidue` definition (= the shared wall), non-vacuity, the Publication swap, the headline.

```
Non-rigid (Algorithm A): confinement → CertifiedSinglePath + X3 residual ─→ ① + symmetric obstruction ─┐
                                                                                                        │
Rigid seal (Algorithm R, IR §11.12): P1..P4 + B1..B6 + §11.14 no-Cameron ─→ rigid obstruction ─────────┤
                                                                                                        ├─→ one named UnhandledResidue ─→ ③ ─┐
Runtime Phase: canonForm?/cost + consumption bridge ─→ ② (pilot on quasipoly seal, independent) ────────┘                                   ├─→ canonizer
Seal substrate (warm_6_2, spine) ─→ ①a/①b/①c ──────────────────────────────────────────────────────────────────────────────────────────────┘
```

- **Independent, start-anytime:** the cost-model pilot on the quasipoly seal; the correctness trio assembly;
  the rigid P1 (extraction soundness).
- **Gated:** ③ waits on the `UnhandledResidue` definition = both seals' structural residues (which unify, §1a).
  ② waits on the cost model + consumption bridge.
- **Do before IR builds on it:** the Seal-Phase substrate consolidation.
- **Parked (not on the critical path):** Route C Lean; the C# main's global-flag + Route-C dispatch (§1a).

---

## 6. Risks and open decisions to resolve early

- **② is the highest-risk, latest-placed item.** Formalizing a runtime cost bound is foundational and rare;
  it may reshape how "poly" is banked upstream. *Mitigation: pilot on the quasipoly seal now.*
- **`UnhandledResidue` non-vacuity / firewall.** The single failure mode that would silently hollow out the
  result. *Mitigation: the non-vacuity obligation is already in the skeleton; enforce the firewall on every
  axiom.*
- **IR reuse assumption — PRICED (2026-07-08, §1a).** Resolved: the group-harvest machinery does NOT transfer
  (trivial rigid `Aut`); the recovery philosophy + forms/Gauss substrate do; rigid node-4 is handled (validated).
  The rigid seal is Algorithm R on the F₂/ring system (IR §11.12), not a reuse of the symmetric seal's internals.
- **rigid-Cameron non-viability is conjectural (IR §11.14).** *Mitigation: state IR's goal as the conditional; a
  non-empty rigid residual is an expected outcome. Upside: proving no-rigid-Cameron collapses `UnhandledResidue`
  to one atom — pursue it as a headline-tightener, not just a hope.*
- **`UnhandledResidue → ⊥` = closing the shared wall** (`hSmallAutThin` = rigid-GI ∈ P), the central open
  problem — NOT a near-term deliverable. *Mitigation: the honest best headline is one named residue with no
  witness (§1a); `⊥` drops in free if the wall falls. Do not gate "done" on emptying it.*
- **Cost-model granularity is an unmade decision** that everything in ② inherits. *Resolve at the pilot.*
- **Paper theorem statement** should be pinned now (it is `canonizer`); it defines "clean enough" for
  Publication-Phase cleanup and prevents polishing what the paper will not use.

---

## 7. Split-off files (create when the piece needs depth)
- **Cost model** → `chain-descent-cost-model.md` (granularity, the operation-count proxy, the explicit bound,
  the quasipoly-seal pilot). Split once the granularity is chosen.
- **`UnhandledResidue`** → likely folded into the Seal-Phase (Cameron shrink) and IR-Phase (rigid residual)
  docs as they produce the two disjuncts; a short unifying note here when both land.
- **The consumption bridge** → a Runtime-Phase build note when it starts.
