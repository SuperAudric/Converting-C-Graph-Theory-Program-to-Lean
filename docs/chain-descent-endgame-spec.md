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

**Progress (2026-07-12) — the model is now the INTERLEAVED fixpoint; the sequential Algorithm-A seal crash-landed on fusion; RRU is retired.**
The single durable statement, superseding the earlier sequential/RRU/confinement build-log (that history is in
[`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md), the doc STATUS blocks, and the changelogs):

- **The canonizer is the interleaved stepwise alternating fixpoint** `…∘phase2∘phase1…` — one pairwise relation at a
  time (the oracle **consumes** it via a *verified* automorphism; the rigid solver **forces** it if it lies in the current
  row-space; else it is **deferred**), 1-WL refine between, the rigid solver's kernel feeding *de-fused* symmetry back to
  Phase 1. Sequential `phase2 ∘ phase1` is only the **fusion-free special case**. The run is **done at MUTUAL STALL** —
  neither the oracle nor the rigid solver has a step left; **the flag fires exactly at mutual stall**, not at a base
  threshold. Engine spec: [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11.11;
  Lean composition track: [`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md).
- **Why the model changed (the crash-landing).** The sequential **Algorithm A** seal pruned on a *threshold-gated* flag
  (`base > baseMax ⟹ assume-VT`) **without verifying an automorphism**. Its soundness was "completeness of deferral ⟺ no
  fusion," and **no theorem bounds how mild fusion must be** — so a conditional symmetry *fused* with a real (rigid)
  decision (Chang-A) could be assume-VT-pruned, pruning the rigid residue. Interleaving fixes this structurally:
  consumption is **verify-gated**, so a rigid residue (no automorphism) presents as a *stall*, never a harvestable orbit,
  and the mechanism that could misprune it is gone. The abelian/linear fused case is then **de-fused constructively** by
  the solver kernel (nontrivial kernel-module → verify → consume → refine → loop); the residual risk narrows to
  **non-abelian fusion in a rigid medium**, excluded by IR §11.14 and **carried like "or Cameron"** (empirically solid,
  not load-bearing on a missing theorem). See [`chain-descent-cost-model.md`](./chain-descent-cost-model.md) STATUS and
  [`chain-descent-deferred-decisions.md`](./chain-descent-deferred-decisions.md) top banner.
- **RRU is retired.** The Phase-1 deliverable is no longer "Reaches Rigid Unconditionally" (a one-shot `R(G)` handoff);
  it is the **iterative fixpoint object** above. The typed **`Phase2.Solver` / `Sound` / `IsoInvariant` contract** (+
  `handoffBase_relabel`) in `ChainDescent/Phase2Handoff.lean` survives as the seam the rigid solver fills; the `RRU`
  reachability apparatus (`ComputesResidue`/`rru`, built on `rigidResidue = supp Aut`) is content-free and abandoned.
- **What is proven and reusable.** ①a `canon_sound` and the ② cost side (`descentCost_le`, `≤ n⁴`) are proven axiom-clean
  against the shared capped object (`ChainDescent.CostModel` / `CanonForm`); the mixed-composition Stage 0a framework
  (`ChainDescent.CanonicalForm`: `complete_of_isCanonicalForm`, `lexMin`) makes ①b/①c free given one iso-invariance
  obligation. These transfer to the interleaved object; the concrete `n⁴`/quasipoly *degree* must be re-established
  against it (the `nbud = n` single-path justification does not carry — see cost-model STATUS).

**★★★ ① IS DONE — THE WHOLE CORRECTNESS SIDE IS DISCHARGED AND HYPOTHESIS-FREE (2026-07-14).** The stack, all in
`build.sh`, all axiom-clean, no `sorry`:

| module | what it gives |
|---|---|
| `ChainDescent/Descend.lean` | **THE OBJECT.** `descend` — a *computable*, resolver-parameterized **branching** descent in `CostM`. **`isCanonicalFormOpt_canonForm?`**: sound ∧ iso-invariant ⟹ (Stage 0a) a complete isomorphism invariant with an iso-invariant flag ⟹ **①a/①b/①c**. Executable and cost are the `value`/`cost` **projections of that same definition** — no second object, no bridge. |
| `ChainDescent/Refine.lean` | The **encode-free** refiner. Discharges *both* refiner obligations ⟹ `exhaustive_canonizer`: the exhaustive descent is **unconditionally** a canonical form **that answers**. |
| `ChainDescent/Consume.lean` | The **oracle** resolver (`Covering` route). The oracle is **untrusted** — the resolver *verifies* — so `consume_canonizer` holds for **every** supply. |
| `ChainDescent/Force.lean` | The **rigid/force** resolver route (`NarrowEquivariant`), as a **combinator** `forceBy key`. Its **entire ① obligation is `KeyEquivariant`**. |
| `ChainDescent/PerformanceTest.lean` | The **regression gate** — a correctness or firing regression *fails the build*. |

**The resolver contract is `NarrowTransport`** (*the narrowed-branch aggregate transports under σ*), fed by **two**
routes with **complementary firing domains**: **`Covering`** (consume — non-equivariant choice, redundant discards;
must be **fuel-graded**, `CoveringAt`) and **`NarrowEquivariant`** (force — structural choice, genuinely-different
discards, a *different but equally valid* canonical form). ⛔ **Do not re-unify them under `Covering`** — a covering
resolver is provably **value-invisible** (`canonForm?_eq_deferAll_of_covering`), which silently re-imports the retired
`canonMin` anchor and would force the rigid solver to *know the answer*. `narrow_eq_branches_of_orbit` proves force
cannot fire on an orbit cell and consume fires exactly there — **graphs where neither fires are the residue**, and that
is why the design does not collapse into GI ∈ P.

**The live Lean frontier (what a fresh reader should pick up) — ② and ③ only:**
1. **② / the cost + flag — THE remaining gap.** Re-base the node bound onto the branching object (the old `n⁴` used
   `nbud = n` = the single-path assume-VT justification and does **not** transfer); replace `descend`'s
   **`fuel`-exhaustion `none`, which is still a PLACEHOLDER**, with the real **mutual-stall** flag. Fuel is
   **per-layer, never threaded**, so each resolver is poly-or-flag *locally*. Both resolver instances now exist to
   cost against.
2. **③** — `stalled ⟹ D1 ∨ D2`, plus non-vacuity.
3. **The Publication swap** — `canonForm?` is still `opaque`. ⚠ `unhandledResidue_nonvacuous` is **unprovable in
   principle** while the three residue atoms remain `opaque … : Prop` with no definition.

**No longer a separate track:** the *runnable* Lean canonizer — the executable **is** `descend`
([`chain-descent-executable-track.md`](./chain-descent-executable-track.md)); it `#eval`s today.

---

## 1. The end state, and the definition of "done"

> **⚠ RETARGET (2026-07-18, user steer — read before the bullets below).** The end state below (poly-or-flag +
> a characterized residue) is the honest **intermediate scaffold and the fallback**, NOT the target. **The
> target is a COMPLETE canonizer — every input handled, polynomially: the flag provably never fires**
> (totality assembled per-leg + the G3 case-split). A named residue is acceptable in the final version **only
> for a gap whose every identified route has been attempted and recorded dead** (steers-archive discipline).
> The full gap enumeration and the plan to closure:
> [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §0–§2. The obligations below stay
> exactly as stated — each intermediate stage publishes through them; "done" tightens from "③ characterized"
> to "③ vacuous (no flag)".

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

**Two algorithms are in play; they INTERLEAVE (they are not two sequential phases).**
- **Algorithm A — symmetry consumption** (the oracle side; cascade/linear). Consumes a pairwise relation via a
  **verified automorphism**, reducing the residual symmetry. As a *standalone sequential seal* (assume-VT / confinement,
  the earlier "prune the whole flagging residue" plan) it **crash-landed on fusion** — its threshold-gated prune could
  misprune a rigid residue fused with a real decision (Chang-A), and its soundness needed a fusion-mildness theorem that
  does not exist. It survives **only** as the verify-gated consume step *inside* the interleaved engine, where a rigid
  residue simply stalls rather than being pruned. Symmetric machinery it still carries: {G3, Liebeck, Witt, hImprim} for
  classifying the *large-Aut* Cameron case.
- **Algorithm R — the rigid solver** (the force side; F₂/ring → Smith). Recovers the linear constraint system of the
  rigid residue and solves it (row-space force / canonical coset), **de-fusing** any abelian symmetry hidden behind a
  real decision (its kernel is a symmetry detector) and flagging the non-linear residue. It is the mechanism for the
  rigid domain (trivial `Aut` ⟹ consumption is vacuous there) and, via interleaving, for the mixed residue too.
  **No new citations** (unlike G3 on the symmetric side). Detail: IR §11.11–§11.14. *(Route-C form recovery on the
  symmetric side is a separate, parked poly result — not on the headline path.)*

**★ The two algorithms INTERLEAVE; the Phase-1 deliverable is the ITERATIVE FIXPOINT OBJECT, not a one-shot handoff (RRU is retired).**
The earlier plan had Phase 1 (Algorithm A) run to a rigid residue `R(G)` and hand it *whole* to Phase 2 — the "RRU"
switch-over gate. **That sequential split is retired**, because it required Phase 1 to consume every symmetry *before* any
rigid work, which is exactly "completeness of deferral ⟺ no fusion" — an open question with **no theorem bounding how mild
fusion must be**. The current model **interleaves**: at each pairwise relation the oracle consumes it (verified
automorphism), or the rigid solver forces it (row-space), or it is deferred; 1-WL refine between; the solver kernel feeds
*de-fused* symmetry back to Phase 1. The Phase-1 deliverable is therefore the **iterative fixpoint object** — the descent
run to **mutual stall** (neither oracle nor rigid solver can take a step). This is strictly stronger than RRU: the rigid
solver does **not** need a purely-rigid residue to start, so fusion (Chang-A) never has to be shown mild. **`none` fires
exactly at mutual stall**, and the residual it names is the shared wall.
- **Why interleaving restores viability (the fusion resolution).** Consumption is **verify-gated, not threshold-gated**:
  the oracle merges a pair only via a verified automorphism (`real_stays_real`, `CascadeOracle.lean`), so a rigid residue
  — which *has* no such automorphism — presents as a **stall, never a harvestable orbit**, and the threshold-prune that
  crashed Algorithm A is gone. Abelian/linear symmetry *fused* behind a real decision is **de-fused constructively** by
  the solver's kernel (a nontrivial kernel-module is the hidden linear symmetry → verify → consume → refine → loop). Only
  **non-abelian fusion in a rigid medium** could survive both, and IR §11.14 argues a rigid medium admits none (hiding is
  abelian/linear; Johnson/Cameron is non-abelian) — carried like the symmetric seal's "or Cameron", empirically solid,
  **not** load-bearing on a missing fusion-mildness theorem. Full argument: cost-model STATUS + IR §11.11/§11.14.
- **The typed seam that survives.** `ChainDescent/Phase2Handoff.lean` keeps the **`Phase2.Solver` / `Sound` /
  `IsoInvariant` contract** (+ `handoffBase_relabel`) — the interface Algorithm R witnesses. The `RRU` namespace's
  *reachability* apparatus (`ComputesResidue`/`rru`, built on `rigidResidue = supp Aut`, a `rfl`-inhabited content-free
  object per the 2026-07-10 audit) is abandoned; do not build on it.
- **Consequence for the Lean objects.** ① and ② are established against the mixed-composition object
  ([`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md)), whose spec is **sound ∧ iso-invariant**
  (Stage 0a `complete_of_isCanonicalForm` makes completeness free); composition is a **fold over alternation depth**, not
  one append. The `∨ none` disjunct of `canon_poly_or_flag` is the mutual-stall flag. The Cameron-visible forms families
  (Route C) are **deprioritized** — they widen what the oracle consumes, but the composition must hold regardless.

**The two seals (mirror table, IR §11.12).**

| | handles | the escape | wall |
|---|---|---|---|
| **symmetry seal** `reachesRigidOrCameron` | symmetry consumption (Algorithm A / assume-VT) | "or Cameron" | `hSmallAutThin` |
| **rigid seal** `canonizesRigidResidue_or_flags` | linear-over-a-ring: CFI / multipede / `Z_{2^k}` (Algorithm R / F₂→Smith) | "or non-linear" | **= `hSmallAutThin`** |

**The target — minimize `UnhandledResidue`, do NOT concede the rigid side.** The goal is the *best* headline, not
the shortest line. Concretely:
- **`UnhandledResidue` → one named residue.** Every symmetry-only residue is believed to be **node-4 (Schurian by
  definition) or Cameron**, so `residueNonSchurian` (D0) is a **modelling gap, not a genuine unhandled residue** (see §4.1)
  — the live atoms are **D1 (hidden-Johnson, symmetric) and D2 (rigid obstruction)**. The two seals' flag floors are the
  **same object** (IR §11.11 node-4 unification: the symmetry seal reduces node-4 from the rank-3 side, the rigid solver
  reduces the multipede from the high-rank side, both leave the identical residue), so D1 and D2 collapse toward **one**
  predicate. (D2 itself later splits into rigid-Cameron-equivalent / rigid-node-4-equivalent — a downstream refinement,
  the mirror of the Cameron→hidden-Johnson shrink, off the immediate critical path.)
- **`UnhandledResidue → ⊥` is exactly closing that shared wall** (`hSmallAutThin` = "small-Aut ⟹ bounded WL-dim"
  = rigid-GI ∈ P). That is the project's central open problem — **not reachable with current techniques**, but it
  has **zero constructible falsifiers**, so the honest best headline is "*poly-time complete canonizer whose only
  unhandled inputs are one named residue coinciding with a known GI-hardness frontier, for which no witness
  exists*". If the wall ever falls, `⊥` drops in for free.

**Transfer assessment (answers "does node-4/Cameron → known-solution transfer to the rigid side?").**
- **Rigid node-4 (the F₂/ring-multipede): TRANSFERS / handled** ⚠ **for odd-part(fold) ≤ 5 (scoped 2026-07-17;
  the 2026-07-16 audit found F_k fold covers with odd-part ≥ 7 are linear-over-a-ring yet unhandled BOTH sides —
  inside this leg's stated boundary. Closure plan = [`chain-descent-fold-tower-plan.md`](./chain-descent-fold-tower-plan.md):
  the Lean CONSUME half is complete 2026-07-18 — F1 `partialMatchSupply` + F2a `foldSupply` + F2b `deckSupply`
  (propagation harvest, generators of any order: the symmetric/gauge side has NO odd-part cap in Lean any more);
  the remaining odd-part fix = F3 CRT/Smith coset ordering, the DISTINGUISHABLE-copy force half, open both sides).** The F₂→ring
  (Smith-normal-form) solver canonizes it — validated end-to-end (D-M0–M4) *and* for `Z₄` (IR §11.11). `Z_{2^k}` is
  **inside** the iterative engine, not the floor. Lichter's FPC+rank lower bound does **not** bind it: Lichter is
  individualization-free; this solver individualizes.
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
| **①a `canon_sound`** | Output is a relabelling of the input | **`Descend.soundOpt_canonForm?`** (`ChainDescent/Descend.lean`) | **★ DISCHARGED (2026-07-13)** on the real branching object; holds for ANY `refine`/resolver |
| **①b `canon_complete`** | Complete iso-invariant when it answers | **`Descend.canonForm?_complete`** (via `CanonSpec.complete_of_isCanonicalFormOpt` + `Descend.isCanonicalFormOpt_canonForm?`) | **★ DISCHARGED (2026-07-13)**, modulo the 2 carried hyps `RefineEquivariant` + `Covering` |
| **①c `flag_iso_invariant`** | Flagging is a class property | **`Descend.canonForm?_flag_iso_invariant`** | **★ DISCHARGED (2026-07-13)** — free; `IsoInvariantOpt` is one equation on `Option`s, carrying output *and* flag invariance |
| **② `canon_poly_or_flag`** | Poly-time or flag | the **`cost` projection** of the same `descend` (`Descend.descentCost`, co-defined in `CostM`) + the **verify-consume monovariant** (the old `n⁴`/`nbud = n` single-path bound does NOT transfer) | **OPEN — now the main gap.** Flag = **mutual stall**, not `base > baseMax` |
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

### Seal Phase — the symmetric-domain seal, now the interleaved CONSUME step (not a standalone sequential phase)
> **⚠ SUPERSEDED FRAMING (2026-07-12).** This subsection described **Algorithm A** as a standalone assume-VT/confinement
> seal that *finishes the non-rigid half first*. That plan **crash-landed on fusion** (§1a): its threshold-gated prune
> could misprune a fused rigid residue, and its soundness needed a fusion-mildness theorem that does not exist. The
> `reachesRigidOrCameron` seal and its {G3, Liebeck, Witt, hImprim} machinery are **retained**, but only as the
> **verify-gated consume step inside the interleaved engine** (classify/consume the large-Aut Cameron case); they no
> longer carry the whole non-rigid correctness. The X3 / `CertifiedSinglePath` single-path work below is superseded by
> the mixed-composition **branching** descent (Stage 0b). Read the rest of this subsection for the reusable substrate
> only. The `reachesRigidOrCameron` seal is in build; its symmetric machinery consumes
`exhaustiveObstruction_scheme` + **G3** (§1a). Substrate notes (still valid):
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
- **Define `canonForm?` = ONE computable `CostM` descent, parameterized over `Resolver`s** — scoped in
  **[`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md)** §1 (the priority track; object
  revised 2026-07-13). The existing `defaultSpineChain`/`SpineChain.canonAdj` model is a **single deterministic path
  with no branching, no oracle, no consume/defer** (source-verified) — only the all-symmetric pole.
  **The `canonMin` (min-over-all-leaves) target is RETIRED:** the spec is **`Sound ∧ IsoInvariant`, full stop**
  (completeness + flag-invariance are then free via `complete_of_isCanonicalForm`), and the descent **defines** the
  canonical form rather than searching for a pre-existing global lex-min. Consume and force are unified by one
  **branch-covering** contract (a discarded branch's output is already reachable through a kept one — so force needs
  no knowledge of the answer). **The executable and the cost are PROJECTIONS of that same definition** (`value` /
  `cost`), not separate objects — the cost model's own D1 decision. ①b/①c reduce to a single induction (Stage 2).
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
| **(D0) `residueNonSchurian`** | scope | reached residue is **not schurian** | **modelling artifact to DISCHARGE, not a live atom** | **A MODELLING GAP — see below; every symmetry-only residue is node-4/Cameron ⟹ Schurian or Cameron** |
| **(D1) `residueHiddenJohnson`** | symmetric | reached residue is the **un-shrinkable Cameron core** (= the concrete `IsCameronScheme` instance minus its handled sub-classes) | **Seal Phase — the Cameron shrink** | **LIVE — research; the shrink defines it** |
| **(D2) `residueRigidObstruction`** | rigid | the **IR residual** ("rigid-Cameron-equivalent"; later splits rigid-Cameron / rigid-node-4-equivalent) | **IR Phase (Algorithm R)** | **LIVE — research; `⊥` if "no rigid-Cameron"** |

**Why (D0) is a MODELLING GAP, not an unhandled residue (2026-07-12 correction).** It is *believed* that every
symmetry-only residue is **node-4 (Schurian by definition) or Cameron** — so a "non-schurian reached residue" is not a
genuine class of hard graph, it is the `SchurianScheme` model-faithfulness question ("is the canonizer's actual
2-WL-closure residue equal to the `orbitalScheme H` model?"). That is a **modelling obligation to discharge**, on par with
the other modelling assumptions the seal carries — *not* an honest flag for a real obstruction. So the **live**
`UnhandledResidue` is `residueHiddenJohnson ∨ residueRigidObstruction` (D1 ∨ D2); D0 stays in the `Publication.lean`
disjunction for now as a documented placeholder (see the note there), but the intended end shape drops it once the
schurian-faithfulness modelling gap is closed. *(Superseded framing: D0 was previously treated as "the important
absorber" that dissolves the SchurianScheme gap by flagging — that conflated a modelling gap with a genuine residue.)*

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

**The sequencing (2026-07-12; interleaved-fixpoint frame; best headline, not shortest line).** The sequential
"finish the non-rigid half first, then the rigid seal" plan is retired — the non-rigid seal (Algorithm A) crash-landed on
fusion and is now the verify-gated consume step *inside* the interleaved engine (§1a). The critical path is the
mixed-composition Lean track plus the rigid seal, which run in parallel (the composition proceeds with `phase2` abstract):

1. **Build the interleaved/branching descent in Lean (mixed-composition, the priority track).**
   [`chain-descent-mixed-composition.md`](./chain-descent-mixed-composition.md) §1 + Stages 0–2. **Stage 0a's
   `Option`-lift** (small) → **Stage 0b**: define `descend : AdjMatrix n → CostM (Option Matrix)` — computable, over
   the **encode-free `refineStep`** (lock this now; it is definitional and it is what makes the executable a free
   projection), parameterized over a list of `Resolver`s (computable `decide`, `Prop` fields for equivariance +
   **covering**). → **Stage 2**: `descend` is **`Sound ∧ IsoInvariant`**, by induction over the descent (the branch
   list transports; the leaf matrix absorbs σ via the rank permutation). ①b/①c are then **free**. The resolver
   *instances* (consume, force) do not gate this — the descent is proved against the **contract**, which is also what
   lets a future solver shrink the residue with no re-proof.
   **✅ ALL OF THIS IS DONE (2026-07-13, `ChainDescent/Descend.lean`, axiom-clean, no `sorry`):** capstone
   `isCanonicalFormOpt_canonForm?` ⟹ **①a/①b/①c discharged**, modulo `RefineEquivariant` + `Covering`. **The remaining
   work is ② (cost + the mutual-stall flag), instantiating `refine` with the encode-free round, the resolver
   instances, and ③** — see the STATUS block at the top of this file.
2. **Build the rigid seal (Algorithm R, IR §11.12 roadmap)** — the `Phase2.Solver` witness that Stage 3 plugs in. Lean
   **P1** first (extraction soundness, standalone F₂/matroid) alongside the (already-built) C# solver; then P3 (the
   Smith solve + canonical-form iso-invariance) + P4 (the capstone `canonizesRigidResidue_or_flags`, isolating
   `LinearObstruction`). P2 (forcing = unit-propagation) carried as a hypothesis. No new citations.
3. **Tighten the escape** — prove IR §11.14 (no non-abelian fusion survives into a rigid medium ⟹ no rigid Cameron) ⟹
   `UnhandledResidue` collapses toward one atom (carried like "or Cameron" until then).
4. **Re-base cost + Publication** — re-establish the cost bound (Stage 4) against the interleaved object (the `nbud = n`
   single-path degree does **not** carry — cost-model STATUS), define `UnhandledResidue` (= D1 ∨ D2, the shared wall),
   non-vacuity, the Publication swap, the headline.

```
✅ Interleaved descent (mixed-composition 0a/0b/1/2, Descend.lean): branching canonForm?, sound ∧ iso-inv ─→ ①a/①b/①c ─┐
                                                                                                            │
Rigid seal (Algorithm R, IR §11.12): P1..P4 + §11.14 no-Cameron ─→ Phase2.Solver witness + D2 rigid residue ┤
                                                                                                            ├─→ D1∨D2 UnhandledResidue ─→ ③ ─┐
Cost (Stage 4): re-base cost on the fixpoint + mutual-stall flag ─→ ② ───────────────────────────────────────┘                              ├─→ canonizer
                                                                                                                                             │
Seal substrate (warm_6_2, spine, Stage 0a complete_of_isCanonicalForm) ─→ correctness scaffolding ───────────────────────────────────────────┘
```

- **Independent, start-anytime:** the rigid P1 (extraction soundness, standalone); the cost-model pilot on the
  quasipoly seal.
- **Gated:** ①b/①c wait on Stage 0b's branching descent + X3 (mixed-composition); ③ waits on the `UnhandledResidue`
  definition = D1 ∨ D2, the shared wall (§1a/§4.1); ② (re-based) waits on the interleaved cost accounting (Stage 4).
- **Parked (not on the critical path):** Route C Lean; the RRU reachability apparatus; the C# main's global-flag +
  Route-C dispatch (§1a).

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
  problem. ⚠ REFRAMED (2026-07-18, user steer): this IS the target, not a stretch goal — the wall is attacked
  to route-exhaustion (remaining-work §1W), and the named-residue headline is the *fallback* carried with its
  recorded route obituaries, never a design assumption. Near-term stages still publish through the
  poly-or-flag shape while the wall stands.
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
