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
where **"poly" stops being a meta-argument** — and **③ (flag ⟺ obstruction)**, which requires the
`UnhandledResidue` definition plus consuming both the Seal-Phase and IR-Phase results. Neither ② nor ③'s
supporting objects exist yet; they are the substance of the Runtime and IR phases.

---

## 1. The end state, and the definition of "done"

The finished project is the theorem `Showcase.canonizer` (and the trio + non-vacuity guard it composes):

- **Correctness is unconditional** — for *every* graph, whenever the canonizer answers, its output is a
  complete isomorphism invariant that is a genuine relabelling of the input (never wrong). It may instead
  emit an honest **flag**.
- **Cost is conditional** — the descent runs within an explicit polynomial budget, *or* it flagged.
- **The flag is characterized** — a flag is emitted iff the input genuinely contains an **unhandled
  obstruction** (`UnhandledResidue`), not because the algorithm is weak.

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

## 2. The obligation map — what each needs, and what already exists

Anchored on `Publication.lean §3`. "Built" = the supporting object exists in the library; "assembly" = wiring
existing pieces; "new" = a genuinely unbuilt object.

| Obligation | Statement (informal) | Discharged by | State |
|---|---|---|---|
| **①a `canon_sound`** | Output is a relabelling of the input | `SpineChain.canonAdj` (leaf relabelling by the rank permutation) is a `labelledAdj` | **Built substrate; assembly** — once `canonForm?` is defined off the descent |
| **①b `canon_complete`** | Complete iso-invariant when it answers | `spine_branch_independent` + `warm_6_2` (direction-invariance) + `canon_sound` | **Built substrate; assembly** |
| **①c `flag_iso_invariant`** | Flagging is a class property | partition-invariant selector (`target_direction_blind` / the spine) | **Built substrate; assembly** |
| **② `canon_poly_or_flag`** | Poly-time or flag | **Cost model** (new) + the **consumption bridge** "reaches-rigid ⟹ poly node budget ⟹ ¬flag ∧ cost ≤ poly" (new) | **NEW — the main gap; where poly stops being meta** |
| **③ `flag_iff_residue`** | Flag ⟺ genuine obstruction | **`UnhandledResidue` definition** (new) + `reachesRigidOrCameron_*` consumed (Seal) + IR residual characterization (IR) + citations | **NEW — gated on Seal + IR completion** |
| **non-vacuity** | Handled and unhandled graphs both exist | concrete witnesses (a forms-graph / CFI handled; a hidden-Johnson unhandled) | **NEW — small, but the anti-vacuity guard** |

**Reading of the map.** The correctness trio is close (the hard invariance work — `warm_6_2`,
`spine_branch_independent` — is banked). The distance to done lives in three *new objects*: the **cost
model**, the **consumption bridge** (②), and the **`UnhandledResidue` definition** (③). Everything else is
either built or a citation.

---

## 3. The workstreams (phase-level)

Five workstreams reach the obligations. Names are for this doc's organization only (they are deliberately
absent from `Publication.lean`, whose statements are independent of the route taken).

### Seal Phase — the symmetric-domain seal, finished and reusable
The `reachesRigidOrCameron` seal already covers every schurian residue down to the forms-graph families
(Route C, all four sealed mod scoped citations). To feed ③ it must reach two end-states:
- **Node-4 residue: closed and non-meta where it matters.** Route C is done at the structural level; the
  live technical item is **R1, the Aut-free geometric coordinatizer** (removes the `O_p(Aut)` consumption so
  the poly claim is non-circular *in the runtime*, not just meta — see route-c-plan §7a). This is also the
  natural first probe of the cost model (Runtime Phase).
- **Cameron shrink → the symmetric half of `UnhandledResidue`.** Investigate/shrink the Cameron escape toward
  hidden-Johnson-only. This need not *empty* it (that is likely GI ∈ P); the deliverable is a crisp
  *structural* predicate naming exactly what stays unhandled, which becomes the symmetric disjunct of
  `UnhandledResidue`.
- **Consolidate the reusable core** (the recovery / forms / Gauss substrate the IR Phase will import) and
  prune the ⊘-superseded seal capstones — *before* IR builds on it, so the mess is not compounded.

Output for the endgame: a clean `reachesRigidOrCameron` object + a structural symmetric-obstruction predicate.

### IR Phase — the rigid mirror solver
The rigid mirror-domain (recover the F₂ constraint system `H` → `ker(H)` → Gaussian) reuses the recovery
*idea* and the shared geometry, giving the rigid analogue of the seal. To feed ③ it must:
- Build the rigid solver and its Route-C analogue for the rigid node-4 residue.
- Characterize the **rigid residual** structurally (the "rigid-Cameron-equivalent"), which — if it collapses
  (conjectural: "no rigid-Cameron") — is empty, and otherwise is the rigid disjunct of `UnhandledResidue`.
- **De-risk the reuse assumption first** (a scoping spike): the rigid domain has trivial `Aut`, so the seal's
  group-harvest machinery does not transfer; what transfers is the recovery philosophy + the forms/Gauss
  lemmas. Price the reuse before budgeting on it.

Output for the endgame: a structural rigid-obstruction predicate (possibly empty).

**Design note (robust success criterion).** State the IR goal as the *conditional* ("canonized or unhandled
rigid residue"), not "rigid GI ∈ P". The conditional is exactly what ③ formalizes and is robust to a
non-empty residual; "residual empty" is the optimistic case, not the success gate.

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
  into *runtime* statements ("¬flag ∧ cost ≤ poly", "flag ⟺ residue"). This is where "poly" stops being a
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

1. **`UnhandledResidue` — the firewall valve (the single most important definition).** It must be:
   (i) an *independent structural/geometric* predicate — Cameron/hidden-Johnson (symmetric) ∨ the IR residual
   (rigid) — **not** "the algorithm flagged" (that makes ③ a tautology); (ii) defined to *absorb exactly the
   open cases*, so everything on the handled side needs only real citations; (iii) non-vacuous on both sides.
   Its exact definition is gated on Seal + IR producing their structural residue predicates, but its *shape*
   (a disjunction of two structural predicates) is fixable now. This is where the whole "conditional GI ∈ P"
   honesty is won or lost.

2. **The cost model (`cost` + the bound).** Decide granularity early; prefer an explicit polynomial over
   `∃ p : Polynomial`. Pilot on the quasipoly seal. *Split candidate:* its own file once the granularity is
   chosen.

3. **The consumption bridge.** The theorem-level connective from the structural seal to the runtime `canonForm?`
   / `cost` statements. It is the concrete meaning of "the seal implies the algorithm is correct-and-poly", and
   it is currently unbuilt — the honest measure of the gap between "we have `reachesRigidOrCameron`" and "we
   have `canonizer`".

---

## 5. Ordering and dependencies

```
Seal Phase (node-4 R1, Cameron shrink) ─┐
                                        ├─→ UnhandledResidue definition ─→ ③ flag_iff_residue ─┐
IR Phase (rigid solver, rigid residual)─┘                                                      │
                                                                                               ├─→ canonizer (headline)
Runtime Phase: canonForm?/cost + cost model ─→ ② canon_poly_or_flag ───────────────────────────┤
             (pilot on quasipoly seal first)                                                   │
Seal-Phase substrate (warm_6_2, spine) ─→ ①a/①b/①c correctness (assembly) ──────────────────────┘
```

- **Independent, start-anytime:** the cost-model pilot on the quasipoly seal (does not wait on Seal/IR); the
  correctness trio assembly (substrate already banked); the reuse spike for IR.
- **Gated:** ③ waits on the `UnhandledResidue` definition, which waits on Seal + IR structural residues.
  ② waits on the cost model + consumption bridge.
- **Do before IR builds on it:** the Seal-Phase substrate consolidation.

---

## 6. Risks and open decisions to resolve early

- **② is the highest-risk, latest-placed item.** Formalizing a runtime cost bound is foundational and rare;
  it may reshape how "poly" is banked upstream. *Mitigation: pilot on the quasipoly seal now.*
- **`UnhandledResidue` non-vacuity / firewall.** The single failure mode that would silently hollow out the
  result. *Mitigation: the non-vacuity obligation is already in the skeleton; enforce the firewall on every
  axiom.*
- **IR reuse assumption unpriced.** "Reuse almost all the seal work" is an aspiration given trivial rigid Aut.
  *Mitigation: scoping spike before committing IR budget.*
- **rigid-Cameron non-viability is conjectural.** *Mitigation: state IR's goal as the conditional; a non-empty
  rigid residual is an expected outcome, not a failure.*
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
