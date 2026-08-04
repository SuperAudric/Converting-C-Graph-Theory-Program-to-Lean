# WIND-DOWN — the closing plan

> **STATUS: research phase CLOSED (2026-08-01). This document is authoritative for what
> remains.** Every forward-looking item in every other `chain-descent-*.md` is **SUSPENDED**
> unless it appears in §2 below. Those docs remain accurate as a *record* of what was built
> and what was refuted; they are no longer a plan.

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

### W1 — Tinhofer family `Handled` *(box: 2 weeks)*
Turn [`KeyComplete.handledS_of_reached_tinhofer`](../GraphCanonizationProofs/ChainDescent/KeyComplete.lean#L325)
from a hypothesis-defined class into a **named family**. Today the only `Handled`
populations are that one and `handled_emptyAdj`; everything else
(`handledS_recordSupply`, `handled_of_seal*`) is a transfer or a reduction lemma.

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

### W5 — archive
Freeze the repo, final README pass, presentability pass on secondary documents.

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
