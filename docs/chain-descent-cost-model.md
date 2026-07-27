# Cost model — the Lean runtime cost framework and the poly bound

> # ▶▶ ⚠ STATUS 2026-07-14 — **② IS DONE, AND UNCONDITIONALLY.** This doc is now BACKGROUND.
>
> The cost bound is no longer conditional and no longer lives here. **`Stall.descentCost_guard_le`: the guarded
> descent is polynomial with NO hypothesis** — not on the graph, the supply, or the key. The reason is a *model*
> correction, not a proof trick:
>
> > **Deferral is not a cheap mode of a healthy run — it IS the failure mode.** Every node consumes or forces; a node
> > that can do **neither** has reached the mutual stall and *is* the unhandled residue. There is **no
> > deferred-then-retried decision in the design**, hence **no exhaustive fallback to be polynomial *about***. A
> > descent runs as a single path or it stops. **`poly` AND `flag`, never `poly` OR `exponential`.**
>
> The banked `n⁴` (`CanonForm.descentCost_le`) is against the **single-path** `spineCappedCanonizer` (`nbud = n`,
> assume-VT) and does **NOT** transfer to a branching object. `ChainDescent/Cost.lean` + `ChainDescent/Stall.lean`
> replace it. ⚠ **New obligation the flag creates: `Stall.StallEquivariant`** — a flag is *not* value-invisible, so
> the oracle supply must be **equivariant** or `①c` is false (counterexample `#guard`ed in `Regression.lean`).
> **Authoritative:** [`chain-descent-handoff-2026-07-14.md`](./chain-descent-handoff-2026-07-14.md) §3.
>
> **✅ UPDATE 2026-07-17 — the `c₂` side is DISCHARGED for the consume oracle (`ChainDescent/SupplyCost.lean`).**
> Explicit per-supply `supplyCost` bounds (match / deep / partial / pruned, closed-form, poly per fixed `d`), the
> key-abstract mixed per-node bound, and the first end-to-end explicit-polynomial `descentCost` for the concrete
> canonizer of record (`descentCost_pruned_lookahead_le`) + the ②+③ capstone `handled_answers_poly`. It also
> **weakened `hR` in place**: the old `∀ χ B` form was *unsatisfiable* for both built resolvers (cost reads
> `B.length`); the hypothesis now lives at the descent's only call site `B = branches χ`. Detail: handoff §3.

> **What this is.** The design + build doc for the project's **cost model**: the Lean objects that turn
> "poly time" from a meta-claim into a proven bound, serving obligation ②/③ of
> [`GraphCanonizationProofs/Publication.lean`](../GraphCanonizationProofs/Publication.lean). It records the
> seven locked design decisions, the framework as built, the per-node and node-count pieces still to build,
> and the pilot that validates the whole thing on the banked quasipoly seal. It is a design doc — the
> authoritative Lean state is [`ChainDescent/ScratchCostModel.lean`](../GraphCanonizationProofs/ChainDescent/ScratchCostModel.lean)
> + `#print axioms`.
>
> **Companion docs.** Endgame map: [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md).
> The quasipoly seal the pilot rides on: [`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md),
> [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md). The branching bound
> the poly case needs: [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md).

---

## STATUS (read first)

> # ★★★ THIS DOC IS THE NEXT TASK (2026-07-14). ① IS DONE; **② IS THE FRONTIER.**
>
> **Everything ② needs to be stated against now exists**, all in `build.sh`, all axiom-clean:
> `ChainDescent/Descend.lean` (**the object** — `descend`, in `CostM`; `descentCost` is the **`cost` projection of the
> same definition** ①a/①b/①c ride on, so ② needs **no bridge lemma**), `Refine.lean` (the encode-free refiner —
> **charges its own cost**), `Consume.lean` + `Force.lean` (**both** resolver instances — they charge their own cost
> too, since `Refiner` and `Resolver` are both `CostM`-valued).
>
> **The two concrete jobs:**
> 1. **Re-base the node bound onto the BRANCHING object.** The banked `n⁴` (`CanonForm.descentCost_le`) is against
>    `spineCappedCanonizer` — a **single path**, justified by `nbud = n` (assume-VT, `leaves = 1`). **It does NOT
>    transfer.** (Also note `CostModel.lean`'s own comment: `spineCappedCanonizer` *can never flag*, so ③ against it
>    would be **vacuous**.) The poly guarantee is the **verify-consume monovariant** + the fusion-severity look-ahead.
> 2. **Replace the FLAG.** `descend`'s `fuel`-exhaustion `none` is a **PLACEHOLDER** — and `Descend.canonForm?_ne_none`
>    proves it **never actually fires** for a genuine refiner, so fuel is a pure *depth* bound and `none` is free to
>    acquire its real **mutual-stall** meaning.
>
> **Two constraints that must not be "optimized" away:**
> - **Fuel is PER-LAYER, never threaded.** Every branch at a level gets the same fuel; accumulated cost is never fed
>   back. This is what makes "resolver `R` is poly-or-flag" a **local** statement about `R`. A global budget would
>   couple the resolvers' flag behaviour and destroy that locality.
> - **The flag must be a LOCAL, STRUCTURAL predicate of the node — not of the traversal.** `aggregate` is
>   permutation-invariant and the branch list is built in *index* order; if "flagged" depended on traversal order
>   (e.g. which branch exhausted a shared budget first), **①c would be false**. Keep it a function of `(adj, χ)`.
>
> *(The D7 fork below is RESOLVED — see its banner. Its diagnosis was also wrong; the encode had to be dropped
> entirely, not compressed.)*

> **▶ CURRENT MODEL (2026-07-12) — the cost account is on the INTERLEAVED fixpoint; the threshold-gated assume-VT flag is
> retired.** The big build-log below predates the model change and is retained as history; this banner is the current
> state. Live Lean source is [`ChainDescent/CostModel.lean`](../GraphCanonizationProofs/ChainDescent/CostModel.lean)
> (the `ScratchCostModel*` pointers below are stale — that cluster was ported into `CostModel.lean` 2026-07-09).
> - **What is reusable, unchanged:** the cost monad + budgeted process + per-node cap ⟹ **② unconditional by
>   construction** (`cost ≤ budget` with no hypothesis; all poly content in ③-forward); ①a `canon_sound`; the co-defined
>   `warmRefine` summand. The **abstract** cap mechanism survives a rigid solver (it charges `min(trueCost, w)` for *any*
>   `step`).
> - **What does NOT carry:** the concrete degree (`n⁴` / quasipoly) was proven with `nbud = n` = the **single-path,
>   assume-VT `leaves = 1`** justification (`spineCappedCanonizer`). The canonizer is now the **interleaved stepwise
>   alternating fixpoint** (`…∘phase2∘phase1…`; IR §11.11), so the node count must be re-established against the
>   branching/interleaved object — the poly guarantee is the **verify-consume monovariant** (each verified consumption
>   strictly reduces residual symmetry; each rigid force reduces free relations) + the **fusion-severity look-ahead
>   bound** (IR §11.11), not a single `n`-deep path. Cost composes as a **fold over alternation depth**; the abelian
>   fused case is an inline poly interleave (measured **sum-not-product**, `[[project_rru_cost_probe_2026-07-10]]`), so
>   Phase-1 symmetry work does not multiply Phase-2 rigid branching.
> - **The flag is the MUTUAL STALL, not `base > baseMax`.** Consumption is **verify-gated** (a rigid residue stalls, it
>   is never harvested), so the threshold-gated assume-VT prune (§7a) — which could misprune a *fused* rigid residue
>   (Chang-A) — is retired. `none` fires exactly when neither the oracle nor the rigid solver can take a step.
> - **The carried hypothesis shrinks from `NoFusion` to "no non-abelian fusion in a rigid medium"** (IR §11.14 /
>   `chain-descent-cameron-entanglement.md` Route A): the abelian half of fusion is discharged constructively by the
>   solver kernel (Smith solve), so no fusion-mildness theorem is needed; the remaining risk is carried like the
>   symmetric seal's "or Cameron". See `chain-descent-endgame-spec.md` §1a and `chain-descent-deferred-decisions.md`.
> - **Live cost frontier:** re-base the node-count bound onto the interleaved object (mixed-composition Stage 4); the
>   quasipoly-seal pilot below still validates the per-node `w` machinery and is unaffected.
> - **★ THE OBJECT TO COST NOW EXISTS (2026-07-13): `ChainDescent.Descend.descentCost`** — the `cost` projection of
>   `descend`, the same definition ①a/①b/①c are proved of (`Descend.lean`; the D1 "cost co-defined with the value"
>   decision, realized). **② is now the main open obligation.** Two concrete tasks: (a) prove a node bound for the
>   **branching** descent — the **verify-consume monovariant** (each covering-narrowing strictly reduces residual
>   symmetry; each force reduces free relations; each defer is bounded by the branching bound); (b) replace `descend`'s
>   **`fuel`-exhaustion `none`** — a deliberate *placeholder* — with the real **mutual-stall** flag.
>   **⚠ FUEL IS PER-LAYER AND MUST STAY THAT WAY:** every branch at a level gets the same fuel and the accumulated cost
>   is **never fed back into it**, so no earlier resolver can drain a shared budget and make a *later, polynomial*
>   resolver flag through no fault of its own. This keeps "resolver `R` never flags on class `X`" a **local** statement
>   about `R`. Do not "optimize" this into a threaded global budget.

**Built substrate (reusable; live source `ChainDescent/CostModel.lean` + `ChainDescent/CanonForm.lean`, axiom-clean; the
authoritative record of what is proved is `PublicTheoremIndex.md`).**
- Framework: `CostM` + `budgetedIterate` + `cost_budgetedIterate_le`; the per-node cap `CappedCanonizer` (`cost_run_le` —
  ② with **no** per-node-cost hypothesis, the cap charges `min(trueCost, w)`).
- Concrete ② on the real descent: `descentCost_le` (`descentCost ≤ n⁴`, unconditional) via `spineCappedCanonizer`; the
  co-defined `costedWarmRefine` (cost = running the refinement loop, `= n³`, not a fiat literal).
- ①a: `CanonForm.canonForm?_sound` (`some cG ⟹ ∃π, cG = labelledAdj π G`) + `canonForm?_eq_none_iff` (the ③ hook) — the
  shared object ①a and ② converge on.
- *(Superseded, kept only in the Lean sources / for provenance — all keyed to the retired threshold-gated assume-VT
  flag, see the STATUS banner):* the fireable-flag `spineCappedCanonizerO` (quasipoly), the `baseMax`/`oracleCost`/
  `greedy_base_card_le_baseMax` P1-cost interface, and the confinement assembly skeleton. The still-live **D7
  renumbering** design fork is in §4 (not lost by trimming this log).

---

## 1. Purpose, and the relocation of "where poly lives"

The cost model discharges two `Publication.lean` obligations:
- **② `canon_poly_or_flag`** — `cost G ≤ costConst·n^costDeg ∨ canonForm? G = none`.
- **③-forward `residue_if_flag`** — `canonForm? G = none → UnhandledResidue G` (the weakened, `→`-only form:
  the `↔` was dropped because the headline never used `residue → flag`, and that backward direction is the
  prove-the-hard-case-fails direction the project struggles with).

**The design decision D3 (budget-capped) collapses ② and relocates the content.** If `canonForm?` is the
*budget-capped* descent — it flags the moment a fixed node budget is hit — then `cost ≤ budget` is true **by
construction**, unconditionally. This is not a weakening: the real algorithm already has a hard node budget
(the project's "cannot run exponentially" is a *settled, unconditional* guarantee). The consequence is that
the genuine research content — *handled graphs actually finish within the budget* — is not in ② at all; it
is **③-forward** (`handled ⟹ ¬flag`), and it is exactly the same content as the seal (reaches-rigid ⟹
discretizes in a bounded number of nodes). **This is where "poly stops being a meta-argument."**

Reading, in one line: **② says "never over budget" (free); ③-forward says "the budget is generous enough
that handled inputs finish" (the work).**

**Demonstration → prerequisite (the 2026-07-07 shift; §7a).** The original framing treated the cost model as an
*external demonstration* — a post-hoc certificate whose failure costs only completeness, never correctness. The
per-node-flag mechanism (§7a) changes this: a Phase-1 flag ⟹ vertex-transitive ⟹ **assume-the-harvest-and-prune**, which
*handles* node-4/Cameron in poly by **using the flag inside the pruning decision**. A wrong flag is then a *correctness*
bug, so the cost/flag mechanism is a **load-bearing prerequisite of the algorithm**, and ① (on the non-rigid residue) is
conditional on the *confinement lemma* (`Phase-1 flag ⟹ primitive rank-3 / VT residue`; plan: route-c-plan §7c). The
only place the flag still emits `none` is the **rigid Phase-2** residue (IR row-4) — the design boundary of "non-rigid".

---

## 2. The seven decisions (locked), each with its realization

| # | Decision | Resolution | Realized by |
|---|---|---|---|
| **D1** | Model of computation / granularity | **Cost monad** — cost carried *with* the value, tied to the code; not a parallel bookkeeping function. Declared unit-cost primitives (D7) are the residual meta-surface. | `CostM`, `bind`, `tick`, `cost` |
| **D2** | Cost decomposition | **`cost = node_count × per_node`** — localizes the hard content (`node_count` ← seal/branching) away from the easy (`per_node` ← concrete poly). | `budgetedIterate` (fuel=nodes, `w`=per-node); `BudgetedCanonizer.nbud`/`w` |
| **D3** | Budget-capped vs uncapped | **Budget-capped** ⟹ ② unconditional, content relocated to ③-forward (§1). Matches the real hard-budget algorithm. | `cost_budgetedIterate_le`, `BudgetedCanonizer.cost_run_le` |
| **D4** | Node-accounting model | The descent is a **node-sequential traversal**: `σ` carries the branch frontier/stack + best-so-far, `step` processes one node, `fuel` = total node budget. Branching lives *inside* `σ`, so the linear iterate counts the whole tree. | `budgetedIterate` + the §3 `σ` framing |
| **D5** | Bound form | **Explicit `C·n^k`** (not `∃ p : Polynomial`): honest, avoids formalizing the class P, reviewer reads the degree. Degree TBD from `w`·`nbud`. | `BudgetedCanonizer.nbud`/`w`; `Publication.costConst`/`costDeg` |
| **D6** | Input size measure | **Vertex count `n`** (poly in `n` ⟺ poly in bit-size `n²`). | `nbud n`, `w n` |
| **D7** | Declared unit-cost primitives | An **explicit list** of what counts as one tick (e.g. an `F_q` op, one `warmRefine` signature compare). Proven poly-size where cheap; declared where formalizing bit-cost is disproportionate. The new, small "meta" footprint. | §4 + §8 |

**Optional later (noted, no planning needed):** D3's cap may get a *disableable* flag for downstream
convenience — a runtime knob, not part of the showcase. It does not change any statement above.

---

## 3. The framework as built, and the D4 traversal-state framing

```
CostM α            := α × Nat                        -- value with its tick count (D1)
budgetedIterate step done fuel s : CostM (Option σ)  -- run ≤ fuel steps; some = leaf, none = FLAG
cost_budgetedIterate_le : (∀ s, cost (step s) ≤ w) → cost (budgetedIterate … fuel s) ≤ fuel · w
done_of_budgetedIterate_some : (budgetedIterate … s).1 = some s' → done s'
BudgetedCanonizer σ := { step, done, nbud, w, hstep }   -- packages the explicit budget nbud·w
BudgetedCanonizer.cost_run_le : cost (run M n s₀) ≤ nbud n · w n     -- ② for free, unconditional
```

**The key modeling choice (D4).** The descent *branches* (k-way at a cell with k orbits), and the poly
target is the leaf count `∏ bᵢ`, not the depth. Yet the framework's `budgetedIterate` is a *linear* loop.
These reconcile by choosing the state `σ` to be the **traversal configuration**: the current branch frontier
(a stack of pending subproblems) plus the best-so-far canonical candidate. Then:
- `step s` = "process the next descent node" (refine + oracle at that node, push/pop the frontier);
- `fuel` = the **total node budget** (not depth);
- `done s` = "frontier empty, lex-min settled";
- `cost ≤ fuel · w` = **(total nodes) × (per-node work)** — exactly the D2 decomposition, counting the whole
  branching tree, with the branching hidden inside `σ`.

This is why the linear iterate suffices: no tree-shaped recursion is needed, and the node budget bounds the
tree size directly. Defining this concrete `σ` (and `canonForm?` as its `BudgetedCanonizer`) is the
first Runtime-Phase build.

---

## 4. Per-node cost `w` (D2 easy half; D7)

`w n` bounds the work at a single descent node. Its constituents, each concretely polynomial in `n`:
- **`warmRefine`** — 1-WL refinement: `n` rounds, each a pass over `Fin n × Fin n` with a signature sort.
  Concretely `O(n² · …)`; **buildable now** against the real `ChainDescent.warmRefine` (this is the natural
  next brick after the framework — it also exercises the seal-side import path early).
- **The oracle** — orbit certification at the node: group ops / Gaussian elimination (rigid) / form recovery
  (Route C), all poly-size `F_q` arithmetic.
- **Selection** — the partition-invariant target-cell selector; a pass over cells.

**The R1 / Aut-free connection (important).** `w` must count the oracle's *actual* work. If the oracle
computes `Aut` (as the de-risking F1 path does, consuming `O_p(Aut)`), that computation's cost enters `w` —
and its poly-ness is the meta-circularity concern of route-c-plan §7a. The **Aut-free geometric
coordinatizer (R1)** is precisely what keeps `w` poly for the affine-polar pilot without a circular
`Aut`-computation. So R1 is not only a Seal-Phase cleanliness item — it is a *prerequisite for a poly `w`* on
the pilot family. Any node whose honest `w` cannot be shown poly forces that family into `UnhandledResidue`
(§7).
**Scope note (route-c-plan §7a 2026-07-06 refinement):** this bites only on the **poly** oracle — the *quasipoly*
pilot's per-node work is warmRefine-based (isotropy-count separation, Aut-free, no R1). For the poly oracle, R1's
poly `w` is an **effective-construction obligation** (line-recovery → classicality → coordinatize by linear algebra),
manifestly poly and **distinct from the WL-dim wall**; the per-graph obligation narrows to *certify vertex-transitive
membership* (explicit `Aut`-harvest shown unnecessary — existence of transitivity suffices), classicality **cited**
(Buekenhout–Shult / Payne–Thas), poly-time an obligation not an axiom.

The D7 list = the leaf primitives these decompose to (one `F_q` op, one signature compare, …), each either a
proven poly-size lemma or an explicitly declared unit cost.

**★ FINDING from the `warmRefine` brick ([`ChainDescent/ScratchCostModelWarmRefine.lean`](../GraphCanonizationProofs/ChainDescent/ScratchCostModelWarmRefine.lean), axiom-clean).**
Two facts are proved against the *real* `warmRefine`: it is exactly `n` rounds (`warmRefine_eq_iterate`), and
each per-vertex signature has exactly `n-1` entries (`signature_card`) — so the structural cost is
`warmRefineCost n = n · (n · sigCost n)`, cubic under the declared per-vertex `sigCost n = n`
(`warmRefineCost_eq`). **But the current Lean `refineStep` recolours via `Encodable.encode (sigKey …)` with
NO cell renumbering**, so colour Nats blow up in bit-size across rounds (encode∘encode∘…). Consequence: this
cubic bound is honest **only under a unit-cost-RAM D7 declaration** (colour compare/encode = O(1)); a genuine
*bit-cost* poly bound requires a **renumbering `refineStep` variant** (cells → `0..k-1` each round, as the C#
does). So the cost model must either (i) put "colour comparison / encode" on the D7 unit-cost list
explicitly, or (ii) have the Runtime Phase define the renumbering variant. This is a real design fork, not a
formality — flagged here and in the brick; decide it when `canonForm?`'s `refineStep` is chosen.

> **★★ D7 FORK RESOLVED — AND ITS DIAGNOSIS CORRECTED (2026-07-13, `ChainDescent/Refine.lean`, in `build.sh`,
> axiom-clean).** The fork is closed by **(iii): drop `Encodable.encode` ENTIRELY** — an option neither (i) nor (ii)
> below contemplated.
>
> **The old diagnosis was wrong.** Both (i) and (ii) assume the problem is *cross-round compounding*
> (`encode ∘ encode ∘ …`) and that rank-renumbering the round's **output** (`vertexRankNat ∘ refineStep`, the
> `ScratchRenumber` primitive) therefore cures it. **Measured: a SINGLE `refineStep` at `n = 3` already fails to
> `#eval` to completion.** The `Encodable.encode` *value* is infeasible after **one** round, before any compounding —
> so renumbering the output cannot help, because the encode is still paid once per vertex per round.
>
> **The encode-free structural round.** `sigKey` is *already* a canonically-sorted `List Nat`, and
> `Descend.lexLeList` is *already* proved a **total order** (`lexLeList_{refl,total,trans,antisymm}`). So the round
> ranks the **keys themselves** under that order and **never forms a `Nat` encoding at all**. Colours land in
> `0..n-1` by construction (`refineRound_lt`); the partition is unchanged (`sigKey_eq_iff`). This is the **strong**
> paper claim — no unit-cost declaration is needed for colour ops, because there is no encode to declare away.
> `refineEquivariant_encodeFree` + `refineSplits_encodeFree` discharge both of `descend`'s refiner obligations.
>
> **No `@[implemented_by]`** (it can assert a false equation ⟹ `#eval` could lie): the runnable version is tied to
> the reasoned-about one by a **proved equation**, `warmRefineMat_eq`.
>
> *(The (i)/(ii) analysis below is retained for provenance. (i) remains a valid fallback; (ii) is superseded — it
> does not actually fix the executable.)*

**★ D7 fork scoping (2026-07-07) — renumbering (ii) is the better target and is only *moderately* harder than the
declaration (i), because rank-compression is order-preserving.** Costs of each:
- **(i) declare colour-ops unit-cost** — *zero* Lean work (add one D7 list entry; the existing
  `refineStep = Encodable.encode (sigKey …)` stays). But it is the *weakest* paper claim: `encode∘encode∘…` colour
  bit-size genuinely blows up super-linearly, so a reviewer auditing a **bit-cost** bound sees the blow-up declared
  away. Standard for unit-cost RAM (WL is `O(n³)` there), but soft. Always available as a fallback.
- **(ii) renumbering `refineStepR`** — rank-compress each round's colours to `0..k-1`, so colour Nats stay `≤ n`
  (bit-size `O(log n)`) and the cubic bound is honest in **bit-cost**. **The de-risking insight:** rank-compression
  is *order-preserving*, so it preserves BOTH the partition (same fibres) AND the colour order — hence `vertexRank`
  and `canonForm` are **literally unchanged**. So (ii) is NOT a spine re-derivation: it is one `refineStepR` def + one
  inductive **order-equivalence bridge** (`refineStep` and `refineStepR` are related by an order-preserving colour
  bijection at every round ⟹ `samePartition` + equal `vertexRank`), after which the whole spine/soundness transfers
  and only the *cost measure* moves onto the bounded-colour variant. The one place it could get fiddly is proving the
  order-equivalence invariant *propagates through a refinement round* (a multiset-signature relabelling argument) —
  worth a spike to confirm before committing.
- **Verdict:** target (ii) (matches the C#, honest bit-cost, tractable via the order bridge), keep (i) as the
  no-build fallback if the bridge invariant proves annoying. Note the per-node cap already contains the *bound*
  honesty (it charges `w` regardless of colour size); (ii) only sharpens the D7 *declaration* to be bit-cost-defensible.
- **★ 2026-07-07 update — (ii) is now a PREREQUISITE, not just a declaration-sharpener.** The executable track's Tier B
  (`chain-descent-executable-track.md`) made the leaf labelling computable, and `#eval`-ing it **hangs on the colour
  blowup** — `vertexRank` comparisons over `Encodable.encode`-iterated `Nat`s. So for a *runnable* executable, the
  renumbering variant (ii) is required, not optional. This promotes (ii) from "nice for bit-cost honesty" to "gates the
  runnable demo." Recommend building it next on the executable track.

---

## 5. The consumption bridge — node count ≤ `nbud` (D2 hard half; ③-forward)

The one non-free ingredient: **the node count on handled inputs is ≤ `nbud n`.** This is where the seal is
consumed and "poly stops being meta." Decomposition:

```
total nodes  ≤  (leaf count) × (max depth)
leaf count   ≤  ∏ᵢ bᵢ            -- bᵢ = #orbits in the selected cell at level i  (recovery-route)
max depth    ≤  |T|              -- the individualization base size (the seal's base bound)
```

- **Depth** `|T|` is bounded by the seal's base bound — for affine-polar, `reachesRigidOrCameron_affinePolar`
  carries `T.card ≤ 128·(Nat.log 2 ((p^d)²)+1) = O(d log p)`.
- **Branching** `bᵢ` is bounded per level — `bᵢ ≤ q²` for span-dim-1 (recovery-route `ScratchSpanDimBound`),
  with the crude a-priori `#orbits ≤ |K|^{|S|+1}` as a fallback.

**Quasipoly (pilot, achievable now):** `∏ bᵢ ≤ q^{O(d log p)}` and depth `O(d log p)` ⟹ node count
quasipoly ⟹ `nbud n = n^{O(log n)}` suffices ⟹ handled affine-polar residues return `some` (no flag).
**Poly (later):** identical shape once the open `∏ bᵢ ≤ poly` branching bound lands (recovery-route T0). **The
framework, the pilot mechanics, and the bridge are all reused verbatim; only the branching bound sharpens.**

This is the strategic payoff (§ STATUS): the cost-model *framework* is decoupled from the open research —
buildable and pilotable now on the closed quasipoly seal, with the poly result dropping in later.

---

## 6. The pilot — affine-polar, quasipoly

**Target.** Instantiate `BudgetedCanonizer` on the affine-polar `VO^ε` residue and prove:
1. **per-node** `w n ≤ n^c` (§4) — from `warmRefine` + the (Aut-free, §4) oracle;
2. **node budget met** `handled G → ∃ s', (run M n s₀).1 = some s'` (§5) — the descent discretizes within
   `nbud n = n^{O(log)}`, from the seal's base bound + the span-dim-1 branching bound;
3. compose with `cost_run_le` (② free) and correctness (①) ⟹ the affine-polar residue is canonized within a
   **proven quasipoly cost**, in the Lean cost model.

**What it exercises:** every framework piece except the poly-specific branching bound; the seal→runtime
consumption; the D4 traversal `σ`; the D7 `w`. It is the first end-to-end structural-bound → runtime-cost
proof in the project, and the template the poly case reuses. **Note honestly:** it proves *quasipoly*, not
poly — the mechanism is validated, the degree is not yet polynomial.

**Dependencies:** the Runtime-Phase descent model (`canonForm?` as a `BudgetedCanonizer`), which is the
gating build; and (for a poly `w`) R1.

---

## 7. The coupling: budget level ↔ what's provably poly ↔ `UnhandledResidue`

③-forward (`handled ⟹ ¬flag`) requires the budget `nbud·w` to be ≥ the *true* node count on handled graphs.
So the budget's degree is **exactly the best provable node bound across all handled families**, and anything
worse gets flagged — hence must sit inside `UnhandledResidue` for ③ to hold. Concretely:
- A family with a proven poly node bound → inside the budget → handled.
- A family only provably *quasipoly* (or only meta) → either the headline degrades to "quasipoly-or-flag" for
  it, **or** it moves into `UnhandledResidue`.

This is the exact mechanism by which the firewall bites: a *meta*-poly family (Route C today) either becomes
a real `cost ≤ poly` proof (via this cost model) or goes into the excluded residue. It cannot be axiomatized.
The cost model is thus the instrument that decides, per family, "handled at poly" vs "excluded."

### 7a. Per-node flag, witness-or-flag, and the assume-VT poly mode (2026-07-07) — SUPERSEDED (2026-07-12)

> **⚠ SUPERSEDED — the threshold-gated assume-VT prune is retired.** This section flagged on `base > baseMax` and then
> **assume-VT-pruned** the flagging (Phase-1) residue *without verifying an automorphism*. That crash-landed on fusion:
> a conditional symmetry fused with a rigid decision (Chang-A) is not vertex-transitive, so assume-VT-pruning it is
> unsound, and the guard needed a fusion-mildness theorem that does not exist. The current engine is **interleaved** and
> **verify-gated** (IR §11.11): the oracle consumes only via a verified automorphism, so a rigid/fused residue **stalls**
> instead of being pruned; the abelian fused case is de-fused constructively by the rigid solver's kernel; `none` fires
> at **mutual stall**. Correctness ① is therefore conditional on the **fusion obligation** ("no non-abelian fusion in a
> rigid medium", carried like "or Cameron"), NOT on a threshold-gated confinement lemma. Read the rest of this section
> for the per-node-cap mechanics (still valid: a node cannot exceed `w`, so ② stays unconditional) and the phase-tagged
> `UnhandledResidue` idea (still valid) — but NOT for the assume-VT-prune-on-threshold soundness story.
>
> **▶▶ REVIVED IN REPAIRED FORM 2026-07-27 — `ChainDescent/KeyComplete.lean`, analysis in
> [`scratchpad/DUAL_resolver_scoping.md`](../scratchpad/DUAL_resolver_scoping.md) §10.** The *idea*
> (consume unverified when nothing separates, licensed by an automorphism that exists but was never
> computed) is sound; what killed it here was the **antecedent**. Replace the threshold `base > baseMax`
> by *"the force key separates every non-automorphic pair"* (`KeySeparatesAt`) and obituary A is repaired
> structurally: Algorithm A had **no force resolver**, so "unresolved" conflated *VT* with *fused*, and
> Chang-A's rigid decision — exposed once the symmetry is consumed, `A_stall < A_full` — is exactly what
> a force resolver acts on, so the predicate is FALSE there and the licence never fires. The separate
> 2026-07-10 vacuity failure (`ConfinementCitations.hflag` uninhabited) does **not** transfer; that was a
> universally-quantified citation bundle. **⚠ But read §10.2/§10.4 before scoping it as a weakening — it
> is a UNIFICATION** (consume's `Tinhofer` absorbed into force's separation obligation, two carried
> predicates → one), and the 2026-07-10 audit's FORK still applies: the antecedent is informative only
> when non-separation means *"none exists"* rather than *"the key deferred"*.

Refining the flag from a **global** to a **per-node** budget (a small `budgetedIterate` variant: flag the moment one
node's work hits `w`, recording *which phase* flagged) yields two consequences. Authoritative writeup:
[`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md) §7b; summarized here for the cost model's obligations.

- **Per-node cap contains the honesty issues.** A node physically cannot exceed `w`, so ② stays unconditional
  (`cost ≤ nbud·w` by construction) *and* the §4 `warmRefine` colour-blowup stops threatening the bound — the D7 fork
  becomes only about the flag *threshold*, not the cost accounting.
- **The flag's phase discriminates the `UnhandledResidue` atom (structural — fixes the firewall soft-spot).**
  Phase-1 flag → node-4/Cameron (vertex-transitive); Phase-2 flag → rigid (IR row-4). Define the atoms by *which phase
  flagged* (a structural fact via the confinement lemma), **not** by "handled sub-classes" (algorithm-relative). This is
  the issue-#1 fix carried into `Publication.lean`.
- **One canonizer — witness-or-assume (no separate "safe mode").** At a Phase-1 node: harvest succeeds within budget ⟹
  it *is* a certified orbit ⟹ prune soundly (VT *witnessed*); harvest exceeds budget ⟹ the flag fires and, by the
  confinement lemma, the residue is node-4/Cameron ⟹ VT ⟹ pick any root and prune *without* exhibiting the automorphism.
  Either way is *prune-and-continue* ⟹ single-path poly; **node-4/Cameron are handled, not flagged.** A flag emits
  `none` only in **Phase 2** (rigid / IR row-4). So the algorithm is **poly-time and complete on the non-rigid residue**.

**★ The reframe this forces — the cost model is no longer only a *demonstration*.** The flag/budget mechanism is *used by
the algorithm to decide to prune*, so it is **load-bearing for correctness (①)**, not external accounting:
assume-VT-prune on a non-VT residue is a *correctness* bug, so **① on the non-rigid residue is conditional on the
confinement lemma** (`Phase-1 flag ⟹ primitive rank-3 / VT residue`). The sporadic-node-4 soundness worry = the carried
`SchurianScheme` model-faithfulness gap, now a **soundness obligation** (killed on the flagged subset by the *largeness*
clause — small-`Aut` non-Schurian SRGs don't flag). This is the sense in which "the cost model moved from demonstration
into a prerequisite for the algorithm." Plan for the whole non-rigid correctness proof (sub-obligations P1–P4):
route-c-plan §7c. See also §1 (the relocation).

---

## 8. The residual meta-surface — what "poly" means after this

Today the project disclaims: "poly is a meta-claim; no runtime model." After the cost model, that blanket
disclaimer is replaced by a **small, explicit** one: "poly *in the declared cost model*", whose only
non-Lean content is the **D7 unit-cost primitive list** (the handful of primitives declared unit-cost rather
than bit-cost-formalized). The paper states that list. This is a large honesty upgrade — from "no runtime
model" to "a Lean runtime model with an explicit, inspectable primitive-cost declaration."

---

## 9. Build notes, risks, open items

**Build notes.**
- The framework is **core-only** (no Mathlib): `import Mathlib` is pathologically slow in this env (timed out
  past 8 min), and the framework needs only `Nat`/`Option`/`Prod` + `omega`. Keeping the reusable core
  Mathlib-free is a bonus — it stays fast. **The pilot is heavy**: instantiating on the real affine-polar
  residue pulls in the seal (hence Mathlib), so expect slow compiles there.
- Verify: `cd GraphCanonizationProofs && lake build ChainDescent.ScratchCostModel` then a `#print axioms`
  check file — expect `[propext, Quot.sound]` for the framework theorems.

**Risks / open items.**
- **The D4 descent-model extension is the biggest new build** — defining `canonForm?` as a `BudgetedCanonizer`
  over the branching traversal `σ`. It is Runtime-Phase and gates the pilot's steps 2–3.
- **The pilot's branching bound must be confirmed sufficient** — span-dim-1 `bᵢ ≤ q²` + the a-priori bound
  must compose to a quasipoly node count; confirm the general (span-dim ≥ 2) affine-polar case is covered by
  the seal's discreteness, not left open.
- **D7's declared primitives are a judgement call** a reviewer may push on — keep the list minimal and
  proven-where-cheap.
- **`w` poly-ness depends on R1** for the *poly* oracle (§4; the quasipoly pilot rides warmRefine, no R1). R1's
  poly `w` is a **non-wall effective-construction obligation** whose per-graph core is *certify vertex-transitive
  membership* (not full coordinatization / Aut-harvest); classicality is cited (Buekenhout–Shult / Payne–Thas), the
  `d=4` GQ case is the residual, and there is **no KNOWN poly transitivity-test shortcut** (VT is reducible to GI but
  NOT known GI-hard — open, not barred; WL-blocked for n div by 16). Detail: route-c-plan §7a (2026-07-06 refinement,
  corrected 2026-07-07).
- **The renumbering / unit-cost-colour fork (§4 FINDING)** must be decided when `canonForm?`'s `refineStep`
  is chosen: declare colour-ops unit-cost (D7), or build a renumbering `refineStep`. Under the current
  `Encodable.encode` refineStep, only the unit-cost-RAM reading gives a poly `warmRefine`.

---

## 10. Pointers
- Framework: [`ChainDescent/ScratchCostModel.lean`](../GraphCanonizationProofs/ChainDescent/ScratchCostModel.lean).
- The obligations it serves: [`GraphCanonizationProofs/Publication.lean`](../GraphCanonizationProofs/Publication.lean) §3 (② + `residue_if_flag`).
- Endgame map + the ②-safety / ③-completeness refinement: [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md).
- Seal base bound (pilot input): `reachesRigidOrCameron_affinePolar` ([`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md)).
- Branching bound (poly upgrade): [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md).
