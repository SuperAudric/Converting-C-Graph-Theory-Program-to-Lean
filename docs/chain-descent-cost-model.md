# Cost model — the Lean runtime cost framework and the poly bound

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

**The framework is landed and axiom-clean; the pilot is the live frontier.**
[`ChainDescent/ScratchCostModel.lean`](../GraphCanonizationProofs/ChainDescent/ScratchCostModel.lean)
(core-only, WIP, not in `build.sh`) builds the cost monad + the budgeted process + the ② mechanism. The
three framework theorems verify axiom-clean — in fact tighter than the project bar: `[propext, Quot.sound]`,
**no `Classical.choice`**. Landed decls: `CostM` (+ `bind`/`tick`/`cost` lemmas), `budgetedIterate`,
`cost_budgetedIterate_le` (the ② heart), `done_of_budgetedIterate_some`, `BudgetedCanonizer` +
`cost_run_le`.

**What building it settled.** ② (`canon_poly_or_flag`) is **unconditional by construction** — `cost ≤ budget`
holds with *no* hypothesis (the `∨ flag` disjunct is not even needed for the cost side). So **all**
poly-completeness content lives in **③-forward** (`residue_if_flag`: `handled ⟹ ¬flag`), never in ②. This
refines the endgame-spec's obligation map: **② is the unconditional *safety* guarantee (never exceeds
budget); ③-forward is the *completeness* content (handled inputs actually finish within it).**

**The per-node `w` brick has started (2026-07-06).**
[`ChainDescent/ScratchCostModelWarmRefine.lean`](../GraphCanonizationProofs/ChainDescent/ScratchCostModelWarmRefine.lean)
(axiom-clean) lands the **warmRefine summand** of `w`: `warmRefine_eq_iterate` (n rounds, real) +
`signature_card` (per-vertex input size `n-1`, real) + `warmRefineCost_eq` (`= n·n·n` under the declared
`sigCost n = n`). It also surfaced the **renumbering / unit-cost-colour finding** (§4 FINDING): the current
`Encodable.encode` `refineStep` blows up colour bit-size, so poly holds only under a unit-cost-RAM D7
declaration (or a renumbering variant) — a fork to decide when `canonForm?`'s `refineStep` is chosen.

**What's left (the pilot, gated on the Runtime-Phase descent model):** (a) the rest of `w` — `oracleCost`
(gated on R1 for a poly, not just quasipoly-with-Aut-harvest, oracle) + `selectCost` (small, buildable now);
(b) `canonForm?` as a `BudgetedCanonizer` instance (the D4 traversal-state descent); (c) the
node-count-on-handled-inputs bound that feeds the seal's base bound — the quasipoly pilot. §5–§6.

**★ Per-node flag + assume-VT (2026-07-07, §7a).** Refining the flag to a **per-node** budget (a small `budgetedIterate`
variant, flagging per node + recording phase) gives: (i) ② stays unconditional and the §4 colour-blowup stops
threatening the bound; (ii) the flag's *phase* structurally discriminates the `UnhandledResidue` atom (issue-#1 firewall
fix); (iii) the **canonizer itself** — a Phase-1 flag ⟹ VT ⟹ assume-the-harvest-and-prune (node-4/Cameron *handled*,
single-path poly; `none` only in rigid Phase 2). This makes the flag/budget mechanism **load-bearing for correctness ①**
(conditional on a *confinement lemma*), so the cost model shifts from a demonstration into a **prerequisite of the
algorithm**. Plan: route-c-plan §7c (sub-obligations P1–P4; P4 reduced to the citable Witt flag-transitivity).

**★ Per-node-cap variant LANDED (2026-07-07, `ScratchCostModelPerNode.lean`, core-only, axiom-clean `[propext,
Quot.sound]`).** `capStep` charges `min(trueCost, w)` per node; `cost_budgetedIterate_capped_le` + `CappedCanonizer`
(no `hstep` field) give **② unconditionally with NO per-node-cost hypothesis** — the cap relocates the assumption into
the algorithm, so a quasipoly harvest doesn't break the bound (it flags, `flagsAt`). `Phase` (symmetric/rigid) records
the flag phase. **Attachment decision (scoping):** instantiate over **`defaultSpineChain`** — node bound already proven
(`defaultSpineChain_reaches_leaf : ∃ k ≤ n, IsLeaf` ⟹ `nbud = n`), correctness via `spine_branch_independent` +
`SpineChain.canonAdj` (→ `canonForm?`), per-node work = `warmRefine` + oracle. It is single-path (assume-VT `leaves=1`),
so the branch-frontier σ of §3 is **not needed** for the poly target; the `≤ n` path is the whole cost.

**★ CappedCanonizer INSTANCE over the real spine LANDED (2026-07-07, `ScratchCostModelSpine.lean`, axiom-clean
`[propext, Classical.choice, Quot.sound]`).** `spineCappedCanonizer` instantiates the capped canonizer over
`defaultSpineChain` (σ = the descent level `k`; `step` advances a level; `done` = leaf/discrete; `nbud = n`;
`w = warmRefineCost n`). Capstone **`spineCappedCanonizer_cost_le`**: the run costs **`≤ n · warmRefineCost n = n⁴`,
unconditionally** — the first *concrete* ② discharge on the actual canonizer's descent (matches the C#
`DefaultBudget`'s `16·n⁴`). The per-node cap makes it free of any per-node-cost hypothesis.

**★ CO-DEFINED cost upgrade (2026-07-07, `ScratchCostModelCostedWarmRefine.lean` + spine, axiom-clean).** Closed the
D1 "fiat cost" seam: the per-level charge is no longer a literal but the **actual accumulated cost of running the
refinement loop**. `costedWarmRefine` runs `n` costed rounds in the cost monad with `value_costedWarmRefine :
value = warmRefine` (all spine correctness transfers) and `cost_costedWarmRefine : cost = warmRefineCost n`
(accumulated by the loop, via the reusable `CostM.iterate` + `cost_iterate_const`). The spine `step` now charges
`(costedWarmRefine adj chₖ.P chₖ.χι).cost`, and `spineCappedCanonizer_step_cost` proves that charge `= warmRefineCost
n` — so "the spine CAN be refined in n³" is now "running the refinement IS n³ (co-defined)". Per-round `roundCost n`
is the D7-declared unit.

**★ ①a `canon_sound` DISCHARGED on the real spine (2026-07-07, `ScratchCanonSound.lean`, axiom-clean `[propext,
Classical.choice, Quot.sound]`) — the FIRST `Publication.lean` obligation crossed into the real runtime.** Defines a
spine-level `canonForm?` off `defaultSpineChain` (extract the reached leaf via `defaultSpineChain_reaches_leaf`, emit
`some (canonForm …)`; never flags — flagging is the cost side) and proves `canonForm?_sound`: a `some cG` output is
`∃ π, cG = labelledAdj π adj` — the `Publication.canon_sound` shape, against the *actual* descent, not the `opaque`
stub. The content lemma `canonForm_isLabelledAdj` is nearly definitional (`SpineChain.canonAdj` **is** `labelledAdj
(rankPerm …) adj`; the lex-min `canonForm` is one such image via `canonForm_mem_image`), so it is reusable regardless
of the leaf-extraction / `Option` wrapper.

**★ ①a carried pieces CLOSED — a parameter-free canonizer (2026-07-07, same module).** The three carried descent
parameters are now discharged to concrete canonical choices, giving `canonFormOf : AdjMatrix n → Option (…)` (the exact
`Publication.canonForm?` shape) + `canonFormOf_sound` (the exact `canon_sound` shape), axiom-clean. Scoping outcome:
`P₀ := unknown` everywhere (antisymmetric by `rfl`) and `χι₀ := 0` (no carried predicate) are **trivial**; the selector
is the one carried piece with content — `nonDiscreteSel χ` = the whole non-discrete part, chosen `PartitionInvariant`
(pure partition data — what the spine's cross-branch sharing needs, and what a raw-colour-min rule *fails*, per
ChainDescent.lean §968), discharging `TargetsNonsingletonCell` + `NonemptyOnNonDiscrete` trivially. It over-individualizes
(a ② *efficiency* matter, not ①a); since `canonForm_isLabelledAdj` is **selector-agnostic**, ①a transfers to the eventual
single-cell ② selector for free.
**The one subtlety — final Publication wiring waits on the CAPPED canonForm?, NOT `canonFormOf` directly:** `canonFormOf`
never returns `none`, so wiring it as the final `canonForm?` would make ③ (`none → UnhandledResidue`) **vacuously true** —
a firewall breach. The real `canonForm?` = `canonFormOf ∘ budget-cap` (the flagging version); soundness transfers through
the cap (capping only restricts the `some` set to the same values), so ①a is *content-complete now* and its Publication
body lands with the capped object (② work). **So ①a is closed modulo the shared capped-canonForm? object that ② builds.**

**★ SHARED `canonForm?` OBJECT LANDED (2026-07-07, `ScratchCanonFormCapped.lean`, axiom-clean) — ①a and ② converge in
ONE object.** `CanonForm.canonForm? : AdjMatrix n → Option (…)` gates the sound `canonFormOf` by the real per-node-capped
spine descent (`spineCappedCanonizer`), so **cost + flag come from the actual capped run and the `some` value is the
sound canonizer**. Three theorems, all axiom-clean `[propext, Classical.choice, Quot.sound]`:
- **`canonForm?_sound`** — ①a on the *flagging* object: `some cG ⟹ ∃π, cG = labelledAdj π G` (`canonFormOf_sound`
  transferred through the gate). This is the `Publication.canon_sound` body.
- **`descentCost_le`** — ② cost side: `descentCost G ≤ n⁴`, **unconditional** (the per-node cap; no hypothesis). This is
  the `cost ≤ costConst·n^costDeg` side of `Publication.canon_poly_or_flag` (`Or.inl` always).
- **`canonForm?_eq_none_iff`** — the flag IS budget exhaustion (`canonForm? = none ↔ descentResult = none`), the ③ hook.
The Publication swap is now a one-liner set (`canonForm? := CanonForm.canonForm?`, `cost := descentCost`, `costConst=1`,
`costDeg=4`), deferred only so the opaque swap happens once alongside ③.
**Honest scope of the flag (keeps ③ non-vacuous):** at this level `w` is warmRefine-cost only, and the warmRefine descent
provably reaches a leaf within `n` nodes, so the fuel-`none` never fires — the object is currently *total*. The REAL flag
is the **oracle summand of `w`** (an expensive harvest exceeding the per-node budget ⟹ `flagsAt` ⟹ `none`), not wired yet
(gates on confinement-P1 / R1). So ③ is deliberately NOT claimed against this object yet — wiring the oracle-cost flag is
what makes `none` a genuine event and ③ dischargeable. **NEXT** = the oracle summand of `w` (fires the flag; gates P1).

**NEXT:** the value-side descent co-definition proper (σ = descent state, `step` = the real transition projecting to
`defaultSpineChain`) — the deeper "IS descended" level, on which ①b/②-completeness ride; then the oracle summand of `w`
(gates confinement-P1 — the correctness-critical piece), completeness (③-forward), and the Publication param-fixing.

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

### 7a. Per-node flag, witness-or-flag, and the assume-VT poly mode (2026-07-07)

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
