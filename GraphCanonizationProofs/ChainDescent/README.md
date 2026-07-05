# Lean proving reference — chain-descent canonizer

Orientation for the Lean side: the module layout, how the Lean model maps to the
C# implementation, the central modelling decisions, and what the model does and
does not capture. For **what is currently proved**, read
[`../PublicTheoremIndex.md`](../PublicTheoremIndex.md) (script-maintained, the
ground truth). For the **architecture and live frontier**, read
[`../../docs/chain-descent-declassing.md`](../../docs/chain-descent-declassing.md)
and [`../../docs/chain-descent-schreier-sims.md`](../../docs/chain-descent-schreier-sims.md).
For the **project idea + reading order**, start at
[`../../docs/00-START-HERE.md`](../../docs/00-START-HERE.md).

> This file is a stable modelling reference. It deliberately does **not** track
> proof progress (that drifts) — the theorem index does. A fuller pre-2026-06
> proving guide, including its dated proof-state log, is archived at
> [`../../docs/Archive/ChainDescent/chain-descent-lean-proving-guide-v1.md`](../../docs/Archive/ChainDescent/chain-descent-lean-proving-guide-v1.md).

---

## 1. Module layout

The active library is this `ChainDescent/` split plus the top-level
`ChainDescent.lean` that everything imports.

| Module | Proves / contains |
|---|---|
| `../ChainDescent.lean` (top level) | direction-invariance `warm_6_2` (invariant 6.2) and the descent **spine** (`spine_branch_independent`) — the canonizer-correctness substrate |
| `Saturation.lean` | the generic saturation engine: an extensive `Finset` operator reaches a fixpoint in bounded rounds (`exists_iterate_isFixed_within`) |
| `Scheme.lean` | `EdgeGenerates` + the de-classed metric/distance-regular family (`theorem_2_HOR_of_pPolynomial`) |
| `Cascade.lean` | Leg A recovery to a base; **Part A** — `StabilizerAt` (residual `Aut_S^P` as a Mathlib `Subgroup`), the harvest soundness + completeness seams, the order product |
| `CascadeOracle.lean` | the unified construct-and-check oracle `matchOracle` / `matchOracleSeq` |
| `LinearOracle.lean` | the linear (abelian / CFI) oracle |
| `CFI.lean` | CFI gadgets, gauge flips (`cfiFlipAut`), the `Z₂^β` cycle space, the CFI-cov coverage instance |
| `Group.lean` | permutation-group scaffolding |

> This table is the **core** substrate only. The forms-graph node-4 work is further modules in `build.sh` (not listed
> here): `CascadeAffine` + the ~14 pair-route modules (`…AffinePolarSeal`, the quasipoly `VO^ε` seal) and the **Route C**
> spine `RouteCTransport` / `RouteCFormAdapters` / `RouteCSeam` / `RouteCNode4` (form-recovery poly route — recover `Q`,
> canonicalize via its known Aut). The authoritative complete list is `scripts/build.sh` MODULES + `PublicTheoremIndex.md`;
> the Route-C narrative + decl homes are in [`docs/chain-descent-route-c-plan.md`](../../docs/chain-descent-route-c-plan.md).

---

## 2. The C# implementation being modelled

The canonizer is `GraphCanonizationProject/ChainDescent.cs` + `CanonGraphOrdererChainDescent.cs`:

- **`CanonGraphOrdererChainDescent`** — Tier-0 component decomposition, then
  dispatches each connected component to the harness.
- **`ChainDescent` (harness)** — `Search`: warm-refine the partition (1-WL); if
  discrete, emit a leaf; else pick the lowest-cell-id non-singleton cell (the
  iso-invariant *target cell*), ask the oracle which vertices to branch on, recurse.
  `Branch`: individualize `v` (write `v < w` for every cell-mate `w` into the
  partial-order matrix `P`), transitively close, recurse. `HandleLeaf`: build the
  permuted matrix, keep the lex-min, harvest verified automorphisms from coinciding
  leaves into a `PermutationGroup`.
- **Budget / flag.** A polynomial node budget; exceeding it raises
  `CanonizationFlaggedException` — an honest "not handled", never a wrong answer.
- **`ITransversalOracle`** — the T-C seam. The oracle supplies the a-priori
  transversals; without one the harness is a budget-bounded IR search.
- **`WarmPartition`** — 1-WL refinement, warm-started from the carried `CellOf`;
  each vertex's new colour is the lex-rank of `[own-colour, sorted multiset of
  (neighbour-colour, adjacency-value, P-relation)]`.

---

## 3. Lean ↔ C# correspondence

| Lean (`ChainDescent.lean`) | C# counterpart | Faithful? |
|---|---|---|
| `refineStep` / `signature` / `refineStep_iff` | `WarmPartition.RefineRound` | **Yes** — `refineStep_iff` (equal new colour ⟺ equal old colour ∧ equal signature multiset) is exactly `RefineRound` |
| `warmRefine` (iterate `refineStep` `n×`) | `WarmPartition.Refine` (iterate to fixpoint) | **Yes** — `n` rounds always reach fixpoint |
| `applyGuess P a b dir` (writes one entry pair) | `Branch` (writes `v < w` for the whole cell) | **Simplification** — single-pair models a 2-element target cell `{e,f}`, i.e. one genuine decision |
| `closeStep` / `transitiveClose` | `TransitiveClose` | **Diverges** — but TC is *relegated* (§4), so absent from the proof path |
| fresh-colour individualisation (`χι` hypotheses) | refinement separating the individualized vertex | **Model choice** (§5) — true by construction vs. by refinement |

`adj : AdjMatrix n` (a `Fin n → Fin n → Nat` wrapper); `P : PMatrix n`;
`χ : Colouring n`.

---

## 4. TC relegation — the central modelling decision

The C# `TransitiveClose` is a Floyd–Warshall closure of `less` that returns
`false` on a cycle (`i == j`) or a direction conflict (`cur == GREATER`); `Branch`
then prunes that child. The Lean model **relegates** transitive closure entirely:
a guess is just `applyGuess` writing one `(a,b)`/`(b,a)` pair — no closure in the
refinement loop. An inconsistent partial order is treated as a *lex-min ranking*
criterion, not a pruning step.

**Why this is equivalent (no refactor needed).** A non-lex-min branch is never
chosen, so "pruned" and "kept but ranked worse and discarded by lex-min" are
observationally identical for the canonical output: (a) a consistent partial order
always extends to a linear order, so a valid leaf exists below any consistent node;
(b) an inconsistent/cyclic configuration ranks strictly worse than any valid one.
The lex-min leaf is valid either way.

**Consequence for proofs.** The post-guess matrix is exactly `applyGuess P₀ a b dir`,
differing from `P₀` at *only* `(a,b)` and `(b,a)`. This is what makes invariant 6.2
provable. (The unconditional lemma "`transitiveClose` commutes with the
`less ↔ greater` swap" is **false** — `closeStep`'s `less`-first tie-break is not
σ-symmetric, machine-checked by `transitiveClose_swap_false` with witness
`conflictMatrix` — but `conflictMatrix` is exactly the kind C# `TransitiveClose`
rejects, so under relegation the question is moot.)

---

## 5. Fresh-colour individualisation

`warm_6_2` and relatives take a starting colouring `χι` in which the guessed
vertices `a`, `b` are **singletons** (hypotheses `ha`/`hb`). This models standard
IR individualisation (a fresh, unique cell id). It is equivalent to a design
assumption already in force — the oracle's transposition pre-check is justified by
"the guessed pair is always singletons after refinement." The C# realises this via
refinement separating the vertex by its `P`-signature; the Lean model makes it true
by construction, closing the gap a signature coincidence could otherwise leave.

---

## 6. The model objects and the (former) axiom

- `POE` — partial-order entry `less | unknown | greater`, with involution
  `POE.swap` (`less ↔ greater`, `unknown` fixed).
- `PMatrix n := Fin n → Fin n → POE`; `Colouring n := Fin n → Nat`.
- `applyGuess P a b dir` — set `P(a,b) := dir`, `P(b,a) := neg dir`, else `P`.
- `signature adj P χ v` — the multiset of `(χ u, adj v u, P v u)` over `u ≠ v`.
- `refineStep` — one 1-WL round, a **concrete `def`** (no longer an axiom, since
  2026-05-30): `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)`. Its
  partition behaviour is the **theorem** `refineStep_iff`:
  `refineStep … v = refineStep … w ↔ χ v = χ w ∧ signature … v = signature … w`.
  The encoding fixes a canonical, iso-invariant cell-id order; partition-level
  proofs are unchanged and concreteness additionally makes value-level
  (`*_transport`) facts provable.
- `warmRefine adj P χ := (refineStep adj P)^[n] χ` (`n` rounds suffice).
- `samePartition χ χ' := ∀ i j, χ i = χ j ↔ χ' i = χ' j` — same cell partition; an
  equivalence relation.

---

## 7. What the model does NOT capture (gaps)

- **Partition-only.** The model speaks of `samePartition` — which cells form, never
  which cell is "less". `warm_6_2` proves "same partition", not "order mirrored";
  the order-label half of invariant 6.2 is unmodelled.
- **Single-pair guesses.** `applyGuess` models a 2-element target cell; a `k > 2`
  target cell is not directly modelled.
- **No transitive closure.** Relegated (§4) — correct for 6.2, but the model cannot
  state anything about TC-derived relations.
- **No automorphism action.** No σ-action / equivariance in the base model, so the
  "branch one representative per orbit" reduction is justified separately — the
  **spine** (`spine_branch_independent`) and, for the group object, **Part A**
  (`Cascade.lean`).
- **No linear / `Z₂` structure** in the base model — supplied by `LinearOracle.lean`
  and `CFI.lean`.

---

## 8. The descent spine — cross-branch sharing

`warm_6_2` / `warmRefine_agree_off` share the *partition* across guess directions.
Pushing that through the descent recursion gives the IR-resistant work-sharing
result: **if target-cell selection is partition-invariant, the set of
individualized vertices, the partition, and the target cell are identical for every
branch at each level.** The tree of *partitions* is therefore a **path** (the
*spine*) of length `m ≤ n`; the `2^m`-way branching lives entirely in the order
labels overlaid on it. This is proved as `spine_branch_independent` (top-level
`ChainDescent.lean` §15), stringing the per-level lemmas (`warmRefine_agree_off'`,
`target_direction_blind` / `target_agree_off`) through the recursion. The spine is
why an automorphism found deep, if it fixes a shallow path, certifies shallow-level
orbits — the mechanism Part A formalizes cross-branch.
