# Executable track — raising the Lean canonizer to runnable form

> **What this is.** The scope + build plan for making the Lean canonizer **executable** (option B), not just a
> proof model: "provably exists, and here it is (runs), C# for normal use." Lower value than the feasibility
> proofs, pursued now so the executable is a corollary of the proofs rather than a painful retrofit later. It
> may be **abandoned** if it hits an unresolvable wall — the abandon-points are marked.
>
> **Companion:** [`chain-descent-cost-model.md`](./chain-descent-cost-model.md) (the cost model this couples to),
> [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md).

---

## STATUS (read first)

**Tier A DONE (2026-07-07) — the descent RUNS.** `spineCappedCanonizer`/`descent`/`descentResult`/`descentCost`
are now **computable** (a real `Decidable (Discrete)` / `Decidable IsLeaf` instance replaced the `Classical`
`done`; everything else on the descent path — `refineStep`, `warmRefine`, `defaultSpineChain`, the cost-model
core — was already computable). Validated by `#eval` (`ScratchExecutable.lean`): `descentResult triangle = some 1`,
`descentCost triangle = 27` (= warmRefineCost 3 = 3³). All theorems stayed axiom-clean. The descent — the part
that *finds the leaf and counts the cost* — executes.

**Still noncomputable (Tier B/C): the OUTPUT.** `canonForm?`/`canonFormOf`/`canonForm` remain noncomputable.

---

## The architecture decision (why executable is a separate track from the proofs)

The Lean side is a **proof model**; the executable is C#. The endgame theorem `canonizer` + `#print axioms`
never needs the Lean function to *run*. So executability is an **optional add** — pursued to close the gap
"provably exists, and the C# is *kind of* the thing I proved" → "provably exists, and **here it is**, C# for
normal use." The poly runnable is **downstream of the main proofs**, not parallel: see the wall.

## The lex-min reframing (validated 2026-07-07) — the key to a *poly* executable

A canonizer needs only ①a (output is a relabelling) + ①b (`canonForm G = canonForm H` when `G ≅ H`). **Lex-min
over all order-labels is NOT required** — it is one (exponential: `3^C(|D|,2)`) way to get ①b. What ①b truly
needs is a *canonical representative among symmetric alternatives*:
- **true symmetry (VT / assume-VT single-path):** branches are Aut-equivalent ⟹ any representative gives the
  same labelled matrix ⟹ **no min at all** (`leaves = 1`);
- **false symmetry (rigid):** must compare alternatives, but only the **poly-many** the budget allows.

So the exponential in the current `canonForm` (Spine.lean) comes from mining over **all** σ — conflating true
and false symmetry. The **orbit-pruned output is poly and iso-invariant**, and is *the same object the main
proofs build*. **Consequence:** the executable's canonical form should be validated by proving ①a+①b **directly
for the pruned output**, NOT "= the exponential lex-min". `canonForm`/`canonFormOf` (the lex-min) stay only for
the existing spine theorems; the executable defines its own poly form. This makes C-poly "the proven poly
algorithm's output", not a separate exponential artifact — but does **not** remove the wall (see below).

## Tiers (with abandon-points)

| Tier | Content | Blockers | State |
|---|---|---|---|
| **A** | **Computable descent** (find leaf, count cost) | `done` decidability (`Classical`→real `Decidable Discrete`) | ✅ **DONE** — `#eval` runs |
| **B** | Computable single-leaf **labelling** | `rankPerm` (`Equiv.ofBijective`) → compute `rankInv` by finite search; `leafLevel` (`Classical.choose`) → use the descent loop's returned level | next |
| **C-exp** | Computable canonical form by **enumeration** | `Fintype (DirAssignment)` (noncomputable) → enumerate order-labels; `canonForm` = `List.min` | optional; **exponential**, runs on tiny `n` only |
| **C-poly** | **Poly** canonical form (orbit-pruned; validated by ①a+①b directly) | orbit-pruning = the oracle/harvest, computable + correct | **⛔ the WALL — = the main open content; abandon-point** |

Tiers A+B are cheap, wall-free, independently valuable (a computable verified descent + labelling). C-exp gives an
honest end-to-end runnable reference (exponential). **C-poly ≈ implementing the whole verified poly algorithm** —
gated on the same oracle content the proofs chase; reached only after A+B, so nothing is wasted if abandoned.

## The cost-model coupling this surfaced (a genuine finding)

The cost model counts descent-nodes × warmRefine, **not** the canonical-output construction (the σ lex-min). A
*faithful* executable (cost matches what runs) forces accounting for the output — and doing that in poly is the
**same orbit-pruning core** as C-poly and the main proofs. So the executable track, the cost model's
output-accounting gap, and the poly proofs **converge on one core** — the project's "isolate the wall" pattern,
reached from the executable side. (Actionable: when the oracle summand of `w` lands, extend it to cover the
output construction, not just the descent.)

## Files
- `ChainDescent/ScratchExecutable.lean` — Tier A demo (`#eval` the descent). Grows into the executable's home.
- `ChainDescent/ScratchCostModelSpine.lean` — now carries `decidableDiscrete`/`decidableIsLeaf`; `spineCappedCanonizer` computable.
- `ChainDescent/ScratchCanonFormCapped.lean` — `descent`/`descentResult`/`descentCost` computable.

## NEXT
Tier B — computable `rankInv` (rank-permutation inverse by finite search) + a computable single-leaf `canonAdj`,
and drop the `Classical.choose` leaf extraction in favour of the descent loop's returned level. No wall.
