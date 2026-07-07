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
`done`; everything else on the descent path was already computable). Validated by `#eval`
(`ScratchExecutable.lean`): `descentResult triangle = some 1`, `descentCost triangle = 27` (= 3³). The descent —
*find the leaf, count the cost* — executes.

**Tier B DONE (2026-07-07) — the single-leaf labelling is computable + proven.** All axiom-clean:
- `rankInv` — a **total, computable** inverse of `vertexRank` (`List.find?` over `Fin n`, `==`), replacing the
  noncomputable `Equiv.ofBijective` in `rankPerm`; `rankInv_spec` proves it inverts `vertexRank` on discrete χ.
- `canonAdjComp adj χ` — the leaf's canonical adjacency via `rankInv`; **`canonAdjComp_eq`** proves it equals the
  spec `labelledAdj (rankPerm χ h) adj`, so it is a genuine relabelling.
- `canonOutput` — wires it to the descent's returned leaf (**NO `Classical.choose`** — the leaf level is the loop's
  own output); `canonOutput_sound` = ①a on this runnable output.

**★ Tier B FINDING — the colour blowup makes `#eval canonOutput` INFEASIBLE (confirms D7 renumbering).** The
labelling is computable and proven, but `#eval`-ing it hangs: the leaf colouring's `Nat` values are
`Encodable.encode` iterated across refinement rounds (the cost-model §4 blowup), so `vertexRank`'s `<`/`==`
comparisons are over astronomically large `Nat`s. This is the D7 fork made concrete **from the executable side** —
a *practical* run needs the **renumbering `refineStep`** (cells → `0..k-1` each round). Renumbering is thus promoted
from "nice for a defensible bit-cost" to a **prerequisite for a runnable executable**. The theory is complete; the
runnable labelling demo is deferred behind renumbering.

**Still noncomputable / deferred: the lex-min `canonForm` (Tier C) + the practical run (needs renumbering).**

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
| **B** | Computable single-leaf **labelling** | `rankPerm` (`Equiv.ofBijective`) → `rankInv` by finite search; `leafLevel` (`Classical.choose`) → the loop's returned level | ✅ **DONE** — computable + proven; `#eval` needs renumbering (colour blowup) |
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
Two independent options: **(1) Renumbering `refineStep`** — the D7 variant (cells → `0..k-1` each round,
order-preserving ⟹ `canonAdjComp` unchanged). Now a *prerequisite* for any runnable `#eval` of the labelling
(Tier B finding), and it also sharpens the cost model's bit-cost bound. The one fiddly spot is proving the
order-equivalence invariant propagates through a refinement round (cost-model §4). **(2) Tier C-exp** — enumerate
`DirAssignment` order-labels + `List.min` for the lex-min (exponential, tiny-n only). Tier C-poly stays the wall.
Renumbering (1) is the higher-value next step: it unblocks the runnable demo *and* the honest bit-cost.
