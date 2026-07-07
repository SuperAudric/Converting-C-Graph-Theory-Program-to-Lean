# Executable track — raising the Lean canonizer to runnable form

> **What this is.** The scope + build plan for making the Lean canonizer **executable** (option B), not just a
> proof model: "provably exists, and here it is (runs), C# for normal use." Lower value than the feasibility
> proofs, pursued now so the executable is a corollary of the proofs rather than a painful retrofit later. It
> may be **abandoned** if it hits an unresolvable wall — the abandon-points are marked.
>
> **Companion:** [`chain-descent-cost-model.md`](./chain-descent-cost-model.md) (the cost model this couples to),
> [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md).

---

## STATUS (read first, 2026-07-07)

**Where it stands:** the Lean canonizer's output **is computable, `#eval`-runs, and is ①a-sound (proven,
axiom-clean)** — the user confirmed concrete outputs on an unconstrained machine (K₃ → `[[0,0,1],[0,0,1],[1,1,0]]`,
path 0–1–2 → `[[0,1,1],[1,0,1],[1,1,0]]`). It is **NOT yet poly-time in practice**: n=3 takes ~10 min, and reifying
the descent did **not** fix that (see the OPEN ISSUE). It is also **not yet iso-invariant** (①b) — that is Tier C /
the wall. Everything below is WIP scratch, **NOT in `build.sh`**, all axiom-clean `[propext, Classical.choice, Quot.sound]`.

**What's built (files + key decls):**
- **Tier A — computable descent** (`ScratchExecutable.lean` + `decidableDiscrete`/`decidableIsLeaf` in
  `ScratchCostModelSpine.lean`): `descentResult`/`descentCost` `#eval` (`some 1`, `27`). Made `spineCappedCanonizer`
  computable (dropped `Classical` `done`).
- **Tier B — computable single-leaf labelling** (`ScratchExecutable.lean`): `rankInv` (total, `List.find?`, replaces
  noncomputable `Equiv.ofBijective`) + `canonAdjComp` + `canonAdjComp_eq` (= `labelledAdj (rankPerm) adj`) +
  `canonOutput` + `canonOutput_sound` (①a). FINDING: `#eval canonOutput` HANGS (colour blowup).
- **Renumbering** (`ScratchRenumber.lean`): `refineStepR = vertexRankNat ∘ refineStep` (bounded `<n`) + `refineStepR_iff`
  (same partition characterisation as `refineStep`) + `warmRefineR` + `samePartition_warmRefineR` +
  `discrete_warmRefineR`. **Plus the REIFIED** `refineRoundMat`/`warmRefineMat` (materialise each round to a `Vector`) +
  `refineRoundMat_eq`/`warmRefineMat_eq` (= `refineStepR`/`warmRefineR`, only evaluation differs) + `materialize`/`materialize_eq`.
- **Runnable outputs** (`ScratchRenumberExec.lean`): `canonOutputR` (via `warmRefineR`, reasoned) + `canonOutputMat`
  (via `warmRefineMat`, runnable) + `canonOutputMat_eq` + soundness (①a). `canonOutputMat` is what the user ran (~10 min, n=3).
- **Fully reified descent** (`ScratchRenumberFast.lean`): `defaultColouringMat` (descent colouring, each level =
  `warmRefineMat` + `materialize`) + `leafLevelMat` (bounded `List.find?` for first `Discrete` reified leaf) +
  `canonOutputFast` + `canonOutputFast_sound` (①a, self-contained — the search returns a decidably-`Discrete` leaf).

**★ Two findings that a fresh reader MUST internalise:**
1. **The blowup is unmemoised RECOMPUTATION, not (only) values.** `warmRefineR` hangs on `#eval` even for SMALL
   colours: `refineStepR χ = fun v => vertexRankNat (refineStep χ) v` recomputes `refineStep χ` per vertex, re-reading
   the lazy `χ` closure ⟹ exponential across rounds. Fix = **reify** (materialise each round). Renumbering (bounded
   values) is necessary but NOT sufficient.
2. **★ OPEN ISSUE — reifying the descent did NOT give the hoped speedup.** `canonOutputFast` (reified *descent*) still
   runs in ~the same order of time as `canonOutputMat` on the user's machine. (An earlier "~500× / 1.2s CPU" note was a
   MEASUREMENT ARTIFACT of this dev box's 2 GB-limited `lake env lean` thrash — the `#eval` never completed here, so the
   CPU counter caught only pre-thrash work; do NOT trust it.) **The real bottleneck is still unidentified.** Prime
   suspects for the next reader: (a) `leafLevelMat` recomputes `defaultColouringMat k` for each `k = 0..n`, and
   `defaultColouringMat` is itself prefix-recursive ⟹ O(n²) descent recomputations; (b) `materialize`'s `let vec :=
   Vector.ofFn χ; fun i => vec.get i` may not actually SHARE `vec` across calls under Lean's evaluator (if not, each
   lookup rebuilds the vector ⟹ no memoisation); (c) something still blows up in `descentResult`/`costedWarmRefine`
   (which uses the *non-reified* `warmRefine` for the cost). **Diagnose (b) first** — it's the crux of whether reification
   works at all. NB: this dev box cannot reliably `#eval`/measure these (2 GB thrash); profile on an unconstrained machine.

**Deferred: Tier C — the iso-invariant canonical form (①b).** All outputs above are the leaf's *single* labelling
(a valid relabelling), not the iso-invariant min. C-exp (exponential enumeration, tiny-n) or C-poly (orbit-pruned = the
oracle = the wall). See "Tiers" + "the wall" below.

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

## Renumbering — foundation LANDED (2026-07-07, `ScratchRenumber.lean`, axiom-clean)
The D7-option-ii primitive: `refineStepR adj P χ = vertexRankNat (refineStep adj P χ)` — one round, then compress
colours to their rank `0..n-1` (the C#'s `cells → 0..k-1`), breaking the cross-round encode blowup. Proven:
- `refineStepR_lt` — colours stay `< n` (the point: no compounding bit-size);
- `refineStepR_iff` — **same partition characterisation as `refineStep`** (same refined colour ⟺ same old colour ∧
  same signature), so the spine's proofs (which use only `refineStep_iff`) transfer;
- `samePartition_refineStepR` — one renumbered round is partition-equal to one plain round (the bridge seed).

`vertexRankNat` is order-preserving *and* injective-on-colours (`vertexRankNat_eq_iff`), so the compression is a
canonical renumbering. **Correction to the earlier worry:** no delicate "order-equivalence across rounds" invariant is
needed — `refineStepR` is validated by its own `refineStepR_iff` (partition-level), and the executable canonizer is
proven ①a directly (`canonAdjComp` is a relabelling for any discrete leaf), not by matching `refineStep`'s order.

## Renumbering — RUNNABLE output DONE via renumber + reify (the real blocker was recomputation, not values)

**The decisive finding (2026-07-07):** `warmRefineR` hangs on `#eval` even for SMALL colours — so the blowup was
never the *values*, it was **unmemoized recomputation**: `refineStepR χ = fun v => vertexRankNat (refineStep χ) v`
recomputes `refineStep χ` per vertex, each re-reading the lazy `χ` closure, exploding exponentially across rounds.
Renumbering (bounded values) is necessary but NOT sufficient; you also need **reification** — materialise each round
to a `Vector` (computed once, O(1) lookup).

`ScratchRenumber.lean` adds `refineRoundMat` (materialise `refineStep` → rank → materialise) + `warmRefineMat`
(`n` reified rounds), with **`refineRoundMat_eq` / `warmRefineMat_eq`** proving `warmRefineMat = warmRefineR` (only
evaluation differs), so every partition/soundness result transfers. `ScratchRenumberExec.lean` adds **`canonOutputMat`**
(the runnable output, `warmRefineMat`) + **`canonOutputMat_sound`** (①a, axiom-clean). It **`#eval`s to a real value** —
the user ran it on an unconstrained machine (K₃ → `[[0,0,1],[0,0,1],[1,1,0]]`, path → `[[0,1,1],[1,0,1],[1,1,0]]`),
in ~10 min for n=3.

**Takeaway:** a runnable canonizer needs the whole descent **reified**, not just renumbered — lazy `Colouring = Fin n
→ Nat` closures recompute exponentially.

**★ FULLY REIFIED DESCENT (2026-07-07, `ScratchRenumberFast.lean`) — built + ①a-sound, but did NOT fix the speed.**
`canonOutputMat` took ~10 min for n=3 because the *descent internals* (`descentResult` via `costedWarmRefine`,
`defaultColouring`) use the lazy blown-up `warmRefine`. `ScratchRenumberFast` reifies the whole descent:
`defaultColouringMat` (each level = `warmRefineMat` + `materialize`; `IndivStep.default` only doubles the colour, so
bounded `π` ⟹ bounded `χ'`), `leafLevelMat` (bounded `List.find?` for the first `Discrete` reified leaf),
`canonOutputFast` (emit `canonAdjComp` there). **`canonOutputFast_sound` = ①a, axiom-clean** — self-contained (the
search returns a *decidably `Discrete`* leaf, so no bridge to the original descent is needed). `materialize_eq` proves
materialisation is value-preserving. **BUT the user reports `canonOutputFast` still runs in ~the same order of time as
`canonOutputMat` — the descent reification did NOT resolve the slowness.** (A prior "~1.2s CPU / ~500× win" note was a
FALSE reading from this dev box's 2 GB thrash — disregard it.) See the OPEN ISSUE in STATUS for the suspect list; the
crux is whether `materialize` actually shares its `Vector` across lookups.

The partition bridge (used by both `canonOutputR` reasoning and `canonOutputMat`): `warmRefineR = (refineStepR)^[n]` +
**`samePartition_warmRefineR`** (same partition as `warmRefine`, via `samePartition_iterate` = the per-round bridge
chained with `refineStep_samePartition`) + `discrete_warmRefineR`. `canonOutputR` (via `warmRefineR`) + `canonOutputR_sound`
are the *reasoned* form; `canonOutputMat` (via `warmRefineMat`) + `canonOutputMat_sound` are the *runnable* form, equal by
`canonOutputMat_eq`. (A false lead along the way: the 7000-bit seed `ch.χι` looked like the cause, but the true blocker
was recomputation — reification fixes it with NO renumbered descent needed.)

## NEXT
Optional: **reify the descent internals** (`descentResult`/`defaultColouring` still use lazy `warmRefine`) so larger-n
graphs run — same `Vector`-materialisation pattern. Then Tier C (the iso-invariant canonical form): C-exp (exponential
enumeration, tiny-n) or C-poly (the wall = orbit-pruning = the oracle). Or pivot back to the main proofs
(oracle-summand → spine-`step` wiring, P1/P2 in Lean).
