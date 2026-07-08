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
the descent did **not** fix that — **but the cause is now RESOLVED (see finding #2): the bottleneck is the
`Encodable.encode` VALUE (exp-bit `Nat`), not recomputation; the fix is an encode-free structural round (= cost-model
D7 fork ii) + `@[csimp]` array-backing, DEFERRED to the Runtime-Phase `refineStep` choice (do NOT reify further).** It is
also **not yet iso-invariant** (①b) — that is Tier C / the wall. Everything below is WIP scratch, **NOT in `build.sh`**,
all axiom-clean `[propext, Classical.choice, Quot.sound]`.

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
2. **★ OPEN ISSUE — RESOLVED (2026-07-07): the bottleneck is a *value* (`Encodable.encode`), and the fix is
   `encode-free round + @[csimp]`, NOT reification and NOT `@[implemented_by]`.** Root cause (traced to
   [`WLGeneric.lean:92-93`](../GraphCanonizationProofs/ChainDescent/WLGeneric.lean#L92-L93)):
   `refineStep χ v = Encodable.encode (sigKey … v)` where `sigKey : List Nat` has length ~`n`. `Encodable.encode` on a
   `List Nat` is nested `Nat.pair` (Cantor pairing), which **squares magnitude per element ⟹ the returned `Nat` is
   exponential-bit in `n`**, and `vertexRankNat` compares those Nats by `<` every round. So the blowup lives *inside one
   round's return value*, produced fresh regardless of input bounds — which is exactly why reifying the descent moved
   nothing (the earlier suspects (a)/(b)/(c) were all wrong; at small `n` the residual 10 min is instead the Mathlib
   `Finset`/`Multiset`-`Quotient` interpreter constants, which the same fix removes).
   **Resolution — the tooling, tested (core-only spike, re-derivable in ~15 lines):** `@[implemented_by]` and `@[csimp]`
   are both honored by `#eval` and both add **zero axioms** (`#print axioms` unaffected — off the firewall surface,
   unlike `native_decide`). To re-verify: attach `@[implemented_by fastWrong] def slow …` with `fastWrong` returning a
   *different* value ⟹ `#eval slow` shows the fast value (honored) and `#print axioms slow` = none; and
   `@[csimp] slow_eq : slow = fast` (proof required) swaps execution with `#print axioms slow_eq = [propext, Quot.sound]`. **Decision: use `@[csimp]` (sound — requires a proof `slow = fast`); AVOID `@[implemented_by]`**
   (trusted, can assert an *arbitrary/false* equation — a firewall risk; a non-faithful `refineStep` impl would make
   `#eval` lie). **The critical catch:** `@[csimp]`/`@[implemented_by]` can only substitute an *equal* function, and
   `refineStep`'s output Nat is load-bearing — so the `Encodable.encode` blowup is **not a swap target**; it must be
   *removed from the definition*. **Two-layer fix:** (1) **encode-free round** (definitional, no trust) — rank vertices to
   `0..n-1` by comparing `(χ v, sorted-signature)` keys **structurally** (lex on `List Nat`), never encoding. Same
   partition as today, different canonical *order* ⟹ a **valid but distinct canonizer**: ①a transfers for free
   (`canonAdjComp` is a relabelling for any discrete leaf, label-agnostic), ①b needs only that lex-on-signatures is
   iso-canonical (it is). **This IS the cost-model D7 fork option (ii)** — `refineStepR_iff` (same-partition
   characterisation) already done; the missing piece is ranking by structural comparison instead of by re-encoding.
   (2) **`@[csimp]` array-backing** `signature`/`Multiset.sort`/`vertexRankNat` (value-preserving ⟹ sound) to kill the
   `Finset` constants — pure polish.
   **Best development point (decided):** fold layer (1) into the **D7 (ii) renumbering build** when the Runtime Phase
   pins `canonForm?`'s `refineStep` (on the headline path anyway); do layer (2) `@[csimp]` polish LAST, in the
   Publication phase, once `canonForm?` is frozen. Building a fast `refineStep` NOW is throwaway (the renumber fork
   replaces it). NB: this dev box cannot reliably `#eval`/measure the heavy path (2 GB thrash); the *mechanism* was
   validated core-only; profile the full canonizer on an unconstrained machine.

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
The fast-executable path is now **scoped and deferred** (see finding #2, RESOLVED): the speedup is `encode-free round`
(= D7 fork (ii), fold into the Runtime-Phase `refineStep` choice) + `@[csimp]` array-backing (Publication-phase polish).
Do **not** reify further — reification was the wrong lever (the blocker is the `Encodable.encode` *value*, not
recomputation). Tier C (the iso-invariant canonical form) remains the wall (C-poly = orbit-pruning = the oracle).
**Active work pivoted back to the main proofs** (the headline path): **wire the oracle summand of `w` into the
spine-`step`'s true cost** so the flag fires on the real descent, then P1/P2 in Lean + confinement assembly ⟹ ①.
