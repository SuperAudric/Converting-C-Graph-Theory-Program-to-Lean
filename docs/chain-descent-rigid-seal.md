# Chain descent — the rigid seal (Algorithm R): the complete working doc

> **What this doc is.** The self-contained working home for the **rigid seal** — Algorithm R, the force/rigid side
> of the mixed canonizer. It covers *everything the rigid work must now do* (canonize a rigid residue or honestly
> flag, iso-invariantly) and *everything needed to do it* (the handoff it receives from consume, the solver it must
> build/certify, the seal theorem it targets, the wall it reduces to). This is the doc to work from when building
> the rigid side — the mirror of [`chain-descent-deepen-supply.md`](./chain-descent-deepen-supply.md) (the consume
> side). (The consume→rigid handoff, once a standalone note, is now §3 here.)
>
> **Division of labour with the existing docs.** The rigid *solver algorithm* (C#, complete) is designed in
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11.11–§11.14 — this doc
> **summarises** it (§6) and points there for the exhaustive B1–B6 detail. The two-seals endgame frame is
> [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md) §1a/§3. The no-rigid-Cameron tightening is
> [`chain-descent-cameron-entanglement.md`](./chain-descent-cameron-entanglement.md). This doc owns the **Lean
> build** of the rigid seal and its integration.

---

## ▶ STATUS (2026-07-23)

> **The C# rigid solver is COMPLETE; the Lean rigid seal is nearly empty; the consume side now feeds it a clean
> per-node handoff object, AND discharging its own `Amenable` hypothesis is a rigid-side deliverable (§9.1).**
> This is the next track to build. First concrete steps (all wall-free / design-level): resolve the mixed-cell
> design question (§8.1), then R0a (§8.1); the heavy P3 Smith build waits until the design settles.
>
> - **C# — DONE.** Algorithm R is built, wired (`EnableRigidSolver` default-ON), and validated: `Option2Solver.cs`
>   (recover → solve → emit → verify, ring-general, **B1–B6 all landed, 50 tests**; `ir-blindspot-solver` STATUS +
>   §11.12). It solves CFI / multipede / `Z_{2^k}` / general-arity / `s`-fold covers. This is the **reference spec**
>   the Lean must certify — not a lift (there is no Smith-normal-form in Lean yet).
> - **Lean — NEARLY EMPTY.** What exists: the typed contract `Phase2.Solver`/`Sound`/`IsoInvariant`
>   (`Phase2Handoff.lean:74,78,85`) + `handoffBase_relabel`; the force resolver `lookaheadKey` +
>   `keyEquivariant_lookahead` (`Force.lean:564,592`, PROVED); the consume-handoff lemmas (§5). **No Lean
>   rigid-solver, no Smith/ring solve, no force-separation theorem, no P1–P4.** ⚠ The `RRU` namespace in
>   `Phase2Handoff.lean` (the *sequential* R(G) handoff) is **RETIRED** for the interleaved model (`endgame §1a`) —
>   do not build on it; the surviving seam is `Phase2.Solver`/`Sound`/`IsoInvariant`.
> - **The handoff (NEW, from consume).** Consume (`deepenSupply`) now provably exposes, per node, a concrete
>   `RigidObstructionAt` — a same-colour non-automorphic pair the rigid side must distinguish
>   (`not_amenablePath_imp_rigidObstruction`, axiom-clean). This is the *interleaved* handoff object, replacing the
>   retired whole-residue R(G).
> - **The build ahead (this doc §9):** the seam bridge (R0a discretizing / R0b wall) + the Algorithm-R Lean roadmap
>   (P1 extraction → P2 forcing-bridge → P3 solve+iso → P4 capstone `canonizesRigidResidue_or_flags`) + per-family
>   coverage + the no-rigid-Cameron tightening. Everything reduces to the single shared wall `hSmallAutThin`.

---

## 1. The target — the rigid seal theorem

The deliverable is the Phase-2 mirror of the symmetry seal `reachesRigidOrCameron`:

> **`canonizesRigidResidue_or_flags`** — for a rigid residue, *canonize it (linear-over-a-ring) or honestly flag
> (non-linear)*, with the open content isolated into **one** hypothesis. Iso-invariant answer AND flag.

| seal | handles | the escape | wall |
|---|---|---|---|
| symmetry seal `reachesRigidOrCameron_viaBoundedMinMult` | symmetry consumption | "or Cameron" | `hSmallAutThin` |
| **rigid seal** (this) `canonizesRigidResidue_or_flags` | linear-over-ring (CFI/multipede/`Z_{2^k}`) | "or non-linear" | **= `hSmallAutThin`** |

By the node-4 unification (`IR §11.11`) the two flag floors are the **same object**; §11.14 argues the rigid
escape is *strictly tighter* (no "or Cameron"). Combined, the two seals isolate **one** wall — the endgame's
"two seals, one wall."

**The correctness contract it witnesses** (`Phase2Handoff.lean`, the surviving seam):
- `Solver n := AdjMatrix n → Option (Fin n → Fin n → Nat)` (:74) — a canonical labelled adjacency, or an honest flag.
- `Sound sol := ∀ adj c, sol adj = some c → ∃ π, c = labelledAdj π adj` (:78) — ①a specialised to the rigid residue.
- `IsoInvariant sol := ∀ σ adj, sol (relabelAdj σ adj) = sol adj` (:85) — ①b/①c specialised.

Algorithm R is the future witness of `Sound ∧ IsoInvariant`; `canonizesRigidResidue_or_flags` is that witness plus
the `∨ flag` disjunct whose residual is `hSmallAutThin`.

---

## 2. The frame — two seals, one wall, INTERLEAVED (`endgame §1a`)

Two algorithms, interleaved (not sequential):
- **Algorithm A — symmetry consumption** (cascade / linear / **deepen**). Merges a branch pair via a *verified
  automorphism*. `deepenSupply` is a consume supply in this family.
- **Algorithm R — the rigid solver** (F₂/ring → Smith). Recovers the rigid residue's linear system, solves,
  de-fuses hidden abelian symmetry (its kernel is a symmetry detector), and **flags the non-linear residue**.

They interleave to a **mutual stall** = the flag = the shared wall. Consumption is **verify-gated**: a rigid
residue has no automorphism, so it presents to Algorithm A as a **stall, never a harvestable orbit** — this is
exactly the `RigidObstructionAt` handoff (§5). **The sequential "Phase 1 → whole R(G) → Phase 2" handoff is
retired** (it needed "completeness of deferral ⟺ no fusion", an open question with no fusion-mildness theorem);
the live model interleaves per relation, and the flag fires exactly at mutual stall.

---

## 3. What the rigid side receives — the handoff (the interleaved object)

**The per-node handoff object (NEW, from the consume work — all axiom-clean, `DeepenAmenable.lean`):**
- **`RigidObstructionAt adj χc cid`** (:200) := `∃ u w, χc u = cid ∧ χc w = cid ∧ ∀ σ, IsColAut adj χc σ → σ u ≠ w`
  — a concrete same-colour non-automorphic pair.
- `rigidObstruction_of_not_cellSingleOrbit` (:206) — an `Amenable`-violation *is* one (de Morgan).
- `rigidObstruction_imp_not_cellIsOrbit` (:957) — consume can NEVER connect a rigid pair (deepen gens are
  `IsColAut`). **Deepen defers soundly; it hands off, never mishandles.**
- `not_amenablePath_imp_rigidObstruction` (:972) — a consume-stall ALWAYS surfaces one (possibly *deeper* than the
  compared pair, which under fusion is itself automorphic).

The interleaving loop:
```
consume stalls  →  exposed RigidObstructionAt (concrete non-automorphic pair)
                →  [RIGID SIDE]  distinguish it (force key / linear solve)
                →  refine re-exposes symmetry  →  consume retries  →  … → mutual-stall flag
```

**The rigid residue's three regimes** (`IR §1`), for scoping the solver:
1. **cascade / already-discretizing** — 1-WL discretizes at the base → canonize for free (§9 R0a; **no wall**).
2. **IR-blind-spot / multipede** — rigid but 1-WL does not discretize at bounded depth → *the target* (Algorithm R).
3. **hidden Johnson / Cameron** — unconsumed non-abelian symmetry; *not* rigid, Algorithm A's job, out of scope.

---

## 4. The obligation, precisely — the two levels the rigid side must meet

**Level 1 — the totality obligation (`CellResolved`, `Cost.lean:156`).**
```
CellResolved key S adj χ := CellIsOrbit S adj χ ∨ (∀ u w ∈ branches χ, keyV key adj χ u = keyV key adj χ w → u = w)
```
The rigid side owns the **second disjunct** (force separates the cell). On a rigid cell the first disjunct is dead
(`rigidObstruction_imp_not_cellIsOrbit`), so `CellResolved` reduces to **force distinguishing the exposed
non-automorphic pair**. ⚠ **This is NOWHERE proved in Lean** — force separation is an *assumed* `hsep` hypothesis
throughout (`Force.lean:409` `forceBy_singleton_of_separating`), named as the open obligation
(`Composite.lean:238`, `DeepenAmenable.lean:947`). `Handled` (`Residue.lean:162`) quantifies `CellResolved` over
the reachable non-discrete colourings; every current discharge goes through the *consume* branch, never force.

**Level 2 — the solver-correctness obligation (`Phase2.Solver`, §1).** `Sound ∧ IsoInvariant`, and canonize-or-flag
with the flag residual = the wall. This is the full rigid canonizer (Algorithm R), of which Level-1 force-separation
is the "distinguish one pair" atom.

**The seam predicate this doc owns** (thin, deepen-facing):
```
def RigidResolved (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ, (∀ σ, IsColAut adj χ σ → σ u ≠ w) → keyV key adj χ u ≠ keyV key adj χ w
```
*"Force distinguishes every non-automorphic branch pair."* Everything in §9 either proves it (R0a, R2) or reduces
it to `hSmallAutThin` (R0b/R4).

---

## 5. The classification — which obstructions are provable vs. the wall (`IR §11.11/§11.14`)

| | abelian / linear | non-abelian / non-linear |
|---|---|---|
| **symmetry** | hidden gauge → Phase-1 linear oracle | Johnson/Cameron → cascade, **or excluded by rigidity** |
| **structure (rigid)** | multipede / `Z_{2^k}` → **Algorithm R ✓ (C#-built)** | **THE WALL** — non-schurian, open, **no witness** |

The rigid medium kills the whole **symmetry row** (hiding is abelian ⟹ linear-oracle's job; non-abelian ⟹ not
hideable ⟹ visible ⟹ excluded by rigidity). Algorithm R owns **structure/linear**. The only remainder is
**structure/non-linear** = the wall. Three completeness claims (keep separate):
1. *"F₂ is the only obstruction"* — **FALSE** (Lichter's CFI-over-`Z_{2^k}`).
2. *"every rigid obstruction is linear over some abelian ring"* — **CONJECTURE** (claim #2; F₂ ⊊ `Z_{2^k}` ⊊ rings).
3. *"some rigid obstruction is non-linear"* — **OPEN, no constructible witness** (0-falsifier record).

**The wall `hSmallAutThin`** — not a Lean def; it is the carried hypothesis inside
`reachesRigidOrCameron_viaBoundedMinMult` (`CascadeAffine.lean:1320`), typed
`¬IsLargeSchemeViaAut IsLarge n S → BoundedMinMult B M`. `RigidResolved` (force-completeness on rigid cells)
reduces to exactly this. Cameron-entanglement tightens the rigid flag floor to "or non-linear" (no Cameron carry).

---

## 6. What Algorithm R IS — the solver to certify (summary; detail `IR §11.12`)

The **C# reference** (`Option2Solver.cs`, complete) — what the Lean must mirror:

- **The engine** — a **stepwise alternating fixpoint** `… ∘ phase2 ∘ phase1 …`: per pairwise relation, the oracle
  **consumes** it (verified automorphism), else the Gaussian/Smith solve **forces** it (in the current row-space),
  else **defers**. A nontrivial kernel-module of the recovered system `H` is a hidden abelian symmetry fused behind
  a real decision — verify, consume, refine, loop (de-fusion). `Z_{2^k}` is *inside* the engine (an F₂ tower peeled
  by individualization; Lichter's FPC+rank bound cannot individualize, so it doesn't bind).
- **`Recover`** (B1a) — structural (recognition-free): find segments (bipartition + average-degree side), infer the
  ring `A` (degree-3 Latin-square order-profile; general arity by pinning `d−3` segments), build incidence `M`.
- **`SolveOverA` / Smith** (B1b/d) — `RecoverRing` → invariant factors; extended Smith `U·M·V = D` (poly,
  `BigInteger`); `SolveOverA` (`Mx = target`, poly); `KernelSizeOverA`. Pin an **affine frame** on the lowest-cell
  segment (`r+1` states → generators of `A`), linear-solve every other segment over `A` — closes the cyclic
  constraint graph unit-propagation stalls on (`m ≥ 8`), poly for bounded rank.
- **Emit + verify-by-reconstruction** (B1c/B3) — `TryCanonicalOrder`: search a gauge `φ` making every gadget sum to
  0; **success = canonical form, failure = flag** (verify unified with emit) ⟹ the succeed/flag verdict is
  iso-invariant.
- **The fold** (B4) — canonizes a clean `s`-fold cover (fibers = same-cell-neighbour components; copies = the rest),
  detected structurally at the iso-invariant root; poly for unbounded `s` on fully-symmetric covers.
- **Wiring** (B2) — fires at the **root (`depth == 0`)** on "is the root residue a clean multipede" (iso-invariant),
  NOT at `target == -1` (labelling-dependent → breaks iso-invariance).

⚠ **Bounded open C# items** (off the critical path): distinguishable fold covers `s > 6`, harvesting the fold `Aut`,
the deferred B1d solve-speed perf. The rigid-solver track is **complete for handoff**.

---

## 7. The Lean gap — what is NOT built

- **No rigid-solver object.** "Algorithm R" / "linear oracle" are C#/prose only; the Phase-1 linear oracle is
  `LinearOracle.configSwap_of_aut/twin` inside CFI, not a general solver.
- **No Smith normal form / ring solve** anywhere in Lean.
- **No force-separation theorem** — the whole `RigidResolved` / `CellResolved` force branch (§4) is open, an assumed
  `hsep`.
- **No `canonizesRigidResidue_or_flags`** — the capstone does not exist.
- **`hSmallAutThin` is a hypothesis, not a lemma** (`CascadeAffine.lean:1320`).
- The surviving Lean seam is only the **contract** (`Phase2.Solver`/`Sound`/`IsoInvariant` + `handoffBase_relabel`);
  the `RRU` reachability apparatus is retired.

---

## 8. The plan — the full Lean build

### 8.1 The seam bridge (from consume) — the new content

- **R0a — the discretizing case (PROVABLE, no wall; do first).** When `lookData adj χ u` discretizes, `lookaheadKey u`
  returns `leafMatrix` = the canonical form pinning `u` (`Force.lean:564`). Two branch vertices have equal `keyV` iff
  their pinned canonical forms match iff `(adj,u) ≅ (adj,w)` iff **same orbit**. So on the discretizing regime `keyV`
  separates *exactly* the non-automorphic pairs — `RigidResolved` holds. Content: the **leaf-matrix complete-invariant**
  lemma (discrete refinement distinguishes non-isomorphic pointed graphs), the force analog of
  `handled_of_root_discrete` (`Residue.lean:176`). Regime (1) of §3; the clean core.
- **⚠ The mixed-cell / fusion design question (load-bearing — resolve before the capstone).** `CellResolved` is
  *single-step*: whole-cell consume OR whole-cell force. A **mixed cell** (some same-orbit pairs, some rigid pairs)
  satisfies *neither* in one step — consume can't connect the rigid pair; force merges the same-orbit pair (even in
  the discretizing case). Resolution is the **interleaving**: force separates the rigid pairs (splitting the cell → a
  new `Reaches` node), consume then fires on the same-orbit sub-cells. So mixed cells resolve over
  `Handled`-`Reaches`, not at the mixed node. **Open: does `CellResolved` need a "force partially separates, then
  recurse" refinement, or does the `Reaches`-iteration already carry it?** This is the Lean form of the fusion
  resolution `endgame §1a` cites for retiring the sequential handoff.
- **R0b — the bridge, carrying the wall.** `RigidResolved ⟸ hSmallAutThin` per node: on the non-discretizing regime,
  force-separation of the exposed pair = force-completeness on the rigid cell = `hSmallAutThin`. Land the reduction,
  carry `hSmallAutThin` — the honest `modulo {hSmallAutThin}` end-state.

### 8.2 Algorithm R Lean (P1–P4 — `endgame §3`, `IR §11.12`; do-not-rescope)

- **P1 — extraction-soundness (do first; standalone / Mathlib-direct).** Minimal forcing-circuits generate
  `rowspace(H)` — pure F₂/matroid, no graph model. The soundness of the linear-system recovery.
- **P2 — forcing-model bridge (carried, discharge later).** "1-WL forcing over `A` = ring-unit propagation" as a
  model hypothesis linking the graph to the recovered system.
- **P3 — solve + canonical-form iso-invariance (the heavy new build).** Smith over the ring → canonical coset;
  the emit's iso-invariance (verify-by-reconstruction lifted to Lean). This is `Phase2.IsoInvariant` for the solver.
- **P4 — the capstone `canonizesRigidResidue_or_flags`.** Assembles P1–P3 into the rigid seal, isolating the
  `LinearObstruction` hypothesis = the wall. **No new citations** (unlike G3 on the symmetric side).

### 8.3 Per-family coverage (R2 — PROVABLE, imports) and tightening (R5)

- **R2.** CFI: `theorem_1_HOR_cfi_oddDeg` (`CFI.lean:3179`, axiom-free) gives orbit-recovery = warm-refined colouring
  at bounded depth for odd-degree CFI; `cfiFlipAut` (:3722) + `isAut_cfiFlipAut` (:3740) build the `Z₂^β` gauge autos.
  These discharge `RigidResolved` for CFI by import. `Z_{2^k}` / multipede (`MultipedeWitness.lean`) are build targets
  (no `Z_{2^k}` theorem yet). Each family landed shrinks what R0b/P4 carries.
- **R5.** No-rigid-Cameron (`cameron-entanglement`): rigid medium admits no hidden Johnson/Cameron ⟹ the rigid flag
  floor is "or non-linear" with no Cameron carry.

### 8.4 Ordering + dependencies

`R0a` (clean, immediate) → resolve the **mixed-cell design question** (gates the capstone shape) → `P1` (extraction,
standalone, parallel to R0a) → `R0b` (bridge, carry `hSmallAutThin`) → `P2`/`P3` (solve + iso, the heavy build) →
`P4` (capstone). `R2` (per-family) and `R5` (tighten) run in parallel as residue-shrinkers. The C# is the reference
throughout (validate Lean claims against `Option2Solver` behaviour before proving).

---

## 9. Integration — how the rigid seal closes ③ / totality

The rigid seal is one of the two inputs to `UnhandledResidue` (`endgame §4.1`). Combined with the symmetry seal it
collapses the residue toward **one named atom** = the shared wall. In the canonizer's terms: `Handled key S adj`
(`Residue.lean:162`) holds at every reachable node because each is either consume-resolved (`CellIsOrbit`) or
rigid-resolved (the force branch, via `RigidResolved`), with the interleaving handling mixed cells. The rigid seal
supplies the force-branch discharge, conditional on `hSmallAutThin`. State the goal as the **conditional**
("canonized or unhandled rigid residue"), not "rigid GI ∈ P" — the conditional is exactly what ③ formalises and is
robust to a non-empty residual (`endgame §3` design note).

**⚠ Non-vacuity note (③).** `Residue.residue_nonvacuous` is proven for the real `Residue := ¬Handled` object; but
`Publication.UnhandledResidue` is still three `opaque` atoms with a `sorry` non-vacuity. The ③ Publication-swap
(opaque atoms → the real `¬Handled` residue) is **deliberately deferred** until this doc's build determines the
rigid residue's final shape — the atoms should not be pinned before the rigid seal fixes what the rigid-obstruction
atom actually is. When R0a/R0b/P4 land, the swap becomes mechanical and non-vacuity follows.

### 9.1 The `Amenable` coupling — this is ALSO how consume's ①c closes

The rigid seal is not merely a parallel second seal; it is **what discharges the consume side's last domain
hypothesis.** `deepenSupply`'s ①c is closed modulo **`{Amenable}` alone** (`deepenSupply_guarded_canonizer_direct`,
`DeepenAmenable.lean`; the track-A whole-graph-discretize redesign made `[DISC]`/gate/termination structural and
**eliminated `AnchorFires`** — 2026-07-23, axiom-clean), and an **`Amenable`-violation is exactly a `RigidObstructionAt`**
(`rigidObstruction_of_not_cellSingleOrbit`) — a same-colour non-automorphic pair, i.e. the rigid side's job. So
"discharge `Amenable` on family `F`" is not a separate obligation from the rigid work; it **is** the statement that
the interleaving delivers Schurian (pure-symmetry) cells to consume, with the rigid pairs peeled by force first.
Concretely, per family this is a **totality/scheduling** obligation (not a new conjecture): show that every cell
deepen visits on `F` is either a single Stab-orbit (Schurian → consume fires, `Amenable` holds) or carries a
`RigidObstructionAt` that force separates first (→ refine → re-expose → the now-Schurian sub-cell is `Amenable`).
Both branches route through the same shared wall `hSmallAutThin`. **Framing consequence:** every family the rigid
seal handles (R2: CFI, `Z_{2^k}`, multipede) simultaneously discharges deepen's `Amenable` on that family — track
the two together, not as separate legs.

---

## 10. Gap ledger

| Item | Statement | Status |
|---|---|---|
| **handoff** | `RigidObstructionAt` exposed per consume-stall; deepen defers soundly | **PROVED** (`not_amenablePath_imp_rigidObstruction`, `rigidObstruction_imp_not_cellIsOrbit`) |
| **contract** | `Phase2.Solver`/`Sound`/`IsoInvariant` | **stated** (`Phase2Handoff.lean`); Algorithm R is the future witness |
| **R0a** | discretizing → `keyV` separates non-aut pairs (`RigidResolved`) | **PROVABLE, no wall** — leaf-matrix complete-invariant lemma; not built |
| **mixed-cell** | fusion cell resolved by force-split + `Reaches`-iteration | **DESIGN QUESTION** — does `CellResolved` need refining? |
| **R0b** | `RigidResolved ⟸ hSmallAutThin` (bridge) | **not built** — reduction to the shared wall |
| **P1** | minimal forcing-circuits generate `rowspace(H)` | **not built** — F₂/matroid, standalone, do first |
| **P2** | forcing-model bridge (1-WL forcing = ring propagation) | **carried** — model hypothesis |
| **P3** | solve (Smith/ring) + canonical-form iso-invariance | **not built** — the heavy build |
| **P4** | `canonizesRigidResidue_or_flags` | **not built** — the capstone; isolates `LinearObstruction` = wall |
| **R2** | per-family: CFI, `Z_{2^k}`, multipede | CFI **axiom-free** (`theorem_1_HOR_cfi_oddDeg`); `Z_{2^k}`/multipede **build targets** |
| **the wall** | `hSmallAutThin` (rigid-GI∈P) | the **shared wall** — carry-only |
| **R5** | no rigid Cameron ⟹ "or non-linear" only | `cameron-entanglement` — conjecture, empirically solid |
| **C#** | `Option2Solver` B1–B6 | **COMPLETE** (50 tests) — the reference spec |

Everything conjectural lives in **`hSmallAutThin`** (shared). The seam's *own* new content is **R0a** + **R0b** + the
**mixed-cell design question**; the solver's is **P1–P4**; the rest is per-family imports and the C# reference.

---

## 11. Traps and pointers

- ⚠ **"Force separates non-automorphic pairs" is NOT proved** — assumed `hsep` everywhere (`Force.lean:409`,
  `Composite.lean:238`). R0a proves it only on the discretizing regime.
- ⚠ **`hSmallAutThin` / "Algorithm R" / "linear oracle" are hypotheses / C# / prose — not built Lean objects.**
- ⚠ **`CellResolved` is single-step** — it does not model the interleaving; mixed/fusion cells need the
  `Reaches`-iteration (or a refined predicate). The load-bearing design question (§8.1).
- ⚠ **The `RRU` sequential handoff is RETIRED** (`Phase2Handoff.lean` RRU namespace; `endgame §1a`). The live handoff
  is the interleaved per-node `RigidObstructionAt`. The surviving seam is `Phase2.Solver`/`Sound`/`IsoInvariant`.
- ⚠ **Do not re-scope the C# roadmap** — B1–B6 are landed (`IR §11.12`); the work is the Lean P1–P4 + the seam bridge.
- **Pointers.** Consume side: `chain-descent-deepen-supply.md`. Solver design + C# B1–B6: `ir-blindspot-solver`
  §11.11–§11.14. Two-seals frame + P1–P4 roadmap: `endgame-spec` §1a/§3. No-rigid-Cameron: `cameron-entanglement`.
  Seal capstone: `reachesRigidOrCameron_viaBoundedMinMult` (`CascadeAffine.lean:1314`). Typed seam:
  `Phase2Handoff.lean`. CFI: `CFI.lean:3179,3722`. Ring design: `IR §11.13/§11.13a`.
