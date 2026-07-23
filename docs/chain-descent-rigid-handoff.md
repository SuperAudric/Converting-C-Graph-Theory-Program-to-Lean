# Chain descent — the rigid handoff (Algorithm R: discharging the consume-exposed residue)

> **What this doc is.** The self-contained home for the **consume→rigid seam**: the rigid side (Algorithm R)
> receiving the concrete `RigidObstructionAt` that the consume side (`deepenSupply`) now *provably exposes*, and
> discharging it toward the one shared wall. It is the mirror-facing companion to
> [`chain-descent-deepen-supply.md`](./chain-descent-deepen-supply.md) (the consume side).
>
> **What this doc is NOT.** A re-scope of Algorithm R's *design* — that lives in
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §11.11–§11.14 (the solver,
> C#-complete) and [`chain-descent-endgame-spec.md`](./chain-descent-endgame-spec.md) §1a/§3 (the two-seals frame
> + the P1–P4 Lean roadmap). This doc owns the **Lean seam**: turning consume's exposed obstruction into a rigid
> obligation, and reducing that obligation to `hSmallAutThin` (the shared wall) — nothing more.
>
> **Pointers.** Consume side: deepen doc. Solver design: `ir-blindspot-solver` §11. Two-seals frame + roadmap:
> `endgame-spec` §1a/§3. No-rigid-Cameron tightening: `chain-descent-cameron-entanglement.md`. The wall/seal:
> `reachesRigidOrCameron_viaBoundedMinMult`. The typed seam: `ChainDescent/Phase2Handoff.lean`.

---

## ▶ STATUS (2026-07-22)

> **The consume side is done to its boundary; the rigid Lean side is nearly empty.** Consume's `①c` closes
> reference-free modulo `{Amenable, AnchorFires}` (deepen doc), and consume now hands the rigid side a **first-class
> Lean object**: a concrete same-colour non-automorphic pair (`RigidObstructionAt`), provably surfaced on every
> consume-stall (`not_amenablePath_imp_rigidObstruction`, axiom-clean). The rigid side must **distinguish** it.
>
> - **What EXISTS on the rigid side (Lean):** essentially the target predicate and the sound-deferral half only.
>   `RigidObstructionAt` (`DeepenAmenable.lean:200`); `rigidObstruction_of_not_cellSingleOrbit` (:206),
>   `rigidObstruction_imp_not_cellIsOrbit` (:957), `not_amenablePath_imp_rigidObstruction` (:972) — all PROVED,
>   all the "consume defers correctly" side. The force resolver `lookaheadKey` + `keyEquivariant_lookahead`
>   (`Force.lean:564,592`, PROVED). **NO Lean rigid-solver object exists** ("Algorithm R" / "linear oracle" are
>   C#/prose only). **NO theorem separates non-automorphic pairs** — force separation is an *assumed* `hsep`
>   hypothesis everywhere (`Force.lean:409`), named as the open obligation at `Composite.lean:238` and
>   `DeepenAmenable.lean:947`.
> - **What EXISTS on the rigid side (C#):** Algorithm R is **complete and validated** — `Option2Solver.cs`
>   (recover→solve→emit→verify, ring-general, 50 tests; `ir-blindspot-solver` STATUS). The Lean side is the gap.
> - **The gap this doc targets:** the **bridge** `RigidObstructionAt → force separates it` — provable for the
>   discretizing case (**R0a**, no wall) and per-family (CFI/seal imports, **R2**), and reducing to `hSmallAutThin`
>   for the general non-linear case (**R0b/R4**). Plus the mixed-cell/fusion subtlety at `CellResolved` (§7).

---

## 1. The frame — two seals, one wall (grounding, `endgame-spec §1a`)

The canonizer has two domains, each with its own seal, **interleaved** (not sequential):

- **Algorithm A — symmetry consumption** (the oracle side; cascade/linear/**deepen**). Merges a branch pair via a
  *verified automorphism*. `deepenSupply` is a consume supply in this family (the base-symmetry constructor).
- **Algorithm R — the rigid solver** (the force side; F₂/ring → Smith). Recovers the linear constraint system of
  the rigid residue, solves it, de-fuses hidden abelian symmetry, and **flags the non-linear residue**.

They interleave to a **mutual stall** = the flag = the shared wall. Consumption is **verify-gated**: a rigid
residue has no automorphism, so it presents to Algorithm A as a **stall, never a harvestable orbit** — which is
exactly the `RigidObstructionAt` handoff below. The two seals **isolate the same single wall** (`hSmallAutThin`);
`UnhandledResidue` collapses toward one named residue.

**What Algorithm R receives** (`ir-blindspot-solver §1`): the rigid residue, orbit-annotated, in three regimes —
(1) **cascade / already-discretizing** (1-WL discretizes at the base → canonize for free; **R0a**); (2)
**IR-blind-spot / multipede** (rigid but 1-WL does not discretize at bounded depth → *the target*); (3) **hidden
Johnson / Cameron** (unconsumed non-abelian symmetry — *not* rigid, Algorithm A's job, out of scope here).

---

## 2. The handoff object — what consume hands the rigid side

Consume's boundary is now a clean Lean object, not prose. The relevant landed lemmas (all axiom-clean,
`DeepenAmenable.lean`):

- **`RigidObstructionAt adj χc cid`** (:200) := `∃ u w, χc u = cid ∧ χc w = cid ∧ ∀ σ, IsColAut adj χc σ → σ u ≠ w`.
  A concrete same-colour non-automorphic pair.
- **`rigidObstruction_of_not_cellSingleOrbit`** (:206) — a `CellSingleOrbit` failure *is* a `RigidObstructionAt`
  (de Morgan). So an `Amenable`-violation localises to one.
- **`rigidObstruction_imp_not_cellIsOrbit`** (:957) — a rigid pair can NEVER be consume-connected (deepen gens are
  `IsColAut`, so `WordReach` would furnish the ruled-out automorphism). **Deepen defers soundly; never mishandles.**
- **`not_amenablePath_imp_rigidObstruction`** (:972) — `¬AmenablePath → ∃ RigidObstructionAt`. **A consume-stall
  ALWAYS surfaces a concrete rigid node** (possibly *deeper* than the compared pair, which under fusion is itself
  automorphic — see the deepen doc §7).

**The interleaving loop (the handoff in motion):**

```
consume stalls  →  not_amenablePath_imp_rigidObstruction: exposed RigidObstructionAt (concrete pair)
                →  [RIGID SIDE] force / Algorithm R distinguishes that non-automorphic pair
                →  refinement re-exposes symmetry  →  consume retries on the now-Amenable residue  →  … → fixpoint
```

So the rigid side's input is precise: **a concrete `RigidObstructionAt` — a same-colour pair `(u,w)` with no
colour-automorphism `u ↦ w`. Its job: distinguish `(u,w)`** (give them different keys / resolve them in the linear
system). This is the *same* 1-WL-merged non-automorphic pair the rigid solver / §11.14 classification already own —
**no new obstruction type** (`rigidObstruction_imp_not_cellIsOrbit`'s docstring).

---

## 3. What Algorithm R is (brief — detail in `ir-blindspot-solver` §11)

The **stepwise alternating fixpoint** `… ∘ phase2 ∘ phase1 …`: per pairwise relation, the oracle **consumes** it (a
verified automorphism moves it), else the Gaussian/Smith solve **forces** it (it lies in the current row-space of
the recovered linear system `H`), else it is **deferred**. A nontrivial kernel-module of `H` is a hidden
*abelian/linear* symmetry fused behind a real decision — verify, consume, refine, loop (de-fusion). `Z_{2^k}` is
*inside* the engine (an F₂ tower peeled by individualization; Lichter's FPC+rank bound does not bind — it cannot
individualize). Verdict made iso-invariant by **verify-by-reconstruction**. Cost `~O(n⁶)`; the deferral
product→sum win is untouched.

**The typed Lean seam** (`ChainDescent/Phase2Handoff.lean`): the `Phase2.Solver` / `Sound` / `IsoInvariant`
contract (+ `handoffBase_relabel`) is the interface Algorithm R witnesses. **The Lean roadmap** (`endgame §3`, IR
§11.12, do-not-rescope): **P1** extraction-soundness (minimal forcing-circuits generate `rowspace(H)`, F₂/matroid,
standalone) → **P2** forcing-model bridge (carried) → **P3** solve + canonical-form iso-invariance (the heavy
build) → **P4** capstone `canonizesRigidResidue_or_flags` (isolates the `LinearObstruction` hypothesis = the wall).
**No new citations** (unlike G3 on the symmetric side).

---

## 4. The obligation, precisely — where the seam bites

The totality predicate is `Handled` over the reachable non-discrete colourings (`Residue.lean:162`), demanding
`CellResolved` at each (`Cost.lean:156`):

```
CellResolved key S adj χ  :=  Consume.CellIsOrbit S adj χ                                    -- consume connects the cell
                              ∨ (∀ u w ∈ branches χ, keyV key adj χ u = keyV key adj χ w → u = w)  -- FORCE separates the cell
```

The rigid side owns the **second disjunct** (`keyV` injective on branches). The consume handoff gives:
`RigidObstructionAt → ¬ CellIsOrbit` (`rigidObstruction_imp_not_cellIsOrbit`) — the *first* disjunct is dead on a
rigid cell. So **`CellResolved` at a rigid cell reduces to the force branch**, and the seam's obligation is:

> **`SEAM`** — *for the exposed `RigidObstructionAt` pair `(u,w)`, `keyV key adj χ u ≠ keyV key adj χ w`* (force
> distinguishes the non-automorphic pair). Extended over the cell: `keyV` injective on branches.

**Current status of `SEAM` in Lean: entirely open.** No theorem takes a non-automorphic pair to `keyV … u ≠
keyV … w`; separation is only ever an assumed hypothesis (`Force.lean:409` `forceBy_singleton_of_separating` takes
`hsep`; `Composite.lean:238` names it the rigid solver's inherited firing obligation). This doc's plan (§7) is to
discharge `SEAM` where provable and reduce it to `hSmallAutThin` elsewhere.

---

## 5. The classification — and the wall (`ir-blindspot-solver §11.11/§11.14`)

The 2×2 that says which `RigidObstructionAt`s are provable vs. the wall:

| | abelian / linear | non-abelian / non-linear |
|---|---|---|
| **symmetry** | hidden gauge → Phase-1 linear oracle | Johnson/Cameron → cascade, **or excluded by rigidity** |
| **structure (rigid)** | multipede / `Z_{2^k}` → **Algorithm R ✓ (C#-built)** | **THE WALL** — non-schurian, open, **no witness** |

The rigid medium kills the whole **symmetry row** (hiding is abelian ⟹ the linear oracle's job; non-abelian ⟹ not
hideable ⟹ visible ⟹ excluded by rigidity — `cameron-entanglement`). Algorithm R owns **structure/linear**. The
only remainder is **structure/non-linear** = the wall. The three completeness claims, kept separate:

1. *"F₂ is the only obstruction"* — **FALSE** (Lichter's CFI-over-`Z_{2^k}`).
2. *"every rigid obstruction is linear over some abelian ring"* — **CONJECTURE** (claim #2; F₂ ⊊ `Z_{2^k}` ⊊ rings).
3. *"some rigid obstruction is non-linear"* — **OPEN, no constructible witness** (0-falsifier record).

**"Never flag on rigid" = rigid-GI ∈ P = `hSmallAutThin`** — the project's single shared wall, identical to the
symmetry seal's. Not a Lean def: it is the carried hypothesis inside `reachesRigidOrCameron_viaBoundedMinMult`
(`CascadeAffine.lean:1320`), typed `¬IsLargeSchemeViaAut IsLarge n S → BoundedMinMult B M`. **`SEAM` reduces to
exactly this** — force-completeness on rigid cells IS `hSmallAutThin`. Cameron-entanglement tightens the flag floor
to "or non-linear" (no Cameron carry on the rigid side).

---

## 6. The seam predicate — a thin Lean target this doc owns

To keep the seam crisp (rather than threading `hSmallAutThin`'s scheme-level statement through the descent), define
a **thin deepen-facing predicate** the seam discharges:

```
-- proposed, DeepenAmenable-adjacent or a new RigidHandoff.lean
def RigidResolved (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u ∈ branches χ, ∀ w ∈ branches χ,
    (∀ σ, IsColAut adj χ σ → σ u ≠ w) → keyV key adj χ u ≠ keyV key adj χ w
```

*"Force distinguishes every non-automorphic branch pair."* Then the seam theorems are:

- **`cellResolved_of_rigidResolved`** — `RigidResolved key adj χ ∧ (cell has no same-orbit pair) → CellResolved`
  force branch. (The "no same-orbit pair" side is consume's job; the interplay is §7.)
- **`RigidResolved ⟸ hSmallAutThin`** (per-node) — the reduction to the shared wall, carrying it as the single
  open hypothesis; the honest `modulo {hSmallAutThin}` end-state, mirroring the seal capstone.

`RigidResolved` is the doc's own crisp obligation: everything below either proves it (R0a, R2) or reduces it to
`hSmallAutThin` (R0b/R4).

---

## 7. The plan — Lean deliverables (the NEW bridge + the existing roadmap)

**R0a — the discretizing case (PROVABLE, no wall; do first).** When `lookData adj χ u` discretizes, `lookaheadKey u`
returns `leafMatrix` = the canonical form pinning `u` (`Force.lean:564`). Two branch vertices have equal `keyV` iff
their pinned canonical forms match iff `(adj,u) ≅ (adj,w)` as pointed graphs iff **same orbit**. So on the
discretizing regime, `keyV` separates *exactly* the non-automorphic pairs — `RigidResolved` holds. Content: the
**leaf-matrix-is-a-complete-invariant** lemma (discrete refinement distinguishes non-isomorphic pointed graphs),
the force-side analog of `handled_of_root_discrete` (`Residue.lean:176`). This is regime (1) of §1 and the clean
core — **no wall, no citation.**

**⚠ The mixed-cell / fusion subtlety (a real design point, surface it).** `CellResolved` is a *single-step*
disjunction: whole-cell consume OR whole-cell force. A **mixed cell** — some same-orbit pairs, some rigid pairs —
satisfies *neither* in one step (consume can't connect the rigid pair; force can't separate the same-orbit pair,
since `keyV` merges them even in the discretizing case). Resolution is via the **interleaving/iteration**: force
separates the rigid pairs (splitting the cell → a new `Reaches` node), and consume then fires on the same-orbit
sub-cells. So mixed cells are handled by `Handled`-over-`Reaches`, *not* by `CellResolved` at the mixed node. **Open
design question:** does `CellResolved` need a "force partially separates, then recurse" refinement, or does the
`Reaches`-iteration already carry it? (This is the same fusion resolution `endgame §1a` cites for retiring the
sequential handoff — resolve it here, in Lean, before wiring the capstone.)

**R0b — the bridge, carrying the wall.** `RigidResolved ⟸ hSmallAutThin` at each node: on the non-discretizing
regime, force-separation of the exposed non-automorphic pair is exactly force-completeness on the rigid cell =
`hSmallAutThin`. Land the reduction, carry `hSmallAutThin` as the single open hypothesis. Makes totality
conditional on exactly the shared wall — the honest `modulo {hSmallAutThin}` end-state.

**R1–R4 — Algorithm R's Lean roadmap (do-not-rescope; `endgame §3`, IR §11.12).** P1 extraction-soundness (F₂/matroid,
standalone, do first) → P2 forcing-model bridge → P3 solve + iso-invariance → P4 `canonizesRigidResidue_or_flags`.
This *builds* the linear-oracle side of `RigidResolved` for the structure/linear families, shrinking what R0b must
carry.

**R2 — per-family linear coverage (PROVABLE, imports).** CFI: `theorem_1_HOR_cfi_oddDeg` (`CFI.lean:3179`,
axiom-free) already gives orbit-recovery = warm-refined colouring at bounded depth for odd-degree CFI; `cfiFlipAut`
(:3722) + `isAut_cfiFlipAut` (:3740) construct the `Z₂^β` gauge automorphisms. These discharge `RigidResolved` for
the CFI family by import. Multipede / `Z_{2^k}` are their own witnesses (`MultipedeWitness.lean`; no `Z_{2^k}`
theorem yet — a build target). Each family landed shrinks the residue R0b carries.

**R5 — tighten the escape (`cameron-entanglement`).** Prove the rigid medium admits no hidden Johnson/Cameron
(hiding is abelian, Johnson is not) ⟹ the rigid flag floor is "or non-linear" with **no Cameron carry** ⟹ the
residue collapses to one atom shared with the symmetric side.

**Ordering.** R0a (clean, immediate) → resolve the mixed-cell design question → R0b (bridge, carry `hSmallAutThin`)
→ R1 (extraction, standalone) → R3/R4 (solve + capstone) ; R2 (per-family) and R5 (tighten) in parallel as
residue-shrinkers.

---

## 8. Gap ledger

| Item | Statement | Status |
|---|---|---|
| **handoff object** | `RigidObstructionAt` exposed on consume-stall | **PROVED** (`not_amenablePath_imp_rigidObstruction`), sound-defer PROVED (`rigidObstruction_imp_not_cellIsOrbit`) |
| **R0a** | discretizing cell → `keyV` separates non-aut pairs (`RigidResolved`) | **PROVABLE, no wall** — leaf-matrix complete-invariant lemma; not yet built |
| **mixed-cell** | fusion cell resolved by force-split + `Reaches`-iteration | **DESIGN QUESTION** — does `CellResolved` need refining? (open) |
| **R0b / SEAM** | `RigidResolved ⟸ hSmallAutThin` (bridge) | **not built** — the reduction to the shared wall |
| **R1–R4** | Algorithm R Lean (`canonizesRigidResidue_or_flags`) | **roadmap** (`endgame §3`); C# complete, Lean not started |
| **R2** | per-family: CFI (`theorem_1_HOR_cfi_oddDeg`), `Z_{2^k}`, multipede | CFI **axiom-free**; `Z_{2^k}`/multipede **build targets** |
| **the wall** | `hSmallAutThin` (force-complete on rigid = rigid-GI∈P) | the **shared wall** — carry-only; `reachesRigidOrCameron_viaBoundedMinMult` carries it on the symmetric side |
| **R5** | no rigid Cameron ⟹ "or non-linear" only | `cameron-entanglement` — conjecture-level, empirically solid |

Everything conjectural lives in **`hSmallAutThin`** (shared, covered whenever anyone covers it). The seam's *own*
new content is **R0a** (clean) + **R0b** (bridge) + the **mixed-cell design question** — the rest is the existing
Algorithm R roadmap and per-family imports.

---

## 9. Traps and pointers

- ⚠ **Do not claim "force separates non-automorphic pairs" as proved** — it is nowhere proved in Lean; it is an
  assumed `hsep`/`hne` everywhere and is the *open* obligation (`Force.lean:409`, `Composite.lean:238`). R0a proves
  it *only* on the discretizing regime.
- ⚠ **`hSmallAutThin` is a carried hypothesis, not a lemma** (`CascadeAffine.lean:1320`); "rigid solver" / "Algorithm
  R" are C#/prose, not Lean defs. Don't cite them as built Lean objects.
- ⚠ **`CellResolved` is single-step** — it does not model the interleaving; mixed/fusion cells need the
  `Reaches`-iteration (or a refined predicate). This is the load-bearing design question (§7).
- **Pointers.** Consume side: `chain-descent-deepen-supply.md`. Solver design: `ir-blindspot-solver` §11.11–§11.14.
  Two-seals frame + roadmap: `endgame-spec` §1a/§3. No-rigid-Cameron: `cameron-entanglement`. Seal capstone:
  `reachesRigidOrCameron_viaBoundedMinMult` (`CascadeAffine.lean:1314`). Typed seam: `Phase2Handoff.lean`. CFI:
  `CFI.lean:3179,3722`.
