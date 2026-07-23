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
> This is the next track to build. **The mixed-cell/fusion design question is SETTLED (§8.1, 2026-07-23):**
> the "Progress" completeness predicate IS the ALREADY-BUILT sel-rewrite (`Select.HandledS`/`NodeResolved`/`selNode`,
> 2026-07-18) — a resolver-aware selector that picks a resolvable cell (single-path, `②` preserved) and flags ONLY
> at the true mutual stall (`selNode_stall_iff`). No object change, no new predicate.
>
> **✅ R0a LANDED 2026-07-23 (`ChainDescent/RigidSeal.lean`, in `build.sh`, axiom-clean).** Force separates
> non-automorphic pairs on the DISCRETIZING regime. **★ FINDING: the plain `Force.lookaheadKey` is INSUFFICIENT**
> — its leaf matrix is adjacency-only, so equal keys give only a *graph* automorphism (no `σ u = w`, no
> χ-preservation). The fix, built: the augmented key **`leafColKey`** recording the complete coloured-pointed
> invariant `(pin-rank, χ-in-rank-order, leaf-matrix)`; `colAut_of_leafColKey_eq` proves equal keys ⟹ a
> **colour**-automorphism `u↦w` (σ = π_w⁻¹π_u), `rigidResolved_leafColKey` discharges `RigidResolved`, and
> `nodeResolved_leafColKey_of_rigid_discretizing` gives `Select.NodeResolved` on a rigid discretizing cell (feeds
> `HandledS` via `answersS_of_handledS`). `leafColKey` is the strictly-stronger, still-poly, still-equivariant
> force key of record.
>
> **✅ R0b LANDED 2026-07-23 (`RigidSeal.lean`, axiom-clean).** The leafColKey precursor:
> `smallAutThinAt_of_all_discretize` (vacuous on the discretizing regime), `rigidResolved_of_smallAutThin`,
> `nodeResolved_leafColKey_of_rigid` — `RigidResolved`/`NodeResolved` for the whole cell modulo the
> non-discretizing separation, shrinking the blanket `hsep`.
>
> **⚠ SEAM CORRECTED + ✅ `compKey` LANDED 2026-07-23 (§9, `RigidSeal.lean`, axiom-clean).** The R0b carried object
> was **wrongly** glossed "`SmallAutThinAt` = `hSmallAutThin` at the seam." **RETRACTED.** `hSmallAutThin`
> (`CascadeAffine.lean:1320`) is a **static `SchurianScheme` predicate** (minMult-form of Babai's SRG theorem) — a
> *symmetry-consumption / Route-C* artifact, **false on consumable cases** (multipede + small added symmetry,
> already reduced by consume). The canonizer's actual residue is the **dynamic `¬Select.HandledS`** (interleaved
> mutual stall); the two join only via the unbuilt W1 bridge (*one-directional* seal-transfer, not `↔`). And
> `SmallAutThinAt`-over-`leafColKey` is **not dischargeable** (its non-discretizing pairs are exactly where the
> histogram ties). **The fix — the composite force key `compKey sk`:** discretizing branch = `leafColKey` (tag
> `1 ::`, R0a); non-discretizing rigid branch = the **solver key `sk`** (tag `0 ::`, P3). Disjoint tags ⟹ mixed
> pairs separate free; the sole carried obligation is **`SolverSeparates`** = *the solver key separates the
> both-non-discretizing rigid pairs* — a property of an **algorithm we build**, discharged by the solver's
> soundness (P3), **NOT** an SRG citation. Landed axiom-clean: `keyEquivariant_compKey` (① obligation = P3's
> `IsoInvariant`, structural given `KeyEquivariant sk`), `rigidResolved_compKey` (whole cell modulo
> `SolverSeparates`), `nodeResolved_compKey_of_rigid` (the force half of "consume-can't-fire ⟹ force-fires"; the
> consume half is the untouched `cellIsOrbit` disjunct of `NodeResolved`). `sk`/`SolverSeparates` are stubbed to
> P3. **Next:** P1 (extraction, standalone F₂/matroid) → P3 (build `sk` = the ring solve, discharges
> `SolverSeparates`) → R6(c)/P4. The residue is `¬HandledS` at non-linear rigid; `hSmallAutThin` stays home on the
> Route-C symmetry seals (W1, a separate obligation).
>
> - **C# — DONE.** Algorithm R is built, wired (`EnableRigidSolver` default-ON), and validated: `Option2Solver.cs`
>   (recover → solve → emit → verify, ring-general, **B1–B6 all landed, 50 tests**; `ir-blindspot-solver` STATUS +
>   §11.12). It solves CFI / multipede / `Z_{2^k}` / general-arity / `s`-fold covers. This is the **reference spec**
>   the Lean must certify — not a lift (there is no Smith-normal-form in Lean yet).
> - **Lean — R0a/R0b LANDED; the SOLVER is still empty.** What exists: the typed contract
>   `Phase2.Solver`/`Sound`/`IsoInvariant` (`Phase2Handoff.lean:74,78,85`) + `handoffBase_relabel`; the force
>   resolvers `lookaheadKey` and now the augmented **`leafColKey`** (`RigidSeal.lean`); **the force-separation
>   theorem on the discretizing regime (R0a) + the wall reduction (R0b), all axiom-clean.** **Still no Lean
>   rigid-solver, no Smith/ring solve, no P1–P4, no `canonizesRigidResidue_or_flags`.** ⚠ The `RRU` namespace in
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
non-automorphic pair**. ⚠ **UPDATED 2026-07-23 — this is now PARTLY PROVED (R0a/R0b, `RigidSeal.lean`).** The
augmented key `leafColKey` provably separates every non-automorphic branch pair on the **discretizing regime**
(`RigidSeal.rigidResolved_leafColKey`, axiom-clean), and R0b (`rigidResolved_of_smallAutThin`) reduces the whole
cell to the wall `SmallAutThinAt` (non-discretizing pairs only). The blanket assumed `hsep`
(`Force.lean:409` `forceBy_singleton_of_separating`; `Composite.lean:238`, `DeepenAmenable.lean:947`) is thus
shrunk from *all* non-automorphic pairs to just the non-discretizing residue. `Handled` (`Residue.lean:162`) /
`HandledS` (`SelectNode.lean:842`) quantify `CellResolved`/`NodeResolved` over the reachable non-discrete
colourings; R0a is the **first** force-branch discharge (every prior discharge went through *consume*).

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

> **▶ UPDATED 2026-07-23 — R0a/R0b changed this list.** `RigidSeal.lean` now builds the **force-separation
> theorem on the discretizing regime** + the reduction to the wall. What remains unbuilt is the *solver* (P1–P4)
> and the *non*-discretizing separation (`SmallAutThinAt`, = the wall). Corrected below.

- **No rigid-solver object.** "Algorithm R" / "linear oracle" are C#/prose only; the Phase-1 linear oracle is
  `LinearOracle.configSwap_of_aut/twin` inside CFI, not a general solver.
- **No Smith normal form / ring solve** anywhere in Lean.
- **✅ Force-separation on the DISCRETIZING regime is now BUILT** (R0a, `RigidSeal.lean`, axiom-clean): the
  augmented key `leafColKey` + `rigidResolved_leafColKey` + `nodeResolved_leafColKey_of_rigid_discretizing`.
  **What is NOT built:** the *non*-discretizing separation — carried as the wall `SmallAutThinAt` (R0b's
  `rigidResolved_of_smallAutThin`); it is discharged by the rigid solver (P3), not yet built.
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
- **✅ The mixed-cell / fusion design question — SETTLED 2026-07-23 (traced against source).** The answer:
  **the "Progress" completeness predicate the user endorsed IS THE ALREADY-BUILT SEL-REWRITE
  (`Select.HandledS`/`NodeResolved`/`selNode`, landed 2026-07-18 — `SelectNode.lean`). It is not a new predicate,
  and it is NOT an object change that surrenders the single-path `②` bound.** ⚠ **This CORRECTS an earlier
  version of this bullet** that described the mechanism as "fan-out over the min-key orbit-reps + `Reaches`
  recursion" against `forceThenConsume`/`Stall.guard`; that is *not* the object of record and is withdrawn. The
  correct trace:
  - **`Stall.stalled := 1 < (narrow …).length`** (`Stall.lean:79`) makes the blind `Stall.guard` object
    DELIBERATELY single-path — it flags on *any* fan-out, which is exactly what buys the unconditional `②`
    node-bound (`resolvedAll_guard`). The authors already diagnosed (`Stall.lean:225–242`) that the blind object's
    flag is *spurious*: it reads only the **least-colour** cell, so it flags at a stalled cell `A` even when
    another cell `B` is resolvable and individualizing in `B` would expose what `A` needs (the exposure/fusion
    dependency). The scoped fix — a **resolver-aware selector** — is the sel-rewrite, and it is BUILT.
  - **`selNode` (`SelectNode.lean:371`)** probes all cells, commits to the least **resolvable** one (the cell whose
    `cellNarrow` reaches `≤ 1`), hands each kept child its refined colouring, and emits `[]` = flag **iff NO
    non-singleton cell narrows to `≤ 1`** (`selNode_stall_iff`, :810) — the **true mutual stall**. Each resolved
    cell still narrows to `≤ 1`, so **the object stays single-path and `②` is preserved** (`Publication.canonForm?`
    IS this fused object).
  - **`NodeResolved key S adj χ := ∃ non-singleton cell c, (cellNarrow … c).length ≤ 1`** (:838) = *"some cell can
    progress."* **`HandledS := ∀ reached non-discrete χ, NodeResolved`** (:842). Its negation — a reached node
    where **no** cell resolves — is exactly the user's *"a state that cannot progress"*, and it is
    `selNode_stall_iff`'s true mutual stall.
  - **The deflation + answers chain is all built and axiom-clean:** `nodeResolved_of_cellResolved` / `handledS_of_handled`
    (:858 — `Residue.Handled ⟹ HandledS`, strictly weaker, the exposure witness in `Regression.lean` shows strict);
    `answersS_of_handledS` (:933 — `HandledS ⟹` the fused canonizer ANSWERS, no flag); `residue_of_not_handledS`
    (:863 — `¬HandledS ⟹ Residue`); `handledS_of_sameOrbits` (:868 — reads the supply only through its orbits, so
    it transfers to deepen the same way `①c` does); `handledS_of_seal` (:879 — the seal populates it per family).
    So the **residue is already the deflated `¬HandledS`** (the true mutual stall), not the blind `¬Handled`.
  - **A single mixed CELL** (same-orbit `{a,b}` + rigid `{u,w}`, all in one cell, ≥2 non-automorphic branches
    *tying* on the min key so `cellNarrow` of THAT cell stays `> 1`) resolves iff **some OTHER cell** is resolvable
    (selector picks it, single-path, `Reaches`-exposure handles the rest). If NO cell is resolvable, `selNode`
    flags — and that is the **genuine residue** (a same-key non-automorphic pair in every cell = the key's / force's
    weakness), *not* spurious. This is correct poly-or-flag behaviour, and closing it is force STRENGTH (R6(c) / the
    wall), not a predicate change.
  **Consequences for the build (do these):**
  1. **R0a targets `NodeResolved`, not whole-cell `RigidResolved`.** On the discretizing regime R0a's content is
     "the discretizing cell's leaf-matrix `keyV` separates its exposed non-automorphic pairs ⟹ that cell's
     `cellNarrow` reaches `≤ 1` ⟹ `NodeResolved` at the node ⟹ `HandledS` there." Feed `answersS_of_handledS`.
  2. **`RigidResolved` (§4 seam predicate) should be stated per-cell as "the exposed rigid pairs get distinct
     `keyV` so `cellNarrow` reaches `≤ 1`"** — i.e. it discharges `NodeResolved` for that cell, not a whole-node
     claim. `HandledS` is the node-level target it feeds.
  3. **This IS the Lean form of the fusion resolution `endgame §1a` cites** — the resolver-aware selector +
     `Reaches`-exposure, single-path, flag = true mutual stall. It confirms retiring the sequential handoff.
  4. **No new Lean predicate is needed for the "Progress" core** — the work is (i) realign R0a/`RigidResolved`
     onto `NodeResolved`/`HandledS` (above), (ii) wire deepen's `HandledS` per family via `handledS_of_sameOrbits`
     (T1), (iii) R6(c) force-strength for the true-mutual-stall residue.
- **✅ R0b — the leafColKey precursor — LANDED 2026-07-23 (`RigidSeal.lean`, axiom-clean).**
  `smallAutThinAt_of_all_discretize` (vacuous on the discretizing regime), `rigidResolved_of_smallAutThin`
  (`RigidResolved (leafColKey)` for the whole cell modulo the non-discretizing separation),
  `nodeResolved_leafColKey_of_rigid` (→ `Select.NodeResolved`). ⚠ **The carried object `SmallAutThinAt` is the
  leafColKey-specialization, NOT the scheme wall `hSmallAutThin` — see the retraction in §9 below. It is not
  dischargeable; superseded by `compKey`/`SolverSeparates` (§9).**
- **✅ THE DISCHARGEABLE SEAM — `compKey` — LANDED 2026-07-23 (§9, `RigidSeal.lean`, axiom-clean).** The connecting
  theorem is *"when consume can't fire, force must"*, stated in a **dischargeable** form. The composite force key
  `compKey sk` = `leafColKey` on the discretizing branch (tag `1 ::`, R0a) ∘ the **solver key `sk`** on the
  non-discretizing rigid branch (tag `0 ::`, P3). Disjoint tags ⟹ mixed pairs separate for free. Landed:
  `keyEquivariant_compKey` (① obligation = P3's `Phase2.IsoInvariant`, structural given `KeyEquivariant sk`),
  `SolverSeparates` (the sole carried obligation = *the solver key separates the both-non-discretizing rigid
  pairs*), `rigidResolved_compKey` (whole cell modulo `SolverSeparates`), `nodeResolved_compKey_of_rigid`. **Why
  this is dischargeable where `hSmallAutThin` isn't:** `SolverSeparates` is a property of the **rigid solver we
  build** (discharged by P3's `Phase2.Sound` — distinct canonical forms for non-isomorphic pointed residues, a
  flag = the honest non-linear residue), not a static SRG-scheme citation. `sk`/`SolverSeparates` are stubbed to
  P3. **The honest residue is `¬Select.HandledS` at non-linear rigid** (the consume half = the untouched
  `cellIsOrbit` disjunct; the force half = `compKey`); `hSmallAutThin` is a *separate* obligation that stays home
  on the Route-C symmetry seals (W1).

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
  These help discharge `SolverSeparates`/`RigidResolved` for CFI by import — but ⚠ **not a freebie:**
  `theorem_1_HOR_cfi_oddDeg` gives discreteness over a **base set**, whereas `compKey`/`lookData` individualize a
  **single** vertex, so odd-degree CFI sits in the *non*-discretizing branch (needs the solver key `sk`, not R0a's
  vacuity). `Z_{2^k}` / multipede (`MultipedeWitness.lean`) are build targets (no `Z_{2^k}` theorem yet). Each
  family landed shrinks what `SolverSeparates`/P4 carries.
- **R5.** No-rigid-Cameron (`cameron-entanglement`): rigid medium admits no hidden Johnson/Cameron ⟹ the rigid flag
  floor is "or non-linear" with no Cameron carry.

### 8.4 Ordering + dependencies

**Mixed-cell design question SETTLED (§8.1)** — the "Progress" predicate layer is the already-built sel-rewrite
(`HandledS`/`NodeResolved`/`selNode`), so the ordering is: **✅ `R0a` DONE** (against `NodeResolved`, feeds
`answersS_of_handledS`) → **✅ `R0b` DONE** (leafColKey precursor) → **✅ `compKey` DONE** (§9 — the dischargeable
seam; carried object is now `SolverSeparates` over the composite key, a solver property) → **now: `P1`**
(extraction, standalone) → `P2`/`P3` (solve + iso, the heavy build — **P3 builds `sk` and discharges
`SolverSeparates` via `Phase2.Sound`**, NOT the static `hSmallAutThin`) → `P4` (capstone) + **R6(c)**
(force-separates-every-exposed-rigid-pair, the strength-dependent residue closure, co-evolves with P3/P4).
`R2` (per-family, via `handledS_of_seal`/`handledS_of_sameOrbits`) and `R5` (tighten) run
in parallel as residue-shrinkers. The C# is the reference throughout (validate Lean claims against `Option2Solver`
behaviour before proving).

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
| **R0a** | discretizing → `keyV` separates non-aut pairs (`RigidResolved`) → `NodeResolved` | **✅ LANDED 2026-07-23, axiom-clean** (`RigidSeal.lean`, in `build.sh`) — via the augmented key `leafColKey` (plain `lookaheadKey` INSUFFICIENT); `colAut_of_leafColKey_eq` / `rigidResolved_leafColKey` / `nodeResolved_leafColKey_of_rigid_discretizing` |
| **mixed-cell** | resolver-aware selector picks a resolvable cell (single-path) + `Reaches`-exposure; flag = true mutual stall | **✅ SETTLED 2026-07-23** (§8.1) — the "Progress" predicate IS the ALREADY-BUILT sel-rewrite `Select.HandledS`/`NodeResolved`/`selNode` (2026-07-18). No object change, no new predicate, `②` single-path PRESERVED. |
| **R0b** | leafColKey precursor (non-discretizing separation) | **✅ LANDED 2026-07-23, axiom-clean** (`RigidSeal.lean`) — `smallAutThinAt_of_all_discretize` + `rigidResolved_of_smallAutThin` + `nodeResolved_leafColKey_of_rigid`. ⚠ `SmallAutThinAt` is the leafColKey-specialization, **NOT the scheme wall `hSmallAutThin`** and **not dischargeable**; superseded by `compKey` |
| **compKey** | dischargeable seam: force key = `leafColKey` (disc, tag `1::`) ∘ solver key `sk` (non-disc rigid, tag `0::`); carried obligation = `SolverSeparates` (a solver property, discharged by P3's `Phase2.Sound`) | **✅ LANDED 2026-07-23, axiom-clean** (§9, `RigidSeal.lean`) — `compKey` + `keyEquivariant_compKey` (given `KeyEquivariant sk`) + `SolverSeparates` + `rigidResolved_compKey` + `nodeResolved_compKey_of_rigid`. `sk`/`SolverSeparates` stubbed to P3. The force half of "consume-can't-fire ⟹ force-fires." |
| **R6** | interleaving-convergence: `¬Amenable ⟹ exposed `RigidObstructionAt` ⟹ force separates it ⟹ `NodeResolved` ⟹ no reached node is a genuine mutual stall (`selNode_stall_iff`) except at the wall` | **predicate layer BUILT** (`HandledS`/`NodeResolved`/`selNode_stall_iff`/`answersS_of_handledS`/`handledS_of_handled`, all axiom-clean). **Remaining = (c) force-separates-every-exposed-rigid-pair** (`RigidObstructionAt`'s pair gets distinct `keyV` ⟹ its cell `cellNarrow`s to ≤1 ⟹ `NodeResolved`) — the substance, tied to rigid-resolver STRENGTH, co-evolves with P3/P4. Deepest ③/totality claim. |
| **P1** | minimal forcing-circuits generate `rowspace(H)` | **not built** — F₂/matroid, standalone, do first |
| **P2** | forcing-model bridge (1-WL forcing = ring propagation) | **carried** — model hypothesis |
| **P3** | build `sk` (solve Smith/ring) + canonical-form iso-invariance ⟹ **discharges `SolverSeparates`** (`Phase2.Sound`) + `KeyEquivariant sk` (`Phase2.IsoInvariant`) | **not built** — the heavy build |
| **P4** | `canonizesRigidResidue_or_flags` | **not built** — the capstone; isolates the non-linear-rigid residue (`¬HandledS`) |
| **R2** | per-family: CFI, `Z_{2^k}`, multipede | CFI **axiom-free** (`theorem_1_HOR_cfi_oddDeg`, but non-disc ⟹ needs `sk`); `Z_{2^k}`/multipede **build targets** |
| **residue (rigid)** | `¬Select.HandledS` at non-linear rigid (dynamic, per-node) | the honest rigid residue — conjecturally empty (claim #2/#3, §5) |
| **W1** | scheme `hSmallAutThin` seal ⟹ `HandledS`-for-family (Route-C symmetry side) | **separate obligation** — one-directional transfer, NOT `↔`; `hSmallAutThin` stays a carried SRG citation here |
| **R5** | no rigid Cameron ⟹ "or non-linear" only | `cameron-entanglement` — conjecture, empirically solid |
| **C#** | `Option2Solver` B1–B6 | **COMPLETE** (50 tests) — the reference spec |

⚠ **The conjectural content is now TWO cleanly-separated objects, not one conflated "wall":** (A) the rigid
residue `¬HandledS` at non-linear rigid — discharged (linear part) by `compKey`/`SolverSeparates` via P3, its
non-linear part conjecturally empty (§5 claims #2/#3); and (B) `hSmallAutThin` — the static SRG-scheme citation
that stays home on the Route-C symmetry seals, reached via W1. **They are related but NOT equal**; the old
"`SmallAutThinAt` = `hSmallAutThin` at the seam" identity is retracted. The seam's *own* new content is **R0a** +
**R0b** + **`compKey`**; the solver's is **P1–P4**; the rest is per-family imports and the C# reference. **R6's
predicate layer is already
built** (the sel-rewrite `HandledS`/`NodeResolved`/`selNode`, 2026-07-18); R6's remaining content is **(c)**
force-separates-every-exposed-rigid-pair, which lands alongside P3/P4 once the solver's strength is fixed — it is
NOT a corollary of P4 (P1–P4 build the solver in isolation; R6(c) is the claim the force key actually separates
the exposed pairs, closing the true-mutual-stall residue).

---

## 11. Traps and pointers

- ⚠ **"Force separates non-automorphic pairs" is assumed (`hsep`) in the GENERAL case** (`Force.lean:409`,
  `Composite.lean:238`) — but **R0a now PROVES it on the discretizing regime** (`RigidSeal.rigidResolved_leafColKey`,
  axiom-clean, with the augmented key `leafColKey`; the plain `lookaheadKey` is insufficient). The non-discretizing
  regime is R0b (carries `hSmallAutThin`).
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
