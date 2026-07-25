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

## ▶ STATUS (2026-07-25)

> **The C# rigid solver is COMPLETE, and on the Lean side the Algorithm-R *scaffold* (seam R0a/R0b/`compKey` +
> reduction layers P1/P3-I/P3-Sound/P2/P3-F₂ core), the full `gen`-labelling reduction chain (A)–(D), AND the concrete
> rigid refinement `ref` (steps 1–6b, `RigidRefine.lean`) are all built (axiom-clean, gate green ~99 modules).**
>
> ▶▶ **HEADLINE FOR A FRESH READER.** The `gen`-chain (A)–(D) reduced the rigid **linear** `①` to *"supply a discrete,
> equivariant `ref`"* (`RigidGen.genOfRef` reads `rankPerm` of a discrete `ref`; `①` needs only `RefEquivariant ref`).
> The concrete `ref` is now built, and its state is the current frontier:
> - **✅ The DISCRETIZING reader `structRead` (step 6b) is the object of record** — reads each vertex's RREF-column
>   signature over a **recovered iso-invariant column order** `ord`. Its whole rigid-linear seal rests on **exactly
>   three carried `Recover` facts**: `OrdEquivariant ord` + `HsEquivariant Hs` (order/system transport ⟹ `①`, via the
>   χ-rank-free `framedRREFBy_transport` — **no `Discrete χ`**) and `structRead` injective (discretization ⟹ `②`, =
>   "the recovered ordered base pins every vertex" = full-rank on the rigid residue). Capstones
>   `keyEquivariant_compKey_structRead` (`①`) / `nodeResolved_compKey_structRead` (`②`/firing).
> - **⚠⚠ DO-NOT-RE-DERIVE — the single-bit reader `refineByFrame` (Route B′, steps 1–5) CANNOT discretize.** It reads
>   one F₂ bit per vertex (coordinate-free forcing over P2's `rowspace`), so `①` is unconditional (`refEquivariant_refineByFrame`)
>   **but** on a rigid cell (no gauge, all forced) it gives ≤2 classes ⟹ **fails the rigid multipede (the primary target).**
>   The reduction lemmas (`hemit_of_forcedSeparates` etc.) are correct and kept; the mis-scoping was **contained to the
>   reader** (probe `scratchpad/probe_rigid.py`). The χ-frame route (C) has a `Discrete χ` gap; both are superseded for
>   the discretizing job by `structRead` (§8.2 steps 5–6b).
> - **▶ WHAT REMAINS:** discharge the three carried `Recover` facts — either **`IsRigidF2 ⟹ structRead` injective**
>   (self-contained Lean, via `RigidRREF`'s rank toolkit, shrinks `②`) or the **concrete Lean `Recover`** (per family;
>   the same object as `ForcingModel.bridge`/L4, §9.2) — then **P3-ring** (`Z_{2^k}`), then **P4**
>   (`canonizesRigidResidue_or_flags`).
>
> **Module chain to read:** `RigidRREF`(A,B) → `RigidFrame`(C) → `RigidGen`(D) → **`RigidRefine`** (steps 1–6b: coord-free
> reader 1–5, general interface 6, structural reader 6b); see §8.2 and §10. The consume side feeds a clean per-node handoff
> object, and discharging its `Amenable` hypothesis is a rigid-side deliverable (§9.1). **The mixed-cell/fusion design
> question is SETTLED (§8.1):** the "Progress" predicate IS the already-built sel-rewrite
> (`Select.HandledS`/`NodeResolved`/`selNode`, 2026-07-18) — resolver-aware, single-path, `②` preserved, flags ONLY at
> the true mutual stall (`selNode_stall_iff`).
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
> P3. **✅ P1 LANDED** (`ForcingCircuits.lean`, extraction-soundness — `forced_certificate`: forced ⟹ backed by a
> `rowspace` codeword) **· ✅ P3-I LANDED** (`RigidSolverInterface.lean`, the interface: `compKey`'s obligations
> reduced to the pointed solver contract `PtSolver`/`PtIsoInvariant`/`PtSound`(+`hemit`) via `skOf` +
> `keyEquivariant_skOf`/`solverSeparates_skOf`), both axiom-clean 2026-07-23. ⚠ **Mathlib Smith =
> noncomputable/existence-only** ⟹ P3 is construction not a lift; F₂=field→RREF tractable, ring→finite-Smith heavy.
> **✅ P3-Sound LANDED 2026-07-23** (`RigidSolverSound.lean`): **soundness is FREE** (`emitLabel`/`ptSound_emitLabel`
> — emit the pointed relabelling `ptForm`, `PtSound` for any `gen`), and `①` reduces to **`GenEquivariant gen`**
> (the canonical-labelling law); capstones `keyEquivariant_compKey_emitLabel`/`nodeResolved_compKey_emitLabel` close
> the whole rigid seam on `GenEquivariant + hemit`. **⟹ the entire rigid `①` = one poly total equivariant `gen` =
> canonization of the linear code.** **✅ P2 LANDED 2026-07-23** (`ForcingModel.lean`): the forcing-model bridge
> graph↔F₂ (`ForcingModel.bridge` = Layer B WL=unit-prop, carried) + `recoverable_of_model` (transport: graph-forced
> ⟹ `rowspace(H)` codeword, via P1) + `rowspace_eq_span_recoverable` (exact recovery mod carried generation).
> **✅ P3-F₂ CORE LANDED 2026-07-23** (`RigidSolveF2.lean`): the F₂ rigid-solve determinacy `unique_solution_of_rigid`
> (rigid `IsRigidF2` = trivial kernel ⟹ ≤1 solution to `Hx=b`, the unique-solve Gaussian gives where unit-prop stalls
> at `2^{Θ(n)}`; rigidity is a `rowspace(H)`-only property via `dotP_zero_rowspace`). **The concrete `gen` is SCOPED
> into four sub-bricks (§8.2), reusing the already-built executable F₂ echelon (`Kernel.echelon`); ✅ sub-brick (A) —
> the canonical column-ordered RREF `rrefCanon` — LANDED 2026-07-23** (`RigidRREF.lean`, axiom-clean, gate green:
> `pivInv_rrefCanon`). **✅ sub-brick (B) — RREF-CANONICITY — COMPLETE 2026-07-24** (`rrefCanon_eq_of_span_eq`: same
> row space ⟹ equal canonical RREF, via kernel triviality + leading-position + reconstruction ⟹ `pivotCols_eq` +
> `pivotRow_eq`; all axiom-clean). **✅ (C) χ-FRAME — LANDED 2026-07-24** (`RigidFrame.lean`: RREF is NOT
> column-equivariant, so order columns by iso-invariant χ-rank ⟹ the framed system is LITERALLY σ-invariant
> [`leafMatrix` pattern, via `RigidSeal.rankInv_transport`]; `framedRREF_transport` ⟹ `gen`'s `GenEquivariant`
> reduces to the extraction transporting as `H ↦ H.map (transportRow σ)`, carried). **✅ (D) READ-LABELLING — LANDED
> 2026-07-24** (`RigidGen.lean`: `genOfRef ref` = `rankPerm` of the solve-refined colouring; `rankPerm_transport` ⟹
> `genEquivariant_genOfRef` (`GenEquivariant ⟸ RefEquivariant ref`); capstones `keyEquivariant_compKey_genOfRef` /
> `nodeResolved_compKey_genOfRef` close `compKey`'s `①`/firing). **▶▶ THE (A)–(D) `gen`-REDUCTION CHAIN IS COMPLETE**
> — the rigid **linear** `①` reduces to just: `RefEquivariant ref` (⟸ C ⟸ carried extraction-transport) + `ref`
> discrete on residue (⟸ solve discretizes, per-family). **Next:** wire P2's extraction into the concrete `ref`
> (`refineByFrame`), then P3-ring → R6(c)/P4. Residue = `¬HandledS` at non-linear rigid; `hSmallAutThin` = separate
> (Route-C, W1).
>
> - **C# — DONE.** Algorithm R is built, wired (`EnableRigidSolver` default-ON), and validated: `Option2Solver.cs`
>   (recover → solve → emit → verify, ring-general, **B1–B6 all landed, 50 tests**; `ir-blindspot-solver` STATUS +
>   §11.12). It solves CFI / multipede / `Z_{2^k}` / general-arity / `s`-fold covers. This is the **reference spec**
>   the Lean must certify — not a lift (there is no Smith-normal-form in Lean yet).
> - **Lean — the Algorithm-R scaffold + the `gen`-reduction chain LANDED, all axiom-clean, gate green (92 modules).**
>   Built: the typed contract `Phase2.Solver`/`Sound`/`IsoInvariant` (`Phase2Handoff.lean`) + `handoffBase_relabel`;
>   the force key **`leafColKey`** + composite **`compKey`** (`RigidSeal.lean`, R0a/R0b/§9); **P1**
>   (`ForcingCircuits.lean`), **P3-I** (`RigidSolverInterface.lean`), **P3-Sound** (`RigidSolverSound.lean`), **P2**
>   (`ForcingModel.lean`), **P3-F₂ core** (`RigidSolveF2.lean`); and the **`gen` chain (A)–(D)**: **(A)+(B)**
>   `RigidRREF.lean` (canonical RREF `rrefCanon` + `rrefCanon_eq_of_span_eq` = RREF is a canonical fn of the
>   subspace), **(C)** `RigidFrame.lean` (`framedRREF_transport` = χ-rank frame ⟹ σ-invariant), **(D)**
>   `RigidGen.lean` (`genOfRef`/`genEquivariant_genOfRef` + capstones = the whole `compKey` `①` closes on
>   `RefEquivariant ref`). **Still NOT built:** the concrete `ref` (`refineByFrame` = P2-extraction wiring +
>   solve — the `②`/poly content, no longer an equivariance obligation), the ring-general Smith (`Z_{2^k}`), and the
>   capstone `canonizesRigidResidue_or_flags` (P4). ⚠ The `RRU` namespace in `Phase2Handoff.lean` (the *sequential* R(G)
>   handoff) is **RETIRED** for the interleaved model (`endgame §1a`) — do not build on it; the surviving seam is
>   `Phase2.Solver`/`Sound`/`IsoInvariant`.
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

## 7. The Lean gap — what IS and is NOT built

> **▶ UPDATED 2026-07-24 — the whole Algorithm-R scaffold AND the `gen`-labelling reduction chain (A)–(D) landed.**
> The seam (R0a/R0b/`compKey`), the solver's *reduction* layers (P1, P3-I, P3-Sound, P2, P3-F₂ core), and the full
> `gen` chain (A canonical RREF, B RREF-canonicity, C χ-frame, D read-labelling) are all built and axiom-clean. What
> remains is the concrete `ref` (extraction wiring) + P3-ring + P4, and the carried model obligations. The full
> ledger is §10; the sub-brick plan is §8.2.

**Built (axiom-clean, in `build.sh`):**
- **The seam** — `leafColKey` + `compKey` (`RigidSeal.lean`): force separates non-aut pairs on the discretizing
  regime, and the composite key carries the sole obligation `SolverSeparates`.
- **P1** `ForcingCircuits.lean` — F₂ extraction-soundness (`forced_certificate`).
- **P3-I** `RigidSolverInterface.lean` — reduce `compKey`'s obligations to the pointed solver contract.
- **P3-Sound** `RigidSolverSound.lean` — soundness FREE; the whole `①` reduces to one canonical labelling `gen`.
- **P2** `ForcingModel.lean` — graph↔F₂ forcing-model bridge + transport of P1 to the graph level.
- **P3-F₂ core** `RigidSolveF2.lean` — the F₂ rigid-solve determinacy (`unique_solution_of_rigid`).
- **`gen` chain (A)–(D)** — `RigidRREF.lean` (A `rrefCanon`/`pivInv_rrefCanon` + B `rrefCanon_eq_of_span_eq`: the
  executable F₂ RREF is a canonical function of the row *subspace*, via kernel triviality + leading-position +
  reconstruction ⟹ `pivotCols_eq`/`pivotRow_eq`); `RigidFrame.lean` (C `framedRREF_transport`: χ-rank column order
  makes the framed RREF σ-invariant — RREF is *not* column-equivariant); `RigidGen.lean` (D
  `genEquivariant_genOfRef` + capstones `keyEquivariant_compKey_genOfRef`/`nodeResolved_compKey_genOfRef`: the
  labelling `genOfRef ref` = `rankPerm` of the solve-refined colouring closes `compKey`'s `①`/firing on
  `RefEquivariant ref` + `ref`-discrete). **⟹ rigid linear `①` fully reduced to the carried `ref`.**

**NOT built:**
- **The concrete `ref` (`refineByFrame`)** — wire P2's extraction (`gForce`/`encodeFreeFast`) into the χ-framed
  RREF solve to produce the refined colouring `ref adj χ`. **★ The `gen` REDUCTION CHAIN (A)–(D) IS BUILT AND
  axiom-clean** (`RigidRREF`/`RigidFrame`/`RigidGen`): `genOfRef ref` is `GenEquivariant` given `RefEquivariant ref`
  (⟸ (C) `framedRREF_transport` ⟸ carried extraction-transport), and the `compKey` `①`/firing capstones close on
  `RefEquivariant` + `ref` discrete-on-residue. So what is NOT built is exactly the concrete `ref` = the extraction
  wiring + the solve, **not** the (now-reduced) canonicity/equivariance/labelling layers. This is the graph-canonization
  of the linear code, `②`/poly, still substantive but no longer an equivariance obligation.
- **No Smith / ring solve** (`Z_{2^k}` = P3-ring); Mathlib's Smith is noncomputable/existence-only (see §8.2 gate).
- **No `canonizesRigidResidue_or_flags`** (P4 capstone).
- **Carried model obligations:** `ForcingModel.bridge` (Layer B, empirical/cited), `RecoversRowspace` (Layer-C
  generation), `gForce`'s `encodeFreeFast` realization; and `hSmallAutThin` (a hypothesis on the Route-C symmetry
  seals, `CascadeAffine.lean:1320`, reached via W1 — NOT the descent residue).
- The `RRU` reachability apparatus is retired; the surviving seam is `Phase2.Solver`/`Sound`/`IsoInvariant`.

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

- **✅ P1 — extraction-soundness — LANDED 2026-07-23 (`ChainDescent/ForcingCircuits.lean`, Mathlib-only standalone,
  axiom-clean).** Pure F₂, no graph model. `Forced H S j` = unit-propagation closure `cl_up` over constraint rows
  `H : Finset (ι → ZMod 2)`. **`forced_certificate`:** everything forced is backed by a genuine row-space codeword
  — `Forced H S j ⟹ j ∈ S ∨ ∃ c ∈ rowspace H, c j ≠ 0 ∧ support(c) ⊆ insert j S`. ★ This is the **corrected,
  unconditional** form of the prototype's minimality fix (§11.4a #2): the naive `e_W ∈ rowspace` is *unsound*
  because `cl_up ≠ cl_lin`, so we extract the **actual codeword `c`** (not the indicator `e_W`) and no minimality
  bookkeeping is needed. Proof = induction on the forcing derivation (base row + F₂-cancellation of the
  intermediate certificates). Corollaries `certificate_of_forced_notMem` / `certificate_mem_rowspace`
  (`cl_up ⊆ cl_lin` at the witness level — what P3's Smith/rank solve consumes). ⚠ The **generation** direction
  (certificates *span* `rowspace(H)`) is the P2 model bridge, carried (needs rows = minimal circuits, a graph
  property). This matches P1's name: *extraction-**soundness***.
- **✅ P2 — forcing-model bridge — LANDED 2026-07-23 (`ChainDescent/ForcingModel.lean`, axiom-clean).** Links the
  **graph** side (1-WL refinement forcing over `Fin n`) to the **pure-F₂** side (`ForcingCircuits.Forced`/`rowspace`
  over abstract vars `ι`). Empirical content = **Layer B** (`IR §11.4a`): WL-forcing on the real multipede/CFI graph
  = unit-propagation on the recovered matrix `H`, *exactly* (50/50 validated, mechanism-verified; asymptotics cited
  Neuen–Schweitzer) — a **gadget-model** property, so **carried** as the hypothesis `ForcingModel.bridge : gForce S
  j ↔ Forced H S j` (where it fails = non-linear rigid residue; `gForce`'s realization by `encodeFreeFast` is the
  deferred wiring). **Proved:** `recoverable_of_model` / `forcing_certificate_of_model` = the **transport**
  (graph-forced ⟹ genuine `rowspace(H)` codeword — P1's `forced_certificate` pulled across the bridge =
  graph-extraction soundness P3-F₂ consumes); `rowspace_eq_span_recoverable` = exact recovery reduces to the carried
  generation `RecoversRowspace` (soundness inclusion from P1; generation = the delicate minimal-circuit Layer-C
  content, carried).
- **P3 — solve + canonical-form iso-invariance (the heavy new build), SCOPED into sub-bricks 2026-07-23.**
  ⚠ **Feasibility gate (Mathlib reality):** Mathlib's Smith (`Submodule.smithNormalForm`) is **`noncomputable` and
  existence-only** (invariant factors over a PID — NO executable `U·M·V=D` transforms, NO canonical-form emit), so
  P3 is genuine construction, not a lift. Resolution: compute the key value by an *executable* route (over **F₂ =
  a field** → RREF, canonical + a complete subspace invariant; over the **finite ring** `Z_{2^k}` → executable
  finite-ring Smith), prove correctness against Mathlib's abstract structure theorem (noncomputable is fine *in
  proofs*). Sub-bricks (ordered; dischargeable-now vs carried):
  - **✅ P3-I — the interface/reduction layer — LANDED 2026-07-23 (`ChainDescent/RigidSolverInterface.lean`,
    axiom-clean).** Reduces `compKey`'s obligations to a standard **pointed coloured solver contract**
    (`PtSolver n = AdjMatrix n → Colouring n → Fin n → Option (List Nat)`; `PtIsoInvariant` + `PtSound` = equal
    non-flag forms ⟹ a colour-aut `u↦w`, the iso-reflection). `skOf sol : Force.Key n` wires the solver into
    compKey's non-disc slot (`encodeOpt`: flag→`[]` sentinel = all flagged pairs *tie* = the residue; form→`0::c`).
    `keyEquivariant_skOf` (`KeyEquivariant ⟸ PtIsoInvariant`, immediate) + `solverSeparates_skOf`
    (`SolverSeparates ⟸ PtSound + hemit` no-flag completeness). **★ Detail surfaced by building first:** the
    *pointed* contract keeps the interface thin — `KeyEquivariant` falls straight out of `PtIsoInvariant` with **no
    `lookData`-faithfulness lemma needed at the seam**; the individualization/reflection content defers *into* the
    concrete solver, where it is provable from the construction. `PtSound`/`hemit` are the exact obligations
    P3-Sound/P3-F₂ + R2 must meet.
  - **✅ P3-Sound — soundness is FREE — LANDED 2026-07-23 (`ChainDescent/RigidSolverSound.lean`, axiom-clean).**
    Verify-by-reconstruction (C# B1c/B3) lifted: `ptForm π adj χ v` = the pointed coloured graph *relabelled* by
    π (injective in the triple `(relabelAdj π adj, transportColouring π χ, π v)`); `emitLabel gen` emits `gen`'s
    chosen permutation's `ptForm`. **`ptSound_emitLabel`: `PtSound` holds for ANY `gen`** — soundness needs no
    completeness (extract the actual relabelling, not an indicator). `colAut_of_ptForm_eq` is `r0a_core` off the
    discretizing regime (equal forms ⟹ colour-aut `u↦w`, σ=πw⁻¹πu). `ptIsoInvariant_emitLabel`: `PtIsoInvariant ⟸
    GenEquivariant gen` (the canonical-labelling law `gen (relabel σ ·) = (gen ·).map (·*σ⁻¹)`, via `ptForm_transport`).
    **★ Capstones** `keyEquivariant_compKey_emitLabel` / `nodeResolved_compKey_emitLabel`: the **whole rigid seam
    closes** on just two obligations on the concrete labelling — `GenEquivariant gen` (all the `①`) + `hemit` (no-flag,
    the `②`/completeness; where it flags = the residue). **⟹ the entire `①` content of Algorithm R = a poly, total,
    equivariant canonical labelling `gen`** = graph-canonization of the F₂/ring-linear residue.
  - **P3-F₂ — the concrete poly `gen`** (via the extracted `rowspace(H)` from P1/P2). **✅ CORE LANDED 2026-07-23
    (`ChainDescent/RigidSolveF2.lean`, axiom-clean): the F₂ rigid-SOLVE determinacy** — `dotP` (F₂ pairing),
    `IsRigidF2 H` (trivial kernel = `dim ker 0` = the rigid condition), **`unique_solution_of_rigid`** (a rigid F₂
    system `Hx=b` has *at most one* solution — the unique-solve Gaussian delivers where the unit-prop descent stalls
    at `2^{Θ(n)}`); `dotP_zero_rowspace`/`isRigidF2_rowspace` make rigidity a property of `rowspace(H)` alone
    (basis-independent, composes with P1/P2). ⚠ **Remaining** — wire this unique assignment, under an iso-invariant
    frame, into an equivariant `gen` (`GenEquivariant` + `hemit`); that framing + emit is graph-canonization of the
    linear code and is where the `②`/poly content lives. **▶ SCOPED into four sub-bricks (2026-07-23), reusing the
    EXISTING executable F₂ echelon** (`Kernel.echelon` + `pivInv_echelon`, `KernelGauss.lean`: the RREF algorithm is
    already built and its span-preservation both-ways proved via `PivInv`):
    - **✅ (A) canonical RREF object — LANDED 2026-07-23 (`ChainDescent/RigidRREF.lean`, axiom-clean, in `build.sh`).**
      `echelon` returns pivots in fold-discovery order (a function of the generating *list*); `rrefCanon m rows`
      reorders them to increasing **column order** `0…m-1` (`find?`-scan), a canonical *shape*. `mem_rrefCanon_iff`
      (same pivots — a reorder, no loss) + `pivInv_rrefCanon` (the canonical form **inherits `PivInv`** — reduced
      echelon, row space preserved both ways). `#eval`-tested. The foundation the labelling reads.
    - **✅ (B) canonicity as a subspace invariant — COMPLETE 2026-07-24** (`RigidRREF.lean` §5, axiom-clean):
      **`rrefCanon_eq_of_span_eq`** — two uniform-length row lists with the same row space (mutual `Spans`) have
      **equal canonical RREFs**. Per column, the two `echelon`s pivot at the same `c` (`pivotCols_eq`) and share the
      pivot row there (**`pivotRow_eq`**, (B-rows): `xorRow ρ₁ ρ₂` is in the span and zero at every pivot ⟹ kernel
      triviality). The executable RREF is a canonical form of the *subspace*, independent of the generating list —
      the invariant an iso-invariant `gen` reads once the χ-frame supplies the column order. Sub-DAG:
      - **✅ (B-kernel) kernel triviality — LANDED 2026-07-23** (`RigidRREF.lean` §2, axiom-clean):
        `combo_eq_zero_of_pivots_zero` — a row-space vector `false` at every pivot column is the zero row (the
        pivot rows are a **transversal / linearly independent**), the workhorse of pivot-row uniqueness. Proof =
        dedup a span element to a **Nodup** XOR of pivot rows (`spans_nodup_combo`, via `combo_perm`) then evaluate
        at a used pivot's column (`xorList_map_single`). ⚠ **KEY FINDING:** `PivInv` alone does **not** pin the
        pivot *columns* — `span{[1,1]}` admits both column 0 and column 1 as valid `PivInv` pivots — so column
        determination needs the **leading-position** property (each pivot row `false` strictly below its pivot),
        which `echelon` satisfies but `PivInv` does not record. That is (B-cols) below, the harder remaining piece.
      - **(B-cols) pivot columns are intrinsic — IN PROGRESS.**
        - **✅ leading-position invariant — LANDED 2026-07-23** (`RigidRREF.lean` §3, axiom-clean):
          `leadInv_echelon` — every pivot row of `echelon rows` is `false` strictly below its pivot column (the
          structural fact `PivInv` lacks). A fresh fold invariant (`LeadInv`/`leadInv_echStep`/`lead_foldl`,
          parallel to `pivInv_echelon`): the new pivot is `false` below its column by `findIdx?` (leftmost true),
          and a *triggered* back-reduction has `c ≥ cp.1` so it never touches below `cp.1`.
        - **✅ reconstruction + column determination — LANDED 2026-07-23** (`RigidRREF.lean` §4, axiom-clean):
          `reconstruction` (`w ∈ span ⟹ w = combo of the pivot rows at the columns where `w` is set`, via kernel
          triviality on `xorRow w (recon w)`) ⟹ `pivotCol_isLeading` / `leading_isPivotCol` (pivot columns = the
          space's **leading positions**, both directions) ⟹ **`pivotCols_eq`**: two reduced-echelon systems with the
          same row space have the **same pivot columns**. (B-cols) is complete.
      - **✅ (B-rows) pivot rows are intrinsic** — `pivotRow_eq` (direct from (B-kernel)); **✅ (B5)** assembled into
        `rrefCanon_eq_of_span_eq`. **(B) is closed.**
    - **✅ (C) the χ-frame — LANDED 2026-07-24** (`ChainDescent/RigidFrame.lean`, axiom-clean). **★ Design finding:**
      RREF is **NOT column-equivariant** — permuting columns changes which is leftmost, hence the pivot set
      (`span{[1,1]}` pivots at position 0 either way, but that's a *different actual column*). So the order must come
      from the iso-invariant **χ-rank** (`Colouring.vertexRank`/`rankInv`) — the `leafMatrix` pattern: reading a
      vertex-indexed object in rank order is *literally* σ-invariant because `rankInv` transports
      (`RigidSeal.rankInv_transport`). `frameRow`/`frameSys` read a row / system in χ-rank order;
      `frameRow_transport`/`frameSys_transport` prove they are literally σ-invariant when the row transports as
      `r ↦ r ∘ σ⁻¹` (`transportRow`); **`framedRREF_transport`** ⟹ the χ-framed `rrefCanon` is σ-invariant. This
      **reduces `gen`'s `GenEquivariant` to the extraction transporting as `H ↦ H.map (transportRow σ)`** (a
      P2/extraction property, carried) — the RREF/frame layer owes no further equivariance. `framedRREF_span_invariant`
      (from B) = also a canonical function of the framed code.
    - **✅ (D) read the labelling — LANDED 2026-07-24** (`ChainDescent/RigidGen.lean`, axiom-clean). `genOfRef ref` =
      `rankPerm` of χ **refined by the solve** (`ref adj χ`), when discrete; else flag. **Ignores the pin `v`** — a
      whole-graph canonical labelling suffices, since `ptForm`'s pin component `(π v).val` already separates the
      pinned vertex by its rank. **`rankPerm_transport`** (from `vertexRank_transport`): `rankPerm (transportColouring
      σ χ) = rankPerm χ * σ⁻¹` — *exactly* `GenEquivariant`'s shape ⟹ **`genEquivariant_genOfRef`**: `GenEquivariant
      (genOfRef ref)` ⟸ **`RefEquivariant ref`** (the refinement transports) *alone*. `emit_isSome_genOfRef`: `hemit`
      ⟸ `ref` discrete. **Capstones `keyEquivariant_compKey_genOfRef` / `nodeResolved_compKey_genOfRef`** compose with
      P3-Sound to close the whole `compKey` `①`/firing on `RefEquivariant` + `RefDiscrete`.
      **▶▶ THE (A)–(D) `gen`-REDUCTION CHAIN IS COMPLETE.** The entire rigid **linear** `①` now reduces to exactly
      two carried, per-family facts: (i) **`RefEquivariant ref`** ⟸ (C) `framedRREF_transport` ⟸ the extraction
      transporting as `H ↦ H.map (transportRow σ)` (P2); (ii) **`ref` discrete on the residue** ⟸ the RREF solve
      discretizing the gauge (per-family). The pure-F₂ / RREF / frame / labelling layers owe **nothing** further —
      what remains is the concrete `ref` (wire P2's extraction into `refineByFrame`) and P3-ring.
    - **✅ (C) the χ-frame — LANDED** (`RigidFrame.lean`, full detail in the sub-DAG above): RREF is canonical only
      per column order and NOT column-equivariant, so the order comes from χ-rank (`RigidSeal.rankInv_transport`),
      making the framed system literally σ-invariant (`framedRREF_transport`).
    - **✅ (D) read the labelling — LANDED** (`RigidGen.lean`): `genOfRef ref` = `rankPerm` of the solve-refined
      colouring; `genEquivariant_genOfRef` + capstones close P3-F₂'s `①` via P3-Sound on `RefEquivariant ref` alone.
    - **✅ (steps 1–3) LANDED 2026-07-25 — the concrete `ref` = `refineByFrame`, ROUTE B′ (coordinate-free forcing),
      `ChainDescent/RigidRefine.lean`, axiom-clean, in `build.sh`. ⚠ REFRAMED (de-risk finding — supersedes the
      frame-based spec).** The frame route below has a **discreteness gap**:
      `RigidFrame.framedRREF_transport` carries `(h : Discrete χ)` (via `frameRow_transport` → `rankInv_transport`),
      but `ref` is applied to **non-discrete cell colourings** — and on a non-discrete cell there is provably no
      equivariant column tiebreak (the "no iso-invariant within-cell vertex pick" wall). So the χ-frame **cannot**
      prove the *unconditional* `RefEquivariant` that `RigidGen.genEquivariant_genOfRef` consumes. The doc conflated
      the *solving algorithm* (frame/RREF, `②`) with the *equivariance argument* (`①`).
      **The fix (validated — pure-F₂ probe, mixed system + 4 relabellings + controls, `scratchpad/probe_forced.py`):
      build `ref` over P2's already-built `rowspace`/`Forced`, coordinate-free.** The per-vertex datum is *"is `e_v`
      forced (`e_v ∈ rowspace(H)`), and if so to what value (from the target `b`)"* = P2's
      `certificate_of_forced_notMem` read per vertex. It (i) **transports UNCONDITIONALLY** — `rowspace`/`b`
      transport under the `transportVec σ` linear equiv (span commutes with a linear iso), **no `Discrete χ`, no
      frame**; (ii) **handles your MIXED residue correctly** — when `CellsAreOrbits` is false with only *some* rigid
      decisions, the reader **pins exactly the forced (rigid) coords and leaves the gauge/kernel coords `None` = tie
      preserved = consume's job** (the de-fusion handoff; where forcing misses an actually-rigid coord = bridge
      fails = the non-linear residue) — needs **no uniqueness** (`unique_solution_of_rigid` was too strong: it
      assumes the *whole* system rigid, which the mixed residue violates). **What LANDED (`RigidRefine.lean`):**
      (1) `transportVec σ` (`ZMod 2` analog of `transportRow`, a `LinearMap`) + **`rowspace_transport`**
      (`(rowspace H).map (transportVec σ) = rowspace (H.image (transportVec σ))`, via `Submodule.map_span`) +
      `transportVec_e`/`transportVec_injective`/**`e_mem_rowspace_transport`** (per-vertex forcedness is σ-invariant);
      (2) **`forcedVal H x₀ v`** (`some (x₀ v)` if `e_v ∈ rowspace H`, else `none`) + **`forcedVal_transport`** (a
      vertex-invariant); (3) **`refineByFrame extract adj χ v := 3 * χ v + encOpt (frameRead …)`** + the payoff
      **`refEquivariant_refineByFrame`** (`RefEquivariant`, **UNCONDITIONAL**, on the sole carried obligation
      `RefExtractEquivariant` = the extraction transports) + capstones **`keyEquivariant_compKey_refineByFrame`** (①)
      / **`nodeResolved_compKey_refineByFrame`** (firing, `hext`-free) + `refExtractEquivariant_trivial` (non-vacuity).
      **(D) needed NO edits.** **The frame (C)/`rrefCanon`
      is retained as the executable COMPUTATION of `e_v ∈ rowspace(H)` (the `②`/poly content), NOT the `①` handle.**
    - **✅ (step 4) THE CONCRETE EXTRACTION — `RefExtractEquivariant` DISCHARGED, LANDED 2026-07-25** (`RigidRefine.lean`,
      axiom-clean). `RefExtractEquivariant` needs only that the extraction **transports** (structural); its
      *faithfulness* is separate (carried, below). **Step A (generic, reusable):** `extractOf rowAt wit` (rows =
      `{rowAt adj χ i : i}`) + **`refExtractEquivariant_extractOf`** (`RowAtEquivariant rowAt` + `WitEquivariant wit`
      ⟹ `RefExtractEquivariant`, via a `Finset.image` reindex by σ). **The faithful per-family extraction (CFI =
      `KernelSupply` rails/pats) discharges its `①` obligation HERE.** **Step B (concrete instance):** `rowAdj` (F₂
      adjacency rows) + `witChi` (χ mod 2) ⟹ **`refExtractEquivariant_adj`** (non-vacuous — a real graph invariant).
      **Step C:** **`keyEquivariant_compKey_refineByFrame_adj`** — `compKey`'s `KeyEquivariant` holds for the concrete
      `refineByFrame (extractOf rowAdj witChi)` with **ZERO hypotheses**. ⟹ the rigid-linear `①`/**equivariance**
      machinery is instantiated end-to-end. **The `①`/equivariance side owes nothing further.** ⚠ This is *not* the same
      as "the rigid case is solved" — see the step-5 CORRECTION below: `②`/**discretization** is a separate obligation
      the single-bit reader does NOT meet.
    - **⚠⚠ (step 5) CORRECTED 2026-07-25 — the single-bit reader CANNOT DISCRETIZE; `②` needs the structural (Recover)
      frame.** The `hemit_of_forcedSeparates` REDUCTION (`Discrete (refineByFrame extract adj χ) ⟸ ForcedSeparates`, via
      `encOpt_injective`) and the firing capstone `nodeResolved_compKey_refineByFrame_of_forcedSeparates` are **correct
      lemmas and stay** — but the earlier framing of `ForcedSeparates` as "carried per-family faithfulness / CFI =
      interleaving R6" was **WRONG**. **The real finding (probe-confirmed, `scratchpad/probe_rigid.py`):** `refineByFrame`
      reads **one F₂ bit per vertex** (`forcedVal v = some (x₀ v)`); on a RIGID cell (zero symmetry ⟹ every coord forced,
      no gauge `none`) that is only two values, so by **pigeonhole a colour class with >2 vertices cannot be separated**.
      Rigid CFI = the **multipede** (zero symmetry, the rigid solver's PRIMARY target, regime 2) has exactly such cells,
      so `ref adj χ` is NOT discrete ⟹ `genOfRef` flags ⟹ **`ForcedSeparates` is UNSATISFIABLE there**. It is reader
      *coarseness*, not faithfulness. **The mis-scoping is CONTAINED to the concrete reader** (`forcedVal`/`refineByFrame`
      single-bit); the reduction scaffold (steps 1–2 transport lemmas, (A)–(D), `genOfRef`, P3-Sound, `compKey`) is
      SOUND — it correctly reduces `①` to *"supply a discrete equivariant `ref`."* **The fix = match Recover:** the
      discretizing `ref` reads a RICHER per-vertex value (the vertex's forced coordinate / RREF-column signature —
      probe-confirmed it discretizes) over the **recovered canonical ordered base** (structural, iso-invariant column
      order — NOT χ-rank, which needs `Discrete χ`; NOT coordinate-free F₂, which gives ≤2 classes/cell). This is
      exactly the C# `Recover → canonical ordered base → pin directions → canonForm` path (IR §11 B1a, tested). See
      step 6 below.
    - **✅ (step 6) THE FIX — re-parameterize around a per-vertex canonical reader, LANDED 2026-07-25**
      (`RigidRefine.lean`, axiom-clean). Generalize the reader from the single F₂ bit to an arbitrary
      `read : AdjMatrix n → Colouring n → Fin n → ℕ`, with two clean mirrored obligations: **`ReadEquivariant read`**
      (a vertex-invariant — transports) ⟹ **`refEquivariant_refineBy`** (`①`, reader-agnostic); **`ReadSeparates read
      adj χ`** (separates co-cellular vertices) ⟹ **`discrete_refineBy`** (`②`, via `Nat.pair` injectivity). Capstones
      **`keyEquivariant_compKey_refineBy`** / **`nodeResolved_compKey_refineBy_of_readSeparates`**. ⟹ **the rigid-linear
      seal for the structural reader rests on exactly `{ReadEquivariant, ReadSeparates}`, both discharged by the
      recovered canonical ordered base (carried).** `ReadSeparates` is the honest restatement of `ForcedSeparates`
      ("the ordered base pins every vertex"). The single-bit reader is retained as a *coarse* `ReadEquivariant`
      instance (**`readEquivariant_encOpt_frameRead`** — steps 1–5 supply a transporting reader) that does NOT satisfy
      `ReadSeparates` on rigid cells.
    - **✅ (step 6b) THE CONCRETE STRUCTURAL READER — LANDED 2026-07-25** (`RigidRefine.lean`, axiom-clean). Reads each
      vertex's RREF-column signature (`rrefCanon`, reused) over a **recovered iso-invariant column order** `ord` (a
      `Perm` transporting as `ord' = σ·ord`). **★ THE UNLOCK — no `Discrete χ`:** `frameRowBy ord` / `framedRREFBy_transport`
      generalize `RigidFrame` to an arbitrary order; a *structural* order makes the framed RREF invariant
      **unconditionally** (the χ-rank frame's `Discrete χ` gap came from `rankInv` needing injectivity; a recovered order
      sidesteps it). **`①` (proven):** `readEquivariant_structRead` (`ReadEquivariant (structRead ord Hs)` from the carried
      `OrdEquivariant ord` + `HsEquivariant Hs` + `framedRREFBy_transport`) ⟹ `keyEquivariant_compKey_structRead`. **`②`
      (reduced):** `readSeparates_of_injective` (`ReadSeparates ⟸ structRead injective`) ⟹ firing capstone
      `nodeResolved_compKey_structRead`. ⟹ **the whole rigid-LINEAR seal for the discretizing reader rests on exactly
      THREE carried `Recover` facts:** `OrdEquivariant` + `HsEquivariant` (order/system transport, `①`) and `structRead`
      injective (discretization, `②` = "the recovered ordered base pins every vertex" = full-rank on the rigid residue via
      `IsRigidF2`). **No `Discrete χ`, no coordinate-free coarseness** — this is the reader the rigid multipede actually
      needs. `ord`/`Hs` are the carried Lean `Recover` objects (C#-tested; Lean side = P2/`ForcingModel`). **▶ NEXT:** the
      concrete Lean `Recover` (discharge `OrdEquivariant`/`HsEquivariant`/injectivity per family) — the same object as
      `ForcingModel.bridge`/L4; or `IsRigidF2 ⟹ structRead` injective (rigidity ⟹ full-rank ⟹ distinct columns, via
      `RigidRREF`'s rank toolkit) to shrink the `②` carry.
  - **P3-ring (`Z_{2^k}`/finite-abelian)** — ring-inference (the genuinely open piece, `IR §11.13`) + finite-ring
    Smith + the 2-adic tower solve. The heavy stage; ring-inference carried as an obligation initially.
  - **The iso-invariance mechanism (C# B2, hard-won):** fire the emit at the **iso-invariant root partition**
    (`Recover` is structural — reads cell structure, never labels); one spec throughout (do NOT mix the φ-form with
    a global-lex-min form — broke iso-invariance on Z₃ empirically).
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
(`HandledS`/`NodeResolved`/`selNode`). Ordering, with current state:
**✅ `R0a`** (feeds `answersS_of_handledS`) → **✅ `R0b`** (leafColKey precursor) → **✅ `compKey`** (§9 — the
dischargeable seam; carried object `SolverSeparates` = a solver property) → **✅ `P1`** (`ForcingCircuits`) →
**✅ `P3-I`** (`RigidSolverInterface`, contract reduction) → **✅ `P3-Sound`** (`RigidSolverSound`, soundness free ⟹
`①` = one `gen`) → **✅ `P2`** (`ForcingModel`, graph↔F₂ bridge) → **✅ `P3-F₂` core** (`RigidSolveF2`, solve
determinacy) → **✅ the `gen`-reduction chain (A)–(D)**: **✅ (A)+(B)** `RigidRREF` (canonical RREF, canonical fn of
the subspace) → **✅ (C)** `RigidFrame` (χ-rank frame ⟹ σ-invariant) → **✅ (D)** `RigidGen` (`genOfRef` +
`genEquivariant_genOfRef` + `compKey` capstones ⟹ rigid `①` closes on `RefEquivariant ref`) → **▶ NOW: the concrete
`ref` = `refineByFrame`, ROUTE B′** (coordinate-free forcing over P2's `rowspace`/`Forced` — `RefEquivariant`
unconditional, mixed-cell-correct, no frame; §8.2) → `P3-ring` (`Z_{2^k}`) → `P4`
(capstone `canonizesRigidResidue_or_flags`). **R6(c)** is ✅ discharged for the linear residue by (D)'s
`nodeResolved_compKey_genOfRef` (modulo `ref` discrete). `R2` (per-family) and `R5` (tighten) run in parallel as
residue-shrinkers. The C# `Option2Solver` is the reference throughout (validate Lean claims against its behaviour
before proving).

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

### 9.2 The `ForcingModel.bridge` coupling — this is ALSO the W2 completeness track's last obligation

`ForcingModel.bridge` (P2, Layer B, carried — §10 ledger) is not only the rigid solver's graph↔F₂ recovery obligation;
it is **the F₂/`A_0` instance of the W2 completeness track's `L4`** (`chain-descent-w2-solvability-route.md` §3b +
HANDOFF). The W2 track (the *completeness dual* — "is the rigid gauge forced solvable?") has now built, axiom-clean, the
whole group-theoretic + linear-algebra reduction: a recovered **solvable** gauge reduces to a bounded tower of
per-coordinate **linear** (Smith) solves (`GaugeLayer` L1–L3, `GaugeNonabelian`, `GaugeSolvable`), **modulo exactly one
hypothesis — that `Recover` produces each derived layer as an explicit linear system from the graph.** That hypothesis
is `L4`. **⚠ SCOPE — do NOT flatly equate `L4` with `ForcingModel.bridge`.** The bridge is the **single-layer F₂**
faithfulness (`gForce S j ↔ Forced H S j` over `ZMod 2`); `L4` is the **per-derived-layer** extraction over the tower's
coefficient rings `A_k = Abelianization(derivedSeries G₀ k)`, of which the bridge is the `A_0 = ZMod 2` case (W2 doc
§3b lines 30–32/381–382; and §5a's own caveat "stronger than the empirical F₂ `ForcingModel.bridge`", line 472).
**Consequence for this doc:** discharging `ForcingModel.bridge` (the P2/P3 build) empties the **abelian/F₂** solvable
corner and is genuinely shared with W2 at the **forcing-faithfulness (R-b)** level; the **general** solvable tower
additionally needs the `A_k` (k ≥ 1) layer extraction, so the identity is exact only at F₂ — beyond it `L4` strictly
generalizes the bridge. The two tracks meet at this object *at the F₂ layer*; see the W2 doc's ▶▶ HANDOFF "LOGICAL
STATE" note. **Track them together — but count the `A_k`-layer extraction as W2-only work, not discharged by the F₂ bridge.**

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
| **R6** | interleaving-convergence: `¬Amenable ⟹ exposed `RigidObstructionAt` ⟹ force separates it ⟹ `NodeResolved` ⟹ no reached node is a genuine mutual stall (`selNode_stall_iff`) except at the wall` | **predicate layer BUILT** (`HandledS`/`NodeResolved`/`selNode_stall_iff`/`answersS_of_handledS`/`handledS_of_handled`, all axiom-clean). **(c) force-separates-every-exposed-rigid-pair** — **✅ DISCHARGED for the LINEAR residue 2026-07-24** by the (D) firing capstone `RigidGen.nodeResolved_compKey_genOfRef` (`NodeResolved` on a rigid cell ⟸ `ref` discrete + rigidity, soundness free). What remains of (c) is exactly `ref` discretizing on the residue (the solve, carried per-family) and the non-linear residue (the wall). Deepest ③/totality claim. |
| **P1** | extraction-soundness: forced ⟹ backed by a `rowspace(H)` codeword (support ⊆ `insert j S`) | **✅ LANDED 2026-07-23, axiom-clean** (`ForcingCircuits.lean`, Mathlib-only standalone) — `Forced`/`cl_up` + `forced_certificate` (unconditional; the codeword not the indicator ⟹ no minimality needed) + `certificate_of_forced_notMem`/`certificate_mem_rowspace` |
| **P2** | forcing-model bridge (graph 1-WL forcing ↔ F₂ `Forced H`); transport P1→graph; exact recovery | **✅ LANDED 2026-07-23, axiom-clean** (`ForcingModel.lean`) — `ForcingModel.bridge` (Layer B, carried) + `recoverable_of_model` (transport) + `rowspace_eq_span_recoverable` (recovery mod carried `RecoversRowspace`) |
| **P3-I** | interface: reduce `compKey`'s `KeyEquivariant`/`SolverSeparates` to the pointed solver contract `PtSolver`/`PtIsoInvariant`/`PtSound` (+ `hemit` no-flag) | **✅ LANDED 2026-07-23, axiom-clean** (`RigidSolverInterface.lean`) — `skOf` + `keyEquivariant_skOf` + `solverSeparates_skOf` |
| **P3-Sound** | soundness is FREE (relabelling-emit) + `①` reduces to `GenEquivariant gen` | **✅ LANDED 2026-07-23, axiom-clean** (`RigidSolverSound.lean`) — `ptForm`/`colAut_of_ptForm_eq`/`emitLabel`/`ptSound_emitLabel`/`ptIsoInvariant_emitLabel` + capstones `keyEquivariant_compKey_emitLabel`/`nodeResolved_compKey_emitLabel` |
| **P3-F₂** | concrete poly `gen` over `rowspace(H)` ⟹ `GenEquivariant` + total (`hemit`) | **core ✅ LANDED 2026-07-23** (`RigidSolveF2.lean`) — the rigid-solve determinacy `unique_solution_of_rigid` (+ `IsRigidF2`/`dotP`/`dotP_zero_rowspace`). **`gen` scoped into (A)–(D), §8.2.** **✅ (A) canonical RREF + ✅ (B) RREF-CANONICITY LANDED** (`RigidRREF.lean`, axiom-clean): `rrefCanon`/`pivInv_rrefCanon` (A) + **`rrefCanon_eq_of_span_eq`** (B — same row space ⟹ equal canonical RREF: kernel triviality + leading-position + `reconstruction` ⟹ `pivotCols_eq`/`pivotRow_eq`). **✅ (C) χ-FRAME + ✅ (D) READ-LABELLING LANDED** (`RigidFrame.lean` `framedRREF_transport` + `RigidGen.lean` `genEquivariant_genOfRef`/capstones `keyEquivariant_compKey_genOfRef`/`nodeResolved_compKey_genOfRef`). **▶ (A)–(D) CHAIN COMPLETE.** **✅ concrete `ref` = `refineByFrame` LANDED 2026-07-25, ROUTE B′** (`RigidRefine.lean`, axiom-clean): coordinate-free forcing over P2's `rowspace` (`rowspace_transport`/`forcedVal`/`forcedVal_transport`) ⟹ **`refEquivariant_refineByFrame`** (`RefEquivariant` **UNCONDITIONAL**, no `Discrete χ`, no frame — the χ-frame route had a discreteness gap) + capstones `keyEquivariant_compKey_refineByFrame`/`nodeResolved_compKey_refineByFrame`. The rigid linear `①`/firing now closes on the SINGLE carried `RefExtractEquivariant` (the extraction transports), handles MIXED cells (forced coords pinned, gauge coords tied), needs NO uniqueness. **✅ `RefExtractEquivariant` DISCHARGED (step 4, `RigidRefine.lean`): `refExtractEquivariant_extractOf` (any equivariant local extraction transports — the faithful CFI extraction plugs in here) + concrete `refExtractEquivariant_adj` ⟹ `keyEquivariant_compKey_refineByFrame_adj` = `compKey`'s `KeyEquivariant` with ZERO hypotheses. The `①`/EQUIVARIANCE side owes NOTHING.** **✅ `②` REDUCTION lemma (step 5): `hemit_of_forcedSeparates` + firing capstone (correct, retained).** ⚠⚠ **BUT single-bit `refineByFrame` CANNOT DISCRETIZE (2026-07-25 correction): one F₂ bit ⟹ ≤2 classes/cell ⟹ `ForcedSeparates` UNSATISFIABLE on rigid multipedes (>2-vertex cells, the PRIMARY target). Mis-scoping CONTAINED to the concrete reader; scaffold sound.** **✅ FIX LANDED (steps 6+6b): the discretizing structural reader `structRead` (RREF-column over a recovered iso-invariant order) — `readEquivariant_structRead`/`keyEquivariant_compKey_structRead` (`①`, no `Discrete χ`, via `framedRREFBy_transport`) + `readSeparates_of_injective`/`nodeResolved_compKey_structRead` (`②`). Rigid-linear seal for the discretizing reader now rests on exactly 3 carried `Recover` facts: `{OrdEquivariant, HsEquivariant, structRead-injective}`.** Remaining: discharge those 3 (`IsRigidF2 ⟹ structRead` inj / Lean `Recover`); P3-ring |
| **P3-ring** | `Z_{2^k}`/finite-abelian: ring-inference + finite-ring Smith + 2-adic tower | **not built** — heavy; ring-inference carried (`IR §11.13`). ⚠ Mathlib Smith = noncomputable/existence-only |
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
