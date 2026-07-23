# Chain descent — the deepen supply (`C3b`, the base-symmetry constructor)

> **What this doc is.** The single self-contained home for `deepenSupply` (the `DeepenAnchor` /
> `ReplayDeepening` port of the C# `HarvestTwists`). It grew its own thread — seven Lean files plus
> scattered `remaining-work.md` §1C and topic-memory sections — so this collects the **grounding** (what it
> is, why it exists, what is proved) and the **future work** (the one open crux and its decomposition) in
> one place. Authoritative for deepen; when it disagrees with an older scattered note, this wins.
>
> **Related docs:** `chain-descent-remaining-work.md` §1C (the live tracker), the topic memory
> `[[project-c3-kernel-supply-2026-07-19]]`, the `kernelSupply` staging analog (`KernelRef`/`KernelTransport`)
> which deepen mirrors exactly, and — the **mirror-facing companion** for the RIGID side that consume hands off to
> — [`chain-descent-rigid-seal.md`](./chain-descent-rigid-seal.md) (Algorithm R: the complete rigid-seal working
> doc — the handoff, the solver to certify, the P1–P4 Lean build, the wall).

---

## ▶ STATUS (2026-07-22)

> **UPDATE 2026-07-22 — Layer-1 core + the BRIDGE REDUCTION + the BRANCH-CELL HALF all LANDED axiom-clean**
> (`DeepenAmenable.lean`; full `build.sh` green). Reading order: this STATUS → **§2.1 (why deepen not the
> already-closed index-free `deepMatchSupply` — the poly/quasipoly division + the `viaSpielman` sub-exp→poly
> payoff, NEW 2026-07-22)** → §7 ledger → §8 inventory → §9.1.1 (reduction) → §9.1.2 (route ledger for the crux).
>
> - **Landed this session** (all `[propext, Classical.choice, Quot.sound]`): `b1` (`chooseIdK_mem`); `b2`
>   (**`joint`** — the re-relating induction, now with **anchor-tracking** `σ' a₀ = σ a₀` via the atoms
>   `isColAut_fixes_singleton`/`step_preserves_singleton`/`step_indiv_singleton`); **piece 3**
>   (`twistOf_of_transport_fixing`); the **bridge reduction `hL1 ⟸ hreach`** (`deepenRefInExec_of_reachOnK` +
>   `deepenRefGens_isColAut`/`twistOf_id_off_K`/`refGen_id_off`; off-`K` = `refl`); and the **BRANCH-CELL HALF**
>   `exec_recovers_cell_orbits` (+ `mem_deepenGens_of`). K-coverage VALIDATED (`ScratchKCov`, deleted: exec-orbit
>   == ref-orbit over ALL vertices, incl. `t3`'s size-6 `K∖cell` orbit, exec-6 vs ref-96 IDENTICAL).
> - **`hreach`** (what `hL1` reduces to) = *"the anchor-to-rep twists generate the full `IsColAut`-action on
>   `K`"*. Branch-cell half DONE, and **`[INV]` now discharged from `[DISC]`** (`offCoupled_singleton`, LANDED
>   axiom-clean 2026-07-22 — `exec_recovers_cell_orbits` now carries the single clean domain fact `Discrete
>   d1.col` instead of the ad-hoc `hinv`). **Remaining = (b) the `K∖cell` crux = `ker φ` recovery.**
> - **The crux (b)** — automorphisms that fix the cell but move `K∖cell`; no single exec gen is in `ker φ`, so
>   they must be recovered as WORDS. **Route ε** (native ref⊆exec path-difference induction, reuses `joint`)
>   primary; **Route ζ** (import `RecoverableByDepth`/`CellsAreOrbits`) parallel; **α** flawed (absorbed as ε's
>   base case). Empirically solid (t3 96-vs-6) but the genuinely hard part. The poly **all-or-nothing backup
>   gate** sidesteps it by construction — the fallback ONLY if ε+ζ stall on the same family (per standing steer).
> - **★★★ `①c` CLOSED modulo `{Amenable, AnchorFires}` ONLY — REFERENCE ELIMINATED (2026-07-22, axiom-clean,
>   `deepenSupply_guarded_canonizer_direct`).** The object's flag reads the supply only through `rep` on
>   `forcedSet ⊆ branches`, so `StallEquivariant` needs only that deepen's **branch-orbit relation transports** —
>   and it does, because deepen's branch orbits EQUAL the `IsColAut`-orbits (`deepen_branch_orbit_iff_aut`), which
>   conjugate under `σ`. Fed to `Residue.guarded_mixed_canonizer` via the new generic
>   `stallEquivariant_forceThenConsume_of_branchOrbitTransport`. **The whole reference apparatus —
>   `deepenRefSupply`, R1 (`SameOrbits`), R2 (`twistOf`-transport) — is DISCARDED.** (Both the `K∖cell` crux and
>   the R2 `twistOf` order-dependence subtlety are now moot; `SameOrbitsOnBranches`/`deepenRefSupply` kept only
>   for provenance.)
> - **NEXT for a fresh reader:** `①c` is closed modulo two **domain facts** only: **`Amenable`** (Layer 2 → the
>   shared rigid-obstruction wall `hSmallAutThin`, §5) and **`AnchorFires`** (per-anchor: `deepen` succeeds +
>   gate + `Discrete` leaf `[DISC]` — a firing lemma). No mechanical obligations remain.

## ▶ STATUS (2026-07-21)

- **The executable is landed and measured** (`DeepenSupply.lean`, in `build.sh`): `deepenSupply` solves
  the `mp7` base symmetry end-to-end (branch cell 28 and foot cell 14 each collapse to a single orbit;
  C# cross-check `|Aut| = 1344 = 8 × 168`). It is **not yet in `Publication.canonForm?`'s record object**
  — it enters once its `①c` proof closes, exactly how `kernelSupply` was staged.
- **`①c` reduces to `SameOrbits deepenRefSupply deepenSupply`** (against an equivariant all-picks
  reference), = **R1** (the hard half) **+ R2** (reference equivariance, mechanical). The easy half of
  `SameOrbits` and the R2 algebraic core (`twistOf_transport`) are landed.
- **R1 FACTORS:** `R1 ⟸ (Amenable ⟹ R1) + Amenable`. `Amenable` = every deepening level individualizes a
  single-orbit cell.
  - **`(G1 ∧ G2) → ①c` is FORMALIZED** (gate-conditional capstones + the G2 attribution) — the open links
    are explicit Lean hypotheses, not prose.
  - **Layer 1 (`Amenable ⟹ R1`) = a mechanical re-relating induction.** All its bricks are **landed
    axiom-clean** — engine (`step_rerelate`), monotonicity (piece 1: `step_refines`,
    `isColAut_parent_of_refines`), cell transport (`cidCell_*`), the `Amenable`-transfer (piece 2a:
    `cellSingleOrbit_transport`), and the accumulator lemma (piece 2b-b0: `deepen_acc`). The remaining core
    is the joint fuel induction body (piece 2b, which composes those bricks) plus pieces 3 (twistOf verifies)
    and 4 (K-coverage).
  - **Layer 2 (`Amenable` holds on the residue) = the WL-obstruction classification**, which **imports no
    new conjecture** — it is gated on the project's existing single shared wall (claim #2 / `hSmallAutThin`).
- **The one genuinely-open thing touching `①c`** is finishing Layer 1's induction (`hL1`) + R2. `G1` (the
  shared wall) is **not** needed for `①c` — only for totality. A poly **all-or-nothing backup gate** is
  designed and held in reserve.

**Frontier (one live task):** finish the Layer-1 joint fuel induction `hL1 : Amenable → DeepenRefInExec`
(piece 2b), then pieces 3+4, then the mechanical R2 assembly. All bricks are in `DeepenAmenable.lean`.

---

## 0. What deepen is, and why it exists (the `C3b` gap)

The propagation supplies (`deckSupply`, `deck2Supply`) work by **seeding vertices and chasing forced
consequences**. On the `C3` witness `mp7` (the Fano multipede, `n = 42`) that is defeated *in principle*:
the incidence structure has **girth 6**, so a seed forces exactly one vertex and nothing chains, at any
number of seeds. `kernelSupply` then certifies the whole **F₂ gauge** (the `[7,3,4]` simplex code), but
the gauge is not all there is — the **base** symmetry (the `Z₇` translation of the Fano plane, in fact all
of `PGL(3,2)`) survives, and no gauge-shaped or propagation-shaped constructor reaches it.

`deepenSupply` is the **base-symmetry constructor**. It is a faithful port of the C# `ChainDescent.cs`
`HarvestTwists`, which is measured to solve `mp7` end-to-end on a **single path** (4 nodes, 1 leaf).

---

## 1. The mechanism — deepen / replay / twist / verify

Stop propagating; instead **replay a deepening and compare refinement footprints** (`DeepenSupply.lean`):

1. **`deepen` (`DeepenAnchor`)** — individualize the anchor `r₁` of the branch cell and refine; then
   repeatedly individualize the **lowest-id non-singleton sub-cell of the footprint** (the diff against the
   node colouring, held fixed as parent) until all-singletons, recording the sequence of chosen cell ids.
   One sub-cell, one vertex per level — a **single path**, never a branch over representatives.
2. **`replay` (`ReplayDeepening`)** — for each other representative `rⱼ`, individualize `rⱼ` and follow the
   SAME recorded id sequence. If `rⱼ` cannot follow it, it yields no candidate (sound — the reps stay
   separate).
3. **`twist` (`twistOf`)** — on the coupled component `K` (the parent cells that split), match `r₁`'s
   colour-`c` vertex to `rⱼ`'s colour-`c` vertex, identity off `K`. Materialised as a `Vector` (trap #1).
4. **verify** — `permOf` gates bijectivity and `Consume.verified` re-checks `IsColAut`. The construction
   only *proposes*; verification disposes. Junk costs firing, never `①`.

**Why it reaches what deck/deck2 cannot:** it does not propagate — girth 6 kills chaining at any number of
seeds, but replaying a deepening does not chain, it **compares**.

### 1.1 All anchors are required (the `G8` falsifier)

The anchor is a within-cell pick and each level breaks ties by vertex index, so a single-anchor supply runs
a *different computation* under relabelling. **Measured false** with one anchor: five relabellings of `G8`
give branch-cell orbit profiles `[2,2,2,2,4,4,4,4]` under two and `[1,1,2,2,2,2,2,2]` under two others —
genuinely different partitions ⟹ `①c` FALSE. Quantifying over **all anchors** repairs it (all five then
agree, and the union fires strictly more). So `deepenGens` loops over every anchor. ⚠ `mp7` cannot detect
this — it fires *totally* there; **an equivariance falsifier must be a PARTIALLY-firing witness.**

### 1.2 The all-singletons gate

The twist is a forced bijection only when the coupled component `K` is fully discretized
(`allSingletonsK K χ1`). A non-singleton sub-cell is refinement-indistinguishable, so no iso-invariant
match exists — those are rejected outright.

### 1.3 Performance (traps, measured — prototype `> 1 h` → `~3 min`)

- ★ the twist was a **closure**, re-running `List.contains`/`List.find?` on each of `IsColAut`'s `~2n²`
  applications — cure: materialise as a `Vector` (**trap #1: data, not functions**);
- per-representative refinement recomputed once per (anchor, rⱼ) pair — hoist the `|cell|` `firsts` once;
- `O(n³)` `coupled` computed twice per level and again per pair — compute once per level and thread.

---

## 2. The `①c` obligation and its reduction

`①c` is iso-invariance of the emitted **orbit relation** (the supply's contribution to the canonizer's
equivariance). `deepenSupply` is **not** `GensEquivariant` — its per-level lowest-index pick does not commute
with a relabelling, so its generator *set* changes under `σ`. What is canonical is the **group it
generates** — exactly what `OrbitPrune.SameOrbits` asks for. So `①c` is discharged the `kernelSupply` way:

> **`①c(deepenSupply) ⟸ SameOrbits deepenRefSupply deepenSupply + SupplyEquivariant deepenRefSupply`**
> via `OrbitPrune.guarded_mixed_canonizer_of_sameOrbits` (+ `KeyEquivariant` of the lookahead key).

`deepenRefSupply` (`DeepenRef.lean`) is a **proof-side, exponential** reference: the same
deepen/replay/twist pipeline branching over **every** member of the chosen sub-cell each level
(`deepenAll`/`replayAll`), through the **shared** `twistOf` (extracted so "an exec generator IS a reference
generator" is a `rfl`). It makes no choice, so it is manifestly equivariant.

The reduction splits into:
- **R1** = the reverse `SameOrbits` half: `ref orbits ⊆ exec orbits` (the exponential reference reaches no
  orbit the single canonical pick misses). **The crux.** = the predicate `DeepenRefInExec`.
- **R2** = `SupplyEquivariant deepenRefSupply` (the reference's own transport). **Mechanical.**

The easy half (`exec orbits ⊆ ref orbits`, `wordReach_ref_of_deepen`) is landed, and the R2 algebraic core
(`twistOf_transport` — the twist conjugates under `σ`) is landed.

### 2.1 Why deepen, not the index-free `deepMatchSupply` — the poly/quasipoly division (2026-07-22)

`deepMatchSupply d` (`DeepMatchSupply.lean`, LANDED, sorry-free capstone `deepMatchSupply_guarded_canonizer`)
solves the *same* job a different way: enumerate **every** individualization sequence of length `≤ d` and
colour-match all pairs. Because it makes **no choice** it is **index-free**, so its `①c` (`SupplyEquivariant`)
is **free and already closed** — no `joint`, no `hreach`, no crux. So why deepen at all? They are duals; the
axis is **cost vs. `①c`**:

| | `①c` | firing hypothesis | cost |
|---|---|---|---|
| **`deepMatchSupply d`** | **free** (index-free) | external `CellsAreOrbits` (seal import) + `SeparatesAt d` | `n^{O(d)}` — poly at fixed `d`, **quasipoly at `d = Θ(log n)`, exp at `d = Θ(n)`** |
| **`deepenSupply`** | **hard** (the crux) | **self-certified** (verification gate; `deepenGens_sound`) — needs `Amenable`, not external `CellsAreOrbits` | **single greedy path — poly at ANY depth** |

**Deepen's whole value is the cost column.** A single greedy path individualizes `≤ |K| ≤ n` vertices before
the cell discretizes, so it is polynomial *regardless of separation depth*. `deepMatchSupply` pays `n^{O(d)}`
to hedge against not knowing *which* sequence separates; deepen commits to one (greedy) and pays for that
commitment in `①c`. So `deepMatchSupply` already covers every family deepen does **at bounded `d`** — deepen's
marginal contribution is exactly the **super-constant-depth** regime where `n^{O(d)}` stops being polynomial.

**This is why the WL-dim wall (§5, `cxt-scoping.md`) does not bite deepen — the *cost* side of §5's "not
is-WL-dim-bounded".** For `deepMatchSupply`/`viaSpielman` the target genuinely *is* bounded WL-dim
(`c(X_T)=O(1) ⟺ bounded b(X) ⟺ bounded WL-dim`, `cxt-scoping:59`), because `n^{WL-dim}` must stay poly —
unbounded WL-dim (the linear `0.15n` ceiling, Schneider–Schweitzer) makes it exponential. For deepen,
**`WL-dim < cell-size` is a free construction fact** (individualizing a cell's own vertices discretizes it, so
no cell ever needs more than its own size in individualizations — `WL-dim ≥ cell-size` is vacuous), and a
single path of that length is poly *at any WL-dim up to `0.15n`*. So deepen **relocates the obstruction off
the WL-dim/cost axis onto `Amenable`** (single-orbit per greedy level, §5), which is *orthogonal*:
high-WL-dim + `Amenable` ⟹ deepen poly-complete exactly where `deepMatchSupply` goes exponential. That is
deepen's reason to exist, and it is precisely the A2 wall the seal has been stalled on.

**Concrete payoff — `viaSpielman` sub-exp → poly.** `reachesRigidOrCameron_viaSpielman`
(`PublicTheoremIndex:1128`) carries `SeparatesAtBoundedBase S (Õ(n^{1/3}))` and today fires `deepMatchSupply`
at **sub-exponential** `n^{O(n^{1/3})}` (`SealDepthBridge.cellIsOrbit_pathCol_of_spielman`). Deepen needs only
that *some* path separates (its own greedy one, poly-length — it does **not** need the `Õ(n^{1/3})` *bound*),
so **if the `①c` crux closes and ζ imports the separation, the claw-bounded-SRG floor upgrades sub-exp → poly**
(conditional on `Amenable` there; the `schemeAdj S`→realizing-graph step is the `RouteCTransport` hop, and
Spielman is claw-bounded-only — the `Θ(√n)`-base Neumaier families exit via Cameron). This is the sharpest
single motivation for closing the crux.

---

## 3. The reframe — what the obligation actually is (grounding; read before any R1 work)

Three corrections settled in discussion (2026-07-21), each retracting an earlier over-statement:

1. **The obligation is symmetry-CONSUMPTION completeness, NOT WL / I-R completeness.** By the force/consume
   division — *decision removes output states → force; decision does not limit output → consume* — two
   colour-equal but **non-automorphic** vertices are a *force* decision (choosing between them changes the
   canonical form). So the reference's **verified** twists only ever connect genuinely-automorphic vertices
   ⟹ **R1 needs no external single-orbit hypothesis; the verification gate (`twistOf_isColAut`) supplies
   it.** CFI-hardness *splits away* from deepen: the gauge is `kernelSupply`'s, the WL-merge is force's.
   deepen is never asked to distinguish non-isomorphic things.
2. **§L.4 is a FORCE-resolver result, an analogy only.** The linear-oracle's "forced candidate fires iff
   branches isomorphic" (`chain-descent-linear-oracle.md` §L.4) is about the force side; it is *not* a proof
   that deepen (a consume resolver) cannot close.
3. **"Miyazaki defeats it" was RETRACTED.** deepen takes a **single path per anchor**, not the I-R search
   tree, so tree-exponentiality doesn't touch it; and canonicalization *cost* ≠ consume *completeness*.

**1-WL never over-splits** (same-orbit vertices are always colour-equal); it only over-merges, and
over-merge is force's to separate. That is why the residue deepen must handle is genuine symmetry.

---

## 4. The `Amenable` factoring

R1's crux is not monolithic. `R1 ⟸ (Amenable ⟹ R1) + Amenable`, where

> **`Amenable adj χ`** := at every level of the canonical deepening, the cell `chooseIdK` selects is a
> single orbit of the pointwise-stabilizer of the vertices individualized so far
> (`DeepenAmenable.AmenablePath` / `Amenable`).

⚠ **Firing does NOT imply `Amenable`** — a WL-merged multi-orbit cell can still discretize (a nested force
decision the greedy pick resolves arbitrarily). So `Amenable` is a genuine domain hypothesis; a `¬Amenable`
*firing* graph is the still-missing "fires-but-strictly-incomplete" (part-III) witness.

- **LAYER 1 — `Amenable ⟹ R1`** — MECHANICAL, the **re-relating induction**:
  > the deepen-from-`a` and replay-from-`b` descents (`a ~ b` via `σ ∈ Aut`) stay related by an automorphism
  > `σₖ` with `ψ_b^(k) = transportColouring σₖ ψ_a^(k)`.
  Per level: same id (`chooseIdK_transport`); the single-orbit cell (`Amenable`) supplies `τ ∈ Stab(ψ_b)`
  with `τ(σₖ u_a) = u_b` (absorbing the lowest-index mismatch); `σₖ₊₁ = τσₖ` re-establishes the invariant
  (`step_rerelate`). At discreteness the leaves are `σ`-related ⟹ `twistOf`'s colour-match *is* `σ` on all
  `K` ⟹ the exec twist verifies ⟹ direct `WordReach`.
- **LAYER 2 — `Amenable` holds on consume's residue** — see §5.

---

## 5. Layer 2 = the WL-obstruction classification (imports no new conjecture)

The question is **not** "is WL-dimension bounded" (unbounded WL-dim exists — CFI — and is irrelevant; the
*cost* side of this — why a single greedy path is poly at any WL-dim — is **§2.1**). It is
"**every `Amenable`-obstruction is a known WL-obstruction type with a handler.**"

> **`Amenable`-violation ⟺ a RIGID (non-symmetric) WL-obstruction in a cell deepen visits.** A WL-stable
> cell fails single-orbit exactly when it WL-merges non-automorphic vertices; symmetric merges give a single
> orbit (no obstruction).

The project already classifies rigid obstructions (EOL `chain-descent-exhaustive-obstruction.md:998`; the
§11.14 2×2 `chain-descent-ir-blindspot-solver.md:1538`):

| | linear | non-linear |
|---|---|---|
| **symmetry** | Phase-1 linear oracle | Cameron / excluded by rigidity |
| **rigid** | multipede / `Z_{2^k}` → **rigid solver ✓ (built)** | **the wall** (open, no witness) |

So the two handlers of `Amenable`-violations are the **rigid solver** (rigid-linear obstructions — built,
`EnableRigidSolver` on, poly-complete modulo the single open `hSmallAutThin` wall) and **the wall**
(rigid-non-linear — the project's standing open frontier = claim #3, no constructible witness).

**⟹ Deepen's completeness = exactly the project's rigid-obstruction-coverage frontier.** It imports no new
instance of the wall — it shares the one boundary (claim #2, "every rigid obstruction is linear over an
abelian ring", `ir-blindspot-solver.md:1068`) that the rigid solver, the linear oracle, and the wall program
are all gated on. Deepen is complete on the **Schurian (pure-symmetry) residue**; on rigid cells it soundly
emit-nothings (verification gate) and hands off. Connect to landed CFI infra to discharge per-family:
`theorem_1_HOR_cfi_oddDeg` (`CFI.lean:3179`, axiom-free CFI ⇒ cascade-at-base-depth), `cfiFlipAut` (the
`Z₂^β` gauge).

**⚠ The one deepen-specific new sub-question (a totality/T-gap, not a new wall):** the interleaving must
deliver Schurian cells to consume — a mixed/**fusion** cell (symmetry over a deeper rigid obstruction, cf.
Chang-A) is where `Amenable`/`①c` could break. Per the framing, consume's residue completeness rests on the
§11.11 consume-schedule + verify-by-reconstruction iso-invariance, and does **not** rest on no-rigid-Cameron.

---

## 6. The `(G1 ∧ G2) → ①c` formalization (`DeepenAmenable.lean §2–3`)

`①c` is discharged in the project's **gate-conditional** style, with the open links as explicit hypotheses:

- **G2, reframed as ATTRIBUTION not avoidance** (`rigidObstruction_of_not_cellSingleOrbit`): a
  `CellSingleOrbit` failure *is* a `RigidObstructionAt` (a same-colour non-automorphic pair — de Morgan). So
  we do not (yet) prove the path avoids rigid cells; we prove any `①c` failure **attributes to the rigid
  side** at this stage. Proving avoidance is a *final* objective.
- **Capstones:**
  - `deepenSupply_guarded_canonizer_of` : `(R1 ∧ R2) → ①c` — mirrors
    `KernelTransport.kernelSupply_guarded_canonizer` via `guarded_mixed_canonizer_of_sameOrbits` +
    `sameOrbits_of_core`.
  - `deepenSupply_canonizer_of_amenable` : `(Amenable ∧ L1 ∧ R2) → ①c` — factors R1 through the domain
    hypothesis.
- **G1 (rigid ⟹ F_k, the shared wall) is NOT a hypothesis of either capstone.** `①c` needs only `Amenable`;
  G1 lives purely at the **totality** layer (it certifies the rigid cells deepen defers on are the rigid
  solver's, so the whole canonizer stays total).

---

## 7. The gap ledger (provability status)

**▶ SUPERSEDED 2026-07-22 — the reference (R1/R2) is ELIMINATED (§2b″).** `①c` closes REFERENCE-FREE modulo
`{Amenable, AnchorFires}` only. The table below is updated; the L0/R1/R2 rows are retired to provenance.

| Link | Statement | Status |
|---|---|---|
| **①c** | `{Amenable, AnchorFires} → ①c` (reference-free) | **PROVED** (`deepenSupply_guarded_canonizer_direct`) — via deepen-branch-orbit = `IsColAut`-orbit, transports; no `deepenRefSupply`, no R1, no R2 |
| **AnchorFires** | per-anchor: `deepen` succeeds + gate + `Discrete` leaf | **domain fact** — a `deepen`-discretizes lemma (firing-completeness, NOT a wall); undischarged |
| **L2 / G2** | `¬Amenable → RigidObstructionAt` (attribution) | **PROVED** (`rigidObstruction_of_not_cellSingleOrbit`) |
| **rigid handoff** | `RigidObstructionAt → ¬CellIsOrbit` (deepen defers SOUNDLY) | **PROVED** (`rigidObstruction_imp_not_cellIsOrbit`) — deepen never mishandles a rigid pair; it is the SAME obstruction type the rigid solver / §11.14 own |
| **G1 / force-sep** | `RigidObstructionAt → CellResolved`'s force branch (key injective on branches) | the **shared wall** (`hSmallAutThin`) — totality only, NOT `①c` |
| **exposed-rigid** | `¬AmenablePath → ∃ RigidObstructionAt` (a consume-stall surfaces a concrete rigid node) | **PROVED** (`not_amenablePath_imp_rigidObstruction`) — the honest handoff: a stall never dead-ends, it exposes a force-actionable rigid pair (possibly DEEPER than the compared pair, which may itself be automorphic = fusion) |
| **fusion** | deep-level `Amenable` obstruction peeled before consume sees the cell | **totality scheduling** (the interleaving): stall → exposed-rigid → force distinguishes → re-expose symmetry → retry → fixpoint. `Amenable`-on-residue holds because force peels every exposed node first |
| **force-complete** | force distinguishes each *exposed* non-automorphic pair | the **shared wall** `hSmallAutThin`, now LOCALIZED to concrete exposed pairs (not a global `Amenable` assumption) |
| ~~L0~~ ~~R1~~ ~~R2~~ | `(R1∧R2)→①c` / `Amenable→R1` / `SupplyEquivariant deepenRefSupply` | **RETIRED** (reference eliminated); `deepenRefSupply` route kept for provenance only |

Everything conjectural lives in **G1** (the shared wall, covered whenever anyone covers it) + the **fusion
scheduling** (a totality obligation). `①c` itself is prose-free modulo the two domain facts `{Amenable,
AnchorFires}`; the rigid **handoff is sound** (deepen defers, never mishandles), so deepen introduces **no new
obstruction** — only the shared wall + scheduling remain.

---

## 8. Lean file map + landed-theorem inventory (all axiom-clean, in `build.sh`)

- **`DeepenSupply.lean`** — the executable. `classOf` · `coupled` · `allSingletonsK` · `chooseIdK` · `step`
  · `deepen` · `replay` · `twistOf` · **`twistOf_isColAut`** (every emitted twist is verified) · `deepenGens`
  · `deepenSupply`.
- **`DeepenTransport.lean`** (part I) — every pipeline stage transports except the pick. `transport_apply(')`
  · `mem_classOf_*` · `classOf_perm_transport` · `classOf_length_transport` · `mem_coupled_transport` ·
  `allSingletonsK_transport` · **`chooseIdK_transport`** (★ the chosen id is an INVARIANT `Nat`) ·
  **`step_transport`** (individualize+refine commutes with σ).
- **`DeepenCrux.lean`** (part II) — soundness + named predicates. **`deepenGens_isColAut`** (every gen is a
  genuine colour-automorphism) · **`deepenGens_sound`** (emitted ⊆ true orbit relation) · `GateAt` ·
  `DeepenGateInvariant` · `DeepenForcedMatch` (the earlier truth-framed predicates, superseded by `Amenable`).
- **`DeepenRef.lean`** (part III) — the all-picks reference + easy inclusion. `deepenAll` · `replayAll` ·
  **`deepenRefGens`** · `deepenRefSupply` · `deepen_mem_deepenAll` · `replay_mem_replayAll` ·
  `deepenGens_subset_ref` · `wordReach_mono` · `verified_deepen_subset_ref` · **`wordReach_ref_of_deepen`**
  (the easy `SameOrbits` half).
- **`DeepenRefTransport.lean`** (R2 core) — `imgFun` · `vget_ofFn` · `twistOf_eq_imgFun` · `contains_map_apply`
  · `imgFun_transport` · **`twistOf_transport`** (the twist conjugates under σ).
- **`DeepenR1.lean`** (part V) — R1 reduced. **`DeepenRefInExec`** · `wordReach_deepen_of_ref` ·
  **`sameOrbits_of_core`** (`DeepenRefInExec → SameOrbits`) · `refInExec_of_mem_deepenGens`.
- **`DeepenAmenable.lean`** (part VI) — Layer-1 machinery + the `①c` capstones.
  - *engine:* `transportColouring_comp` · `step_aut` · `step_isColAut` · **`step_rerelate`** (the
    invariant-maintenance step).
  - *cell transport:* `cidCell` · `mem_cidCell_iff` · `cidCell_nodup` · `mem_cidCell_transport` ·
    `cidCell_perm_transport` · `mem_cidCell_transport_apply` · `cidCell_length_transport`.
  - *piece 1 (monotonicity):* `indivOne_refines` · **`step_refines`** · `isColAut_parent_of_refines`.
  - *predicates + attribution:* `CellSingleOrbit` · `RigidObstructionAt` ·
    **`rigidObstruction_of_not_cellSingleOrbit`** (G2) · `AmenablePath` · `Amenable`.
  - *piece 2a:* **`cellSingleOrbit_transport`** (Amenable transfers a-descent → b-descent).
  - *piece 2b-b0:* **`deepen_acc`** (the accumulator only prefixes the output seq — reduces the joint
    induction to `acc = []`).
  - *piece 2b-b1 (2026-07-22):* **`chooseIdK_mem`** + `foldl_min_mem` (`chooseIdK = some cid ⟹ id-cell ≥ 2`;
    passes replay's guard).
  - *piece 2b-b2 (2026-07-22) — THE CORE:* **`joint`** — the joint re-relating induction. Canonical deepen-a
    & replay-b leaves are `σ_final`-related over the WHOLE colouring, **AND** (anchor-tracking) `σ' a₀ = σ a₀`.
  - *anchor atoms (2026-07-22):* **`isColAut_fixes_singleton`** (an `IsColAut` fixes a singleton-colour vertex)
    · **`step_preserves_singleton`** · **`step_indiv_singleton`** (the individualized vertex is a singleton) —
    the engine of `joint`'s anchor-tracking.
  - *piece 3 (2026-07-22):* **`twistOf_of_transport_fixing`** (`twistOf = some σ'` from the σ-relation + gate
    + `hfix`) + **`gate_unique`** (gate ⟹ each `χ1`-colour globally unique).
  - *bridge reduction (2026-07-22, §9.1.1):* `permOf_apply` · **`twistOf_id_off_K`** (`twistOf` is `id` off `K`)
    · **`deepenRefGens_isColAut`** · **`refGen_id_off`** · **`deepenRefInExec_of_reachOnK`** (★ `hL1 ⟸ hreach`;
    off-`K` = `refl`).
  - *branch-cell half (2026-07-22, §9.1.2):* `transportColouring_isColAut` · **`mem_deepenGens_of`** (forward
    membership in `deepenGens`) · `eq_of_mem_of_length_le_one` · **`offCoupled_singleton`** (★ `[DISC] ⟹
    [INV]`: `Discrete` leaf ⟹ off-coupled = `χ`-singleton) · **`exec_recovers_cell_orbits`** (★ `x,y ∈ cell` +
    automorphism ⟹ `WordReach exec x y`; now carries the single clean domain fact `Discrete d1.col`).
  - *Route ε foundations + crux isolation (2026-07-22, §9.1.2):* `wordReach_of_mem_verified` · `wordReach_symm`
    · `isColAut_mem_branches` · `AnchorFires` (per-anchor firing bundle) · **`exec_recovers_refgen_on_cell`**
    (★ whole-cell coverage for a ref gen) · `ExecRecoversKMinusCell` / `deepenRefInExec_of_cell_and_crux` /
    `ExecReachesAut` (the now-UNNEEDED full-`SameOrbits` route, kept for reference).
  - *★★★ the `K∖cell`-free close (2026-07-22):* in `OrbitPrune` — `rep_congr_at` · **`SameOrbitsOnBranches`** ·
    `narrow_forceThenConsume_congr_branch` · **`guarded_mixed_canonizer_of_sameOrbitsOnBranches`** (weakened
    reduction: branch-only orbit agreement suffices). In `DeepenAmenable` — **`wordReach_deepen_of_ref_on_branch`**
    · **`sameOrbitsOnBranches_of_cell`** · **`deepenSupply_guarded_canonizer_of_cell`** (`①c` modulo
    `{R2, Amenable, AnchorFires}` — the `deepenRefSupply` route, superseded).
  - *rigid handoff (2026-07-22, §2b‴):* **`rigidObstruction_imp_not_cellIsOrbit`** (deepen defers SOUNDLY on a
    rigid pair — `¬CellIsOrbit`; the same obstruction the rigid solver / §11.14 own, no new type) ·
    **`not_amenablePath_imp_rigidObstruction`** (★ a consume-stall EXPOSES a concrete `RigidObstructionAt` — the
    honest handoff: never dead-ends, surfaces a force-actionable rigid node, DEEPER than the compared pair under
    fusion).
  - *★★★★ the REFERENCE-FREE close (2026-07-22) — the intended `①c`:* in `SupplyTransport` —
    **`stallEquivariant_forceThenConsume_of_branchOrbitTransport`** (generic: `StallEquivariant` from branch-orbit
    transport, no `SupplyEquivariant`). In `DeepenAmenable` — **`wordReach_imp_isColAut`** · **`deepen_branch_orbit_iff_aut`**
    (deepen branch-orbits = `IsColAut`-orbits) · **`deepen_branchOrbit_transport`** · **`deepenSupply_guarded_canonizer_direct`**
    (★★★ `①c` modulo `{Amenable, AnchorFires}` ONLY — no reference, no R1/R2).
  - *capstones:* **`deepenSupply_guarded_canonizer_of`** · **`deepenSupply_canonizer_of_amenable`**.

---

## 9. Remaining work

### 9.1 Layer 1 — finish `hL1 : Amenable → DeepenRefInExec` (4 pieces)

> **▶ READER: the current structure is §9.1.1 (the `hL1 ⟸ hreach` reduction, LANDED) + §9.1.2 (the route
> analysis for `hreach`).** This "4 pieces" list is the ORIGINAL Layer-1 plan; pieces 1/2a/2b/3 are all
> LANDED and "piece 4 (K-coverage)" was reframed by the reduction — it is now the branch-cell half
> (LANDED, `exec_recovers_cell_orbits`) + the `K∖cell` crux (OPEN, §9.1.2). Read §9.1.1/§9.1.2 for what's live.

1. ✅ **piece 1 (refinement monotonicity)** — `indivOne_refines`, `step_refines`, `isColAut_parent_of_refines`.
   Keeps the running composite `σ' = τσ` in the parent-stabilizer.
2a. ✅ **piece 2a (`cellSingleOrbit_transport`)** — `Amenable` (about the a-descent) delivers `τ ∈ Stab(cur_b.col)`.
2b. **piece 2b — the joint fuel induction** (the remaining core). Substructure:
   - **b0 ✅ `deepen_acc`** — the accumulator only prefixes the output seq, so the joint induction works at
     `acc = []` (the recursion's `[cid]` accumulator becomes `cid ::` on the seq). ⚠ Its proof needed the
     `deepen` match-reduction recipe now recorded in §11 — reuse it for the body below.
   - **b1 ✅ `chooseIdK_mem`** (2026-07-22, axiom-clean) — `chooseIdK … = some cid ⟹ (cidCell χc cid).length ≥ 2`
     via a `foldl`-min "result is an element" lemma (`foldl_min_mem`), so replay's `mem.length < 2` guard
     passes on the b-side (through `cidCell_length_transport`).
   - **b2 ✅ `joint`** (2026-07-22, axiom-clean `[propext, Classical.choice, Quot.sound]`) — THE joint
     re-relating induction. Invariant `cur_b.col = transportColouring σ' cur_a.col`, `σ' ∈ IsColAut adj χp`,
     + both-sides "refines χp" side-invariants. At `acc = []` (`deepen_acc` handles the rest): base cases =
     `K` empty (contra) / `chooseIdK` none (terminal leaf, `σ' = σ`). Step: `deepen_acc` splits `seq = cid ::
     inner`; replay-b picks head `w_b` of b's cid-cell (nonempty by b1 + `cidCell_length_transport`);
     `cellSingleOrbit_transport` + `Amenable` give `τ ∈ Stab(cur_b.col)` with `τ(σ w_a) = w_b`; `step_rerelate`
     carries the invariant with `σ'' = τσ`; `step_refines`+`isColAut_parent_of_refines` keep `τσ` a
     parent-automorphism; the IH threads `replay inner (step..w_b)`. **Concludes: canonical deepen-a leaf &
     canonical replay-b leaf are `σ_final`-related over the WHOLE colouring** (so K-coverage is built in).
   **All five bricks + b1 composed and landed.**
3. ✅ **piece 3 — twistOf verifies** (2026-07-22, axiom-clean: `twistOf_of_transport_fixing` + `gate_unique`).
   Given the σ-relation `χj = transportColouring σ' χ1`, the all-singletons gate (⟹ each `χ1`-colour GLOBALLY
   unique, so the colour-match is forced), `σ'` fixing off-`K`, and `IsColAut adj χ σ'`, then
   `twistOf adj χ χ1 K (transportColouring σ' χ1) = some σ'` — the exec generator IS `σ'` on `K`. ⚠ Carries
   the hypothesis **`hfix`: `σ'` fixes off-`K`** — empirically vacuous (every measured witness has
   support `= K`); discharging it (or K = support) is a bridge obligation (§9.1.1).
4. ⏳ **piece 4 — K-coverage** (`x ∈ K ∖ branch-cell`). ✅ **VALIDATED 2026-07-22 (`ScratchKCov`, deleted)** —
   the decisive cheap test the prior branch-cell-only probe never ran: exec-orbit partition == ref-orbit
   partition over **all** vertices (not just the cell) on partially-firing witnesses with **nonempty `K∖cell`**:
   `wcyc9` (cell `[1,4,7]`, K∖cell orbits `[0,3,6]`/`[2,5,8]`, EQUAL) and — the strong one — **`t3`
   (exec **6** gens vs ref **96** gens; K∖cell orbits incl. a **size-6** `[1,3,6,8,11,13]`; partition over all
   15 vertices IDENTICAL)**. So the 16×-larger reference generator set enlarges no orbit on OR off the cell.
   **CORRECTION to the mechanism:** R1 is an **orbit** statement (`WordReach exec x (ρ x)`, the word may depend
   on `x`), NOT `ρ ∈ ⟨exec⟩` — a reference gen `ρ` and exec gen `g_{a,b}` are NOT equal pointwise (they differ
   by a `Stab(a)` element), they agree at the orbit level, which is all R1 needs. The earlier "trivial Stab ⟹
   ref twist = exec twist" one-liner was imprecise. **The clean closure:** b2's invariant is already the
   WHOLE-COLOURING equation `cur_b.col = transportColouring σ' cur_a.col`, so the re-relating automorphism is
   whole-graph and `twistOf`'s off-`K`=id support coincides with it (exec-support == full on every witness) —
   **piece 4 is SUBSUMED by the b2 invariant, not a separate wall.** `twistOf` is `id` off `K` (`DeepenSupply`
   :187), so `∀ x` is `refl` for `x ∉ K` — K-coverage is only about `x ∈ K`. ⚠ The missing part-III `¬Amenable`
   witness is still the one untested regime (unrelated to K-coverage).

### 9.1.1 THE REFERENCE-GEN BRIDGE — the plan (2026-07-22)

> **▶ LANDED 2026-07-22 (axiom-clean):** the reduction and its infrastructure — `deepenRefGens_isColAut`,
> `twistOf_id_off_K`, `permOf_apply`, `refGen_id_off`, and **`deepenRefInExec_of_reachOnK`** (the whole
> `hL1 ⟸ on-K` reduction; off-`K` is `refl`). So **`hL1` now reduces to `hreach`** := *each ref gen reaches
> every `x` in its coupled component `K`*. The detailed route analysis for `hreach` is **§9.1.2**.

`joint` (b2) + piece 3 close the **canonical** story: under `Amenable`, the canonical exec twist for a
σ-related pair verifies and equals `σ_final` on `K`. But `hL1` targets `DeepenRefInExec`, which quantifies
over **arbitrary** `deepenRefGens` (all `deepenAll`/`replayAll` paths). This subsection is the plan to bridge
that gap. **THE STRUCTURE — a clean reduction, a clean half, and one crux.**

**The reduction (clean): `hL1 ⟸ ORBIT_K`.**
`DeepenRefInExec := ∀ ρ ∈ deepenRefGens, ∀ x, WordReach (verified deepenSupply) x (ρ x)`.
- Every `ρ ∈ deepenRefGens` is `IsColAut adj χ` (need `deepenRefGens_isColAut`, the ref analog of the landed
  `deepenGens_isColAut` — mechanical) and is **`id` off its `K_ρ`** (`twistOf` :187).
- So for `x ∉ K_ρ`: `ρ x = x`, `WordReach` is `refl` — **nothing to prove off `K`.**
- For `x ∈ K_ρ`: `ρ x ∈ K_ρ` (ρ bijects `K_ρ`) and `ρ x` is in `x`'s `IsColAut`-orbit (witness `ρ`). So it
  suffices to prove:
  > **`ORBIT_K`** — *for `x, y ∈ K` in the same `IsColAut adj χ`-orbit* (`∃ α, IsColAut adj χ α ∧ α x = y`),
  > `WordReach (verified deepenSupply adj χ) x y`. (i.e. **exec recovers the full automorphism orbits on `K`**.)
  Under the discreteness regime the `K_ρ` all coincide with `K = ` union of non-singleton `χ`-cells (a
  function of the node colouring), which is `IsColAut`-invariant — so "the `K`" is well-defined. `ORBIT_K`'s
  `⊆` (exec-orbit ⊆ IsColAut-orbit) is free (exec gens are `IsColAut`); `ORBIT_K` is the `⊇` content.

**The clean half — `ORBIT_K` on the BRANCH CELL.** For `x, y` both in the branch cell, `α x = y`,
`α ∈ IsColAut`: the **exec generator `g_{x,y}` maps `x ↦ y` directly** (`img x = y`, because `x` is
individualized into the anchor colour-slot and `y` into the same slot on the replay — `img anchor = rep`,
independent of the `Stab` difference). So `WordReach exec x y` in ONE step. Needs, all tractable:
  (i) `deepen` **terminates** from the anchor under `Amenable` (reaches `chooseIdK = none` within fuel `n` —
      each level adds a singleton; a small monotonicity lemma);
  (ii) `joint` applied with `σ := α` (via `step_isColAut`, `cur_b = step χ (α x)` transports) ⟹ the replay
       succeeds, so `g_{x,y} ∈ deepenGens`;
  (iii) `img anchor = rep` (the "same colour slot" lemma) ⟹ `g_{x,y} x = y`.
**This closes the branch cell — a large fraction of `DeepenRefInExec`, and worth landing next as its own
theorem** (`exec_recovers_cell_orbits`).

**The crux — `ORBIT_K` on `K∖cell`.** For `x ∈ K∖cell`, `y = α x`, need `WordReach exec x y`. `x` is not an
anchor, so no `g_{x,·}` maps it directly. The exec gens `g_{a,b} = σ_final(a,b)` DO move `K∖cell` (piece 3:
`= σ_final` on all `K`), but `σ_final(a,b) x ≠ α x` in general. This is the genuine **`Stab`-reachability**
residue (surplus ref gens differ from exec gens by a `Stab(a)` element). Two candidate routes:
- **Route α — "branch cell determines `K`" + branch-cell GROUP completeness.**
  1. **`branch_determines_K`** (clean, from discreteness): an `IsColAut adj χ` that fixes the branch cell
     pointwise is the identity on `K`. *Why:* individualizing the branch cell + refinement discretizes `K`
     (that is exactly what `deepen` does — all-singletons on `K` at the leaf), and a colour-automorphism of a
     discrete colouring is `id`. This is a `deepen`-discreteness lemma (`SealDepthBridge`-style).
  2. **branch-cell group completeness:** `⟨exec gens⟩` restricted to the branch cell `= IsColAut` restricted
     to the branch cell (as groups). Then a word `w ∈ ⟨exec⟩` with `w = α` on the branch cell exists; by (1)
     `w = α` on all `K`, so `w x = α x = y` ⟹ `WordReach exec x y`. **This step is the hard part** — it is a
     genuine "the `g_{a,b}` generate the full branch-cell action group", not a one-liner. The clean half gives
     TRANSITIVITY (every pair `x→y`), which yields the full symmetric group on each orbit only if the orbit
     maps compose correctly; whether transitivity ⟹ the full group here needs the `g`'s to realize not just
     `anchor↦rep` but the whole `σ_final` consistently. **Assess before committing.**
- **Route β — direct orbit transitivity on `K` via a `K`-extended `joint`.** Generalise `joint`/`g_{x,y}` so
  the anchor-to-rep map is proved for `K∖cell` vertices too: since `deepen` individualizes a SEQUENCE that
  eventually singletons `K∖cell` vertices, a `K∖cell` vertex `x` is individualized at some deepening level `ℓ`;
  run the pair `(a, b)` whose level-`ℓ` pick is `x` vs `α x` and read off `WordReach` for `x`. Risk: the level-`ℓ`
  pick is `chooseIdK`'s lowest-index, not freely `x`; needs the all-anchors/all-levels quantification to hit `x`.

**The `hfix` obligation (piece 3's hypothesis).** `twistOf_of_transport_fixing` needs `σ'` to fix off-`K`.
Empirically vacuous (support `= K` on every witness). To discharge: prove `K = ` union of non-singleton
`χ`-cells at the leaf (so off-`K` = fixed `χ`-singletons, which every `IsColAut` fixes) — i.e. **off-`K`
vertices are `χ`-singletons**, hence `σ_final`-fixed. This is a `coupled`/`allSingletonsK`-discreteness lemma,
tractable, and shared with `branch_determines_K`.

**Difficulty ledger.** reduction `hL1 ⟸ ORBIT_K` = EASY (plumbing + `deepenRefGens_isColAut`). Branch-cell half
= MEDIUM (deepen-terminates + `img anchor = rep` + joint plumbing) — **land next.** `hfix` discharge = MEDIUM
(discreteness). `K∖cell` (Route α step 2 / Route β) = **HARD, the crux** — this is where, if it stalls, the
**all-or-nothing backup gate** (§9.3, `①c` by construction, sidesteps the group-completeness entirely) becomes
the pragmatic pivot. Recommended order: land the branch-cell half + `hfix` discharge (real progress, clean),
THEN attack `K∖cell` with a hard look at Route α-2's group-completeness vs the backup.

### 9.1.2 `hreach` — DETAILED ROUTE ANALYSIS (2026-07-22)

`hreach` := *`∀ ρ ∈ deepenRefGens, ∀ x ∈ K_ρ, WordReach exec x (ρ x)`.* Since `ρ ∈ IsColAut` and `ρ x ∈ K_ρ`,
this is: **for `x, y ∈ K` in the same `IsColAut(χ)`-orbit, `WordReach exec x y`** — i.e. *the anchor-to-rep
twists generate the full automorphism action on `K`*. Landing the infra sharpened three things below.

**The shared obligation `[INV]` — `K` is `σ_final`-invariant (⟺ `hfix`).** `twistOf`'s `imgFun` sends `v ∈ K`
to `σ_final v` **only if `σ_final v ∈ K`**; else `find?` misses and the map breaks (not a bijection ⟹ `permOf`
fails ⟹ `twistOf = none` ⟹ NO exec gen). Since `coupled χ (transportColouring σ_final χ1) = σ_final(coupled χ
χ1)` (coupled transports — provable), `[INV] ⟺ coupled χ (dj.col) = coupled χ χ1 ⟺ σ_final(K) = K`. **This is
not automatic** — off-`K` = non-`χ1`-splitting cells, which `σ_final` can move. It gates BOTH piece 3's `hfix`
AND the branch-cell existence. **Discharge:** `[DISC]` — the deepening discretizes the WHOLE graph (MEASURED
on G8/t3/wcyc9/mp7) ⟹ `K` = union of non-singleton `χ`-cells (a function of `χ` alone, so `σ_final`-invariant)
and off-`K` = `χ`-singletons (`σ_final`-fixed). `[DISC]` is a firing-completeness domain fact, plausibly
provable per-family; it is the honest cost of the clean half too. **Priority infra.**

**The clean half — branch cell — ✅ LANDED 2026-07-22 (`exec_recovers_cell_orbits`, axiom-clean).** For
`x, y ∈ cell` related by `t ∈ IsColAut` (`t x = y`), the executable emits a verified gen mapping `x ↦ y`, so
`WordReach exec x y` in one step. Assembly: **`joint` strengthened with ANCHOR-TRACKING** (new
`σ' a₀ = σ a₀` conclusion — the per-level `τ`'s fix the protected singleton `y` via the new atoms
`isColAut_fixes_singleton`/`step_preserves_singleton`/`step_indiv_singleton`) gives `σf x = y`; **piece 3**
(`hfix` from `[INV]`) gives `twistOf = some σf`; **`mem_deepenGens_of`** (new) reconstructs `σf ∈ deepenGens`.
Carries the firing/domain facts as hypotheses: `deepen` succeeds, gate passes, `Amenable`, and **`[DISC]`**
(`Discrete d1.col`). ✅ **`[INV]` discharged from `[DISC]`** (2026-07-22, `offCoupled_singleton`, axiom-clean):
`w ∉ coupled χ χc` means `w`'s `χ`-cell has constant `χc`, and `Discrete χc` collapses a constant-`χc` set to
one vertex ⟹ `w` is a `χ`-singleton, which every `IsColAut` fixes. So the half is complete modulo the single
named domain fact `[DISC]` (whole-graph leaf discretization — measured on every firing witness, plausibly
provable per-family; shared with the crux).

**✅ CELL COVERAGE — extended to the WHOLE cell (2026-07-22, `exec_recovers_refgen_on_cell`, axiom-clean).**
The branch-cell half holds for ANY anchor-rep pair, and a ref gen `ρ ∈ IsColAut` maps each cell vertex `x` to
`ρ x` in `x`'s orbit — so applying the half at anchor `x` (rep `ρ x`; `ρ x = x` is `refl`) reaches `ρ x`
directly. Thus the **cell part of `hreach` needs no `K∖cell` content**, discharged from the domain bundle
`AnchorFires` (deepen succeeds + gate + `Discrete` leaf, all anchors) + `Amenable`.

**★ R1 (full-`SameOrbits` route) REDUCED TO ONE PREDICATE (2026-07-22, `deepenRefInExec_of_cell_and_crux`,
axiom-clean).** For the FULL `SameOrbits` route, `hreach` splits: off-`K` = `refl`, cell =
`exec_recovers_refgen_on_cell` (done), so the entire remaining content is the isolated `K∖cell` crux
`ExecRecoversKMinusCell` — for a ref gen `ρ` and a coupled-but-non-cell `x ∉ branches`, `WordReach exec x (ρ x)`.

**★★★ BUT THE `K∖cell` CRUX IS NOT NEEDED (2026-07-22, `deepenSupply_guarded_canonizer_of_cell`, axiom-clean).**
The object narrows only through `rep` on `forcedSet ⊆ branches` (`Composite.narrow_forceThenConsume` +
`forcedSet_subset`), and `rep` at a branch source depends only on that source's orbit, which stays inside the
branch cell (`orbit_subset_branches`). So `①c` needs orbit agreement **only for branch sources** — the weakened
reduction `OrbitPrune.SameOrbitsOnBranches` (lemmas `rep_congr_at`, `narrow_forceThenConsume_congr_branch`,
`guarded_mixed_canonizer_of_sameOrbitsOnBranches`, landed). And `SameOrbitsOnBranches deepenRefSupply
deepenSupply` follows from the cell coverage ALONE (`wordReach_deepen_of_ref_on_branch` inducts a ref word, each
step landing in the cell): **`①c` closes modulo `{R2, Amenable, AnchorFires}` only.** The `K∖cell` group-recovery
was an artifact of the over-strong full `SameOrbits`; the greedy pick's `K∖cell` action is invisible to the
canonizer. `ExecRecoversKMinusCell` / Route ε below are retained only as the (now-unneeded) full-`SameOrbits` route.

**★★★ THE REFERENCE IS ELIMINATED — `①c` modulo `{Amenable, AnchorFires}` ONLY, no `deepenRefSupply`/R1/R2
(2026-07-22, `deepenSupply_guarded_canonizer_direct`, axiom-clean).** Reconsidering *what introduced R1/R2* (the
equivariant-reference detour): the object's flag reads the supply only through `rep` on `forcedSet ⊆ branches`,
so `StallEquivariant` needs only that deepen's **branch-orbit relation transports** — and it does, because
deepen's branch orbits EQUAL the `IsColAut`-orbits (`deepen_branch_orbit_iff_aut`: `⟹` soundness
`wordReach_imp_isColAut`, `⟸` the branch-cell half), which conjugate under `σ` (`isColAut_conj_iff`). The generic
`SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport` (no `SupplyEquivariant`) feeds this to
`Residue.guarded_mixed_canonizer`. **So the entire reference apparatus — `deepenRefSupply`, R1 (`SameOrbits`),
R2 (`twistOf`-transport) — is discarded, and the `twistOf` order-dependence subtlety (below) is MOOT.** The
`SameOrbits`/`SameOrbitsOnBranches` route and everything about `deepenRefSupply` are kept only for provenance.

> **⚠ R2 / `twistOf`-transport RETIRED (2026-07-22).** While building R2 (`SupplyEquivariant deepenRefSupply`),
> found `twistOf` is **order-dependent even on emitted gens**: `K=[w,w']`, gate on `χ1` passes, but `χj` collides
> (`χj w=χj w'`) with `χ1 w'` unmatched ⟹ `imgFun=id` (`permOf` some) under one `K`-order, non-injective
> (`permOf` none) under the reverse. So `permOf`-success does NOT force `χj`-injective-on-`K`; R2 would need a
> `replayAll`-discretizes-`K` lemma (possibly false). The reference-free route above sidesteps it entirely — the
> reference is never used, so its equivariance is never needed.

**The crux — `K∖cell` — characterized precisely.** Exec gens `= {σ_final(a,b)}` on `K`, each moving the cell
(`a↦b`, `b≠a`). Need `⟨σ_final(a,b)⟩`-orbits on `K` `=` `IsColAut`-orbits on `K`. The hard content is
**`ker φ`** (`φ : IsColAut → Sym(cell)`, `β ↦ β|_cell`): automorphisms that FIX the branch cell but move
`K∖cell` (e.g. a `K∖cell` swap fixing the cell). **No single exec gen is in `ker φ`** (all move the cell), so
`ker φ` must be recovered as WORDS in cell-moving gens. Measured recovered (t3 `K∖cell` size-6 orbit matches).
This is exactly `ExecRecoversKMinusCell` — the Route-ε target.

**ROUTE α — `branch_determines_K` + branch-cell group completeness. ⚠ HAS A FLAW.**
  - α1 `branch_determines_K`: an `IsColAut` fixing the cell pointwise is `id` on `K`. **FALSE in general** —
    `deepen` individualizes a *sequence* (cell vertex, then `K∖cell` picks at deeper levels); the cell alone
    need not discretize `K`, so a `K∖cell` swap can fix the cell (`ker φ ≠ 1`). α1 holds only in the
    "single-level coupling" special case (cell individualization alone discretizes `K`). **Route α is
    incomplete on its own** — it handles `ker φ = 1` only.

**ROUTE β — per-level / `K`-extended reachability.** A `K∖cell` vertex `x` is individualized at some deepening
level `ℓ`; read off `WordReach` from a pair whose level-`ℓ` pick is `x` vs `α x`. Content: the deeper-level
member-swaps must be exec-reachable. **This IS the `ker φ` recovery**, re-expressed per level: it recurses
(level-`ℓ` cells are single-orbit under `Amenable`, and their member-swaps are what deeper exec structure must
generate). Viable but needs a nested induction; the risk is `chooseIdK`'s lowest-index pick — hitting a chosen
`x` needs the **all-anchors × all-picks** quantification (which is exactly why the reference is all-picks and
why all-anchors was forced by G8).

**ROUTE ε (NEW — most promising native route) — direct `ref ⊆ exec` via a path-difference induction.** Do NOT
route through `Aut`-completeness. A ref gen `ρ = σ'_P` (path `P`) differs from the canonical `g_{a,b} =
σ_final` by the sequence of "pick a different member of a single-orbit cell at each level". **Induct on the
deepening depth:** at each level the two picks lie in one `Amenable` single-orbit cell, so they differ by a
`τ ∈ Stab`; if each such `τ`'s action is exec-reachable, compose. This turns the crux into a *local* claim —
"each single-orbit-cell member-swap is exec-reachable" — instead of a global group-generation theorem, and it
reuses the `joint`/`step_rerelate` machinery already built. **The bottom of the recursion** (level-0 = the
branch cell) is the clean half. The open part is whether deeper-level swaps bottom out via all-anchors coverage
or need their own sub-induction — but this is the route that most directly leverages what is already landed.

**ROUTE ζ (NEW — merges with existing project work) — import the recovery / `CellsAreOrbits` machinery.**
`hreach` = "cells become orbits at the deepening depth" = the project's **`RecoverableByDepth` / `CellsAreOrbits`**
notion (`CascadeOracle`, `SealDepthBridge`, `HandledBridge`). `deepen`'s `K`-discretization IS a bounded-depth
individualization; the seal machinery already proves *cells-are-orbits at bounded depth* for the recoverable
families. So for **seal-covered families the crux discharges by IMPORT**, not fresh proof — exactly the
"merge with the WL-dimension / recovery work" the user flagged. Scope: this covers the metric/DRG/Cameron
families the seal reaches; the residue is whatever `deepen` targets beyond them (the base symmetry of `mp7`,
`PGL(3,2)` — check whether `theorem_1_HOR_*` / Route-C reach it).

**VERDICT — HYBRID is most viable.**
1. ✅ **DONE (2026-07-22): `[DISC]`/`[INV]` + branch-cell half + WHOLE-cell coverage + R1-reduced-to-one-predicate.**
   `exec_recovers_cell_orbits` → `offCoupled_singleton` (`[INV]⟸[DISC]`) → `exec_recovers_refgen_on_cell`
   (all cell vertices) → `deepenRefInExec_of_cell_and_crux` (R1 = `{Amenable, AnchorFires, ExecRecoversKMinusCell}`).
   The entire remaining content of R1 is now the single predicate `ExecRecoversKMinusCell`.
2. **★★★ SUPERSEDED — the `K∖cell` crux is OFF the critical path (2026-07-22).** Attacking
   `ExecRecoversKMinusCell` revealed it is not needed: `①c` narrows only through branch-cell reps, so
   `OrbitPrune.SameOrbitsOnBranches` (branch-only orbit agreement) suffices, and that follows from the landed
   cell coverage. `deepenSupply_guarded_canonizer_of_cell` closes R1 modulo `{R2, Amenable, AnchorFires}`. Route
   ε / `ExecRecoversKMinusCell` remain only for the (unneeded) full-`SameOrbits` route. **Remaining for `①c`:
   R2 (§9.2) + the domain facts `Amenable` (§5) and `AnchorFires`.**
3. **ROUTE α** is not standalone (α1 false in general) but its valid special case (single-level coupling) is
   the `ker φ = 1` base that ε's induction bottoms out on — so α is *absorbed into the hybrid*, not discarded.
4. **ROUTE β** ≡ ε viewed per-level; keep ε's framing (cleaner recursion, reuses landed machinery).
5. If ε's deeper-level recursion and ζ's import both stall on the same residual family, THAT family is the
   honest trigger for the **all-or-nothing backup gate** — but not before (per the standing steer).

### 9.2 R2 — mechanical assembly

`twistOf_transport` (done) → `GensEquivariant deepenRefSupply` → `SupplyEquivariant` (via
`supplyEquivariant_of_gensEquivariant`). The set-level piece: `deepenAll`/`replayAll` leaf-set transport
under σ (fuel induction on the part-I stage lemmas), lifting the conjugation core. ⚠ Subtlety: the
transported reference calls `twistOf` with `coupled` only a `List.Perm` of `(coupled).map σ`, and `find?` is
order-dependent — but under the `allSingletonsK` gate the colour-match is UNIQUE, so the assembly needs
"`twistOf` invariant under a `Perm` of `K` when `allSingletonsK`", then composes.

### 9.3 The BACKUP — the poly all-or-nothing gate (held; only if Layer 1/2 stalls)

Per deepening level, check whether individualizing **each** member of the chosen id-cell gives the same
footprint-partition; emit **all-or-nothing**, deferring on failure. Poly (`≤ n` members × `≤ n` levels × a
refine); it **checks** `Amenable` locally instead of proving it (`①c` by construction — a canonical gate +
pick-independence ⟹ a canonical group); gate-failure = honest deferral. Strictly better than a budgeted
firing reference (route (b), off the table). Changes the landed executable, so it is the fallback, not the
plan.

---

## 10. Evidence / validation record

- **C# strength sweep** (`DeepenStrengthProbe.cs`, 39 families — CFI, multipedes both colourings, Cameron
  Johnson/Hamming/Kneser, T(8), Chang-A/B): **starvation = 0 everywhere**; every checkable row **complete**
  (`harvested == |Aut|`). Since `harvested == |Aut| ⟹ exec == Aut == ref ⟹ R1`, this is broad **symmetric-family
  R1 evidence**. ⛔ The old "Chang-A leak 24/384" is RETRACTED — measured **complete 384/384**; what survives
  is **fusion** (`A_stall < A_full`), which costs deferral not completeness.
- **Lean direct exec-vs-ref check** (`ScratchR1Probe`, deleted): **no R1 falsifier** — `exec-orbits ==
  ref-orbits` on `G8` ×7 relabellings (rich `[4,2,2]`, multiset relabelling-invariant), `cG8` (complement,
  same Aut / different deepening), `t3`, `wcyc9`; rigid `F12` all-singletons both sides (ref does **not**
  falsely merge). ★ **Tight:** `G8` exec = **16 = Σ k(k−1) over {4,2,2}** = one DIRECT verifying twist per
  same-orbit ordered pair (no words).
- **`mp7` acceptance** (`PerformanceTest` §16): branch cell 28, 756 = 28×27 gens, gadget cell (28) *and*
  foot cell (14) each a single orbit.
- **Discreteness** (`ScratchDisc`, deleted): the canonical deepening discretizes the WHOLE graph on
  `G8`/`t3`/`wcyc9`/`mp7`.
- **⚠ Caveats — the honest limits.** The random-`n=8` sweeps are DEGENERATE (cells ≤ 2). The direct
  exec-vs-ref check covered **branch-cell profiles only** (K-coverage is less validated). And the one
  untested regime is a **`¬Amenable` firing witness** — the missing part-III "fires-but-incomplete" graph;
  expander-base multipedes (rigid) and Chang (complete) are both closed as candidates.

---

## 11. Traps and lessons (do not re-walk)

- **The G8 falsifier discipline:** an equivariance falsifier must be a **partially-firing** witness (`mp7`
  fires totally, so its profile is `[28]` down any path and it cannot falsify). Sweep partially-firing,
  symmetric witnesses — random graphs are almost surely asymmetric (cells ≤ 2) and carry no signal.
- **Two retracted claims (⛔ do not re-derive):** (1) any "X ⟹ GI∈P, therefore X impossible" argument is
  BANNED — a perfect key *is* GI∈P, the target; the inference is circular. This was violated once (the
  "cell orbit partition ≡ GI so the supply would be GI∈P" argument) and retracted. (2) "Miyazaki defeats
  it" (see §3).
- **Perf trap #1:** never return the twist as a closure — materialise as `Vector` (data, not functions).
- **Lean tactics:** `split at h` (not `cases`/`dsimp`) for `(match e …) = some` after `dsimp only` clears
  `let`/`have`; `rw` under `decide` breaks the motive → use `simp only [iff_lemma]`; `Subgroup` is NOT
  imported; `Vector.get` reduces via `rw [Vector.get]; simp`; for `¬CellSingleOrbit`, `push_neg` yields the
  `RigidObstructionAt` shape; `subst` on `x = v` may eliminate `v` — use `rw` when you need `v` to survive.
- **★ THE `deepen` MATCH-REDUCTION RECIPE** (13 iterations to find; reuse it for the joint induction body,
  which reduces `deepen`/`replay` the same way). To reason about `deepen adj χp (fuel+1) cur acc = …`:
  1. `unfold deepen; dsimp only` (zeta-reduce the `let χc := cur.col; let K := …`).
  2. `cases hK : (coupled χp cur.col).isEmpty with | true => … | false => …` (it is a **Bool** if).
  3. `rw [if_neg (by simp [hK]), if_neg (by simp [hK])]` — reduces the `if` on **both** sides of the
     equation (LHS bare + RHS under `Option.map`).
  4. **`generalize chooseIdK (coupled χp cur.col) cur.col = co` BEFORE any `split`/`cases`** — else they
     descend into `chooseIdK`'s internal `foldl` and expose a spurious `acc✝ : Option ℕ`.
  5. `cases co with | none => simp | some cid => …`; in the `some` case `dsimp only` to iota-reduce the
     `match some cid`.
  6. **`split` for the filter** (safe now — `chooseIdK` is opaque). Order = **`[]` first, then `cons`**
     (`· rfl` for nil = `none = map none`; `· rename_i _ w _ _` for cons — 4 inaccessibles
     `x✝ w✝ tail✝ heq✝`). ⚠ `generalize` on the filter FAILS (lambda-elaboration mismatch); `‹Fin n›` is
     unreliable — name via `rename_i`.
  7. Map-equalities close with `rw […, Option.map_map]; congr 1; funext p; simp [Function.comp,
     List.reverse_cons, List.append_assoc]`.

---

## 12. Pointers

- **Live tracker:** `chain-descent-remaining-work.md` §1C (C3 arc) + the CURRENT FRONTIER block.
- **Topic memory:** `[[project-c3-kernel-supply-2026-07-19]]` (the full C3 arc, including this thread).
- **The staging analog:** `kernelSupply` (`KernelRef.lean` / `KernelTransport.lean`) — deepen mirrors its
  `SameOrbits`-against-an-equivariant-reference discharge exactly.
- **The obstruction classification:** `chain-descent-exhaustive-obstruction.md` (EOL) +
  `chain-descent-ir-blindspot-solver.md` §11.14 (the 2×2) — the Layer-2 grounding.
- **C# side:** `ChainDescent.cs` `HarvestTwists` (the source), `DeepenStrengthProbe.cs` (the 39-family
  sweep), `FanoMultipedeProbe.cs` (`mp7` cross-check).
