# Chain descent — the deepen supply (`C3b`, the base-symmetry constructor)

> **What this doc is.** The single self-contained home for `deepenSupply` (the `DeepenAnchor` /
> `ReplayDeepening` port of the C# `HarvestTwists`). It grew its own thread — seven Lean files plus
> scattered `remaining-work.md` §1C and topic-memory sections — so this collects the **grounding** (what it
> is, why it exists, what is proved) and the **future work** (the one open crux and its decomposition) in
> one place. Authoritative for deepen; when it disagrees with an older scattered note, this wins.
>
> **Related docs:** `chain-descent-remaining-work.md` §1C (the live tracker), the topic memory
> `[[project-c3-kernel-supply-2026-07-19]]`, and the `kernelSupply` staging analog
> (`KernelRef`/`KernelTransport`) which deepen mirrors exactly.

---

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
  - **Layer 1 (`Amenable ⟹ R1`) = a mechanical re-relating induction.** Its engine + monotonicity +
    cell-transport bricks are **landed axiom-clean**; the remaining core is one ~100–200-line joint fuel
    induction (piece 2b) plus pieces 3 (twistOf verifies) and 4 (K-coverage).
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

The question is **not** "is WL-dimension bounded" (unbounded WL-dim exists — CFI — and is irrelevant). It is
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

| Link | Statement | Status |
|---|---|---|
| **L0** | `(R1 ∧ R2) → ①c` | **PROVED** (`deepenSupply_guarded_canonizer_of`) |
| **L1** | `Amenable → R1` (`DeepenRefInExec`) | engine + bricks landed; joint induction (2b/3/4) remain |
| **L2 / G2** | `¬Amenable → rigid obstruction` (attribution) | **PROVED** (`rigidObstruction_of_not_cellSingleOrbit`) |
| **R2** | `SupplyEquivariant deepenRefSupply` | core (`twistOf_transport`) landed; set-level assembly remains |
| **G1** | `rigid obstruction ⟹ F_k` | the **shared wall** — NOT needed for `①c`, only totality |

Everything conjectural lives in **G1** (the shared wall, covered whenever anyone covers it) and the
**Schurian-delivery** scheduling piece (G2's *avoidance* direction, a totality obligation). Nothing else is
prose.

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
  - *capstones:* **`deepenSupply_guarded_canonizer_of`** · **`deepenSupply_canonizer_of_amenable`**.

---

## 9. Remaining work

### 9.1 Layer 1 — finish `hL1 : Amenable → DeepenRefInExec` (4 pieces)

1. ✅ **piece 1 (refinement monotonicity)** — `indivOne_refines`, `step_refines`, `isColAut_parent_of_refines`.
   Keeps the running composite `σ' = τσ` in the parent-stabilizer.
2a. ✅ **piece 2a (`cellSingleOrbit_transport`)** — `Amenable` (about the a-descent) delivers `τ ∈ Stab(cur_b.col)`.
2b. ⏳ **piece 2b — the joint fuel induction** (~100–200 lines, the remaining core). Invariant
   `cur_b.col = transportColouring σ' cur_a.col`, `σ' ∈ IsColAut adj χ`, + carry "`cur_a.col` refines χ".
   Seq accumulator: `seq.drop acc.length` = choices-from-here (`deepen` returns `reverse(acc) ++ choices`;
   top-level `acc = []`). Base = `chooseIdK` none. Step: replay-b picks head `w_b` of b's cid-cell (nonempty
   by `cidCell_length_transport`); `cellSingleOrbit_transport` + `Amenable` give `τ` with `τ(σ' w_a) = w_b`;
   `step_rerelate` carries the invariant; `replay (cid::rest) cur_b = replay rest cur_b'` threads to the IH.
   Concludes: deepen-a leaf & replay-b leaf are `σ_final`-related.
3. ⏳ **piece 3 — twistOf verifies:** `σ_final`-related discrete leaves ⟹ the colour-match
   `twistOf adj χ χ1 K χj` = `σ_final` on all `K` ⟹ returns `some` ⟹ an exec verified gen `a ↦ b` ⟹
   `WordReach exec a b`.
4. ⏳ **piece 4 — K-coverage** (`x ∈ K ∖ branch-cell`): collapses under full discreteness (trivial `Stab` at
   a discrete leaf ⟹ unique relating automorphism ⟹ ref twist = exec twist on all `K`, membership not
   words). ⚠ the least-validated piece; the missing part-III `¬Amenable` witness lives here.

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
