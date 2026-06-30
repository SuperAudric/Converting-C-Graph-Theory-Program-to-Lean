# The CellsAreOrbits route — bounded WL-dimension of the forms graphs (independent-math; DEMOTED)

> **⚠ This is NOT the live polynomial route.** The live route is
> [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) (cross-branch harvest + form-recovery — what the
> C# canonizer actually does). This doc pursues poly *through* **bounded WL-dimension** (`CellsAreOrbits` = refinement
> reaches orbits). That was found (2026-06-30) to be the **wrong model of the C#**, so it is **demoted** to:
> (i) a built, axiom-clean **scaffold** (the cap / base case / Witt / node-count bridge / wall isolation — all NOT in
> `build.sh`), and (ii) the **bounded-WL-dimension statement as independent mathematics** (the forms graph has WL-dim 2,
> probed; a clean result worth pinning, off the canonizer's critical path).
>
> **Read this doc only if** you want the WL-dim-2 theorem or the scaffold. For the polynomial seal, read the recovery doc.

---

## STATUS (read first)

**What this route is.** A proof that the affine-polar forms-graph residue is canonized in **polynomial** time *via the open
core* `CellsAreOrbits` (= the WL-closure / square-class refinement partition equals the orbit partition at every bounded
base = **bounded WL-dimension**). The reduction is **`poly ⟸ B`** (B sufficient for poly; a corrected slogan — *not* the
earlier `poly ⟺ B`).

**Why demoted.** The C# canonizer does **not** reach orbits by refinement. `CellsAreOrbits` (∀ cells) is genuinely **false
at 1-WL** at bounded bases (`model_gap.py`: cells `10 < 12` orbits at `|S| = 2`; gap grows with `q`; 2-WL reaches orbits —
so the forms graph has **WL-dimension 2**, not 1). The canonizer's single path comes instead from **deferral + cross-branch
harvest + form-recovery** (verified against `ChainDescent.cs`; see §5). So `CellsAreOrbits`/bounded-WL-dim is not the
mechanism — it is a true-but-tangential structural fact. Full demotion arc: §5.

**What's built (axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`):**

| Module | Content |
|---|---|
| `ScratchSimilitudeCap.lean` | **the cap** — the graph fixes `Q` only up to scaling, so refinement is capped at the **square class** (`χ(det G₂)` invariant; exact value and singleton square-class are not). The wall is real, not a formalization gap. |
| `ScratchOrbitBaseCase.lean` | **base case + delimiter + free prefix** — depth-0 (translations), depth-1 isotropic sphere (mod Witt), the **multiplier-rigidity delimiter** (`μ = 1` once `span S` carries an anisotropic vector), and the general totally-isotropic free prefix (mod `WittRealizes`). |
| `ScratchWittCone.lean` | **Witt W0 + W1** — orthogonal reflection as an isometry; `WittConeTransitive` reduced to the concrete residual `IsotropicPairing`. |
| `ScratchNodeCountBridge.lean` | **the node-count bridge + transport seam** — the `poly ⟸ B` reduction's *missing pillar*: `selectedCell_single_stabOrbit`, `certifiedSinglePath_of_disposition` (bounded nodes `≤ n` + every consumed cell one orbit), `repTransport`/`baseTransport` (rep-choice/level transport), keyed on the weaker `SelectedCellIsOrbit`. Residual = the `canonForm` lex-min lift (`ChainDescent.lean §15.7`; not Route-specific). |
| `ScratchWallKernel.lean` | **the wall isolated as one predicate** — `WallKernelFor Obs` + `stabOrbit_iff_obs_of_wallKernelFor`: at an anisotropic base, modulo Witt, `CellsAreOrbits ⟺ WallKernel` for a graph-invariant observable `Obs`. The single-round `WallKernel` (= `SameSquareClass`) is the *refuted* separator; the right `Obs` is the iterated `χ(det G₂)` 2-WL. |

**The open core (B = bounded WL-dim) — probed TRUE and `O(1)`-crackable, unproved in Lean.** The 2026-06-29 crackability +
depth probes (`wall_*.py`) found that the **iterated `χ(det G₂)` 2-WL** observable **determines** the orbit at a bounded
anisotropic base with `O(1)` iteration depth, **uniformly in `d, |S|, q,` type** (orbit counts grown to 324). So for this
family the "node-4 wall" is not a wall — it is a bounded-depth character inversion awaiting formalization. (This same
"information is there at a bounded base" evidence supports the **recovery route**, which extracts it via harvest instead.)

**If pursued (for the independent-math value), the live Lean target** is `WallKernelFor Obs` for `Obs` = the iterated
`χ(det G₂)` 2-WL, as a bounded-depth (1–2 round) character inversion — reusing `pairCharSum_factor_gen` /
`gaussSum_sq_ne_zero` / the `χ(det G₂) ↔ Z_u` bridge. This is the **bounded-2-WL-dimension theorem**, of interest but off
the canonizer's critical path.

**Banked / durable.** Quasipoly seal `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (in `build.sh`, axiom-clean) +
sub-exp `viaSpielman`. Probes: `GraphCanonizationProofs/{model_gap,descent_probe,wall_frame,wall_2wl,wall_pair,wall_depth,wall_depth2}.py`.

**Quality bar:** axiom-clean, no `sorry`/fresh `axiom`, `native_decide` banned, full build green when ported.

---

## 1. The claim, and why B is worth pinning as independent math

The chain-descent canonizer's cost is a **sum over descent-tree nodes**. For the forms graph the descent is empirically a
single path, so cost is poly **provided** every cell the descent individualizes is a single orbit (it never has to branch).
That proviso is:

> **B (`CellsAreOrbits`).** At every partial base `S`, each refinement cell equals a single `Stab(S)`-orbit. Equivalently,
> the WL-closure (square-class refinement) partition equals the orbit partition = **bounded WL-dimension**.

**The reduction, stated honestly:**

> **`poly ⟸ B`** (B *sufficient*, not equivalent). B gives poly in three steps: (1) per base —
> `twinsRealizedByResidualAut_iff_cellsAreOrbits` (LANDED, `Cascade.lean`): WL-cells at base `S` = `Stab(S)`-orbits; (2)
> assembly — B at every node ⟹ the consumed cell is one orbit at each step ⟹ single path (the **node-count bridge**,
> `ScratchNodeCountBridge`); (3) node-count → poly — single path ⟹ poly node count ⟹ poly (a meta budget argument; the
> project formalizes no runtime model).

**Independent-math value.** Even demoted as a *route*, B is a clean structural question — "do the forms graphs have bounded
WL-dimension at every partial base?" — whose answer (WL-dim 2, probed) is a real result. The scaffold reduces the entire
question to one predicate (`WallKernelFor Obs`), and the probes shifted it from "open both ways" to "true and
`O(1)`-crackable." Pinning it in Lean is worthwhile on its own; it is just **not** how the canonizer achieves poly.

---

## 2. The object

- **Graph.** `V = K^d` (`K` finite, `d = 2m`), adjacency `Q(x − y) = 0` for a nondegenerate `Q`.
- **Automorphisms.** Affine **similitudes**: translations `⋊` linear similitudes `g` (`Q(gx) = μ(g)·Qx`, `μ ≠ 0`); an
  isometry is `μ = 1`. Modelled as `OrbitBaseCase.Similitude Q`.
- **Refinement sees only the square class** (the cap, §3a): the finest iso-invariant form-data is `χ(det G₂)` = square
  classes of even-order Gram minors. The exact form value is not a graph invariant.

---

## 3. What's proved (the scaffold)

### 3a. The cap — refinement's ceiling (`ScratchSimilitudeCap`)
`affinePolarAdj_smul_eq` (graph of `c•Q` = graph of `Q`); `chi_pairForm_smul` (`χ(det G₂)` scaling-invariant — the
legitimate pair observable); `chi_singleton_smul` (singleton `χ(Q·)` flips — not invariant); `pairForm_value_not_invariant`
(exact value not recoverable by any iso-invariant). **Consequence:** B can only be certified from square-class data; the
exact-Gram data the orbit "really" needs is not refinement-visible — that gap *is* the wall.

### 3b. Base case + delimiter (`ScratchOrbitBaseCase`)
`affinePolar_empty_base_one_orbit` (depth 0, free); `depth1_isotropic_sphere_one_orbit` (depth 1, mod `WittConeTransitive`);
`mult_eq_one_of_fixes_anisotropic` / `…_span_anisotropic` (**the delimiter**: a similitude fixing an anisotropic vector has
`μ = 1` ⟹ multiplier freedom in `Stab(S)` ⟺ `span S` totally isotropic); `stabOrbit_zero_base_scales` (free side at the
origin — orbits square-class-coarse, matching refinement); `stabOrbit_preserves_norm_of_anisotropic_base` (wall side —
at an anisotropic base, orbits are norm-fine, strictly finer than square-class cells). Plus the general free prefix
(Increment 2, mod `WittRealizes`).

### 3c. The induction, and exactly what B needs
B is proved by induction on base size; the step splits along the delimiter:

| Regime | `span S` | `Stab(S)` multipliers | Kernel status |
|---|---|---|---|
| **Free prefix** | totally isotropic | free | multipliers absorb the square→exact gap ⟹ **free, modulo Witt** |
| **Wall (tail)** | contains an anisotropic vector | `μ = 1` only | square-class must genuinely pin exact Gram = **bounded WL-dim = the open kernel** |

So B = [free prefix: Witt tech debt] + [anisotropic tail: the open kernel, `~d/2` levels].

### 3d. The wall, isolated (`ScratchWallKernel`)
`WallKernelFor Obs` + `stabOrbit_iff_obs_of_wallKernelFor`: at an anisotropic base, modulo Witt, `CellsAreOrbits ⟺
WallKernel` for any graph-invariant observable `Obs` (orbit-sound for free). Soundness
`stabOrbit_imp_sameExactGram_of_anisotropic` is free (the `μ = 1` delimiter + `similitude_polar`). The wall = `WallKernelFor
Obs` for `Obs` = the iterated `χ(det G₂)` 2-WL. (This `WallKernel` = the exact-Gram form of the seal's `ZProfileSeparates`.)

---

## 4. The open core + the probe verdict

The wall reduces, through the *existing* seal chain `ZProfileSeparates → QProfileSeparatesAtBase → IsotropySeparatesAtBase`,
to `ZProfileSeparates` with the base shrunk from the matching `Θ(log n)` to the `O(d)` frame. The **probe findings**
(`wall_*.py`, durable):
1. `CellsAreOrbits` holds at every **spanning anisotropic** base even with plain 1-WL (the only over-merges are the
   totally-isotropic free prefix = the delimiter).
2. 1-WL is **insufficient** at a bounded single-anchor base; the gap grows with `q` ⟹ **WL-dim > 1** (the forms graph has
   WL-dim 2).
3. The single-round `Z_u(S)` joint count also under-determines at a bounded base — its character matrix is **singular**
   there (the clean single-round Gauss inversion FAILS at a bounded base).
4. **The crack:** the **iterated `χ(det G₂)` 2-WL** count **determines** the orbit at the bounded anisotropic base —
   exactly, uniformly across `q`, both types — with `O(1)` iteration depth (det@1–2, fixpoint@2–3), **uniform in `d, |S|, q`,
   type** (orbit counts grown `12→324`). So the wall is **true, crackable, `O(1)`-depth**.
5. The determination genuinely needs the **pair** observable `χ(det G₂)` (the cap: singleton square-class flips under
   `Q ↦ cQ`; binary-adjacency-only is insufficient).

**⟹ If pursued:** prove `WallKernelFor Obs` for the iterated `χ(det G₂)` 2-WL as a bounded-depth character inversion. This
is the **bounded-2-WL-dimension theorem** for the forms graphs — independent-math value, off the canonizer's critical path.

---

## 5. Why this is NOT the C# model (the demotion, settled — do not re-walk)

Direct comparison to `GraphCanonizationProject/` (2026-06-30) showed:
- The C# refinement is **1-WL** (`WarmPartition.cs`), and `CellsAreOrbits` (∀ cells) is **false** at 1-WL at bounded bases
  (`model_gap.py`). The canonizer does not rely on cells = orbits.
- Its single path comes from an **all-reps oracle** (`CascadeOracle.cs`, "certifies nothing a priori") + **cross-branch
  harvest pruning** (`CoveredByPathFixingAut`, `ChainDescent.cs:589`) + a **deferral selector** (`ChainDescent.cs:251-281`,
  off by default). Orbits are reached **a-posteriori from verified automorphisms**, not from refinement.
- The real-canonizer probe (`RecoveryReconcileProbe.cs`) confirms it: on `VO^ε_4(q)` the harvest is **complete**
  (`ClassifyStarved = 0`), single-path under deferral, full `|Aut|` recovered. The mechanism is harvest, not WL.

**Settled corrections (do not re-attempt):**
- *"base-`d` 1-WL discreteness ⟹ poly"* — **false**: discreteness bounds the node *count*, not cells = orbits at the
  bounded intermediate bases the descent visits.
- *"Route B needs a 2-WL refinement model"* — **withdrawn**: it conflated `CellsAreOrbits` (∀ cells, genuinely false at
  1-WL) with the bridge's weaker `SelectedCellIsOrbit`, and ignored the C#'s deferral + harvest.

**⟹ The implementation-faithful poly target is the recovery route** ([`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md)).
This route's residual value is the WL-dim-2 theorem (§4).

---

## 6. The Witt build — scope (only if completing the scaffold)

Witt is the shared enabler (depth-1 sphere, free prefix, the easy half of each step). It is **tech debt** (known-true
classical geometry, char ≠ 2; Mathlib has the primitives but no Witt theory). Stages:

| Stage | Target | Status |
|---|---|---|
| **W0** | orthogonal reflection `τ_v` is an isometry | ✅ DONE (`ScratchWittCone`) |
| **W1** | cone transitivity — reduced to the residual `IsotropicPairing` (a finite-field vector-existence fact) | reduced; residual open (Medium) |
| **W2** | anisotropic-shell transitivity | Medium |
| **W3** | Witt extension theorem | Large |
| **W4** | Witt decomposition + multiplier realization | Large |

**W0 + W1** is a cheap, self-contained win completing the base case. **W3 + W4 are LARGE and only convert `modulo {Witt}` →
unconditional on the scaffold — they do NOT touch the open kernel** (the wall survives regardless). Defer them as carried
hypotheses until the kernel's tractability is settled; pull them in only when closing out. Mathlib support:
`Module.reflection`, `BilinForm.orthogonal` + `isCompl_orthogonal_of_restrict_nondegenerate`, `QuadraticForm.Isometry`,
`polarBilin`, `Anisotropic`.

---

## 7. Pointers

- **Live polynomial route:** [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) (read this for the seal;
  this doc is independent-math only).
- **Built modules** (axiom-clean, NOT in `build.sh`; all decls in `PublicTheoremIndex.md`):
  `ScratchSimilitudeCap` / `ScratchOrbitBaseCase` / `ScratchWittCone` / `ScratchNodeCountBridge` / `ScratchWallKernel`.
  Verify: `bash scripts/build.sh` (in-build seal) + `lake env lean ChainDescent/ScratchWallKernel.lean` (the scaffold).
- **Probes (durable, reproducible):** `GraphCanonizationProofs/wall_pair.py` / `wall_2wl.py` (the crack: iterated
  `χ(det G₂)` determines the orbit; 1-WL does not), `wall_depth.py` / `wall_depth2.py` (`O(1)` depth), `model_gap.py`
  (1-WL stuck at bounded base — WL-dim 2), `descent_probe.py` (the greedy-selector model, superseded by `RecoveryReconcileProbe.cs`).
- **Reusable machinery:** `PairForm`, `PerAnchorBound.c0_le_threequarters`, `AffinePolarSeal`, `ProfileReduction`,
  `Cascade` (`twinsRealizedByResidualAut_iff_cellsAreOrbits`, `CellsAreOrbits`).
- **The seal / quasipoly build:** `chain-descent-formsgraph-wldim-plan.md` (STATUS + §1). **What's left map:**
  `chain-descent-remaining-work.md`. **Viability arc:** `[[project_formsgraph_wldim_viability_2026-06-28]]`.
- **Naming:** this doc's "Route B" = the forms-graph plan's Route A/B (poly through `CellsAreOrbits`). Unrelated to
  START-HERE's "Route B" (the superseded imprimitive branch).
