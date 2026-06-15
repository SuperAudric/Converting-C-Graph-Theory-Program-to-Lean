# A2 — the potential-drop route (the uniform, Lean-portable attack on the residue)

> **What this is.** The plan for closing **A2** (the seal's lone open math — bounded WL-dimension of the
> primitive / small / non-abelian / non-Cameron residue) by a **potential-drop argument**, the one route that is
> simultaneously *uniform* (not a family ladder) and *Lean-portable* (no CFSG / quasipoly machinery). It
> supersedes the monovariant probe doc (archived: `Archive/ChainDescent/chain-descent-a2-monovariant-probe.md`),
> which is the empirical evidence this route rests on. Frontier overview: `chain-descent-cxt-scoping.md`; the
> consuming substrate + A1: `chain-descent-general-cc-separability.md`, `chain-descent-a1-cc-substrate.md`.

---

## STATUS (read first)

**Goal of this route.** Produce, for the residue, a **small base `T₀` with `c(X_{T₀}), k(X_{T₀}) = O(1)`** — A1's
exact deliverable (`allSingletonFiber_of_card_gt_subset` then fires the seal). The route gets it from a
**potential that drops by a constant factor per individualization.**

**Why this route (the probe verdict, 2026-06-15).** The probe (`A2MonovariantProbe.cs`) measured the max 1-WL
cell size `Φ` under greedy individualization across residue vs carved SRGs and found a clean, *dual* signal:
- **Carved geometric SRGs** (rook/lattice, Johnson/triangular) have `Φ` worst-drop **climbing to 1** — rook
  `L(m)` is *exactly* `((m−1)/m)²` with base `= √n`. They have a rigid geometric core; individualization chips
  it only linearly → large (√n) base. **But these are Cameron-carved.**
- **The residue** (Shrikhande, Clebsch @16; the three Chang graphs @28, validated `≇ T(8)` by 2-rank) keeps
  `Φ` worst-drop **bounded and non-climbing** (≤ 0.667; Chang 0.536, base 2–4 ≪ √28). No geometric core → cells
  **shatter multiplicatively** → `O(log n)` base.

So **"bounded drop" and "non-geometric" coincide, and "geometric" is exactly the Cameron carve.** The monovariant
exists; its driver is geometricity; and geometricity is *already* a handled leg. That duality is this route.

**The route in one line.**
> **non-geometric residue ⟹ a potential drops by a factor `ρ<1` per seed ⟹ `O(log n)` base ⟹ A1 fires ⟹ seal**,
> with **geometric** routed to **Cameron** (cited classification, G3-style) so it never reaches the drop lemma.

**State (Stage 1a + the Stage 1b *reduction* LANDED, 2026-06-15).** The consumer (A1 → seal), the **iteration
engine**, and now the **Stage 1b `c`-halving reduction** are landed, axiom-clean: `CoherentConfig.lean §CC.20`
(`exists_potential_descent` — the abstract halving→`O(log n)` descent; `potential` Φ; `PotentialDrops`;
`exists_small_base_of_potentialDrops`; **`IndistinguishingHalves` + `potentialDrops_of_indistinguishingHalves`**)
+ the seal capstones `reachesRigidOrCameron_viaPotentialDrop` and **`reachesRigidOrCameron_viaShattering`**
(`CascadeAffine.lean §S-gate2`). **The seal now stands conditional `modulo {G3 + IndistinguishingHalves + hcatch +
hImprim}`** — sharpened from `PotentialDrops` (the product `(k−1)c` halves) to **`IndistinguishingHalves`** (the
indistinguishing number `c(X_T)` alone halves): `k` rides free by `maxValency_mono` (build doc §1B), and the
reduction `potentialDrops_of_indistinguishingHalves` makes that rigorous. So the *entire* open mathematical content
is now the single hypothesis **`IndistinguishingHalves`** (the drop lemma proper, `c`-form). The "geometric ⟹
Cameron" / "non-geometric" dichotomy that discharges it is carried as cited classification hypotheses (Neumaier +
the primitive-CC classification), never fresh axioms. **Honest scope:** research-scale, may not close; the residual
math gap is the generic (row-4) case — and the probe (§5 Run 3) refined it: the drop-obstruction is the
*partial-geometry line system*, not the smallest-eigenvalue magnitude. Quality bar held: axiom-clean `[propext,
Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned. **NEXT = discharge
`IndistinguishingHalves` on the residue — i.e. exhibit, for any over-`B` base, a `v` that halves `c(X_T)`, with
"no surviving `c`-class" = "no partial-geometry line system" the structural condition (§2-§3).**

---

## 1. The target and how it plugs in (this half is LANDED)

A1 already converts the route's output into the seal (`chain-descent-a1-cc-substrate.md`):

```
   drop lemma output:  ∃ T₀ small with c(X_{T₀}), k(X_{T₀}) = O(1)
        ⟹  allSingletonFiber_of_card_gt_subset   [pad T₀ to |T| > (k−1)c ⟹ X_T complete]
        ⟹  dominatorReachable_of_card_gt_subset   [feeds hclo]
        ⟹  reachesRigidOrCameron_viaBoundedExtensionParams   [the seal, modulo {G3 + hcatch + hImprim}]
```

So the route owes exactly **"the residue has a small base with bounded `c, k`."** Nothing downstream is open.

## 2. The potential and the drop lemma (the NEW Lean content)

**The potential.** Use `Φ(T) := (CoherentConfig.indistinguishingNumber (pointExtension X T))` — A1's `c(X_T)`,
already defined and `mono` under base extension (`indistinguishingNumber_mono`). (`k(X_T)` is the cheaper half —
driven down with `c` and bounded via the orbit–stabiliser/greedy-base side, build doc §1B.) The probe tracked the
1-WL proxy (max cell size); `c(X_T)` is the 2-WL/coherent quantity A1 consumes — they track, and the 1-WL↔2-WL
slack is the known `hcatch` co-gap (build doc §5.1), not new.

**The drop lemma (the target).** Under a *shattering* hypothesis `Shatters X` (every indistinguishing-class of
size `> B₀` is split by *some* individualization — made precise below), there is a vertex whose individualization
strictly multiplicatively shrinks the potential:

```lean
-- TARGET (not yet built):
theorem potential_drop (hsh : Shatters X) {T} (hbig : B₀ < Φ X T) :
    ∃ v, Φ X (insert v T) ≤ ρ * Φ X T          -- ρ < 1 a fixed rational
```

**The engine — LANDED (Stage 1a, `§CC.20`).** Iterating a per-step constant-factor drop to a `log` bound is what
`exists_greedy_base_le_log` does for `|Aut|`; the **`c`-analogue is now landed** as `exists_potential_descent`
(the abstract halving→`O(log n)` descent), with the per-step drop carried as the predicate
`PotentialDrops B := ∀ T, B < Φ T → ∃ v, 2·Φ(insert v T) ≤ Φ T` and `exists_small_base_of_potentialDrops`
producing the small base (`Φ(T_t) ≤ ρ^t·Φ(∅)` ⟹ base size `O(log n)`, since `Φ ∅ ≤ n²`). The potential is
`Φ X T = (k(X_T)−1)·c(X_T)` — the **threshold-matched product**, not `c` alone: A1 needs *both* `c` and `k`
bounded (the threshold is `(k−1)c < |T|`), and the product captures both. **So the drop lemma proper —
`PotentialDrops` for the residue — is the entire remaining content.**

**`∃ v` (single splitter), not "branch on the cell" — and why (from the IR-solver unification,
[`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §5).** The predicate pins
*one* vertex per step (`∃ v`), and that is load-bearing, not cosmetic. As an **existence** statement (the seal:
"a bounded base exists") the single-vertex form already suffices — `exists_potential_descent` walks one
canonical path. But the *algorithmic* reading (the rigid-residue solver) exposes why it must be a **bounded
splitter**: if instead one branched on the *largest cell* at each level, the leaf product is
`∏_{i<b} Φ(T_i) ≈ ∏ ρ^i n ≈ n^{(b+1)/2}` — **quasipoly even with a short base**. Pinning a bounded splitter (which
`Shatters` provides) and letting refinement *propagate* keeps per-step branching `O(1)`, giving `2^{O(log n)} =
n^{O(1)}` leaves. **Takeaway for the drop lemma:** `Shatters`/`PotentialDrops` must furnish a splitter that is not
just halving but *itself bounded* (`c, k = O(1)` at the pin) — the single-vertex `∃ v` form encodes exactly this.

**Downstream payoff (free once `PotentialDrops` closes).** A2's `PotentialDrops` *is* the seed-selection rule of
the **poly-time rigid-residue (IR-blind-spot/multipede) canonizer** (the deferral Phase-2 hand-off,
[`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §2): closing the drop lemma
delivers both the seal *and* that solver, and the solver's flag set = A2's open row 4 (§3). They are one object.

**Why a constant-factor drop is the right shape (probe-anchored).** The geometric obstruction has worst-drop
`((m−1)/m)² → 1`; that is the *only* way to defeat a constant `ρ`. The drop lemma's job is to show the obstruction
is exactly geometric, so off the geometric locus a fixed `ρ` holds.

## 3. The hypothesis `Shatters`, and discharging it (cited dichotomy; honest gaps)

The content of `potential_drop` is: **a class that resists splitting under *every* individualization is a regular
/ geometric sub-structure.** A class `C` survives individualizing `v` iff every vertex of `C` has the same count
of neighbours among `v`'s relations — a regular bipartite pattern; persistent across all `v` ⟹ a strongly-regular
sub-object = a grand clique / partial-geometry line = **geometric**. So `¬Shatters ⟹ geometric`, and the discharge
is the dichotomy below. **None of these are proved here — they are carried as theorem-statement hypotheses (the G3
pattern), like `PrimitiveCCClassification` already is.**

| Regime (by smallest eigenvalue `−s`) | Classification | Routes to |
|---|---|---|
| `s` bounded, **geometric** (grand cliques, thickness ≥ √n) | Neumaier (geometric ⟹ partial geometry) | **Cameron** (large) — cited G3 leg, *not* the drop lemma |
| `s` bounded, **exceptional** | Neumaier (finitely many per `s`) | **bounded base trivially** (finite set) — residue, Shrikhande/Chang live here |
| `s` unbounded, **conference** | cyclotomic | **abelian leg B** (`AbelianConsumed`) — probe: base 2 |
| `s` unbounded, **generic** (CGGP `n^{Ω(n^{2/3})}` family) | CGGP `base ≤ 2 ⟹ WL-dim ≤ 4` | **the drop lemma must cover this** — the genuine open core |

**The duality that makes the route work:** rows 1–3 are *already-handled legs* (Cameron / finite / abelian). The
drop lemma only has to fire on what's left — the **generic non-geometric** case (row 4) — where there is no
grand-clique to stop the constant-factor split. So `Shatters` is discharged on the residue by: *the geometric and
conference obstructions are carved into other legs; what remains shatters.*

**Honest gap (the one real uncertainty).** Row 4 — unbounded-`s`, non-conference, generic — is where Neumaier's
finiteness does *not* apply (super-polynomially many such SRGs exist) and the only positive result is CGGP's
`base ≤ 2 ⟹ WL-dim ≤ 4`, which is **not yet a portable proof** (it is the affine-plane / BCN Thm 3.3.8 argument
for one construction). Whether a *uniform* counting proof of `potential_drop` covers row 4 is the open research
question this route stakes out. The probe's residue (Shrikhande/Chang/Clebsch) all sit in rows 2 (bounded `s`), so
the **empirical evidence is strongest exactly where Neumaier already gives finiteness** — the scalable row-4
evidence is the construction-bottlenecked gap the probe flagged.

**Refinement (2026-06-15, `Probe_SmallestEigenvalueAxis`, §5 Run 3): the drop-obstruction is the partial-geometry
LINE system, not the magnitude of `|s|`.** Sweeping the smallest-eigenvalue axis on constructible Latin-square nets
showed worst-drop *peaks at the rook/grid* (`s=−2`, bounded!) and its complement, and *troughs* for the intermediate
nets — it is **not** monotone in `|s|`. So keying this table's dichotomy on `−s` alone mislocates what defeats a
constant drop: the obstruction is a *grid / partial-geometry line system* (a bounded-`s`, row-1 geometric feature),
not large `|s|`. **Consequence — two updates to the plan:** (a) **state `Shatters` as "no partial-geometry line
system,"** not "bounded `|s|`" (Stage 1b, §2/§4); (b) this *helps* row 4 — a generic non-geometric SRG has **no line
system by definition**, hence no grid to stop the multiplicative split, so the heuristic now points toward
`PotentialDrops` *holding* on row 4. The gap stays open (no constructible row-4 witness), but its likely resolution
shifted from "fear unbounded `|s|`" to "certify absence of lines," which the forced-triangle / `interNum_eq_one`
calculus is already the right language for (it *counts* the would-be line incidences).

**A parallel proof language for row 4 — bounded constraint-width (from
[`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) §7).** The Neumaier/spectral
route above is *one* way to discharge `PotentialDrops`; there is a second, structurally different one worth
keeping open because it *need not be equally hard*. The residue's recovery constraints are not a generic SAT
instance — they are **coherent-configuration-structured**: `interNum_eq_one_of_forcedUnique` is literally a
forced-triangle *uniqueness* constraint, and `DominatorReachable` is their propagation closure. A theorem of the
form **"the residue's forced-triangle constraint network has bounded treewidth / clique-width"** is *equivalent
to* `c(X_T) = O(1)` (bounded-width constraint networks both propagate-to-discrete cheaply and bound the
indistinguishing classes), so it discharges `PotentialDrops` in a **combinatorial-constraint** language rather
than the spectral/geometric one. **Caveat (do not misread):** a *generic* SAT/treewidth solver bolted on is
circular — it is poly *iff* the instance is in a tractable fragment, and proving it lands there *is* the bound.
The non-circular content is the structural width theorem itself. Keep this as a sibling attack on row 4, not a
solver bolt-on; if it closes, the bounded-width network *is* the poly rigid-residue canonizer (they unify).

## 4. Formalization plan (stages, reuse, risk)

- **Stage 0 — LANDED.** A1 → seal (§1). Nothing to do.
- **Stage 1a — the iteration engine — LANDED (2026-06-15).** `exists_potential_descent` (the abstract halving
  descent, ported from `exists_greedy_base_aux`), `potential` Φ = `(k−1)c`, `PotentialDrops` (the per-step drop
  predicate), `exists_small_base_of_potentialDrops` (→ small base, `2^|T₀| ≤ max 1 (Φ ∅)`), and the seal capstone
  `reachesRigidOrCameron_viaPotentialDrop` (pads via `§CC.18/19`). All axiom-clean (`§CC.20` / `§S-gate2`). The
  seal's open content is now exactly `PotentialDrops`.
- **Stage 1b, the *reduction* — LANDED (2026-06-15).** The drop lemma is split into (a) a *reduction* and (b) a
  *discharge*. **(a) is done:** `IndistinguishingHalves B` (some `v` halves `c(X_T)` alone) `⟹ PotentialDrops B`,
  via `potentialDrops_of_indistinguishingHalves` — `k` rides free by `maxValency_mono`, so `2(k'−1)c' =
  (k'−1)(2c') ≤ (k−1)c`. Plus the seal capstone `reachesRigidOrCameron_viaShattering` carrying
  `IndistinguishingHalves`. All axiom-clean (`§CC.20` / `§S-gate2`). **This sharpens the open content from "the
  product halves" to "`c` halves"** (build doc §1B: `k` free, `c` the crux).
- **Stage 1b, the *discharge* (the heart, OPEN).** Prove `IndistinguishingHalves` for the residue: for any over-`B`
  base `T`, exhibit a `v` that halves `c(X_T)`. State `Shatters` as the structural condition — **"no surviving
  `c`-class" = "no partial-geometry line system"** (the probe's §5-Run-3 refinement: the obstruction is the
  line/grid geometry, not the smallest-eigenvalue magnitude). **Reuses:** `indistinguishingNumber`(`_mono`),
  `pointExtension`, the forced-triangle `interNum_eq_one_of_forcedUnique` (it *counts* the would-be line
  incidences). *Risk: medium-high* — the per-step split-counting is the genuine new combinatorics; row 4 (§3) is
  where it's hardest, though the line-system framing now suggests row 4 (non-geometric ⟹ no lines) *should* halve.
- **Stage 2 — discharge `Shatters` on the residue.** Carry Neumaier (geometric dichotomy) + the existing
  primitive-CC classification as hypotheses; prove `¬Shatters ⟹ geometric` (a `c`-class resisting every split is a
  partial-geometry line system), route geometric→Cameron, finite→trivial, conference→leg B. *Risk: high on row 4*
  (§3) — the uniform generic case (but see the line-system reframe above).
- **Stage 3 — assemble.** `Shatters (residue) → IndistinguishingHalves → PotentialDrops → O(log n) base → A1 →
  seal`, modulo the cited Neumaier/CGGP + G3 + carried `hcatch`/`hImprim`. The capstone
  `reachesRigidOrCameron_viaShattering` is the landed Stage-1b-reduction endpoint; Stage 2/3 discharge its
  `IndistinguishingHalves` hypothesis.

## 5. Evidence (the probe — full detail archived)

`A2MonovariantProbe.cs` (`Probe_CellSizeDropAcrossSRGs`, `Probe_ScalingResidueVsCarved`). Headline data:

| family | worst-drop vs `n` | base | reading |
|---|---|---|---|
| RESIDUE (Shrikhande, Clebsch, Chang×3) | `n16: 0.562, 0.667 · n28: 0.536,0.536,0.536` | 2–5 (non-√n) | bounded, non-climbing |
| CARVED lattice (rook `L(4..8)`) | `0.562,0.640,0.694,0.735,0.766` = `((m−1)/m)² → 1` | `m = √n` | the geometric obstruction |
| CARVED Johnson (`T(6,7,8)`) | `0.667,0.667,1.000` (T(8) stalls) | √-ish | geometric |
| CARVED conference (Paley) | `≈0.47` flat | 2 | non-geometric, leg B |

Paired twins (same parameters, residue strictly tamer): Shrikhande `b3` < rook `L(4)` `b4` @16; Chang `b2–4`
(C8: `28→15→1`) ≪ `T(8)` `b5`/stall @28. Full protocol + correction log (bare 2-rank does *not* separate the
cospectral pairs; the separator is the geometric/exceptional *structure*) in the archived probe doc.

**Probe follow-ups that would harden the route** (optional, construction-bottlenecked): hard-code 2–3 sporadic
residue SRGs at `n = 25–40` (Paulus `(25,12,5,6)`, the `(26,10,3,4)` family) — especially any with *growing*
smallest eigenvalue, to get a row-4 (generic) data point the current evidence lacks.

**Run 3 — the smallest-eigenvalue axis (`Probe_SmallestEigenvalueAxis`, 2026-06-15).** Built to attack the row-4 gap
directly, using the only constructible *controlled* growing-`|s|` family: Latin-square (net) graphs `L_g(m)` via cyclic
MOLS, which are geometric with smallest eigenvalue exactly `−g`, so sweeping `g` at fixed `n=m²` walks the `|s|`-axis.
**Two findings, the first a falsified hypothesis:**
- **F1 — worst-drop is NOT monotone in `|s|`.** On the geometric axis it *peaks at the rook/grid extreme* (`g=2`,
  `s=−2`, base `=√n`, drop 0.735 @n=49) **and** its complement (`g=m−1`, `s=−6`, same 0.735), and *troughs in the
  middle* (`L_4(7)`, `s=−4`, drop 0.500, base 3). Drop is symmetric under complementation (`g ↔ m+1−g`). **So the
  climb-toward-1 obstruction is the partial-geometry LINE/grid structure — a bounded-`s` (`s=−2`) phenomenon — not the
  magnitude of `|s|`.** This refutes the naive "growing `|s|` ⟹ climbs" reading of the §3 table.
- **F2 — the row-4 cell is empty among constructibles.** Every growing-`|s|` SRG buildable is geometric (net) or
  conference (leg B); all residue evidence sits at `|s| ≤ 3`. Non-geometric + high-`|s|` + small-Aut has no
  constructible witness (CGGP is the only known inhabitant) — the gap is confirmed with data, not closed.
- **Positive inference for the route (the useful part).** If the drop-obstruction is specifically the *partial-geometry
  line system* (a geometric feature), and row 4 is **by definition non-geometric** (no line system), then row 4 has no
  grid to stop the multiplicative split — heuristically it *should* shatter, supporting `PotentialDrops` on row 4. This
  reframes the Stage-1b `Shatters` predicate: key it on **"no partial-geometry line system"**, *not* "bounded `|s|`"
  (see §3).

## 6. Honest scope and failure modes

- **Could fail at row 4.** If the generic unbounded-`s` residue does *not* admit a uniform constant-factor drop
  (only the family-specific CGGP argument), the route degrades to a **ladder** (formalize CGGP as a rung) + the
  conditional-predicate floor — the outcome cxt-scoping §5 route 3 already banks.
- **A genuine counterexample** — a primitive, small, non-abelian, non-Cameron SRG with *no* fast-dropping
  potential (large base) — would falsify the seal (a statement change, itself a result). The 0-witness record +
  the probe's clean residue/carved split are the standing evidence against this.
- **`Shatters` precision risk.** Getting the predicate right (strong enough to give the drop, weak enough to hold
  off the geometric locus) is the crux of Stage 1; a too-strong predicate is a vacuity trap (cf. the project's
  history with `SchemeReproduced`).

## 7. Pointers

- **Stage 1a (LANDED):** `CoherentConfig.exists_potential_descent`, `potential`, `PotentialDrops`,
  `exists_small_base_of_potentialDrops`, `card_foldl_insert_le` (`CoherentConfig.lean §CC.20`);
  `reachesRigidOrCameron_viaPotentialDrop` (`CascadeAffine.lean §S-gate2`).
- Consumer / A1: `allSingletonFiber_of_card_gt_subset`, `dominatorReachable_of_card_gt_subset`,
  `reachesRigidOrCameron_viaBoundedExtensionParams` (`CoherentConfig.lean §CC.18/19`, `CascadeAffine.lean §S-gate2`).
- Potential ingredients: `CoherentConfig.indistinguishingNumber`(`_mono`), `maxValency`(`_mono`), `pointExtension`,
  `refines_pointExtension_of_subset`, `interNum_eq_one_of_forcedUnique` (`CoherentConfig.lean §CC.10/11/19`).
- Engine template to port: `exists_greedy_base_aux` / `exists_greedy_base_le_log` (`Cascade.lean`).
- Cited dichotomy (carry as hypotheses): `PrimitiveCCClassification` (G3, `Scheme.lean`); Neumaier + CGGP to be
  added the same way.
- Evidence: `GraphCanonizationProject.Tests/A2MonovariantProbe.cs`; archived plan
  `Archive/ChainDescent/chain-descent-a2-monovariant-probe.md`.
