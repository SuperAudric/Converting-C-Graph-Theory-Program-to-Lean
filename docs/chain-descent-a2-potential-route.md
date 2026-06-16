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
(`CascadeAffine.lean §S-gate2`). **[Historical — this paragraph is the Stage-1a/1b state; the §4c build-order is now
COMPLETE and the current state is the build-order paragraph below + §8.]** At that point the seal stood conditional
`modulo {G3 + IndistinguishingHalves + hcatch + hImprim}` — sharpened from `PotentialDrops` (the product `(k−1)c`
halves) to **`IndistinguishingHalves`** (the
indistinguishing number `c(X_T)` alone halves): `k` rides free by `maxValency_mono` (build doc §1B), and the
reduction `potentialDrops_of_indistinguishingHalves` makes that rigorous. So the *entire* open mathematical content
is now the single hypothesis **`IndistinguishingHalves`** (the drop lemma proper, `c`-form). The "geometric ⟹
Cameron" / "non-geometric" dichotomy that discharges it is carried as cited classification hypotheses (Neumaier +
the primitive-CC classification), never fresh axioms. **Honest scope:** research-scale, may not close; the residual
math gap is the generic (row-4) case — and the probe (§5 Run 3) refined it: the drop-obstruction is the
*partial-geometry line system*, not the smallest-eigenvalue magnitude. Quality bar held: axiom-clean `[propext,
Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned.

**The discharge is underway (the plan + build-order is §4c; READ IT to continue).** Landed axiom-clean: the
geometric-obstruction framework (`§CC.21`: `confusionSet`, the balanced/majority pigeonhole — *note*: that
balanced-splitter framing models the **1-WL cell**, the probe's object, not the 2-WL `c`; superseded by §CC.22), and
**★ the G-mech kill lemma (`§CC.22`: `relOf_v_eq_of_confused` + `confusionSet_eq_empty_of_relOf_v_ne`)** — a `v` that
*distinguishes* `α,β` annihilates `C(α,β)` in `X_{T∪v}`. So `c(X_{T∪v}) ≤ max{|C_{X_T}(α,β)| : v ∈ C(α,β)}`, and a
`v` outside all over-half confusion sets halves `c`. **Step 2 (the bound `indistinguishingNumber_pointExtension_insert_le`:
`c(W) ≤ M` if every `v`-undistinguished pair has `|C_{X_T}| ≤ M`) ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean)** —
proved via `Finset.sup_le` over non-reflexive `W`-classes, and it **dissolved the G-sim gap** (the single covering
hypothesis on `v` replaces the per-class splitter). **Step 3 (the halving wiring
`indistinguishingHalves_of_exists_avoiding_v`: `∃ v` avoiding all big confusion sets per over-`B` base `⟹
IndistinguishingHalves`) ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean)** — pure arithmetic instantiating the bound at
`M = c(X_T)/2`. **Step 4 (the `BigConfusionCover` obstruction: `BigConfusionCover` predicate +
`exists_avoiding_of_not_cover` + the capstone-facing `indistinguishingHalves_of_not_bigConfusionCover`) ✅ LANDED
(2026-06-15, `§CC.22`, axiom-clean).** **Step 5 (G-cite) ✅ LANDED (2026-06-15, the conditional capstone + non-vacuity,
axiom-clean; citations then SEPARATED to isolated literals):** the capstone `reachesRigidOrCameron_viaNoConfusionCover`
factors the dichotomy `cover ⟹ Cameron` — the **Cameron step reuses the canonical G3** `hClassify` (via
`exhaustiveObstruction_scheme`, no new carry); the only **new** citation is the **Neumaier direction** `hNeumaier :
(∃ T over-B, BigConfusionCover (X_T)) → IsLarge` (case-split: cover → `IsLarge` → primitive → G3 → Cameron / imprimitive
→ `hImprim`; no cover → `…viaShattering`) + the non-vacuity counting `card_bigClasses_mul_ge_of_cover` (`cover ⟹ n ≤
#bigClasses·c`, the explicit near-pencil structure). **The §4c build-order is COMPLETE (steps 1–5), and the citation is
sealed up.** The whole seal stands **`modulo {G3 (hClassify) + hNeumaier + hcatch + hImprim}`**. **★ Faithfulness scoped
(2026-06-16, §8):** `hNeumaier`'s faithful citation is **Babai's SRG structure theorem (rank 3) + Kivva (rank 4), NOT
"Neumaier"** (Neumaier is only the geometric-classification ingredient; "geometric ⟹ large Aut" alone is false — CGGP).
It is faithful **only at the sub-exponential largeness threshold** (where G3 + Babai's individualization bound hold); at
a *polynomial* threshold it is the **open rank-3 base case**. So the seal, at its established (sub-exp) citation
thresholds, gives **sub-exponential-base** "reaches rigid or Cameron"; polynomial is GI-adjacent open. `hcatch`'s target
is the `dimWL(X) ≤ dimWL(X_α)+1` exchange (CFI-1992 Thm 5.2); `hImprim` is project block-tower infra, not a citation. The
full citation map + what proving each takes is **§8**. The §CC.21 balanced-splitter defs are parked as the 1-WL-cell model.
**★ CITATION ADJUSTMENT — Phases 1–2 LANDED (2026-06-16, axiom-clean, build green; §8.5):** the **faithful-direction**
capstone `reachesRigidOrCameron_viaSmallAutShatters` now carries `hSmallAutDiscretizes : ¬IsLarge → ∀ over-`B` base,
¬BigConfusionCover` (= "small Aut ⟹ shatters", the literature-true Babai/Kivva direction) instead of the CGGP-false
`hNeumaier : cover ⟹ large`; fed by the citation-free bridge `not_bigConfusionCover_of_allSingletonFiber` (`complete ⟹
¬cover`, `§CC.22`). `…viaNoConfusionCover` (the `hNeumaier` form) kept, superseded. (Phase 3 — carry named `hBabaiBase` +
lift bridge to `cover ⟹ b(X)>B` — is now *deprioritized*: §8.6's research showed it only yields a sub-exp citation, not poly.)
**★★ RESEARCH PASS DONE + LIVE FRONTIER MOVED TO NODE 4 (2026-06-16; §8.6, §9).** The `B(n)` research (§8.6) pinned the
**threshold ladder**: polynomial is OPEN (rank-3 base case, not even conjectured), sub-exp `Õ(n^{1/3})` = Spielman (citable);
**no citation makes the seal polynomial.** So the poly side was decomposed by line-system structure into **five nodes (§9.0)** —
four carved/foreseeable, the open crux is **node 4** (a primitive, non-geometric, non-conference SRG). Anchor
**`reachesRigidOrCameron_viaNoCover`** (axiom-clean): **node 4 (`hShatter`) ⟹ polynomial seal, no largeness citation.** Best
handle = the **multiplicity reframe (§9.6):** node 4 ⟺ confusion-cover multiplicity `L=(Σ_{|C|>ρc}|C|)/n` bounded (computable;
high `L`=thick=Cameron carved, low `L`=poly via `1+L`-cleanup). **▶ PICK UP HERE — NEXT = the `N_ρ`/multiplicity PROBE (§9.7):**
measure `N_ρ`/`L_ρ`/`minMult_ρ`/mass-`Σ|C|²` on residue vs rook/Johnson across `ρ`+base; test "residue `L_ρ=O(1)` at constant
`ρ<1` while geometric families thick". Extends `A2MonovariantProbe.cs`. **Read §9 (esp. §9.0 nodes, §9.6 multiplicity, §9.7
probe) to continue.**

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

## 4b. The discharge — approaches, exact gaps, and the landed §CC.21 framework (2026-06-15)

Discharging `IndistinguishingHalves` for the residue is the genuine open heart. The mechanism, worked out: `c(X_T)`
is the size of the largest **confusion set** `C(α,β) = {γ : relOf γ α = relOf γ β}`; individualizing `v` partitions
`C` by the relation profile `γ ↦ relOf γ v`, and the question is whether some `v` brings the global-max confusion
down to `≤ |C|/2`.

**Three approaches:**
1. **Geometric dichotomy (main, matches the G3 pattern).** A class that *no* `v` can balance-split is seen
   monochromatically from everywhere — a partial-geometry **line system** (the `Probe_SmallestEigenvalueAxis`
   finding: the drop-obstruction is the line/grid geometry, *not* `|s|`). So `¬shatter ⟹ line system ⟹ geometric ⟹
   Cameron(large) ∨ finite-exceptional`; the residue (non-Cameron, not finite-exceptional) shatters.
2. **Balanced-splitter mechanics** — prove the bridge from a relation-profile balanced splitter to the actual
   `c`-halving in the coherent closure `X_{T∪v}`.
3. **Cited-bound floor** — cite `c(X_{T₀}),k(X_{T₀})=O(1)` for the rank-3/4 residue, use `…viaBoundedExtensionParams`.
   Not a discharge (cxt-scoping: not directly citable); the conditional floor.

**The exact gaps (Approach 1):**
- **G-mech (the open Lean core).** "balanced relation-splitter at `v` ⟹ the class's confusion halves in `X_{T∪v}`."
  Confirmed there is **no monotonicity shortcut**: `c(X_{T∪v})` has no upper bound but `c(X_T)`; beating `c/2` *must*
  use the coherent closure's forced-triangle propagation (the δ′ machinery — `interNum_eq_one_of_forcedUnique`,
  `Sharp`). This is the genuine new combinatorics and the hardest piece.
- **G-sim (simultaneity).** One `v` must balance-split *all* near-max classes at once (classes already `≤ c/2` ride
  free by per-class monotonicity). The pigeonhole gives per-class splitters; simultaneity is extra structure.
- **G-cite (cited).** "near-pencil line system ⟹ Cameron ∨ finite-exceptional" — Neumaier + the primitive-CC
  classification (G3), carried as theorem-statement hypotheses, never `axiom`s.

**Landed this session — the §CC.21 framework (the CC-intrinsic core of Approach 1, all axiom-clean):**
`confusionSet`, `BalancedSplits` / `MajorityRelation` (the relation-profile split vs monochromatic view),
`balancedSplits_or_majority` (the dichotomy), **`majority_fibers_inter`** (the intersecting-majority pigeonhole —
two monochromatic views overlap, the **near-pencil** structure that *is* the partial-geometry line system, the
combinatorial heart), `GeometricObstruction` (the obstruction predicate at scale `B`), and
`exists_balancedSplits_of_not_forall_majority` (no obstruction ⟹ a balanced splitter exists). This proves the
combinatorics that says "the drop-obstruction is a line system" and gives the predicate the cited Neumaier/Cameron
dichotomy (G-cite) attaches to.

**What remains (clearly isolated):** (i) **G-mech** — the closure-halving mechanics; (ii) **G-sim** — simultaneity;
(iii) **G-cite** — carry Neumaier + G3 and route the residue out.

> **⚠ CORRECTION (2026-06-15, from planning G-mech — supersedes the §CC.21 "balanced-splitter" framing above).**
> Working out the *coherent-closure* mechanism (§4c) showed the §CC.21 primitives (`BalancedSplits` /
> `MajorityRelation` / `majority_fibers_inter`) model the wrong object for the **2-WL** indistinguishing number `c`:
> individualizing `v` does **not** split `C(α,β)` into relation-to-`v` fibers. Those primitives correctly model the
> **1-WL cell** split (what the *probe* measured) — keep them for a future cell-potential, but the `c`-route's G-mech
> is the **kill lemma** of §4c, not balanced-splitting. §CC.21 is to be repurposed/replaced accordingly.

## 4c. G-mech, corrected: the kill lemma (the clean, provable heart)

**The actual closure mechanism.** Let `W = pointExtension X (insert v T)` (so `v` is a singleton fiber of `W`, and
`W` refines `X_T`). For a pair `(α,β)`, the `W`-confusion is `{γ : relOf_W γ α = relOf_W γ β}`. The key fact:

> **Kill lemma.** If `v` is a singleton fiber of a CC `W` and `relOf_W v α ≠ relOf_W v β`, then the `W`-confusion of
> `(α,β)` is **empty**.

*Proof (interNum coherence + singleton isolation; no construction internals, no tower lemma).* Suppose `γ` is
`W`-confused: `relOf_W γ α = relOf_W γ β =: c'`. For the first-coordinate class `a := relOf_W γ v`, the filter
`{z : relOf_W γ z = a ∧ relOf_W z α = b}` forces `z = v` (since `relOf_W γ z = relOf_W γ v ⟹` (by
`relOf_diag_right_eq`) `z, v` share a reflexive class `⟹` (SingletonFiber `v`) `z = v`), so its card is `[b = relOf_W
v α]`; by `interNum_eq` this card is `interNum a b c'`. The same computation on `(γ,β) ∈ c'` gives `interNum a b c' =
[b = relOf_W v β]`. Hence `[b = relOf_W v α] = [b = relOf_W v β]` for all `b`, so `relOf_W v α = relOf_W v β` —
contradiction. ∎ (Provable with `inter_card_eq` / `interNum_eq` / `relOf_diag_right_eq` / `SingletonFiber`, the
`sharp_pointExtension` toolkit; ~30–40 lines.)

**The corrected G-mech chain.** `v` distinguishing `(α,β)` (`relOf v α ≠ relOf v β`, i.e. `v ∉ C_{X_T}(α,β)`) **kills**
that pair's confusion in `W`. Every surviving `W`-class came from a pair `v` does *not* distinguish, whose `W`-confusion
`⊆ C_{X_T}(α,β)` (monotone). So
> `c(W) ≤ max { |C_{X_T}(α,β)| : (α,β) non-reflexive, v ∈ C_{X_T}(α,β) }`.
Hence **`IndistinguishingHalves` at `T` follows from: ∃ `v` lying in NO confusion set of size `> c(X_T)/2`** — then every
surviving pair has `|C| ≤ c/2`, so `c(W) ≤ c/2`, i.e. `2·c(W) ≤ c(X_T)`.

**The corrected obstruction (G-cite).** No such `v` ⟺ the *big* confusion sets (`|C(α,β)| > c/2`) **cover `Fin n`**.
A cover forces `n ≤ (#big pairs)·c`, i.e. ≥ `n/c` near-maximal confusion sets — a partial-geometry / near-pencil
structure, which Neumaier + the primitive-CC classification (cited) route to `Cameron ∨ finite-exceptional`. The residue
(non-Cameron, not finite) therefore admits a good `v` and shatters. (Note: big confusion sets need *not* pairwise
intersect — they live in `Fin n`, not a size-`c` universe — so the `majority_fibers_inter` pigeonhole does **not**
transfer; the covering count replaces it.)

**Build order (G-mech implementation):**
1. **Kill lemma — ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean).** `relOf_v_eq_of_confused` (the core, singleton-fiber
   isolation + `interNum_eq`) and `confusionSet_eq_empty_of_relOf_v_ne` (the kill lemma: `v` distinguishes `(α,β)` ⟹
   `C(α,β)=∅`). The genuine new content; built first.
2. **The bound — ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean).** `indistinguishingNumber_pointExtension_insert_le`:
   if every pair `(α,β)` (`α≠β`) that `v` fails to distinguish in `X_T` has `|C_{X_T}(α,β)| ≤ M`, then `c(W) ≤ M`.
   Proved via `Finset.sup_le` over the non-reflexive `W`-classes (cleaner than the planned `Finset.exists_mem_eq_sup`
   extraction — bounds every class directly): per class, the kill lemma (`v` a singleton fiber of `W` from
   `isPointExtension_pointExtension`) empties the confusion of pairs `v` distinguishes, else `confusionSet_W ⊆
   confusionSet_{X_T}` (monotone via `refines_pointExtension_of_subset`) lands it in the `≤ M` hypothesis.
   **This dissolved the G-sim (simultaneity) gap:** the single covering hypothesis on `v` (`∀` undistinguished pair
   `≤ M`) replaces the per-class splitter, so the old §4b "one `v` balance-splits all near-max classes" worry is gone.
3. **The halving wiring — ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean).** `indistinguishingHalves_of_exists_avoiding_v`:
   if every over-`B` base `T` admits a `v` avoiding all big confusion sets (every `v`-undistinguished pair has
   `2·|C_{X_T}| ≤ c(X_T)`), then `IndistinguishingHalves B`. Pure arithmetic: instantiate the step-2 bound at
   `M = c(X_T)/2` (the avoiding hypothesis gives `|C| ≤ c/2` per undistinguished pair), giving `c(W) ≤ c(X_T)/2`, i.e.
   `2·c(W) ≤ c(X_T)`; `omega` closes it. **The whole open content is now exactly the existence of the avoiding `v`** —
   its negation is the covering obstruction (step 4).
4. **The `BigConfusionCover` obstruction — ✅ LANDED (2026-06-15, `§CC.22`, axiom-clean).** `BigConfusionCover`
   (the `>c/2` confusion sets cover `Fin n`: `∀ v, ∃ α≠β, c(X) < 2·|C(α,β)| ∧ v∈C(α,β)`); `exists_avoiding_of_not_cover`
   (`¬BigConfusionCover ⟹ ∃ v avoiding`, via `not_forall` + `not_le`, feeding step 3); and the capstone-facing wiring
   `indistinguishingHalves_of_not_bigConfusionCover` (`∀T over-B, ¬BigConfusionCover (X_T) ⟹ IndistinguishingHalves B`,
   composing it with step 3). `confusionSet` kept; the §CC.21 balanced-splitter primitives parked as the 1-WL-cell model
   (left in place, documented as superseded — not deleted). **This packages the entire open content of A2 as one
   predicate on the extension: `¬ BigConfusionCover (X_T)`.**
5. **G-cite + capstone — ✅ LANDED (2026-06-15, the conditional capstone + non-vacuity, axiom-clean).** Two parts:
   - **The capstone `reachesRigidOrCameron_viaNoConfusionCover`** (`CascadeAffine.lean §S-gate2`), with the two citations
     **separated to isolated literals** (the "seal up the citation" pass): the dichotomy `cover ⟹ Cameron` is *factored*
     rather than carried as one composite. The **Cameron step reuses the canonical G3** `hClassify` (via
     `exhaustiveObstruction_scheme`, no new carry); the only **new** citation is the **Neumaier direction** `hNeumaier :
     (∃ T over-B, BigConfusionCover (X_T)) → IsLarge`. `by_cases` on the cover: cover → `hNeumaier` → `IsLarge`, then
     primitive → cited G3 → Cameron / imprimitive → `hImprim` recovers; no cover →
     `indistinguishingHalves_of_not_bigConfusionCover` → `…viaShattering`.
   - **The non-vacuity counting `card_bigClasses_mul_ge_of_cover`** (`CoherentConfig.lean §CC.22`): `BigConfusionCover X
     ⟹ n ≤ (bigClasses X).card · c(X)`, i.e. a cover forces `≥ n/c` near-maximal confusion classes — the explicit
     near-pencil / partial-geometry line system, proving `BigConfusionCover` is a genuine geometric condition (not the
     conclusion in disguise; the vacuity-trap guard).

**The §4c build-order is COMPLETE (steps 1–5 landed, axiom-clean), and the citation is sealed up.** The whole seal now
stands **`modulo {G3 (hClassify) + Neumaier (hNeumaier) + hcatch + hImprim}`**, where **each citation is now a single
isolated literal external theorem** — G3 = Babai/Sun–Wilmes (large primitive ⟹ Cameron, the project's canonical carry),
Neumaier = (geometric/near-pencil ⟹ large Aut). This is the target shape for the longer-term goal of *replacing each
citation with its Lean proof*: each is independently formalize-able, and the provable counting (5b,
`card_bigClasses_mul_ge_of_cover`) already bridges `cover → near-pencil`. **The sole remaining mathematical risk is
`hNeumaier`'s faithfulness on row 4** (generic non-geometric, unbounded `s`), where the cited geometric step is
non-portable (CGGP only) — but the probe reframe (§5 Run 3) says row 4 has no line system, hence no cover (it shatters
into the `¬cover` branch). Closing that unconditionally is the open research; the conditional capstone is the honest
floor (cxt-scoping §5 route 3), with the open content sharpened from "prove `IndistinguishingHalves`" (an open
conjecture) to two isolated established citations.

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

## 8. Sealing the citation — `hNeumaier` faithfulness + what proving it would take (2026-06-16)

> **Why this section exists.** Step 5 carries `hNeumaier : (∃ T over-B, BigConfusionCover (X_T)) → IsLarge`. The
> "seal up the citation" pass asked whether this is a *faithful literal* external theorem. **Verdict: it is — but
> only at the sub-exponential largeness threshold, and it is NOT "Neumaier."** This pins what the citation actually
> is, the genuine threshold ambiguity, and the work each resolution would take.

### 8.1 The full map of what the seal carries (all four, with their citation targets)
| Carried | What it is | Citation target / status |
|---|---|---|
| `hClassify` (G3) | large primitive ⟹ Cameron | **Babai 1981 / Sun–Wilmes 2015** — the project's canonical carry (sub-exp threshold). |
| `hNeumaier` | cover ⟹ `IsLarge` | **Babai's SRG structure theorem (rank 3) + Kivva JCTB'23 (rank 4)** — §8.2 (NOT Neumaier alone). |
| `hcatch` | `WarmTwinsAreFiberTwins` (1-WL↔2-WL) | **`dimWL(X) ≤ dimWL(X_α)+1`, Cai–Fürer–Immerman 1992 Thm 5.2** (= eq. (41) in Ponomarenko arXiv:2006.13592; Chen–Ponomarenko CC monograph §4.2). Citable or provable; *free* at n=16 (`warmTwinsAreFiberTwins_of_dominatorClosure`). |
| `hImprim` (G2-A) | imprimitive ⟹ recovered | **Not a citation** — project block-tower infra (reduces to the primitive case via ≤ log n layers; machinery ~80% landed, recursion unbuilt). |

### 8.2 What `hNeumaier` actually is (not Neumaier alone)
`hNeumaier` reads *"a scheme whose extension resists discretization at a bounded base is large."* Its faithful
citation is **not** Neumaier's theorem — Neumaier classifies geometric SRG *parameters* into partial geometries and
says **nothing about Aut**. The honest chain is **Babai's SRG structure theorem** (cxt-scoping §4.2):
> a primitive SRG (n ≥ 29) is *large-motion* (≥ n/8; small Aut — the residue) **or** a named geometric family
> (triangular/Johnson `T(m)`, lattice/Hamming `L₂(m)`) of thickness `≥ √n`, hence **large Aut** → Cameron (G3);
> rank-4 amorphic via **Kivva (JCTB'23)**.

Neumaier's claw bound is only the *ingredient* that makes the named families geometric. **"geometric ⟹ large Aut"
alone is false** — a generic partial geometry / the CGGP construction has trivial Aut. The "⟹ large Aut" comes from
the *named families' thickness*, via Babai's structural dichotomy. The bridge the cover supplies (partly landed):
`cover` ⟹ (`card_bigClasses_mul_ge_of_cover`) `≥ n/c` near-maximal confusion classes = a **rigid line system** ⟹
the scheme is **not large-motion** ⟹ (Babai) a named family ⟹ large Aut. The first `⟹` (cover ⟹ ¬large-motion) is
the genuinely-new bridge — spectral SRG theory linking "resists bounded-base individualization" to "small motion."

### 8.3 The faithfulness verdict — threshold-bound (the genuine ambiguity)
- **At the SUB-EXPONENTIAL largeness threshold** (`IsLarge` = `|Aut| > exp(Õ(n^{1/3}))`, where Babai/Sun–Wilmes G3
  *and* Babai's individualization bound hold): `hNeumaier` is a **faithful CFSG-based citation**. Large-motion ⟹
  base ≤ quasipoly ≤ B ⟹ no cover; so cover ⟹ named family ⟹ large. The seal then gives **sub-exponential-base**
  "reaches rigid or Cameron."
- **At a POLYNOMIAL threshold** (what GI ∈ P needs): `hNeumaier` is **not established**. A large-motion (small-Aut)
  SRG could have base between poly and quasipoly — a cover while small-Aut — falsifying it. This is the **open rank-3
  base case** (cxt-scoping §5 route 2): *"primitive large-motion non-conference SRG ⟹ b(X) = O(log n)."* **CGGP**
  (arXiv:2312.00460: `n^Ω(n^{2/3})` trivial-Aut SRGs, all WL-dim ≤ 4) is the strongest positive evidence (small Aut →
  bounded WL-dim for *that family*), but a universal theorem is unproven.

So the **ambiguity is real and is exactly the sub-exp-vs-poly threshold** — the build-doc §1B(4) calibration caveat,
now localized to `hNeumaier`. At the citable (sub-exp) threshold the seal is honest and faithful; the polynomial
version's faithfulness *is* the open conjecture. **This also means the whole seal is sub-exponential, not polynomial,
at the established citation thresholds** (G3 is itself sub-exp); polynomial canonisation needs the poly thresholds of
*both* G3 and `hNeumaier`, which are GI-adjacent open.

### 8.4 What proving `hNeumaier` would take
1. **As a faithful citation (sub-exp; the realistic next "seal up the citation" step).** Carry **Babai's SRG
   structure theorem** (rank 3) + **Kivva** (rank 4) as named hypotheses (the G3 pattern — they rest on CFSG, so
   formalizing them from scratch is infeasible but citing them is legitimate). Then **prove the bridge**
   `cover ⟹ ¬large-motion` — the new content: connect the `bigClasses` confusion-cover count to the graph's
   motion / spectral gap (the cover's `≥ n/c` rigid lines force a small-support automorphism, i.e. ¬large-motion).
   Bounded Lean work on SRG spectral theory. Outcome: `hNeumaier` becomes `{Babai-SRG-structure + Kivva + a proved
   bridge}`; the seal is sub-exponential, `modulo {G3 + Babai-SRG + Kivva + CFI-exchange}` — every carry a literal
   theorem, the user's "exactly citable" target reached for this leg.
2. **As an unconditional (poly) theorem.** Prove the rank-3 base case — *"primitive small-Aut / large-motion SRG has
   poly WL-dim / base."* **Open research** (resolving it is a chunk of GI ∈ P for SRGs); Babai's bound is quasipoly,
   no portable poly proof exists. CGGP is the positive anchor; row-4 (generic non-geometric) is hardest. This is the
   long-horizon goal, not a near-term build.

**Recommendation.** Target (1): correctly attribute and factor `hNeumaier` into Babai's SRG structure theorem + Kivva
+ a *provable* `cover ⟹ ¬large-motion` bridge. It makes the citation honest (it is not "Neumaier"), isolates a real
Lean target (the bridge), and matches the project's established sub-exponential scope. (2) is the open rank-3 math.

### 8.5 Step 1 build plan — factor `hNeumaier` into faithful citations (the recommended next build)

**Goal.** Replace the monolithic `hNeumaier : (∃ T over-B, BigConfusionCover (X_T)) → IsLarge` with {named Babai/Kivva
citations} + {a provable project bridge}, so **every carried piece is one literal external theorem** (the "exactly
citable" target) — honestly at the **sub-exponential** largeness threshold.

**The recommended factoring — via the base number `b(X)`.** The cleanest pivot is the base number (a WL/combinatorial
quantity Babai's individualization bound directly controls, and one the project already has: `IsBase` / "X_T complete").
It separates the *provable* project content from the citation:
- **Citation (Babai SRG structure + Kivva), in pure base/Aut terms:**
  `hBabaiBase : ¬ IsLarge n S → S primitive → S.rank ≤ 4 → ∃ T, |T| ≤ B(n) ∧ (X_T complete)`
  — *"a primitive small-Aut SRG (rank-3 Babai / rank-4 Kivva) has a bounded base."* This is the contrapositive of
  `large base ⟹ large Aut`, and the faithful restatement of {Babai's SRG structure theorem (small Aut ⟹ large-motion,
  since the named geometric families are large-Aut) + Babai/Spielman SRG individualization (large-motion ⟹ `b(X) ≤ B(n)`)}.
- **Provable bridge (project — the genuine new Lean content):**
  `cover ⟹ b(X) > B` — a `BigConfusionCover (X_T)` means a `>c/2` confusion class survives ⟹ `X_T` not discrete ⟹ `T`
  not a base; lifted over all `|T| ≤ B` ⟹ no `≤B` base exists ⟹ `b(X) > B`. Built **contrapositively from the landed A1
  machinery** (`allSingletonFiber_of_card_gt_subset` / `DominatorReachable`): a complete `X_T` has no surviving confusion
  class, so `cover ⟹ ¬complete`.
- **Compose:** `cover ⟹ b(X) > B ⟹` (contrapositive of `hBabaiBase`) `IsLarge` `= hNeumaier`.

**★ PHASES 1–2 LANDED (2026-06-16, axiom-clean, build green) — the citation-independent half is done.**
- **Phase 1 (sub-task 3 — the provable bridge) ✅** `CoherentConfig.confusionSet_eq_empty_of_allSingletonFiber`
  (`complete ⟹ empty confusion sets`, via `relOf_diag_right_eq` + `SingletonFiber`) + **`not_bigConfusionCover_of_allSingletonFiber`**
  (`complete ⟹ ¬BigConfusionCover` = `cover ⟹ ¬complete`), both `§CC.22`. The load-bearing, citation-free heart of the
  factoring — no `B(n)` needed.
- **Phase 2 (the faithful-direction capstone) ✅** `reachesRigidOrCameron_viaSmallAutShatters` (`CascadeAffine.lean §S-gate2`)
  carries `hSmallAutDiscretizes : ¬IsLarge → ∀ over-`B` base, ¬BigConfusionCover(X_T)` (= "small Aut ⟹ shatters", the
  **literature-true** Babai/Kivva direction) and `by_cases` on the genuine `IsLarge` dichotomy. Contrapositive of `hNeumaier`
  so no weaker; the gain is a faithfully-stated, *derivable* citation (the old "cover ⟹ large" direction is CGGP-false and
  not derivable from Babai). This is the **Fallback Option B landed as a sibling** — `…viaNoConfusionCover` kept, marked superseded.
- **Phase 3 (REMAINING, gated on sub-task 1):** factor `hSmallAutDiscretizes` further into {`hBabaiBase` named citation + the
  Phase-1 bridge + the base-number lift}. Blocked on pinning `B(n)` (sub-task 1 below).

**Concrete sub-tasks (in order).**
1. **[VERIFY FIRST — gating] Pin the exact Babai SRG individualization bound + threshold `B(n)`.** Is it `Õ(√n)`?
   quasipoly `exp(Õ(n^{1/3}))`? (Babai SRG iso / Spielman / Babai–Wilmes; Kivva JCTB'23 for rank 4.) This sets the
   seal's actual base/cost regime and `hBabaiBase`'s faithful statement. **Do NOT build until pinned** — candidate for a
   focused deep-research pass (the project's A2-research established the *structure* theorem but not the exact individualization bound).
2. **State the citations** as named `Prop`s (the G3 pattern; `Scheme.lean` or `CascadeAffine.lean`), parametrized by the
   largeness predicate + threshold. Never a fresh `axiom`.
3. **Prove the bridge** `BigConfusionCover (X_T) ⟹ ¬ (X_T complete)` (then the `b(X) > B` lift) from the landed A1
   machinery. The genuine new content; moderate.
4. **Re-assemble** `reachesRigidOrCameron_viaNoConfusionCover` to carry `hBabaiBase` instead of `hNeumaier`, routing
   cover → `b(X) > B` → `IsLarge` → G3 → Cameron. Axiom-clean.
5. **Verify** axiom-clean + build green; regen `PublicTheoremIndex.md`; update STATUS + this doc.

**Risks / honesty.**
- **Fallback (Option B) if the base-number bridge is awkward:** carry the single renamed citation
  `hSmallAutDiscretizes : ¬IsLarge → (∀ T over-B, ¬ BigConfusionCover (X_T))` (= "small Aut ⟹ shatters"), documented as
  the Babai composite. Cleaner than `cover → IsLarge`, still one honest citation, **no base-number infra** — a strictly
  smaller build than the full factoring, and a safe first landing.
- Even fully done, the seal stays **sub-exponential** (B(n) is sub-exp); polynomial is Target 2 (the open rank-3 base case).
- Sub-task 1 (the exact bound) is the gating unknown — verify before building.

**Outcome.** `hNeumaier` replaced by {Babai SRG structure + Kivva + a proved cover→base bridge}; seal
`modulo {G3 + Babai-SRG-structure + Kivva + CFI-exchange + hImprim}`, every carry a literal theorem — the "exactly
citable" target reached for the geometric leg, honestly at the sub-exponential threshold.

### 8.6 Research pass (2026-06-16): `B(n)` pinned + corrected citations + the threshold ladder

A 3-angle web-grounded deep-research pass (structure/motion · individualization bounds · WL-dimension) + an Eberhard
verification ran the sub-task-1 gate. **Verdict: `B(n)` is pinned, and it confirms the seal is sub-exponential, with the
polynomial version genuinely OPEN (no citation, no conjecture).**

**The threshold ladder (the headline — `B(n)` is not one number, it is three regimes):**
| Base budget `B` | What discretizes the residue at `\|T\| ≤ B` | Status / citation |
|---|---|---|
| **Polynomial** `O(log n)` (the GI∈P target) | the WL-realization of the `O(log n)` group base | **OPEN — the rank-3 base case.** No theorem, *no conjecture even exists* (CGGP: community had no such expectation; CFI/FDF make it false in general). |
| **Quasipolynomial** (`O(log n)` *group* base) | Babai/Kivva motion ⟹ large-motion ⟹ `b(Aut)=O(log n)`; but `X_T` **complete** needs WL-realization | group base proven; the WL step is the **same open gap**. |
| **Sub-exponential** `Õ(n^{1/3})` | **Spielman**: every primitive SRG individualizes-and-refines to discrete at `Õ(n^{1/3})` | **PROVEN & citable** (Spielman, STOC 1996). |

**The reframing that matters for next steps.** At `B = Õ(n^{1/3})` Spielman discretizes *every* primitive SRG, so
`hSmallAutDiscretizes` holds **unconditionally** (the cover branch is vacuous, everything shatters) — the seal is honestly
sub-exponential **but then subsumed by Spielman**, and the whole "or Cameron" / largeness machinery is unnecessary. The
Cameron carve-out is **load-bearing only at the polynomial threshold**, where the citation *is* the open rank-3 base case.
**So no citation makes the seal polynomial — that is the open frontier; `hSmallAutDiscretizes`/`hNeumaier` at sub-exp = carry
Spielman (Cameron-trivial); at poly = open.** Phase 3 ("carry a named citation") therefore changes the seal's *honesty*,
not its *scope*: the citation is now exactly scoped, and building it is optional.

**Pinned citations (corrected — apply these):**
- **Babai SRG structure theorem (rank 3):** *motion ≥ n/8, OR X / X̄ is triangular `J(s,2)` / lattice `H(2,s)` / disjoint
  equal cliques*; `n ≥ 29`, threshold **exactly n/8**. **L. Babai, "On the automorphism groups of strongly regular graphs
  I", ITCS 2014** (DOI 10.1145/2554797.2554830) + Part II, J. Algebra 421 (2015) 560–578. **NOT STOC.** Clean restatement:
  Kivva arXiv:1912.11427 Thm 1.2.
- **Kivva (rank 4):** *motion ≥ γ₄·n, OR Johnson scheme, OR Hamming scheme* — a **MOTION bound, NOT a WL-dim bound and NOT
  an amorphic classification** (correcting the old "rank-4 amorphic" gloss). **JCTB 164 (2024) 245–298**, DOI
  10.1016/j.jctb.2023.09.006, arXiv:2110.13861. **Print year 2024, not 2023.**
- **"geometric ⟹ large Aut" is FALSE — fully vindicates the Phase-2 direction-flip.** Large Aut comes from the **named-family
  identification** (Johnson/Hamming, thickness `Ω(√n)`, routed via Cameron/Maróti), *not* from generic geometricity; Neumaier
  is only the geometric-classification ingredient. Fon-Der-Flaass (Adv. Geom. 2002, trivial Aut) + CGGP confirm.
- **CGGP:** authors are **Cai, Guo, Gavrilyuk, Ponomarenko** (arXiv:2312.00460, Combinatorica 2025) — WL-dim ≤ 4 for the
  Fon-Der-Flaass *affine* family (**SPECIFIC, not universal**; the base-≤2 step cites BCN Thm 3.3.8). The "trivial Aut" is
  the Fon-Der-Flaass family's, not a stated CGGP property (CGGP's `Aut` use = the 2-point extension is discrete).
- **Spielman**, STOC 1996, `exp(Õ(n^{1/3}))`, base `Õ(n^{1/3})`; **Babai 1980** (SIAM J. Comput.) `exp(Õ(√n))`;
  **BCSTW**, FOCS 2013, `exp(Õ(n^{1/5}))` canonical forms. **Motion–base lemma** `b(G) ≤ (n/m)·log n` (Babai 1981 / Maróti
  survey, Arch. Math. 2023): large-motion ⟹ group base `O(log n)`. **Schneider–Schweitzer**, ICALP 2025: WL-dim `≤ 0.15n`
  universal — linear, useless for polynomiality (confirms the only universal bound is linear).

**Eberhard risk — DISMISSED for the schurian seal (but sharpens the threshold).** Sean Eberhard, "Hamming sandwiches"
(arXiv:2203.03687, Combinatorica 2023) refutes Babai's combinatorial Cameron conjecture with primitive PCCs of rank 28,
`|Aut| ≥ exp(n^{1/8})`, small motion — but they are **explicitly NON-SCHURIAN** (imprimitive Aut). The project's residue is
schurian (`orbitalScheme H`), and `hClassify` (G3) is stated over `SchurianScheme`, so Eberhard does **not** touch the seal.
It *does* confirm the largeness threshold must be the **Sun–Wilmes `exp(n^{1/3})`** level AND schurian: the combinatorial
version is false at `exp(n^{1/8})` even with large Aut counts.

**Impact on next steps (see the reply / STATUS):** the citation is now *exactly scoped*; the genuine remaining frontier is
the **open rank-3 base case** (polynomial WL-realization of the `O(log n)` motion base — GI-adjacent, uncited, unconjectured).
Phase 3 options: **(a)** carry Spielman → a fully-citable sub-exp "honest floor" capstone (Cameron-free, subsumed by known
results); **(b)** carry Babai/Kivva motion + leave the WL-realization as the open gap (poly-aspirational, the gap = the open
case); **(c)** hold — the citation is scoped, redirect to `hImprim` discharge or the open rank-3 research.

---

## 9. Node 4 — anatomy of the open polynomial crux (the forced-triangle frontier)

> **What this is.** The forced-triangle scope (§9.0) decomposes the polynomial side by **line-system structure**
> into five nodes; four are carved or template-able and the open crux is **node 4**. This section lists the nodes
> (§9.0), then dissects node 4 — in simple terms, precisely, the gaps, the handles — so it can be worked. The
> seal-level anchor is `reachesRigidOrCameron_viaNoCover` (`CascadeAffine §S-gate2`, axiom-clean): the poly seal
> carrying node 4 as a single hypothesis, **no largeness citation.**

### 9.0 The five nodes (the poly-side decomposition by line-system structure)

The probe's reframe (the obstruction is the *partial-geometry line system*, not `|s|`) splits the residue along
Neumaier's smallest-eigenvalue classification. `c(X_{T₀})` stays large iff a **line system** (a "grid" of confusion
classes) survives individualization. The crucial structural win: **non-Cameron ⟹ not a *thick* line system ⟹
thin-or-no line system ⟹ poly-capable** — the only non-poly leg (thick) is exactly Cameron, which the residue
excludes by hypothesis. The five nodes:

| # | Residue structure | `c(X_{T₀})` bounded? | Status / route |
|---|---|---|---|
| **1** | **Thick line system** (Johnson/Hamming, lines of size →∞) | no — base √n | **Cameron** → landed **G3** (`exhaustiveObstruction_scheme`). *Excluded from the residue by hypothesis.* |
| **2** | **Thin line system** (geometric, bounded thickness — FDF/affine) | yes, base `O(1)` | **CGGP/BCN template** (`base ≤ 2 ⟹ WL-dim ≤ 4`, BCN Thm 3.3.8). FORESEEABLE; landed vehicle = `RainbowRigid` / `dominatorReachable_of_rainbowRank` (`clebschZ4_closure` is the proof-of-concept). *Ladder risk* (per geometry type). |
| **3** | **No line system, bounded `m`** (Neumaier-exceptional) | yes (finite list) | **Neumaier finiteness** ⟹ max `c` over a finite set = const. FORESEEABLE/citable. |
| **4** | **No line system, unbounded `m`, non-conference** ("row 4") | probe: yes; **no proof** | **THE OPEN POLY CRUX.** No template, no witness, not even a conjecture. §9.1–§9.6 below. |
| **5** | **Conference** (irrational `m`) | — | **abelian / leg B** (`AbelianConsumed`). Landed. |

Nodes 1, 5 are landed/carved; nodes 2, 3 are foreseeable buildable legs that would shrink the seal to node 4 (the
bounded-`m` cases); **node 4 is the irreducible frontier.** Closing nodes 2+3 lands the seal `modulo {G3-for-Cameron +
leg B + node-4 crux + hImprim}`. Full foreseeability discussion: the §8.6 / scope reply; this §9 dissects node 4.

### 9.1 The problem in simple terms

Pin a few vertices of the graph, run colour refinement, hope every vertex ends up uniquely coloured (rigid). The
**confusion number** `c(X_T)` = how many vertices still look identical after pinning `T` and refining. We want it to
drop to a *constant* after pinning a *constant* number of vertices (then A1 finishes).

The mechanism is a **chain reaction.** Pin two vertices `α, β`. A third vertex `γ` that relates *differently* to them
gets distinguished. A `γ` that relates *identically* is "confused" — it lies in the confusion set `C(α,β)`. The **kill
lemma** (`§CC.22`) says: pinning a vertex `v` that *distinguishes* a confused pair wipes out their whole confusion set.
So if we can find a vertex `v` that distinguishes *every* near-maximally-confused pair (a "**`c/2`-avoiding `v`**"),
pinning it **halves** `c`. Repeat ⟹ rigid in `O(log n)` pins ⟹ polynomial.

The **obstruction**: maybe *no* single vertex distinguishes all big confused pairs — the big confusion sets **cover**
all vertices (every vertex is confused about some near-maximal pair). That is a `BigConfusionCover`. **Node 4 claims a
non-geometric primitive SRG never develops such a cover** (an avoiding `v` always exists). The intuition: a cover is a
*tiling of the graph by near-maximal confusion sets* — and that tiling **is** a geometric "line system" (a grid /
partial geometry). A non-geometric graph has no line system, so no cover. The probe (`Probe_SmallestEigenvalueAxis`)
confirmed the obstruction is exactly the line/grid geometry, peaking at the rook graph, not at large `|s|`.

### 9.2 Node 4, precisely (the project's language)

> **Node 4 (`hShatter`):** for the residue, `∀ T` with `Φ(T) > B`, `¬ BigConfusionCover (X_T)` — equivalently, every
> over-`B` base admits a `v` outside all confusion sets of size `> c(X_T)/2`.

`reachesRigidOrCameron_viaNoCover` proves **node 4 ⟹ polynomial seal** (modulo `{G3 + hcatch + hImprim}`, G3 unused on
the shattering path). So node 4 is the *entire* open polynomial content, stated with **no largeness/Cameron/Babai/Spielman
citation** — the honest poly target.

### 9.3 The gaps node 4 carries

- **Gap 1 — the propagation: ✅ LANDED.** avoiding `v` ⟹ `c` halves (`indistinguishingHalves_of_exists_avoiding_v`) ⟹
  `O(log n)` base, `c=O(1)` (`exists_potential_descent`) ⟹ poly (A1). Nothing open here.
- **Gap 2 — the crux: prove `¬BigConfusionCover` for the residue.** Its negation, by `card_bigClasses_mul_ge_of_cover`,
  is a covering of `Fin n` by `≥ n/c` near-maximal confusion classes (each of size in `(c/2, c]`) — a partial-geometry /
  near-pencil **line system**. So Gap 2 = *"a primitive non-geometric non-conference SRG has no such covering."* This is
  the irreducible open content (the rank-3 base case), and it splits:
  - **2a — the extremal/tight cover (partition case): a HANDLE, scoped.** If the cover is *tight* (`#bigClasses·c ≤ n`,
    forcing equality with the landed `≥`), the big classes **partition** `Fin n` into equal Aut-invariant blocks. Since
    `Aut` permutes confusion sets (`C(gα,gβ) = g·C(α,β)`), a partition of them is a **system of imprimitivity** ⟹
    **¬primitive** — contradiction. *So primitivity rules out the extremal cover.* (Logic verified, not yet Lean; needs
    the vertex-partition→block bridge. The residual is **non-tight (overlapping)** covers.)
  - **2b — the loose/overlapping cover (the open heart): no current technique.** Overlapping near-maximal confusion
    classes covering `Fin n` = a genuine partial-geometry line system that is *not* a block system (e.g. Johnson is
    primitive yet line-system'd). Classifying it loops toward the geometric/Neumaier theory. **Elementary
    double-counting does NOT kill it** (checked: each `v` lies in `≤ rank·k²` big classes, giving `#bigClasses ≤
    2n·rank·k²/c`, which is *consistent* with the cover — no contradiction). The content is genuinely geometric.

### 9.4 What there is to work with (the handles)

1. **The landed reduction** — kill lemma, halving, `BigConfusionCover`, `card_bigClasses_mul_ge_of_cover` (the cover
   count `n ≤ #bigClasses·c`). Node 4 is one clean predicate (`hShatter`) feeding `reachesRigidOrCameron_viaNoCover`.
2. **Primitivity kills the extremal cover (2a)** — the tight/partition case is a system of imprimitivity. *Buildable*
   (a real lemma): formalize "Aut-invariant confusion partition ⟹ ¬IsPrimitive" via the landed block/`schemeEquiv`
   correspondence (`isBlock_schemeEquiv`, `isPreprimitive_iff_isPrimitive`). Shrinks node 4 to non-tight covers.
3. **The landed-but-UNUSED PV connectivity machinery closes the SPARSE sub-case.** `separatesAtBoundedBase_of_sparseSeparable`
   (Separability.lean / `§S-bridge`): `2c(k−1) < n ∧ k≥2 ⟹ b(X) ≤ 2`. For a **low-degree** residue (small `k`),
   `2c(X_T)(k−1) < n` holds at a bounded base ⟹ b≤2 directly, *no cover argument*. The **dense** (high-`k`) residue is
   the residual (there `2c(k−1)<n` ≈ discreteness, no free lunch). Re-activating this PV machinery is a concrete leg.
4. **The intersection-number coherence toolkit** (`fiberSize_mul_valency`, `valency_mul_interNum`, `sum_pu_le`,
   `interNum_eq_one_of_forcedUnique`, `RainbowRigid`/`dominatorReachable_of_rainbowRank`) — the project's lane for any
   *direct* counting/forced-triangle argument on the cover. (But §9.3-2b: simple double-counting is insufficient.)
5. **The probe evidence + CGGP** — the obstruction is the line/grid (geometric); non-geometric ⟹ no grid ⟹ should
   shatter. CGGP's `base ≤ 2 ⟹ WL-dim ≤ 4` is a *direct* (non-largeness) poly proof, but **for the geometric/affine
   case (node 2)** — node 4 is non-geometric, where CGGP's geometry does not apply, so node 4 *should* be easier yet has
   **no template**.

### 9.5 Honest verdict + concrete sub-targets

Node 4 = "a primitive non-geometric non-conference SRG has no big-confusion cover under individualization" — the rank-3
base case in the project's own forced-triangle language. **No elementary counting kills it; it is genuinely geometric
and open.** But it is now a *single sharp predicate* (`hShatter`) with two carved-off sub-cases and a clean anchor.
Buildable sub-targets, in order of tractability:
1. **(2a) Primitivity kills the tight cover** — formalize "Aut-invariant confusion partition ⟹ ¬primitive". Real lemma,
   reuses landed block machinery; carves the extremal case. *Low-medium risk.*
2. **(handle 3) Re-activate PV for the sparse residue** — wire `separatesAtBoundedBase_of_sparseSeparable` to the
   low-degree residue; closes node 4 there. *Low risk, partial coverage.*
3. **(2b) The dense loose-cover heart** — the genuine open research: show an overlapping near-maximal confusion cover
   forces a structure (partial geometry) a primitive non-geometric scheme lacks. *No current technique; the frontier.*

### 9.6 The multiplicity reframe — from "halve the max" to a global mass argument (the better-posed handle)

The fixed-threshold halving (kill all `>c/2` sets at once with one avoiding `v`) is *fragile*: its obstruction is a
cover, and tuning the constant `ρ` (call a set big if `|C|>ρc`) likely does not save it — if the largest avoidable
threshold is `c(1−o(1))`, the per-step drop is too slow (`~n` steps, not `O(log n)`). **The robust replacement is a
global multiplicity / mass argument** (the productive reframe):

- For a family of confusion sets `C₁,…,C_N` (the big ones), pinning a vertex `v` **kills exactly the sets `v`
  distinguishes** (`v ∉ Cᵢ`) and **leaves the ones it lies in** (`v ∈ Cᵢ`, since pinning a member never breaks a
  confusion — `v` relates identically to that pair). So pinning `v` kills `N − #{i : v ∈ Cᵢ}` sets.
- **Double-count:** `Σᵥ #{i : v∈Cᵢ} = Σᵢ |Cᵢ|`, so the **least-covered vertex lies in `≤ L := (Σᵢ|Cᵢ|)/n` big sets**
  (the average **multiplicity / load**). Pinning it leaves `≤ L` big sets; clean them up with `≤ L` more distinguishing
  pins. **So one halving costs `1 + L` pins, and `c → O(1)` in `O(L·log n)` base — polynomial iff `L = O(1)`.**
- **This defeats the cover when `L = O(1)`** even though no single avoiding `v` exists: a *minimal* cover (`N ≈ n/c`,
  each vertex in `~1` big set) has `L = O(1)` ⟹ `O(1)` cleanup ⟹ `c` halves. The cover only genuinely obstructs when
  `L = ω(1)` — **a high-multiplicity cover, where every vertex lies in *many* big confusion sets**.

**The payoff — the refined node-4 crux:** high multiplicity `L` = each point on many "lines" = a **thick** line system
= the Johnson/Hamming **Cameron** case (carved by G3). Low multiplicity = thin/net (defeated by the mass argument or
by primitivity, §9.3-2a). **So node 4 sharpens to: the residue's confusion-cover multiplicity `L = (Σ_{|C|>ρc}|C|)/n`
is bounded (`O(1)` / `O(log n)`).** `L` is a *concrete, computable* quantity (unlike "is it Cameron"), so the gap
becomes measurable. (User's two metrics: (a) count form `N − Σ|Cᵢ|/n` = sets removed by the best pin; (b) a
**size-weighted** form — weight by `|Cᵢ|` so the argument prioritises shattering a *large* set over many small ones,
since reducing `c` needs killing the biggest. The size-weighted potential `Σ|Cᵢ|²` or "mass above `ρc`" is the right
monovariant when the stacked region is all small covers.)

**Caveat (honest):** "`L` bounded for non-Cameron" is still morally the thick⟹Cameron classification — but as a
*measured quantity* it may admit a direct combinatorial/coherence bound the abstract "Cameron" predicate does not, and
it is exactly what the probe below can settle.

### 9.7 The `N_ρ` / multiplicity probe (the agreed next target)

Measure, on the residue (Shrikhande, Clebsch, Chang) vs the carved geometric families (rook `L(m)`, Johnson `T(m)`),
as a function of the size threshold `ρ ∈ (0,1)` and the base `T` (bare, +1, +2 individualizations):
- **`N_ρ`** = number of *distinct* confusion sets of size `> ρ·c(X_T)` (the cover-count; `card_bigClasses` analogue).
- **`L_ρ`** = `(Σ_{|C|>ρc} |C|) / n` = the average **multiplicity / load** (the §9.6 monovariant).
- **`minMult_ρ`** = `min_v #{big sets containing v}` = the per-halving cleanup cost (the operational quantity).
- **mass-weighted potential** `Σ_{|C|>ρc}|C|²` and its drop per individualization (the size-weighted monovariant).

**The hypothesis to test:** the residue has `L_ρ`/`minMult_ρ = O(1)` (and `N_ρ < n/c`) at some constant `ρ < 1`,
while the geometric families have `L_ρ = ω(1)` / `N_ρ ≥ n/c` (a thick cover). If so: the multiplicity is the provable
handle, the probe pins the exact `ρ`, and the Lean engine generalizes from `1/2`-halving to the `(1+L)`-cleanup form.
Extends `A2MonovariantProbe.cs`; reuses the residue/carved SRG fixtures already there.

### 9.7.1 Results — `A2MonovariantProbe.Probe_ConfusionCoverMultiplicity` (2026-06-16, built, run, green)

Built 2-WL-**faithful**: confusion sets on the coherent closure `X_T` (`PairClosure` = WL-on-ordered-pairs of the
graph adjacency with `T` individualized = `pointExtension` of the rank-2 SRG scheme), `BigConfusionCover` quantified
over **all** pairs (the first cut took one rep per relation class — a bug: 2–6 sets can't cover `n`; the all-pairs
metric is the Lean object). Rank-2 is the **conservative** view (an amorphic refinement is finer ⟹ `c` only shrinks,
`indistinguishingNumber_mono` ⟹ a cover only gets easier to avoid). Three findings:

1. **NO TIGHT COVER ANYWHERE — every cover is loose (`maxMult ≫ 1`, up to `= N`).** Confusion-set covers overlap
   *intrinsically* (many pairs share confused vertices), so the partition/tight configuration **sub-target 2a**
   targets does not arise — on residue or geometric, at any base/`ρ` tested. **⟹ 2a is empirically (near-)vacuous:**
   it would rule out a case that is already empty; the entire live content is the **loose cover (2b)**. *Reprioritize:
   2a is NOT the high-value Lean target the §9.5 ranking suggested — the loose-cover multiplicity bound is.*
2. **Geometric multiplicity GROWS with `n`; residue stays small / shatters.** Base `{0}`, ρ=0.5, `minMult`:
   rook `L(m)` **10→43→117→271** (`n=16,25,36,49`), Johnson `T(m)` **3→9→23** (`n=15,21,28`) — thick, `→ ω(1)`
   (`L` and mass `Σ|C|²` likewise). Residue: Shrikhande **3**, Chang-C8 **0 (shatters!)**, Chang-4K2 **4** — small/flat.
   **The cospectral `(16,6,2,2)` pair separates correctly:** Shrikhande shatters by base 2 (`minMult=0`, `c`: 8→6→4),
   Rook L(4) stays covered (`c`: 8→8→8, `minMult=1` even at `|T|=2`, base only at `√n=4`). Directional support for
   the reframe — multiplicity tracks the geometric/residue split the way base-size does.
3. **The rank-2 (conservative) view CONFLATES Clebsch with rook at fixed `n`.** Clebsch `c` is sticky (8→8→8) and
   `minMult=9 ≈` rook's 10 at `n=16` — because Clebsch's recovery lives in its **amorphic (rank-4) refinement**, which
   the rank-2 graph closure does not see. The residue also cannot be *scaled* (the construction bottleneck, §5 F2): only
   `n=16` (Shrikhande/Clebsch) and `n=28` (Chang) exist, so "residue `L=O(1)`" is inferential from a flat 2-point trend.

**Verdict.** The probe is **decisive on 2a (drop it — covers are intrinsically loose)** and on **geometric thickening
(clean, `ω(1)`)**. The residue-vs-Cameron *separation* — the crux — is clean only on the cospectral pair; Clebsch needs
the amorphic refinement to beat the obstruction (on rank-2 it looks Cameron-like). **Two honest next moves:**
(a) **iterate the probe onto the residue's amorphic schemes** (ℤ₄² Clebsch rank-4 `clebschZ4ColF`, Shrikhande rank-3)
— the decisive test of whether multiplicity *cleanly* separates residue from Cameron once the residue is viewed on its
own scheme; (b) **skip to the loose-cover Lean content (2b)**: since tight covers don't occur, the open theorem is
"a loose big-confusion cover of a primitive non-geometric SRG has bounded multiplicity `L` (or `minMult`)", the
`(1+L)`-cleanup engine. The fixed-`ρ` halving threshold showed no special structure (the ρ-sweep is flat 0.5–0.6 then
steps), consistent with §9.6's "fixed `ρ` is fragile — use the global mass/multiplicity argument."