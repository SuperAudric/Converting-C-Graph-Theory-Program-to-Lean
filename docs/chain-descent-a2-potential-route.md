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
high `L`=thick=Cameron carved, low `L`=poly via `1+L`-cleanup).

**★★★ THIS SESSION (2026-06-16, HANDOFF) — probe run, endgame scoped + corrected, PART 1 LANDED. Read §9.7.1–§9.7.2 (probe
results), §9.8 (endgame), then PICK UP at part 2 below.**
1. **Multiplicity probe — built, run, green (§9.7.1–§9.7.2; `A2MonovariantProbe.{Probe_ConfusionCoverMultiplicity,
   Probe_ConfusionCover_Amorphic}`).** Findings: (a) **2a is DEAD** — confusion covers are *intrinsically loose* (no tight/
   partition cover on ANY scheme, primitive or imprimitive), so the tight/loose split is excised; the axis is **multiplicity
   magnitude**. (b) **Clean separation on the FAITHFUL (amorphic) scheme** — Clebsch on its rank-4 scheme shatters at base 1
   (`minMult`→0), rook stays thick; the rank-2 graph view conflated them. (c) geometric `minMult`/`L` grows with `n`, residue
   small/shatters. **Faithful-scheme lesson: measure the residue on its amorphic/orbital scheme, never the rank-2 graph.**
2. **Endgame scoped + a correction (§9.8).** `hShatter` = TWO parts (the "thick⟹Cameron" 3rd part was a phantom — multiplicity
   is a *measurement*, not a case split): (1) cascade-rate engine [now LANDED]; (2) the carved residue cascades = the open
   **rank-3 base case**. The seal's real split is large-Aut→G3 / small-Aut→cascade — **no SRG-structure citation needed beyond
   G3.** ⚠ **Correction:** earlier "polynomial unreachable" was WRONG — it imported the *citation* route's sub-exp ceiling onto
   this *direct-proof* route. **Polynomial-unconditional-`modulo {G3+hcatch}` IS the target and is reachable in principle**
   (open & hard, but unbarred — CGGP + 0 falsifiers lean toward it). cxt-scoping route 3 = fallback, not target.
3. **PART 1 — the cascade-rate engine — ✅ LANDED, axiom-clean (`§CC.20b` + `§S-gate2`).** `exists_potential_descent_bounded`,
   `BoundedConfusionMultiplicity B M`, `potentialCleanup_of_boundedConfusionMultiplicity`,
   `exists_small_base_of_boundedConfusionMultiplicity`, capstone `reachesRigidOrCameron_viaBoundedMultiplicity`. **"Residue
   cascades (bounded `M`) ⟹ polynomial seal" is now a THEOREM.** Seal `modulo {G3 + BoundedConfusionMultiplicity + hcatch +
   hImprim}`; the entire open content is the single discharge `BoundedConfusionMultiplicity` (strictly weaker than
   `IndistinguishingHalves` = its `M=1` case).

**★ LOAD-BRIDGE LANDED (2026-06-16, `§CC.22b`, axiom-clean, build green) — part 1's consumer is now fed by the computable load.**
The §9.6 `(1+L)`-cleanup mechanism is in Lean: `indistinguishingNumber_pointExtension_biUnion_le` (the SET generalization of the
single-vertex kill bound — a `≤M`-set distinguishing every big pair bounds `c(X_{T∪S})`), the predicate `BoundedConfusionLoad B M`
(a size-`≤M` set hits every `>c/2` confusion set per over-`B` base), and **the bridge `boundedConfusionMultiplicity_of_boundedConfusionLoad`**
(`BoundedConfusionLoad B M ⟹ BoundedConfusionMultiplicity B M`, via the set bound at `M'=c/2`). Plus the **non-vacuity anchor**
`boundedConfusionMultiplicity_univ` (`BoundedConfusionMultiplicity B n` for *every* CC — `S=univ` completes the extension, `c=0`;
guards the vacuity trap, mirrors `cascadesAt_univ`) and its brick `indistinguishingNumber_eq_zero_of_allSingletonFiber`. **Effect:**
A2's open content is re-expressed as **"the residue's confusion-cover load `L`/`minMult` is `O(1)`/`O(log n)`"** — the exact computable
quantity the `A2MonovariantProbe` measures, not the opaque "a set halves `c`". The `M=1` case is the landed cover route
(`indistinguishingHalves_of_not_bigConfusionCover`); this is its bounded-multiplicity generalization.

**★★★ HANDOFF (2026-06-17) — the full thin-side machine + the D1/D2/D3 attack on node 4 are LANDED; the wall is pinned and
its method of attack written. The authoritative current state is §9.9.6 + §9.9.7; read those two first.** Arc of this work,
all axiom-clean, build green, nothing committed (user commits):
- **PV-sparse + raw-counting sub-class leads CLOSED** (§9.5a/§9.5b): both trivial/dead for the residue; the open content is
  irreducibly the thin-cover/low-`minMult` geometric core (node 4). So option (i), the direct attack, was taken.
- **The thin-side cascade machine is now PROVED end-to-end** (§CC.22b–d): `BoundedMinMult` (bounded `minMult` per over-`B` base)
  → `boundedConfusionLoad_of_boundedMinMult` (the §9.6 `(1+L)`-cleanup) → `boundedConfusionMultiplicity_of_boundedMinMult`
  → `…viaBoundedMultiplicity` (the §CC.20b engine) → **polynomial seal**. Plus the non-vacuity anchor
  `boundedConfusionMultiplicity_univ` (M=n every-graph fallback).
- **D1 (cover rigidity) DONE** (§CC.22c): confusion-set equivariance (`confusionSet_perm`, `card_`, `mem_`, `big_confusion_perm`)
  + the punchline `confusionMultiplicity_perm` — cover-load is `Aut`-invariant (constant on orbits; `= L` on the vertex-transitive
  bare scheme). A persistent cover is a rigid invariant line system.
- **D3 dichotomy capstone LANDED** (`reachesRigidOrCameron_viaBoundedMinMult`, §S-gate2): carries `hSmallAutThin : ¬IsLarge →
  BoundedMinMult B M`, by_cases largeness (large→G3/Cameron-or-`hImprim`; small→cascade). Seal `modulo {G3 + hSmallAutThin +
  hcatch + hImprim}`. Strictly sharper than `…viaSmallAutShatters` (bounded load, not the rarely-true zero-load/¬cover).

**▶ THE WALL (where a new reader picks up).** The lone open content is now the single computable predicate **`hSmallAutThin`
= "small-Aut primitive residue ⟹ `BoundedMinMult`"**, i.e. its contrapositive **thick (`minMult` unbounded) ⟹ large Aut**.
This is *irreducible* (rook is thick, needs √n base, saved only by large Aut; δ′ gives √n there) = Babai SRG-structure / CFSG =
a slice of GI∈P-for-SRGs = **node 4, no known witness, not known to mathematics.** **Method of attack = §9.9.7** (1 sharpen
[done] · 2 threshold ladder: Spielman→sub-exp floor / poly→open · 3 node-2 rung [bridge DONE §9.9.9, uniform-rank piece open] ·
4 Neumaier — NOT a way through).

**▶▶ THE DIRECT NODE-4 ATTACK LEADS ARE NOW ALL CLOSED (this session, 2026-06-17 — do NOT re-walk them; see the dated pointers
below + §9.9.10–§9.9.12):** (i) the **D2 "stable ⟹ regular partial geometry" extraction** is REFUTED as a proof route (§9.9.10
— persistent carved covers go irregular under individualization; the only robust separator is persistence = `hSmallAutThin`
itself, no regularity shortcut); (ii) **climbing the k-WL ladder cannot manufacture a gap** (§9.9.11 — `base_k ≥ b(Aut)` for
every `k`, and the user's c^k hypergrid `H(k,c)` has base that SHRINKS with `k`; the wall lives in the group-base term, invariant
under WL level); (iii) the **Hamming-twist (Doob) falsifier hunt is negative** (§9.9.12 — every small-Aut twist, incl. the
composed Doob `Shrikhande□K₄` cospectral with `H(3,4)`, keeps `base = b(Aut)`, gap 0). **With §9.9.8 (trivial-Aut sporadics) the
falsifier record is 0 across EVERY constructible probe**, and the two natural "engineer a thick small-Aut graph" routes (climb
WL / twist Hamming) are closed. **Net characterization of the wall:** the open question is exactly *"is the WL-dim gap `base −
b(Aut)` bounded for the small-Aut residue?"* — the group term `b(Aut)` is handled (`exists_greedy_base_le_log` → O(log n) for
small Aut), there is **no constructible falsifier and no current proof technique**, so node 4 is the long-horizon open frontier,
**not directly attackable by these means**. A fresh reader should NOT re-attempt a direct node-4 attack via covers/regularity/
WL-level/Hamming-twists; those are exhausted.

**Recommended next builds (the carve-around — these remain the live work):** (a) **the remaining node-2 work — a *uniform*
rainbow rank** for a parametric affine/FDF family via `dominatorReachable_of_rainbowRank` (δ′→discrete→`minMult=0`; `clebschZ4`
is the n=16 instance; the landed `reachesRigidOrCameron_viaCompleteBase` is its seal consumer; gap = generalizing the rainbow
rank off n=16), shrinking the residue to node 4; (b) **Spielman floor** — a `…viaSpielman` capstone making the seal
unconditional-modulo-citations at the sub-exponential threshold (Cameron-free). Both reuse landed infrastructure; neither
touches the open node-4 core. **Read §9.9.6 + §9.9.7 (the wall + its method) first, then the probe record §9.9.8 + §9.9.10 +
§9.9.11 + §9.9.12 (the falsifier hunts, all negative) + §9.9.9 (the node-2 bridge) to continue.** **★ NEWEST (2026-06-17,
§9.9.17): closure-angle reduction + literature SOTA pass.** Literature confirms the wall is open both ways (0 falsifiers,
no citable bound); two deltas (sub-exp floor is `n^{1/5}` not `n^{1/3}`; NEW cite Skresanov rank-3 2-closure). The
closure-angle reduction's "⟹ block" is VACUOUS on the primitive floor (lemma `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive`,
axiom-clean) — the crux is the 2-closure deficiency `G^(2)_T/G_T`, which MERGES with the Skresanov lead (§9.9.18).
**★ HEADLINE (2026-06-17, §9.9.18 + §9.9.18a + §9.9.18b): node-4-FOR-THE-SEAL is AFFINE — and the open residue is now
4 NAMED, CONSTRUCTIBLE families, not a mysterious wall.** Skresanov's rank-3 2-closure + Cameron/Liebeck ⟹ every
small-Aut non-geometric *schurian* rank-3 residue is affine; C3 RESOLVED (§9.9.18a, verdict A — seal deliberately
scoped to schurian, `StablyRecoverable ↔ DiscretizesAtBases ∧ RecoversWhileSymmetric`, keyed IR-core-free), so the
non-schurian wall is relocated to the IR-solver row 4 (never the seal's job). **BUT C1 (§9.9.18b) shows the affine
target is only PARTLY cited:** node-4-schurian = `{1-dim cyclotomic — CITED (Ponomarenko 2-sep) + forms-graphs (c)–(f):
affine-polar / alternating / half-spin / Suzuki–Tits — UNCITED, bounded-WL-dim OPEN}`. So the seal's node-4 is **not**
closed-modulo-citations; the forms-graph part is open. **The upside (a real correction):** these 4 families are
*explicit, constructible* node-4 witnesses (growing `q`) — refuting the "no constructible witness" framing — and being
small-Aut schurian (group base `O(log n)`) they are *probable* — and **PROBE DONE (§9.9.18c, `Probe_FormsGraphs`):
the affine-polar `VO^-_4(q)` SHATTERS** (base = [5,5,6] FLAT vs √n = [4,9,16] for n=16,81,256; geometric Rook needs
base = √n) — hSmallAutThin **confirmed** on the first constructible unbounded-`s` witnesses, refuting "no witness".
Bounded-WL-dim for them stays UNCITED/OPEN (empirical, not a proof). Read §9.9.18 → §9.9.18a → §9.9.18b → §9.9.18c.

**▶ ROW-4 SPORADICS PROBE DONE (2026-06-17, §9.9.8) — `hSmallAutThin` confirmed at TRIVIAL Aut, 0 falsifiers.**
`A2MonovariantProbe.Probe_Row4Sporadics` loads the Paulus `srg(25,12,5,6)`/`(26,10,3,4)` + Chang(28) + conference(29)
from the verified Hanaki catalogue and measures the Lean `BigConfusionCover`/`minMult` on the 2-WL closure. **42 small-Aut
non-geometric SRGs (many `|Aut|=1`) ALL shatter at base ≪ √n (`minMult→0`); the 3 geometric/large-Aut stay thick (base ≈√n,
`minMult` 7–9). No falsifier.** Sharpest test yet of `hSmallAutThin` — extends the 0-falsifier record from the biggish-Aut
Shrikhande/Clebsch/Chang to genuinely-trivial-Aut residue. **Honest scope unchanged:** all data is bounded `s` (node 3 /
exceptional / leg B); **node 4 = unbounded `s` is construction-bottlenecked, unreached — `hSmallAutThin` stays the open wall**,
now with strictly stronger empirical support. Build: green; nothing committed (user commits).

**▶ D2 STABLE-COVER REGULARITY PROBE DONE (2026-06-17, §9.9.10) — the "stable ⟹ regular" extraction is REFUTED as a proof
route; the one novel node-4 lead is closed.** `A2MonovariantProbe.Probe_StableCoverRegularity` (green) probe-tested the
§9.9.2/§9.9.4 bet *before* any Lean investment. Reframe: REGULAR ≠ TIGHT (the rook grid cover is loose yet a regular partial
geometry), so the axis is regular-vs-irregular, which §9.7.1's `minMult`/`maxMult` never isolated. **Result:** (A) carved
(geom+imprim) covers PERSIST 8/8 but go **IRREGULAR** under individualization (point-degree spreads, 0 regular at the deepest
base) — so "persistent ⟹ regular partial geometry" is **false**; (B) residue covers shatter 9/10 (the cross-check at base ∅
*also* fails to separate — Clebsch is more line-regular than rook). **So D2 cannot extract a partial geometry from a stable
cover; the robust separator is PERSISTENCE itself = bounded `minMult` = `hSmallAutThin` (the existing wall), with no
regularity shortcut.** Do NOT build the D2 regular-PG extraction. The live next builds revert to the carve-around: node-2
rung uniform rainbow rank + the Spielman floor. Node 4 untouched (bounded-`s` data only). Nothing committed (user commits).

**▶ k-WL LADDER / HAMMING HYPERGRID PROBE DONE (2026-06-17, §9.9.11) — climbing k-WL is NOT a node-4 attack; the c^k
hypergrid is the carved (Cameron) leg, and its base SHRINKS with dimension.** `A2MonovariantProbe.Probe_HammingLadder`
(green; correct oblivious k-WL + group-base `AutBase`). Two facts: (i) `base_k ≥ b(Aut)` for all `k` (k-WL can't split an
Aut-orbit); (ii) constant-k-WL ≡ 2-WL + O(1) individualizations via the carried `hcatch` (`dimWL ≤ dimWL(X_α)+1`) — so base
and WL-dimension are dual coordinates, and "bounded base" = "bounded WL-dim" = node 4. **Probe: `base_3 = base_2 = b(Aut)`
(gap 0) on rook L4/L5, H(3,3), Shrikhande — the base is the GROUP base, no WL level reduces it; the c^k hypergrid base
`≈ k·n^{1/k}` SHRINKS with `k` (rook k=2 = √n is the extremal thick case, NOT an escalating ladder); 3-WL statically
separates cospectral rook/Shrikhande (`[16,96,144]` at 2-WL → 15 vs 31 colours at 3-WL — corrects §9.9.7 step-4's "needs
CFSG", but identifying ≠ bounding base).** ⟹ `hSmallAutThin` is invariant under climbing (not a level-2 artifact); the Hamming
family is Cameron with `base = b(Aut)` (equality), not a node-4 falsifier. Re-pins the open content as the **WL-dim gap
`base − b(Aut)`** (group term already handled by `exists_greedy_base_le_log`). Nothing committed (user commits).

**▶ HAMMING-TWIST (DOOB) FALSIFIER PROBE DONE (2026-06-17, §9.9.12) — the sharpest constructible node-4 falsifier test comes
back TAME.** `A2MonovariantProbe.Probe_HammingTwists` (green). Hunts a small-Aut graph with `base ≫ b(Aut)` (the §9.9.11
falsifier shape) among Hamming **twists**. Centerpiece: **Doob `D(1,1) = Shrikhande □ K₄` (n=64)**, cospectral with `H(3,4) =
K₄^□3` but `|Aut|` 4608 vs 82944 — the Shrikhande/rook contrast one level up. **Result: Doob gap 0 (`b(Aut)=base₂=3`); Shrikhande
+ both Chang graphs all gap 0 — every small-Aut twist TAME, no falsifier.** Even a *composed* twist keeps `base = b(Aut)` (the
twist shrinks `|Aut|` and the base together). 2-WL cospectrality confirmed (`[64,576,1728,1728]` identical for H(3,4) vs Doob).
Extends the 0-falsifier record to a composed cospectral twist; with §9.9.11 closes off the two natural "engineer a thick small-Aut
graph" routes (climb WL / twist Hamming). Bounded-`n` scope (≤64). Nothing committed (user commits).

**▶ NODE-2 RUNG, first increment LANDED (2026-06-17, §9.9.9) — the δ′ → multiplicity-pipeline bridge.** Axiom-clean,
build green: `boundedConfusionMultiplicity_of_completeBase` (§CC.22e — a bounded *discrete* base ⟹
`BoundedConfusionMultiplicity B M`, sharpening the trivial `M = n` anchor to `M = |T₀|`) + the capstone
`reachesRigidOrCameron_viaCompleteBase` (§S-gate2 — routes a discrete-base thin family through `…viaBoundedMultiplicity`,
no largeness guard, seal `modulo {G3 + hcatch + hImprim}`). **The pipeline-validation half** (connective tissue
δ′→D1/D2/D3) is done; the **remaining node-2 content is a *uniform* discrete base for a parametric affine/FDF family** (a
uniform rainbow rank via `dominatorReachable_of_rainbowRank`, generalizing `clebschZ4` off n=16 — the genuine
combinatorial work). Nothing committed (user commits).

**▶ NODE-2 RUNG, second increment LANDED (2026-06-17, §9.9.9a) — the seal-level rainbow lift + the rank-counting node-4
boundary.** Axiom-clean, build green: `reachesRigidOrCameron_viaRainbowRank` (CascadeAffine — any `RainbowRigid` schurian
scheme with a bounded rainbow rank seals, composing `dominatorReachable_of_rainbowRank` into the catch-up-free
`viaDominatorClosure`; carries only {G3 + `hne` + `hrank` + `hImprim`}, **no `hcatch`/largeness/`hSmallAutThin`** — the
previously-missing seal capstone that consumes the rainbow lift) + `clebschZ4_closure_viaRainbow` (ClebschConcrete —
non-vacuity: the family engine fires on the real n=16 residue; gap to a *sealed* instance = the deferred `SchurianScheme`
structure on `clebschZ4Scheme`). **★ Node-4 insight:** the rainbow carve needs **rank ≥ 4** (a rainbow triangle = 3 distinct
non-diagonal colours); node 4's core is a primitive **rank-3 SRG** with no rainbow triangles, so the scheme-level engine is
**structurally inapplicable** there (colour-counting, not difficulty) — node-2 carving provably cannot leak into node 4, and
any node-4 progress must work in the 2-WL extension arena (D1/D2/D3). Nothing committed (user commits).

**▶ SCHURIAN-TRANSPORT FINDING (2026-06-17, §9.9.9b) — `clebschZ4` is NON-schurian; the schurian rainbow-rigid Clebsch is
AFFINE.** Investigating a *sealed* clebsch instance for `viaRainbowRank`: the extracted `clebschZ4Scheme` (on `ℤ₄²`,
non-affine) has **`|Aut| = 32`** (translations `⋊` order-2 stab), the stabiliser **not transitive** on the size-5 colour
classes ⟹ each orbital splits 5-fold ⟹ **non-schurian** (cannot be sealed; corrects the "deferred schurian" note — it is
impossible, not pending). The schurian rainbow-rigid Clebsch is the **affine cyclotomic `clebschScheme`** (`F₁₆ = Z2⁴`,
order-5 multiplier, `|Aut| = 160`, rainbow-rigid — verified). **Consequence:** at `n = 16` the schurian rainbow-rigid
amorphic is *affine* (leg-B-adjacent), the non-affine amorphic is *non-schurian* (not a residue) ⟹ `viaRainbowRank`'s new
non-affine territory is **empty here**; its achievable instance is `clebschScheme` = a *citation-free reproof of the affine
amorphic slice* (cost = a noncomputable cyclotomic `RainbowRigid` proof), not a non-affine breakthrough. Recorded, not
auto-pursued (an affine rung; cannot approach node 4). ClebschConcrete docstrings corrected. Nothing committed.

**▶ SPIELMAN FLOOR LANDED (2026-06-17, §9.9.13) — the fully-citable, Cameron-free sub-exponential end-state (§9.9.7
step 2-subexp).** Axiom-clean, build green: `reachesRigidOrCameron_viaSpielman` (Cascade.lean) carries the **single**
hypothesis `hSpielman : SeparatesAtBoundedBase S bound` (the residue individualizes a `≤bound` base to `Discrete`) and
concludes the seal via the **rigid branch outright** — **carries ONLY `hSpielman`: no G3, no `hImprim`, no
largeness/Cameron** (the Cameron disjunct is never taken; discretization ⟹ reaches rigid, so the whole "or Cameron"
machinery is unneeded at this threshold). Faithful citation: **Spielman STOC 1996** (every primitive SRG
individualizes to discrete at `Õ(n^{1/3})`) ⟹ `hSpielman` at `bound = Õ(n^{1/3})` unconditionally (imprimitive = block
tower, conference = leg B). Plus the reusable positive bridge `schemeRecoveredByDepth_of_separatesAtBoundedBase`
(separation supplied outright ⟹ depth-graded recovery, via `stablyRecoverable_of_discrete`). The sub-exp-vs-poly
split = the scaling of `bound`: `Õ(n^{1/3})` proven (here), `O(log n)` = node 4 (no citation). **This is the sharpest
fully-citable end-state; it does NOT close the polynomial seal** (node 4 untouched). Nothing committed (user commits).

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
| **2** | **Thin line system** (geometric, bounded thickness — FDF/affine) | yes, base `O(1)` | **CGGP/BCN template** (`base ≤ 2 ⟹ WL-dim ≤ 4`, BCN Thm 3.3.8). **Seal vehicle LANDED & citation-free** (`reachesRigidOrCameron_viaRainbowRank`, §9.9.9a — any `RainbowRigid` schurian scheme w/ a bounded rainbow rank seals, no `hcatch`/largeness); affine instances fully sealed (`viaG0powNeg`, `…affineSlice`). **Ladder risk largely DEFUSED** (§9.9.9b): the genuinely-novel *non-affine* schurian node-2 instances appear empty — the non-affine amorphic schemes are *non-schurian* (not `orbitalScheme H` residues), the schurian rainbow-rigid amorphic ones are *affine* (leg-B). So node-2's real content = {landed affine seals} + {the cited CGGP template}; no open math, no infinite per-geometry ladder. *(Cannot reach node 4 — rank-counting, §9.9.9a.)* |
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
3. **~~PV connectivity closes the SPARSE sub-case~~ — DEAD LEAD (resolved 2026-06-16, see §9.5a).** The hoped-for
   "low-degree residue" sub-case via `separatesAtBoundedBase_of_sparseSeparable` (`2c(k−1)<n ⟹ b≤2`) **does not exist**:
   the residue is dense (`k=maxValency=Ω(n)`, `c=Ω(n)` on every primitive SRG/amorphic ⟹ `2c(k−1)=Ω(n²)≫n`, vacuous on the
   bare scheme), and on the extension `X_T` — where the inequality *does* hold — the homogeneous PV Thm 3.1 is proven
   **blocked at the cross-fiber wall** (§CC.17). Do NOT re-activate PV sparse for the residue. Full verdict + evidence: §9.5a.
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
2. **~~(handle 3) Re-activate PV for the sparse residue~~ — DROPPED (resolved 2026-06-16, §9.5a).** No low-degree
   primitive-SRG sub-case exists for PV sparse to bite (vacuous on the bare scheme; wall-blocked on `X_T`). Replaced by:
   bound the load/`minMult` *directly* on `X_T` with the **ported** CC counting toolkit (§CC.12–17: `sum_pu_le`,
   `pu_eq_sum`, `valency_mul_interNum`, `fiberSize_mul_valency`, within-fiber smax symmetry) for a specific
   intersection-number / bounded-fiber-degree regime — NOT through the (blocked) homogeneous PV connectivity.
3. **(2b) The dense loose-cover heart** — the genuine open research: show an overlapping near-maximal confusion cover
   forces a structure (partial geometry) a primitive non-geometric scheme lacks. *No current technique; the frontier.*

### 9.5a PV-sparse caveat — RESOLVED (2026-06-16): it is a dead lead for the residue; drop it

The part-2 plan listed "re-activate PV sparse `separatesAtBoundedBase_of_sparseSeparable` for the low-degree residue" as
a cheap sub-class. Investigation (source-verified) shows **it is not viable** — both at the bare scheme and the
extension. Recorded here so no effort is spent on it.

**The consumer** (`CascadeAffine.separatesAtBoundedBase_of_sparseSeparable`, CascadeAffine.lean:402) needs a
**homogeneous** `SchurianScheme` with `SparseSeparable := 2·c·(k−1) < n` (`c = indistinguishingNumber`, `k = maxValency`).
Its own docstring concedes *"the dense amorphic residue needs Thm 4.1's full strength."*

- **Bare scheme — vacuous.** A primitive SRG`(n,d,λ,μ)` has relation valencies `{1, d, n−1−d}`, so `k = maxValency =
  max(d, n−1−d) = Ω(n)`; rank-4 amorphic relations are `~n/rank`. And `c = Ω(n)` (most γ fail to distinguish a pair).
  So `2c(k−1) = Ω(n²) ≫ n` — `SparseSeparable` fails on every primitive SRG/amorphic. Checked even on Clebsch
  (`k=5, c=4, n=16`: `2·4·4 = 32 > 16`). PV sparse fires only when `c` AND `k` are *both* small — a genuinely sparse CC,
  which a dense primitive SRG never is.
- **Extension `X_T` — proven blocked.** The inequality `2·c(X_T)·(k(X_T)−1) < n` *does* hold at a bounded base (M1:
  `c(X₁)≤4`, `k(X₂)=O(1)`), but `X_T = pointExtension X T` is multi-fiber for `T≠∅`, and the homogeneous PV theorem does
  not apply. The CC port of PV Thm 3.1 is **proven blocked at the cross-fiber wall** (`CoherentConfig.lean §CC.17`,
  `smaxAdj_symm_of_sameFiber`): PV §S.10's `smaxConnected_of_sparseSeparable` runs `exists_small_closed_of_not_connected`,
  which needs a *symmetric* `smaxAdj`; on a multi-fiber CC `n_s ≠ n_{s*}` across fibers, so global `SmaxConnected` is
  unavailable — symmetry survives only *within a fiber*. A1 (`§CC.18`) deliberately routed around this with the crude
  abundance bound `dominatorReachable_of_card_gt` (*"No smax/sα connectivity, no SparseSeparable, citation-free"*).
- **No essential gain even hypothetically.** PV's sharp `b≤2` vs A1's crude `b ≤ (k−1)c+1` are both polynomial when `c,k`
  are bounded, and the seal only needs polynomial. PV sparse offers a sharper *constant*, not a different *scope*.

**Verdict.** Drop PV sparse from the part-2 sub-class plan. The one PV-flavoured handle that survives on `X_T` is the
*within-fiber* smax localization (§CC.17) — a per-fiber connectivity argument — but that is a research direction, not a
quick wire. The natural next idea — bound the load/`minMult` directly with the *ported* CC counting toolkit (§CC.12–17)
— was then scoped: **§9.5b shows raw counting is also trivial.** The honest conclusion is in §9.5b.

### 9.5b Scoping the counting redirect — RESOLVED (2026-06-16): raw counting is trivial; the tractable structured case is already landed

§9.5a redirected sub-class effort to bounding the load/`minMult` directly with the ported CC counting toolkit
(`sum_pu_le` et al., §CC.12–17). **Scoping verdict: raw counting yields only a trivial bound — no new tractable load
sub-class exists.** The chain, source-verified against `sum_pu_le` (`Σ_{δ} pu(α,u,δ) ≤ k(k−1)·c`, per non-reflexive
relation, no rank factor):

- **The multiplicity bound it gives is trivial.** Summing `sum_pu_le` over the `≤ rank` non-reflexive relations `u`
  (using `pu(z,u,δ)` = `u`-neighbour pairs of `z` confused by `δ`, and `z∈C(β,γ) ⟺ relOf z β = relOf z γ`) gives, for
  every `z`, `Σ_{(β,γ): β≠γ, z∈C(β,γ)} |C(β,γ)| ≤ rank(X_T)·k(X_T)(k(X_T)−1)·c(X_T)`. Each big pair through `z`
  contributes `>c/2`, so `mult(z) = #{big sets ∋ z} < 2·rank(X_T)·k(X_T)(k(X_T)−1)`. **But `rank·k ≥ n`** (from any
  vertex the `n` targets split into `≤ rank` classes of size `≤ k`), so `2·rank·k² ≥ 2nk ≥ 2n` — never beats the trivial
  `mult ≤ n`. This is §9.3-2b's obstruction, pinned at the load level: the `rank` factor (≥ `n/k`) is fatal.
- **The sharp per-relation version is vacuous for SRGs.** `minMult ≤ Σ_{r: c(r)>c/2} valency(r)·c(r)/n` (each relation's
  confusion is constant `= c(r)`, `indistinguishingNumberOf_eq_card`). Bounded only if `Σ_{big r} valency(r) = O(n/c)` —
  but an SRG's big relations are adjacency / non-adjacency with valency `Ω(n)`, forcing `c = O(1)` (already near-discrete).
  No primitive-SRG/amorphic sub-class.
- **The one structured tractable case is already discharged.** The bounded/forced-intersection-number regime
  (`c^i_{jk} = 1` triangles) is the δ′/`RainbowRigid` family — landed (`dominatorReachable_of_rainbowRank`, `clebschZ4`),
  independent of the load argument. Counting adds nothing on top of it.

**Net.** Beyond the already-landed forced-triangle (δ′/rainbow) regime, `BoundedConfusionLoad B (1+minMult)` reduces to
the **thin-cover / low-`L` condition** (`#distinct big sets = O(n/c)`, equivalently `minMult = O(1)`) — which is exactly
the §9.6 geometric open core, NOT a raw-counting consequence. **So part 2 has no remaining low-hanging counting
sub-class.** The genuine options are now just two: **(i)** the direct geometric argument that a primitive *non-geometric*
residue has a thin cover (the hard heart, §9.3-2b / node 4), or **(ii)** carry `BoundedConfusionLoad`/`BoundedConfusionMultiplicity`
as the named predicate (cxt-scoping route 3, the honest floor). (Optional artifact: the trivial `mult ≤ 2·rank·k²` bound
could be formalized to turn §9.3-2b from a note into a theorem — low value, demarcates where counting stops.)

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

### 9.7.2 Move (a) done — amorphic residue + imprimitive controls (`Probe_ConfusionCover_Amorphic`, 2026-06-16)

Both open questions from §9.7.1 resolved (green, test passes):

- **Q1 — multiplicity CLEANLY separates residue from Cameron on the FAITHFUL scheme.** Measured Clebsch on its own
  **rank-4 amorphic** scheme (`ClebschZ4Amorphic` = `ClebschConcrete.clebschZ4ColF`) vs the coarse rank-2 graph closure
  vs rook L(4). On rank-4 Clebsch **shatters at base 1** (`minMult`: 25→**0**; `c`: 4→4→discrete at base 2); on rank-2 it
  was sticky (`c`: 8→8→8, `minMult` 25→9→3, never shatters in 2). Rook L(4) stays thick (`minMult=10` at base 1, covered
  to base √n=4). **The rank-2 conflation (§9.7.1 finding 3) was an artifact of the coarse scheme** — `X = orbitalScheme H`
  in the seal IS the amorphic scheme, and on it the residue shatters fast while Cameron stays thick. *Multiplicity is the
  right discriminator; the (b) loose-cover bound is well-motivated.* (NB the amorphic shatter is `minMult→0`, stronger than
  the bounded-`L` the bound needs.)
- **Q2 — loose-ness is INTRINSIC; 2a is UNIVERSALLY vacuous (excise the tight/loose framing).** No TIGHT (partition,
  `maxMult=1`) cover on **any** scheme — primitive *or* imprimitive. The imprimitive controls (`4·K₄`, `K_{4×4}`, `2·K₈`)
  all have **thick loose** covers (`maxMult` 24/24/49, `minMult` 17–49) that never shatter — i.e. imprimitive looks like
  the *thick/Cameron* case in the multiplicity picture, not a tight case. So loose-ness is intrinsic to confusion covers,
  **not** a primitivity consequence: the partition configuration 2a (`§9.3-2a`, "tight ⟹ imprimitive") rules out **never
  arises for any scheme**. ⟹ **2a is dead content** (true-but-vacuous-premise); delete the tight/loose split from §9.3.

**Consolidated picture (the redirect, confirmed).** The productive axis is **multiplicity magnitude**, not tight/loose:
- **High `minMult`/`L` (thick cover) ⟸ does NOT shatter** — and this captures *both* carved legs: geometric → Cameron
  (G3, `minMult` grows with `n`, §9.7.1) **and** imprimitive (`hImprim`, thick by Q2). Aligns with the existing seal split.
- **Low `minMult`/`L` (→ 0 on the amorphic residue) ⟹ shatters** — the primitive non-geometric residue (Q1).
**Next Lean target = the loose-cover bound (b)**, stated on multiplicity: *primitive non-geometric ⟹ `minMult(X_T)` (or `L`)
bounded ⟹ shatter via the `(1+L)`-cleanup*. **2a (`§9.3-2a`, §9.5 sub-target 1) is dropped.** Faithful-scheme caveat for any
future probe: measure the residue on its **amorphic/orbital** scheme, never the rank-2 graph (which conflates with Cameron).

## 9.8 Endgame scoping — where the (b) redirect leads (does it reach unconditional-modulo-citations?)

> **The question.** If the (b) loose-cover/multiplicity route is carried to completion, is an unconditional (modulo
> citations) seal within reach, or does it hit a wall later? **Answer (corrected 2026-06-16): polynomial-unconditional-
> modulo-`{G3 + hcatch}` IS the target of this route and is reachable *in principle* — it reduces to ONE open theorem
> ("the carved residue cascades / has `O(log n)` base"). That theorem is open and hard (a chunk of GI∈P-for-SRGs) but
> NOT barred — no proven obstruction, and the evidence (CGGP, 0 falsifiers) leans toward it. What §8.6 actually shows is
> narrower: no *citation* reaches polynomial — which is exactly why the largeness/citation route was set aside in favour
> of this DIRECT-proof route.**
>
> **⚠ Correction.** An earlier draft of this section called polynomial "the wall / unreachable." That was wrong — it
> imported the *citation* route's sub-exponential ceiling (§8.6) onto this *direct-proof* route, which does not rely on a
> citation. "Open / unconjectured-in-the-literature" ≠ "barred": it means unproven, not unprovable. The project's whole
> premise (00-START-HERE "isolation is the method, not a surrender"; cxt-scoping §5 route 2) is that the carved residue is
> the *tame remainder* and proving it cascades is the live target — not a foreclosed one. Worked chain below.

### 9.8.1 The seal's full dependency chain

The seal stands `modulo {G3 (hClassify) + hcatch + hImprim + hShatter}`. Classifying each:
| Carried | Status toward "unconditional modulo citations" |
|---|---|
| **G3** (`hClassify`, Babai/Sun–Wilmes large-primitive⟹Cameron) | **Citation** (CFSG-based) — legitimately carried, never proved in-project. |
| **hcatch** (`WarmTwinsAreFiberTwins`, CFI-1992 Thm 5.2) | **Citation or small proof** — `dimWL(X)≤dimWL(X_α)+1`. |
| **hImprim** (block tower) | **Provable in-project** — deferred infra (~80% landed, recursion unbuilt), NOT a wall. |
| **hShatter** (node 4 = A2 open core) | **What (b) targets.** Decomposes below. |

So "unconditional modulo citations" = discharge `hImprim` (infra) and `hShatter` (the math), leaving only {G3 + hcatch}.

### 9.8.2 hShatter decomposes into TWO parts (not three — "part 2" was a phantom)

The seal's genuine case split (as wired in `_viaSmallAutShatters` / `_viaNoCover`) is **large-Aut vs small-Aut**, NOT
tight/thick vs loose:
> imprimitive → `hImprim` · primitive **large-Aut** → G3/Cameron (the legitimate cited "or Cameron") · primitive
> **small-Aut** → must cascade (`hShatter`).

So `hShatter` (the carved residue cascades) = exactly two pieces:
1. **Cleanup engine: bounded `minMult`/`L` (cascade rate) ⟹ `O(log n)` base.** **PROVABLE in-project** — the `(1+L)`
   generalization of the landed `§CC.20` halving engine (`exists_potential_descent`) + the `§CC.22` kill lemma: a best
   vertex leaves `≤ minMult` big sets, cleaned by `≤ minMult` further pins ⟹ base `O(L·log n)`. No citation. *Buildable now.*
2. **The carved residue actually cascades: primitive ∧ small-Aut ∧ non-geometric ∧ non-conference (schurian) ⟹ bounded
   cascade rate.** This is the open **rank-3 base case** — the single open theorem the seal reduces to. **Open and hard,
   but NOT barred:** no proven obstruction; CFI/FDF break the *general* (un-carved) statement, but the residue is exactly
   the remainder after those families are carved off (large→G3, conference→leg B, imprimitive→`hImprim`). Positive evidence:
   CGGP (`n^Ω(n^{2/3})` small-Aut SRGs, all base ≤ 2), 0 falsifiers, the amorphic-shatter probe (§9.7.2 Q1).

**Why there is NO "part 2 = thick⟹Cameron citation" (the earlier draft's error).** Multiplicity was a *measurement* of
cascade-ability (the probe), not a case split the theorem needs. The large/small-Aut dichotomy is the real one, and the
large-Aut branch is the *legitimate, always-kept* G3 citation (the "or Cameron" escape). The small-Aut branch — even when
the residue is geometric/thick (cf. CGGP, which is thick-ish yet small-Aut **and** cascades at base 2) — must be PROVED to
cascade; it is not routed to a citation. So discharging `hShatter` needs **no SRG-structure citation** beyond the G3 we
already keep for the large branch. The thick⟹Cameron framing conflated the multiplicity proxy with a needed case split.

### 9.8.3 What is, and isn't, within reach

- **Polynomial, unconditional modulo `{G3 + hcatch}` — the TARGET, reachable in principle.** It reduces to the *single*
  open theorem of §9.8.2 part 2 ("carved residue cascades"), discharged via the part-1 engine. `hImprim` is infra. No
  citation beyond G3 (large-Aut→Cameron) and `hcatch`. **This is the route's purpose** — open and hard, not foreclosed.
- **What §8.6 actually rules out:** no *citation* makes the seal polynomial — the largeness theorems (Babai/Kivva/Spielman)
  are sub-exponential. That is the **citation route's** ceiling, and the reason it was set aside: e.g. carrying **Spielman**
  gives `hShatter` unconditionally at `B=Õ(n^{1/3})` (cover branch vacuous, G3 even unneeded) — but Spielman alone already
  canonizes in sub-exp time, so the seal adds nothing there. **The direct cascade proof, not a citation, is how this route
  goes for polynomial.**
- **The realistic, genuine win (partial unconditionality + de-risking).** The `(1+L)` engine (part 1) is unconditional, and
  multiplicity is a *computable* handle, so the redirect lets us **peel off structural sub-classes of the residue with
  combinatorial (citation-free) bounds**, shrinking the open core: e.g. the landed PV sparse `2c(k−1)<n ⟹ b≤2`
  (`separatesAtBoundedBase_of_sparseSeparable`, low-degree residue) already does this; a coherence/counting bound on
  `minMult` for further sub-classes (bounded fiber-degree, specific intersection-number regimes) would extend it. The
  honest end-state is **cxt-scoping route 3**: seal `modulo {G3 + hcatch + (the rank-3-base-case predicate)}`, with as much
  of the residue as possible carved into *proved* sub-cases and the irreducible generic core carried as one named predicate.

### 9.8.4 Verdict + recommended build order

The redirect is the **right reformulation** (computable, combinatorial, aligns the carve with the seal's existing legs)
**and it is a legitimate direct attack on the polynomial bound** — the one piece of GI∈P-for-SRGs the project deliberately
isolates. It is **not blocked**; it is **unproven**. Polynomial-unconditional-modulo-`{G3 + hcatch}` is reachable iff the
§9.8.2-part-2 cascade theorem is proved — open, hard, but with positive evidence and no obstruction. Recommended order:
1. **Part 1 (the cascade-rate engine), unconditional — ✅ LANDED (2026-06-16, `§CC.20b`, axiom-clean, build green).**
   `exists_potential_descent_bounded` (bounded-cardinality-step generalization of `exists_potential_descent`, pure
   `Finset`/`Nat`), `BoundedConfusionMultiplicity B M` (the cascade-rate hypothesis — a `≤ M`-set halves `c`),
   `potentialCleanup_of_boundedConfusionMultiplicity` (`k` rides free), `exists_small_base_of_boundedConfusionMultiplicity`
   (→ base `T₀`, `card ≤ M·r`, `2^r ≤ max 1 (Φ ∅)` = `O(M·log n)`); seal capstone `reachesRigidOrCameron_viaBoundedMultiplicity`
   (`CascadeAffine §S-gate2`). **"Residue cascades (bounded `M`) ⟹ polynomial seal" is now a theorem** — the entire open
   content collapses to the single discharge `BoundedConfusionMultiplicity` (strictly weaker than `IndistinguishingHalves`,
   its `M=1` case). Seal `modulo {G3 + BoundedConfusionMultiplicity + hcatch + hImprim}`.
2. **Attack the cascade discharge.** ~~Sub-classes first~~ — **both counting sub-class leads are now closed (§9.5a PV-sparse
   dead; §9.5b raw counting trivial, the forced-triangle case already landed as δ′/`RainbowRigid`).** What remains is the
   generic primitive-small-Aut non-geometric residue = the thin-cover/low-`L` geometric core (§9.6) — the hard heart, attacked
   directly (no citation, the route's purpose), with no current technique.
3. **Honest floor if the generic core resists:** carry it as ONE named predicate (`BoundedConfusionMultiplicity` on the
   residue = the rank-3 base case), seal `modulo {G3 + hcatch + that predicate}` (cxt-scoping route 3). This is the
   *fallback*, not the target — the target (step 2) is the direct proof.
This converts "node 4" into {one proved engine + a shrinking carved frontier + the directly-attacked generic core}.
**Polynomial-unconditional is gated on proving the cascade theorem — open and hard, but unbarred; it is the route's
intended endpoint, not a wall (cxt-scoping risk (a): a falsifier would change the seal statement; 0 found).**

## 9.9 Option (i) — the direct thin-cover attack on node 4 (research plan, 2026-06-16)

> **What this is.** With both counting sub-class leads closed (§9.5a/§9.5b), the only path to *polynomial-unconditional*
> is the **direct geometric argument**: prove `¬ BigConfusionCover (X_T)` for the primitive non-Cameron residue at a
> bounded base, feeding `reachesRigidOrCameron_viaNoCover`. This section is the plan — the precise target, the
> decomposition, the gaps, the approaches, and the ranked near-term actions. Honest scope: node 4 is open research; this
> lays out where the provable scaffolding ends and the genuine frontier begins.

### 9.9.1 The target and the key reframing (resolves the CGGP block)

**Target (Lean):** for the residue at every over-`B` base `T`, `¬ BigConfusionCover (pointExtension X T)` — i.e. some
vertex `v` lies outside every confusion set of size `> c(X_T)/2`. Then `reachesRigidOrCameron_viaNoCover` (landed,
axiom-clean) gives the **polynomial** seal `modulo {G3 + hcatch + hImprim}`, G3 unused on the shattering path.

**The reframing that dissolves the earlier CGGP objection.** Recall the apparent wall (route-doc §8.2): "geometric ⟹
large Aut" is FALSE — the Fon-Der-Flaass / CGGP family is geometric (partial geometry from an affine plane) yet has
*trivial* Aut (non-Cameron). That looked fatal to "non-Cameron ⟹ no line system." **It is not, because the target is
the EXTENSION `X_T`, not the bare scheme `S`.** CGGP's own theorem says those geometric small-Aut SRGs have `base ≤ 2`
(`WL-dim ≤ 4`): individualizing 2 points + WL refinement **discretizes** them — so their line system *does not survive*
to `X_T`, and `¬ BigConfusionCover (X_T)` holds for them too. The bare-scheme geometry is a red herring; the question is
whether a confusion line system **survives individualization to a bounded base**. So:

> **Unified claim.** A primitive non-Cameron SRG has *no big-confusion cover surviving to a bounded base* — either because
> it has no line system (genuinely non-geometric, node 4) or because the line system **collapses under individualization**
> (geometric small-Aut, à la CGGP forced triangles, node 2). The collapse mechanism is the δ′ / forced-triangle engine.

This unifies the thin-cover route (option i) with the landed δ′/`RainbowRigid` route: a big confusion set survives
individualization *only if* it is rigid against forced triangles, which the probe (§9.7.2) + CGGP say happens only for
the **thick** (large-Aut/Cameron) line systems.

### 9.9.2 The decomposition (contrapositive: a persistent cover forces a contradiction)

Assume `BigConfusionCover (X_T)` persists at every base `T` with `|T| ≤ b` (a *stable cover* up to depth `b`). Derive a
contradiction with "primitive, non-Cameron, non-conference":

- **D1 — persistence ⟹ a rigid invariant line system.** The big confusion sets are `Aut(X_T)`-equivariant
  (`C(gα,gβ) = g·C(α,β)`); a cover stable across the stabiliser chain is an `Aut`-invariant family of near-maximal
  "confusion lines" (`card_bigClasses_mul_ge_of_cover`: `≥ n/c` of them). *[Provable scaffold — new Lean, from
  `IsSchemeAut.relOfPair_eq` + `dominatorReachable_map`; the foundation D2/D3 attach to.]*
- **D2 — rigid line system ⟹ a partial geometry on `S`.** The stable confusion lines organise into a partial-geometry /
  spread (grand cliques) on the bare scheme. *[The extraction; genuinely novel combinatorics — the probe found covers
  intrinsically LOOSE (§9.7.1), so the bet is that the **stable** (persistent-across-bases) sub-covers are regular where
  arbitrary ones are not. This is the tractable-novel piece worth attempting.]*
- **D3 — partial geometry on a primitive SRG ⟹ Cameron OR collapse.** A partial geometry is **thick** (grand cliques of
  size `→∞` ⟹ Johnson/Hamming ⟹ Cameron, carved by **G3** — contradicts non-Cameron) **or thin** (bounded thickness ⟹
  the affine-plane / BCN forced-triangle mechanism discretises at base `≤ O(1)`, so the cover does **not** persist —
  contradicts D1). *[Thick→Cameron = citable G3. Thin→collapse = CGGP — proven for the affine/FDF family, open in general.]*

The contradiction: persistence (D1) forces a line system (D2) that is either Cameron (excluded) or collapses
(contradicting persistence). So no stable cover exists ⟹ at some base `≤ b`, `¬ BigConfusionCover` ⟹ (cascade engine)
polynomial.

### 9.9.3 The gaps (where provable scaffolding ends)

- **G-equivariance (D1):** confusion-set / `bigClasses` equivariance + stability across the stabiliser chain. *Provable,
  low-risk, foundational; not yet in Lean.*
- **G-extract (D2):** loose stable cover ⟹ clean partial geometry. *The novel combinatorial heart; tractable-uncertain.
  The bet (stable ⟹ regular) is testable on the probe data before committing.*
- **G-thin (D3-thin):** thin partial geometry on a primitive non-Cameron SRG ⟹ forced-triangle collapse at bounded base.
  *The genuine open frontier (node 4 ∩ the affine-classification gap). CGGP gives the affine instance; no uniform proof.*
- **G-construct:** no parametric non-geometric residue family exists (§5 F2) ⟹ the row-4 case cannot be scale-probed.

### 9.9.4 Approaches

1. **Native forced-triangle / rainbow (the project's lane, best Lean-fit).** Show "thin or no line system ⟹ a *rainbow
   rank* from a bounded base," feeding the landed `dominatorReachable_of_rainbowRank`. Connects D3 directly to the
   `clebschZ4` machinery; the open piece is the *uniform* rank (clebsch has only a probe-extracted one). This is the most
   portable attack and the one that reuses the most landed infrastructure.
2. **Node-2 buildout (the citable rung).** Generalise `clebschZ4_closure` from sporadic `n=16` to the **affine / FDF
   family** via `dominatorReachable_of_rainbowRank` — formalises CGGP's `base ≤ 2 ⟹ WL-dim ≤ 4` (node 2). *Discharges a
   real sub-class, shrinking the seal to node 4.* Concrete, medium risk, real progress — but a rung, not the crux.
3. **Spectral / Neumaier (understanding only, NOT Lean-portable).** The smallest-eigenvalue structure (Neumaier
   geometricity, the partial-geometry parameters) to guide the combinatorial D2/D3 argument and the predicate — kept
   off the formal path (no spectral theory in Lean).
4. **Probe the row-4 cell.** Build sporadic non-geometric residues (Paulus `(25,12,5,6)`, the `(26,10,3,4)` family) and
   measure cover/`minMult`/rainbow-rank survival — de-risks the unified claim and sharpens the predicate where there is
   no scalable data.

### 9.9.5 Ranked near-term actions

1. **[provable, foundational] G-equivariance (D1).** Land confusion-set / `bigClasses` `Aut`-equivariance + stability
   (from `IsSchemeAut.relOfPair_eq`). The scaffold every structural argument needs; sharpens the predicate; reusable.
   *Recommended first step.*
2. **[provable, real rung] Node-2 buildout (approach 2).** Extend `clebschZ4` to the affine family — visible
   seal-shrinking, reuses `dominatorReachable_of_rainbowRank`.
3. **[research, the heart] G-extract (D2) on the D1 scaffold.** Attempt the line-system extraction from a stable cover;
   the genuine node-4 attack. Probe-test the "stable ⟹ regular" bet (action 4) first.
4. **[de-risk] Probe row-4 sporadics (approach 4).**

**Honest verdict.** D1 is provable scaffolding; node-2 (D3-thin for affine) is a citable rung that shrinks the seal;
**G-extract (D2) + G-thin (D3 general) are the open heart of node 4 — no current technique, the GI-adjacent frontier.**
The plan makes node 4 *attackable in pieces* (scaffold → rung → extraction) rather than monolithic, and pins exactly
which piece is the irreducible research gap. If D2/D3-general resist, the floor is cxt-scoping route 3 (carry the
predicate) — but the target is the direct proof.

### 9.9.6 Progress (2026-06-16) — D1 done; D2 reframed onto `minMult` and the thin side landed

**D1 LANDED, axiom-clean (`§CC.22c`).** Confusion-set equivariance (`confusionSet_perm`, `card_…`, `mem_…`,
`big_confusion_perm`) + the punchline **`confusionMultiplicity_perm`** (`mult(π v) = mult(v)` for a CC automorphism,
where `confusionMultiplicity v` = #big pairs through `v`). So **cover-load is `Aut`-invariant**: `minMult` is constant on
automorphism orbits, and on the *vertex-transitive* bare scheme it is literally constant `= L = (Σ_{big}|C|)/n` (no
min-vs-average slack).

**D1's invariance reframed D2 — the dichotomy is on `minMult` directly, not via abstract extraction.** Because `minMult`
is now a rigid invariant, the clean split is: **bounded `minMult` (thin) ⟹ cascade** (provable) vs **unbounded `minMult`
(thick) ⟹ Cameron** (D3, cited; **not** CGGP-blocked — CGGP is thin). The abstract "partial-geometry extraction" is needed
*only* on the thick→Cameron leg (D3), not for the thin side.

**The thin side LANDED, axiom-clean (`§CC.22d`) — the §9.6 `(1+L)`-cleanup, finally formalized.** `BoundedMinMult B M`
(some vertex in `≤ M` big pairs per over-`B` base) ⟹ `BoundedConfusionLoad B (M+1)` (`boundedConfusionLoad_of_boundedMinMult`:
the hitting set `{v} ∪ {α : (α,β) big through v}` distinguishes every big pair — `v` kills those it avoids, the endpoint
`α` kills those through `v`) ⟹ `BoundedConfusionMultiplicity B (M+1)` (`boundedConfusionMultiplicity_of_boundedMinMult`)
⟹ the polynomial seal. **So the entire cascade open content is now the single computable statement "the residue has
bounded `minMult`"** — the exact quantity the probe measures.

**Updated gap map.** The open content of node 4 is now precisely: **`BoundedMinMult` for the residue** = "non-Cameron
primitive ⟹ bounded `minMult` at every over-`B` base." Its complement (unbounded `minMult` = thick) is the D3 thick→Cameron
leg (cited Babai-thickness, the partial-geometry extraction lives here). **NEXT:** either (a) D3 — connect "unbounded
`minMult`" to "thick partial geometry ⟹ named family ⟹ Cameron" (the cited dichotomy, isolating the carried predicate);
or (b) the node-2 rung (affine/FDF via `dominatorReachable_of_rainbowRank`), which discharges a concrete thin sub-family.
The irreducible research gap is unchanged (a primitive non-geometric SRG keeps `minMult` bounded — no current technique),
but it is now a single *computable* predicate with the entire thin-side machinery proved beneath it.

### 9.9.7 D3 — the dichotomy capstone landed; the wall analyzed; the method of attack

**D3 wiring LANDED, axiom-clean (`reachesRigidOrCameron_viaBoundedMinMult`, `§S-gate2`).** The faithful large/small
dichotomy in the *achievable* quantity: carry `hSmallAutThin : ¬IsLarge → BoundedMinMult B M` ("small Aut ⟹ bounded
`minMult`"), `by_cases` largeness: large → cited **G3** → Cameron / `hImprim`; small → `boundedConfusionMultiplicity_of_
boundedMinMult` (§CC.22d) → `…viaBoundedMultiplicity` (cascade). **Strictly sharper than `…viaSmallAutShatters`** — asks
only *bounded* load, not *zero* load (`¬cover`), which the probe showed rarely holds (covers are loose). Seal `modulo
{G3 + hSmallAutThin + hcatch + hImprim}`.

**The wall (precise).** Discharging `hSmallAutThin` = **thick (`minMult` unbounded) ⟹ large Aut**. This is irreducible:
the **rook** graph is thick, needs `√n` base, and is saved *only* by its large Aut (it is Cameron) — δ′/forced triangles
give `√n` there, so thick **cannot** route to cascade. So "thick ⟹ large Aut" is unavoidable, and it is Babai's
individualization–refinement / SRG-structure theorem (CFSG-based) — a slice of GI∈P-for-SRGs. **No full portable proof
exists.** The wall is real and located exactly at `hSmallAutThin`.

**Method of attack (the realistic decomposition of `hSmallAutThin`):**
1. **Carried-citation sharpening — DONE.** `hSmallAutThin` is the sharpest faithful form: the `minMult`-form of Babai's
   structure theorem, in the computable quantity the probe measures, and *weaker* than the old `¬cover` carry.
2. **Threshold ladder (pick the honest endpoint):**
   - **Sub-exponential, citable, Cameron-free:** carry **Spielman** (every primitive SRG individualizes to discrete at
     `Õ(n^{1/3})`) ⟹ at `B = Õ(n^{1/3})` every over-`B` base is discrete (`minMult = 0`), so `hSmallAutThin` holds
     *unconditionally* — the seal is honestly sub-exponential and the largeness/Cameron machinery is unneeded. A clean
     `…viaSpielman` capstone is buildable (one carried literal, no G3). This is the **fully-citable floor**.
   - **Polynomial (the target):** `hSmallAutThin` at a poly threshold = the **open rank-3 base case**. No citation.
3. **Shrink the open scope — node-2 rung (the concrete next build).** Discharge `BoundedMinMult` for the **affine/FDF
   thin family** via the landed δ′/`RainbowRigid` (`dominatorReachable_of_rainbowRank`): δ′ closure gives *discrete* at a
   bounded base ⟹ `minMult = 0` ⟹ `BoundedMinMult` outright (no `¬IsLarge` guard needed). `clebschZ4` is the `n=16`
   instance; the gap is a *uniform* rainbow rank for the parametric family (real work, landed template). **This is NOT a
   node-4 ladder:** node 2 is the part CGGP *proved portable* (`base≤2⟹WL-dim≤4`), and the δ′/rainbow engine is uniform
   over rainbow-rigid families (a few rungs, not infinite). It does **not** extend to node 4 — the mechanism relies on the
   geometric forced-triangle structure node 4 lacks. Companion: **node 3** (bounded-eigenvalue Neumaier-exceptional = the
   *constructible* residue, Shrikhande/Chang) is a finite list, handled by Neumaier finiteness. So node 2 (this rung) +
   node 3 (finiteness) cover everything constructible, leaving **only node 4 — which has no known witness at all.**
4. **The CFSG-free Neumaier route — NOT a way through (record only, do not pursue).** The tempting chain thick ⟹ (Neumaier
   claw bound) Johnson/Hamming *parameters* ⟹ (identification) the named family ⟹ (group computation) large Aut **breaks at
   the identification step**: cospectral mates have equal parameters but different Aut — Shrikhande vs the 4×4 rook
   (SRG(16,6,2,2)), the Chang graphs vs `T(8)` (SRG(28,12,6,4)) — and these are *exactly* residue-vs-Cameron. So
   "named-family parameters ⟹ is the named family / large Aut" is false, and separating the cospectral mates needs the
   **dynamic** individualization behaviour (rook stays thick, Shrikhande shatters) = Babai's individualization–refinement.
   **★ CORRECTION (2026-06-17, §9.9.11 probe): the "needs CFSG to separate the mates" claim is 2-WL-SPECIFIC — 3-WL
   STATICALLY separates them** (`Probe_HammingLadder`: rook and Shrikhande share the 2-WL class-size histogram `[16,96,144]`
   but 3-WL gives 15 vs 31 colours). So the *identification* gap closes at WL-level 3, not only via dynamic individualization;
   2-rank failing was a 2-WL artifact. **But this buys NOTHING for node 4**, because the base is invariant under the WL level:
   `base_k ≥ b(Aut)` for all `k` (k-WL cannot split an Aut-orbit), and the probe measured `base_3 = base_2 = b(Aut)` (gap 0)
   on rook/Shrikhande/Hamming alike — the rook's `√n` base is its *group* base, which no WL level reduces. Identifying the
   family ≠ bounding the base; the wall is the base, not the identification. Neumaier buys **node 3** (bounded eigenvalue:
   finite exceptions + named families), **not node 4** (unbounded eigenvalue, where finiteness fails). So option 4 is a
   large spectral-theory build that arrives at the *same node-4 wall* by a costlier road, plus an extra identification gap.
   Value = a map of what spectral tools buy (node 3) and don't (node 4), not a path to the goal.

**Recommended continuation: the node-2 rung (step 3) — its pipeline-validation half is now LANDED (§9.9.9); the live
piece is a *uniform* rainbow rank.** The bridge + capstone (`boundedConfusionMultiplicity_of_completeBase` /
`reachesRigidOrCameron_viaCompleteBase`) route a δ′-discretizing thin family through the `…viaBoundedMultiplicity`
pipeline, validating it on a real discreteness witness (as `clebschZ4` did for δ′). **The remaining, harder node-2 work
is the family-level discharge: a uniform rainbow rank for a parametric affine/FDF family** (`dominatorReachable_of_rainbowRank`,
generalizing `clebschZ4_closure` off the n=16 sporadic), which feeds `reachesRigidOrCameron_viaCompleteBase`. The poly
discharge of `hSmallAutThin` for the non-geometric core (step 2-poly) is the long-horizon open frontier; the Spielman
floor (step 2-subexp) is the honest fully-citable fallback.

### 9.9.8 Row-4 sporadics probe — DONE (2026-06-17): hSmallAutThin holds on trivial-Aut data, 0 falsifiers

**Built + run, green: `A2MonovariantProbe.Probe_Row4Sporadics`** (approach 4 / action 4 of §9.9.4–§9.9.5). It loads
the genuinely-small-Aut non-geometric SRGs — **Paulus `srg(25,12,5,6)`, `srg(26,10,3,4)`, Chang `srg(28,12,6,4)`,
and the conference `(29,14,6,7)` family** — from the **verified Hanaki–Miyamoto catalogue** (`data/hanaki/as{25,26,28,29}.gz`,
the same source `CatalogueSchemeProbe` validates; no hand-transcribed adjacency), and measures the exact Lean objects
`BigConfusionCover` / `minMult` / `c(X_T)` on the **2-WL coherent closure** (`PairClosure` of the scheme's own rank-3
relation matrix — the conservative/hardest faithful view, §9.7 note) at bases ∅ / {0} / {0,v*}. `|Aut|` (capped
backtracking) classifies small-Aut (residue) vs large-Aut (geometric/Cameron); `Rook L(5)` + the catalogue's pseudo-Latin
`as25 #3` + `T(8)` (`as28 #6`) are the geometric thick-cover reference.

**Result — clean separation, no falsifier:**
- **42 small-Aut non-geometric SRGs — including many with `|Aut| = 1` (trivial) — ALL shatter:** `c(X_T)` collapses
  to a constant / 0 and `minMult → 0` at a base ≪ √n (typically {0} or {0,v*}). e.g. `srg(25,12,5,6)` `|Aut|=1`: `c` 15→…→0
  by base 2; `srg(26,10,3,4)` `|Aut|=1`: `c` 12→0 by base ≤2. **0 falsifiers** (no small-Aut SRG needs base ≥ √n).
- **The 3 geometric/large-Aut SRGs stay THICK:** `Rook L(5)`, `as25 #3` (pseudo-Latin), `T(8)` all keep `c=15/16` and
  `minMult = 7/9` through base 2, discretizing only at base ≈ √n = 5. Exactly the Cameron-side behaviour.

**Significance.** This is the **sharpest available test of `hSmallAutThin`**: the prior §9.7 evidence used Shrikhande/
Clebsch/Chang, which have a *biggish* Aut; this extends the 0-falsifier record to **genuinely-trivial-Aut** residue
(`|Aut|=1`), where the predicate is most exposed. `hSmallAutThin` holds on every constructible data point.

**Honest scope (unchanged — the probe does NOT close node 4).** All data is **bounded smallest eigenvalue**: n=25/26 are
`s=−3` (Paulus, **node 3** / Neumaier-exceptional), n=28 `s=−2` (Chang, exceptional non-line-graph), n=29 `s=0`
(conference, **leg B**). **Node 4 = unbounded `s`, non-geometric, small-Aut remains construction-bottlenecked** (CGGP is
the only known inhabitant, not codeable at scale) — no probe reaches it (§5 F2 / §9.9.3 G-construct). So the probe
**de-risks the unified claim and the falsifier question at trivial Aut, but the irreducible node-4 frontier is untouched**:
`hSmallAutThin` stays the open wall, now with strictly stronger empirical support beneath it.

### 9.9.9 Node-2 rung — first increment LANDED (2026-06-17): the δ′ → multiplicity-pipeline bridge

**The bridge + capstone are landed, axiom-clean, build green** (the step-3 "node-2 rung" of §9.9.7). They route the
δ′/forced-triangle **discrete-base** world into the new D1/D2/D3 **`…viaBoundedMultiplicity`** pipeline, validating that
pipeline accepts a real discreteness witness (the multiplicity analogue of how `clebschZ4_closure` validated δ′):
- **`CoherentConfig.boundedConfusionMultiplicity_of_completeBase` (§CC.22e).** A bounded *discrete* base `T₀` (`|T₀| ≤ M`,
  every point of `pointExtension X T₀` a singleton fiber — the δ′ deliverable
  `allSingletonFiber_of_dominatorClosure_pointExtension`) ⟹ `BoundedConfusionMultiplicity B M` for **every** `B`. Proof:
  `S := T₀` halves `c(X_T)` outright since `X_{T∪T₀}` refines the complete `X_{T₀}` (`indistinguishingNumber_mono`), whose
  `c = 0` (`indistinguishingNumber_eq_zero_of_allSingletonFiber`). **Sharpens the trivial `boundedConfusionMultiplicity_univ`
  (`M = n`) to `M = |T₀|`** — a δ′ bounded base becomes a *polynomial-grade* cascade-rate witness.
- **`reachesRigidOrCameron_viaCompleteBase` (§S-gate2).** Composes the bridge with `reachesRigidOrCameron_viaBoundedMultiplicity`:
  a thin family discretizing at a bounded base seals in poly time **with no `hSmallAutThin`/largeness guard** (it cascades
  outright; node 4 never invoked). Seal `modulo {G3 + hcatch + hImprim}`.

**What this is / isn't.** It is the *connective tissue* between the landed δ′ engine and the new multiplicity machine —
the pipeline-validation half of the node-2 rung, done. It does **not** by itself discharge a new family: feeding it needs
`hcomplete` (a discrete base), which the δ′ route already produces per-instance (`clebschZ4_discrete` for n=16; `viaG0powNeg`
for the `H={±1}` affine family). **The remaining node-2 content is the family-level `hcomplete`: a *uniform* discrete base
for a parametric affine/FDF family** — i.e. a uniform rainbow rank via `dominatorReachable_of_rainbowRank` (the genuine
combinatorial work, §9.9.7 step 3). That generalizes `clebschZ4` from the n=16 sporadic to an infinite family; the bridge
landed here is what such a family would plug into. Node 4 (the wall, `hSmallAutThin` for unbounded-`s` non-geometric) is
untouched, as expected.

#### 9.9.9a Node-2 rung — second increment LANDED (2026-06-17): the seal-level rainbow lift + the rank-counting node-4 boundary

**Two theorems, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green, nothing committed.** The first increment
(§9.9.9) wired the δ′ *discrete-base* world into the new multiplicity pipeline; this increment lifts the **rainbow-rigid
δ′ engine itself** to the seal level, as a *uniform family* capstone (the catch-up-free scheme-level route, not the
extension route), and validates that engine on the real non-affine residue:

- **`reachesRigidOrCameron_viaRainbowRank` (CascadeAffine §S-gate2, generic `n`).** The seal-level lift of `clebschZ4`'s
  mechanism to the **whole rainbow-rigid family**: any `SchurianScheme` that is `RainbowRigid` and carries a **rainbow rank**
  from a bounded base seals, by composing `dominatorReachable_of_rainbowRank` (forced-triangle closure in `S`'s **own**
  colours) into the citation-/catch-up-free `reachesRigidOrCameron_viaDominatorClosure`. **Carries only the standard
  {G3 + `hne` + `hrank` + `hImprim`}** — no `hSmallAutThin`/largeness/Cameron citation and **no `hcatch`**. This is the
  previously-missing connective tissue: the rainbow lift `dominatorReachable_of_rainbowRank` stopped at `DominatorReachable`;
  no seal capstone consumed it. The per-family residual is now purely combinatorial (`RainbowRigid` + a rainbow rank).
- **`clebschZ4_closure_viaRainbow` (ClebschConcrete).** Non-vacuity witness: the ℤ₄² Clebsch closure re-derived through the
  *family* lemma (vs the bespoke `domReach_of_rank_pin` of `clebschZ4_closure`), confirming the rainbow `hbase`/`hstep` data
  the capstone needs is satisfiable on genuine non-affine amorphic-NLS data (the `n=16` instance). The gap to a *sealed*
  instance is the deferred `SchurianScheme` (automorphism) structure on `clebschZ4Scheme` — the concrete next step (either a
  schurian promotion, or an iso-transport from the schurian affine `clebschScheme`).

**★ NODE-4 INSIGHT (rank-counting boundary — surfaced while building this).** `viaRainbowRank` is catch-up-free *because*
rainbow rigidity supplies forced triangles in the scheme's **own** colours, and a rainbow triangle needs **three distinct
non-diagonal colours ⟹ rank ≥ 4**. Node 4's core is a primitive **rank-3 SRG** (only two non-diagonal colours,
adjacency / non-adjacency) — so it has **no rainbow triangles at all**; the scheme-level δ′/rainbow engine is
**structurally inapplicable** there (a colour-counting obstruction, not mere difficulty). This sharply re-confirms the
node-2 / node-4 boundary and that node-2 carving **cannot leak into node 4**: node 2 = rank-≥4 amorphic (forced triangles
in own colours ⟹ 1-WL closes, the wall bypassed); node 4 = rank-3 SRG (forced structure, if any, lives only in the finer
**2-WL extension** colours ⟹ re-incurs `hcatch` + the `minMult` multiplicity wall). Corollary for strategy: any node-4
progress **must** work in the 2-WL extension arena (the existing D1/D2/D3 machinery); the scheme-level rainbow engine is a
rank-counting dead end there, so no amount of node-2 (rainbow) generalization approaches the wall — consistent with
"node 2 + node 3 cover everything constructible, node 4 untouched."

#### 9.9.9b Schurian-transport investigation (2026-06-17): `clebschZ4` is NON-schurian; the schurian rainbow-rigid Clebsch is AFFINE

**Goal:** promote `clebschZ4Scheme` to a `SchurianScheme` so it feeds `reachesRigidOrCameron_viaRainbowRank` (the first
*sealed* concrete non-affine residue). **Result: impossible for `clebschZ4` — it is non-schurian — and the finding
reshapes the node-2 value.** Computations (Python, on the extracted matrix + the F₁₆ cyclotomic scheme):

- **`clebschZ4Scheme` (on `ℤ₄²`) is a translation scheme** (colour depends only on `w−v` over the `ℤ/4 × ℤ/4` ring,
  natural id `k ↦ (k%4, k//4)`) — so translations are automorphisms (regular on vertices). **But its full `|Aut| = 32`
  only** (16 translations `⋊` an order-2 point stabiliser): the stabiliser of `0` is order 2 and is **not transitive on
  the size-5 colour classes**, so each rank-3 orbital (80 pairs) splits into **5 `Aut`-orbits** of 16 — the schurian
  axiom (one `Aut`-orbit per orbital) **fails**. It is a genuine *non-schurian* amorphic mate of the Clebsch parameters.
  `ℤ/4` is **not a field**, so this `ℤ₄²` scheme is non-affine in the project's sense (confirming clebsch's "non-affine
  residue" billing) — and the non-affine amorphic Clebsch is exactly the one that is non-schurian.
- **The cyclotomic `F₁₆` scheme (order-5 multiplier) = the affine `clebschScheme`** is **schurian** (`|Aut| = 160` =
  16 translations of `Z2⁴` `⋊` an order-10 stabiliser, the order-5 multiplier transitive on each class) **and
  `RainbowRigid`** (max rainbow `interNum = 1`, verified). It is on `Z2⁴` (elementary abelian = `affineScheme` form).

**Consequence (the node-2 value, sharpened).** At `n = 16` the schurian rainbow-rigid amorphic Clebsch is **affine**
(`clebschScheme`, leg-B-adjacent — its residual is the abelian translation group), and the non-affine amorphic Clebsch
is **non-schurian** (so it is *not* an `orbitalScheme H` residue at all — it never arises as a seal obligation). So the
genuinely-*new* (non-affine, schurian) territory `viaRainbowRank` could carve is **empty at `n = 16`**: the capstone's
real instances here are the affine cyclotomic family, where it gives a **citation-free** seal (removing the cyclotomic
2-separability citation of `…affineSlice`) but **no non-affine breakthrough**. The achievable instantiation is therefore
`viaRainbowRank` on `clebschScheme` — value = *citation reduction on the affine amorphic slice*, cost = a **noncomputable**
cyclotomic intersection-number proof of `RainbowRigid` (schurian is free; affineScheme is schurian by construction). This
is recorded as the concrete next option, **not** auto-pursued — it is an affine rung, and by §9.9.9a's rank-counting it
cannot approach node 4. The `clebschZ4` ClebschConcrete docstrings were corrected to state the non-schurian fact.

### 9.9.10 D2 stable-cover regularity probe — DONE (2026-06-17): the "stable ⟹ regular" extraction is REFUTED as a proof route

**Built + run, green: `A2MonovariantProbe.Probe_StableCoverRegularity`** (the §9.9.4 approach-1/action-3 "probe-test the
`stable ⟹ regular` bet *before* committing the D2 Lean extraction"). It is the one genuinely-novel node-4 lead — the only
proposed attack on node 4's *open heart* (G-extract D2) rather than a carve-around. The probe settles it negatively, which
is exactly what a probe-before-commit is for: it saves the cost of a Lean extraction built on a false premise.

**The precise bet tested (§9.9.2).** D2 needs: a *persistent* (stable-across-bases) big-confusion cover is a **regular
partial geometry**, so "persistent ⟹ regular line system ⟹ (D3) Cameron ∨ block" routes any stable cover to a carved leg,
and the residue (no stable cover) shatters. **Key reframe the probe isolates:** REGULAR ≠ TIGHT. §9.7.1 killed the
*tight/loose* (2a) framing (covers are intrinsically loose), but a *regular partial geometry* (the rook grid: every cell on
2 grid-lines) is **loose yet regular** (constant point-degree, constant line-size, two lines meet in ≤1 point). So the right
axis is **regular vs irregular**, which §9.7.1's `minMult`/`maxMult` never isolated. The trap it also pins: at base ∅ a
vertex-transitive scheme has constant point-degree *by D1* (`confusionMultiplicity_perm`) — regular for free, vacuous; the
genuine discriminators are line-size + the pairwise-**meet** (PG incidence) axiom at base ∅, and point-degree spread (over
non-base vertices) at a nontrivial base `{0}`/`{0,v*}`. Measured on the **faithful** scheme (§9.7.2), ρ=0.5, across the base
sequence; reuses `PairClosureBase`/`BaseSeqBase`/the Hanaki loader. New metric `Regularity` returns line-size spread + the
pairwise-meet distribution alongside the cover-load.

**Result — the bet FAILS on half (A), and the separator collapses back to the wall:**
- **(A) carved covers PERSIST but go IRREGULAR — 8/8 persist, 0 regular at the deepest base.** Rook L(4)/L(5), Triangular
  T(6)/T(8), the imprimitive controls (`4·K₄`, `K_{4×4}`), and the catalogue large-Aut references (`as25 #3` pseudo-Latin,
  `as28 #6 = T(8)`) all keep a thick cover to base `{0,v*}` (`c` never collapses) **but their point-degree spreads** under
  individualization: e.g. Rook L(4) `deg[33..33] → deg[10..33] → deg[1..4]`. So the *persistent* cover is **not** a regular
  partial geometry in the confusion-cover incidence sense — "stable ⟹ regular" is **false on the carved side**.
- **(B) residue covers shatter — 9/10 (the 10th is irregular, not regular); persist-AND-regular = 0.** Clebsch (amorphic),
  Shrikhande, all Paulus `as25/26 #*` (incl. `|Aut|=1,2`), conference `as29 #*` collapse to `discrete`/`minMult→0` by base
  `{0}` or `{0,v*}`. The residue-side prediction (no regular persistent cover) holds — but trivially, via shattering.
- **Negative cross-check at base ∅:** regularity does **not** separate residue from Cameron there either. Clebsch (residue)
  is `regular` (constant line-size 4) while Rook (geometric) is only `reg-deg` (sizes 6–8, 4 distinct meets) — the residue is
  *more* line-regular than the carved family. So no base-∅ regularity discriminant exists.

**Verdict — D2 regular-PG extraction is unfounded; do NOT invest Lean effort there.** The robust separator is **persistence
itself** (thick-cover vs shatter = bounded `minMult`), which is **exactly `hSmallAutThin`** — the existing wall (§9.9.7). The
regularity refinement adds **no new handle**: it does not let D2 extract a partial geometry from a stable cover (the stable
cover is irregular), and it does not give a base-∅ residue/Cameron discriminant. So G-extract (D2) via regularity collapses
back onto "thick ⟹ Cameron ∨ block" = `hSmallAutThin`, with no shortcut. **Consequence for the plan:** the §9.9.4 approach-1
(native forced-triangle/rainbow on a "thin or no line system") and approach-3 (spectral) lose their D2-regularity premise;
the live next builds revert to the *carve-around* progress — **node-2 rung uniform rainbow rank** (§9.9.9, shrinks the
residue) and the **Spielman floor** (`…viaSpielman`, the honest citable sub-exp cap) — not a direct D2 attack. Honest scope
unchanged: all residue data is bounded `s` (node 3 / leg B); node 4 (unbounded `s`) has no constructible witness, so the
probe de-risks the *method* (kills the regularity lead) without reaching node 4. Nothing committed (user commits).

### 9.9.11 k-WL ladder / Hamming hypergrid — DONE (2026-06-17): climbing k-WL is NOT a node-4 attack, and the c^k hypergrid is the carved leg

**Built + run, green: `A2MonovariantProbe.Probe_HammingLadder`** (+ a correct oblivious k-WL `KWLStable`/`KWLBase`/`KWLHistogram`
and a group-base `AutBase`). It answers two questions raised in investigating alternative node-4 attacks: (1) does the
indistinguishing-number concept climb the k-WL ladder into an exploitable pattern? (2) is the **c^k hypergrid** `H(k,c)` (the
natural generalization of the rook `= H(2,c)`) a build that "defeats k-WL" the way the rook defeats 2-WL?

**The two load-bearing facts (theory, then probe-confirmed).**
- **(i) `base_k(X) ≥ b(Aut(X))` for every `k`.** k-WL is iso-invariant, so it never splits two vertices in one Aut-orbit;
  individualization is the *only* symmetry-breaker. Hence the k-WL base is bounded below by the **group base** at every level.
- **(ii) constant-k-WL ≡ 2-WL + O(1) individualizations** (the project's carried `hcatch`, `dimWL(X) ≤ dimWL(X_α)+1`,
  CFI-1992 Thm 5.2): so `base₂ ≤ base_k + O(k)`. For constant `k` that is `base₂ ≤ base_k + O(1)` — climbing to any constant
  k-WL is absorbed into the seal's O(log n) base budget and changes nothing; `k = ω(1)` costs `n^{ω(1)}` (breaks poly). The
  base and the WL-dimension are **dual coordinates on the same quantity**, with `hcatch` the change of variables; "is the base
  bounded" = "is the WL-dimension bounded" = node 4.

**Probe result (decisive on both questions, and it corrects a naive reading):**
- **base = b(Aut) on every constructible row, and `base_3 = base_2` (gap 0).** Rook L4 `b(Aut)=base_2=base_3=4=√n`; rook L5
  `=5=√n`; H(3,3) `=3`; Shrikhande `=3`. So the base IS the group base, no WL level reduces it (Fact (i)), and **no
  constructible graph has `base ≫ b(Aut)`** (the would-be node-4 falsifier = a small-Aut graph with a large WL-dim gap).
- **The c^k hypergrid does NOT escalate — its base SHRINKS with dimension.** `base(H(k,c)) ≈ k·n^{1/k}`: rook (k=2) is `√n`,
  H(3,3) is `n^{1/3}=3 < √n`. So the rook (k=2) is the **extremal** thick case; climbing the Hamming dimension moves *away*
  from thickness, not toward a harder k-WL obstruction. (Corrects the natural "hypergrid is harder" intuition.)
- **Cospectral 3-WL separation (the §9.9.7 step-4 correction's evidence):** rook and Shrikhande share the 2-WL histogram
  `3 colours [16,96,144]` but 3-WL gives `15` vs `31` colours — 3-WL statically separates the cospectral mates that 2-WL
  cannot. So the "needs CFSG to identify the family" barrier is 2-WL-specific; **but identifying ≠ bounding the base**, and the
  base is `b(Aut)` at every level, so this gives no node-4 traction.

**Verdict.** Neither ladder is an exploitable node-4 attack. The k-WL ladder is the WL-dimension hierarchy, dual to the
individualization base via `hcatch`; constant-k is free in the seal's budget, growing-k breaks poly — so the wall
`hSmallAutThin` is **invariant under climbing**, not a level-2 artifact. The Hamming/hypergrid family is the **carved (Cameron)
leg** — large structured Aut, with `base = b(Aut)` (i.e. `hSmallAutThin` holds *with equality*) — and its base *decreases* with
dimension, so it is not even a worsening obstruction. The genuine node-4 falsifier (`base ≫ b(Aut)` at small Aut) has no
constructible witness, and no WL level or Hamming dimension can manufacture one (`base_k ≥ b(Aut)` always). **Useful payoff:**
the probe re-pins the open content as the **WL-dim gap `base − b(Aut)`** (the genuine-decision count beyond what Aut prunes) —
the sharpest statement of `hSmallAutThin` is "the residue's gap is bounded," with the group term `b(Aut)` already handled
(`exists_greedy_base_le_log` → O(log n) for small Aut). Same construction bottleneck (bounded-`s` data only). Nothing committed.

### 9.9.12 Hamming-twist (Doob) probe — DONE (2026-06-17): the sharpest constructible node-4 falsifier test comes back TAME

**Built + run, green: `A2MonovariantProbe.Probe_HammingTwists`.** §9.9.11 re-pinned the node-4 falsifier as a **small-Aut graph
with `base ≫ b(Aut)`** (a large WL-dim gap). This probe hunts one among the natural candidates — **twists of the Hamming
family**. The centerpiece is the **Doob graph `D(1,1) = Shrikhande □ K₄` (n=64)**: cospectral with `H(3,4) = K₄^□3` (same
distance-regular parameters) but with strictly smaller Aut (`|Aut|` **4608 vs 82944** — Shrikhande's 192 replaces the 4×4
rook's 1152 in one Cartesian factor). It is the Shrikhande/rook (n=16) contrast lifted one level: a clean small-Aut-vs-Cameron
cospectral pair, and the most structured constructible candidate for "thick at small Aut."

**Result — every small-Aut twist is TAME (`base = b(Aut)`, gap 0); no falsifier:**
| graph | n | \|Aut\| | b(Aut) | base₂ | gap |
|---|---|---|---|---|---|
| H(3,4)=K₄^□3 [Cameron] | 64 | >25000 (large) | large | 4 | — |
| **Doob Shrik□K₄ [twist]** | 64 | **4608** | **3** | **3** | **0** |
| Shrikhande [twist@16] | 16 | 192 | 3 | 3 | 0 |
| Chang as28 #5/#7 [twist] | 28 | 360/384 | 3 | 3 | 0 |

- **Doob D(1,1): gap 0.** Even a **composed** twist (Shrikhande folded into a Cartesian product, cospectral with a large-Aut
  Hamming graph) keeps `base = b(Aut)`. The twist shrinks **both** `|Aut|` and the base *together* — the gap stays 0. So the
  twist is the *opposite* of a falsifier: reducing Aut reduces the base in lockstep.
- **2-WL cospectrality confirmed:** `H(3,4)` and Doob share the identical 2-WL class-size histogram `[64,576,1728,1728]` — 2-WL
  genuinely cannot separate the small-Aut twist from its Cameron mate, so the largeness split is essential (the n=64 analogue of
  the rook/Shrikhande `[16,96,144]` collision).

**Verdict.** The Doob/Hamming-twist family is the sharpest *constructible* probe of the node-4 falsifier question (`base ≫
b(Aut)` at small Aut), and it comes back **negative** — extending the 0-falsifier record from the sporadic residue (§9.9.8) to a
**composed cospectral twist**. Combined with §9.9.11 (the WL ladder cannot manufacture a gap, `base_k ≥ b(Aut)`), this closes
off the two most natural "engineer a thick small-Aut graph" routes: climbing WL and twisting Hamming. **Honest scope unchanged:**
fixed `n ≤ 64` (no scalable small-Aut thick family, §9.9.3 G-construct), so this confirms the gap is `O(1)` at the constructible
sizes — it cannot rule out a gap *growing* with `n` (which would need an unconstructible witness = the open node 4). Nothing
committed (user commits).
### 9.9.13 Spielman floor — LANDED (2026-06-17): the fully-citable, Cameron-free sub-exponential end-state

**Two theorems, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green, nothing committed.** This is the
§9.9.7 **step 2-subexp** endpoint — the honest *floor* of the threshold ladder (§8.6): a seal that stands on a single,
concrete, replaceable citation (Spielman), with the entire largeness/Cameron machinery dropped.

- **`reachesRigidOrCameron_viaSpielman` (Cascade.lean).** Carries the **single** hypothesis
  `hSpielman : SeparatesAtBoundedBase S bound` — the residue individualizes a base of size `≤ bound` to `Discrete`
  warm refinement — and concludes the seal disjunction via the **rigid branch outright**
  (`Or.inl (Or.inr …)`). **It carries ONLY `hSpielman`: no `hClassify` (G3), no `hImprim`, no largeness/Cameron
  routing.** The Cameron disjunct is never taken — the residue discretizes, hence reaches rigid — so the whole "or
  Cameron" / largeness apparatus is *unneeded* at this threshold. That is the precise sense in which the floor is
  Cameron-free (contrast the live `…viaBoundedMinMult`, which carries the open `hSmallAutThin`, and
  `…viaSmallAutShatters`, which carries the Babai/Kivva largeness direction).
- **`schemeRecoveredByDepth_of_separatesAtBoundedBase` (Cascade.lean).** The reusable *positive* bridge:
  `SeparatesAtBoundedBase S bound ⟹ SchemeRecoveredByDepth n S bound`, via `stablyRecoverable_of_discrete`
  (discrete base ⟹ every cell a singleton ⟹ orbit at every `T ⊇ S₀`) then `schemeRecoveredByDepth_of_stablyRecoverable`.
  Where `PersistentTwinYieldsBlock` *derives* separation by refuting a persistent twin (the open crux), this consumes
  separation supplied **outright** — exactly what a discretization citation or the δ′ engine delivers
  (`separatesAtBoundedBase_of_dominatorClosure` already produces the hypothesis on real residues, so the capstone is
  non-vacuous).

**The citation and the threshold (what `hSpielman` faithfully is).** Spielman (STOC 1996): every **primitive strongly
regular graph individualizes-and-refines to discrete at a base of size `Õ(n^{1/3})`** — so for the primitive residue
`hSpielman` holds with `bound = Õ(n^{1/3})` *unconditionally* (no smallness/largeness guard; the cover branch of the
multiplicity route is vacuous because everything shatters). Imprimitive = the block tower (`hImprim` infra), conference
= leg B; folded into the one `SeparatesAtBoundedBase` deliverable. The **sub-exponential-vs-polynomial** distinction
lives entirely in how `bound` scales with `n`: `Õ(n^{1/3})` is the proven Spielman floor (here); a *polynomial*
`O(log n)` is the open rank-3 base case = node 4 (`hSmallAutThin`), which **no citation reaches**. So this is the
sharpest *fully-citable* (Cameron-free, G3-free) end-state of the seal, honestly sub-exponential and subsumed by
Spielman — it does **not** close the polynomial seal, which remains node 4. The remaining non-Spielman cleanup
(`hImprim` block-tower discharge, `hcatch` 1-WL↔2-WL exchange) is orthogonal and still open.

### 9.9.14 hcatch (the 1-WL↔2-WL catch-up) — analysis + the two discharge targets, route-B first increment LANDED

**`hcatch = WarmTwinsAreFiberTwins S T (X_T)`** ("same 1-WL `warmRefine` cell ⟹ same 2-WL `pointExtension` fiber") is
the project-model half of the **CFI-1992 individualization exchange `dimWL(X) ≤ dimWL(X_α)+1`** (Thm 5.2; Ponomarenko
arXiv:2006.13592 eq. (41)). It is carried by the 2-WL-extension capstones (the live `…viaBoundedMinMult`,
`…viaCompleteBase`, `…viaBoundedMultiplicity`); the scheme-level routes (`…viaRainbowRank`, `…viaG0powNeg`,
`…viaSpielman`) **do not carry it**.

**Key structural facts (verified against source).** `warmRefine` is genuine plain **1-WL** (recolour `v` by the
multiset of `(neighbour-colour, scheme-edge-colour)`); `pointExtension` is **2-WL** (finer). So `hcatch` is the
coarse⟹fine direction — **false in general** (probe: false at `T={0}`, true at `|T|≥2` for the residue). The honest
accounting (`warmTwinsAreFiberTwins_of_warmDiscrete` + `discrete_warmRefine_of_extensionComplete`) gives the decisive
reduction: **at a complete extension, `hcatch ⟺ Discrete (warmRefine …)`** — discharging `hcatch` *is* establishing
**1-WL discreteness at the base**, nothing more. So `hcatch` is **free wherever 1-WL discretizes** (scheme-level δ′,
rainbow, joint-profile separation) and **bites only at `n ≥ 25`** where 2-WL discretizes but 1-WL does not (the genuine
WL-dimension gap).

**Target A — reduce to an exact citation (CFI-1992 Thm 5.2).** `hcatch` is *already* annotated as exactly this
theorem. A faithful *formal* citation (stating (41) verbatim and deriving `hcatch`) needs a **`dimWL` framework**
(k-WL refinement, WL-dimension, the exchange's base-padding mechanics) the project lacks — real infrastructure
(~hundreds of lines), and it does **not** close anything. Lower ROI; the honest accounting below makes it largely
unnecessary for the residue.

**Target B — close directly (the better target), via the weaker version that suffices.** Because `hcatch ⟺ 1-WL
discrete at the base`, closing it is **the project's own open self-detection (`s(C)`) content**, not a separate WL-dim
theorem: the depth-1 (`s(C)=1`) case is already a landed piece (`discrete_of_jointProfileSeparates`), and the residual
`s(C)≥2` (iterated/cyclotomic, base + `O(1)`) case is the *same* open bounded-depth-separation engine the seal already
needs (`docs/chain-descent-self-detection-plan.md` §9.3). **So `hcatch` is not an independent gap — it collapses onto
the 1-WL self-detection content.**

**First increment LANDED (2026-06-17, axiom-clean, build green):** `warmTwinsAreFiberTwins_of_jointProfileSeparates`
(CascadeAffine) — discharges `hcatch` from the **checkable depth-1 joint-profile separation** (existing pieces:
`discrete_of_jointProfileSeparates` → `warmTwinsAreFiberTwins_of_warmDiscrete`). Strictly generalizes the
forced-triangle `…_of_dominatorClosure` (δ′ is one way to separate the profile), closing `hcatch` on the entire
**depth-1-separable** sub-class with no WL-dim citation. **Remaining:** the `s(C)≥2` iterated engine = the shared open
content (self-detection), the genuine direct-close target. Nothing committed (user commits).

### 9.9.15 SCOPE — the bounded-depth separation engine (closes hcatch's residual + the seal's s(C))

**Headline finding (verified against source): the "iterated separation engine" is ALREADY BUILT; what remains is
not infrastructure but the separation CERTIFICATE — which is the seal's own G2-B / `s(C)` crux. `hcatch`'s residual
and the seal's open self-detection are the SAME object.** So there is no separate engine to build for `hcatch`.

**What is landed (axiom-clean), the engine inventory:**
- **depth-1:** `discrete_of_jointProfileSeparates` (joint `(relOfPair t ·)_{t∈T}` profile injective ⟹ warmRefine
  discrete). The `s(C)=1` slice.
- **depth-2:** `twoRoundCount_eq_of_warmRefine`, `discrete_of_twoRoundProfileSeparates`, Lemma A
  `relOfPair_eq_of_refineStep_base`, `discrete_of_twoRoundRelationSeparates` (§13b).
- **general depth-`k`:** `kRoundCount_eq_of_warmRefine`, iterated Lemma A `relOfPair_eq_of_iterateRefineStep_base`,
  `kRoundProfileCount_eq`, `discrete_of_kRoundRelationSeparates` (§13c) — stated for any `AssociationScheme`.
- **orbit (non-base) analogue:** `RelCountsDetermineOrbit` + `cellsAreOrbits_of_relCountsDetermineOrbit`.
- **affine discharge:** `discrete_affineScheme_of_twoRoundDiffSeparates` (depth-2 engine on `affineScheme`).
- **hcatch bridges (this session):** `warmTwinsAreFiberTwins_of_jointProfileSeparates` (depth-1) +
  `warmTwinsAreFiberTwins_of_kRoundRelationSeparates` (depth-`k`, full strength) — `hcatch ⟸ the engine certificate`.

**The ceiling (why "more rounds" is not the lever).** The relation-count profile is the **k-independent** bounded-depth
invariant — `k` drives only the peeling in `kRoundProfileCount_eq`, so deeper rounds add **no** separating power. The
lever is **multi-base** (a larger `T`, base + `O(1)`), not deeper `k`: single-base depth-2 collapses to intersection
numbers (adds nothing); the cyclotomic separation is the *multi-coset* count at a Γ-breaking base of size `O(d)`.

**The open content = the certificate (NOT the engine).** Discharging the producers requires the separation hypothesis
`hsep`: *the count profile is injective across vertices* (base) / *determines the `Stab(T)`-orbit* (non-base,
`RelCountsDetermineOrbit`). This is the seal's open `s(C)` crux, in its mechanism-agnostic form
`PersistentTwinYieldsBlock` ("persistent count-twin ⟹ `ClosedSubset` ⟹ imprimitive"). It is **FALSE for high `s(C)`**
(a persistent twin is a non-congruence amorphic fusion), so it holds only for structured families; it is the GI-adjacent
G2-B wall. The project's own verdict: *the unconditional seal will not close from Mathlib alone.* The intended discharge
is the **fusion / closed-subset closure** (`schemeEquiv_trans`) — not yet built.

**Consequence for `hcatch`.** Since `hcatch ⟺ warmRefine discrete at the base`, and the engine produces exactly that
from the certificate, **`hcatch` is discharged on precisely the certificate-dischargeable class**: δ′ forced-triangle
families (rainbow-rigid, `…_of_dominatorClosure`), the `s(C)=1` joint-profile-separable primitives, and the affine
cyclotomic `s(C)=2` families (via the affine discharge). The residual biting case (general non-affine `s(C)≥2`) is the
**same** open certificate — closing it closes the seal's main crux, not a separate cleanup.

**Buildable (non-research) next pieces, ranked:**
1. **(DONE this session)** the depth-1 + depth-`k` `hcatch` bridges — `hcatch` now rides the full engine.
2. **`EdgeGeneratesFromSet`** — the *checkable* multi-base isolation closure (the relation-count analogue of
   `dominatorReachable_of_rainbowRank`): a structural sufficient condition that PRODUCES the certificate for a family,
   making recovery checkable. The single-base `EdgeGenerates` exists (`Scheme.lean`) but fails on cyclotomic/catalogue
   schemes (depth-1); the multi-base version is **deferred** by the self-detection plan (§9.3, "only needed to make
   recovery checkable on a concrete family — a Phase-2 concern"). Real infra, moderate; not on the seal's critical path.
3. **The certificate discharge** (`PersistentTwinYieldsBlock` via fusion/closed-subset closure) — the research wall =
   G2-B. Not routine.

**Recommendation.** The engine is complete; do NOT rebuild it. `hcatch` is now ridden on it (pieces 1, done). The only
genuine remaining work here is piece 3 = the seal's main open crux (research), with piece 2 as optional checkability
infra. So `hcatch` is effectively discharged-modulo-the-same-crux — it is no longer an independent line item.

### 9.9.16 SCOPE — hImprim (the imprimitive branch): infra built, content = constituent recovery

**Headline finding (verified against source): `hImprim`'s block-tower INFRASTRUCTURE is fully built; its open content
is `hqvis`/`hfvis` = the constituents' WL-recovery — the substrate-conditional A2-ii frontier, which (by the project's
no-sub-scheme-materialization design) is carried, not recursively reduced. So `hImprim`, exactly like `hcatch`,
collapses onto the same WL-recovery core as the primitive floor — it is NOT an independent cleanup item.**

`hImprim : ¬IsPrimitive → SchemeBlockRecovered ∨ AbelianConsumed` (carried by every seal capstone).

**What is landed (axiom-clean), the block-tower inventory:**
- **closed-subset extractor:** `exists_nontrivial_closedSubset_of_not_isPrimitive` (imprimitive ⟹ a nontrivial block
  system `I`, `ClosedSubset I`, `I ≠ {0}, univ`).
- **§11.1 gate** (`Scheme.lean`): the constituents stay transitive/schurian — `schemeBlocks_transitive` (quotient),
  `schemeBlock_fiber_transitive` (fiber). So the recursion's constituents remain in the schurian class.
- **Route B chain** (`Cascade.lean`): `orbitCoverage_of_blockDecomposition` (the wreath swap-decomposition — a
  cross-block orbit pair = block-swap `σ` ∘ fiber-move `h`, needing the *composition-closed* `closure (gensAt …)`) →
  `coversOrbits_of_blockDecomposition` (Phase-2: assemble full coverage from per-level block-reach + within-block
  coverage; induction stays **entirely on `Fin n`** — no sub-scheme materialized) → `reachesRigid_of_blockVisibleDecomposition`
  → `SchemeBlockRecovered`, with the consumer `schemeAutGroup_eq_closure_of_blockRecovered`.
- **leg B:** the abelian constituents route to `AbelianConsumed` (`abelianConsumed_of_residualAbelian`, citation-free).
- **producer (this session):** `schemeBlockRecovered_of_visibleRealizers` — the seal-facing PRODUCER naming the
  reduction: `ClosedSubset I` + sound `gens` + base + block-visible `hqvis`/`hfvis` ⟹ `SchemeBlockRecovered`.

**The open content = constituent recovery (NOT the tower).** The Route B chain's carried inputs are `hqvis` (the
**quotient**/block-action recovers — block-move realizers) and `hfvis` (the **fiber**/within-block action recovers —
within-block realizers). The doc's own verdict (`reachesRigid_of_blockDecomposition`): *"the remaining open content is
discharging `hreach`/`hfiber` from the constituents' recovery (the substrate-conditional depth-graded block-visibility,
A2-ii) — the honest frontier."* The "s(C) reduction-to-constituents" (exhaustive-obstruction §0.7.6) is
**sought-and-not-located**.

**Why it is not cheap cleanup.** The constituents live on the **same `Fin n`** via the block partition `β_I`
(deliberately — the project rejected materializing quotient/fiber sub-`AdjMatrix`es), so there is no clean
"smaller-`n`" IH to invoke the seal recursively. Discharging `hqvis`/`hfvis` is therefore a *direct* argument that the
block-level and within-block 1-WL recover — substrate-conditional content of the **same character as the primitive
floor / `hcatch` / the s(C) self-detection core**, reached one block-tower layer down. The two honest routes to close it
are (a) materialize the constituents + a genuine size-recursion (the rejected route, large), or (b) the direct
constituent-WL-recovery argument (= the open core). Neither is routine.

**Consequence for the seal's `modulo` set.** Combined with §9.9.14–§9.9.15: the live capstone's `modulo {G3 +
hSmallAutThin + hcatch + hImprim}` is, in honest substance, `modulo {G3 + [one WL-recovery / s(C) core]}` — the three
non-G3 hypotheses (`hSmallAutThin` on the primitive residue, `hcatch` on the 1-WL↔2-WL exchange, `hImprim` on the
constituents) are **facets of the same open object**, not four independent gaps. `hImprim` is now reduced (via the
landed producer) to the constituent-recovery interfaces; closing it = closing that shared core (one tower-layer down),
not a separable task. Buildable non-research residue: only the `EdgeGeneratesFromSet`-style checkable closure (§9.9.15
piece 2), shared with the engine.

### 9.9.17 Closure-angle reduction + literature pass — DONE (2026-06-17): the block escape is vacuous on the primitive floor; the crux is the 2-closure deficiency, which merges with Skresanov's rank-3 2-closure theory

**Two threads landed: (i) a literature SOTA check confirming the wall is open both ways + two deltas to the cited
record; (ii) the closure-angle reduction, worked against the existing Lean, which sharpens the open content and
exposes a vacuity in the stated discharge plan. One small axiom-clean lemma committed the finding.**

**(i) Literature SOTA (web-verified, 2026-06-17).** The node-4 wall (`hSmallAutThin`) is genuinely open in
mathematics — *no* citable theorem in either direction, *no* constructible falsifier. Confirmations: no poly SRG-iso
result is keyed on small-Aut/rigidity; NO primitive small-Aut non-geometric SRG with large WL-dim is known to exist
(and no SRG with provably unbounded WL-dim is known at all); every unbounded-WL witness (CFI / multipede / circulant)
is non-SRG and abelian/affine or imprimitive — i.e. exactly the families the seal already carves (leg B / `hImprim`),
which is **direct literature support for the closure angle** ("SRG" and "large WL-dim" are opposite ends of one
construction, Cai–Guo–Gavrilyuk–Ponomarenko 2023/Combinatorica 2025 = the project's CGGP cite). No IR/WL lower bound
touches primitive SRGs; spectral side-doors (bounded-multiplicity GI) are vacuous on SRGs (two Θ(n) multiplicities).
**Two deltas to the project's record:**
- **DELTA 1 — the sub-exp floor is `exp(Õ(n^{1/5}))`** (Babai–Chen–Sun–Teng–Wilmes, FOCS 2013), *not* Spielman's
  `n^{1/3}` (that survives only for the broader PCC class, Sun–Wilmes 2015). The `viaSpielman` floor / §8.6 / §9.9.13
  cite `n^{1/3}`. Caveat before re-citing: Spielman gives an *individualize-to-discrete at base Õ(n^{1/3})* statement
  (what `hSpielman`/`SeparatesAtBoundedBase` consumes); BCSTW is a canonical-form algorithm — confirm it yields a
  base/individualization statement before swapping the carried predicate. The floor *value* is `n^{1/5}` regardless.
- **DELTA 2 — a NEW directly-relevant citation: Skresanov on rank-3 2-closures** (2021, Ars Math. Contemp.,
  arXiv:2007.14696; 2023, J. Algebra 633, arXiv:2202.03746 — poly-time `G^(2)`). The schurian residue is `Inv(G)`,
  `G` a primitive rank-3 group; the open gap is `s(X)=b(X)−b(G)` = the 2-closure deficiency `G^(2)_T / G_T`.
  Skresanov 2021 (2-closure of a large-degree affine rank-3 group stays affine 1-dim) is the closest structural
  handle. Likely outcome: it *identifies* the affine rank-3 residue's 2-WL-closure with an affine scheme (= the
  already-handled affine slice), confirming/extending that carve rather than cracking node 4 — but it is the precise
  group-theoretic target of the closure angle and is **not currently used** here. (The carve-around path.)

**(ii) The closure-angle reduction — worked against the Lean, two findings.**

**Finding A — the open content factors, and (C) the group base is FREE.** The separation content
`SeparatesAtBoundedBase` factors (via `separatesAtBoundedBase_of_separable_of_small`, CascadeAffine §S-gate Bridge)
into **(A)** `Separable` (Ponomarenko Thm 4.1) + **(B)** the transport `SeparabilityTransports : Separable →
TwinsRealizedByResidualAut` + **(C)** a bounded group base `IsBase`. **(C) is already discharged** —
`exists_greedy_base_le_log` gives `b(G) ≤ log₂|Aut|`, and the seal's existing `¬IsLarge` antecedent makes that
`O(log n)`. So the open content is (A)+(B), which the docstrings show are *coupled through the general-CC substrate*
(the transport needs `s(X_T) ≤ s(X)`, a multi-fiber-CC fact the homogeneous `AssociationScheme`/`AlgIso` cannot
express). In one line: the open piece = *the point extension `X_T` recovers Aut-orbits at a bounded base* = no
2-closure deficiency = the `s(X)` wall. The Stage-2 route (`twinsRealized_of_extensionPointed`) is the live form:
pointed separability of `X_T` on non-singleton fibers + `hcatch` ⟹ the sink. Both routes' open input is the same
extension-separability / deficiency content.

**Finding B — the block escape is VACUOUS on the primitive floor (the correction).** `PersistentTwinYieldsBlock`'s
"⟹ block" disjunct needs a non-trivial proper `ClosedSubset`, which `IsPrimitive` forbids *by definition*. So the
docs' stated intended discharge — "the fusion / closed-subset closure (`schemeEquiv_trans`) generates a `ClosedSubset`
from a persistent twin ⟹ block ⟹ contradicts primitivity" — **cannot fire on a genuinely primitive residue**: the
generated closed subset is always `univ` there, never a block, so it yields no contradiction by itself. The block
construction discharges only the *imprimitive* case (already `hImprim`'s job). On the primitive floor the crux is
irreducibly `¬SeparatesAtBoundedBase → IsLarge` = the 2-closure deficiency / `s(X)` wall, with **no block shortcut**.
Committed as `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive` (Cascade.lean, axiom-clean
`[propext, Classical.choice, Quot.sound]`, build green) — a route-vanishes-on-the-primitive-floor guard, the
analogue of `intraCellRelations_eq_singleton_zero_of_primitive`. **Consequence:** do NOT attempt the fusion-closure
block construction expecting it to close the primitive crux; it is structurally vacuous there.

**The merge (why "closure-angle first" was right).** Findings A+B show the closure-angle reduction, on the primitive
floor, is NOT a block construction — its real content is the **deficiency-group trichotomy**: a WL-twin not realized
by a residual automorphism is an element of `Aut(X_T) \ Aut_T = G^(2)_T \ G_T` (the 2-closure deficiency), and the
claim "large `s(X)` ⟹ large ∨ abelian ∨ imprimitive (carved)" is a statement about that deficiency. That is **exactly
Skresanov's rank-3 2-closure structure** (DELTA 2). So the closure-angle and Skresanov paths *converge*: the
closure-angle's crux IS the Skresanov question. **Next:** the Skresanov path — does the rank-3 `G^(2)` description
make the deficiency `G^(2)_T / G_T` trivial-or-affine at a bounded base for the residue (a concrete affine-rank-3
carve capstone, sibling to the cyclotomic slice)? Node 4 (unbounded-`s`, the true wall) remains untouched. Nothing
else committed (user commits).

### 9.9.18 Skresanov reduction — DONE (2026-06-17): node-4-SCHURIAN is AFFINE; the genuine thick wall is non-schurian (a citation-factoring of `hSmallAutThin`)

**The Skresanov lead (§9.9.17 next-step) resolved into a structural reduction of the seal's open content, with caveats.
Headline: restricted to the SCHURIAN residues the seal actually handles, node 4 is AFFINE — it is not uncited open
math, it is a CFSG citation stack reducing to the affine slice. The genuinely-uncited "thick wall, no witness" is a
NON-schurian phenomenon that cannot be a seal residue.** This is a citation-factoring of `hSmallAutThin` (the analogue
of §8.5's `hNeumaier` factoring), NOT a closure: it trades open math for named citations.

**The chain (each step its citation).** A schurian rank-3 SRG residue has `Aut(X) = G^(2)` (the Wielandt 2-closure), a
primitive rank-3 *group*. Then:
1. **Cameron's rank-3 trichotomy** (CFSG): `G^(2)` is affine / almost-simple / grid-product.
2. **small-Aut (`¬IsLarge`) kills almost-simple and grid** — both are large-Aut Cameron families (grid `Aut = Sym(m)≀Sym(2)` ~ `(m!)²`, almost-simple socle large). So the **only small-Aut survivor is AFFINE** (`G^(2) ≤ AΓL_a(q)`). [= the seal's existing G3/Cameron carve, used contrapositively.]
3. **Skresanov [Skr21] (arXiv:2007.14696) Thm 1+2** pins `G^(2)` *explicitly affine*; for the 1-dimensional case `G^(2) ≤ AΓL₁(q)` (cyclotomic) **except a finite explicit list** (Table 7: degrees `2^4,2^6,…,89^2`; degree 64 = `2^6` has a nonsolvable `G^(2)`). [Skr23] (arXiv:2202.03746) computes `G^(2)` in poly time.
4. **Liebeck (1987) affine rank-3 classification** splits the affine survivors into (i) **1-dim cyclotomic** (Paley/Peisert/Van Lint–Schrijver) and (ii) the **forms-graph classes** (bilinear/alternating/affine-polar/half-spin/Suzuki–Tits).
5. **All survivors are `affineScheme`-shaped** (`orbitalScheme (affineG G₀)`, `G₀ ≤ ΓL_d`), hence in the structural domain of the project's affine-slice machinery. The 1-dim cyclotomic family seals via `reachesRigidOrCameron_affineSlice` (carries the **Ponomarenko cyclotomic 2-sep** citation `TwinsAreSemilinear`) or citation-free `viaG0powNeg` for the `H={±1}` sub-family.

**The merge with §9.9.9b — the unifying statement.** §9.9.9b found the non-affine amorphic (rank-≥4) residue is
**non-schurian** (clebschZ4, `|Aut|=32`, orbital splits 5-fold). Combined with the rank-3 result here:
> **Every small-Aut primitive SCHURIAN residue is affine** (rank-3 via Cameron+Skresanov; rank-≥4 non-affine amorphic
> is non-schurian, not a residue). The seal's primitive floor is entirely affine-structured. The "thick wall with no
> constructible witness" (`hSmallAutThin` at its hardest) is a **non-schurian abstract-SRG** phenomenon — and a
> non-schurian scheme cannot be the WL-closure `Inv(G^(2))` of an automorphism group, so it **cannot arise as a seal
> residue.** This reads the project's own 0-falsifier probe record correctly: catalogue SRGs that stay thick are
> large-Aut (rook, T(8)) = Cameron; every small-Aut one shatters — *because the small-Aut schurian ones are affine.*

**What it buys / costs.** Moves node-4-schurian from "uncited open, GI-adjacent" to the **citation stack
`{G3/Cameron + Liebeck + Skresanov + Ponomarenko-cyclotomic-2-sep + finite Table-7 exceptions}`** — exactly the
"conditional only on citations" target, but it ADDS citations beyond G3 (Liebeck, Skresanov) that a later pass would
want to discharge. The bounded-WL/separation itself still comes from the affine-slice machinery (Ponomarenko/δ′), NOT
from Skresanov (which gives only the *group* structure `G^(2)` affine, no WL-dim/base bound) — so Skresanov is the
*structural identification* (residue IS affine), the affine slice is the *recovery*.

**Caveats (do NOT paper over).**
- **(C1) The forms-graph classes are affine but NOT 1-dim-cyclotomic, and CAN be small-Aut + non-geometric.** Bilinear
  forms `H_q(2,m)` at fixed `m≥3`, growing `q`: `n=q^{2m}`, `|G^(2)|=poly(q)=n^{O(1)}` (small), smallest eigenvalue
  `~ -q^{m-1}` (unbounded ⟹ non-geometric). So node-4-schurian ⊋ cyclotomic — it includes forms-graph affine schemes.
  These are `affineScheme`-shaped (so structurally in domain) but their separability needs a citation OTHER than
  Ponomarenko's cyclotomic 2-sep. **VERIFICATION OWED:** confirm each Liebeck forms-graph class is either large-Aut
  (→Cameron, fixed-`m`/growing-`q` may NOT be) or has an available separability/WL-dim citation. This is the main hole.
- **(C2) CFSG-heavy:** Cameron/Liebeck/Skresanov are formalizable only as carried citations (like G3).
- **(C3) THE LOAD-BEARING ONE — is the residue schurian at all?** A canonizer residue is the **WL-closure** (a
  coherent configuration) of the individualized graph. A coherent config is schurian iff it equals `Inv(G^(2))` —
  which holds only when WL-dimension is low enough; a genuinely high-WL-dimension residue is a **non-schurian**
  coherent config. The seal is typed on `SchurianScheme`, so the reduction here covers exactly the schurian residues
  (= affine, handled). **If non-schurian residues can arise from the canonizer, they are precisely the open thick wall
  and sit OUTSIDE the seal's scope — the reduction is then a genuine advance for the schurian scope but NOT a closure
  of node 4.** Conversely, if the architecture guarantees schurian residues (or carries schurian-ness as a deliberate
  scoping assumption), node-4-schurian = affine = handled-mod-citations is the whole story. **This is the decisive
  check** — confirm against the canonizer's residue construction and the seal's scope discipline. (The project knows
  non-schurian schemes exist, §9.9.9b; whether they arise as *residues* is the open question.)
- **(C4) Skresanov Table-7 exceptions:** finite explicit degrees, handled by finiteness (like node-3 Neumaier exceptions).

**Lean direction (next, if pursued).** A conditional capstone `reachesRigidOrCameron_viaSchurianRank3Affine` carrying
the reduction "small-Aut ∧ primitive ∧ non-geometric ∧ schurian rank-3 ⟹ ∃ iso to an `affineScheme` satisfying the
slice's separability hypothesis" as a single named citation, routing through `reachesRigidOrCameron_affineSlice`. This
makes the citation-factoring a real (conditional) capstone — but it should wait on the (C1) forms-graph verification so
the carried citation is faithful (not silently assuming cyclotomic). Cites: [Skr21]/[Skr23], Liebeck 1987, Cameron 1981.

**Net.** The closure-angle (§9.9.17) said the primitive crux is the 2-closure deficiency; Skresanov says that for the
*schurian* residue the 2-closure `G^(2)` is affine and classified — so the deficiency is governed by known affine
structure, not open math. Node-4-schurian reduces to the affine slice modulo a citation stack; the open uncited wall is
non-schurian and outside the seal's residue class. **Subject to the (C1) forms-graph check + (C3) schurian confirmation.**
Nothing committed (user commits).

#### 9.9.18a (C3) RESOLVED — the seal IS deliberately scoped to schurian; the non-schurian wall is the IR-solver's, not the seal's

**Verdict (A), well-sourced from the project's own architecture.** The seal `reachesRigidOrCameron` is *deliberately,
provably* scoped to schurian residues; the non-schurian / high-WL-dimension term is split out by design and handled by
the honest flag + the (forward) IR-blind-spot solver — it is **not** an unacknowledged seal gap.

**The architectural separation (Lean-grounded).** `StablyRecoverable ↔ DiscretizesAtBases ∧ RecoversWhileSymmetric`
(`stablyRecoverable_iff_symmetric_and_bases`, Cascade.lean:3749). The two conjuncts are exactly the two terms:
- **`RecoversWhileSymmetric` = the `s(C)` self-detection term = the SCHURIAN part** (`CellsAreOrbits` at non-base
  prefixes; the seal's open content). The seal is keyed on the IR-core-FREE `SchemeRecoveredWhileSymmetric`
  (`reachesRigidOrCameron_viaSymmetricRecovery`, Cascade.lean:4255) — it **drops `DiscretizesAtBases` entirely.**
- **`DiscretizesAtBases` = the `IR_core` / multipede term = the NON-schurian / high-WL-dim part** = the *second
  guarantee* (flag-allowed), explicitly "*not a symmetry-completeness obligation*" (Cascade.lean:3740-3744, 3762).
The project maps these to the WL-dim axis directly (seal-handoff.md:502-504: "*rigidified full-rank linear coupling =
multipede (IR-core)*"; :50-51: "*rigid (multipede — high s(C) with trivial Aut) → IR-core, outside the seal*"). The
IR-solver owns "1-WL/2-WL does NOT discretize" (ir-blindspot-solver.md:74-76, the multipede target), gated on A2.

**Consequence for the Skresanov reduction — it genuinely reduces the SEAL's node 4.** Since the seal's obligation IS
the schurian (`s(C)`) part, and §9.9.18 shows the schurian small-Aut non-geometric residue is affine, the Skresanov
reduction **completes the seal's primitive-floor obligation modulo citations** (+ the C1 forms-graph check) — it is
*not* merely "advancing the schurian scope while node 4 stays open." Node-4-*for-the-seal* reduces to the affine slice.

**Where the genuine wall actually lives (the honest relocation).** The canonizer = seal (schurian; now affine-mod-citations)
+ IR-solver (non-schurian; **still flags** on its "row 4" = generic unbounded-`s` SRG residue where A2 / bounded-WL-dim
may FAIL; ir-blindspot-solver.md:102). So the genuine poly-GI wall is **not in the seal** — it is the IR-solver's row 4
(non-schurian, A2-may-fail ⟹ flag). The canonizer stays "polynomial-or-flag," flag set = exactly A2's row 4. The
Skresanov reduction resolves the seal's node 4 and **relocates** the open wall to the IR-solver (the forward payoff,
A2-gated) — it does not make the overall canonizer unconditionally polynomial.

**The remaining nuance (a separate, acknowledged gap — NOT closed by C3).** `SchurianScheme` is a **carried typing
assumption**, never discharged: the residue is *modeled* as `orbitalScheme H` (schurian by construction); there is no
theorem equating the canonizer's actual 2-WL-closure output to an `orbitalScheme H` (promoting a *computed* scheme to
schurian is documented INFEASIBLE, general-cc-separability.md:554-558). So the seal's completeness is relative to the
`orbitalScheme H` model; faithfulness of that model to the canonizer's output is its own modeling gap, orthogonal to the
Skresanov reduction. **Net: C3 confirms the Skresanov reduction is a real reduction of the seal's node 4 (mod citations +
C1), with the genuine open wall relocated — correctly, by design — to the non-schurian IR-solver row 4.** Nothing committed.

#### 9.9.18b (C1) RESOLVED — node-4-schurian = {1-dim cyclotomic (cited) + forms-graphs (c)–(f) (uncited, OPEN, but CONSTRUCTIBLE); (b) excluded as geometric}

**C1 (the §9.9.18 main hole) is resolved — and it partially walks back §9.9.18's "reduces to citations": the affine
reduction is correct, but the affine target is NOT fully cited.** Checking Skresanov's affine forms-graph classes (b)–(f)
at the small-Aut regime (fixed dimension, `q→∞`), against Brouwer–Van Maldeghem *Strongly Regular Graphs* (2022) + BCN:

- **(b) bilinear forms `H_q(2,m)` — EXCLUDED (geometric).** Smallest eigenvalue `s = −(q+1)` (verbatim BVM §3.4.1,
  double-derived) — it is the **q-analog of the rook's/Hamming graph `H(2,m)`**, the collinearity graph of a net
  `pg(q^m, q+1, q)`. Geometric ⟹ Neumaier-excluded. (The `−q^{m−1}` eigenvalue I had flagged was **wrong**.)
- **(c) affine polar `VO^ε_{2m}(q)`, (d) alternating forms on `F_q^5`, (e) half-spin `VD_{5,5}(q)`, (f) Suzuki–Tits
  `VSz(q)` — SURVIVE: small-Aut AND non-geometric.** All four have poly `|Aut|` (fixed dim / `q→∞`; e.g. (c)
  `|Aut|=n^{Θ(m)}`, (e) `~n^{3.9}`) and smallest eigenvalue `→ −∞` (`−q^{m−1}` / `−(q²+1)` / `−(q³+1)` / `−(q²−q+1)`),
  with no partial-geometry structure. So **node-4-schurian ⊋ 1-dim cyclotomic** — it includes these four forms-graph
  families. (Caveat: (c)/(d)/(f) parameters corroborated via Sage + arXiv + numeric checks but not fetched verbatim
  from BVM — worth a verbatim confirm before any formal citation; (b)/(e) are verbatim, high confidence.)
- **No citation covers (c)–(f).** All published bounded-WL-dim / poly-iso / separability results are for *other*
  families (cyclotomic/Paley WL-dim ≤3, Evdokimov–Ponomarenko/Ponomarenko arXiv:2006.13592; prime-power circulants ≤3;
  Fon-Der-Flaass ≤4, arXiv:2312.00460; abelian Cayley schemes). **Bounded WL-dim for the affine-polar / alternating /
  half-spin / Suzuki–Tits rank-3 families is OPEN** — an uncited residue, not closeable by citation.

**Net — the honest, sharper picture (corrects §9.9.18 and the "no witness" framing).**
1. **The Skresanov reduction is correct but incomplete as a citation-closure.** Node-4-schurian = affine =
   `{1-dim cyclotomic — CITED (Ponomarenko 2-sep / δ′) + forms-graphs (c)–(f) — UNCITED, OPEN}`. The forms-graph part
   is the genuine remaining open core *within the seal's schurian scope* — so §9.9.18a's "completes the seal's node-4
   obligation modulo citations" is **too strong**: it completes it modulo citations **only on the cyclotomic part**;
   the forms-graph part is open.
2. **MAJOR CORRECTION to the node-4 framing: the witnesses ARE constructible.** The project's "node 4 has no
   constructible witness / construction-bottlenecked" (§5 F2, §9.9.3, MEMORY) is **wrong** — the four forms-graph
   families (c)–(f) are explicit parametric small-Aut non-geometric primitive schurian rank-3 SRGs, the precise
   node-4-schurian witnesses, at growing `q`. The 0-falsifier probe record used the Hanaki catalogue (small `n`,
   bounded-`s` = node 3) and **never constructed these families at the unbounded-`s` (growing-`q`) regime.**
3. **They are PROBABLE and likely CONFIRMERS (not falsifiers) — the concrete next step.** Being schurian with poly
   `|Aut|`, their *group* base `b(G^(2)) = O(log n)` is free (greedy base); the open question is only whether 2-WL
   *achieves* discreteness at that base (the deficiency / `hSmallAutThin`), i.e. **bounded WL-dim for these specific
   classical schemes** — a far more tractable, concrete target than "all SRGs." Unlike the rook (thick because
   *large*-Aut, group base `√n`), these are small-Aut so cannot be thick *for group reasons*; a large WL-deficiency
   would be required, which a primitive classical scheme is not expected to have. **Recommended next: extend
   `A2MonovariantProbe` to (c)–(f) at growing `q`** — measure `minMult`/`c(X_T)` to test whether they shatter at
   `O(log n)` base (confirming `hSmallAutThin`, strong evidence) or stay thick (a falsifier ⟹ the seal would need
   restating — a real result either way).

**Updated modulo picture.** Seal node-4-schurian `modulo {G3 + Liebeck + Skresanov + [1-dim: Ponomarenko-2-sep] +
[forms-graphs (c)–(f): an OPEN bounded-WL-dim, no citation]}`. The open content is no longer a vague thick wall — it is
the bounded-WL-dim of four named, constructible classical-group families. Nothing committed (user commits).

#### 9.9.18c Forms-graph PROBE — DONE (2026-06-17): the affine-polar node-4 witnesses SHATTER; hSmallAutThin holds on the FIRST constructible unbounded-s family

**Built + run, green: `A2MonovariantProbe.Probe_FormsGraphs`** (the C1 §9.9.18b next-step). It constructs the **affine
polar graph `VO^ε_{2m}(q)`** (Skresanov class (c)) from scratch — a small finite-field arithmetic layer (`GFq`, prime +
prime-power via hardcoded irreducibles for GF(4)/GF(8)/GF(9)) + the quadratic-form Cayley construction — and measures the
1-WL individualization base (greedy best-fit for n≤81, first-fit upper bound for n=256) and the 2-WL cover trajectory
(`minMult`/`c`, n≤81) with the **existing** pipeline (`GreedyBaseCurve`/`Row4_CoverTrajectory`/`SrgParams`/`SmallestEig`).
This is the FIRST probe to reach genuine **node-4 (unbounded-`s`) witnesses** — every prior probe (catalogue/sporadics,
§9.9.8) was bounded-`s` = node 3.

**Construction validated:** `VO^-_4(2)` = `(16,5,0,2)` = **Clebsch** (the known residue); `VO^+_4(2)` = `(16,9,4,6)`;
`Rook(4)` = `(16,6,2,2)` — all match. `VO^-_4(3)`=`(81,20,1,6)`, `VO^-_4(4)`=`(256,51,2,12)` are valid SRGs.

**The result — the base TREND is the discriminator (the money shot):**
```
n            =  16    81    256
√n           =   4     9     16
VO^-_4 base  =   5     5      6     ← FLAT / bounded  (small-Aut non-geometric, s = −3,−7,−13 unbounded)  → SHATTERS
Rook(m) base =   4     9     (16)   ← = √n           (geometric, large-Aut)                               → THICK
```
So the small-Aut non-geometric affine-polar family — the C1 open residue — **shatters at a bounded base ≪ √n as `q`
(hence `s`, `n`) grows**, exactly the geometric/non-geometric dichotomy hSmallAutThin predicts: the *geometric* Rook is
thick (base = √n, its *group* base, large-Aut wreath); the *small-Aut* affine-polar base is flat (~5–6, ≈ O(log n):
log₂256 = 8 > 6) even as `s` → −∞. **0 falsifiers** (n≥64 targets; n=16 Clebsch is the validation anchor, small-`n` noise).

**Significance.** (1) **Corrects the "no constructible witness" framing** (§5 F2 / §9.9.3 / prior MEMORY): genuine
node-4 (unbounded-`s`) witnesses ARE constructible — the affine-polar family `VO^-_4(q)` at growing `q` — and they
**confirm** hSmallAutThin, the strongest empirical support yet (prior evidence was bounded-`s` node-3 catalogue data).
(2) **Strengthens §9.9.18:** node-4-schurian is affine, and the affine forms-graph residue (the open, uncited part)
empirically shatters at bounded base — the seal's node-4 prediction holds on constructible unbounded-`s` data, not just
node-3. (3) It does NOT close the residue: bounded-WL-dim for the forms-graph families stays UNCITED/OPEN (§9.9.18b) —
this is empirical support, a 3-point growing-`q` trend, only class (c) built ((b) excluded geometric; (d)–(f) harder,
not built). Honest scope: `VO^-_4(q)` is small-Aut only at fixed `m` (growing `m` at fixed `q` ⟹ super-poly Aut =
Cameron); `|Aut|` annotated analytically (poly, Skresanov), not enumerated (O(|Aut|)≈10⁵ too slow); n=256 base is a
first-fit upper bound. Nothing committed (user commits).

**▶ BREADTH EXTENSION (2026-06-17, §9.9.18c cont.): hSmallAutThin confirmed across THREE forms-graph classes.**
`Probe_FormsGraphs` extended (green) — added `GFq`-based builders for the **alternating forms graph `A(5,q)`** (class
(d): alternating 5×5 matrices, rank-2 adjacency) and the **Suzuki–Tits ovoid graph `VSz(q)`** (class (f): Cayley graph
on `GF(q)^4` with connection set = cone over the Suzuki–Tits ovoid, Tits automorphism `σ(x)=x^4` on GF(8)), plus a
cheap vertex-transitive parameter extractor (`SrgParams` is `O(n³)`, infeasible at these `n`), and pushed the (c)
affine-polar trend to `q=5`. Results:
- **(f) `VSz(8)` params = `(4096, 455, 6, 56)`, `s = −57` — EXACTLY the known Suzuki–Tits values** `((q²+1)(q−1), q−2,
  q(q−1), −(q²−q+1))` at `q=8`, validating the construction. This is the cospectral mate of `VO^-_4(q)` (same params)
  but with `Sz(q) ⊂ Aut` — a particularly sharp test. **Base = 9 ≪ √4096 = 64 ⟹ SHATTERS.**
- **(d) `A(5,2)` = `(1024, 155, 42, 20)`, `s = −5 = −(q²+1)`** (matches C1). **Base = 8 ≪ √1024 = 32 ⟹ SHATTERS.**
- **(c) extended:** `VO^-_4(5) = (625,104,3,20)`, `s = −21`. Base trend now **`[5,5,6,7]` for `n=[16,81,256,625]`**
  (√n = `[4,9,16,25]`) — flat/logarithmic, `≪ √n`.
- **(e) half-spin `VD_{5,5}(q)`: `n = q^16 ≥ 65536` — INFEASIBLE**, noted not built.

**Net: across 3 Skresanov classes (c affine-polar `q=2..5`, d alternating, f Suzuki–Tits), every small-Aut
non-geometric forms-graph node-4 witness SHATTERS at base ≪ √n (bases 5–9 vs √n 4–64), 0 falsifiers.** The bases grow
logarithmically (`O(log n)`), exactly the small-Aut prediction; the geometric Rook needs base = √n. This is
comprehensive empirical confirmation of `hSmallAutThin` on the **forms-graph residue** — the precise C1 open core —
across multiple classes and a genuine growing-`q` (unbounded-`s`, `s = −3..−57`) range, decisively refuting the "no
constructible witness" framing. Honest scope unchanged: empirical (single points for (d),(f); bounded-WL-dim stays
uncited/open); `|Aut|` analytic; large-`n` base = first-fit upper bound. Nothing committed (user commits).

**▶ SPIKE-K PART 1 EXTENSION (2026-06-24, `Probe_CoarseInvariantInjectivity`, green) — the FAITHFUL-invariant base, odd
`q` up to 9.** The `[5,5,6,7]` trend above used `CheapBaseSize` (plain 1-WL first-fit). This new probe individualises
`VO^ε_4(q)` under the **exact `VO⁻₄(3)`-`decide` invariant** `cnt(u;t₁,t₂)=#{y≠0:Q(y)=0,Q(y−(t₁−u))=0,Q(y−(t₂−u))=0}`
(char-sum-free; by the Gauss identity the count only sees `χ(det G)`, so it reflects the **coarse-invariant** separating
power — the object a uniform proof targets). Min base over 8 random restarts: minus `5,7,8,9` and plus `5,7,7,8` for
`q=3,5,7,9` (√n `9,25,49,81`). **(i) injectivity survives at every odd `q≥5`, both ε** (the coarsening does not kill it);
**(ii) base tracks `d+log₂q` to the integer** (logarithmic, the old `≈d+2` constant refuted); **(iii) base `≤ log₂n`** ⟹
within the `O(log n)` budget. `q=9`=GF(9) behaves like the primes. This is the existential de-risk for the plan's kernel
(plan §11.1 SPIKE-K block) — turns the empirical shatter into evidence the *uniform* kernel is provable, not just true.

#### 9.9.19 → Proof plan for the forms-graph families: `docs/chain-descent-formsgraph-wldim-plan.md`

The §9.9.18c empirical shatter is turned into a **proof target** in the dedicated plan doc
[`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md). One-line summary: the reduction is
mostly landed — **free group base** (`T = origin+basis`, `(G^(2))_T={1}`, `IsBase` via `exists_greedy_base_le_log`) +
the **landed depth-`k` engine** (`discrete_of_twoRoundRelationSeparates`) — so the whole proof is **one crux lemma**:
*the two-round relation-count profile at `T` recovers the form coordinates `B(v,e_i)`* (nondegenerate ⟹ injective ⟹
`hsep`). Uniform for the form-based families (c) affine-polar / (d) alternating / (e) half-spin (Mathlib `QuadraticForm`/
`BilinForm` available; `affineScheme G₀` already supports arbitrary `d`); (f) Suzuki–Tits is the outlier (ovoid, not a
form — separate). Stage A = a conditional capstone `reachesRigidOrCameron_viaAffineFormScheme` carrying the
probe-validated certificate (wiring now); Stage B = discharge the crux lemma for `VO^ε`. Closes node-4-for-the-seal
`modulo {G3 + Cameron/Liebeck/Skresanov + the affine-form certificate}`; the non-schurian IR-solver row 4 is untouched.

**▶ UPDATE (2026-06-18) — Stages A, B.0, B.1 + both isolation checkpoints all LANDED (axiom-clean, build green);
read the plan doc's HANDOFF box for the live state.** The above "Stage A wiring / Stage B discharge" framing is
superseded. The seal for the rank-3 SRG `VO^ε` residue (`affineScheme (similitudeGroup Q)`) is now reduced
**end-to-end** (`CascadeAffine.lean §OrthogonalForm`, `PublicTheoremIndex.md:1207, 1210-1233`) to **two isolated heavy
Mathlib builds**: **B.1c-i `OrbitIsIsotropyClass`** (Witt's theorem; ABSENT in Mathlib) + **B.1c-ii
`IsotropyCountsRecoverFrameQ`** (quadratic Gauss-sum / affine-quadric point counts). Checkpoint work is exhausted; the
next increment is a genuine heavy build (recommend B.1c-ii at `VO^ε_4(3)`). Full scoping: plan doc §8. The back-half
(`coords_determine`) and all wiring (`reachesRigidOrCameron_via{AffineFormScheme,OrthogonalForm,SimilitudeForm,CountsDetermineFrameQ,IsotropyCounts}`)
are landed.

**▶▶ UPDATE (2026-06-18 later) — the B.1c predicates are MIS-SHAPED; the "checkpoint exhausted / next = heavy build
B.1c-ii via `IsotropyCountsRecoverFrameQ`" framing just above is SUPERSEDED.** Finite probe over `VO^ε_4(3)`:
`IsotropyCountsRecoverFrameQ` / `CountsDetermineFrameQ` / `SimilitudeFrameSeparates` are **FALSE at the standard frame**
for `VO^-` (the one-round count is shell-blind via the frame's `e_i`-swap isometry symmetry). The scheme DOES discretize
(iterated WL), so bounded-WL-dim holds; the fix is a **symmetry-broken base** (`≈ d+2`, greedy size-4 at q=3) on which
the one-round count is injective. The landed B.1 capstones (idx 1221-1233) are axiom-clean but have unprovable
hypotheses as stated → need reformulation; the "recover-Q-profile-then-`coords_determine`" architecture is wrong for
minus-type. **Correct target = direct count-injectivity at the symmetry-broken base** → `discrete_of_kRoundRelationSeparates`
→ seal. The Gauss-sum toolkit for it (13 axiom-clean lemmas) is built in `ChainDescent/ScratchGauss.lean`. **B.0
(`viaOrthogonalForm`, isometry `O(Q)`) is UNAFFECTED.** Authoritative state: plan doc STATUS (the ⚠/⚠⚠ boxes).
