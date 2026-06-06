# Chain descent — the no-fusion battery + the largeness-via-deferral proof path (plan)

> **STATUS (2026-06-06): working plan, adjustable.** The durable piece is the **proof path** (§1) — the
> route to deriving leg C's *largeness* antecedent instead of hypothesizing it. The battery (§3–§5) is the
> empirical gate that validates the one substrate-conditional witness the path leans on. Fold the surviving
> conclusion into [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
> §0.7 (the bottom-up seal) and [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md)
> (Part A, where the order identity lives) once it resolves. **The plan may be revised as probes/constructions
> surface new patterns — see §7.**
>
> Companions: exhaustive-obstruction §0.7 (the mechanism-side seal, where "leg C ⟹ Cameron" lives),
> schreier-sims STATUS (Part A, `card_autP_eq_prod_of_base`), the deferred-decisions doc (`real_stays_real`).
>
> **Precursor LANDED (2026-06-06, axiom-clean, `Scheme.lean §12.1`).** Ahead of the battery, the §12
> capstone's largeness antecedent is now **traceable** via a *stated* bridge: `LargenessBridge`
> (`NonCascade m S → IsLargeScheme m S`, a named `Prop`), `exhaustiveObstruction_scheme_of_nonCascade`, and
> `exhaustiveObstruction_scheme_nonCascade_trichotomy`. This isolates the single substrate-conditional input
> the battery validates and gives **PP3 its concrete Lean target** — discharge `LargenessBridge` (currently a
> hypothesis) once `NoFusion` is validated. The bridge is stated, not proved (PP3 is the derivation). The
> doc-comment records the multipede caveat (sound to state only on the schurian-scheme class, which is
> vertex-transitive). Origin: exhaustive-obstruction §0.7.2 (3b) rec (2) / §0.7.5 "stated bridge LANDED".
>
> **PP1 + PP3 + PP2-core LANDED (2026-06-06, axiom-clean, `Cascade.lean` Part A).** The no-fusion predicate
> and the largeness-traceability engine are now first-class Lean objects (§1): `NoFusion` (PP1, the
> orbit-realizer coverage — the symmetry-only harvest reproduces every orbit, **no recovery hypothesis**),
> `reproducesResidual_of_noFusion` / `autP_reproduced_of_noFusion` (PP3, `NoFusion` ⟹ `closure = Aut^P ∧ |·| =
> ∏ orbit-sizes` via the landed order identity — largeness *read off the harvest*, no Babai / no WL-dimension),
> and `noFusion_of_visibleRecovery` (PP2 provable core — recovery ⟹ no fusion). **Routing finding:** PP2's
> axes-separation is already landed (`recoverableAt_base_iff_discrete`); the heavy Tier-0 disjoint-decoupling
> form is deferred (component-decomposition gap, strategy §15 gap 4). **PP3 reworded honestly** (§1): the order
> identity is unconditional; `NoFusion` is what makes the orbit product the *harvest's* output, so largeness is
> *derived from the witness*, not proven. The remaining open content is purely **whether `NoFusion` holds** —
> exactly what the battery (§3–§5) measures.

> **LARGENESS BRIDGE DISCHARGED modulo `NoFusion` — LANDED (2026-06-06, axiom-clean, `Cascade.lean` Part A).**
> The `LargenessBridge` is now a **proved theorem** (PP5), not a carried hypothesis. Class-agnostic graph core:
> `isLargeAutP_of_noFusion` (largeness read off the harvest, bare `AdjMatrix`) + the unconditional order-transport
> `isLargeAutP_of_isLargeProd`. Scheme discharge: `schemeAdj` (faithful scheme→labelled-graph encoding,
> `isAut_schemeAdj_iff`), `stabilizerAt_schemeAdj_empty_eq` (`StabilizerAt ⊥ ∅ = SchemeAutGroup`),
> `largenessBridge_viaHarvest` (proves `LargenessBridge`), and `exhaustiveObstruction_scheme_of_harvest` (the §12
> capstone with the bridge *supplied, not carried*). `IsLarge : Nat → Prop` stays the abstract super-poly citation.
> Only the cited `PrimitiveCCClassification` + the explicit, battery-validated `NoFusion` antecedent remain.

## 0. One-line goal

Close leg C's **largeness** antecedent by **deriving** it from a battery-validated **no-fusion** witness, via
the landed order identity `|Aut| = ∏ basic-orbit sizes`. Largeness goes from a free hypothesis on
`exhaustiveObstruction_scheme` to *derived-from-a-witness*, tightening "leg C ⟹ Cameron" to "modulo (cited
Babai classification + the no-fusion witness + the separate primitivity witness)".

## 1. The proof path (this is what defines the battery)

Work backward from what we would build *if* the battery shows no fusion. The key: **largeness becomes
derivable on already-landed machinery.**

- **PP1 — Name the property as a witness. LANDED 2026-06-06 (axiom-clean, `Cascade.lean` Part A):**
  `NoFusion adj P gens S` — the orbit-realizer coverage form: under a *defer-all-reals* policy (consume only
  certifiable/recovered symmetries, never make a genuine decision), the symmetry-only harvest's `gens`
  reproduces **every** `Aut_T`-orbit pair at every level `T ⊇ S` — i.e. it finds the **full** `Aut_S`. This is
  the **orbit-realizer** (not visible-cell) form, so it carries **no** recovery hypothesis: it asserts the
  harvest *found* the symmetry, independent of whether 1-WL *sees* it. `real_stays_real` is its soundness dual
  (deferred reals stay real ⟹ the harvest folds only genuine orbit pairs); `NoFusion` is the completeness
  dual, the single substrate-conditional witness the battery validates. Equivalently the stuck-state residual
  is **never small-but-non-trivial** — only *trivial* (IR-core) or *large*.
- **PP2 — the separable case. Provable core LANDED, general form routed around.** *Routing finding:* PP2's
  conceptual halves are **already landed** — the axes-separation (symmetry-consumption vs. IR-stickiness are
  independent) is `recoverableAt_base_iff_discrete` / `forcedNode_recoverable_iff_discrete`, and the
  coverage→group→order engine is `coversOrbits_of_realizers` (+ A3.5). The genuinely-provable separable
  sub-case is **`noFusion_of_visibleRecovery`** (`Cascade.lean`, axiom-clean): where orbits recover at every
  level (`CellsAreOrbits`) and the harvest collected the visible cell-mate realizers, `NoFusion` holds — *why
  metric/CFI (refinement-visible) symmetry never fuses*. The **fully-general Tier-0 disjoint-decoupling** form
  ("disjoint structure ⟹ `NoFusion`") is **deferred** — it needs the component-decomposition machinery that is
  a pre-existing project gap (strategy §15 gap 4, "assumed not proven"), not a cheap win.
  **Sharpened by Tier-3 (2026-06-06).** The consumption condition is **candidate-pinning** (recovery),
  **orthogonal to abelian-ness**: `noFusion_of_visibleRecovery` consumes *any* symmetry — including a non-abelian
  `S_k` over IR-core copies — once recovery pins the construct-and-check candidate (Tier-3: label-aligned IR-core
  copies ⇒ S₃ consumed). It is missed *only* when the candidate is unpinnable (matching 1-WL-resistant copies is
  GI-hard), and **every such miss the battery produced was decomposable** (separable / Tier-0). So PP2's separable
  case is not just a "friendly shadow" — it is **where all constructible hidden non-abelian symmetry lives**, and
  it is Tier-0-handled. The deferred general form is therefore precisely the **non-decomposable** residual (PP4).
  **SEPARABLE-DECOMPOSITION LEMMA LANDED 2026-06-06 (axiom-clean, `Cascade.lean` Part A):**
  `noFusion_of_warmSeparatedPartition` — `NoFusion` decomposes along a **1-WL-separated** partition `β : Fin n → ι`
  (sharing a `warmRefine` cell ⟹ same block) into **per-block coverage**, via `OrbitPartition.subset_warmRefine`
  (orbits refine cells ⟹ no orbit crosses a block). This is the divide-and-conquer the non-isomorphic separable
  case needs: the distinguishing witness `hsep` (parts 1-WL-told-apart, what canonizing distinct components
  supplies) + the per-component recursion `hcov` (itself dischargeable by `noFusion_of_visibleRecovery` where a
  block recovers). Strictly more general than `noFusion_of_visibleRecovery` on the separation axis (block-level
  separation, not full `CellsAreOrbits`). **Honest scope:** handles the **non-isomorphic** (1-WL-distinguished)
  components; the **isomorphic-copy / swap** case (blocks 1-WL-*indistinguishable*) fails `hsep` — those pairs
  cross `β`-blocks — and routes through recovery + the sort-key completeness gap (strategy §15 gap 4), still the
  substrate-conditional remainder. The full Tier-0 disjoint-union `AdjMatrix` construction (with the wreath swap)
  remains deferred (heavy `Fin`-reindexing + the assumed sort-key gap); this lemma is the reusable abstract core
  it would consume.
- **PP3 — largeness traceable from the harvest (the payoff, on landed machinery). LANDED 2026-06-06
  (axiom-clean):** `reproducesResidual_of_noFusion` / **`autP_reproduced_of_noFusion`** — under `NoFusion`
  with a terminal base, the folded harvest is **exactly** `Aut(G)^P` **and** `|Aut(G)^P| = ∏ basic-orbit
  sizes` (= `orbitSizeProd adj P bs ∅`), via the **landed** order identity `card_autP_eq_prod_of_base` /
  `card_closure_gensAt_eq_prod_of_coversOrbits`. *Honest framing (the reword):* the order identity holds
  **unconditionally** (it is `|Aut| = ∏ orbit-sizes` for any graph — K_n included); what PP3 buys is that
  under `NoFusion` the orbit-size product is **computed by the symmetry-only harvest**, so the **largeness
  predicate (that product super-poly) is read off the harvest** rather than asserted. So largeness is *derived
  from the `NoFusion` witness*, not proven unconditionally; "super-poly ⟹ large" stays definitional. This is
  the no-fusion analogue of `autP_reproduced_of_visibleRealizers`, but keyed on **orbit** (not visible-cell)
  realizers — so it needs **no recovery / no WL-dimension boundary**, and **no Babai** (the order identity does
  it). *(The multipede escapes cleanly: trivial residual, no orbit pairs to cover, so `NoFusion` holds
  vacuously and the product is 1 — small, not large; it is the IR-core, outside the seal.)*
- **PP4 — Carry the entangled case as a battery-backed witness.** Unconditional `NoFusion` = unconditional
  decomposability = the wall, so the entangled regime stays a witness (the battery is its evidence, exactly
  as the cascade backs `recoverableByDepth_cfi`). The structural bridge for the separable part is PP2.
  **Sharpened by Tier-3 (2026-06-06) — the witness's burden is now specifically the NON-DECOMPOSABLE residual.**
  The battery found **no** non-decomposable non-abelian fusion: every hidden non-abelian symmetry it could build
  decomposed into IR-core blocks under an outer `S_k` (calculator §7 "layered products decompose" confirmed
  empirically), and the *separable* part is PP2-provable (Tier-0). By the bottom-up route (non-consumed ∧
  non-abelian ⟹ primitive ⟹ Cameron, `Group.lean` Steps 2/4 landed), the non-decomposable residual **equals a
  genuine Cameron section — no third graftable species**. So PP4 reduces to "no non-decomposable non-abelian
  fusion outside Cameron": the witness is the *same* cited-Cameron boundary, now empirically backed (the battery
  could not exhibit a counterexample), not a new unmodeled object.
- **PP5 — Wire to the capstone. LANDED 2026-06-06 (axiom-clean, `Cascade.lean` Part A).**
  `exhaustiveObstruction_scheme_of_harvest` reaches the §12 Cameron conclusion with **largeness derived** and the
  `LargenessBridge` **discharged** (`largenessBridge_viaHarvest`), not carried. Two layers: the class-agnostic
  graph core `isLargeAutP_of_noFusion` (+ unconditional `isLargeAutP_of_isLargeProd`) on bare `AdjMatrix`, and the
  scheme discharge via the faithful encoding `schemeAdj` (`isAut_schemeAdj_iff`, `stabilizerAt_schemeAdj_empty_eq`:
  `StabilizerAt (schemeAdj S) ⊥ ∅ = SchemeAutGroup S`). Net: "leg C ⟹ Cameron" modulo (cited Babai classification
  + the explicit `NoFusion` antecedent inside `NonCascadeViaHarvest` + the *separate* primitivity witness), with
  `IsLarge : Nat → Prop` the abstract super-poly citation (never concretized). Primitivity stays its own
  depth-graded line (Shrikhande-evidenced; "imprimitive ⟹ recovers" is a secondary signal, **not** the largeness
  target).

**Net endpoint:** largeness is *derived from a battery-validated witness via the landed order theorem*, with
the genuinely-open residual now sharply pinned (Tier-3): it is the **non-decomposable ∧ recovery-resistant ∧
has-symmetry** case = a **genuine Cameron section** (no third species), the *already-cited* boundary — the
separable case is Tier-0-handled (PP2) and the consumption mechanism is candidate-pinning/recovery (orthogonal
to abelian-ness). This is a real tightening of leg C — the `NoFusion` gap collapses onto layers the project
already isolates (recovery/WL-dimension + Tier-0 + cited Cameron), with **no** room for a non-abelian fusion
species — not a closure of the wall.

## 2. The reduction chain (why this is the right target)

`leg C ⟹ large` ⟸ `small ⟹ consumed` (contrapositive) ⟸ **completeness of deferral** (deferring all reals,
the harvest finds every symmetry before any real is forced) ⟸ **no fusion** (no symmetry is 1-WL-entangled —
sharing cells — with rigid / genuine-decision structure in a way that gates its recovery on a real decision).

- `real_stays_real` (landed) gives **soundness of deferral**: a deferred real stays real, never lost, never
  masquerading as a symmetry. What is *open* is **completeness of deferral**.
- The exact gap: the oracle can only reach "every remaining decision is **uncertifiable**", and uncertifiable
  splits into *(a)* genuinely multiple orbits (real) and *(b)* a single orbit it cannot prove (a **hidden
  symmetry**, high WL-dimension). "uncertifiable = real" ⟺ no hidden symmetry ⟺ completeness ⟺ no fusion.
- The witness is substrate-conditional, and the **multipede** is why: trivial `|Aut|` yet high WL-dimension —
  so "small group ⟹ low WL-dim ⟹ recovers" is false in general. The multipede is the IR-core (trivial
  residual), *outside* the seal; the leak the battery hunts is the **small-but-non-trivial** analogue.

**Sharpened by Tier-3 (2026-06-06) — the split is the proof structure.** A small hidden non-abelian symmetry is
either **separable/decomposable** (it permutes IR-core blocks under an outer action — disjoint, or severed by a
small cut; **Tier-0 + per-block canonization closes it**, PP2) or **non-decomposable** (the genuine residual).
The battery could build *only* the separable kind (scrambled IR-core copies: harvest misses the `S₃`, but the
graph decomposes); the non-decomposable kind was **unwitnessable**, and by the bottom-up route equals a genuine
**Cameron** section (no third species). And the consumption mechanism is **candidate-pinning (recovery),
orthogonal to abelian-ness**: `small ⟹ consumed` is really `small ⟹ recovery pins the construct-and-check
candidate`, which fails *only* on the WL-resistant matching of *separable* IR-core blocks (Tier-3: aligned copies
consumed, scrambled missed). So the open content of `NoFusion` is exactly **non-decomposable ∧ recovery-resistant
∧ has-symmetry = genuine Cameron** — already the cited boundary, not a new unmodeled species. This collapses the
"completeness of deferral" gap onto the WL-dimension/recovery layer ("B's core") the project already isolates,
*plus* the separate (Tier-0) decomposition handler — with **no** room left for a non-abelian fusion species.

## 3. The decisive measurement

For each graph `G`: brute-force ground-truth `Aut(G)`; run the **recovery-only** (defer-all-reals) harvest;
classify the stuck-state residual:

| Residual at stuck state | Verdict |
|---|---|
| **trivial** | IR-core — fine (the rigid pole) |
| **large** (super-poly / matches a large `Aut`) | expected for hard symmetry — fine (this *is* largeness) |
| **small-but-non-trivial** + harvest `⊊ Aut` | **fusion leak** — a small symmetry not found without a real decision |

> **Decisive signal:** recovery-only harvest `⊊ Aut(G)` **while `|Aut(G)|` is small (poly)**. The size split
> is essential — harvest `⊊ Aut` with `|Aut|` *large* is **expected** (largeness, not fusion). Only the
> *small-and-incomplete* case is the leak. Property holds iff no graph (especially Tier 3) yields it.

## 4. The battery (tiers + targets)

Each tier is tied to a proof obligation. **Not limited to four constructions — breadth is welcome; the
constructions most likely to surface new behaviour are the products and the engineered adversarial ones.**

- **Tier 1 — Controls (validate the measurement + PP2's separable case).** Pure symmetric (Cₙ, Kₙ, Johnson,
  Hamming, Petersen — should recovery-harvest the full `Aut`); pure rigid (multipede on a circulant base —
  trivial residual, the IR-core pole); disjoint unions (multipede ⊔ Cₙ, multipede ⊔ Johnson — separable, must
  fully harvest the symmetric factor). A failure here falsifies the *measurement itself*.
- **Tier 2 — Operation closure (test `NoFusion` preserved under graph operations).** The informally-tested
  ones — pendant leaf, bipartite clone, CFI layer — are **least likely to show new results** (re-run for
  closure confirmation, low priority). **Drop vertex blow-up** (already known to be identified by
  construction — separates trivially, no stress). **Use lexicographic / tensor product** (and possibly
  *multiple* products) — products are the classic structure-fuser and double as a Tier-2/Tier-3 bridge (most
  likely to *create* shared cells).
- **Tier 3 — Adversarial engineered entanglement (the decisive core).** Actively *try to construct fusion*:
  graft a small (ideally non-abelian) symmetry *onto* a multipede so its orbit shares 1-WL cells with rigid
  genuine-decision vertices; CFI over a high-WL / multipede-like base; a rigid high-WL core with a small
  automorphism permuting parts of it. **The point is to test the limit — even finding a fusion is a place to
  work from** (it is the exact small-non-abelian/rigidity-entangled object the theory predicts is hard to
  build; characterizing it sharpens the seal). The battery "passes" iff every viable construction yields
  recovery-only `= Aut`.

## 5. Implementation notes

> **Increment 1 LANDED (2026-06-06) — instrument built + Tier-1 validated.** `GraphCanonizationProject.Tests/FusionBatteryExperiment.cs`.
> - **Recovery-only mode** — `ChainDescent.RecoveryOnly` (additive, gated, default off ⇒ zero regression;
>   9 deferral/linear/cascade tests still green). At the Phase-1/Phase-2 boundary (a node where every cell is
>   a real decision) it stops instead of branching the rigid residue; `Automorphisms` then holds the
>   symmetry-only harvest, `StuckResidual` records whether a real-only node was hit. This is the
>   deferred-decisions §7 "rigid-residue hand-off", previously unbuilt.
> - **Ground truth** — colour-aware brute-force `|Aut|`, **BFS-ordered + 1-WL-filtered + node-capped**
>   (naive in-order backtracking is *exponential* on rigid multipedes by construction — the runtime lesson;
>   the cap + BFS order + colour filter make it ms-fast). Verified exact against the Cameron closed forms.
> - **Colouring matters** — the multipede is the IR-core only *vertex-coloured*; its raw adjacency keeps the
>   circulant base's `Dₘ` symmetry. The harness seeds vertex types into both the descent `P` (TC-free
>   `SeedFromTypes`, type-< already transitive) and the brute-force initial colour.
> - **Tier-1 validated (all pass, <1 min):** cascading Cameron ⇒ harvest **= Aut** (Clean); coloured
>   multipede ⇒ harvest 1 = Aut 1 (TrivialResidual); multipede ⊔ C₇ ⇒ harvest = 14, **stuck** (Clean — the
>   separable case PP2 working empirically); verdict scramble-invariant.
>
> **Increment 2 LANDED (2026-06-06) — Tier-2 products + orbit-based leak triage (harness-only).**
> - **Product generators** — `Tensor` (categorical) and `Lex` (lexicographic, the wreath structure-fuser).
> - **Leak triage** — sharpened to an **orbit-partition** comparison (the faithful "fusion = missed symmetry"
>   criterion): `MechanismGapB` = harvest recovered the full Aut-**orbit** partition but a proper subgroup
>   (representation/transversal gap, *not* a missed symmetry); `AbstractFusionA` = harvest's orbits are
>   strictly **finer** than Aut's (a genuine symmetry unreachable without a real decision = fusion). The
>   full-canonizer harvest is logged as a cross-check that the canonizer itself reaches Aut. Both branches
>   validated deterministically (`Triage_DistinguishesMechanismFromFusion`, Z₅ vs trivial harvest on C₅).
> - **Tier-2 result (all Clean, <0.2s):** every product preserves NoFusion — `C5×C3` (|Aut|=60), `C5×C5`
>   (200), `C5[K2]` (320), `C4[K2]` (128) all give harvest **= full Aut**. Products of cascade-class graphs
>   do not fuse. 13/13 battery tests green.
>
> **Increment 3 LANDED (2026-06-06) — Tier-3 adversarial grafts + the decisive finding (harness-only).**
> Constructions: `KCopies`/`KCopiesScrambled` (k interchangeable IR-core copies ⇒ `Aut ⊇ S_k`, non-abelian),
> `AddHub` (connect copies symmetrically), CFI(K4); plus a **decomposability probe** (`ComponentCount`,
> `LeakIsDecomposable`) splitting a leak into **SEPARABLE/layered** (disconnected or a small cut decomposes it —
> calculator §7 "layered products decompose", Tier-0/IR-core, *not* fusion) vs **GENUINE connected fusion**
> (`AbstractFusionA ∧ ¬decomposable` — the jackpot). 17/17 battery tests green, ~5s.
>
> **Result — no genuine fusion was constructible; the one leak found is separable.** Outcomes:
> - **CFI(K4)** (abelian gauge, |Aut|=192): harvest **= Aut**, Clean — the gauge cascades and is consumed
>   (confirms §0.7.4: abelian is not a fusion species).
> - **Label-ALIGNED copies** (disjoint and hub-bridged, |Aut|=S₃=6): harvest **= 6**, Clean — the harvest's
>   **construct-and-check certifies the non-abelian copy-swap DIRECTLY**, even over 1-WL-resistant IR-core
>   copies, because the role-preserving swap maps corresponding cells (refinement-visible).
> - **Label-SCRAMBLED copies** (|Aut|=S₃=6): harvest **= 1** (misses the whole S₃) ⇒ `AbstractFusionA` — BUT
>   **decomposable** (3 components) ⇒ SEPARABLE/Tier-0, the IR-blind-spot wearing a symmetry hat, *not*
>   genuine fusion.
>
> **Proof-relevant insights (the watch-items):**
> 1. **The harvest's copy-swap completeness is exactly "is the candidate refinement-pinned?"** Aligned copies
>    ⇒ unique role-preserving candidate ⇒ consumed; scrambled IR-core copies ⇒ matching is GI-hard, no unique
>    refinement-pinned candidate ⇒ missed. This is `colourMatchPerm`/M-B's recovery dependency made concrete:
>    construct-and-check succeeds iff recovery pins the candidate (declassing §9 "B's core", the localisation
>    layer) — and crucially that dependency is **orthogonal to the symmetry's abelian/non-abelian-ness**.
> 2. **Every hidden non-abelian symmetry the battery could build is SEPARABLE** (decomposable into IR-core
>    blocks) — calculator §7 "layered products decompose" confirmed empirically. The missed S₃ is an *outer*
>    action over independent IR-cores (Tier-0 + per-block canonization closes it), **not** a non-decomposable
>    Cameron-free fusion. No connected non-decomposable non-abelian leak was constructible — supporting the
>    seal's bottom-up route (non-consumed ∧ non-abelian ⟹ primitive ⟹ Cameron): the only non-consumed
>    non-abelian symmetry is a genuine Cameron section, with **no graftable third species**.
> 3. **PP2's separable case is vindicated and its scope sharpened:** the separable regime is *precisely* where
>    hidden non-abelian symmetry lives, and it is Tier-0-handled. So "leg C ⟹ large ⟸ NoFusion" splits cleanly:
>    the separable part is provable (Tier-0 / component decomposition), and the entangled part has **no
>    constructible counterexample** — strong empirical support that `NoFusion` holds outside genuine Cameron.
>
> **Caveat (honest):** raw `ChainDescent` (the harness) does not apply Tier-0 component decomposition, so the
> scrambled-copy leak is an artifact the *full* canonizer (`CanonGraphOrdererChainDescent`, which decomposes)
> closes; the decomposability proxy correctly flags it SEPARABLE. Confirming Tier-0 closure end-to-end (run the
> per-component harvest + match) is a deferred refinement; it does not change the conclusion (no genuine fusion).

- **Recovery-only mode.** A descent that consumes only certifiable/recovered orbits and *stops* a branch
  rather than making a genuine decision (sidesteps the a-posteriori-needs-leaves tension). Reuses the
  cascade/recovery oracle; the new pieces are the defer-reals control flow + the residual-size classifier.
- **Ground truth.** Brute-force `Aut(G)` (independent of the canonizer), as the Cameron battery already does;
  compare `|recovery-only harvest|` to `|Aut|`. **Must be refinement-pruned + capped** — naive backtracking
  is exponential on the rigid multipede inputs.
- **Reuse.** `CameronGraphGenerator.cs`, `MultipedeGenerator.cs`, and the `Tier2DecompositionExperiment`
  harness already provide most generators + the harvested-Aut comparison; Tier 3 is the main new generator work.

## 6. Outcomes (both are progress)

1. **No fusion across the battery (esp. Tier 3) →** PP1–PP5 proceed; largeness derived modulo the witness;
   "leg C ⟹ Cameron" tightened. Best case.
2. **A fusion witness found →** the exact small-non-abelian/rigidity-entangled object. Worse than covering the
   limit, but **a concrete place to work from**: characterize it, decide whether it refines the seal (a new
   capability leg, a re-route, or a sharpened IR-core boundary), and feed it back into the proof path. A
   stress test exists to find limits; either result advances the picture.

## 7. Standing note — watch for patterns feeding the proof path

While building generators and running probes, **actively watch for structural patterns useful to the proof
path** — the experimental track has repeatedly surfaced the next lemma (Shrikhande pinned A2-iii; the F2
audit fixed the flag classifier). Specifically keep an eye out for:

- which entanglement attempts 1-WL *resists* (separates) vs *absorbs* (fuses) — the boundary between them is
  the structural content of PP2's "separable case" and may reveal a provable separation criterion;
- whether *small `|Aut|`* empirically forces *bounded recovery depth* across examples (the heart of PP3's
  "small ⟹ consumed" — a robust correlation is the lemma to attempt);
- the orbit-size-product behaviour under `NoFusion` (does the recovery path's cost track `|Aut|` as PP3
  predicts?) — a clean match validates the largeness derivation end-to-end on examples;
- primitivity/recovery correlations (the secondary, depth-graded line) — imprimitive examples that recover
  feed the separate primitivity witness.

Record any such pattern here (or in the durable docs) as it appears; the plan is expected to adjust.

**Observed (Increments 1–3, 2026-06-06):**
- **1-WL resist-vs-absorb boundary → it is the *candidate-pinning* boundary, orthogonal to abelian-ness.** The
  recovery-only harvest consumes a symmetry (abelian *or* non-abelian) iff its construct-and-check candidate is
  refinement-pinned: label-aligned copies (unique role-preserving candidate) ⇒ consumed; scrambled IR-core
  copies (matching is GI-hard, candidate unpinnable) ⇒ missed. The "absorb" failure is *recovery/localisation*
  (declassing §9 "B's core"), **not** group structure — sharpening that the depth-witness layer is the sole
  substrate-conditional input (consistent with the Lean `NoFusion`/recovery split, `Cascade.lean` Part A).
- **Every hidden non-abelian symmetry is separable.** All Tier-3 misses were decomposable (IR-core blocks under
  an outer S_k) — calculator §7 "layered products decompose" empirically confirmed; no graftable connected
  non-decomposable non-abelian fusion exists in the battery. Supports leg C's "non-consumed non-abelian ⟹
  Cameron" (no third species) and PP2's separable case.
- **Orbit-size product tracks |Aut| under consumption.** On every Clean case the harvest order = brute-force
  |Aut| exactly (Cameron, products, aligned copies, CFI) — the PP3 order-identity prediction holds end-to-end
  on examples.
