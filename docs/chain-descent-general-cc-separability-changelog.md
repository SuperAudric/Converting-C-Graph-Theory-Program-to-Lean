# Changelog — the general-CC separability build (`chain-descent-general-cc-separability.md`)

> **The detailed, append-only per-increment log for the general-CC / δ′ build.** Moved out of the main
> build doc on 2026-06-13 (it had grown to ~520 lines and buried the current state). The main doc keeps a
> condensed milestone timeline (its §8) + the authoritative current state (its STATUS block); **the full
> blow-by-blow lives here.** This is a *live* file — append a new block for every landed increment (newest
> at the bottom), same format as before: date · decls (file) · axiom-clean? · what it unlocks · next.

- **2026-06-11 — doc created.** The plan above. Nothing of the general-CC substrate built yet. Inputs (gate, sink,
  (C)-discharge, PV Thm 3.1 substrate, §S.17 homogeneous separability) all landed and listed in §2/§4.
  **NEXT: Stage 0 — the modeling decision (Option P/Q/H), with a typechecking `CoherentConfig` (or extension)
  skeleton.** Recommended starting hypothesis: Option H (minimal general-CC to `m=2`), Route β for (A).
- **2026-06-12 — onboarding review pass (docs only, no Lean).** Two independent fresh-eyes reviews of the project,
  cross-checked against the Lean source and the paper extracts; the plan survives, with these doc deltas: (1) paper
  extracts **version-controlled** at `docs/papers/` (were `/tmp`-only — reboot-fragile); (2) Stage 2.2's sub-route
  menu widened with **(c) the Chen–Ponomarenko `dimWL(X) ≤ dimWL(X_α)+1` recursion** (named in `Separability.lean
  §S.17`'s doc-comment all along but missing here) and (d) the direct relation-count form; (3) **Route δ** added to
  §6 (direct 1-regularity at `base+O(1)` via the landed B1–B5 bridge — substrate-free, math-risk-identical, probe
  first); (4) Stage 3.2 gated behind a **conditions-(i)/(ii) probe** (the falsifiers only ever tested the
  conclusion); (5) the §2 homogeneous-`Separable` quantification note sharpened to a **soundness gate** (reconcile
  before Stage 3 proves a possibly-too-weak predicate). Also flagged upstream, not in this doc: pin the intended
  `IsLarge` instantiation — the G3 citations (Babai/Sun–Wilmes) kick in at sub-exponential thresholds
  (≈`exp(n^{1/3})`), not super-poly, so "small" in the crux is wider than the `O(log n)`-base prose suggests
  (verify the exact threshold against the sources before relying). Stage 0 remains the next Lean action.
- **2026-06-12 — THE STAGE-3 GATE RAN: Thm 4.1's hypotheses HOLD on the residue's one-point extension — Route β
  VIABLE.** New probe `GraphCanonizationProject.Tests/Theorem41ConditionsProbe.cs` (2 facts, green): a general-CC
  engine (coherent closure on pairs = the point extension; fully-verified intersection numbers; transpose/products)
  + faithful checkers for condition (i) (domination, exhaustive `|Δ|=4`) and condition (ii) (m-extending couples:
  geometric λ-scan per Lemma 5.3 + exhaustive abstract fallback, so FAIL is genuine). **Control:** cycle schemes
  under `3ck(k−1)<n` PASS (the paper proves they must — checker faithful). **Residue (ℤ₄² Clebsch bullseye + ℤ₂⁴
  anchor):** X fails both conditions (dense, as §3.6 says) — but `X_α` and `X0` **pass both conditions at every
  (non-α) µ, with every witness geometric**. Full detail folded into Stage 3.2. Consequences for the plan:
  Stage 0's recommended hypothesis (Option H, Route β) is now *evidence-backed*; the Stage-3 Lean target can be
  stated witness-constructively (the λ-triangle); and the transport (B) should target the *pointed* conclusion at
  the extension (Stage 2.2(b)/(c)) since that is the form the probe-confirmed conditions feed. NEXT: Stage 0.
- **2026-06-12 — STAGE 0 DECIDED + STAGE-1 SKELETON LANDED (`ChainDescent/CoherentConfig.lean`, axiom-clean
  `[propext, Classical.choice, Quot.sound]`, no `sorry`, full build green ~24s; index regenerated).**
  **The Stage-0 decision (Option H, sharpened by the probe):** model the general CC by its **colour function**
  (`relOf : Fin n → Fin n → Fin rank` + four axioms: classes nonempty / transpose well-defined / reflexive classes
  purely diagonal / intersection numbers constant) — the minimal faithful presentation and *exactly* the object
  `Theorem41ConditionsProbe.cs` computes with, so every predicate has a machine-checked finite mirror. Fiber
  coherence is **derived, not axiomatized** (`relOf_diag_left_eq`: a class determines its source fiber — from
  `diag_eq` + `inter_card_eq` alone). The **point extension is a predicate** (`IsPointExtension`, the
  coarsest-coherent-fission universal property — made complete by the derived fiber coherence; `discreteCC`
  witnesses the family nonempty); its construction is deferred to Stage 1.2 (pair-refinement saturation — the
  `Saturation.lean`/`numCells` stabilization pattern, on pairs). **No `Ωᵐ` tower built**: Thm 4.1's hypotheses are
  first-order in intersection numbers (the "m-extension of a couple" is product-membership + uniqueness), so the
  **cited `Theorem41Statement` landed now** — the staging-fallback carry in the G3 pattern. The §2 quantification
  soundness gate is resolved by **widening**: `CoherentConfig.Separable`'s partner ranges over all
  `CoherentConfig n` (multi-fiber), not homogeneous schemes; `SeparablePointed` is Thm 4.1's actual (pointed)
  conclusion, the form the transport wants. Decls: `CoherentConfig` + `repPair`/`interNum`(`_eq`)/`transposeRel`
  (`relOf_swap_eq`, involution) / `relOf_diag_left_eq`/`_right_eq` / `AssociationScheme.toCoherentConfig` (on the
  seal's `hne`) / `AlgIso`/`InducedBy`/`idAlgIso` / `Separable`/`SeparablePointed` / `InComplexProduct`/`Dominates`/
  `DominationCondition`/`IsCoupleExtension`/`CoupleExtensionCondition`/`Theorem41Hypotheses`/`Theorem41Statement` /
  `Refines`(`refl`/`trans`)/`SingletonFiber`/`IsPointExtension`/`ExtensionSeparable` / `discreteCC`(`_refines`/
  `_singletonFiber`). **NEXT (Stage 1.2): the point-extension construction + the warmRefine↔fiber bridge**, then
  Stage 2 (the transport against `ExtensionSeparable`, sub-route (b)/(c) per the probe's pointed-geometric shape).
  Lean gotcha for the log: the micro-sign `µ` (U+00B5) is not a Lean identifier character — use Greek `μ` (U+03BC).
- **2026-06-12 — THE STAGE-2.1 DIRECTION CHECK RAN: the naive twin⟹alg-iso keying is REFUTED at arbitrary `T`;
  bases are clean; transport sub-route (c) favoured.** New fact `Probe_Stage21_DirectionCheck_CellsVsFibers`
  (`Theorem41ConditionsProbe.cs`, green; C₁₇ control asserted — cells=fibers and all reflection twins
  extension-equivalent). Adds a faithful 1-WL vertex refinement (the Lean `warmRefine (schemeAdj S)` mirror) and a
  **canonical** pair-WL (round-wise sorted renaming ⟹ cross-run-comparable stable fingerprints = WL-equivalence of
  extensions). **Findings:** (1) ℤ₄² bullseye, `T={0}`: 4 cells vs **10 fibers** — fibers strictly finer; 24/30
  same-cell pairs give WL-inequivalent one-point-further extensions (first concrete exhibit that `CellsAreOrbits`
  fails at depth 1 on the bullseye — cells ⊋ orbits, the amorphic gap live, consistent with "fails depth-1
  EdgeGenerates, recovers at depth 2"). (2) ℤ₂⁴ anchor, `T={0}`: cells=fibers, 30/30 equivalent (the gap is
  bullseye-specific). (3) ALL tested `|T|≥2` (one 2-base per relation class + a 3-base, both groups): cells=fibers,
  every same-cell twin extension-equivalent. **Consequences:** Stage 2.1 must not be stated over arbitrary `T`
  (false); the gate needs the transport at bases only (clean); the +1 pattern = the Chen–Ponomarenko
  `dimWL(X) ≤ dimWL(X_α)+1` exchange ⟹ **sub-route (c) promoted to favoured — sourcing the monograph §4.2 is now
  the Stage-2 gating action**. Also this turn: the Stage-4 keying-mismatch note added to §5 (the §S-gate decls are
  homogeneous-`Separable`-keyed; Stage 2 targets the general predicates — plan thin general-keyed gate variants).
  NEXT: Stage 1.2(a), the point-extension construction in Lean (route-independent — needed under every transport).
- **2026-06-12 — STAGE 1.2(a)+(b) LANDED: THE POINT-EXTENSION CONSTRUCTION (`CoherentConfig.lean §CC.8`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 26s; index regenerated,
  32 new rows described).** The coherent closure is computed as a saturation on `Setoid (Fin n × Fin n)`:
  `extInitSetoid` (X's classes split by `extFlag` individualization flags) → `pairStep` (split each class by all
  **representative-indexed** intersection counts `pairCount` — reference *pairs* name their classes, so the
  iteration touches no quotient, no multiset encoding) → stabilization by the `numClasses` (= `Nat.card` of the
  quotient) pigeonhole within `n²` rounds (`numClasses_growth` strict monovariant + `numClasses_le_sq` bound +
  the `le_of_numClasses_le` rigidity half ⟹ `exists_pairIter_fixed`; `pairStep_stableSetoid` via
  `Function.iterate_fixed`). The four CC axioms read off the chain: coherence IS the fixpoint property
  (`stableSetoid_pairCount`); transpose = the swap invariant carried through every round (`pairIter_swap` via the
  `pairCount_swap` reindexing); diagonal + `T`-singletons = split-only facts of the start (`pairIter_le_init` +
  `extFlag_eq_of_mem`). **The universal property is discharged constructively** (`isPointExtension_pointExtension`):
  base case reads the flags off a fission `Z`'s classes via the derived fiber coherence (`relOf_diag_left_eq` +
  the singleton hypothesis); the inductive step is the counting heart `pairCount_eq_of_zrel` (`Z.inter_card_eq`
  summed fiberwise over `Z`'s class pairs via `card_eq_sum_card_fiberwise`, with the `s`-conditions constant on
  each fiber — exactly the predicted generalization of the §CC.2 argument). Headlines:
  **`exists_isPointExtension`** (the family `ExtensionSeparable` quantifies over is inhabited for every `(X,T)` —
  the predicate is never vacuous) and **`isPointExtension_unique`** (Stage 1.2(b), mutual refinement). Lean
  gotchas for the log: `open scoped Classical` must be SECTION-wide (an `open … in` on one def leaves later
  lemma sites unable to synthesize `DecidablePred` for setoid filters); `Prod.mk.injEq` is an `=` of Props, use
  `Prod.ext_iff` where an `Iff` is needed; prefer `refine congrArg Finset.card (Finset.filter_congr ?_)` over
  `congr 1` on filter cards (instance-stable); a doc-comment must directly precede its decl (no `open … in`
  between); `simpa [Nat.card_eq_fintype_card]` can rewrite BOTH sides of a `Nat.card` inequality (use `calc`).
  **NEXT (the handoff list): Stage 2 — the transport.** Gating action: source Chen–Ponomarenko §4.2
  (`dimWL(X) ≤ dimWL(X_α)+1`) and decide sub-route (c) vs (b); any 1-WL-twin-keyed statement must be at bases
  only (the direction-check verdict). Then the citation-checkpoint assembly (mind the §5 Stage-4 keying note).
- **2026-06-12 — STAGE 2 LANDED MODULO THE CATCH-UP + THE CITATION CHECKPOINT ASSEMBLED (`CoherentConfig.lean
  §CC.9` + `CascadeAffine.lean §S-gate2`, all axiom-clean `[propext, Classical.choice, Quot.sound]`, full serial
  build green 43s; index regenerated, 11 new rows described).** **Sourcing verdict first:** the recursion (41)
  `dimWL(X) ≤ dimWL(X_α)+1` is Cai–Fürer–Immerman 1992 Thm 5.2, and `separable ⟹ dimWL ≤ 2` is
  Fuhlbrück–Köbler–Verbitsky 2020 Thm 2.1 — both *graph-dimWL* currency (they serve the paper's Thm 1.3), not the
  seal's; so sub-route (c) is an anchor, not a transport. **Sub-route (b) then won outright, citation-free:**
  apply `SeparablePointed` of the extension `E` to the **identity** algebraic isomorphism — a same-fiber pair
  `(u,u')` satisfies exactly the pointed condition, the returned `f` is an automorphism of `E` with `f u = u'`,
  it fixes `T` (singleton fibers) and descends to the scheme (`Refines`). Decls: §CC.9
  `SeparablePointed.exists_aut_of_fiber_eq` / `IsPointExtension.aut_fixes` / `Refines.aut_descends` /
  **`fiberTwin_realized_of_separablePointed`** (the core) / `extension_complete_of_separablePointed` (at a rigid
  base, pointedness on non-singleton fibers forces the extension complete — the fiber-level `b(X) ≤ b(G)`);
  §S-gate2 **`WarmTwinsAreFiberTwins`** (the catch-up, carried per-base) / `isSchemeAut_of_relOfPair_eq` /
  **`twinsRealized_of_extensionPointed`** (the transport into the sink) /
  `separatesAtBoundedBase_of_extensionPointed`(`_of_small`) (the general-keyed gates — Stage-4 keying note
  RESOLVED) / **`reachesRigidOrCameron_viaExtensionSeparability`** (the citation checkpoint: the general
  conditional seal modulo {G3 + `Theorem41Statement` + conditions-on-E at non-singleton fibers + the catch-up +
  a base}). **Two structural consequences:** (1) the homogeneous (A)-obligation DISSOLVES — bare `Separable`,
  Lemma 2.6, m-extensions, and the `Ωᵐ` tower are off the critical path entirely; (2) the non-singleton-fiber
  guard on `hhyp` matches the probe exactly (ℤ₂⁴'s X_α fails conditions only at α — a singleton fiber, exempt).
  **Honest accounting:** at a base with a complete extension the catch-up is equivalent in strength to the
  discreteness conclusion — its value is isolation: it carries no separability/group content, only the
  1-WL↔pair-WL comparison, attackable by the refinement engines (intended: B1–B5 forced-triangle propagation
  from condition (i)'s `c=1` dominators). NEXT: the catch-up discharge (STATUS item 5, probe-gate first), then
  Stage 3 (the genuine open math).
- **2026-06-12 — DOC HYGIENE LANDED + THE CATCH-UP PROBE-GATE RAN: GATE GREEN, ENGINE CONFIRMED AT SCHEME LEVEL,
  `b(X) = b(G)` ON BOTH INSTANCES (`Probe_CatchUpGate_BasesAndDominators`, `Theorem41ConditionsProbe.cs`, all 4
  facts green; no Lean touched, build re-verified green 29s + capstones re-checked axiom-clean).**
  *Hygiene:* 00-START-HERE §4 module table gained `Separability.lean` + `CoherentConfig.lean` rows (+ the
  CascadeAffine §S-gate2 mention); the seal-handoff got a 2026-06-12 banner routing to THIS doc (the 06-11
  module-adjoin pointer was itself stale); §5 gained the **family-restricted-Stage-3-suffices** scope note
  (Stage 3.4: `Theorem41Statement` is consumed only at `hcite n E u` — a family-level proof feeds the checkpoint
  through a thin wrapper, the global carry retires unused) and the **assembly-shape** note (Stage 4.3: the
  `_of_small` gate quantifies `hsep`/`hcatch` over ALL `T` because its greedy base is unchosen — assemble through
  the per-`T` gate at probe-validated bases instead).
  *The probe-gate* (control C₁₇ asserted: |Aut|=34, all 136 pairs are bases, catch-up + discreteness everywhere,
  scheme-closure 17/17): **(a) THE GATE IS GREEN** — exhaustive sweeps against exactly-computed `Aut(X)`
  (backtracking; ℤ₄²: |Aut|=32 = translations×{±1}; ℤ₂⁴: |Aut|=160): catch-up holds at **every** swept `|T| ≥ 2`
  (ℤ₄²: all 120 pairs; ℤ₂⁴: all 120 pairs + all 560 triples), in particular at every minimal base (96/96 resp.
  480/480). ℤ₄²: b(G)=2, the 24 non-base pairs are exactly the involution-difference pairs (`x ↦ −x + 2u`
  stabilizer), and base ⟺ 1-WL-discrete ⟺ extension-complete (32/40 per class, all three); ℤ₂⁴: no size-2 base,
  b(G)=3, all 480 bases discrete + complete. So **`b(X) = b(G)`** (2 resp. 3) and at minimal bases the catch-up
  is *exactly* the discreteness conclusion — the honest-accounting equivalence exhibited, not just argued.
  **(b) THE ENGINE EXISTS, ONE LEVEL CHEAPER THAN PLANNED** — the `c=1` two-endpoint dominator closure (seed
  `Determined = T`; pin δ when some determined pair (µ,λ) has `#{w : r(µ,w)=r(µ,δ) ∧ r(w,λ)=r(δ,λ)} = 1` — the
  landed B3 `determined_of_saAdj` pinning shape) **discretizes from every tested minimal base on BOTH instances
  using only X's own rank-4 classes** (scheme level; E-level closure agrees), with **0 one-WL-soundness
  violations at bases**; at non-bases it stalls (1/16 from `{0}`) and is 1-WL-**un**sound (ℤ₄² `T={0}`: E-closure
  pins 4, of which 3 sit in non-singleton warm cells) — so B3-style lemmas must stay base-keyed, consistent with
  the direction check. **Consequences:** (1) state `WarmTwinsAreFiberTwins` at `IsBase T`; no base+O(1)
  escalation needed on the instances; (2) **Route δ's parked feasibility probe effectively ran POSITIVE** (§6 δ
  updated) — a citation-free discharge shape on the landed homogeneous substrate is live: formalize the
  two-endpoint dominator *closure* (a `Saturation`-pattern wrapper over B3) ⟹ `Discrete` ⟹
  `SeparatesAtBoundedBase`, carrying "closure exhausts Ω from the base" as the named hypothesis; (3) the
  family-level "closure completes" proof is the same open crux as Stage 3's conditions — two interchangeable
  consumption shapes, both probe-backed. NEXT: the Lean increment for item 5 — either (α) the per-base catch-up
  against the checkpoint's keying, or (δ′) the dominator-closure engine (recommended: it is citation-free,
  lands on `Separability.lean`/`CascadeAffine.lean` machinery, and its hypothesis is what Stage 3 proves anyway).
- **2026-06-12 — THE δ′ DOMINATOR-CLOSURE ENGINE LANDED (item 5 discharged as plumbing): a citation-free Lean
  path to the seal (`CascadeAffine.lean §S-bridge-δ` + `§S-gate2`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 49s; index regenerated, 6 new rows described).** Following the
  probe-gate's positive verdict, formalized the recommended (δ′) shape. Decls, in dependency order: **B3′
  `determined_of_forcedTriangle`** — the smax-free generalisation of `determined_of_saAdj`, taking the
  intersection-number-`=1` fact directly (the `saAdj` proof always discarded its two `smaxAdj` conjuncts via
  `obtain ⟨_, _, hone⟩`, so the body transfers verbatim); the inductive closure **`DominatorReachable S T`**
  (`base : t ∈ T`; `step : reachable α → reachable β → c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1 → reachable γ`);
  **`determinedAt_of_dominatorReachable`** (induction: base = B2 `determined_of_mem_individualized`, step = B3′);
  **`discrete_of_dominatorClosure`** (`(∀ v, DominatorReachable S T v) ⟹ Discrete (warmRefine … T)`, by reading
  `DeterminedAt` at the target of each pair); **`separatesAtBoundedBase_of_dominatorClosure`** (`+ |T| ≤ bound ⟹
  SeparatesAtBoundedBase` — note **no `IsBase` hypothesis**: discreteness is produced outright, lighter than the
  separability route); and the capstone **`reachesRigidOrCameron_viaDominatorClosure`** (same
  `reachesRigidOrCameron_viaPersistentTwinBlock` plumbing as the extension checkpoint, fed by the dominator
  separation). **Net:** the seal now has *two* conditional checkpoints — the extension-separability one
  (`…viaExtensionSeparability`, carries {G3 + `Theorem41Statement` + conditions-on-E + catch-up + base}) and the
  **citation-free δ′ one** (`…viaDominatorClosure`, carries {G3 + `hImprim` + the single `hclo : ∀ v,
  DominatorReachable S T v`}). The catch-up `WarmTwinsAreFiberTwins` is **off every critical path** — δ′ bypasses
  it. The lone remaining open content is **Stage 3** in its lightest form: prove `hclo` for the residue family
  (the `c=1` forced-triangle closure of a bounded base exhausts Ω — probe-confirmed at every minimal base, the
  genuine family-level mathematics). Lean note for the log: B3′ is a *strict* generalisation, so
  `determined_of_saAdj` could be refactored to call it (deferred — non-load-bearing, and the `saAdj_symm`
  extraction is one line). NEXT: Stage 3 (δ′ target recommended), the genuine open math.
- **2026-06-12 — STAGE 3 INCREMENT 1: THE AFFINE FORCED-TRIANGLE CRITERION (`CascadeAffine.lean §S-stage3`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 36s; index regenerated,
  2 rows described).** Began the δ′ Stage-3 frontier (`hclo : ∀ v, DominatorReachable S T v` for the residue
  family). The first brick is the **coordinate translation**: `affineScheme_interNum_eq_one_of_unique` proves, for
  `affineScheme G₀`, that the dominator premise `intersectionNumber (relOfPair α γ)(relOfPair γ β)(relOfPair α β)
  = 1` holds **exactly when `γ` is the unique point `u` with `u−α` in `G₀·(γ−α)` and `β−u` in `G₀·(β−γ)`** — i.e.
  the `c=1` forced-triangle pins `γ` iff the orbit-of-difference triangle is rigid. Proof is clean (no `card_bij`):
  the forced-triangle filter `{u : r(α,u)=r(α,γ) ∧ r(u,β)=r(γ,β)}` is exhibited as the singleton `{γ}` via
  `intersectionNumber_well_defined` + `affineScheme_rel_iff` + `orbMk_affine_eq_iff` (each membership clause
  unfolds to a `G₀`-orbit-of-difference equation, and `huniq` collapses it). `dominatorReachable_affine_step` is
  the matching builder: two reachable points + the orbit-uniqueness ⟹ `DominatorReachable … γ`, via
  `DominatorReachable.step`. **Net:** the δ′ family argument is now stated purely in `G₀`-orbit-of-difference
  terms — the same idiom as `affineScheme_relOfPair_translation` / `discrete_affineScheme_of_jointSeparates`, so it
  composes with the landed affine machinery. Lean note: `rintro rfl` on `u = γ` (γ a parameter) substitutes γ
  *away*; use `intro hu; rw [hu]` to keep γ in scope. **NEXT (Stage 3 increment 2, the genuine open math): the
  family closure** — pick a bounded base `T` (per the probe, the minimal group base) and prove every `v` is
  `DominatorReachable` by iterated `dominatorReachable_affine_step`, for the residue family (`G0pow β`). This is the
  orbit-combinatorics core: showing the rigid-triangle reachability fills `V` from `T`.
- **2026-06-12 — STAGE 3 INCREMENT 2: THE DOMINATOR-CLOSURE EQUIVARIANCE (`CascadeAffine.lean §S-bridge-δ`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 63s; index regenerated,
  2 rows described).** Structural infrastructure for the δ′ family closure. `dominatorReachable_map`: the dominator
  closure is **scheme-automorphism-equivariant** — for `π` a scheme automorphism mapping base `T` into `T'`,
  `DominatorReachable S T v → DominatorReachable S T' (π v)` (induction over `DominatorReachable`; base = `hT`, step
  invariant because `IsSchemeAut.relOfPair_eq` preserves the forced-triangle intersection-number premise — the same
  one-line `relOfPair`-preservation the seal uses throughout). `dominatorReachable_univ_image`: the payoff —
  **complete closure transports across automorphic base images** (`∀ v, DominatorReachable S T v ⟹ ∀ v,
  DominatorReachable S (T.image π) v`, via `π.symm` + `apply_symm_apply`). **Why it matters:** the residue is
  vertex-transitive (schurian), so `Aut(S)` acts transitively on points and richly on bases; the open single-base
  closure now needs proving at only ONE representative base per `Aut(S)`-orbit, not all bases — exactly the
  reduction the probe's "every minimal base closes" suggested was available. General over any `AssociationScheme`
  (not affine-specific), so it composes with the whole scheme substrate. NEXT (Stage 3 increment 3, the genuine
  open math): the single-base closure for `affineScheme (G0pow β)` — pick `T₀` and prove `∀ v, DominatorReachable`
  by the orbit-of-difference combinatorics, the `s(C)` core.
- **2026-06-12 — STAGE 3 INCREMENT 3: THE GENERAL + SCHURIAN FORCED-TRIANGLE CRITERION (`CascadeAffine.lean
  §S-bridge-δ`, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 94s;
  index regenerated, 3 rows described).** Lifted the affine criterion to its natural generality and surfaced the
  group-theoretic form of the open content. (1) **`interNum_eq_one_of_forcedUnique`** — for ANY `AssociationScheme`,
  `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` ⟺ `γ` is the unique `u` sharing `γ`'s `relOfPair`-profile to `α` and `β`
  (forced-triangle filter `= {γ}`; same singleton proof as the affine lemma but with no orbit machinery — pure
  `intersectionNumber_well_defined` + `rel_iff_relOfPair`). (2) **`dominatorReachable_step_of_unique`** — its
  `DominatorReachable` step builder; subsumes `dominatorReachable_affine_step` (the orbit-difference `huniq` is this
  `relOfPair` one unfolded) AND covers non-affine residues (e.g. the ℤ₄² amorphic NLS = `orbitalScheme`, not
  `affineScheme`) the affine lemma could not reach. (3) **`dominatorReachable_step_of_stab`** — the schurian reading:
  `relOfPair`-profile equality is a point-stabiliser-orbit relation (schurian axiom `S.schurian`), so the criterion
  is **`Stab(α)·γ ∩ Stab(β)·γ = {γ}`** — `γ` is pinned exactly when the two point-stabiliser orbits of `γ` meet only
  at `γ`. This is the geometric handle the single-base closure wants: a base `T₀` has `⋂_{t∈T₀} Stab(t) = 1`, so its
  stabiliser orbits must intersect down toward points, and the closure question becomes "do the pairwise
  stabiliser-orbit intersections propagate reachability from `T₀` to all of `V`". **Net:** the open content is now
  framed group-theoretically (stabiliser-orbit intersections), at the right generality (any schurian residue, not
  just affine). NEXT (Stage 3 increment 4, the genuine open math): the single-base closure — exhibit `T₀` and prove
  the stabiliser-orbit-intersection propagation for the residue family. Note: `affineScheme_interNum_eq_one_of_unique`
  is now a special case of (1), left in place (orbit-difference convenience form; non-load-bearing to refactor).
- **2026-06-13 — STAGE 3 INCREMENT 4a: THE ITERATION ENGINE — single-base closure from a pinning rank
  (`CascadeAffine.lean §S-bridge-δ`, `dominatorReachable_of_rank`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 198s; index regenerated, 1 row described).** The δ′ toolkit had
  step builders (`dominatorReachable_step_of_unique`/`_of_stab`/`_affine_step`) and the equivariance reduction, but
  **nothing that iterates the step to exhaust Ω** — the actual single-base closure had no engine. `dominatorReachable_of_rank`
  is that brick: given a rank function `rank : Fin n → ℕ` with (i) every rank-`0` point in `T` and (ii) every
  positive-rank `γ` forced-triangle-pinned (the `relOfPair`-profile uniqueness of `interNum_eq_one_of_forcedUnique`)
  by two **strictly-lower-rank** points, strong induction on the rank yields `∀ v, DominatorReachable S T v`. Proof:
  auxiliary `∀ k v, rank v = k → reachable` by `Nat.strong_induction_on` on `k`; rank-0 ⟹ `base`, positive ⟹ obtain
  the two lower-rank pinners, apply the IH to each (their rank `< k` via `hv ▸ hα`), feed `dominatorReachable_step_of_unique`.
  **What it buys:** the family-level open content is now reduced from the global, hard-to-attack "the `c=1` closure
  exhausts Ω" to the **concrete, checkable** "exhibit a pinning rank" — exactly the *clean sufficient condition* the
  δ′ Stage-3 endpoint targets (the rank = number of pinning rounds the stabiliser-orbit intersections take to reach
  each point; a base has `⋂ Stab(t) = 1`). **Net (the open piece is now purely the rank witness):** to close the
  residue family it remains to *define the rank and verify the pinning at each level* — the genuine `s(C)` arithmetic
  (the cyclic `(r+1−r·h) ∈ H → h = 1` core, char-2 midpoints excluded), now cleanly isolated behind a general,
  provable, axiom-clean interface. NEXT (increment 4b, the genuine open math): the affine cyclic arithmetic reduction
  (`affineScheme` pinning ⟺ `∀ h ∈ H, (r+1−r·h) ∈ H → h = 1`) to translate the rank's pinning obligation into pure
  `F_q^×`-coset arithmetic, then exhibit a propagating rank/base for the residue family.
- **2026-06-13 — STAGE 3 INCREMENT 4b: THE AFFINE CYCLIC ARITHMETIC REDUCTION (`CascadeAffine.lean §S-stage3-δ`,
  `fieldOf` / `G0pow_orbit_iff` / `dominatorReachable_G0pow_step`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 121s first try; index regenerated, 3 rows described).**
  Translates the cyclotomic family's forced-triangle pinning from `G₀`-orbit-of-difference language into pure
  `F_q`-power arithmetic. (1) **`fieldOf hd x := (efield hd).symm (affineE.symm x)`** — the point→`F_q` coordinate.
  (2) **`G0pow_orbit_iff`** — the core: a `G0pow g = ⟨mul g⟩`-orbit relation between coordinate vectors is exactly
  multiplication by a power of `g` through the field iso (`∃ g₀ ∈ G0pow g, g₀ v = w ↔ ∃ k:ℤ, ↑(g^k)·efield.symm v =
  efield.symm w`); proof = `Subgroup.mem_zpowers_iff` + `sigmaPow_zpow_apply` (`σ_g^k` = `·g^k` through `efield`) +
  `efield` injectivity. (3) **`dominatorReachable_G0pow_step`** — the forced-triangle step builder with `huniq` in
  `F_q` powers (`g^k·(fieldOf u−fieldOf α)=fieldOf γ−fieldOf α`, the symmetric one for `β`), obtained from
  `dominatorReachable_affine_step` by feeding each orbit hypothesis through `G0pow_orbit_iff.mp` + `map_sub`
  (`efield.symm` is linear over the difference). **Net:** the δ′ cyclotomic single-base closure now reasons in pure
  `F_q` arithmetic — define a rank, and for each positive-rank `γ` discharge `huniq` as an `F_q`-power uniqueness — with
  no orbital / intersection-number bookkeeping. **NEXT = increment 4c (the field-division packaging):** the ratio form
  `∀ h ∈ ⟨g⟩, (r+1−r·h) ∈ ⟨g⟩ → h = 1` with `r = (fieldOf γ − fieldOf α)/(fieldOf β − fieldOf γ)` (needs `b ≠ c` and
  unit/nonzero handling) — it divides out the field differences and makes the char-2-midpoint obstruction (`r=1` never
  pins) explicit; then the genuine open piece, the pinning-rank witness for the residue family.
- **2026-06-13 — STAGE 3 INCREMENT 4c: THE RATIO-FORM STEP BUILDER (`CascadeAffine.lean §S-stage3-δ`,
  `dominatorReachable_G0pow_ratio_step`, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full
  serial build green 115s first try; index regenerated, 1 row described).** The field-division packaging of 4b: the
  cyclotomic forced-triangle step with the two `F_q`-difference equations *divided through*. For distinct field
  coordinates (`fieldOf γ ≠ fieldOf α`, `fieldOf β ≠ fieldOf γ`), `γ` is pinned by `α, β` once the only `h ∈ F_q`
  that is **both** a power of `g` and has `1 + r·(1−h)` a power of `g` — cross-ratio `r = (fieldOf γ − fieldOf α)/
  (fieldOf β − fieldOf γ)` — is `h = 1`. Proof: from `dominatorReachable_G0pow_step`, set `h = (x−a)/(c−a)` for the
  variable `x = fieldOf u` (cond 1 ⟺ `h ∈ ⟨g⟩`, via `eq_div_iff` + `zpow_neg`), compute `(b−x)/(b−c) = 1 + r(1−h)`
  (`field_simp; ring`) so cond 2 ⟺ `1 + r(1−h) ∈ ⟨g⟩`, then `hpin` gives `h = 1 ⟺ x = c ⟺ u = γ` (`fieldOf`
  injective). **This is the `(r+1 − r·h) ∈ ⟨g⟩ → h = 1` reduction of §5 — the closest Lean form to the open
  cyclotomic `s(C)` arithmetic, and it makes the char-2-midpoint obstruction explicit in the Lean statement**
  (`r = 1` ⟹ `1 + (1−h) = 2 − h = h` in char 2 ⟹ every `h` admitted ⟹ nothing pins; char-2 residues need
  non-midpoint triangles). **Net: the δ′ cyclotomic toolkit is complete** — iteration engine (4a) + `F_q`-power
  step (4b) + ratio-arithmetic step (4c). The lone open piece is the **pinning-rank witness**: exhibit a base `T₀`
  and a rank function whose per-level pinning is discharged by `dominatorReachable_G0pow_ratio_step` (the genuine
  open `s(C)` mathematics; the affine slice is cited-closed, so the new coverage target is the non-affine residue,
  where the general/schurian step builders apply instead). NEXT = the rank witness (open math) — or, lower-priority,
  the post-Stage-3 full `hImprim` discharge.
- **2026-06-13 — STAGE 3, THE MATH: FIRST END-TO-END CLOSURE OF A REAL FAMILY (`CascadeAffine.lean §S-bridge-δ` +
  `§S-stage3-δ`; `dominatorReachable_of_basePinsAll`, `fieldOf_injective`, `exists_zpow_neg_one_iff` (private),
  `dominatorReachable_G0pow_neg`, `reachesRigidOrCameron_viaG0powNeg`; all axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green ~94–128s, all first try; index regenerated, rows described).**
  The first **actual discharge** of the δ′ seal's open `hclo` for a real `affineScheme` family — not more
  infrastructure, a closure. (1) **`dominatorReachable_of_basePinsAll`** — the clean checkable one-round criterion
  (every non-base point pinned by two base points ⟹ closure; the `rank∈{0,1}` instance of 4a). (2) The genuine
  result **`dominatorReachable_G0pow_neg`**: for `g = -1` (so `⟨g⟩ = {1,-1}`) over **odd characteristic** (`p ≠ 2`),
  *every* point is dominator-reachable from *any* 2-element base `{α,β}`, `α≠β`. Math: the cross-ratio
  `r = (c−a)/(b−c)` of pairwise-distinct points satisfies `r ∉ {0,-1}`, so for the only nontrivial `h = -1 ∈ ⟨g⟩`
  the value `1 + 2r ∉ {1,-1} = ⟨g⟩` (uses `2 ≠ 0`), the pinning antecedent fails, only `h = 1` survives —
  discharged through `dominatorReachable_G0pow_ratio_step`; `fieldOf_injective` carries distinctness, `2 ≠ 0` via
  `CharP.cast_eq_zero_iff`, the field algebra via `linear_combination`. **Char ≠ 2 is essential — exactly the
  documented char-2-midpoint obstruction** (`p = 2` ⟹ `⟨g⟩ = {1}`, the argument collapses). (3)
  **`reachesRigidOrCameron_viaG0powNeg`** feeds (2) into `reachesRigidOrCameron_viaDominatorClosure`: the seal on the
  whole `g = -1` family (rank ≥ 3, i.e. `q ≥ 5`) **with the open `hclo` GONE — proved, not carried**; only the
  standard {G3 + `hne` + `hrank` + `hImprim`} remain. **Significance:** the δ′ route is *not vacuous* — it discharges
  the seal's open mathematical content outright on a genuine family, and removes the cyclotomic citation for the
  `H={±1}` sub-family. **Honest scope:** this is the odd-char `|H|=2` slice (one-round; no multi-round arithmetic);
  the *general* cyclotomic family (larger `H`, and char-2 — the Clebsch residue) and the **non-affine** residue (the
  genuine new-coverage target, via the general/schurian builders) remain the open `s(C)` core. NEXT = larger `H` /
  a multi-round rank witness, or the non-affine residue.
- **2026-06-13 — STAGE 3, MULTI-ROUND: THE SUBFIELD FAMILY `H=K^×` CLOSES IN TWO ROUNDS (`CascadeAffine.lean
  §S-stage3-δ`; `ratio_not_mem_num_out`, `ratio_not_mem_denom_out` (private), `dominatorReachable_G0pow_subfield_step`,
  `dominatorReachable_G0pow_subfield`; all axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full
  serial build green 108s; index regenerated, rows described).** The first genuinely **multi-round** (`|H|>2`)
  closure. First the necessity check: one-round-from-a-2-base works **iff `|H|≤2`** (as `r` ranges over `F_q∖{0,-1}`,
  `1+r(1-h)` ranges over `F_q∖{1,h}`, so "no triangle blocked" forces `H⊆{1,h}`) — so `|H|>2` genuinely needs
  iteration. The tractable larger-`H` family is **`H=K^×` for a subfield `K⊊F_q`**, with a **size-free** pinning
  rule: `r=(c−a)/(b−c)∉K ⟹ γ pinned` (`dominatorReachable_G0pow_subfield_step`; for `h∈K^×∖{1}`, `1−h∈K^×` ⟹
  `r(1−h)∉K` ⟹ `1+r(1−h)∉K⊇H`). The 2-round closure (`dominatorReachable_G0pow_subfield`) from a base of two
  `K`-points: round 1 pins all non-`K` points by `α,β` (`ratio_not_mem_num_out`), round 2 pins all `K` points by `α`
  and a reached non-`K` point (`ratio_not_mem_denom_out`). Carries `⟨g⟩=K^×` (`hHK`) + a non-`K` witness as field
  facts; instantiation (`K=F_p`, `g=fqGen^{(p^d−1)/(p−1)}`) is field-theory plumbing, no new open math.
  **IMPORTANT HONEST CAVEAT:** the `K^×` family is **IMPRIMITIVE** (`F_p^×` acts as scalars, preserving every
  `F_p`-subspace ⟹ reducible `G₀` ⟹ not primitive) — so it is the **hImprim/G2-A** case, *not* the primitive G2-B
  residue. This is a real multi-round closure that **validates the iteration engine for `|H|>2` and gives a reusable
  size-free subfield pinning lemma**, but the **primitive** larger-`H` case (irreducible `G₀`, field-generating `g` —
  the Clebsch-type / char-2 residue) has no subfield shortcut and remains the genuine open `s(C)` core. NEXT = the
  primitive irreducible multi-round case (no `K` structure — the hard Frobenius/cyclotomic arithmetic), or the
  non-affine residue.
- **2026-06-13 — PROBE: THE NON-AFFINE RESIDUE'S CLOSURE CONSTRUCTION EXTRACTED — it is UNIFORM, MULTI-ROUND,
  and AMORPHIC (`Theorem41ConditionsProbe.Probe_ExtractPinningRank`, green; no production/Lean touched).** Following
  the §1A analysis (the load-bearing claim is the separability content itself, not elementary smallness ⟹ a blind
  general Lean push stalls; extract the concrete construction first), added `DominatorRank` (rank-extracting closure:
  BFS round + pinning pair per point) and the extraction probe. **Findings on the primitive ℤ₄² amorphic-NLS bullseye
  (the genuine G2-B target, n=16):** (1) **96/120 pairs are completing 2-bases**; sample base `{0,1}` closes in
  **depth 3 rounds**, layers `[2,2,6,6]`. (2) **Genuinely multi-round** — intermediate (non-base) pinners are
  required (not one-round-in-disguise). (3) **THE CONSTRUCTION IS UNIFORM AND STRUCTURAL:** every pinning triangle's
  edge-triple `(rel(µ,d),rel(d,λ),rel(µ,λ))` is a **permutation of {1,2,3}** — a **rainbow triangle** (three distinct
  non-diagonal colours) — and all six orderings occur ≈evenly (248/241/225/222/206/202 over all bases); **no triangle
  with a repeated or diagonal colour ever pins.** So the pinning rule is exactly *"rainbow triangle ⟹ rigid (c=1)"* —
  the **amorphic S₃ structure made operational**, which is precisely the mechanism §1A's carve-out predicted would
  drive recovery on the non-Cameron residue. **The char-2 anchor ℤ₂⁴:** **0/120** completing 2-bases (needs a
  ≥3-base) — the midpoint obstruction at the base-size level. **Strategic read:** on-track (clean uniform mechanism,
  no falsifier; the bullseye recovers exactly as predicted). The abstract lemma the construction points to is
  *"rainbow-rigidity (rank-4, rainbow c=1) + a 2-base ⟹ closure in O(1) rounds."* NEXT (the abstraction step):
  formalize the rainbow-rigidity closure — either abstractly (carry rainbow-c=1 + the round-3 geometry as
  hypotheses) or concretely (hard-code the 16×16 colour matrix as a Lean `AssociationScheme`, `decide` the axioms +
  the 16 rainbow-pinning derivations — feasible only with plain `decide`, since `native_decide` violates the axiom
  bar). **CAVEAT:** rainbow-c=1 is special to the Clebsch parameters `(16,5,0,2)`, not automatic for all amorphic
  rank-4, so the abstraction is parameter-scoped, not "all amorphic."
- **2026-06-13 — THE CONCRETE ROUTE LANDED: THE FIRST NON-AFFINE δ′ CLOSURE IN LEAN (`ChainDescent/ClebschConcrete.lean`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`; in the serial build, the
  module compiles in ~56s; index regenerated, 11 rows).** Took the concrete route from the extraction probe. **Spike
  first:** confirmed plain `decide` can verify the scheme-coherence axiom on the 16×16 matrix (feasible but heavy
  ~66s user, swap-prone under full Mathlib). **Then built it, OOM-managed:** `clebschZ4Scheme : AssociationScheme 16`
  from the hard-coded colour matrix (`clebschZ4ColF`), all four axioms by `decide` — coherence **split per-colour**
  (`fin_cases k`) to quarter the kernel working-set (one giant `decide` OOM-killed the machine; the split + VSCode
  closed fixed it). The closure `clebschZ4_closure : ∀ v, DominatorReachable clebschZ4Scheme {0,1} v` via a local
  **`interNum`-keyed** rank engine `domReach_of_rank_pin` (the Nat-equality `c=1` premise is `decide`-friendly; the
  `relOfPair`-uniqueness form's nested implications have no synthesizable `Decidable`), fed the probe rank
  (`clebschZ4Rank`) + explicit rainbow pinners (`clebschZ4Pin`), with the `relOfPair`→matrix bridge
  (`clebschZ4_relOfPair`) so `decide` checks each rainbow triangle is rigid. Payoff `clebschZ4_discrete`: the ℤ₄²
  Clebsch scheme is **`Discrete` after individualizing `{0,1}`** = `b(X) ≤ 2`, a non-affine
  `SeparatesAtBoundedBase`-grade recovery, fully in Lean. **Significance:** the seal's open `hclo` content is now
  *discharged concretely for a real non-affine primitive G2-B residue* — an existence witness that the δ′ route
  reaches the genuine bullseye, not just the affine/citable corner. **Scope (honest):** one scheme, parameter-scoped
  to Clebsch `(16,5,0,2)`; stays at `AssociationScheme` level (`Discrete`), does **not** feed the seal capstone
  (that needs `SchurianScheme` = the automorphism data, deferred); and it is `decide`-checked, not a general family
  proof. **Lean lessons:** `decide` has no `Decidable (p→q→r)` for nested implications (single `p→q` is fine — that
  is why the `interNum`-form engine was needed); `∃!` has no synthesizable `Decidable` (give the term); split big
  `decide`s with `fin_cases` to bound kernel memory; `native_decide` is BANNED (adds `ofReduceBool`). NEXT = either
  abstract the rainbow-rigidity closure (parameter-scoped family lemma), wire a `SchurianScheme` instance to feed the
  seal, or return to the general/primitive open core.
- **2026-06-13 — OPTION-1 DERIVATION (§1B) + THE δ′ RAINBOW-RIGID FAMILY LEMMA LANDED (`CascadeAffine.lean §S-bridge-δ`
  + `ClebschConcrete.lean`; `dominatorReachable_of_rank_interNum`, `RainbowRigid`, `interNum_eq_one_of_rainbow`,
  `dominatorReachable_of_rainbowRank`, `clebschZ4_rainbowRigid`; all axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `native_decide`, full serial build green 19s; index regenerated, 5 rows described).** Two halves.
  **(A) The written derivation (§1B, this doc):** worked out "does Cameron's dichotomy deliver Thm 4.1 domination?"
  against Ponomarenko §§4–5. **Verdict: NO as a free implication** — domination is the *sparsity* bound
  `n > 3c(k−1)k` (Lemma 5.2, in `c` = indistinguishing number and `k` = max valency); Cameron's dichotomy controls
  only *order* (`|Aut|`). The reduction is clean though: the `k`-half is **free** (`maxValency(X_T) ≤ |Aut_T|` by
  orbit–stabiliser, shrinks geometrically along the landed greedy base), leaving **one** open quantity — the
  **post-base indistinguishing number `c(X_T)`** — which is *identical* to the δ′ forced-triangle abundance /
  rainbow-rigidity. So the general route is not a shortcut around δ′; it IS δ′, and supplies the parameter to bound.
  Plus a flagged calibration caveat (poly vs sub-exponential "small"). **(B) The Lean increment (δ′):** turned the
  §1B `c(X_T)` content into a **family lemma**. `dominatorReachable_of_rank_interNum` = the general public
  `interNum`-keyed rank engine (the form `ClebschConcrete`'s private `domReach_of_rank_pin` had locally — nested
  `huniq` has no `Decidable`, the Nat-equality does). `RainbowRigid` = the structural pinning hypothesis the probe
  extracted (rainbow triangle ⟹ `c=1`), the operational form of "small `c(X_T)`". `interNum_eq_one_of_rainbow`
  (rigidity `≤1` + `γ`-realises `≥1` ⟹ `=1`) feeds `dominatorReachable_of_rainbowRank`: **a `RainbowRigid` scheme
  with a rainbow rank closes — lifting `clebschZ4_closure` from the single hard-coded scheme to the whole
  rainbow-rigid family**, with per-point pinning now a purely combinatorial colour condition. `clebschZ4_rainbowRigid`
  (`decide`) confirms the genuine bullseye satisfies the hypothesis — the family lemma is non-vacuous on the real
  non-affine residue. **Net:** the seal's open `hclo` is now reduced, for the rainbow-rigid family, to {(a) the scheme
  is `RainbowRigid`, (b) it has a rainbow rank from a bounded base} — both clean checkable conditions, the §1B
  `c(X_T)`-boundedness made operational. **Scope caveat (unchanged):** rainbow-rigidity is special to `(16,5,0,2)`-type
  amorphic rank-4, so the family is parameter-scoped, not "all amorphic"; and the lemma is `AssociationScheme`-level
  (does not yet feed the seal capstone — still needs `SchurianScheme`, deferred). **NEXT:** (1) exhibit `RainbowRigid` +
  a rainbow rank for a *parametric* amorphic-NLS family (not just the order-16 instance) to make the family lemma bite
  beyond one scheme; (2) the post-base `c(X_T)` bound for non-rainbow primitives (the genuinely general open core);
  (3) the deferred `SchurianScheme`/seal-capstone wiring and the hImprim `G₀Irreducible → IsPrimitive` bridge.
- **2026-06-13 — PROBE: IS RAINBOW-RIGIDITY PARAMETRIC? — NO; rainbow-rigidity AND scheme-level δ′ are both order-16
  artifacts (`Theorem41ConditionsProbe.Probe_RainbowRigidFamily` + generalized `AmorphicNLS3Scheme`, green; no
  production/Lean touched).** Following discipline (probe before formalizing a *parametric* family), generalized
  `ClebschScheme` to `AmorphicNLS3Scheme(g)` (any group, equal valency `(V−1)/3`, auto-detected SRG params, coherence
  by `BuildCC`) and tested the rainbow-rigid family lemma's hypotheses on the first prime-power square beyond 16
  alongside the two order-16 instances. **Findings (n, rainbow-rigid via max common-nbr over distinct-colour triples,
  full-WL `b(X)`, scheme-level two-endpoint δ′ closure):** `Z4²` (16, **YES** cn=1, b=2, δ′ closes @2 — the bullseye);
  `Z2⁴` (16, **YES** cn=1, b=3, δ′ closes @3 — char-2 base-level obstruction visible); **`Z5²` (25, NO cn=4, b=2, δ′
  does NOT close even from an 8-base).** **Three conclusions:** (1) **rainbow-rigidity is NOT parametric** — the
  `(16,5,0,2)` `c=1`-for-distinct-colours is a small-`q` coincidence; at `q=5` the distinct-colour intersection
  number is already `4`. So `dominatorReachable_of_rainbowRank` genuinely covers only the order-16 parameter point
  (two schemes), not an infinite NLS family — option (i) is **refuted**, do not formalize a parametric rainbow family.
  (2) **The scheme-level δ′ `DominatorReachable` closure is ALSO order-16-only** — it relies on `c=1` forced triangles
  in `X`'s *own* rank-4 colours, which vanish by `n=25`. (3) **But `Z5²` still recovers at `b(X)=2` via full 1-WL** —
  the residue is tame (§1A on track), the recovery just lives in the **extension `X_T`'s finer colours**, NOT in the
  bare scheme. **Redirect (the genuine parametric δ′ path):** lift the `DominatorReachable` forced-triangle closure
  from `AssociationScheme` (`X`'s colours) to the **general-CC extension `X_T`** (`CoherentConfig.lean`, LANDED) —
  where the `c=1` triangles reappear (that is *why* `b(X)=2`). This **unifies the citation-free δ′ route with the
  extension-separability route** for `n ≥ 25` (the δ′-at-scheme-level advantage was an order-16 artifact), and is the
  operational `c(X_T)` content of §1B. NEXT: state `DominatorReachable` / the forced-triangle closure on
  `CoherentConfig` (the point extension), and prove a bounded-base extension closure for the amorphic-NLS family —
  the parametric δ′ target, now correctly aimed at the extension.
- **2026-06-13 — THE δ′ ENGINE LIFTED TO THE GENERAL CC (`CoherentConfig.lean §CC.10`, axiom-clean `[propext,
  Classical.choice, Quot.sound]`, full serial build green 94s; index regenerated, 8 rows described).** Acting on the
  rainbow-probe redirect, ported the forced-triangle dominator closure from the homogeneous `AssociationScheme`
  (`X`'s own rank-4 colours, which vanish at n≥25) to a general `CoherentConfig` — so it runs on the point extension
  `X_T` (`pointExtension X T`), where the `c=1` triangles reappear (that is *why* `b(X)=2` for `Z5²`). Decls: the
  forced-triangle criterion **both directions** (`interNum_eq_one_of_forcedUnique` / `forcedUnique_of_interNum_eq_one`,
  pure counting via `inter_card_eq`); the inductive closure **`DominatorReachable`** (`base`: `t∈T`; `step`: `c=1`
  triangle against two reachable points); the step builder + the **rank engine `dominatorReachable_of_rank`** (mirrors
  of the scheme versions); and the **discreteness payoff** — `singletonFiber_of_dominatorReachable` /
  **`allSingletonFiber_of_dominatorClosure`**: closure exhausts Ω + `T`-points singleton fibers + **`Sharp`** ⟹ every
  point a singleton fiber (the extension complete = `T` a base). **`Sharp`** is the one carried hypothesis — the
  coherent-closure refinement "a singleton fiber sees the whole fiber structure" (same-fiber points share their
  relation to any singleton fiber). It is **FALSE for a general CC but TRUE for `X_T`** (whose fibers are refined by
  relation to each determined point), so it is the clearly-isolated next discharge, not a gap in the engine. **Net:**
  the citation-free δ′ path now exists at the right level (the extension) for the `n≥25` residue the scheme-level
  engine could not reach; the chain is `DominatorReachable`-closure-on-`X_T` ⟹ (modulo `Sharp`) `X_T` complete ⟹ `T`
  a base ⟹ `b(X) ≤ |T|`. **NEXT (the isolated discharges, in order):** (1) **`Sharp (pointExtension X T)`** — prove
  the coherent closure satisfies `Sharp` (its fibers are WL-stable, so a singleton fiber's relations are constant on
  fibers); (2) wire `allSingletonFiber_of_dominatorClosure` on `X_T` to the seal consumer (extension complete ⟹
  `SeparatesAtBoundedBase`, via the §CC.9 / `IsPointExtension` bridge); (3) supply a bounded-base pinning rank for the
  amorphic-NLS family *on the extension* (the genuinely open `c(X_T)` content, now on the right object). The
  order-16 `RainbowRigid` lemma stays as the special case where the scheme-level engine already sufficed.
- **2026-06-13 — `Sharp (pointExtension X T)` PROVED — the δ′ engine's lone carried hypothesis is discharged on the
  extension (`CoherentConfig.lean §CC.10`; `sharp_pointExtension`, `allSingletonFiber_of_dominatorClosure_pointExtension`;
  both axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 95s; index regenerated,
  2 rows described).** The previous increment lifted the engine to `CoherentConfig` but left `Sharp` carried; this proves
  it for the actual construction. **`sharp_pointExtension`:** a singleton fiber `a` of `pointExtension X T` and a
  same-fiber pair `u,u'` (`relOf u u = relOf u' u'`) have equal relations to `a` (`relOf a u = relOf a u'`). The proof is
  the one sketched at handoff, verified end-to-end: the count `#{w : r(u,w)=r(u,a) ∧ r(w,u)=r(a,u)}` is exactly **1** —
  the only qualifying `w` is `a`, because `r(u,w)=r(u,a)` forces `w` into `a`'s fiber (`relOf_diag_right_eq`, the §CC.2
  derived fiber coherence) and that fiber is the singleton `{a}` — and the **fixpoint coherence `stableSetoid_pairCount`**
  transports `=1` to the `u'` row, producing a witness that must again be `a`, pinning `r(a,u')=r(a,u)`. One refinement
  over the hand-sketch: the witness-uniqueness sublemma (`iso_imp`) is stated with *independent* source components
  (`stableSetoid (p,w) (q,a) → w=a`) because the transported witness sits at `(u',w)` against `(u,a)` — `relOf_diag_right_eq`
  only inspects targets, so this is free. **`allSingletonFiber_of_dominatorClosure_pointExtension`:** the unconditional
  discreteness payoff on `X_T` — `(∀ v, DominatorReachable T v) ⟹ X_T discrete = T a base`, carrying **only `hclo`**
  (`Sharp` discharged by `sharp_pointExtension`, `T`-singleton-fibers by `(isPointExtension_pointExtension …).2.1`).
  **Net:** the citation-free δ′ chain on the extension is now `hclo` ⟹ `b(X) ≤ |T|` with no carried model hypothesis;
  the only inputs left are the two genuinely-open pieces below. **Lean note for the log:** §CC.10 is past
  `end PointExtensionConstruction`, so its section-wide `open scoped Classical` is gone — the `Finset.filter` exposed by
  `unfold pairCount` needs a `classical` tactic at proof start to synthesize `DecidablePred` (the §CC.8 gotcha, recurring
  one section later). **NEXT (ranked):** (1) wire `allSingletonFiber_of_dominatorClosure_pointExtension` to the seal
  consumer — `X_T`-complete ⟹ `SeparatesAtBoundedBase`, the **warmRefine↔fiber bridge at bases** (the load-bearing
  modeling risk: cells=fibers holds at `|T|≥2` per the Stage-2.1 direction check, refuted at `|T|=1`; state it base-keyed,
  reuse the §S-bridge B1–B5 template); (2) a bounded-base pinning rank for the amorphic-NLS family **on `X_T`** (the
  genuinely open `c(X_T)` math, now on the right object); then (3, deferred) the `SchurianScheme`/seal-capstone wiring +
  the hImprim `G₀Irreducible → IsPrimitive` bridge.
- **2026-06-13 — DECISION: the δ′ FAMILY-BY-FAMILY plan DRIES UP (it is an infinite ladder) ⟹ the input must be GENERAL
  (the (A)+(B) / cited-Thm-4.1 shape).** G2-B = primitive + small + non-Cameron; by Cameron's dichotomy "small
  non-Cameron" is just "small primitive", and small primitive schemes do **not** finitely classify (SRG / amorphic
  families are unbounded). `Probe_RainbowRigidFamily` already showed the n=16 mechanism (rainbow-rigidity, `c=1` in `S`'s
  own colours) **does not survive to n=25** — so enumerating δ′ closures is the de-classing anti-pattern the project
  abandoned once. **The project's own precedent is decisive:** the *affine* slice (itself infinite — cyclotomic schemes
  over every `F_q`) was closed by **citing the general 2-separability theorem + a finite `(p,d)` exception table by
  `decide`**, not by enumeration. Mirror that for the non-affine residue: **cite Ponomarenko Thm 4.1** for uniform
  coverage (seal `modulo {G3 + Thm 4.1}`), reducing the owed work to discharging Thm 4.1's conditions on the residue's
  extension (finite, structural, probe-backed Stage 3.2) + finite exceptions Clebsch-style. **Caveat (no free lunch,
  §1B):** even citing Thm 4.1 still owes condition (i) = domination = the *same* `c(X_T)` quantity the δ′ route bounds,
  so the δ′ engine on `X_T` stays the natural Lean vehicle for the domination half; what (A)+(B) buys is *uniform
  coverage in one theorem* instead of a per-family ladder.
- **2026-06-13 — THE WIRING TO THE SEAL LANDED — the δ′-on-`X_T` closure now reaches `reachesRigidOrCameron`
  (`CascadeAffine.lean §S-gate2`; `discrete_warmRefine_of_extensionComplete`,
  `separatesAtBoundedBase_of_extensionDominatorClosure`, `reachesRigidOrCameron_viaExtensionDominatorClosure`; all
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 70s; index regenerated, 3
  rows described).** Two probe findings scoped it first (`Probe_RainbowRigidFamily`, extended with a 1-WL-base
  measurement). **(i) NO dimWL-exchange citation needed:** the 1-WL (`warmRefine`, the seal model) base **equals** the
  2-WL coherent base `b(X)` on every residue instance — `Z4²` 2=2, `Z2⁴` 3=3, **`Z5²` 2=2** — so even where scheme-level
  δ′ fails and rainbow-rigidity is gone, plain 1-WL discretises at the same bounded base; the `X_T` machinery is a proof
  *device*, the conclusion holds in the seal's own currency. **(ii) the bridge IS the catch-up:** "warm cell ⊆ `X_T`
  fiber" is *exactly* `WarmTwinsAreFiberTwins`, so lifting δ′ to `X_T` (necessary for `n ≥ 25`) **re-incurs the catch-up
  the scheme-level δ′ avoided** — but nothing heavier. The decls: `discrete_warmRefine_of_extensionComplete` (a *complete*
  `E` + catch-up ⟹ `warmRefine` discrete — a 2-liner `hcomplete u' u (hcatch u u' hcell)`; the δ′ analogue of
  `twinsRealized_of_extensionPointed` consuming **completeness** not **separability**, so the catch-up is the *only*
  carried model hypothesis); `separatesAtBoundedBase_of_extensionDominatorClosure` (discharges `Sharp` internally via
  `sharp_pointExtension` + `allSingletonFiber_of_dominatorClosure_pointExtension`, so its open input is just `hclo` +
  `hcatch`, **no `IsBase`**); and the capstone `reachesRigidOrCameron_viaExtensionDominatorClosure` (mirror of
  `…viaDominatorClosure`, carrying {G3 + `hImprim` + `hclo`-on-`X_T` + `hcatch`}). **Net:** the citation-free `n ≥ 25`
  seal path is end-to-end; the lone open inputs are `hclo` (the `c(X_T)` math, per the decision above = the general
  theorem) and `hcatch` (probe-green at the family's bases — formalise via the B1–B5 forced-triangle engine, or cite the
  direction-check fact). **NEXT:** the open `c(X_T)` pinning rank on `X_T` for the amorphic-NLS family (general, not
  enumerated) + the `hcatch` discharge; then (deferred) `SchurianScheme`/capstone wiring + hImprim.
- **2026-06-13 — `hcatch` ANALYSIS + the free cases (`CascadeAffine.lean §S-gate2`;
  `warmTwinsAreFiberTwins_of_warmDiscrete`, `warmTwinsAreFiberTwins_of_dominatorClosure`; axiom-clean
  `[propext, Classical.choice, Quot.sound]`, full build green 101s; index regenerated, 2 rows).** Set out to discharge
  the catch-up and found an **important correction to the prior framing** (the "probe-green, formalize via B1–B5" note
  was too optimistic). `warmTwinsAreFiberTwins_of_warmDiscrete` (warm-discrete ⟹ `hcatch`, any `E`) is the converse of
  `discrete_warmRefine_of_extensionComplete`'s use of `hcatch`, so together: **at a complete extension,
  `WarmTwinsAreFiberTwins S T E ↔ Discrete (warmRefine …)`**. **Consequence (the honest finding):** for `n ≥ 25` the
  δ′-on-`X_T` closure delivers only **2-WL** (`X_T`) completeness, while `hcatch` *is* the **1-WL** discreteness the seal
  concludes — and 2-WL-complete does not give 1-WL-discrete for free. So discharging `hcatch` there is **equivalent to**
  establishing 1-WL discreteness directly: genuine content (the dimWL 1-WL↔2-WL exchange / the `c(X_T)` layer), **not
  plumbing**. The B1–B3 two-endpoint engine — the tool the optimistic note named — is *exactly* what stalls at `n ≥ 25`
  (probe). **What IS free:** `warmTwinsAreFiberTwins_of_dominatorClosure` discharges `hcatch` wherever the *scheme-level*
  δ′ closes (the order-16 residue), so `reachesRigidOrCameron_viaExtensionDominatorClosure` is non-vacuous and the two
  routes agree there — but it does not extend coverage (where scheme-level δ′ closes, the scheme-level capstone already
  applies). **Net (revised honest status of the wiring):** the δ′-on-`X_T` capstone is correct, but its `hcatch` is
  *not* an independent cheap step for `n ≥ 25` — it is coupled to `c(X_T)`. The clean resolutions: (a) **cite the dimWL
  exchange** (2-WL base ⟹ 1-WL base + O(1); probe shows the residue's blowup is 0) — adds a standard citation, makes
  `hcatch` follow from `hclo`+completeness; or (b) keep `hcatch` carried (probe-validated) and discharge it *together
  with* `c(X_T)`. **No free lunch (§1B) reaching the model layer.** NEXT unchanged: the open `c(X_T)`/`hclo` math
  (general, per the decision), now understood to subsume the `n ≥ 25` `hcatch`.
