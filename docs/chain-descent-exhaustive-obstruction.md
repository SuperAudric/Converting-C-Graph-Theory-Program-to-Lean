# Chain descent — the Exhaustive-Obstruction Lemma (plan)

> **STATUS (2026-06-05): Approach 3 (Cameron-free, scheme leg) STARTED — primitivity foundation
> LANDED, axiom-clean.** After the cross-branch coverage core generalized to non-abelian residuals
> (`coversOrbits_of_realizers`) and localisation was scoped (the polynomiality layer; per-level recovery
> = substrate-conditional WL-dimension boundary), the EOL was chosen as the goal-closing thread (it is
> what "reach a rigid **or Cameron** residual on all classes" actually requires). **Approach 3 chosen**
> (Cameron-free EOL on coherent-configuration residuals) over Approach 1 (cite-Cameron general): it
> yields a fully axiom-clean theorem, and a technical finding sharpens why — the general B1 bridge has a
> **coarsest-equitable gap** (1-WL computes the *coarsest* equitable partition, a block system is
> *finer*, so block ⟹ refinement-split is **not** free in general), whereas **on schemes a block system
> = a closed relation subset = refinement-visible by construction** (1-WL computes the scheme). **Landed
> (`Scheme.lean §1.2`, axiom-clean):** `ClosedSubset` (block system = diagonal-containing,
> complex-product-closed relation subset), `schemeEquiv` (+ `_refl`/`_symm`/`_trans`/`_equivalence` — the
> block system is a genuine equivalence, transitivity from the intersection numbers), `closedSubset_univ`,
> `IsPrimitive` (only `{R_0}` and `univ` closed — Cameron-free scheme primitivity). **Bridge, foundational
> half LANDED (`Scheme.lean §4.2.1`, axiom-clean):** `schemeEquiv_isSchemeAut` (the block system is
> scheme-automorphism-invariant — a genuine *system of imprimitivity*, from `IsSchemeAut.relOfPair_eq`) and
> `schemeEquiv_schemeOrbit` (the block of `v` is a union of v-stabilized scheme-Aut orbits — the block
> system is coarser than the orbit partition). So a non-trivial `ClosedSubset` is an Aut-invariant block
> structure compatible with the orbit action — the combinatorial-closed-subset → group/orbit bridge.
> **Bridge CLOSED (`Scheme.lean`, axiom-clean):** `SchurianSchemeGraph.schemeEquiv_graphOrbit` (graph-Aut
> version of the orbit-coarseness, via `isAut_imp_isSchemeAut`) and **`schemeEquiv_warmRefine_of_pPolynomial`**
> — on a P-polynomial schurian scheme graph, same `warmRefine` cell (after individualizing `v`) ⟹ same
> `schemeEquiv I` block, by composing recovery (`theorem_2_HOR_of_pPolynomial`: cell ⟹ `OrbitPartition adj P {v}`)
> with `schemeEquiv_graphOrbit` (dropping the P-clause via `h.matching`). So a `ClosedSubset`'s **block is a
> union of `warmRefine` cells = refinement-visible**: scheme-imprimitivity is seen by refinement, the ingredient
> for "imprimitive ⟹ cascade" / contrapositive "non-cascade ⟹ primitive".
>
> **GROUP-SIDE primitivity bridge LANDED (2026-06-05, axiom-clean, `Scheme.lean §11`).** The combinatorial
> `IsPrimitive` is now proved to **coincide with Mathlib's `MulAction.IsPreprimitive`** of the scheme-Aut
> group — `isPreprimitive_iff_isPrimitive` (a schurian scheme where every relation occurs). Pieces:
> `SchemeAutGroup` (scheme-Aut as a `Subgroup`), `schemeAutGroup_isPretransitive` (transitivity is *free*
> from the schurian axiom at `R_0`), `isBlock_schemeEquiv` (a `ClosedSubset`'s `schemeEquiv` class is a
> Mathlib `IsBlock`), and both directions `isPrimitive_of_isPreprimitive` / `isPreprimitive_of_isPrimitive`.
> This grounds "primitive scheme" in the **standard primitive-permutation-group notion** the cited capstone
> (Babai / Sun–Wilmes) is stated against, and unlocks Mathlib's primitivity layer (R5) for the leg — the
> genuinely-new Lean content of the (B1) bridge, group side, **with no refinement / WL-dimension content**.
>
> **FINDING (2026-06-05) — the *refinement-side* "decomposition conclusion" is NOT the light next step the
> earlier STATUS claimed; the group side above was the right provable piece.** Three obstructions surfaced
> reading the landed code: (i) `schemeEquiv_warmRefine_of_pPolynomial` is **gated on `PPolynomial`**, which
> already forces cascade at depth 1, so the contrapositive "non-cascade ⟹ primitive" is **vacuous on the
> P-polynomial class**; (ii) generalizing the bridge off `PPolynomial` (where the contrapositive bites) is
> exactly the **WL-dimension / cascade boundary** — declassing §9 "B's core", substrate-conditional, *not*
> a clean theorem; (iii) the full "descent decomposes into quotient + fibers in bounded depth" needs the
> quotient-graph + fiber-graph + depth machinery **modelled in Lean** (only the spine is, today) — a large
> modelling task, not "lighter". So the refinement-side decomposition is deferred as heavy/substrate-
> conditional; the **capstone** (primitive high-rank scheme w/ no abelian regular ⟹ Johnson/Hamming) remains
> a **cited hypothesis** (`PrimitiveCCClassification`, §4 R5), now statable against the standard `IsPreprimitive`.
>
> **CAPSTONE ASSEMBLED (2026-06-05, axiom-clean, `Scheme.lean §12`).** The leg-C EOL is now *stated* on
> scheme residuals and reduced to the cited classification: `exhaustiveObstruction_scheme` — a **primitive**
> (`IsPrimitive`), **large** (`IsLargeScheme`), CC-rank-≥-3 schurian scheme residual is a **Cameron
> section** — plus the doc-§1 disjunction form `exhaustiveObstruction_scheme_trichotomy`
> (`¬IsPrimitive ∨ ¬IsLarge ∨ Cameron`). The **only** non-routing step is the §11 group-side bridge
> `isPreprimitive_of_isPrimitive`, converting the descent's *combinatorial* `IsPrimitive` into the *group*
> `IsPreprimitive` the citation is phrased over — exactly what the bridge was built for.
> **`PrimitiveCCClassification` is a `def` (Prop) carried as an explicit hypothesis argument, NOT a fresh
> `axiom`** (verified: all new decls depend only on `[propext, Classical.choice, Quot.sound]`; the project
> stays custom-axiom-free); `IsCameronScheme` and `IsLargeScheme` are arbitrary predicate parameters (cited
> black boxes — the EOL routes into them, never inspects them).
>
> **Faithfulness fix during assembly — largeness is the driver, NOT non-abelian (the C₇ trap).** A first
> cut keyed the Cameron branch on **non-abelian** (the seal's ¬D2). That makes the cited
> `PrimitiveCCClassification` **factually false**: the 7-cycle scheme `C₇` is schurian, **primitive** (7
> prime), **rank 3**, **non-abelian** (`Aut = D₇`), yet *cascades* (metric/`PPolynomial`, recovers at depth
> 1) and is **not** Cameron (`|Aut| = 14`). Babai/Sun–Wilmes genuinely needs **super-polynomial `|Aut|`**
> (largeness) — `IsPrimitive` is **not** "non-cascade" (the FINDING above; primitive ⊉ non-cascade on the
> P-poly class) and non-abelian is **not** largeness (this is precisely §4 R3, the base-size gap). Fixed:
> the antecedent is now **`IsLargeScheme`** (carried abstractly = super-poly Aut / non-cascade survival /
> high WL-dimension), which correctly excludes `C₇`. Deriving `IsLargeScheme` from the descent's
> "non-cascade" observation is the substrate-conditional refinement-side content (declassing §9), so it is
> a hypothesis. **Lesson for downstream:** when stating the EOL anywhere, the Cameron-branch driver is
> *largeness/non-cascade*, never *non-abelian* alone.
>
> **Honest scope:** `IsPrimitive` and `IsLargeScheme` are both *hypotheses*; the theorem canonizes no new
> graph (Cameron still flags) — the *classification* half, Cameron-hard, not GI-hard. This is the
> **Tier-3/Approach-1 deliverable shape** (EOL modulo a cited classification, new content axiom-clean),
> realized on the Approach-3 scheme-residual class. What remains genuinely open is unchanged: the
> refinement-side decomposition (substrate-conditional) and discharging the cited classification itself
> (deep, out of scope).
>
> **Capstone target pinned + Mathlib reality (2026-06-05 — corrects the "Cameron-free = lighter capstone"
> reading; see §4 R5 and §5 Approach 3).** The capstone's classical content is **Babai's classification of
> primitive coherent configurations** (Babai 1981; Sun–Wilmes 2015: a primitive CC of rank ≥ 3 whose
> automorphism group is super-polynomially large is a Cameron scheme — Johnson/Hamming). **Mathlib has *zero*
> substrate for it:** no association schemes, coherent configurations, Bose–Mesner algebra, distance-regular
> graphs, or scheme spectral theory (the "Higman/Hanaki" eigenvalue/character machinery is entirely absent —
> only Higman's-lemma / HNN false-positive string matches exist). What *is* present is the primitive
> permutation-group action layer (`Primitive`/`IsPreprimitive`, `Blocks`, `Jordan`, `MultiplePrimitivity`),
> which is exactly what the **landed bridge** and the **decomposition conclusion** use. So the capstone, like
> Cameron in Approach 1, must enter as a **named cited hypothesis** (`PrimitiveCCClassification`), not a
> from-Mathlib proof. **The genuine, axiom-clean deliverable of Approach 3 is therefore the bridge +
> decomposition (pieces 1), not the capstone.** Approach 3's advantage over Approach 1 is *not* "no deep
> citation" — it is (a) narrower scope (scheme/CC residuals = the project's WL-stable-partition setting), (b)
> the clean bridge with no coarsest-equitable gap (provable, landed), and (c) a more *natural* citation
> (combinatorial CC classification vs group-theoretic O'Nan–Scott/Cameron).
>
> **BOTTOM-UP ROUTE + current frontier (2026-06-05 — orientation; full record in §0.7).** Independently of
> the cited capstone, the seal's leg-C conclusion is derived from the harvest mechanism (§0.7):
> `non-consumed ⟺ ¬D1 ∧ ¬D2 ⟺ large primitive non-abelian ⟺ Cameron`. **Steps 2 & 4 formalized
> axiom-clean** (`Group.lean`: `smul_eq_on_orbit_of_comm` etc. = abelian ⟹ unique candidate ⟹ consumed;
> `not_comm_of_isPreprimitive_card_lt` = large primitive ⟹ non-abelian). **Step 3a (imprimitive ⟹ cell
> splits) conditional form + A2-ii graded discharge landed** (`Scheme.lean §13`: `BlockRefinementVisible`,
> `cell_splits_of_imprimitive`, `blockRefinementVisible_of_schemePartSeparates`). **A2-iii RESOLVED
> NEGATIVELY (2026-06-05): unconditional block-visibility is FALSE** — the twin-pair search
> (`TwinPairSearchExperiment.cs`, graph-first/Aut-faithful) found the **Shrikhande graph** as a clean,
> verified witness (rank-4 orbital scheme, block system `I={R₀,R₂}` = 4 blocks of 4, 1-WL-from-`v` blind:
> 3 SRG cells vs 4 orbital classes). So `SchemePartSeparatesBlock` does **not** hold for every
> `ClosedSubset`; block-visibility is **depth-graded**, not depth-1, and collapses into the
> substrate-conditional WL-dimension boundary. **Do not pursue unconditional A2-iii (dead).** Crucially the
> witness is **recoverable at depth 2** (small WL-dimension) — so a Gate-G failure is **NOT** an
> `(O*)`-existence witness, correcting the earlier binary. Full record + redirect in §0.7 "A2-iii RESULT".
> **THE OPEN FRONTIER now:** close Step 3 via the top-down §12 capstone (no A2-iii needed) or a
> depth-graded block-visibility tied to `RecoverableByDepth`; plus (3b), the heavy unbuilt quotient/fiber
> recursion.
>
> **ACTIVE TRACK (2026-06-06) — deriving the *largeness* antecedent (§0.7.5).** Independently of primitivity,
> the **largeness** antecedent of the §12 capstone is now being *derived* (not hypothesized): `leg C ⟹ large`
> ⟸ `small ⟹ consumed` ⟸ completeness of deferral ⟸ **no fusion**, with the payoff lemma `¬D1 ∧ NoFusion ⟹
> |Aut| = ∏ orbit-sizes super-poly = large` resting on the **landed** `card_autP_eq_prod_of_base`. The
> separable case is provable; the entangled case is the **`NoFusion` witness**, validated by an adversarial
> battery. Plan: [`chain-descent-fusion-battery-plan.md`](./chain-descent-fusion-battery-plan.md); orientation
> in §0.7.5. (Primitivity stays the separate depth-graded line above.)
>
> Original planning note: this doc plans the item the user surfaced 2026-05-31: the
> hypothesis that **"a graph that does not decompose into the cascade+abelian
> class *is* a hidden Johnson."** It is a **hypothesis, not a certainty** — the
> plan deliberately budgets for refuting it.
>
> Companions: [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
> (Piece C / the (O\*) lemma), [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
> §2/§4/§8 (the two-axis map, sub-claim 2, the wall),
> [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3 (hardness axes),
> [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 gap 5.

---

## 0. The one-sentence contribution

The project's docs bundle **two different claims** under one name "(O\*) / the
wall / GI ∈ P." Pulling them apart is the whole point of this item, because
**one of the two is *not* GI-hard and is a legitimate, finite proof target** —
and it is exactly the user's hypothesis.

- **(O\*)-existence** — *"every graph's residual, after abelian stripping,
  cascades"* (= **no** graph ever hits the wall). This is
  [tier3 §5](./chain-descent-tier3-decomposability.md): if it held in general,
  chain descent would canonize every graph ⟹ **GI ∈ P**. The wall. **Excluded,
  correctly.**
- **(O\*)-classification** — *"**if** a residual does not cascade and is
  non-abelian, **then** it contains a Johnson/Cameron section"* (**Cameron** =
  Cameron's *large-primitive-group theorem*, §1 disambiguation box — **not** the
  Cameron graph). This is the
  user's hypothesis. It says nothing about whether the bad case *arises*; it
  says that *when* it arises it is the named, flaggable one. **This is the
  Exhaustive-Obstruction Lemma, and it is NOT GI ∈ P** (proving it canonizes no
  new graph — the Johnson case still flags). It is **Cameron-hard**, not
  **GI-hard**.

The docs already half-know this — [hidden-johnson §7](./chain-descent-hidden-johnson.md)
calls the classification *"a known-hard but not known-impossible classification
result"* and grounds it in **O'Nan–Scott + Cameron/Maróti**. Earlier framings
collapsed it back into *"= GI ∈ P, no Lean obligation"* (and pointed at a
nonexistent "strategy gap 7" rather than the real
[strategy §15 gap 5](./chain-descent-strategy.md)). That collapse is the
conflation this item removes; the **Approach-0 disentangle has now been written**
(2026-06-02) across strategy §15 gap 5, calculator §3/§6/§7/§9, tier3-decomposability
§0/§6/§8.1, and hidden-johnson §7. **The user's "unnamed gap" was precisely the gap
this conflation hid.**

---

## 0.5 The oracle-capability seal — the primary framing (2026-05-31)

> **This supersedes the group-classification framing as the *organizing*
> structure.** §1's statement and §5's approaches still hold, but they are now
> *legs* of the seal below rather than the top-level plan. The change matters
> because it makes **exhaustiveness free** — and isolates the only Cameron-
> dependent content to one leg.

**The insight (user, 2026-05-31): case-split on what the *oracles* can detect,
not on what the *graph* is.** Each oracle gets a capability theorem; the three
compose into a watertight seal *without enumerating symmetry types or graphs*,
because the case split is on **negation-complete predicates** — there is no room
for a fourth species.

**Conditioning.** The whole seal is under the hypothesis **a symmetry exists**
(an automorphism relates two reps of the target cell). The *no-symmetry* case —
rigid / IR-blind-spot / **multipede** — is the *other* flag cause (residual group
**trivial**, distinguished at flag time by group order; strategy §15 gap 5) and
sits **outside** the seal. Leg C must not be asked to absorb it.

**Two discriminators** (both decidable predicates on the symmetry at a node):

- **D1 — unconditional?** Is the symmetry exposable by *symmetry-only*
  individualization (orbit representatives), within the **polynomial depth
  bound**, *without committing a real (non-symmetric) decision*? This is exactly
  the **unconditional vs. conditional** line of
  [deferred-decisions §5/§8](./chain-descent-deferred-decisions.md) — "revealed
  without fixing a real decision" *is* "unconditional." **D1 must be defined
  abstractly** (∃ a poly-length symmetry-only individualization that exposes it),
  *not* "the built oracle finds it," or leg A is circular.
- **D2 — unique candidate?** Among *not-unconditional* symmetries, does one
  branch's propagation expose a **unique candidate twist**? This is the
  [calculator §6](./chain-descent-calculator.md) abelian/wall boundary
  (unique candidate ⟺ abelian).

**The three legs (oracle-relative theorems) and the tiling:**

| Bucket | Predicate | Handler | Leg = which program |
|---|---|---|---|
| **A** | D1 (unconditional, *any* group) | cascade oracle | **orbit recovery** — leg A's boundary (the "unless revealed by a real decision" caveat) **is** the D1 cutoff = the cascade-1b decision-node frontier |
| **B** | ¬D1 ∧ D2 (hidden abelian) | linear oracle | **abelian-sufficiency** (the handoff doc's open core: "abelian ⟹ linear finds it") |
| **C** | ¬D1 ∧ ¬D2 (hidden, non-abelian, no unique candidate) | **flag** | **the new structural leg: ⟹ Cameron** |

The seal is the **tautology** `D1 ∨ (¬D1 ∧ D2) ∨ (¬D1 ∧ ¬D2)`. Exhaustiveness
needs **no** classification — Cameron/O'Nan–Scott is required only *inside leg
C*, never to close the seal. This is the structural improvement over §1's framing.

> **THE SEAL IS ASSEMBLED AS ONE THEOREM (2026-06-06, axiom-clean, `Cascade.lean` Part A).**
> `reachesRigidOrCameron` / `reachesRigidOrCameron_viaHarvest`: every rank-≥3 schurian scheme residual
> `ReachesRigid ∨ IsCameronScheme` — reaches a rigid residual (legs A/B consume it) or is a Cameron section
> (leg C flags). Wires the landed `exhaustiveObstruction_scheme_nonCascade_trichotomy` (`¬IsPrimitive ∨
> ¬NonCascade ∨ Cameron`): `¬NonCascade`→cascade-recovery (leg A), Cameron→landed; with the largeness bridge
> discharged (`largenessBridge_viaHarvest`), the **free inputs are exactly the honest remainder** — the cited
> `PrimitiveCCClassification` (Babai/Sun–Wilmes), the leg-A cascade-recovery reduction (well-supported), and the
> **primitivity reduction** `¬IsPrimitive ⟹ ReachesRigid` (the one open in-scope gap; §0.7.2 Step 3 /
> Shrikhande's depth-graded block-visibility). The goal is now a typed object whose hypothesis list is the
> to-do list; the live target is the primitivity reduction in *correctness* (eventual-visibility + cell-size
> induction) form. `ReachesRigid` is the abstract descent-outcome predicate (descent dynamics are not one Lean
> object); the IR-core / no-symmetry case (residual trivial) sits outside the seal (§0.6, the other flag cause).

- **Leg A (cascade capability):** *"every unconditional symmetry is cascade-
  certifiable."* = orbit-recovery completeness. Real content (D1 abstract ⟹ the
  built oracle realizes it); the cascade-1b / decision-node-depth frontier is
  literally the D1 boundary.
- **Leg B (linear capability):** *"every hidden abelian symmetry is linear-
  certifiable."* = the abelian-sufficiency lemma (handoff §1–§5).
- **Leg C (the Cameron leg):** *"a symmetry that is non-abelian **and** survives
  all poly-depth symmetry-only individualization is a Cameron/Johnson section."*
  Proof strategy below.

> **The harvest window realises legs A+B, and its *argument* is now PROVED class-agnostic
> (2026-06-02).** [harvest-window §2.4](./chain-descent-harvest-window.md): "a symmetry with a
> (poly-depth) harvest window is harvested" is `colourMatch_eq_aut` / `harvest_isAut_of_discrete`
> ([`CascadeOracle.lean`](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean) §C.2,
> axiom-clean) — at a discrete footprint the colour-match candidate **equals** the orbit
> automorphism (via `warmRefine_transport`), independent of graph class, with no σ-coherence /
> cycle / rank rebasing. So legs A and B are **one** mechanism, and the seal **is** the
> harvest-window's existence characterization: `D1∨D2` ⟺ "has a harvest window," with
> `Findable ⟹ RecoverableByDepth ⟹ CellComplete ⟹ CascadeComplete` class-agnostic end to end. The
> only class-specificity is the window's **depth**, and it splits exactly along A/B: **leg A
> (visible, any group incl. non-abelian)** depth = `base(g)` — the symmetry's *own support*,
> seal-characterizable; **leg B (hidden abelian)** depth = the *concealment structure* (CFI's
> `tw(H)`, via cycle-space; **substrate-conditional** — this is "B's core" /
> `AbelianSufficiencyHolds`). **Leg C is the *absence* of a harvest window** — the wall. The
> per-class CFI/scheme theorems are therefore A/B *witnesses* populating `CascadesAt`, **not** the
> seal's reasoning; in particular the cascade-1b "decision-node-depth frontier" named under leg A
> above is precisely the leg-B *depth witness*, not the harvest argument (which is now closed).
>
> **D1 now has concrete realizations (2026-06-02).** `EdgeGenerates` (a scheme's edge relation
> exposes all relations by bounded-round counting) **is** D1 for scheme graphs, and `PPolynomial`
> (the distance ladder) is its *graded* form — both discharged via a generic saturation engine that
> de-classed the scheme rank ladder (the metric/DRG family in one theorem,
> `theorem_2_HOR_of_pPolynomial`). The same engine proves Leg-A's support-induction termination for
> *every* graph (`exists_isBase_saturated`). Full account:
> [`chain-descent-declassing.md`](./chain-descent-declassing.md).

**Leg C's proof = the inversion (user's method, sharpening §8.1 of tier3-decomp).**
Do **not** start from "an arbitrary primitive group." Instead:
1. **Extract the oracle-limit fingerprint** from legs A and B's *completeness
   proofs*: cascade succeeds because property `X` holds and fails exactly at
   `¬X`; linear succeeds because `Y` and fails at `¬Y`. The bucket-C hypothesis
   `¬D1 ∧ ¬D2` *unfolds* into a concrete property list — *primitive* (no
   refinement-visible block system — else cascade would split it), *large base*
   (survives poly-depth individualization — the D1 cutoff, my R3), *no abelian
   regular structure on the cell* (no unique candidate — ¬D2).
2. **Prove `fingerprint ⟹ Cameron`** with that concrete hypothesis, citing the
   classification only here. **Jordan's theorem** (Mathlib, R5) plausibly carries
   the *large-base ⟹ `A_k`* step, possibly Cameron-free for a restricted slice.

This is why the inversion beats the abstract route: leg C's hypothesis is the
*exact oracle-failure boundary the Lean proofs already produce*, not a generic
primitive group. The "obscuring-structure" `S(H)` of
[tier3-decomp §8.1](./chain-descent-tier3-decomposability.md) is now **defined**
as that fingerprint, not hypothesized.

**Leg C as a consistency check on D1/D2 — the diagnostic reading (one potential
use, distinct from the forward proof).** Because the tiling
`D1 ∨ (¬D1∧D2) ∨ (¬D1∧¬D2)` is a tautology, the bucket-C cell does double duty:
beyond being the *thing to classify* (forward, above), it is the **error surface
that audits the D1/D2 predicates themselves**. The check: leg C is supposed to be
exactly the genuine Cameron sections. So a symmetry the program can actually
*consume* (recoverable in poly depth), or that is otherwise demonstrably **not** a
Cameron section, yet lands in `¬D1∧¬D2`, is a **leak** — a signal that D1/D2 (or
the oracle set behind them) is failing to model a capability it has, *not* a new
hard case. This is what makes the seal self-auditing rather than merely asserted.

- **The remediation is open-ended — a leak does *not* force D1/D2 surgery.** A
  discovered leak can be closed by *any* of: **(i)** refining the D1/D2
  definitions (what happened to the **flat screen**: `CFI(Kₘ)` is recoverable yet
  was `¬D1∧¬D2` under the single-node reading — fixed by the *sequential* screen +
  the `¬IsBase` guard, [harvest-window §6](./chain-descent-harvest-window.md));
  **(ii)** adding a **new oracle / capability leg** for the leaked class; or
  **(iii)** **re-routing** the case into one of the two existing oracles. The leg-C
  partition tells you *that* something is unmodeled and *where*; it does not dictate
  which of these three fixes applies.
- **Already productive before any formal leg-C proof.** Used purely as a
  refinement/diagnostic discipline, the negation-complete partition has already
  ruled out unviable options: the **σ-cell-coherence route** (`C1b.3`,
  machine-checked false in its operative regime); the **flat screen** (above); and
  **CFI(triangle base)** — `cfi_triangle_no_twins` showed CFI's `Z₂` is a *global
  gadget-flip*, not a transposition, so a twin-based handling of CFI's abelian
  symmetry is the wrong model (the twin slice and CFI are complementary abelian
  classes). None of these required proving leg C; the *exhaustiveness discipline*
  alone was the useful tool.
- **It remains "one potential."** The diagnostic reading is complementary to —
  not a replacement for — the forward Cameron-classification target, and it may
  be that the most valuable output of leg C is this auditing role even if the full
  `¬D1∧¬D2 ⟹ Cameron` proof is never reached.

**Honest caveats (so the seal does not leak):**
- **Legs A and B are the program's existing open frontiers.** The seal *unifies*
  — the EOL becomes a **capstone of finishing oracle completeness + leg C**, not
  a separate effort — but it does not make A/B free.
- **Per-node, lifted by composition.** The seal classifies the symmetry *at one
  decision node*; whole-graph coverage rides on the layer decomposition
  (Part A `LayerChain` / Tier-3a "depths add") stripping `N ⋊ Q` layer by layer.
- **Leg C still cites Cameron** — but with the concrete fingerprint hypothesis,
  and possibly Cameron-free on the Jordan-reachable / scheme-restricted slice
  (Approach 3).

**How the §5 approaches re-map onto the legs:** Approach 0 (disentangle) is still
the prerequisite. Approach 2 (empirical) now *also* stress-tests the leg-C
fingerprint (does every oracle-failure-with-symmetry have it?). Approach 1
*becomes* leg C via the inversion above. Approach 3 (Cameron-free on schemes) is
the restricted leg-C proof. Legs A and B are **not new** — they are the
orbit-recovery and abelian-sufficiency programs, now recognized as two-thirds of
the seal.

---

## 0.6 The two flag causes — the seal classifies symmetry; the IR core is orthogonal

The seal (§0.5) is conditioned on **a symmetry exists**. The program flags for
**two independent reasons**, and they must *never* collapse into one — the IR
core has **no symmetry**, so folding a multipede into Cameron is a category error
(**Cameron = unconsumed symmetry**; **multipede = absence of symmetry**).

State the endpoint as **two separate guarantees**, never a single sentence:

1. **Symmetry completeness (the seal).** *Every symmetry is consumed by an oracle,
   **OR** it is a Cameron section.* This is §0.5. In the flag case the residual
   group is **non-trivial**.
2. **Polynomial time (two conditional escapes).** *The residue canonizes in
   polynomial time **unless** it contains a Cameron section (unconsumed symmetry,
   residual group **non-trivial**) **OR** it is an IR blind spot (a **multipede** —
   refinement-resistant rigid core, **no** symmetry, residual group **trivial**).*

The IR core is **outside the seal by construction**: the seal classifies
*symmetric* obstructions, and a multipede is the *¬∃-symmetry* flag. The two are
separated operationally at flag time by **residual-group order** (non-trivial ⟹
Cameron; trivial ⟹ IR core — [strategy §15 gap 5](./chain-descent-strategy.md),
[calculator §14](./chain-descent-calculator.md)).

> **This separation is now a *predicate-level* fact in the screen, not only an
> operational one.** [harvest-window §6](./chain-descent-harvest-window.md) defines
> the screen's abelian leg as `ResidualAbelian S ∧ ¬IsBase S` — the **`¬IsBase`
> (non-trivial-residual) guard** is exactly the "a symmetry exists" conditioning,
> made structural. Bare `ResidualAbelian` is *vacuously true on the multipede*
> (trivial residual), so without the guard the abelian leg would absorb the IR core
> (asserting `D2 ⟹ recoverable` on a refinement-stuck rigid graph — false). With it,
> `¬Findable` bottoms at hidden residuals partitioned by order: **trivial ⟹ IR core,
> non-trivial non-abelian ⟹ Cameron** — so leg C's escape set is precisely the
> non-trivial non-abelian residual, which is what makes the strict-Cameron target
> (R1) statable once a rigid solver retires the trivial-residual flag.

> **F2 — the *operational* order signal is abelian-blind (composite-graph audit,
> 2026-06-01; [harvest-window §6](./chain-descent-harvest-window.md)).** The
> *predicate-level* separator above is "non-trivial **non-abelian** ⟹ Cameron." But
> the coarse *operational* flag signal often quoted as "non-trivial residual ⟹
> Johnson-like" ([strategy §14](./chain-descent-strategy.md)) checks **order, not
> abelian-ness** — so an *unconsumed abelian* residual (e.g. a CFI gauge over an
> **unbounded-treewidth** base, the §2 gap-(B) flagged region) is non-trivial *and*
> abelian, and the order-signal would mis-tag it "Johnson-like" though it is **not
> Cameron**. The predicate screen is unaffected (abelian ⟹ D2, never reaches the
> order test); but any *operational* flag classifier must test **abelian-ness**, not
> just order, before routing to leg C. NB the trigger is **unbounded tw**, not
> rigidity: CFI cascade depth is governed by `tw(H)` alone, so a rigid *bounded-tw*
> base consumes its gauge cleanly (the audit corrected an "IR-resistance blocks the
> gauge" mis-attribution).
>
> **F2 fix LANDED in the C# (2026-06-05).** The operational flag classifier now tests
> abelian-ness: `PermutationGroup.IsAbelian` / `IsElementaryAbelian` (generators
> pairwise commute / are involutions) drive `CanonizationFlaggedException.ClassifyFlag`,
> which routes the harvested residual into a **trichotomy** — trivial ⟹ `IrBlindSpot`
> (multipede), non-trivial **abelian** ⟹ **`AbelianUnconsumed`** (CFI gauge `Z₂^d`,
> *not* Cameron), non-trivial **non-abelian** ⟹ `Tier2Like` (the leg-C / Cameron
> candidate). Both the thrown exception and `CanonGraphOrdererChainDescent.LastFlagKind`
> classify the same residual through this one method, so an unconsumed abelian residual
> is no longer mis-tagged Cameron-like. Tested deterministically on known groups
> (Z₂², Z₂³, C₅, S₃, D₄) in `PermutationGroupTests.cs`; the abelian-blind order-only
> signal is retired. (A deliberate *end-to-end* CFI-over-high-tw flag that exercises the
> `AbelianUnconsumed` bucket is a follow-on, paired with the Approach-2 battery.)
>
> **IR-blind-spot fixture LANDED (Probe B, 2026-06-05) — and a finding.** `MultipedeGenerator.cs`
> builds the faithful Neuen–Schweitzer/Gurevich–Shelah multipede (STOC 2018, arXiv:1705.03283): from a
> bipartite base `(V,W)`, each `w` → a segment `{a(w),b(w)}`, each `v` → a CFI parity gadget over `N(v)`
> (the gadgets *share* the segments — no inter-gadget bridges, the delta from CFI). The fine-coloured
> `R(G)` is **rigid ⟺ the base is "odd" ⟺ its biadjacency has full F₂ column rank** (Lemma 4.3/4.4;
> `IsOdd`), so a small deterministic **circulant** base ({0,1,3} on Z_m, odd ⟺ 7∤m, 6m vertices) yields a
> certified-rigid multipede — the project's first IR-core fixture (closes the "zero IR-core tests" gap,
> strategy §14/§15 gap 5). **Finding:** chain descent **canonizes** small/mid rigid multipedes (circulant
> to 72 v; random-3/5-regular to 288 v) — rigid (residual trivial, *confirming* rigidity) but discretizing
> in ≤ 7 levels. A *natural* IrBlindSpot **flag** requires a **meager** (locally sparse / high-girth) base
> at **scale** — the NS lower bound is asymptotic, and expanders propagate parity fast (easy), so small
> instances do not flag. The descent is thus **robust on small rigid IR-cores**. The IrBlindSpot
> *classification* is validated directly (a tight-budget flag on a certified-rigid multipede → trivial
> residual → `IrBlindSpot`, scramble-invariantly); the **natural-flag-at-scale** over a meager base
> (hundreds+ vertices) is the scoped follow-on.
>
> **Cameron battery — positive-control half LANDED (Probe A, 2026-06-05) — and a strong positive result.**
> `CameronGraphGenerator.cs` builds the two Cameron-group shapes: **`Johnson(n,k)`** (the `d=1` `Aₖ`-on-
> subsets case, `Aut = Sₙ`) and **`Hamming(d,q)`** (the **product action** `S_q ≀ S_d` — the direct control
> for **R1**, "Johnson is too narrow"), plus **`Kneser(n,k)`** (a second `Sₙ` control). The near-theorem
> (§3 item 2; [hidden-johnson](./chain-descent-hidden-johnson.md)) predicts a *visible* Cameron group is a
> scheme graph ⟹ cascades ⟹ canonizes, never `Tier2Like`. **Confirmed:** all 10 measured instances
> (`J(4..8,2)`, `H(2,3)/(3,2)/(2,4)/(3,3)`, `K(5,2)/(7,3)`; 6–35 vertices) **canonize** in 4–7 nodes, and
> the harvested `|Aut|` **exactly equals** the known closed form in every case — including the non-abelian
> `S₇ = 5040` and `S₄≀S₂ = 1152`. This empirically validates the scheme/cascade leg
> (`theorem_2_HOR_of_pPolynomial`), the a-posteriori harvest computing the *full* automorphism group, and
> the no-visible-hidden-Cameron near-theorem. Tests: `CameronGraphGeneratorTests.cs` (with an independent
> brute-force `Aut` cross-check pinning the formulas) + `GraphCanonTests.Cameron.cs` (canonize + exact-Aut
> + scramble-invariant canonical form). **The hard half — an ENCODED non-cascade non-abelian obstruction —
> is NOT built and is out of scope by construction:** it is the GI-hard `(O*)-existence` question (the open
> EOL frontier); visible Cameron groups *can't* be the hard residual precisely because they cascade. So the
> empirical Approach-2 gate (C+B+A) confirms every constructible *visible* obstruction is consumed-or-rigid,
> and isolates the two genuine open items (a meager multipede at scale; an encoded Cameron section) as the
> *same* asymptotic / GI-hard frontier the theory already routes around.

**Drafting rule for every downstream statement.** "All symmetry removed **or**
Cameron" (statement 1) is **not** the time bound (statement 2): statement 2 carries
the *extra* IR-core escape. A future Phase-2 blind-spot handler
([deferred-decisions §7](./chain-descent-deferred-decisions.md)) addresses **only**
that escape — never the seal. Keep both clauses, always.

---

## 0.7 The mechanism-side derivation (bottom-up) — an independent route to the seal

> **STATUS (2026-06-05): a second, independent derivation of the seal's leg-C conclusion, from the
> *harvest mechanism* rather than the *group classification*.** Where §0.5/§1 reach "the non-consumed
> obstruction is a Cameron section" **top-down** (cite O'Nan–Scott / Babai–Sun–Wilmes), this section
> reaches the *same* conclusion **bottom-up** — from what the oracle can and cannot harvest, plus one
> textbook group fact (*a transitive abelian action is regular*). The two routes meeting at the same
> wall is a faithfulness cross-check; and the bottom-up route makes **leg B's "abelian ⟹ consumed" half
> citation-free and Lean-provable** (the §12 capstone still cites the classification only for leg C).

### 0.7.1 The question

Call a symmetry **non-consumed** if the oracle never harvests it within the polynomial budget, yet — by
soundness — it is never returned *wrong* (the descent over-splits on it instead). What must a graph look
like for a non-consumed symmetry to *exist*? The derivation answers: **it can only be a Cameron section**
— there is *no* non-consumed *abelian* species — and exhibiting one is therefore the wall (`(O*)`-existence,
GI-hard), not something constructible cheaply.

### 0.7.2 The derivation (per refinement-stable orbit `O`)

Fix one residual-orbit `O` (the residual acts transitively on it; a multi-orbit cell is handled orbit
by orbit).

1. **Non-consumed ⟹ `¬D1` (does not cascade).** Any symmetry visible by symmetry-only individualization
   at polynomial depth is harvested by leg A (orbit recovery) at depth `base(σ) ≤ |support σ| ≤ n`,
   *regardless of its group*. So a non-consumed symmetry is hidden: `¬D1`.

2. **The rigorous core — on `O`, abelian ⟹ unique candidate (`D2`).** The candidates for a decision
   `e ↦ f` are exactly `{g : g • e = f}` = a coset of the point-stabilizer `Stab(e)` *in the image acting
   on `O`*. A **transitive abelian** action is **regular** (`Stab = 1`): for `s ∈ Stab(e)` and any `c = k•e`,
   `s•c = (s k)•e = (k s)•e = k•(s•e) = k•e = c`, so `s` fixes `O` pointwise. Hence **abelian ⟹ the swap on
   the cell is unique**, which one branch's propagation pins and the linear-oracle harvest consumes
   (cost `≤ n³`, single-path). *So a non-consumed symmetry is `¬D2` = non-abelian.* This is the step with
   **no citation and no WL-dimension content** — the Lean lemmas **L1–L3** (`Group.lean`; see
   [PublicTheoremIndex](../GraphCanonizationProofs/PublicTheoremIndex.md)). The load-bearing form is **L3**
   (`smul_eq_on_orbit_of_comm`): *any two candidates for a decision agree on the whole orbit* — quotient-free,
   needing no faithfulness, so it survives the CFI subtlety that an abelian residual has non-trivial
   *global* stabilizers (flips off the gadget) while being unique *on the cell*.

3. **`¬D1` ⟹ primitive, and ⟹ large.** Imprimitive on `O` ⟹ a block system = a refinement-visible closed
   relation subset ⟹ refinement splits it ⟹ cascades ⟹ `D1`, contradiction. So `¬D1 ⟹ primitive`. And
   `¬D1` = "no harvest window at poly depth" = high WL-dimension = the **large** (super-polynomial-`|Aut|`)
   regime. *(This is the substrate-conditional refinement-side bridge — the deferred piece of §12; it is the
   one non-rigorous link.)*
   **Scoped as Approach A (`Scheme.lean §13`).** Step 3 factors into **(3a) block-visibility** (imprimitive
   ⟹ refinement sees the block ⟹ the cell splits) and **(3b) the quotient/fiber decomposition recursion**
   (unbuilt). **(3a) conditional form LANDED (2026-06-05, axiom-clean):** the predicate
   `BlockRefinementVisible` (quarantining the WL-dimension boundary), its discharge on the orbit-recovery
   class (`blockRefinementVisible_of_edgeGenerates`, widening the `PPolynomial` bridge to `EdgeGenerates`),
   and the reduction `cell_splits_of_imprimitive` (non-trivial closed subset + visibility ⟹ `warmRefine`
   separates two non-`v` vertices = genuine progress). The A2 probe attempts
   `blockRefinementVisible` *off* the recovery class, directly from the `ClosedSubset` closure (which
   mirrors 1-WL counting), since the block is coarser than the orbit — the one realistic shot at closing
   Step 3a unconditionally. (3b) and the A2 probe are the remaining open content of this step.

   **(3b) SCOPING PASS — RESULT (2026-06-05): do NOT build it. It does not de-risk Step 3, and it is not
   needed.** Four grounded findings:
   - **(i) The closed-subset quotient is mathematically cleaner than the orbit-graph quotient — but that
     does not help in Lean.** For a `ClosedSubset I`, the *scheme* quotient `S//I` on the blocks
     (`schemeEquiv I` classes) is **always** a well-defined association scheme (classical; relations = the
     `I`-`I` double cosets), with **no** analogue of the `QuotientAdjCompatible` friction that makes
     `Group.lean §A4`'s orbit-graph `quotientAdj` conditional (well-defined only at discreteness). So the
     lead "block-system quotient avoids the discreteness condition" is **correct** — mathematically.
   - **(ii) But materializing *any* quotient is the already-rejected route, and the scheme quotient is the
     heaviest.** The project faced this exact fork for Tier-3a's `LayerStep` (the §4.2.5 transfer) and
     **explicitly rejected** the materialized quotient (`tier3a-b1-build-plan.md` §4 Approach A: re-typed
     `AdjMatrix m` via `Fintype.equivFin`, "`refineStep` cross-size API gap… high risk, likely
     intractable"), choosing the intrinsic `Fin n` route (Approach B, **landed**: `WitnessUpgrade` /
     `cascadeComposition` / set-monotonicity). A quotient `AssociationScheme` on the block set is
     **strictly heavier** than the rejected orbit-graph quotient: it needs the same `Fin n/~ → Fin m`
     re-indexing **plus** re-establishing all five `AssociationScheme` axioms — including the load-bearing
     `intersectionNumber_well_defined` — via the double-coset homomorphism theorem, with **zero** Mathlib
     substrate (no schemes at all; §4 R5 survey). The cleaner math translates to *more* Lean, not less.
   - **(iii) The intrinsic 3b is gated by the same open content as 3a (Shrikhande-confirmed).** 3b can
     instead telescope individualization sets (a `LayerChain`: resolve the block/quotient structure, then a
     fiber) reusing `cascadeComposition`. But the per-layer **block-transfer** step (a block analogue of
     `LayerStep`) needs block-visibility/recovery at the block layer — exactly the **depth-graded**
     WL-dimension content the A2-iii/Shrikhande result showed is **not free**. So intrinsic 3b lands
     **conditional** on that transfer (mirroring `cascadeComposition`'s conditionality on `LayerStep`), not
     as a closing of Step 3. 3b is **not independently de-riskable** from the A2 open core.
   - **(iv) And 3b is not needed.** The top-down §12 capstone (`exhaustiveObstruction_scheme`) reaches leg
     C modulo the cited classification **without** 3a or 3b — it carries `IsPrimitive`, `IsLargeScheme`, and
     the classification as hypotheses. 3a+3b are the *bottom-up* attempt to **derive** primitive ∧ large
     from `¬D1` — precisely the substrate-conditional content the project routes around.
   **Recommendation:** leave 3b unbuilt. The productive paths are (1) bank the §12 capstone (Tier-3 success,
   modulo cited classification); (2) add a **stated** `non-cascade-at-poly-depth ⟹ IsLargeScheme` bridge so
   the capstone's antecedent is traceable rather than free-floating (cheaper than 3b, avoids the WL-dim
   wall) — **DONE 2026-06-06, axiom-clean** (`Scheme.lean §12.1`: `LargenessBridge` /
   `exhaustiveObstruction_scheme_of_nonCascade` / `exhaustiveObstruction_scheme_nonCascade_trichotomy`; see
   §0.7.5 "stated bridge LANDED"); (3) treat the bottom-up route's value as banked (leg-B citation-free L1–L3 + the "no non-consumed
   abelian species" clarity) — it was never going to close leg C unconditionally (the classification is
   cited either way).

   **A2-i de-risking gate — RESULT (2026-06-05, `Tier2DecompositionExperiment.A2i_BlockVisibility_Probe`):
   INCONCLUSIVE for the hard regime, no counterexample, positive confirmation on examples.**
   *Methodology correction first:* block systems ≡ closed subsets only for a **transitive** `Aut`, so the
   probe is valid only on **vertex-transitive (homogeneous) scheme graphs** — CFI is vertex-*intransitive*
   (subset vs endpoint vertices), and an initial CFI run produced spurious "straddles" (`MinimalBlock`
   merging across intransitive orbits); that run is **retracted**. On the corrected battery (6 VT scheme
   graphs — Petersen, Johnson(5,2)/(6,3), Hamming(2,3)/(3,2)/(2,4); blocks based at `v`, Atkinson minimal
   block): **0 straddles**, and the 2 imprimitive cases (cube `H(3,2)`, Johnson(6,3)) had their block-of-`v`
   **respected** by 1-WL — block-visibility held on every reachable example. *But* all available VT scheme
   graphs are metric/`PPolynomial`, so they **recover at depth 1** (cells = orbits ⊆ blocks); the
   genuinely-uncertain regime — **off-recovery ∧ imprimitive ∧ vertex-transitive** — is **not reachable
   with current generators** (it *is* the WL-dimension boundary). So the gate cannot fire: A2 must go to the
   **A2-iii** proof attempt, or exotic high-WL imprimitive homogeneous schemes must be constructed.
   **Structural lead surfaced for Step 3:** if imprimitive homogeneous schemes *always* have bounded
   WL-dimension (i.e. always recover), then `non-cascade ⟹ primitive` holds outright — a theory question
   worth a pass, and the most promising route to closing Step 3 non-vacuously.

   **A2-i circulant battery — RESULT (2026-06-05, `A2i_Circulant_BlockVisibility_Probe`, INDEPENDENT
   brute-force Aut): no failure case; circulants are too 1-WL-easy to reach the regime.** 18 connected
   circulants (Cayley graphs of `Z_n`, `n ∈ {8,9,10}`, structured connection sets), **all imprimitive**,
   ground-truth `Aut` by brute force (not the canonizer) — **all recovered at depth 1, 0 block-straddles.**
   Circulants have bounded WL-dimension (Muzychuk), so they recover and can't enter the off-recovery
   regime where A2 could fail. Net across both A2-i runs: **every reachable imprimitive vertex-transitive
   scheme (6 metric scheme graphs + 18 circulants) has its block-of-`v` respected by 1-WL — no
   counterexample anywhere, and mounting support for the structural lead.** The genuine failure case (if
   it exists) needs constructions beyond circulants/metric schemes; the leading candidate (CFI) is
   vertex-*intransitive* and thus outside the homogeneous-scheme predicate. **Tentative read: off-recovery
   imprimitive *vertex-transitive* schemes may be rare or nonexistent — i.e. the structural lead may be
   TRUE and Step 3a may hold for homogeneous schemes.** Decisive next move is the **theory pass** on
   "imprimitive homogeneous ⟹ bounded WL-dimension," not more generator-hunting.

   **A2 THEORY PASS — RESULT (2026-06-05): the question was aimed one notch too high; the right target is
   weaker and more likely true.** The A2-i framing ("imprimitive homogeneous ⟹ *recover*") asks for more
   than Step 3a needs. The §13 reduction `cell_splits_of_imprimitive` rests on **`BlockRefinementVisible`**
   (cells ⊆ blocks — 1-WL respects only the *2-way* I/¬I boundary), **not** on full recovery (cells =
   orbits — the whole v-profile separated). On the recovery class the two coincide, which is *why* the gate
   couldn't separate them: 24/24 "recover" only witnessed block-visibility via the strong route; the real
   A2 question (does block-visibility survive *without* recovery) was never exercised.
   - **Full recovery is the wrong target (probably false off the reachable class).** Recovery ⟺ the
     residual coherent configuration is **schurian** (1-WL closure = orbital configuration); `¬D1` ⟺
     **non-schurian** (1-WL strictly coarser than orbits). "Imprimitive homogeneous ⟹ recover" = "no
     imprimitive homogeneous non-schurian high-WL-dimension CC exists" — almost certainly false (high-WL
     *vertex-transitive* structures are known; they are simply not metric/circulant, which is exactly why
     the probe's generators can't reach them). So the structural lead, *as stated*, is likely **false** —
     but Step 3a does not require it.
   - **Block-visibility is the right target — and CFI is evidence *for* it.** CFI itself has **visible
     blocks while recovery fails**: 1-WL separates the gadgets (the blocks) perfectly; it cannot resolve
     the *parity within* a gadget. So CFI is a direct witness that A2's weaker property *survives into the
     off-recovery regime where the strong one dies.* The structural reason to expect this generally: a
     `ClosedSubset I` is closed under the **complex product** — *the same counting operation 1-WL
     implements* — so the coarse I-boundary is "1-WL-closed by construction" in a way the fine orbit
     structure is not.
   - **The reframe.** Step 3 reads cleanly as `¬D1` (non-schurian residual) ⟹ *block-visible* ⟹ cell
     splits ⟹ recurse on quotient/fiber ⟹ bottom out at a **primitive** `¬D1` piece = Cameron (Step 5).
     CFI fits: visible gadget-blocks let the recursion proceed; the irreducible parity sits at the
     primitive base. No "imprimitive ⟹ recover" anywhere.
   - **The one remaining risk, now sharp.** Block-visibility fails iff a closed subset `I` is
     **counting-symmetric** from `v` — `I` and `¬I` carry identical intersection-number signatures, so
     1-WL cannot separate even the coarse boundary. That is a *strictly rarer and stranger* object than a
     high-WL-dimension scheme (it needs the **coarse block** invisible, not just the fine structure). So
     the empirical gate's "can't fire" is itself informative: A2's true obstruction is not "high-WL," it
     is "coarse-block-invisible," which is far more constrained.
   - **Redirect.** Drop "imprimitive ⟹ recover"; target `BlockRefinementVisible` for every `ClosedSubset`
     **directly** (A2-iii), via the closed-subset-closure ↔ 1-WL-counting induction (reuse
     `RelIsolatedAt`/`isolatedCount_eq` applied to the **set `I`**, not singletons). The gating sub-question
     is small and decisive: *can a closed subset be counting-symmetric from `v`?* If closure forbids it →
     A2-iii closes Step 3a unconditionally; if not → that scheme is the exact object to build. **Moderate
     optimism A2-iii closes**, pessimism only on the narrow counting-symmetric escape. Scratch plan:
     [`chain-descent-a2iii-plan.md`](./chain-descent-a2iii-plan.md) (short-lived; this block is the durable
     record).

   **A2 status — the three sub-approaches and where each stands (durable handoff record, 2026-06-05).**
   The A2 effort (discharge `BlockRefinementVisible` off the recovery class) split into three:
   - **A2-i — empirical de-risking gate. DONE, exhausted.** 24/24 reachable imprimitive VT schemes (6
     metric + 18 circulants) respect the block-of-`v`; the off-recovery regime is unreachable with current
     generators (CFI is intransitive; circulants/metric recover). No counterexample, gate can't fire.
   - **A2-ii — graded discharge. LANDED (axiom-clean, `Scheme.lean §13`).** `SchemePartSeparatesBlock`
     (predicate: the depth-`n` counting partition `schemePart_at` separates the I-boundary) +
     `blockRefinementVisible_of_schemePartSeparates` (discharge via `iter_refines_schemePart_at` —
     warmRefine is finer than `schemePart_at`). **Strictly wider than `blockRefinementVisible_of_edgeGenerates`**
     (holds off the full-recovery class, whenever the WL-fusion `W` respects the I-boundary). This is the
     honest graded form and it quarantines the open content into one named predicate.
   - **A2-iii — unconditional discharge. RESOLVED NEGATIVELY (2026-06-05): unconditional A2-iii is FALSE.**
     The twin-pair search (`TwinPairSearchExperiment.cs`, graph-first / Aut-faithful — see the RESULT block
     below) found a clean, verified witness: the **Shrikhande graph**. So `SchemePartSeparatesBlock` does
     **not** hold for every `ClosedSubset`, and `BlockRefinementVisible` is **not** dischargeable at
     single-vertex depth. **Do not pursue a Lean proof of unconditional A2-iii — it is refuted.** The honest
     shape is the graded **A2-ii** form (`blockRefinementVisible_of_schemePartSeparates`), with block-visibility
     re-cast as **depth-graded** (holds after ≥ the WL-dimension's depth of individualization, not at depth 1).

   **A2-iii RESULT — Shrikhande refutes unconditional block-visibility (2026-06-05, axiom-free C# verification).**
   The graph-first, Aut-faithful search (`TwinPairSearchExperiment.cs`; `Verify_Shrikhande_BlockInvisible`,
   `|Aut|` cross-checked against the known 192 / 1152) settles the twin-pair question — **negatively**:
   - **Witness:** the **Shrikhande graph** (SRG(16,6,2,2), `|Aut| = 192`). Its *own* orbital scheme is
     **rank 4** (valencies `[1,6,3,6]`) — finer than the rank-2 SRG, because `Aut` is **not** rank-3. It has
     exactly one non-trivial `ClosedSubset`, `I = {R₀, R₂}`, a **genuine block system (4 blocks of 4)**.
     1-WL-from-`v` gives only **3 cells** (the SRG partition `{self, 6 nbrs, 9 non-nbrs}`) vs **4** orbital
     classes — so it is **blind to the block** (it merges an `R₂`-vertex *in* the block with an `R₃`-vertex
     *out* of it). Contrast control: the **rook graph** `K₄□K₄` (same SRG parameters, but rank-3 `Aut`,
     `|Aut| = 1152`) is **primitive** (no closed subset) and **recovers** — the two SRG(16,6,2,2) graphs
     behave oppositely.
   - **The doc's "counting-twin" mechanism was too narrow.** The merged relations `R₂` (valency 3) and `R₃`
     (valency 6) are **not** global intersection-twins. The real obstruction is **single-vertex WL-dimension
     ≥ 2**, which merges even non-twin relations from one basepoint — weaker (so more common) than "identical
     intersection numbers." Replace "counting-twin split by `I`" with "1-WL-from-`v` cannot separate the
     `I`-boundary on a WL-dim-≥-2 schurian scheme."
   - **KEY NUANCE — a Gate-G failure is NOT an `(O*)`-existence witness (correcting the doc's binary).**
     Shrikhande is **recoverable** (it discretizes at **depth 2** — `D1`, small WL-dimension), *not* a wall
     case. So "block invisible at depth 1" ⇏ "`(O*)`-existence / hard." The earlier framing ("if a
     twin-splitting closed subset exists → that scheme is the exact `(O*)` witness") was wrong: the witness
     is a *depth-2-recoverable* graph, not a hard residual.
   - **Net redirect.** A2-iii (unconditional, single-vertex) is **dead**. Block-visibility collapses back
     into the **substrate-conditional WL-dimension / depth-witness boundary** ("B's core") that the rest of
     the project already flags as the honest open boundary — it is *not* a separable closable theorem. The
     Lean `cell_splits_of_imprimitive` keeping `BlockRefinementVisible` as a **hypothesis** is **vindicated**
     (correctly conditional). For closing Step 3, route via the **top-down §12 capstone** (which needs no
     A2-iii) or a **depth-graded** block-visibility tied to `RecoverableByDepth`.

   **Gate-G pass findings (2026-06-05) — a trap, the reduction, and a methodology lesson.** (i) **Guardrail:**
   `ClosedSubset` is the *complex-product* closure; `EdgeGenerates`/`isolationStep` is the *pinning* closure —
   **different**. Do not argue "off-recovery ⟹ edge-closure `J*` is a proper closed subset ⟹ imprimitive":
   `J*` is the pinning closure, not a `ClosedSubset`, so off-recovery does **not** imply imprimitive (primitive
   schemes can fail `EdgeGenerates` — the Cameron/Johnson case), and Step 3's direction is unthreatened.
   (ii) **The reduction:** `schemePart_at` converges from `v` to the WL-fusion `W`, so block-visibility ⟸
   "`schemePart_at` separates I" ⟸ "`I` respects `W`". (iii) **Methodology lesson (the same trap A2-i hit):**
   the search MUST use the orbital scheme of the graph's *own* `Aut`, never an a-priori group scheme paired
   with a non-generating single relation — a first cut (Z₈ scheme + antipodal matching, whose real `Aut` is
   `S₂≀S₄ ⊋ Z₈`) produced **43 spurious straddles**, all artifacts of invalid `(scheme, graph)` pairs. The
   graph-first form (compute `Aut(G)`, use its orbital scheme so `(G, S_G)` is schurian by construction) is
   the faithful test; the Shrikhande witness survives it.

4. **Large + primitive ⟹ non-abelian, automatically.** A *primitive abelian* group is `Z_p` (order =
   degree = polynomial), hence **not** large. So a large primitive group is non-abelian — the same fact
   Step 2 gave from candidate-counting, now from the order side. **Lean (axiom-clean, `Group.lean`):**
   `card_eq_of_isPretransitive_comm` (transitive faithful abelian ⟹ `Nat.card G = Nat.card α`, via the
   bijection `g ↦ g•a`) and the headline `not_comm_of_isPreprimitive_card_lt` (`Nat.card α < Nat.card G`
   + preprimitive faithful ⟹ non-abelian). So **Steps 2 *and* 4 are now formalized**; only Step 3
   (`¬D1 ⟹ primitive`, the deferred refinement-side bridge) remains non-rigorous.

**Conclusion.** `non-consumed ⟹ ¬D1 ∧ ¬D2 ⟹ large primitive non-abelian action on a WL-stable cell =
a Cameron section`. The chain has **no slot for a non-consumed abelian symmetry** (Step 2 forecloses it
rigorously). This is exactly bucket C of §0.5 — so "a non-consumed symmetry exists" **is** the
`(O*)`-existence question (GI-hard), and the graph must carry a *hidden* Johnson/Hamming-type scheme.

### 0.7.3 Why the two routes agree — and what each owns

`non-consumed ⟺ ¬D1 ∧ ¬D2 ⟺ large primitive non-abelian ⟺ Cameron`. The **top-down** capstone (§12)
reaches the final `⟺` by citing the classification; the **bottom-up** derivation reaches it by candidate
counting (Step 2) + `large primitive ⟹ non-abelian` (Step 4). The split of labour:

| Leg | Statement | Route | Lean status |
|---|---|---|---|
| **A** (D1) | recovers at poly depth ⟹ consumed | orbit recovery | proved (witnesses; `theorem_2_HOR_of_pPolynomial`, …) |
| **B** (¬D1∧D2) | **abelian ⟹ unique candidate ⟹ consumed** | **bottom-up (L1–L3)** | **provable, citation-free** |
| **C** (¬D1∧¬D2) | large primitive non-abelian ⟹ Cameron | top-down (§12) | stated modulo cited `PrimitiveCCClassification` |

So the bottom-up route is **leg B's clean proof core**, complementing — not replacing — leg C's cited
capstone. Merging them: the seal = A (recovery) ∨ B (L1–L3) ∨ C (§12).

### 0.7.4 The high-tw CFI resolution (effectiveness ≠ species)

Step 2 settles a tension recorded elsewhere. CFI's gauge is `Z₂^β` (abelian), so by L3 every gauge
decision is a *locally unique* swap, consumable single-path at `tw·n² ≤ n³` ([cascade-oracle §4.6](./chain-descent-cascade-oracle.md)).
There is therefore **no "non-consumed abelian" species**, even at unbounded treewidth. High-tw CFI under
the *branching* a-posteriori oracle costs `cell_size^{tw}` (flags); under the *single-path* a-priori
oracle it is `O(n³)` (poly) — and L3 *guarantees the poly one exists*. So the §0.6 F2 / §2 gap-(B)
"flagged region" for high-tw CFI is a **mechanism-effectiveness** question (does the built oracle realize
the single-path harvest), **not** a third mathematical flag species. This **corrects an earlier reading**
that treated unbounded-WL-dimension as a distinct escape in guarantee 2: there are exactly two symmetric
outcomes — *consumed* or *Cameron* — plus the orthogonal IR-core (no symmetry).

> **Drafting consequence.** Guarantee 2's escapes are **Cameron** (non-trivial non-abelian residual) and
> **IR-core** (trivial residual); an *unconsumed abelian* residual (high-tw CFI) is **not** a third escape
> — it is a consumed-in-principle case whose poly harvest is an *effectiveness* obligation, falsifiable by
> the `AbelianUnconsumed` e2e probe (which thereby tests single-path effectiveness, not a species).

### 0.7.5 Deriving the *largeness* antecedent — the no-fusion / deferral route (2026-06-06)

> **The active route to *deriving* leg C's largeness antecedent instead of hypothesizing it.** Full plan:
> [`chain-descent-fusion-battery-plan.md`](./chain-descent-fusion-battery-plan.md).

The §12 capstone `exhaustiveObstruction_scheme` carries **largeness** (`IsLargeScheme`) as a free hypothesis.
This route derives it from what the descent observes, via a chain that bottoms out on **already-landed**
machinery:

`leg C ⟹ large` ⟸ `small ⟹ consumed` (contrapositive) ⟸ **completeness of deferral** (deferring all real
decisions, the harvest finds every symmetry before any real is forced) ⟸ **no fusion** (no symmetry is
1-WL-entangled — sharing cells — with rigid / genuine-decision structure so as to gate its recovery on a real
decision).

- **`real_stays_real` = soundness of deferral** (a deferred real stays real). The **open** part is
  *completeness*; the exact gap is **"uncertifiable ≠ real"** — an uncertifiable cell can hide a symmetry
  (high WL-dimension), and the **multipede** witnesses small/trivial-`|Aut|` + high-WL, so no-fusion is
  **substrate-conditional** (a witness, not a free theorem).
- **The payoff lemma (PP3), on landed machinery:** by `card_autP_eq_prod_of_base` (Part A),
  `|Aut| = ∏ basic-orbit sizes` along the recovery base sequence; under no-fusion the consumption path is
  symmetry-only, so its cost **is** that product — hence **`¬D1 ∧ NoFusion ⟹ ∏ orbit-sizes super-poly ⟹
  |Aut|` super-poly = large.** No Babai needed for this step. (The multipede escapes: no symmetry-only path,
  cost is all real decisions — it is the IR-core, not large.)
- **Status:** the separable case is provable (`forcedNode`/`movedSet` + `recoverableAt_base_iff_discrete` +
  Tier-0); the entangled case is carried as the **`NoFusion` witness**, validated by an adversarial battery
  (defer-all-reals harvest vs brute-force `Aut`; decisive signal = harvest `⊊ Aut` while `|Aut|` **small** =
  fusion leak). Endpoint: "leg C ⟹ Cameron" modulo (cited Babai classification + `NoFusion` witness + the
  *separate* primitivity witness), with **largeness derived**. Primitivity remains its own depth-graded line
  (§0.7.2 Step 3 / Shrikhande), not part of this route.
- **The stated bridge LANDED (2026-06-06, axiom-clean, `Scheme.lean §12.1`).** Ahead of the battery, the
  capstone's largeness antecedent is now *traceable*, not free-floating: `LargenessBridge` (`∀ m S,
  NonCascade m S → IsLargeScheme m S`, a named `Prop` mirroring `PrimitiveCCClassification`),
  `exhaustiveObstruction_scheme_of_nonCascade` (the capstone reached *through* the descent's `NonCascade`
  observation + the bridge), and `exhaustiveObstruction_scheme_nonCascade_trichotomy` (`¬IsPrimitive ∨
  ¬NonCascade ∨ Cameron` — the disjunction in the descent's own observable). The bridge is **stated, not
  proved** (the genuine derivation = PP3, needs the `NoFusion` witness) and is the single named input the
  battery validates. **Caveat baked into the doc-comment:** `non-cascade ⟹ large` is false in general (the
  multipede is non-cascade + trivial `Aut`), but the multipede is *rigid* hence not a `SchurianScheme`
  (schurian ⟹ vertex-transitive), so the bridge is sound to *state* on the scheme-residual class; the
  residual content (a *primitive small* non-cascading scheme) is the WL-dimension boundary — why it stays a
  hypothesis. This realizes §0.7.2 (3b) recommendation item (2).
- **PP1 + PP3 + PP2-core LANDED (2026-06-06, axiom-clean, `Cascade.lean` Part A).** `NoFusion` (PP1, the
  orbit-realizer coverage — the symmetry-only harvest reproduces every orbit, **no recovery hypothesis**);
  `reproducesResidual_of_noFusion` / `autP_reproduced_of_noFusion` (PP3 — `NoFusion` ⟹ `closure = Aut^P ∧ |·| =
  ∏ orbit-sizes` via the landed order identity, largeness *read off the harvest*, no Babai/no WL-dim);
  `noFusion_of_visibleRecovery` (PP2 provable core — recovery ⟹ no fusion). PP3 reworded honestly: the order
  identity is unconditional, `NoFusion` makes the product the *harvest's* output ⟹ largeness derived-from-witness.
- **THE NO-FUSION BATTERY RAN — all 3 tiers, decisive (2026-06-06, `FusionBatteryExperiment.cs`, 17/17 green).**
  Recovery-only harvest (`ChainDescent.RecoveryOnly`, the rigid-residue hand-off) vs brute-force `Aut`, triaged
  by an **orbit-partition** comparison + a **decomposability** probe. **Result: no genuine fusion is
  constructible.** Tier-1 cascading Cameron ⇒ harvest = `Aut`; Tier-2 products (tensor/lex) ⇒ harvest = `Aut`
  (products don't fuse); Tier-3 CFI gauge ⇒ consumed (abelian, §0.7.4). The decisive Tier-3 datum: a non-abelian
  `S₃` over **label-aligned** IR-core multipede copies is **consumed** (construct-and-check certifies the swap
  directly), while over **label-scrambled** copies it is **missed** — but that miss is **decomposable**
  (disconnected), i.e. the **separable / Tier-0** case, *not* a genuine connected fusion. **Two proof-relevant
  sharpenings (now folded into the plan §1/§2):** (i) consumption is **candidate-pinning (recovery), orthogonal
  to abelian-ness** — `small ⟹ consumed` is really `small ⟹ recovery pins the candidate`, failing only on
  WL-resistant matching of *separable* IR-core blocks; (ii) "fusion" **splits** into separable (PP2 / Tier-0-
  provable, where *all* constructible hidden non-abelian symmetry lives) vs non-decomposable (empirically
  unwitnessable = a genuine **Cameron** section, no third species). So `NoFusion`'s open content collapses onto
  **non-decomposable ∧ recovery-resistant ∧ has-symmetry = genuine Cameron** — the cited boundary, now
  empirically backed, with no room left for a non-abelian fusion species. Full record: the plan §5/§6/§7.
- **LARGENESS BRIDGE DISCHARGED modulo `NoFusion` — LANDED (2026-06-06, axiom-clean, `Cascade.lean` Part A).**
  The stated `LargenessBridge` is now a **proved theorem** for concrete descent-observable predicates, no longer
  a carried hypothesis. Two layers: (1) the **class-agnostic graph core** `isLargeAutP_of_noFusion` (+ the
  unconditional order-transport `isLargeAutP_of_isLargeProd`) — under `NoFusion` the symmetry-only harvest
  reproduces `Aut(G)^P` exactly, so largeness *observed on the harvest's own output* (`closure gens`) certifies
  the true group's largeness, on bare `AdjMatrix`, no scheme structure, with `IsLarge : Nat → Prop` the abstract
  super-poly citation (never concretized); (2) the **scheme discharge** — `schemeAdj` faithfully encodes a scheme
  as a labelled graph (`isAut_schemeAdj_iff`: `IsAut`=`IsSchemeAut`), `stabilizerAt_schemeAdj_empty_eq` identifies
  `StabilizerAt (schemeAdj S) ⊥ ∅ = SchemeAutGroup S`, and `largenessBridge_viaHarvest` proves `LargenessBridge
  (NonCascadeViaHarvest IsLarge) (IsLargeSchemeViaAut IsLarge)`. The capstone `exhaustiveObstruction_scheme_of_harvest`
  then reaches the §12 Cameron conclusion with the bridge **supplied, not carried** — modulo only the cited
  `PrimitiveCCClassification` and the explicit, battery-validated `NoFusion` antecedent (folded inside
  `NonCascadeViaHarvest`). PP3's reword realized in Lean: the order identity is unconditional; `NoFusion` makes the
  orbit product the *harvest's* output, so largeness is **derived from the witness**, the substrate-conditional
  content sitting as an explicit antecedent rather than a free-floating implication.
- **PP2 SEPARABLE-DECOMPOSITION LEMMA LANDED (2026-06-06, axiom-clean, `Cascade.lean` Part A).**
  `noFusion_of_warmSeparatedPartition`: `NoFusion` decomposes along a **1-WL-separated** partition into per-block
  coverage (orbits refine cells ⟹ no orbit crosses a block, via `OrbitPartition.subset_warmRefine`). The honest
  divide-and-conquer for the **non-isomorphic** separable case — the distinguishing witness `hsep` (parts told
  apart by 1-WL) + per-component recursion `hcov`. Strictly more general than `noFusion_of_visibleRecovery` on the
  separation axis. The **isomorphic-copy / swap** case (blocks 1-WL-indistinguishable) is correctly excluded —
  it routes through recovery + the sort-key gap (strategy §15 gap 4), the substrate-conditional remainder; the
  full disjoint-union construction with the wreath swap stays deferred.

---

## 1. Statement of the lemma (mechanism-pinned)

Informal target:

> **Exhaustive-Obstruction Lemma (EOL).** Let `Aut_S` be the residual
> stabilizer at a descent node, acting on a non-singleton 1-WL cell `C` after
> all cascade and abelian structure has been consumed. Then the action of
> `Aut_S` on `C` is one of:
> 1. **cascade-recoverable** — individualizing one representative and refining
>    collapses `C` to single-orbit cells within the oracle's depth bound; or
> 2. **a hidden elementary-abelian twist** — a `Z₂^d` (more generally abelian)
>    action with a unique candidate readable off one branch (linear oracle); or
> 3. **a Cameron section** — the action contains `A_k`-on-`k`-subsets (Johnson,
>    the leading case) or a product/partition action of a Cameron group.
>
> Contrapositive (= the user's hypothesis): **there is no non-cascade,
> non-abelian, non-Cameron symmetric obstruction.**

> **Terminology — disambiguation (read once).** "Cameron" here means **Cameron's
> theorem on large primitive permutation groups** (P. J. Cameron, 1981; sharpened
> by Maróti) — *not* "the Cameron graph" (the strongly regular graph on 231
> vertices tied to M₂₂ / the Steiner system S(3,6,22)), which is an unrelated
> single object. A **Cameron group** is a primitive group sandwiched
> `(A_m)^d ◁ G ≤ S_m ≀ S_d` acting in **product action** on `d`-tuples of
> `k`-subsets of `[m]` (degree `n = C(m,k)^d`). The `d = 1` case is `S_m`/`A_m` on
> `k`-subsets = **the Johnson group** (the project's "hidden Johnson"). A **Cameron
> section** = a subquotient of the residual that is such a group. The class is
> **richly constructed and fully classified** (Johnson/Hamming/Grassmann schemes,
> `A_m`-on-subsets, product actions) — the *opposite* of "no known constructions";
> that abundance + classification is exactly what makes leg C conclude. Same usage
> as [hidden-johnson §7](./chain-descent-hidden-johnson.md) ("O'Nan–Scott +
> Cameron/Maróti").

**Why "Cameron section," not "Johnson section" (a correction to fold back).**
Cameron's classification yields `A_k`-on-subsets (Johnson, `d=1`) **and** product
actions (`d>1`) and a small list of exceptions. The docs say "Johnson" as
shorthand; the *honest* obstruction class is **Cameron**. Strict "Johnson-only" is
**too narrow** — a product-action Cameron group would be a genuine instance of the
user's "fourth species" (non-cascade, non-abelian, **not strictly Johnson**) that
is nonetheless still *classified and flaggable*. Naming the target as **Cameron**
is what makes the hypothesis actually true rather than narrowly false. (See §6
refutation R3.)

**Why "mechanism-pinned" is load-bearing.** If "cascade-class" is *defined* as
"whatever refinement + individualization can reach," then disjunct 1 is true by
definition, the lemma is vacuous, and all content silently migrates into the
wall. The lemma is only falsifiable if disjunct 1 is **the built oracle's
concrete bounded-depth recursion** (cascade-oracle.md §4.4) — i.e. "cascade-
recoverable" means *the shipped mechanism certifies it*, not "is in principle
exposable." This pins the genuine residual risk where it lives (§2, gap B).

---

## 2. The two sub-gaps (they need different tools)

The hypothesis decomposes into two logically independent pieces. Conflating
*these* is the second trap (after the existence/classification conflation).

- **(A) The mathematical fourth-species gap.** Does a non-cascade ∧
  non-abelian ∧ non-Cameron symmetry exist *in the abstract*? Theory says
  **no**: O'Nan–Scott (primitive groups are a short list of types) + Cameron
  (the *large* primitive ones are Cameron groups). This is the disjunct-3 side.
  **Cameron-hard, not GI-hard.** Tractable *modulo citing the classification*.
- **(B) The mechanism-completeness gap.** Even granting (A), a symmetry that is
  abstractly cascade-/abelian-class may be **missed by the built oracle**
  (recursion stops too early; unique-candidate read fails; depth bound too
  small). This would surface as a **false flag with non-trivial residual that
  is *not* a true Cameron group** — the dangerous one for "never-flag-except-
  Johnson." (B) is *not* a classification question; it is **oracle vs. ideal**,
  and is checked empirically / by the C#→Lean faithfulness translation (lowest
  priority, separate track). **The mechanism-pinning of §1 is what makes (B) a
  statable object at all.**

This plan targets **(A)** as the formal item; **(B)** is scoped, named, and
handed to the empirical/translation track.

---

## 3. What supports the hypothesis (evidence already in the project)

1. **The theory is already cited and is a real classification, not a hope.**
   [hidden-johnson §7](./chain-descent-hidden-johnson.md): "non-trivial residual
   ⟹ Johnson section" is "the graph-isomorphism-flavored shadow of O'Nan–Scott +
   Cameron." The structural backbone for (A) is named and standard.
2. **The "non-cascade ⟹ primitive" half is already articulated.**
   [hidden-johnson §1](./chain-descent-hidden-johnson.md): Johnson "does not
   cascade — the scheme is *primitive*, no invariant partition to refine into."
   The contrapositive — **imprimitive ⟹ has a block system ⟹ refinement splits
   it ⟹ cascades** — is the (B2) bridge below, and it is the *natural* direction
   (1-WL detects equitable partitions; a block system is equitable).
3. **The two-axis map isolates the exact corner.**
   [calculator §3](./chain-descent-calculator.md) / [tier3 §2](./chain-descent-tier3-decomposability.md):
   "cascading is orthogonal to the group; only the **non-cascade, non-abelian**
   corner is hard." The lemma is a statement about precisely one quadrant — the
   framing is already crisp and agreed.
4. **`real_stays_real` / `OrbitPartition.mono` (proved, Lean).** Stabilizer
   monotonicity under individualization — the substrate fact that the residual
   *shrinks* down the descent, which any "what's left at the bottom" argument
   needs. Already axiom-light.
5. **The group object now exists (Part A, `ChainDescent.Group`).** `AutGroup`,
   the vertex `MulAction`, `OrbitPartition`, `LayerChain` — so *primitivity*,
   *block systems*, and *Cameron section* are now **stateable in Lean** (they
   were not before Part A). This is the enabling infrastructure.
6. **The Tier-2 scheme machinery is a Cameron-free beachhead.** The WL-stable
   partition of a cell **is a coherent configuration / association scheme**; the
   project already reasons about these (`IsSchurianSchemeGraph'` — the concrete
   structure that replaced the retired placeholder axiom — `RelIsolatedAt`,
   the depth-1/2/3 isolation bootstrap). On schemes the obstruction classifies
   via *rank / coherent-algebra* arguments (Higman/Hanaki-style) **without**
   importing Cameron — a place to prove a restricted EOL outright (Approach 3).
7. **Empirically, no fourth species has ever appeared.** Through CFI(K7),
   Petersen, Rook3×3, K6 — every residual the C# hit was cascade, abelian, or a
   clean flag. Weak evidence (small `n`), but consistent.

---

## 4. What complicates or could refute it (look here first)

Listed as concrete refutation angles, strongest first — the plan's de-risking
gate (§5 step 2) is built to hit these.

- **R1 — "Johnson" is too narrow (product actions).** Cameron groups ⊋ Johnson.
  A residual in **product action** (`A_k^d`) is non-cascade, non-abelian, and
  **not** a single Johnson scheme. If the program's flag/handler is keyed to
  "Johnson" strictly, this is a *genuine* unnamed-gap instance. **Mitigation:**
  state the lemma with **Cameron** as the obstruction class (§1). This converts
  R1 from a refutation into a scoping correction — but only if acted on.
- **R2 — primitivity ≠ cascade (the bridge is not free).** "Non-cascade ⟹
  primitive" needs: (i) imprimitive ⟹ block system, *and* (ii) 1-WL/refinement
  actually *finds* that block system within the oracle's mechanism (gap B
  creeping in). (ii) is true for *equitable* partitions, and block systems are
  equitable — but "the **built** recursion reaches it at its depth bound" is the
  mechanism claim, not the abstract one. **This bridge is where (A) and (B)
  touch**; keep them separate or the lemma quietly becomes vacuous.
- **R3 — base size vs. cascade depth.** "Cascade in *bounded* depth" is stronger
  than "discretizes eventually." A small-but-positive-base primitive group (e.g.
  `PSL(2,q)` on the line, base ~3) cascades only if the oracle's depth bound
  ≥ its base. If a non-Cameron primitive group has base growing slowly but
  faster than the bound, it is *abstractly* cascade-class yet *mechanically*
  flagged — again a gap-B fourth species. **The depth bound is part of the
  hypothesis, not a free parameter.**
- **R4 — the docs' own conflation as inertia. (RESOLVED 2026-06-02.)** Earlier
  framings collapsed all of (O\*) into "no Lean obligation, the boundary," and
  R4 cited a "strategy gap 7" that never existed (the real flagged-region text is
  [strategy §15 gap 5](./chain-descent-strategy.md)). The Approach-0 disentangle
  has now been written into strategy §15 gap 5, calculator §3/§6/§7/§9,
  tier3-decomposability §0/§6/§8.1, and hidden-johnson §7 — the classification
  half is recorded everywhere as **Cameron-hard, not GI-hard, a finite target**.
  The item now has a sanctioned home; R4 is no longer a blocker.
- **R5 — Cameron/O'Nan–Scott are not in Mathlib (but the primitivity layer IS).**
  **Verified against the pinned Mathlib** (`.lake/packages/mathlib`, 2026-05-31):
  - *Present and directly usable* — `Mathlib/GroupTheory/GroupAction/Primitive.lean`
    (`IsPreprimitive`), `…/Blocks.lean` (`IsBlock`, block systems),
    `…/MultiplePrimitivity.lean`, `…/Jordan.lean` (**Jordan's theorem** — a
    primitive group with a small-support element is `≥ A_n`; a *partial
    Cameron-direction tool*), `…/MultipleTransitivity.lean`,
    `GroupTheory/Perm/MaximalSubgroups.lean`,
    `SpecificGroups/Alternating/MaximalSubgroups.lean`. This is **more than enough
    to formalize the (B1)/(B2) primitivity bridges** and is a stronger starting
    base than assumed.
  - *Absent* — no O'Nan–Scott, no Cameron/Maróti (confirmed: only stray "cameron"
    string matches in the maximal-subgroup files, no theorem).
  So (A) cannot be fully formalized from Mathlib; it must **cite** the
  classification as a clearly-marked hypothesis (Approach 1) — but the *bridges*
  around the citation are well-supported, and Jordan's theorem may let a
  **restricted** EOL (e.g. "primitive of small base ⟹ `A_k`-ish") be proved
  Cameron-*free* further than expected. A from-scratch Mathlib proof of full
  Cameron is out of scope (years of work).
  - **Scheme-side survey (2026-06-05) — the Approach-3 capstone is *also* uncited
    in Mathlib.** Re-ran the survey against the pinned Mathlib for the
    coherent-configuration / scheme classification Approach 3 would cite: **wholly
    absent** — no `AssociationScheme`, coherent configuration, Bose–Mesner algebra,
    distance-regular graph, or scheme spectral theory (eigenvalue/multiplicity,
    Krein/absolute bounds); the project's `AssociationScheme` in `Scheme.lean` is
    home-grown and carries only `rank`/`intersectionNumber`/`relOfPair`, no spectral
    layer. The capstone's classical content — *primitive coherent configuration of
    rank ≥ 3 with super-polynomial Aut ⟹ Cameron (Johnson/Hamming)* — is **Babai
    (1981) / Sun–Wilmes (2015)**, a deep combinatorial theorem with no Mathlib
    substrate. **Consequence:** Approach 3's capstone is *not* lighter to formalize
    than Approach 1's; it too must enter as a **named cited hypothesis**
    (`PrimitiveCCClassification`). What *is* well-supported (and what the landed
    bridge uses) is the primitive-group action layer above. The deliverable,
    fully-axiom-clean part of Approach 3 is the **bridge + decomposition conclusion**,
    not the capstone.

---

## 5. Approaches (multiple) and the recommended path

Four approaches; they are **complementary stages**, not alternatives. Recommended
order: **0 → 2 → (1 ∥ 3)**.

### Approach 0 — Disentangle (documentation; prerequisite, cheap) — **DONE 2026-06-02**
Split (O\*)-existence from (O\*)-classification across hidden-johnson.md,
tier3-decomposability.md, strategy §15, calculator §9. Downgrade the
classification half from "= GI ∈ P / no Lean obligation" to "**Cameron-hard, not
GI-hard; a finite formal target** (this doc)." Add **Cameron** (not just Johnson)
as the obstruction class. *No Lean.* **This is a true prerequisite** — without it
the item has no sanctioned status (R4) and the Johnson/Cameron scope (R1) stays
wrong. ~half a day.

> **Executed (2026-06-02).** The split is now written into: strategy §15 gap 5
> (existence = GI∈P vs classification = EOL, Cameron-hard); calculator §3 wall
> bullet + §6 boundary + §7 box + §9 gap 5; tier3-decomposability §0 scope note +
> §6 + §8.1 (with `S(J)` linked to this doc's leg-C fingerprint); and the new
> **hidden-johnson §7** carrying the O'Nan–Scott + Cameron/Maróti grounding (the
> note §0 above had previously *cited as if it already existed*). "Cameron, not
> Johnson" (R1) is recorded at each site.

### Approach 2 — Empirical falsification harness (de-risking gate; do before formal investment)
Before formalizing, **try to break it.** Enumerate primitive groups up to some
order (GAP's primitive-groups library, or a nauty/`bliss`-driven sweep of
small vertex-transitive graphs), and for each non-cascade, non-abelian one check:
does it contain a Cameron section? Equivalently, run the **built C# oracle** on a
battery of primitive-group graphs (Johnson `J(n,2..3)`, Hamming, Grassmann,
product actions, `PSL`/`PSU` actions, sporadic primitives) and classify every
flag by residual-group structure. **Outputs:** either (a) a counterexample — a
non-cascade-non-abelian-non-Cameron residual, which *refutes* the hypothesis and
is enormously informative; or (b) growing confidence + a concrete list of the
*shapes* disjunct 3 must cover (informs the formal statement). This is the
**single highest-information, lowest-cost step** and directly honours "this is a
hypothesis." ~1–2 weeks; reuses the C# harness.

### Approach 1 — Cite-Cameron bridge (the primary formal target)
Do **not** reprove Cameron. Formalize the *project-specific bridges* and cite the
classification:
- **(B1)** non-cascade (mechanism-pinned) ⟹ the residual action on `C` is
  **primitive with base exceeding the depth bound** (uses Mathlib `IsBlock` for
  the imprimitive ⟹ cascade contrapositive; this is the genuinely new Lean
  content).
- **(Cameron, cited)** primitive + large base ⟹ Cameron group — stated as a
  **named hypothesis** `CameronClassification`, with a doc note that it is a *true
  theorem in the literature*, not a project conjecture. **NB (2026-06-05):** the
  project is now **free of custom axioms** (the former `IsSchurianSchemeGraph` /
  `schurian_scheme_profile_exists` / `cfi_cascades_polynomially` placeholders were
  retired once their concrete replacements landed). So `CameronClassification`
  would be the *first* re-introduced cited hypothesis; prefer a hypothesis carried
  on the theorem statement (an explicit argument) over a fresh `axiom`, to keep the
  axiom basis clean and the citation visible at every use site. The same applies to
  Approach 3's `PrimitiveCCClassification` (Babai/Sun–Wilmes; see §5 Approach 3).
- **(B2)** a Cameron group's natural action on the cell ⟹ the EOL disjunct 3
  (it *is* the flagged obstruction); plus disjuncts 1/2 for the small/abelian
  cases.
**Deliverable:** EOL proved **modulo `CameronClassification`**, with the new
content (B1, B2) axiom-clean. This isolates the imported math from the project
math — the honest, attainable shape. Effort: medium-large (primitivity bridges
are real work); risk: the (B1) base-bound bridge is where R2/R3 bite.

### Approach 3 — Cameron-free restricted proof (parallel beachhead)
Prove the EOL **outright, no Cameron**, on the restricted class where the residual
is a **coherent configuration / association scheme** (the Tier-2 territory the
project already formalizes). Here "non-cascade ∧ non-abelian" classifies via
**rank / coherent-algebra** arguments (a high-rank primitive scheme with no
abelian regular subgroup is Johnson/Hamming-type by scheme theory) without the
full primitive-group classification. **Deliverable:** a fully axiom-clean EOL on
schemes — the *first concrete instance*, and the analogue of how Tier-2 proved
schemes before the abstract route. Builds directly on `Scheme.lean` +
`RelIsolatedAt`. Lower ceiling, no Cameron dependency, fully checkable. Good as
the **proof-of-concept that the lemma is even true** in a real sub-case.

> **Scope correction (2026-06-05) — what "Cameron-free" buys, precisely.** The
> capstone classification *primitive scheme of rank ≥ 3 with no abelian regular
> subgroup ⟹ Johnson/Hamming* is **Babai (1981) / Sun–Wilmes (2015)** on primitive
> coherent configurations, and Mathlib has **no** scheme/CC substrate (no
> association schemes, coherent configurations, Bose–Mesner algebra, DRGs, or
> scheme spectral theory — survey under §4 R5). So the capstone must be a **named
> cited hypothesis** (`PrimitiveCCClassification`) exactly as Approach 1 cites
> `CameronClassification`; it is **not** a from-Mathlib proof, and **not** lighter
> than Approach 1's citation. The real, deliverable, axiom-clean content of
> Approach 3 is **(i)** the imprimitive ⟹ refinement-visible **bridge** (LANDED)
> and **(ii)** the **decomposition conclusion** (refinement-visible block ⟹ the
> descent decomposes into quotient + fibers in bounded depth) — both provable from
> the project's `AssociationScheme` + Mathlib's block layer. Approach 3 wins over
> Approach 1 on **scope** (scheme/CC residuals = the WL-stable-partition setting),
> **bridge cleanliness** (no coarsest-equitable gap), and **citation naturality**
> (combinatorial CC vs group-theoretic O'Nan–Scott), *not* on avoiding a deep
> citation. **Implication for sequencing:** the high-value formal work is pieces
> (i)+(ii); the capstone should be *stated* as a hypothesis and the empirical
> gate (Approach 2) should precede any attempt to discharge it from scratch.

---

## 6. Success criteria & the honest residual

**Success (graduated):**
- **Tier 0 (Approach 0):** the existence/classification split is the canonical
  framing; "Cameron, not Johnson" is fixed; the item has a sanctioned home.
- **Tier 1 (Approach 2):** either a refutation (counterexample → rewrite the
  taxonomy) or a documented battery with no fourth species + the shape list.
- **Tier 2 (Approach 3):** EOL proved Cameron-free on association-scheme
  residuals (axiom-clean).
- **Tier 3 (Approach 1):** EOL proved in general **modulo a cited
  `CameronClassification`**, new bridges axiom-clean.

**What success buys (and does NOT).** The EOL makes the program's flag
**exhaustive and diagnostic**: "never flag except a provable Cameron section or a
multipede" — which is exactly the *exhaustiveness* half of the deferred-endpoint
Goal 1 ("all symmetry except hidden Johnson removed"). It converts the wall from
"an excluded unknown we route around" into "a proven classification with one
named, flaggable hard case." It **does not** canonize any new graph (Cameron/
Johnson still flags) — which is *why it is not GI ∈ P*, and why it is a legitimate
target rather than a disguised assault on the wall.

**The residual after all four tiers:**
- **(B), the mechanism gap** — that the *built* oracle matches the *abstract*
  cascade/abelian class — stays open, owned by the empirical track and ultimately
  the **C#→Lean faithfulness translation** (lowest priority, the V4-style port).
- **Cameron itself**, if cited rather than proved, remains an (honestly marked)
  imported hypothesis, not project-original — acceptable, the same posture as
  Tier-2's abstract scheme axioms.
- **(O\*)-existence / the wall (GI ∈ P)** is *untouched and meant to be* — the
  EOL deliberately classifies the obstruction without claiming it never arises.

---

## 7. Concrete first steps (when the item is picked up)

1. **Approach 0 (DONE 2026-06-02)** — existence/classification split written into
   hidden-johnson.md §7 (new) + tier3-decomposability §0/§6/§8.1 + strategy §15
   gap 5 + calculator §3/§6/§7/§9; Cameron-vs-Johnson note added at each. (No code.)
2. **Mathlib primitivity API — VERIFIED present (2026-05-31, see R5):**
   `IsPreprimitive`, `IsBlock`/blocks, `MultiplePrimitivity`, `Jordan`,
   `Perm/MaximalSubgroups`, `Alternating/MaximalSubgroups`. (B1)/(B2) bridges are
   well-supported; O'Nan–Scott/Cameron absent (must cite). Remaining sub-step:
   pin the exact lemma names for the imprimitive⟹block-system direction.
3. **Approach 2** — stand up the primitive-group battery (start from GAP's
   primitive groups + Johnson/Hamming/Grassmann/product/`PSL` graphs), run the
   C# oracle, classify every flag. **Gate the formal work on its outcome.**
4. **Approach 3** — state `ExhaustiveObstruction` on scheme residuals in Lean
   (on top of `Scheme.lean`); attempt the rank/coherent-algebra classification
   for the depth-≤3 isolation cases already proved. First axiom-clean instance.
5. **Approach 1** — only after 2–4: state `CameronClassification` as a marked
   hypothesis and build the (B1) primitivity bridge.

---

## 8. Cross-references

- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) §7 — the
  (O\*) lemma and its O'Nan–Scott/Cameron grounding (the classification this
  item formalizes; the existence/classification split is written there, Approach 0).
- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §2 (two-axis map), §4–5 ((O\*)-existence = the wall), §8 ((O\*) as the open
  core — the conflation site).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3 (hardness
  axes — the non-cascade∧non-abelian corner).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 gap 5
  (multipede — the *other*, asymmetric flag cause, outside EOL; and now the
  existence-vs-classification split — there is no separate "gap 7").
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) /
  `Scheme.lean` — the association-scheme machinery Approach 3 builds on.
- `ChainDescent/Group.lean` — `AutGroup`/`MulAction`/`OrbitPartition`, the
  substrate that makes primitivity/blocks/Cameron-section *stateable*.
