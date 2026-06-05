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
> for "imprimitive ⟹ cascade" / contrapositive "non-cascade ⟹ primitive". **Remaining on the bridge:** the
> *cascade*/decomposition conclusion proper (refinement-visible block ⟹ the descent decomposes into
> quotient + fibers in bounded depth) — the lighter combinatorial follow-on, **fully provable** from the
> landed bridge + Mathlib's block layer. **Then (the capstone):** primitive high-rank scheme with no abelian
> regular subgroup ⟹ Johnson/Hamming-type.
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

**Drafting rule for every downstream statement.** "All symmetry removed **or**
Cameron" (statement 1) is **not** the time bound (statement 2): statement 2 carries
the *extra* IR-core escape. A future Phase-2 blind-spot handler
([deferred-decisions §7](./chain-descent-deferred-decisions.md)) addresses **only**
that escape — never the seal. Keep both clauses, always.

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
