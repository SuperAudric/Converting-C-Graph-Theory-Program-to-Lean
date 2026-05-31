# Chain descent — the Exhaustive-Obstruction Lemma (plan)

> **STATUS: planning doc for a NEW, not-yet-started item.** Prerequisite
> ordering (set by the user): `hwit` (Stage-3 `Aut(CFI)`) and the existing
> Tier-3 buildout are pursued *first*; another branch already plans that work.
> This doc plans the *separate* item the user surfaced 2026-05-31: the
> hypothesis that **"a graph that does not decompose into the cascade+abelian
> class *is* a hidden Johnson."** It is a **hypothesis, not a certainty** — the
> plan deliberately budgets for refuting it.
>
> Companions: [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
> (Piece C / the (O\*) lemma), [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
> §2/§4/§8 (the two-axis map, sub-claim 2, the wall),
> [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3 (hardness axes),
> [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 gap 7.

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
  non-abelian, **then** it contains a Johnson/Cameron section."* This is the
  user's hypothesis. It says nothing about whether the bad case *arises*; it
  says that *when* it arises it is the named, flaggable one. **This is the
  Exhaustive-Obstruction Lemma, and it is NOT GI ∈ P** (proving it canonizes no
  new graph — the Johnson case still flags). It is **Cameron-hard**, not
  **GI-hard**.

The docs already half-know this — [hidden-johnson §3](./chain-descent-hidden-johnson.md)
calls the classification *"a known-hard but not known-impossible classification
result"* and grounds it in **O'Nan–Scott + Cameron/Maróti** — but
[strategy gap 7](./chain-descent-strategy.md) and the cross-references collapse it
back into *"= GI ∈ P, no Lean obligation."* That collapse is the conflation this
item removes. **The user's "unnamed gap" is precisely the gap this conflation
hides.**

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

**Why "Cameron section," not "Johnson section" (a correction to fold back).**
Cameron's classification of large primitive groups yields `A_k`-on-subsets
(Johnson) **and** product actions (`A_k^d` in product action) and a small list
of exceptions. The docs say "Johnson" as shorthand; the *honest* obstruction
class is **Cameron**. Strict "Johnson-only" is **too narrow** — a product-action
Cameron group would be a genuine instance of the user's "fourth species"
(non-cascade, non-abelian, **not strictly Johnson**) that is nonetheless still
*classified and flaggable*. Naming the target as **Cameron** is what makes the
hypothesis actually true rather than narrowly false. (See §6 refutation R3.)

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
   [hidden-johnson §3](./chain-descent-hidden-johnson.md): "non-trivial residual
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
   project already reasons about these (`IsSchurianSchemeGraph`, `RelIsolatedAt`,
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
- **R4 — the docs' own conflation as inertia.** strategy gap 7 declares the
  whole of (O\*) "**No Lean obligation** (the boundary, not a built claim)."
  Proceeding requires first *overturning that classification* for the (A) half
  (Approach 0). Until then the item has no sanctioned home.
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

---

## 5. Approaches (multiple) and the recommended path

Four approaches; they are **complementary stages**, not alternatives. Recommended
order: **0 → 2 → (1 ∥ 3)**.

### Approach 0 — Disentangle (documentation; prerequisite, cheap)
Split (O\*)-existence from (O\*)-classification across hidden-johnson.md,
tier3-decomposability.md, strategy §15, calculator §9. Downgrade the
classification half from "= GI ∈ P / no Lean obligation" to "**Cameron-hard, not
GI-hard; a finite formal target** (this doc)." Add **Cameron** (not just Johnson)
as the obstruction class. *No Lean.* **This is a true prerequisite** — without it
the item has no sanctioned status (R4) and the Johnson/Cameron scope (R1) stays
wrong. ~half a day.

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
  **named hypothesis** `CameronClassification` (in the spirit of the existing
  `schurian_scheme_profile_exists`/`cfi_cascades_polynomially` axiomatic
  placeholders), with a doc note that it is a *true theorem in the literature*,
  not a project conjecture.
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

1. **Approach 0** — write the existence/classification split into hidden-johnson.md
   §3 + tier3 §8 + strategy gap 7; add Cameron-vs-Johnson note. (No code.)
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

- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) — the
  (O\*) lemma and its O'Nan–Scott/Cameron grounding (the classification this
  item formalizes; **to be split** per Approach 0).
- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §2 (two-axis map), §4–5 ((O\*)-existence = the wall), §8 ((O\*) as the open
  core — the conflation site).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3 (hardness
  axes — the non-cascade∧non-abelian corner).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 gap 5
  (multipede — the *other*, asymmetric flag cause, outside EOL) + gap 7 ((O\*),
  the conflation to overturn for the (A) half).
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) /
  `Scheme.lean` — the association-scheme machinery Approach 3 builds on.
- `ChainDescent/Group.lean` — `AutGroup`/`MulAction`/`OrbitPartition`, the
  substrate that makes primitivity/blocks/Cameron-section *stateable*.
