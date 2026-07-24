# Chain descent — the W2 solvability route: is the rigid gauge forced solvable?

## ▶ STATUS (2026-07-24)

> **What this doc is.** A dedicated planning doc for the **deliberately-avoided** "characterize what k-WL
> *cannot* handle" route — the completeness dual of the rigid seal. It is **W2 attack-route (ii)**
> (`chain-descent-remaining-work.md:734`, *"prove no non-abelian fusion survives into a rigid medium"*),
> re-derived by the user from a **cell-neighbour induction** (mixed non-Schurian cell ⟹ neighbour mixed cell ⟹
> chain ⟹ a global *twist* that blocks collapse). It has its own doc precisely **because** it runs against the
> project's sanctioned architecture — the seal is a *tautology* that avoids classifying obstructions
> (`chain-descent-exhaustive-obstruction.md:221`), so reasoning about the residue's *structure* is deliberately
> sparse. That gap is the reason to write it down, not a reason to skip it. Nothing here is built; this is a
> research plan with a named crux.
>
> **The one-line frontier.** The entire open weight concentrates on **ONE lemma with three equivalent faces**, and
> that lemma **splits into two thresholds** the "linear-or-symmetry" framing conflated:
> 1. **Abelian threshold** (claim #2, the *linear* seal boundary): is the recovered gauge group `Γ` forced
>    **abelian**? — equivalently the c-of-k trigger algebra **composes** (`matroid.md:223-228`), equivalently the
>    recovered gain-graph's **frame matroid is field-representable**. **TRUE over F₂ (XOR composes); OPEN and
>    conjecturally-FALSE beyond** — the S₃/D₄ probe exhibits a *rigid non-abelian* core.
> 2. **Solvable threshold** (the *actual* poly-completeness boundary): is `Γ` forced **solvable**? — equivalently
>    the Babai–Luks canonization of the recovered `Γ`-system is **poly**. **TRUE at every probed level** (abelian,
>    dihedral, Heisenberg all solvable/poly); the **only** open case is a **growing non-solvable** `Γ` (Aₙ/PSL…),
>    for which there is **no constructible witness** and the full CFI is search-infeasible (a theory question).
>
> **The headline correction to the user's hypothesis.** "The obstruction must be linear (F_k) or a symmetry" is
> **too coarse and, in the strict-linear reading, FALSE**: a rigid graph can carry genuinely non-abelian structure
> (`NonAbelianCfiProbe`, Albert's theorem). The correct target is not *linear* but *solvable*: **k-WL fails exactly
> on a non-Schurian rigid core whose difficulty is the Babai–Luks difficulty of its recovered gauge group `Γ` —
> poly for every solvable `Γ`, open only for growing non-solvable `Γ`.**
>
> **Legality guardrails (do not violate).** (a) The form *"X ⟹ GI∈P, therefore X is impossible"* is **BANNED**
> (`remaining-work.md:818`); the "a perfect key cannot exist" argument was **retracted** for exactly this
> (`mixed-composition.md:54-59`). (b) Phrase the crux as an **oracle-capability lemma** ("force fires on any core
> with solvable `Γ`") — a statement about an algorithm we build — **not** as a graph classification ("every rigid
> obstruction is abelian"), which is logged **GI-adjacent** (`wl-visibility.md:152-154`, "the target of the whole
> line, not a near-term build"). Same content, legal framing.
>
> **✅ Tier A piece 1 LANDED (2026-07-24, `ChainDescent/GaugeComplex.lean`, axiom-clean, gate green 93 modules).**
> The split-vs-count base lemma (`chain-descent-matroid.md:146-151`, current API): `refineStep_ne_iff_exists_count_ne`
> — two co-cellular vertices (`χ v = χ w`) are separated by one 1-WL round iff their neighbour class-count vectors
> differ in some class `t = (colour, adj-value, POE)` (= `refineStep_iff` ∘ `Multiset.ext`) — plus the gloss
> `count_signature_eq_card` (each class-count IS a literal neighbour cardinality `|{u≠v : (χ u, adj v u, P v u)=t}|`).
> This is the non-circular skeleton: it says *what warm refinement does at each step*, touching nothing about the
> gauge *group* (Tier B). Next in Tier A: the equitability ⟹ local-exchange (flatness) lemma, then different-orbits
> ⟺ nontrivial holonomy.
>
> **What is DEAD and must not be re-walked.** The **matroid framework on commit-set closures** is closed
> (`matroid.md:463-481`, §6/§8): neither the partition-based `cl` nor the TC-based `cl_prov` satisfies the exchange
> axiom (M3 machine-checked refuted). The live matroid is **not** on the descent closure — it is on the
> **recovered system** (Algorithm R's `Recover` output), which `matroid.md:448-461` §8.3 explicitly anticipated as
> "the remaining possibility … a *linear-algebraic* closure … non-binary for `A_k`-symmetric hidden constructions,
> if any exist." **This doc is that workstream.**

---

## 1. Why this doc exists — the deliberately-avoided path

The rigid seal proves the *resolver* handles the linear class. This route proves the *obstruction* is forced into
a handleable class — the completeness dual. The project's overall seal is an **oracle-capability tautology**
`D1 ∨ (¬D1 ∧ D2) ∨ (¬D1 ∧ ¬D2)` that is exhaustive **without classifying obstructions**
(`exhaustive-obstruction.md:186-190, 221-223`). Leg C's proof is the recorded **"inversion (user's method)"**
(`exhaustive-obstruction.md:276-293`): read the oracle-limit fingerprint off legs A/B's completeness proofs, so the
`¬D1 ∧ ¬D2` bucket *unfolds* into a concrete property list rather than being enumerated.

That architecture deliberately does **not** characterize the residue's algebraic structure — which is why the
project's reasoning about "what shape the twist must be" is thin. This route *does* try to characterize it, on
purpose, to attack **claim #2** (`rigid-seal.md:233`, CONJECTURE, 0 falsifiers) directly. It therefore deserves a
dedicated home: it is off the no-classification main line, it has a genuine attack surface (below), and its dead
ends and standing falsifiers must be recorded so a fresh reader neither re-walks the matroid-closure grave nor
re-derives a banned GI∈P argument.

Two prior forms of "characterize from the WL-blindness side" already exist and were **demoted to lemmas**, not
closed: the **1-WL-visibility dichotomy** (`wl-visibility.md:19-22`, "the only hideable symmetry a graph can carry
is abelian" — GI-adjacent, `:152-154`) and **`CellsAreOrbits`** (`cellsareorbits-route.md:22-26`, demoted because
the canonizer does not reach orbits by refinement; `CellsAreOrbits` is genuinely **false at 1-WL**). This doc
supersedes neither; it reframes both onto the **recovered-system** object, where the live matroid lives.

---

## 2. Localization — where k-WL fails, and the gauge complex

**The obstruction locus is exactly the non-Schurian rigid cells.** For a Schurian scheme `b_WL = b(Aut)` exactly
(`Aut(WL-closure) = Aut(G)`), so **rigid + Schurian ⟹ WL-discrete**, hence **rigid + WL-hard ⟺ non-Schurian**
(`project_nonabelian_cfi_witness` memory; the reframe verified in that probe session). So the user's starting locus
— a stable cell of size ≥ 2 carrying `u, v` in **different Aut-orbits but the same colour** — is provably *the*
place the difficulty lives, and everywhere else the descent discretizes.

**The gauge complex (the user's chain, made precise).** Fix a 1-WL-stable colouring χ.

- **Variables** = the mixed (non-Schurian) cells. Each carries a local "which vertex plays which role" gauge
  choice. In the F₂ model these are the **rails / segments** (columns; `rigid-seal.md:505`, and measured on `mp7`:
  rails = the 7 foot-pairs).
- **Constraints** = the equitability ties. By 1-WL stability `u` and `v` have equal neighbour counts in every cell,
  so a *local exchange* between their neighbour-roles exists — but *which* exchange is undetermined. That is the
  gauge freedom. In the F₂ model these are the **gadget checks / wire supports** (rows of `H`; `rigid-seal.md:381`).
- **Holonomy = different-orbits.** Compose local exchanges around a cycle of constraints. If the composite ≠
  identity, the global swap `{u,u′,…} ↔ {v,v′,…}` is **blocked** ⟹ `u, v` in different orbits. This nontrivial
  class in `H¹(complex; Γ)` is the user's "twist that prevents collapse into true orbit cells." Trivial holonomy ⟹
  the swap **is** an automorphism ⟹ `u, v` same orbit ⟹ the cell was Schurian after all.

**Core vs. decoration is `Recover`.** The user's observation that "pendants extend `{u}` but are secondary" is
exactly right and already operational: decoration cells carry **zero independent holonomy** (their gauge is forced),
and the **core** is the holonomy support. This *is* Algorithm R's **`Recover`** step (`rigid-seal.md:254`, B1a:
strip decoration, keep the reduced incidence `M`). So "core obstruction vs. dependent structure" is a *definition*,
not an intuition — it is the recovered system `M` over the gauge group `Γ`.

**The written precedent for the induction — and its base lemma.** The user's chain is `matroid.md` §4's
**archetype** almost verbatim: a mirror-pair partition `e_v` fires when **any one** neighbour-pair partition fires
(a "1-of-3" *direct* rule, `matroid.md:121-136`), cascading to all pairs. The crucial subtlety is recorded there:
**"1 of k, *unless cancellation*"** (`matroid.md:141-144`) — *two opposite flips can cancel, leaving the multiset
unchanged*. **That cancellation is the additive (linear) structure itself** — it is what makes the trigger algebra
F₂ rather than a free CSP. The **base lemma** the whole induction rests on is `matroid.md:146-151`'s open Lean
lemma: *a vertex `v` breaks from cell `C` iff its neighbour-subcell count vector differs from another vertex's* — a
multiset reformulation of `refineStep_iff`, "a moderate-size lemma; nothing else rests on unproved Lean." **Prove
this first** (Tier A).

---

## 3. The corrected dichotomy — the two-threshold solvability ladder

"Linear obstruction OR symmetry" is too coarse in two ways, both settled by `NonAbelianCfiProbe.cs`
(`project_nonabelian_cfi_witness` memory; 3 tests + Albert-isotopy discriminator, all green):

**(i) WL is blind to `Γ`'s structure.** S₃ ≡ Z₆ and D₄ ≡ Z₈ are **identical in every WL measure** (same `b_WL`,
same forcing-collapse trace) yet non-isomorphic. WL counting sees only `|Γ|` (Latin-square regularity of the
product-=-e level set); commutativity lives in conjugacy/commutators the local gadget never exposes.
**Consequence:** the cell-neighbour induction is WL-visible, so it **cannot decide abelian-vs-non-abelian from
counting data** — the property it wants to conclude is invisible to it. Any "forced abelian" step must route
through **extraction + Albert/isotopy classification** (a non-WL test), never through the neighbour counts.

**(ii) "Rigid ⟹ linear" is FALSE.** Anchor one segment of an S₃/D₄-CFI: `|Aut| = 1` (genuinely rigid), yet the
**extracted gadget relation is genuinely non-abelian** (Albert: no abelian module is isotopic to a non-abelian
group). So a rigid graph **can** carry non-abelian structure. It stays **poly** (fixed finite `Γ` ⟹ fixed-group
CSP), just outside the abelian Smith route.

So the honest picture is a **ladder with two thresholds**, not a dichotomy:

| gauge group `Γ` of the core | canonization | threshold | status |
|---|---|---|---|
| **abelian** (F₂, `Z_{2^k}`, rings) | Smith / rowspace-kernel | ← *abelian* (claim #2, linear seal) | **SEALED — Algorithm R ✓** |
| **non-abelian solvable** (S₃, D₄, dihedral, Heisenberg) | coset-enumeration / fixed-group CSP | between | **poly, TAME — needs a solvable-group solver, not Smith** |
| **non-abelian non-solvable, growing** (Aₙ, PSL…) | Babai–Luks string canonization | ← *solvable* (true completeness) | **the ONLY wall candidate — no constructible witness** |

The user's "must be linear" is the **abelian threshold**; the target that actually secures poly-completeness is the
**solvable threshold**. The S₃/D₄ probe shows the abelian threshold is genuinely crossed (rigid non-abelian exists)
while the solvable threshold holds (S₃/D₄ solvable ⟹ poly). **Retarget accordingly: aim at "solvable," not
"linear."**

**The rigidity fork resolves "structure vs. symmetry."** It is *rigidity*, not linearity, that decides the user's
"OR": the homogeneous (unanchored) gauge acts as an actual automorphism (`|Aut| = |Γ|`) — the **symmetry** case,
consumed by the cascade; **anchoring breaks the automorphism** and leaves the holonomy as a genuine structural
obstruction with no symmetry realizing it — the **structure** case. This is the built **complementary-firing-domain
theorem**: *force provably cannot fire on a symmetric cell, and consume fires exactly there; graphs where neither
fires are the residue* (`mixed-composition.md:399-402`, Lean `narrow_eq_branches_of_orbit` /
`forceBy_no_narrowing_on_orbit`). Non-abelian *symmetry* is caught by the other horn — "non-abelian ⟹ not hideable
⟹ visible ⟹ excluded by rigidity" (`rigid-seal.md:229`).

---

## 4. The crux — one lemma, three faces (and the two thresholds)

All the open weight is one statement. It has three equivalent-looking faces; establishing their coincidence is
itself part of the work, so treat them as *three attack angles on the same crux*, not as a proven equivalence.

**Face A — c-of-k composition (`matroid.md:223-228`, §5.2 Algorithm 2).** The discrepancy chain composes triggers:
if `p` depends on cells `D_i` with triggers `T_i`, is `p`'s ultimate trigger `c-of-k` over `⋃ T_i`? Recorded
verbatim as **load-bearing and not obviously true — "may hold only in the binary case (threshold-of-thresholds =
XOR-of-XOR = XOR); may fail for non-binary."** This is *exactly* the user's "the forced twist IS an F_k linear
obstruction," and the record already says: **provable over F₂, open beyond.** This is the **abelian threshold** in
combinatorial dress.

**Face B — frame-matroid representability (the live matroid).** The recovered core is a **`Γ`-gain graph** (the
gauge complex with `Γ`-valued holonomy — CFI/multipede generalized). By Zaslavsky's theory a gain graph carries a
genuine **frame (bias) matroid for ANY group `Γ`**, so the matroid structure **survives non-abelianness** — as a
*biased-graph* matroid, not the naive commit-closure. The linear/wall split is then matroid **representability**:
the frame matroid is **representable over a field** iff `Γ` embeds appropriately (abelian; for CFI `Γ = F₂` ⟹ the
binary graphic matroid). This is the object `matroid.md:448-461` §8.3 pointed at ("*a linear-algebraic closure …
non-binary for `A_k`-symmetric hidden constructions*") but lacked the group-theoretic generalization (gain graphs)
to name. **Field-representable ⟺ abelian threshold; the coincidence with Face A is the c-of-k = XOR reading.**

**Face C — Babai–Luks solvability (the true target).** Canonizing the recovered `Γ`-gain graph up to gauge is
**string-canonization under `Γ`** — poly for every **solvable** `Γ`, open only for growing non-solvable `Γ`. This
is the **solvable threshold**, strictly weaker (more permissive) than Faces A/B: abelian ⊊ solvable. Faces A/B
secure the *linear* sub-seal; Face C secures *poly-completeness*, which is the actual deliverable.

**The crux lemma, stated legally (oracle-capability form):**

> **`forceSolvable`** — *the force oracle fires (RigidResolved) on any non-Schurian rigid core whose recovered
> gauge group `Γ` is solvable.* Equivalently: the residue `¬HandledS` at non-linear rigid contains **no** core
> with solvable `Γ`; any surviving core has non-solvable growing `Γ`, for which there is no constructible witness.

This is a property of an algorithm (the solver), not a classification of graphs — so it does not trip the
GI-adjacency / banned-form wires. Claim #2 is the **abelian** specialization (Faces A/B); `forceSolvable` is the
honest, achievable **solvable** version (Face C).

**⛔ Dead — do not resurrect.** The matroid framework on **commit-set closures** (`cl`, `cl_prov`) is closed:
exchange (M3) fails, machine-checked `decide` (`matroid.md:436-481`). The exchange lemma "if x determines y then y
determines x" holds at `S = ∅` (`matroid.md:96-99`) but **not** in general — that is the whole retirement. The live
matroid is on the **recovered system `M`**, never on the descent's commit closure. Keep the two straight or you
re-walk a grave.

---

## 5. The attack plan (three tiers)

**Tier A — the localization spine (provable now; non-circular; standalone value).**
1. ✅ **LANDED** — `matroid.md:146-151` base lemma = `GaugeComplex.refineStep_ne_iff_exists_count_ne` (+
   `count_signature_eq_card`), `ChainDescent/GaugeComplex.lean`, axiom-clean, in the gate.
2. Gauge-complex formalization: mixed-cell = non-Schurian; equitability ⟹ local exchange exists (flatness);
   different-orbits ⟺ nontrivial holonomy.
3. Core/decoration split as a theorem: decoration ⟹ zero independent holonomy ⟹ the core is `Recover`'s `M`.
   Re-derive `Recover` as a *statement about WL-stable graphs*, not just an algorithm.
> ⚠ **Do NOT put "linear" in the base case.** The induction produces the *complex*; linearity/solvability is a
> property of the *holonomy group*, proved separately (Tier B) or the whole thing is circular (assumes claim #2).

**Tier B — the crux (`forceSolvable`), attacked by the three faces, NOT by WL-counting.**
- (i) **Extraction + Albert/isotopy**: classify the *recovered relation* `M` (not counting-blind) — abelian? then
  Smith seals it; solvable? then coset-enumeration seals it. The probe's `Probe_ExtractionDiscriminator` is the
  template.
- (ii) **Frame-matroid representability** (Face B): decide binary/field-representable ⟺ abelian; this is the
  Tier-2 detector `matroid.md:463-481` §8.4 concluded "lives at the linear-oracle layer, not commit-closures."
- (iii) **Route-(ii) visibility** (`remaining-work.md:734`): "no non-abelian fusion survives into a rigid medium" —
  the negative-witness evidence is the S₃/D₄ tameness; a *proof* collapses the rigid residual.
- **NOT** the cell-neighbour counting itself (§3(i): WL is blind to `Γ`'s structure).

**Tier C — falsifier discipline (run in parallel; cheap first; per `feedback_validate_cheap_before_long_runs`).**
- Test any "chain cannot collapse" claim against **Shrikhande** first — it killed *unconditional* block-visibility
  (rank-4 scheme with a ClosedSubset 1-WL-from-`v` cannot see, `steers-archive.md:137-139`). If your construction
  claims to see a split there that 1-WL-from-`v` provably cannot, it over-claims.
- The **only** untested corner is **growing non-solvable `Γ`** (Aₙ). The full CFI is search-infeasible
  (`|A₅| = 60` ⟹ 3600 vertices/gadget), so this is a **theory question**, not a probe. A positive result there = a
  genuine witness = a statement-change (claim #3 realized).
- Reuse `NonAbelianCfiProbe.cs` (`GroupFromPerms` / `BuildGroupCfi`); do **not** re-walk the seven Schurian
  falsifiers (`steers-archive.md:211-227`, 0 witnesses) or the amorphic `ℤ₄²` bullseye (recovers at depth 2).

---

## 6. Falsifier ledger & standing evidence (fresh-reader)

| construction | what it kills / shows | not a witness because | ref |
|---|---|---|---|
| **Lichter CFI-over-`Z_{2^k}`** | "F₂ is the only obstruction" — FALSE | still **linear** (varying ring) | `rigid-seal.md:232`, `ir-blindspot-solver.md:1067` |
| **S₃/D₄ group-CFI** (rigidified) | "rigid ⟹ abelian" — FALSE (rigid non-abelian exists) | **solvable ⟹ poly** (coset CSP) | `project_nonabelian_cfi_witness` memory |
| **Dihedral / Heisenberg** (growing) | non-abelian structure stays accessible & tame with growth | **solvable ⟹ Babai–Luks poly** | ibid. §group-varying probe |
| **multipedes** (circulant≤72, rand-reg≤288) | canonize (discretize ≤7 levels) | rigid but not a flag at scale | `exhaustive-obstruction.md:420-427` |
| **rigid expanders** | parity propagates fast (easy) | small instances don't flag | `exhaustive-obstruction.md:424-427` |
| **Shrikhande** | kills *unconditional* block-visibility | a scheme fact, not a rigid core | `steers-archive.md:137-139` |
| **7 Schurian falsifiers + `ℤ₄²` bullseye** | 0 G2-B witnesses; bullseye recovers depth 2 | tame remainder recovers | `steers-archive.md:211-227` |
| **growing non-solvable Aₙ** | THE remaining wall candidate | **no constructible witness** (search-infeasible) | `project_nonabelian_cfi_witness` §refined |

The **off-track falsifier** that would break the carve (watch for it): a **primitive, small, non-abelian,
non-Cameron scheme with *unbounded* base** (`steers-archive.md:28-30`) — that would mean "solvable" is the wrong
target and the residue framing is wrong.

---

## 7. What a fresh reader needs

**Authoritative state to read first:** `chain-descent-rigid-seal.md` §5 (the classification / claims #1–#3) and
`chain-descent-remaining-work.md` W1/W2/W3 (`:717-743`). This doc is the W2-route-(ii) plan; the seal itself is the
soundness dual.

**Docs to work forwards from:**
- `Archive/ChainDescent/chain-descent-matroid.md` — **§4** (the archetype = the user's induction; the base Lean
  lemma `:146-151`; the "1-of-k unless cancellation" caveat), **§5.2** (the c-of-k composition crux `:223-228`),
  **§8.3-8.4** (why the commit-closure matroid is dead but the *recovered-system* linear-algebraic matroid is the
  live Tier-2 detector). Read the STATUS banner: the *closure* framework is retired; the *recovered-system* framing
  is not.
- `chain-descent-exhaustive-obstruction.md` §the-inversion (`:276-293`) — the oracle-capability method this route
  is an instance of; keeps the framing legal.
- `chain-descent-wl-visibility.md` (`:78-87, 152-217`) — the prior WL-blindness dichotomy, demoted to lemmas;
  R3/Route B "only hideable symmetry is abelian" is GI-adjacent (phrase around it).
- `chain-descent-mixed-composition.md` (`:399-402`) — the complementary-firing-domain theorem (structure/symmetry
  fork); and `:54-59` the retracted "perfect key cannot exist" (the banned form).

**Lean objects the crux reduces onto:**
- `ChainDescent/RigidSolveF2.lean` — `IsRigidF2` (trivial kernel = rigid), `unique_solution_of_rigid`, rowspace-only
  rigidity (`dotP_zero_rowspace`). The abelian-threshold seal.
- `ChainDescent/ForcingModel.lean` — `ForcingModel.bridge` (graph↔F₂, carried); `ChainDescent/ForcingCircuits.lean`
  — `forced_certificate` (forced ⟹ rowspace codeword). The extraction to classify at Tier B.
- `ChainDescent/RigidSeal.lean` — `compKey` / `SolverSeparates` (the force key carrying the sole obligation);
  `RigidResolved` / `Select.HandledS` — the residue predicate the crux must empty.
- Wall reference: `hSmallAutThin` (`CascadeAffine.lean:1320`) — a *separate* Route-C object (W1), NOT this residue.

**Probe fixture:** `GraphCanonizationProject.Tests/NonAbelianCfiProbe.cs` — `BuildGroupCfi(G, biadj, anchorSeg0)`,
`GroupFromPerms`, `Probe_ExtractionDiscriminator` (Albert test), `Probe_GroupVaryingNonAbelian`. The reusable
Tier-C instrument. Full findings: memory `project_nonabelian_cfi_witness_2026-06-28`.

---

## 8. Cross-references

- `chain-descent-rigid-seal.md` — the soundness dual (the seal this route completes); §5 classification, §10 gap
  ledger (residue `¬HandledS` "conjecturally empty").
- `chain-descent-remaining-work.md` — W2 (`:729-741`), the frontier framing, the user-flagged open Q "the rigid
  solver likely covers MORE than linear residues" (`:81-82`).
- `chain-descent-ir-blindspot-solver.md` §11.11/§11.14 — the 2×2 classification and "affine = linear-algebraic";
  the residue argued unreachable rather than proven empty (`:1109-1113`).
- `chain-descent-endgame-spec.md` (`:410-415`) — the `UnhandledResidue` trichotomy; `residueNonSchurian` flagged a
  modelling gap, "not a genuine class of hard graph."
- `Archive/ChainDescent/chain-descent-matroid.md` — the retired closure framework + the live recovered-system
  matroid (§8.3); `Archive/ChainDescent/chain-descent-steers-archive.md` — the falsifier record and dead routes.

> **Provenance.** Written 2026-07-24 as the dedicated home for the deliberately-avoided completeness route. It
> reframes the user's cell-neighbour induction onto the recovered-system gauge group and retargets the goal from
> *linear* (claim #2, abelian threshold — genuinely crossed by rigid non-abelian cores) to *solvable* (the
> achievable poly-completeness threshold, `forceSolvable`). The three faces (c-of-k composition / frame-matroid
> representability / Babai–Luks solvability) are attack angles, not a proven equivalence; establishing their
> coincidence is Tier-B work. No Lean built; no build-gate impact.
