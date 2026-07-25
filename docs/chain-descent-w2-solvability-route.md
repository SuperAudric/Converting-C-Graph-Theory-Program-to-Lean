# Chain descent — the W2 solvability route: is the rigid gauge forced solvable?

## ▶ STATUS (2026-07-24)

> ## ▶▶ HANDOFF — FRESH READER START HERE
>
> **The route.** Completeness dual of the rigid seal: *is the rigid gauge forced **solvable**?* (retargeted from
> "linear" — §3). k-WL fails exactly on a non-Schurian rigid core; its difficulty is the Babai–Luks difficulty of
> the recovered gauge group Γ (§4a). Legal framing = oracle-capability, never graph-classification (§1 guardrails).
>
> **BUILT (Lean, all axiom-clean `[propext, Classical.choice, Quot.sound]`, in `scripts/build.sh`, gate green — 97
> modules, ~190 s). Read in this dependency order:**
> 1. **`ChainDescent/GaugeComplex.lean`** — Tier A spine. Piece 1 `refineStep_ne_iff_exists_count_ne` (+
>    `count_signature_eq_card`, `nbhdClass`); piece 2 flatness `localExchange_of_equitable`
>    (+ `refineStep_eq_iff_forall_card_eq`); piece 3 holonomy `IsColAut`/`SameOrbit`/`LocallyFlat`/
>    `HolonomyNontrivial` + `sameOrbit_imp_locallyFlat` (equivariance) + `holonomyNontrivial_iff_diff_orbit`.
> 2. **`ChainDescent/GaugeBridge.lean`** — Tier B step 1. `GaugeContract` (abstract recovered Γ; `faithful` carried)
>    + **`holonomy_iff_gauge`** (Tier A ↔ Γ) + `gaugeContractMax` (non-vacuity witness; ⚠ NOT the recovered gauge).
> 3. **`ChainDescent/GaugeAbelian.lean`** — Tier B abelian branch. `isSolvable_of_carrier_comm` (abelian ⟹ solvable);
>    `kerF2 H` + `isRigidF2_iff_kerF2_eq_bot` + `rigid_unique_solve` (reuse of `RigidSolveF2`).
> 4. **`ChainDescent/GaugeSolvable.lean`** — Tier B solvable branch. `of_solvable_tower` / `of_solvable_abelian_base`
>    (the proved reduction skeleton: solvable ⟹ tower of abelian steps; the per-level `hstep` = carried Luks).
> 5. **`ChainDescent/GaugeIsolation.lean`** — C3 `Recover` R-a. `IsRigid`, `sameOrbit_iff_eq_of_rigid`,
>    `holonomyNontrivial_iff_flat_ne_of_rigid` (rigid ⟹ gauge cells = non-singleton flatness classes).
> 6. **`ChainDescent/GaugeNonabelian.lean`** — C3 `Recover` R-c (non-abelian). The §3a/§3b skeleton: recovered gauge
>    `Γ ≤ (ι → G₀)` ⟹ `isSolvable_pi` (degree-independent) → `recoveredGauge_reduces_to_abelian` (reduces to the
>    abelian branch via `of_solvable_tower`) + `isSolvable_gaugeCarrier` (feeds `GaugeContract`); `S₃` non-vacuity.
> 7. **`ChainDescent/GaugeLayer.lean`** — R-c extraction bricks **L1+L2+L3** (§3b's corner-emptying gap). L1
>    `derivedSeries_pi_const` (tower decomposes coordinatewise = each layer a free module of rank `|gadgets|` ⟹
>    per-coordinate **linear** step); L2 `commutator_mem_derivedSeries_succ` (layer abelian) + `layerCoeff` (`A_k`) +
>    `layerProj_surjective` (the `ι → A_k` coordinate structure); L3 `kerF2Submodule` (the abelian gauge is an
>    F₂-**subspace** — the `A_0 = ZMod 2` field instance). **L4** (`Recover` → explicit linear systems) stays carried.
>
> **PROVED end-to-end (the reduction).** Holonomy → Γ (bridge) → abelian solve (built, `ker H`) / solvable solve
> (reduces to abelian + carried step); isolation automatic in the rigid regime; the **non-abelian** recovered gauge is
> solvable and reduces to the abelian branch (R-c, degree-independently — §3a).
>
> **CARRIED (the honest boundary — cited, never fresh `axiom`s):** (a) **R-b the forcing bridge** = `faithful` ≈
> `ForcingModel.bridge`, **shared** with the rigid-seal track (C3 adds no *new* carried obligation, §5a); (b) the
> **Babai–Luks per-level poly** (`hstep`) = Luks 1982 / Babai–Luks 1983 — **§3a sharpens the scope: a genuine `Γ_d`-poly
> theorem for the whole fixed-`G₀` family** (recovered `Γ ≤ G₀^m ⟹ Γ ∈ Γ_{μ(G₀)}`, `μ = 2` for CFI/Lichter), with the
> **plausibly-poly hedge confined to a *growing* unbounded-cyclic-section solvable corner** (`cameron-entanglement.md:124`);
> (c) **R-c-nonabelian** — **✅ now BUILT** (`GaugeNonabelian.lean`, group-theoretic skeleton); the remaining carried
> part is the extraction preserving each derived layer's *module structure* (so the tower step is a linear solve) =
> the §3b load-bearing gap, shared with `ForcingModel.bridge`.
>
> **NEXT (in value order):** **L4** — the one remaining extraction brick and the honest corner-emptying gap: prove
> `Recover` produces each derived layer *as an explicit linear system from the graph* (so `hstep` is a built Smith
> solve, not carried Luks). This is **shared with `ForcingModel.bridge`** (a cross-track object) — L1–L3 (`GaugeLayer`)
> built the target structure it plugs into. Then wire `carrier ≅ kerF2` on the rigid residue (thin) · R-b (proving the
> forcing bridge) = the same large cross-track effort L4 lives in. **Deferred:** C2 = extraction-free intrinsic Γ (blocked on fibre-isolation; §5a shows rigidity
> makes it unnecessary for force). **Map:** §4a Γ-scope · §5 attack plan · §5a Recover scope · §6 falsifier ledger ·
> §7 fresh-reader pointers. **Chronological landing notes follow below.**
>
> **▶▶ THE LOGICAL STATE — what this track has reduced the corner to (read this).** With **L1–L3 + `of_solvable_tower`**
> built, the chain is complete as *structure*: a recovered **solvable** gauge `⟹` a bounded tower of per-coordinate
> **linear** (Smith/Gaussian) solves — **modulo L4 alone** (the graph→linear-system extraction, `GaugeLayer` L4, whose
> **F₂/`A_0` instance** is `ForcingModel.bridge`). Consequently:
> - **If L4 holds unconditionally, the entire *solvable* corner is poly ⟹ empty** (no residue beyond the wall). L1–L3
>   already discharge everything between "solvable gauge" and "linear tower"; L4 is the *only* remaining hypothesis.
> - The **only** residue that can then survive is the **non-solvable** rigid case = **claim #3 = the wall**
>   (`rigid-seal.md` §5; 0 constructible witnesses) — a **separate** conjecture, **not** implied by L4.
> - ⚠ **Precise form (don't overstate):** L4 ⟹ solvable-corner-empty is **one-directional** (a different poly route
>   could also empty it); "non-solvable case empty" is the *wall*, tracked independently, not equivalent to L4. **Net:
>   this track has reduced the §3a corner to exactly `{L4}` + the pre-existing wall — it opens no new residue.** That is
>   the whole deliverable of the W2 completeness dual: the solvable side is now a single named extraction obligation.
> - ⚠ **L4 ≠ `ForcingModel.bridge` beyond F₂ — do not let the "shared object" framing hide `A_k`-layer work.** The
>   bridge is the **single-layer F₂** faithfulness; L4 is the **per-derived-layer** extraction over `A_k =
>   Abelianization(derivedSeries G₀ k)`, and the bridge is only its `A_0 = ZMod 2` case (§3b; §5a line 472 says as much:
>   `Recover`'s faithfulness is "stronger than the empirical F₂ `ForcingModel.bridge`"). So discharging the rigid seal's
>   `ForcingModel.bridge` empties the **abelian/F₂** solvable corner and shares the **R-b forcing-faithfulness** level
>   with this track — but the `A_k` (k ≥ 1) layer extraction is **W2-only work**, not free from the F₂ bridge. "C3 adds
>   no *new* carried obligation" holds at R-b; the ring-general L4 is that obligation *generalized*, not a fresh one.
>
> ---
>
> **What this doc is.** A dedicated planning doc for the **deliberately-avoided** "characterize what k-WL
> *cannot* handle" route — the completeness dual of the rigid seal. It is **W2 attack-route (ii)**
> (`chain-descent-remaining-work.md:734`, *"prove no non-abelian fusion survives into a rigid medium"*),
> re-derived by the user from a **cell-neighbour induction** (mixed non-Schurian cell ⟹ neighbour mixed cell ⟹
> chain ⟹ a global *twist* that blocks collapse). It has its own doc precisely **because** it runs against the
> project's sanctioned architecture — the seal is a *tautology* that avoids classifying obstructions
> (`chain-descent-exhaustive-obstruction.md:221`), so reasoning about the residue's *structure* is deliberately
> sparse. That gap is the reason to write it down, not a reason to skip it. **(Originally a pure research plan; the
> Tier-A spine + the Tier-B reduction + C3 R-a are now built — see the HANDOFF above.)**
>
> **The one-line frontier.** The entire open weight concentrates on **ONE lemma with three equivalent faces**, and
> that lemma **splits into two thresholds** the "linear-or-symmetry" framing conflated:
> 1. **Abelian threshold** (claim #2, the *linear* seal boundary): is the recovered gauge group `Γ` forced
>    **abelian**? — equivalently the c-of-k trigger algebra **composes** (`matroid.md:223-228`), equivalently the
>    recovered gain-graph's **frame matroid is field-representable**. **TRUE over F₂ (XOR composes); OPEN and
>    conjecturally-FALSE beyond** — the S₃/D₄ probe exhibits a *rigid non-abelian* core.
> 2. **Solvable threshold** (the *actual* poly-completeness boundary): is `Γ` forced **solvable**? — canonization
>    under a solvable gauge is poly for **bounded** composition-factor degree (`Γ_d`, Luks 1982). **§3a (the Luks
>    sharpening) upgrades this to a genuine poly THEOREM for the whole family that arises** — the recovered
>    `Γ ≤ G₀^m` (product of the fixed local gadget group) forces `Γ ∈ Γ_{μ(G₀)}`, `μ = 2` for CFI/Lichter — leaving
>    **plausibly poly** (`cameron-entanglement.md:124`) confined to a *growing* unbounded-cyclic-section solvable
>    corner. **TRUE at every probed level** (abelian, dihedral, Heisenberg — each a fixed `G₀`, hence genuine poly);
>    the **only** wall case is a **growing non-solvable** `Γ` (Aₙ/PSL…), no constructible witness (theory).
>
> **The headline correction to the user's hypothesis.** "The obstruction must be linear (F_k) or a symmetry" is
> **too coarse and, in the strict-linear reading, FALSE**: a rigid graph can carry genuinely non-abelian structure
> (`NonAbelianCfiProbe`, Albert's theorem). The correct target is not *linear* but *solvable*: **k-WL fails exactly
> on a non-Schurian rigid core whose difficulty is the Babai–Luks difficulty of its recovered gauge group `Γ` —
> poly for bounded-degree (`Γ_d`) solvable gauge (Luks) and plausibly poly for general solvable, open only for
> growing non-solvable `Γ`.**
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
> gauge *group* (Tier B).
>
> **✅ Tier A piece 2 LANDED (2026-07-24, same module, axiom-clean).** Flatness / the local exchange:
> `refineStep_eq_iff_forall_card_eq` (the positive twin of piece 1 — same refined colour ⟺ co-cellular ∧ every
> class-count agrees), `localExchange_of_refineStep_eq` and the headline `localExchange_of_equitable` (equitability,
> spelled as the fixpoint condition `∀ x y, χ x = χ y → refineStep x = refineStep y`, ⟹ for every co-cellular pair
> and every class `t` a **bijection** `nbhdClass v t ≃ nbhdClass w t` exists). The bijection is non-canonical
> (`Finset.equivOfCardEq`, choice) — that non-canonicity *is* the local gauge freedom. Flat = every local exchange
> exists; whether a globally-consistent choice exists is the **holonomy** (piece 3, untouched here).
>
> **✅ Tier A piece 3 LANDED (2026-07-24, same module, axiom-clean, gate green).** The holonomy object as the
> **flat-but-not-globally-trivial defect**: `IsColAut` (generic-`V` colour-automorphism), `SameOrbit`,
> `LocallyFlat` (= `refineStep u = refineStep v`, ⟺ per-class exchanges exist via `locallyFlat_iff`), and
> `HolonomyNontrivial u v := LocallyFlat u v ∧ ¬ SameOrbit u v`. **Load-bearing content = the equivariance
> `sameOrbit_imp_locallyFlat`** (every orbit pair is flat — a global section preserves the refined colour, via
> `signature_eq_of_colAut`), which makes the flat locus the correct domain; piece 3 proper is
> `holonomyNontrivial_iff_diff_orbit` (on flat pairs, different-orbit ⟺ nontrivial holonomy). ⚠ **Non-vacuity is
> external** — a Lean witness of an inhabited `HolonomyNontrivial` *is* a WL lower bound (flat ∧ ¬orbit = CFI /
> multipede), carried per the standing evidence, not proved here. The finer structure (this holonomy is a *linear*
> F₂/ring cocycle composing around cycles when the gauge is abelian) is **Tier B** and untouched. **Tier A spine
> complete.**
>
> **✅ Γ SCOPED (2026-07-24, §4a).** Operative **Γ = C3 = the structurally-recovered gauge relation**, layered
> **isolate (group-general) → solve (abelian=Smith built / solvable=coset-enum new)**. The `mp7` check refined this:
> the gauge/base *isolation* (`Recover`) is group-general (`mp7` → `Z₂³`, not `Aut`=1344); only the *solve* is
> abelian-in-Lean. Γ ≠ `Aut` (C1 dead); the extraction-free **C2 is deferred** (completeness ideal, blocked on
> intrinsic fibre-isolation, not needed for the solvable threshold).
>
> **✅ Tier B step 1 (the bridge) LANDED (2026-07-24, `ChainDescent/GaugeBridge.lean`, axiom-clean, gate green 94
> modules).** Abstract `GaugeContract` = the recovered gauge Γ (a group `carrier ≤ Sym V` whose orbits are the
> local-flatness classes; `faithful` = the isolation-faithfulness `Recover` discharges, carried). `holonomy_iff_gauge`:
> `HolonomyNontrivial u v ⟺ Γ-orbit u v ∧ ¬SameOrbit` — Tier A's holonomy connected to the group-carrying Γ.
> `gaugeContractMax` proves the contract is **inhabited** (non-vacuity guard; ⚠ the max partition-stabilizer, NOT the
> recovered gauge — solvability is asked of the recovered `carrier`).
>
> **✅ Tier B abelian branch LANDED (2026-07-24, `ChainDescent/GaugeAbelian.lean`, axiom-clean, gate green 95
> modules).** `isSolvable_of_carrier_comm` (commutative gauge ⟹ solvable — abelian is the trivial base of the
> solvable target); and the `RigidSolveF2` reuse: `kerF2 H` = the abelian gauge as `ker H` (abelian by construction),
> `isRigidF2_iff_kerF2_eq_bot` (`IsRigidF2 ⟺ kerF2 = ⊥` = "rigid = no gauge freedom"), `rigid_unique_solve` (the
> built determinacy as the branch's solve). Carried: the `carrier ≅ kerF2 H` correspondence (`Recover`/`ForcingModel`
> bridge).
>
> **✅ Tier B solvable branch — reduction skeleton LANDED (2026-07-24, `ChainDescent/GaugeSolvable.lean`, axiom-clean,
> gate green 96 modules).** The Babai–Luks reduction: `of_solvable_tower` (capability `P` for `⊥` + preserved across
> each derived step ⟹ `P ⊤`, downward induction on the terminating derived series) + `of_solvable_abelian_base` (the
> solvable branch **reduces to the abelian branch** — abelian base + the step ⟹ whole solvable gauge). ⚠ the
> per-level `hstep` = **Luks's reduction** (Luks 1982, JCSS 25:42–65; Babai–Luks 1983, STOC) — carried, not built.
> **Honest poly scope:** settled for `Γ_d` (bounded composition-factor degree) and bounded-order gauge; for general
> unbounded solvable it is **"plausibly poly"** (project hedge, `cameron-entanglement.md:124`), not a classical
> theorem. The skeleton (proved) makes no poly claim itself.
>
> **✅ C3 `Recover` — piece R-a LANDED (2026-07-24, `ChainDescent/GaugeIsolation.lean`, axiom-clean, gate green 97
> modules; scope in §5a).** Gauge **isolation** in the rigid regime: `sameOrbit_iff_eq_of_rigid`,
> `holonomyNontrivial_iff_flat_ne_of_rigid` (rigid ⟹ nontrivial holonomy = a locally-flat pair of distinct vertices
> ⟹ gauge cells = non-singleton flatness classes). ★ **Refined the scope:** the `mp7 → Z₂³` gauge/base split is the
> two-seals **interleaving** (consume peels `PGL(3,2)`, force sees the rigid `Z₂³` residue), NOT a Recover-internal
> classifier — so rigidity does the isolating, and the deferred C2 fibre-isolation is unnecessary for force.
> `faithful` (R-d) ≈ the carried forcing bridge (`ForcingModel.bridge`, shared with the rigid-seal — C3 adds no new
> carried obligation). **Next: C3's `Recover`** discharging
> `faithful` + the `carrier ≅ kerF2` correspondence (the remaining carried isolation content), and/or consolidation.
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
| **non-abelian solvable** (S₃, D₄, dihedral, Heisenberg) | coset-enumeration / fixed-group CSP | between | **genuine `Γ_d`-poly THEOREM for every *fixed* `G₀` (§3a); hedge only on *growing* unbounded-cyclic-section families** |
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

## 3a. The Luks sharpening — the hedge is confined, not "general solvable"

Face C carries Luks as "poly for `Γ_d`, **plausibly poly** for general solvable." That is **looser than the recovered
gauge groups warrant.** The sharpening rests on one structural fact about how `Recover` produces Γ.

**Structure.** By construction (`project_nonabelian_cfi_witness`; CFI/multipede-over-Γ, `cameron-entanglement.md:49`),
the gauge acts **per gadget** by a **fixed local group `G₀`** (`Z₂` for CFI, `Z_{2^k}` for Lichter, `S₃`/`D₄`/`H` for
the group-CFI), and independent gadgets gauge independently, so the recovered `Γ` is a **subgroup of a product**
`Γ ≤ G₀^m`, with `m ≤ n` the gadget count. For CFI this is exactly the cycle space `Z₂^β ≤ Z₂^{|E|}`.

**Lemma (`Γ ∈ Γ_d` for `d = μ(G₀)` := the max composition-factor degree of `G₀`).** The class `Γ_d` is closed under
**subgroups, quotients, and extensions** (standard — the closure Luks's own recursion rides; Luks 1982). Hence
`G₀ ∈ Γ_{μ(G₀)}` (definition of `μ`) ⟹ `G₀^m ∈ Γ_{μ(G₀)}` (extension/product-closed) ⟹ `Γ ≤ G₀^m` forces
`Γ ∈ Γ_{μ(G₀)}` (subgroup-closed). **So whenever `G₀` is bounded, `μ(G₀) = O(1)`, and Luks canonizes `Γ` in
`n^{O(μ(G₀))}` — a genuine poly THEOREM, not a hedge.**

**The hedge splits four ways, and survives in only one:**

| local gauge `G₀` | `μ(G₀)` | route | status after the sharpening |
|---|---|---|---|
| **bounded** — CFI (`Z₂`), **Lichter `Z_{2^k}` for every `k`**, fixed `S₃`/`D₄`/`H` | `O(1)` (CFI/Lichter **= 2**; `S₃` = 3) | Luks `n^{O(μ)}` | **poly THEOREM — hedge retired** |
| **growing abelian** (`Z_p`, `p → ∞`) | `p` (unbounded) | abelian branch (Smith / `kerF2`) | **poly THEOREM — degree irrelevant** |
| **growing non-abelian solvable, unbounded cyclic sections** (growing `D_p`, `H(𝔽_p)`) | `p` (unbounded) | neither Luks-`Γ_d` nor Smith | **the ONLY surviving "plausibly poly" — narrow, named** |
| **growing non-solvable** (`A_k`, `PSL`) | unbounded non-solvable factor | — | **the wall (unchanged)** |

**Two consequences.**
1. **The hedge never touched the witness bank.** Every *fixed* construction is a fixed `G₀` ⟹ `μ` constant ⟹ genuine
   Luks-poly; so the probe evidence (`D₃…D₈`, `H(𝔽₃)` all tame, `project_nonabelian_cfi_witness`) is each a *genuine*
   poly instance, and "plausibly poly" was only ever the **uniform/asymptotic** claim over a *growing* family.
   ★ **`Z_{2^k}` (Lichter) is `Γ₂` for every `k`** (a cyclic 2-group has every composition factor `= Z₂`), so the whole
   *varying-abelian* row is Luks-poly *verbatim* — it never even needed the abelian branch. This corrects the loose
   reading at `cameron-entanglement.md:124` ("dihedral/Heisenberg solvable ⟹ Babai–Luks poly"): the *fixed* members are
   genuine-poly (`Γ_d`), and only the `p → ∞` limit hedges.
2. **The surviving corner is structurally strained (perhaps empty).** For `G₀` to grow, the gadget alphabet must grow
   (`|G₀|^{d-1}` vertices per gadget), so a growing local group forces `n` to grow with it; and a *single* gadget
   carrying a large `D_p`/cyclic symmetry is directly canonizable (a cycle's dihedral symmetry is trivial to fix). So
   the residual regime — growing non-abelian solvable with unbounded cyclic sections — has **no constructible witness**
   and is squeezed between the abelian branch and the wall. (Argument-sketch, not a proof that the corner is empty.)

**Deliverable.** Face C's carried-vs-theorem boundary moves: **a genuine `Γ_d`-poly theorem on the entire fixed-`G₀`
family (all CFI/Lichter/fixed-non-abelian), poly-by-Smith on growing-abelian, and the hedge confined to one
unwitnessed growing-solvable corner adjacent to the wall.** The earlier "plausibly poly for general solvable"
over-scoped the hedge; the honest carried residue is this single corner.

⚠ **Legality.** This is still an *oracle-capability* statement (Luks's algorithm canonizes any `Γ_{O(1)}` gauge), not a
graph classification — it stays on the legal side of the GI-adjacency wire (§1 guardrails). It does **not** assert the
residue is empty; it narrows *where* the un-settled poly claim lives.

---

## 3b. Is the §3a corner empty? — the argument plan (2026-07-24)

The §3a residual is a **growing non-abelian solvable** recovered gauge (`D_p`, `H(𝔽_p)`, iterated wreath). "Empty" has
three senses; only the **oracle-capability** ones are legal to argue: **(E2)** it arises but is poly-canonizable by a
route other than Luks-`Γ_d`; **(E3)** it arises but never reaches force as a rigid residue. (The third, *"if non-empty
then GI∉P"*, is the **banned form** — do not use it.) **Non-emptiness is graceful:** poly-or-flag **flags** the corner
(sound, poly-bounded), so this is a *completeness*, not a soundness, question. **Free reframe:** by **Babai 2016**
(quasipoly string-canonization under any `Γ ≤ Sym Ω`, `|Ω| = n`), the corner is **quasipolynomial unconditionally** —
the open question is strictly *poly-vs-quasipoly* on a witness-free corner, not "unknown."

| argument | mechanism | gap | resolvable? |
|---|---|---|---|
| **A1 — visibility excludes non-abelian gauge** (E3) | "only hideable symmetry is abelian" ⟹ non-abelian gauge visible ⟹ consumed | **probe-refuted**: anchoring rigidifies a non-abelian gauge into a genuine force-residue (`project_nonabelian_cfi_witness`) | **No — dead** (measured falsifier) |
| **A2 — a graph parameter bounds `μ(G₀)`** (salvage Luks) | bounded arity/degree ⟹ bounded local group | bounded arity ⟹ `G₀ = Γ` arbitrary; nothing bounds the local group | **No — dead** |
| **A3 — derived-series tower of *linear* solves** (E2) — **THE LEAD** | solvable ⟹ tower of abelian steps (`of_solvable_tower`, **built**); each abelian layer canonized **degree-independently by linear algebra** (Smith/`kerF2`), not Luks-`Γ_d` | `hstep` is poly **iff each derived quotient acts *linearly* (as a module) on the recovered lower layer**; linearity collapses the `2^m`-coset branching that makes general-solvable open (the `kerF2` precedent: solve `2^β` gauge in one Gaussian pass, no enumeration) | **Yes in principle** — reduces to the *carried* `hstep`; `D_p` (`Z₂` = `×(−1)`) and `H(𝔽_p)` (central ⟹ trivial action) both have **linear** layers, so both close *if Recover preserves the layer module structure* |
| **A4 — abelian-normal + linear quotient** (E2, A3 sub-case) | `D_p = Z_p ⋊ Z₂`: ring-solver does `Z_p` (P3-ring), `Z₂^m` quotient → `kerF2` | needs P3-ring built; two-unbounded-layer `H(𝔽_p)` folds up into A3 | **Yes for the `D_p`/metabelian sub-corner** (modulo P3-ring); rest → A3 |

⚠ **Derived length is a red herring** — a tower of poly-time steps is poly regardless of length; the hard point is the
**per-quotient coset/branching blow-up**, which **linearity** (module action ⟹ coset orbits, no enumeration) collapses.

**The convergence (the payoff).** A3 reduces "corner empty" to *"each derived layer of the recovered gauge is linearly
representable"* — which is **Face B (frame-matroid representability) applied per derived-series level.** A genuinely
*non-linear* layer is exactly **claim #3** (the wall, 0 witnesses). So A3, if it goes through, shows the solvable corner
contains **no *new* residue** — any true survivor **coincides with the existing wall**. The corner does not widen the
frontier; it maps onto it. This is the strongest honest "empty": *no residue beyond the one already named.*

**The one load-bearing gap (honest).** Does `Recover` deliver each derived layer *with its module structure intact*, so
the step is a linear solve rather than an opaque permutation action? That is a property of the extraction — the **same
object R-c-nonabelian builds** (`carrier` from `M`, non-abelian case) plus the carried `ForcingModel.bridge`. Resolving
it discharges the carried `hstep` **and** empties the corner in one move — not new debt. **Verdict: the corner is
plausibly empty-beyond-the-wall, reducible to already-carried objects, legal, and quasipoly-settled meanwhile.**

**✅ The extraction's structural core (L1+L2+L3) LANDED (2026-07-24, `ChainDescent/GaugeLayer.lean`, axiom-clean, in
the gate).** Scoped into four bricks; **L1–L3 built, L4 carried**:
- **L1** the gauge's derived tower **decomposes coordinatewise** — `derivedSeries (ι → G₀) k = ∏ᵢ derivedSeries G₀ k`
  (`derivedSeries_pi_const`, via Mathlib `commutator_pi_pi_of_finite`; `mem_derivedSeries_pi` the per-gadget form) =
  *each layer is a free module of rank `|gadgets|`*, so each `of_solvable_tower` step is a per-coordinate **linear**
  problem, not a `|G₀|^{|ι|}`-coset search (why `kerF2`'s one Gaussian pass generalizes up the tower).
- **L2** the layer is **abelian** (`commutator_mem_derivedSeries_succ`: commutators drop a level ⟹ `A_k = D_k/D_{k+1}`
  abelian) with coefficient group `layerCoeff G₀ k = Abelianization ↥(derivedSeries G₀ k)` (a `CommGroup`); the
  product layer projects coordinatewise onto each local `A_k` (`layerProj`/`layerProj_surjective`) = the `ι → A_k`
  free-module coordinate structure.
- **L3** the per-layer solve is **linear**: `kerF2` upgraded from `AddSubgroup` to a genuine `Submodule (ZMod 2)`
  (`kerF2Submodule`, via `kerF2_smul_mem`) — a subspace of the free `F₂`-module, the concrete `A_0 = ZMod 2` field
  instance of "each layer is an `A_k`-submodule of `ι → A_k`, solved by Smith/Gaussian."
- **L4** (stays **CARRIED**, shared with `ForcingModel.bridge`) `Recover` produces the layers as explicit linear
  systems *from the graph*. L1–L3 build the target structure; L4 plugs the graph in — the honest remaining gap.

---

## 4. The crux — one lemma, three faces (and the two thresholds)

All the open weight is one statement. It has three equivalent-looking faces; establishing their coincidence is
itself part of the work, so treat them as *three attack angles on the same crux*, not as a proven equivalence.

**Γ, and the two steps `mp7` forces apart.** The object all three faces range over is the **gauge group Γ** — the
WL-invisible *local* symmetry, separated from the visible base symmetry `Aut/Γ` (definition scope: §4a; Γ **is not**
`Aut(G)`). Getting Γ right is **two distinct steps**, which the Fano multipede `mp7` forces apart:
- **Recover (isolation) — group-general.** Structurally extract the gauge *relation*, excluding the base. On `mp7`
  this yields `Z₂³` (the [7,3,4] simplex code), **not** `|Aut| = 1344`; the non-solvable base `PGL(3,2)` never
  enters the system. On S₃/D₄ it yields the genuine non-abelian relation. So isolation is **group-general**, and it
  is what Faces A/B/C all attach to.
- **Solve (canonize Γ) — the threshold split.** Abelian → Smith/`ker H` (built); solvable → coset-enumeration
  (new); non-solvable → wall.

⚠ **Correction to an earlier framing.** The recovered *F₂* system is the abelian shadow of the **solve** only — the
**recover** / isolation is group-general (that is why C3 passes the `mp7` test where a naive `Aut`-based Γ returns
1344). Faces A/B are the *abelian* solve; Face C is the *solvable* solve; all three sit on the same group-general
recovered Γ.

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
**string-canonization under `Γ`** — poly for bounded-degree solvable gauge (`Γ_d`, Luks 1982). **§3a sharpens this
from a hedge to a theorem on the family that arises:** the recovered `Γ ≤ G₀^m` (product of the fixed local group), so
`Γ ∈ Γ_{μ(G₀)}` and Luks is `n^{O(μ(G₀))}` — genuine poly whenever `G₀` is bounded (all fixed constructions +
CFI/Lichter, `μ = 2`). The residual **plausibly poly** (`cameron-entanglement.md:124`, not classical) is confined to a
*growing* non-abelian solvable local group with unbounded cyclic sections (§3a). This is the **solvable threshold**,
strictly weaker (more permissive) than Faces A/B: abelian ⊊ solvable. Faces A/B secure the *linear* sub-seal; Face C
secures *poly-completeness*, which is the actual deliverable.

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

## 4a. The gauge group Γ — definition scope (C3 operative, 2026-07-24)

Γ is the WL-invisible local gauge whose **solvability** decides whether force fires — **not** `Aut(G)`. Three
acceptance tests pin it: **(1)** abelian CFI → `Γ ≅ ker H`; **(2)** Schurian cell → `Γ = 1`; **(3)** `mp7` → `Z₂³`,
**not** 1344. Test (3) is the *discriminating* one — it demands the non-solvable base `PGL(3,2)` be excluded;
CFI/Schurian have trivial base and so cannot catch a bad isolation, `mp7` can (it is the reason isolation, not
solve, is the crux of well-definedness).

| candidate | against the tests | verdict |
|---|---|---|
| **C1: Γ = `Aut(G)`** | fails all (`mp7` → **1344**; Schurian `Aut` large) | **Γ ≠ Aut — dead** |
| **C2: intrinsic fibre-fixing subgroup of `Aut`** (extraction-free) | pass *iff* the intrinsic **fibre structure** is defined — and that isolation is **open** | **deferred** — the completeness ideal (theorem-clean, no `Recover`), parked with its open fibre-isolation problem |
| **C3: structurally-recovered gauge relation** (`Recover`'s `M`) | **passes all three now** — isolation is group-general (§4 recover step; `mp7` → `Z₂³`, S₃/D₄ → genuine non-abelian relation) | **OPERATIVE** |

**Operative Γ = C3**, layered **isolate (group-general) → solve (abelian/solvable)** (§4). **Why not the naive
intrinsic C2:** the gauge/base separation `mp7` stresses is done "for free" by the linear/structural algebra of
`Recover` (kernel = gauge, base = symmetry *of* the code, not *in* it), whereas a purely-intrinsic Γ must define the
fibre structure that realizes the same split — the genuinely open piece. **C2 is the completeness upgrade** — pursue
only if intrinsic fibre isolation resolves; **not needed to reach the solvable threshold.**

The one liability C3 carries: `Recover`'s faithfulness is *structural-but-not-yet-theorem* (recognition-free —
stronger than the empirical F₂ `ForcingModel.bridge` — but still an extraction). That is exactly what the **bridge
lemma** to Tier A's `HolonomyNontrivial` discharges (§5): the completeness-clean holonomy is the theorem-clean
witness that the recovered isolation is faithful.

---

## 5. The attack plan (three tiers)

**Tier A — the localization spine (provable now; non-circular; standalone value).**
1. ✅ **LANDED** — `matroid.md:146-151` base lemma = `GaugeComplex.refineStep_ne_iff_exists_count_ne` (+
   `count_signature_eq_card`), `ChainDescent/GaugeComplex.lean`, axiom-clean, in the gate.
2. ✅ **LANDED (flatness)** — equitability ⟹ local exchange exists = `GaugeComplex.localExchange_of_equitable`
   (+ `refineStep_eq_iff_forall_card_eq`, `nbhdClass`), axiom-clean, in the gate.
3. ✅ **LANDED (holonomy)** — `IsColAut`/`SameOrbit`/`LocallyFlat`/`HolonomyNontrivial` +
   `sameOrbit_imp_locallyFlat` (equivariance, the real content) + `holonomyNontrivial_iff_diff_orbit`. Non-vacuity
   external (WL lower bound). **Tier A spine complete.** Remaining: mixed-cell = non-Schurian (a labelling of the
   locus, cheap) folds into Tier B.
4. Core/decoration split as a theorem: decoration ⟹ zero independent holonomy ⟹ the core is `Recover`'s `M`.
   Re-derive `Recover` as a *statement about WL-stable graphs*, not just an algorithm.
> ⚠ **Do NOT put "linear" in the base case.** The induction produces the *complex*; linearity/solvability is a
> property of the *holonomy group*, proved separately (Tier B) or the whole thing is circular (assumes claim #2).

**Tier B — the crux (`forceSolvable`), on Γ = the recovered gauge relation (C3, §4a), split by the *solve*
threshold. NOT by WL-counting** (§3(i): WL is blind to Γ's structure).
- ✅ **Bridge (LANDED)** — `holonomy_iff_gauge` (`GaugeBridge.lean`): `HolonomyNontrivial u v ⟺ Γ-orbit u v ∧
  ¬SameOrbit`, against the abstract `GaugeContract` (Γ's `faithful` carried, `Recover` discharges it);
  `gaugeContractMax` = non-vacuity witness. The Tier-A→Tier-B connector.
- **Isolation** — the group-general structural `Recover` (§4a); classify Γ by extraction + Albert/isotopy
  (`Probe_ExtractionDiscriminator` is the template).
- ✅ **Abelian branch (LANDED)** — `GaugeAbelian.lean`: `isSolvable_of_carrier_comm` (commutative gauge ⟹
  solvable — abelian is the trivial base of the target); F₂ reuse of `RigidSolveF2` — `kerF2 H` = the abelian gauge
  as `ker H` (abelian by construction), `isRigidF2_iff_kerF2_eq_bot` (`IsRigidF2 ⟺ trivial gauge` = "rigid = no
  gauge freedom"), `rigid_unique_solve` (the built determinacy as the branch's solve). Carried: `carrier ≅ kerF2 H`
  (the `Recover`/`ForcingModel` correspondence). Faces A/B; `matroid.md:463-481` §8.4's Tier-2 detector.
- ✅ **Solvable branch — reduction skeleton (LANDED)** — `GaugeSolvable.lean`: `of_solvable_tower` (a gauge
  capability `P` holding for `⊥` and preserved across each derived-series step `P ⁅H,H⁆ → P H` holds for the whole
  solvable gauge, by downward induction on the terminating derived series `⊤=D₀⊇…⊇Dₙ=⊥`) + `of_solvable_abelian_base`
  (P for every abelian subgroup + the step ⟹ P ⊤ = **the solvable branch reduces to the abelian branch**). ⚠ the
  per-level step `hstep` = **Luks's reduction** (Luks 1982; Babai–Luks 1983), carried. **Poly scope (honest):**
  settled for `Γ_d`/bounded-order; **plausibly poly** for general unbounded solvable (`cameron-entanglement.md:124`),
  not a classical theorem. The skeleton is proved and makes no poly claim. Face C.
- **else → the wall** (growing non-solvable Γ, no constructible witness). Completeness lever: route-(ii) "no
  non-abelian fusion survives into a rigid medium" (`remaining-work.md:734`), evidenced by S₃/D₄ tameness.

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

## 5a. C3 `Recover` — scope (2026-07-24)

`Recover` is the structural, recognition-free extraction that produces the gauge group Γ (C3) from the WL-stable
coloured graph. Discharging it turns the W2 Tier-B chain from *carried* to *theorem-clean*. It must discharge two
carried obligations: **(1)** `faithful` — the recovered Γ's orbits are exactly the local-flatness classes; **(2)**
`carrier ≅ kerF2 H` — the abelian-branch correspondence.

| piece | content | status |
|---|---|---|
| **R-a — gauge isolation** | pick the gauge cells, exclude the base (the `mp7 → Z₂³` test) | ✅ **LANDED** (rigid-regime form, below) |
| **R-b — the forcing bridge** | recovered `M` faithfully models WL-flatness (1-WL forcing = unit-prop/kernel on `M`) | **carried** — this *is* `ForcingModel.bridge`, already carried by the rigid-seal track; **C3 adds no new carried obligation, it inherits it** |
| **R-c — gauge-group construction** | build `carrier` from `M`: abelian = `kerF2` (**built**, `GaugeAbelian`); non-abelian = the recovered gauge `Γ ≤ (ι → G₀)`, its solvability + reduction to the abelian branch | abelian **built**; non-abelian **✅ BUILT** (`GaugeNonabelian`, below) |
| **R-d — `faithful`** | orbits(Γ) = flatness classes | **composition** of R-a+R-b+R-c; ≈ the forcing bridge |

**Key finding.** `faithful` (R-d) ≈ the forcing bridge, so C3 is dischargeable **modulo the same bridge the
rigid-seal linear ① is already modulo** — not an independent liability. The genuinely-new *provable* work is R-a
(isolation) and R-c-nonabelian.

**✅ R-a LANDED — and it REFINED the scope (`ChainDescent/GaugeIsolation.lean`, axiom-clean, gate green).** The
"gauge vs. base classifier on the full graph" is **not** what force needs: force sees the residue *after* consume
peels the base — a **rigid** residue — and in the rigid regime isolation is automatic. `IsRigid` (`Aut = 1`);
`sameOrbit_iff_eq_of_rigid` (`SameOrbit` collapses to equality); `holonomyNontrivial_iff_flat_ne_of_rigid` (nontrivial
holonomy = a locally-flat pair of **distinct** vertices ⟹ **gauge cells = non-singleton flatness classes**);
`carriesGauge_iff_exists_holonomy_of_rigid`. **⟹ the `mp7 → Z₂³` split is the two-seals INTERLEAVING** (consume takes
`PGL(3,2)`, force sees the rigid `Z₂³` residue), **not** a Recover-internal classifier — which also explains why the
deferred **C2 fibre-isolation is unnecessary for force**: rigidity does the isolating. **Next in R-c/R-d:** wire
`carrier ≅ kerF2` on the rigid residue (thin, once R-a picks the cells); R-b stays carried (shared).

**✅ R-c-nonabelian LANDED (2026-07-24, `ChainDescent/GaugeNonabelian.lean`, axiom-clean, in the gate).** The
group-theoretic skeleton of §3b's A3, on the §3a structural fact *the recovered gauge is a subgroup of a product
`Γ ≤ (ι → G₀)` of the fixed local gadget group* (CFI's `Z₂^β ≤ Z₂^{|E|}`): **`isSolvable_pi`** (product of a fixed
solvable `G₀` is solvable — **degree-independent**, one uniform derived length via `map_derivedSeries_eq` at each
projection, so it sidesteps the Luks-`Γ_d` hedge, §3a) ⟹ **`isSolvable_recoveredGauge`** (any recovered `Γ` solvable) +
**`isSolvable_gaugeCarrier`** (its image in `Sym V`, a `GaugeContract.carrier`, solvable); **`isSolvable_extension`**
(solvable-by-solvable = the A3 "two abelian layers" core); **`recoveredGauge_reduces_to_abelian`** (THE deliverable —
wiring into the built `of_solvable_tower`: the non-abelian gauge reduces to the abelian branch); **`map_eval_derivedSeries`**
(the §3b *linearity-of-each-layer* evidence — the `n`-th derived layer is coordinatewise `G₀`'s). Non-vacuity:
`S₃ = Perm (Fin 3)`, genuinely non-abelian (`perm3_not_comm`) and solvable (`isSolvable_perm3`). ⚠ **The one carried
gap is unchanged (§3b):** that `Recover` delivers each derived layer *with its module structure intact* (so the tower
step is a linear solve) — the extraction property, shared with `ForcingModel.bridge`. This module is the skeleton the
extraction plugs into; it does not close that gap.

---

## 6. Falsifier ledger & standing evidence (fresh-reader)

| construction | what it kills / shows | not a witness because | ref |
|---|---|---|---|
| **Lichter CFI-over-`Z_{2^k}`** | "F₂ is the only obstruction" — FALSE | still **linear** (varying ring) | `rigid-seal.md:232`, `ir-blindspot-solver.md:1067` |
| **S₃/D₄ group-CFI** (rigidified) | "rigid ⟹ abelian" — FALSE (rigid non-abelian exists) | **solvable ⟹ poly** (coset CSP) | `project_nonabelian_cfi_witness` memory |
| **Dihedral / Heisenberg** (growing) | non-abelian structure stays accessible & tame with growth | **each *fixed* member is genuine `Γ_d`-poly (§3a); hedge only in the `p → ∞` limit** (unbounded cyclic section, not `Γ_d`, not Smith) | ibid. §group-varying probe; §3a |
| **`mp7` (Fano multipede)** | **the isolation test**: recover yields `Γ = Z₂³` (F₂ gauge), **not** `\|Aut\| = 1344` | base `PGL(3,2)` (non-solvable!) is **symmetry**, not gauge — excluded by `Recover` | `deepen-supply.md:120-124`, `00-START-HERE.md:138` |
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

**The built W2 modules (this track, 7):** `GaugeComplex` → `GaugeBridge` → `GaugeAbelian` → `GaugeSolvable` →
`GaugeIsolation` (R-a) → `GaugeNonabelian` (R-c-nonabelian) → `GaugeLayer` (extraction L1–L3) — all axiom-clean, in the
gate. **The read-order + one-line-each + what is proved vs carried + the ▶▶ LOGICAL STATE note is the HANDOFF block at
the top of this doc's STATUS** — start there. What follows are the rigid-seal objects this track *connects to / carries*.

**⚠ Theorem-index state (`PublicTheoremIndex.md`, refreshed 2026-07-24):** all 7 Gauge modules' declarations are now
*indexed* (rows present, discoverable). `GaugeLayer` (the frontier, L1–L3) has full descriptions; the other 6 Gauge
modules carry rows with **blank (`—`) descriptions** — a pending *description pass* (`scripts/GenerateTheoremIndexes.py`
+ `theorem-index-maintenance.md`), not a gap in the proofs. Full prose for those lives in the module docstrings + the
HANDOFF read-order above.

**Rigid-seal objects the crux reduces onto (downstream connection):**
- `ChainDescent/RigidSolveF2.lean` — `IsRigidF2` (trivial kernel = rigid), `unique_solution_of_rigid`, rowspace-only
  rigidity (`dotP_zero_rowspace`). The abelian-threshold seal — reused by `GaugeAbelian`.
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
