# Chain descent — harvest-window development journal (archived)

> **Archived 2026-06-02.** This is the dated, exchange-by-exchange development log
> (old §6.1–§6.13) of the harvest-window lemma, moved out of the live doc
> [`../../chain-descent-harvest-window.md`](../../chain-descent-harvest-window.md)
> when that doc was hoisted to a clean statement form. The **conclusions** are distilled
> in the live doc's STATUS block and §6 summary; nothing here is load-bearing. It is kept
> for the record of *how* the screen `D1∨D2`, the structural/discretizing two-mode split,
> the sequential-screen fix (the `CFI(Kₘ)` flat-screen escape), the F1/F2 definitional
> fixes, and the Phase-0 / Phase-1 anchors were reached. Section numbers below are the
> original §6.x numbering.

---

## 6. Validation plan — the designed first test

Before any formalization, **state the lemma against the existing Lean objects and check it
specializes to the two proved instances.** This is decisive either way.

1. **Schurian schemes** — `recoverableByDepth_scheme` (depth-1 witness at the decision node). Check it
   is the lemma with **case (c) terminating at depth 1** (base 1: one individualization makes cells =
   orbits — *non-singleton*, the structural mode; see §6.1 result). **✓ DONE — §6.1.**
2. **Odd-degree CFI** — `theorem_1_HOR_cfi_oddDeg` (`k ≤ baseSize`). Check it is the lemma with
   **`b(g) = baseSize`** (the gadget group's discretizing depth). **✓ DONE — §6.2** (discretizing mode;
   bound is class-specific, as anticipated).

Outcomes:
- **Both fall out** ⟹ the induction is the general tool; the per-class proofs are corollaries; proceed
  to formalize the induction-form lemma.
- **One resists** ⟹ the resisting case names the missing tool exactly (e.g. the CFI proof's structure
  doesn't expose `base(g)` — then we learn the bound needs a different handle than treewidth). Record
  it as a gap entry here and re-plan.

Either outcome is a win and neither commits to the stuck σ-coherence model.

> **Both cases done (2026-06-01).** Both specialize at the conclusion level (`RecoverableByDepth`), and
> together they reveal the **two-mode structure** (§6.3): the conclusion form is right and already
> formalized; the open content is the class-agnostic trichotomy *skeleton* plus a per-node **mode-split**
> (structural witness vs discretizing bound). The scheme refined the firing condition to `CellsAreOrbits`
> (§6.1); CFI confirmed the discretizing-mode bound is class-specific (§6.2). The concept survives and is
> sharper. **Next: formalize the trichotomy skeleton** (`recoverableByDepth_of_findable`), with the two
> instances as its mode anchors.

> **⚠ Naming reconciliation — read before §6.4–§6.7 (historical narrative).** The provisional names used in
> the planning sub-sections below were **built under different final names** (see §6.10–§6.12 for the as-built
> state). Map: the single planned **`recoverableByDepth_of_findable`** split into the **bound-free `Findable`**
> (inductive *classification*, §6.10) plus the **bound-carrying `FindableWithin` + `recoverableByDepth_of_findableWithin`**
> (the *non-vacuous* soundness, §6.12 — the flat `∃ b` form was vacuous). The provisional flat screen
> **`Findable := (∃ b, VisiblyRecoverable …) ∨ ResidualAbelian`** became the **inductive `Findable`** (sequential
> `recovered`/`abelian`/`step`, §6.10–§6.11). The provisional **`recoverableByDepth_of_findable_visible`** is
> subsumed by the inductive's `recovered`/`step` legs; `recoverableByDepth_of_visiblyRecoverable` is the retained
> explicit-chain D1 lemma. Below, read those provisional names as their built counterparts.

### 6.1 Case 1 — schurian scheme: RESULT (2026-06-01)

**Verdict: specializes cleanly at the conclusion level; the test *corrects the firing condition*.**
Productive middle outcome — the conclusion form is right (and already formalized), but the mechanism
as stated in §1/§3 was too narrow.

**Conclusion aligns, and the Lean home already exists.** The harvest-window depth bound *is*
`RecoverableByDepth adj P b := ∃ S, S.card ≤ b ∧ CellsAreOrbits adj P S`
([`CascadeOracle.lean:631`](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean)), and
`recoverableByDepth_scheme` is its **`b = 1`** instance (witness `S = {v}`). The trichotomy induction
on a rank-2 / `|J|=1` scheme reproduces it exactly: the root is one cell = one orbit
(vertex-transitive) ⟹ case (a) picks rep `v`; the residual `Aut_v` satisfies `CellsAreOrbits` at depth
1 (`theorem_2_HOR_concrete_rank_two_J_singleton`). Forced node `= {v}`, recoverability depth
`b(g) = 1`. Matches the proved theorem.

**The refinement the test forces** (a sharpening, not a failure):

1. **Firing condition is `CellsAreOrbits`, not "footprint singletonizes."** The scheme recovers at
   depth 1 with **non-singleton cells** that *coincide with orbits* — the orbit witness comes from the
   scheme's transitivity, not from the cells collapsing to singletons. So §1/§3's "all-singleton
   footprint = unique candidate" is only **one of two recovery modes**:
   - **discretizing mode** — deepen to singletons; `CellsAreOrbits` holds for free
     (`cellsAreOrbits_of_discrete`). This is CFI's route and the linear oracle's all-singleton-footprint
     path.
   - **structural mode** — `CellsAreOrbits` at coarse, *non-singleton* cells; the orbit witness is built
     from structure (`orbitPartition_swap_of_twin` for twins/modules; scheme transitivity for
     `recoverableByDepth_scheme`).

   The unifying firing condition is **`CellsAreOrbits adj P S`** — already the project's localisation
   predicate (`orbitRecoverableAt_iff_cellsAreOrbits`) — with "footprint singletonizes" as the
   discretizing special case. §1/§3 should read `CellsAreOrbits`, not singletonization.

2. **The depth is the recoverability depth `b(g)`, not the support `|S|`.** For the scheme `b = 1`
   while the *element* support can be large. So §2's "≤ `base(g)` ≤ `|S|`" should be read: the bound is
   the **recoverability depth** — the least `|S|` with `CellsAreOrbits adj P S`, which
   `RecoverableByDepth` already names. Support size is a loose upper envelope, not the quantity.

**Consequence for the Lean target.** Because the harvest-window *conclusion* is `RecoverableByDepth`,
both anchors already exist axiom-free (`recoverableByDepth_scheme` at `b=1`, `recoverableByDepth_cfi`
at `b=cfi_depth_bound`). The general lemma's only new content is producing `RecoverableByDepth adj P
(b(g))` for an arbitrary *findable* `g` via the trichotomy induction; the per-class theorems are the
proved base cases it must reproduce. The Lean target is therefore sharp: a class-agnostic
`recoverableByDepth_of_findable` whose hypothesis is the screen (§3) and whose two existing instances
are the discretizing (CFI) and structural (scheme) recovery modes.

### 6.2 Case 2 — odd-degree CFI: RESULT (2026-06-01)

**Verdict: conclusion aligns; this is the *discretizing* mode, and the bound `b = baseSize` is
genuinely CFI-theory content — the §6 "doesn't expose base(g) generically" outcome, *expected* for
this mode and not a resist of the concept.**

- **Conclusion aligns.** `recoverableByDepth_cfi : RecoverableByDepth adj P (cfi_depth_bound h)` with
  `cfi_depth_bound h = h.baseSize` ([`CFI.lean:556`](../GraphCanonizationProofs/ChainDescent/CFI.lean)) —
  the `b = baseSize` instance. Same `RecoverableByDepth` conclusion as Case 1, different `b`.
- **Mode = discretizing, and it shows in the type.** CFI's residual is the elementary-abelian gadget
  group `Z₂^β`, whose intermediate 1-WL cells are *strictly coarser than orbits* (exactly why CFI
  defeats 1-WL). So `CellsAreOrbits` holds **only at discreteness**: `theorem_1_HOR_cfi_oddDeg` carries
  a **`Discrete (warmRefine …)`** conjunct ([`CFI.lean:3237`](../GraphCanonizationProofs/ChainDescent/CFI.lean))
  and recovery is `cellsAreOrbits_of_discrete`. Contrast Case 1: `orbitRecoverable_scheme` has **no
  `Discrete` conjunct** — *the mode split is visible in the theorem signatures.*
- **The bound needs the class theory.** `b = baseSize` = one seed per gadget = the discretizing depth.
  The proof that `allSeeds` (size `baseSize`) discretizes within ~5 refinement rounds is a
  per-vertex-type cascade analysis (`refineStep_subset_intra_gadget_S_round5` etc.; case-split
  subset/endpoint × subset/endpoint, [`CFI.lean:3038`](../GraphCanonizationProofs/ChainDescent/CFI.lean)) —
  CFI combinatorics, **not** derivable from a generic support-induction. The induction supplies the
  *skeleton* (consume the gadget generators); the *number* (`baseSize`) is CFI-specific.

### 6.3 The emerging pattern (watch-item for the general theorem)

Cases 1 and 2 together give the shape `recoverableByDepth_of_findable` should take — the reusable
structure for the larger theorem:

- **`b(g)` = recoverability depth** (least `|S|` with `CellsAreOrbits adj P S`). It is *not* the support
  `|S|` (Case 1: scheme support can be large, `b=1`) and *not* uniformly the residual-group base (Case 1:
  `S_n` base is `n−1`, yet `b=1`). The earlier "≤ base(g) ≤ |S|" (§2) should be read as this
  recoverability depth.
- **Two recovery modes certify `CellsAreOrbits`; the depth depends on which fires:**
  - **structural** — non-singleton cells = orbits, witness from structure (`orbitPartition_swap_of_twin`,
    scheme transitivity). Fires **early**, `b` small, **no `Discrete`**. (scheme; twins/modules)
  - **discretizing** — cells = orbits only at discreteness, `cellsAreOrbits_of_discrete`. `b` = the
    discretizing depth (≈ residual-group base). (CFI)
- **The trichotomy induction (§2) is the universal skeleton — independent of mode.** Consume the residual
  structure one generator per (a)/(c) step. The modes differ *only* in the **per-forced-node witness**:
  a structural lemma vs a discretizing-depth bound.
- **The mode is *not* the screen (corrected by W2 — §6.4.1).** Mode (structural/discretizing) is an
  orthogonal *recovery-depth* axis governed by point-stabilizer granularity; the screen is the seal's
  **`D1∨D2`** (visibility/uniqueness), governed independently. The mode-disjunction is exhaustive and
  therefore *vacuous* as a screen. Earlier "structural≈A / discretizing≈B" was a coincidence of the two
  diagonal data points — see §6.4.1 for the off-diagonal (GRR = D1 + discretizing).

So the general theorem is a **mode-split over a common induction**: prove the trichotomy skeleton once
(class-agnostic), then discharge each forced node by *either* a structural witness *or* a
discretizing-depth bound — each class-specific, but slotting into one frame. The two proved instances
are the modes' anchors (`recoverableByDepth_scheme` structural / `recoverableByDepth_cfi` discretizing).
**This mode-split is the structural handle to carry into the larger-theorem work.**

The skeleton's *signature* is therefore fixed by W1: hypothesis = **the screen `D1∨D2`** (a structural
predicate, *not* "recoverable" — which would be circular), conclusion = `RecoverableByDepth adj P (b(g))`.
The mode-split lives *inside* the proof (the per-forced-node discharge), not in the statement:

```
  recoverableByDepth_of_findable :
    (a symmetry exists)  →  (D1 ∨ D2)  →  RecoverableByDepth adj P (b g)
  -- proof: trichotomy induction (class-agnostic skeleton);
  --        each forced node discharged by a structural witness OR a discretizing bound.
```

`¬(D1∨D2)` is *not* in the statement — it is `¬screen`, exported to leg C, never an input here.

### 6.4 Working through the screen (plan, 2026-06-01)

The screen (§3) is the load-bearing hypothesis and the seam to the wall, so it is worked through before
the trichotomy skeleton is formalized (the screen reshapes the skeleton's *hypothesis*). The reasoning
that surfaced this:

**The screen is *not* at σ-coherence vacuity risk — but it *is* the wall.** σ-coherence was
machine-checked false in its operative regime; the screen is *true* for findable classes (CFI, schemes)
and *false* for Johnson (correctly — the flag). Both sides are populated. The danger is the opposite:
its hard direction ("not-Johnson ⟹ recovers in poly depth") *is* the open core. **Discipline: never try
to prove the screen decidable** (that is GI∈P). Operationalize the positive side, export the negative.

**The reshaping realization: the screen = the seal's `D1 ∨ D2`.** Conditioned on "a symmetry exists"
([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)), the screen is exactly the
seal's discriminator disjunction:
- **`D1`** — unconditional (exposable by symmetry-only individualization within poly depth, no real
  decision committed) — leg A / cascade.
- **`¬D1 ∧ D2`** — hidden but unique-candidate (one branch exposes a unique twist ⟺ abelian) — leg B /
  linear.
- **`¬D1 ∧ ¬D2`** — `¬screen` — leg C / Cameron — *the flag, exported as data.*

This is negation-complete by construction (`D1 ∨ (¬D1∧D2) ∨ (¬D1∧¬D2)` is a tautology), so **defining the
screen as `D1∨D2` makes exhaustiveness free** — no risk of a fourth species leaking through. The
harvest-window lemma and leg C are the **two sides of one screen**.

**Open gating check (this is W2, below): does the recovery *mode* (§6.3) coincide with the seal
*discriminator*?** The correlation on the two data points is suggestive — scheme = structural + `D1`,
CFI = discretizing + `¬D1∧D2` — but *mode* (cells=orbits early vs only-at-discreteness) and
*discriminator* (`D1` vs `¬D1∧D2`) are a-priori **different axes**. The leak-risk: discretizing-mode
recovery could occur *within* `D1` (an unconditional symmetry whose cells coincide with orbits only
deep — and the cascade oracle's own recursion *does* deepen to discreteness). If so, mode ≠ leg, and
the screen must be defined by `D1∨D2` (the negation-complete axis), **not** by the mode disjunction
(which would then be non-exhaustive). Verifying this is the gate before the doc's §3/§6.3 framing is
committed.

**The four workstreams:**
- **W1 — define the screen as `D1∨D2`, negation-complete.** **✓ DONE — §3 rewritten** (screen = seal
  discriminator, modes demoted to an orthogonal recovery-depth axis); §2 hypothesis = the screen; §6.3
  fixes the skeleton signature `(symmetry exists) → (D1∨D2) → RecoverableByDepth adj P (b g)`.
- **W2 — pin (or refute) the mode ↔ leg correspondence** (the gate above). **✓ DONE — §6.4.1: REFUTED
  as an identity; the modes are orthogonal to `D1`/`D2`. This validates defining the screen by `D1∨D2`
  (W1), not by the modes.**
- **W3 — operationalize the positive side as the budget** (attempt-certify, flag on exceed; sound by
  construction). Iso-invariance is then **free**: `verdictIsoInvariant_of_complete`
  ([`CascadeOracle.lean`](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean) §C.3 obligation 3)
  derives flag iso-invariance from soundness + completeness + recoverability.
- **W4 — the negative side = the leg-C inversion**, co-developed: `¬screen` produces a non-collapsing
  residual = the leg-C fingerprint; prove `fingerprint ⟹ Cameron` (Jordan, Mathlib). Export `¬screen`
  as named data (the orbit-recovery doc's forward-compat plea).

**Honest open risk:** completeness ("not-Johnson ⟹ poly-recoverable") is the wall — *not* proved inside
the lemma; punted to leg C's characterization. The lemma proves only `D1∨D2 ⟹ recovered`. The "poly" in
poly-`b` is the budget `B(n)`; a findable-but-super-poly-depth class would be wrongly flagged, but within
"not-Johnson" that is the cascade/T-C openness, conjectured not to arise.

### 6.4.1 W2 — mode ↔ leg correspondence: RESULT (2026-06-01)

**Verdict: REFUTED as an identity. Mode and leg are orthogonal axes — which *validates* defining the
screen by `D1∨D2` (W1) and forbids defining it by the modes.**

Precise definitions used: **`D1`** (unconditional) = consumable without committing a real decision
([deferred-decisions §5](./chain-descent-deferred-decisions.md)); **`D2`** = among `¬D1`, one branch
exposes a *unique* candidate twist ⟺ abelian ([calculator §6](./chain-descent-calculator.md)).

- **`structural ⟹ D1`** holds: non-singleton cells = orbits means the orbit is refinement-*visible*, i.e.
  exposed by symmetry-only individualization. (one direction)
- **`discretizing ⟹ ¬D1` FAILS.** Witness: a **GRR** (graphical regular representation) — `Aut(G)` acts
  *regularly* (transitive, trivial point-stabilizer). Individualizing any `v` is symmetry-only (transitive
  ⟹ orbit rep, *no* real decision) so it is **`D1`** — yet `Aut_v` is trivial, so orbits at `{v}` are
  singletons and `CellsAreOrbits` holds only via `Discrete`: the **discretizing** mode. So **`(D1,
  discretizing)` is populated** — the off-diagonal the two data points hid.

**The two axes, separated:**
- **Mode** (structural/discretizing) is governed by **point-stabilizer granularity**: non-trivial
  stabilizer → non-singleton orbits → structural (scheme); trivial residual stabilizer → must reach
  singletons → discretizing (CFI, GRR). It is a *recovery-depth/complexity* descriptor.
- **Leg / screen** (`D1` / `¬D1∧D2` / `¬D1∧¬D2`) is governed by **visibility + uniqueness**. It is the
  *negation-complete* boundary.

**The decisive consequence:** `structural ∨ discretizing` is **exhaustive** (a recovery set is discrete
or not) — so it equals "recoverable at *some* depth" = `recoverableByDepth_univ`, which is **vacuously
true** for every graph. The modes therefore **cannot** be the screen. The screen is the *poly-bounded*
recoverability, and the poly bound holds iff **`D1∨D2`** (cascade-visible OR hidden-but-unique). This is
consistent with the oracle taxonomy ("cascade + linear detect all symmetry except a hidden Johnson"):
`screen = D1∨D2`, `¬screen = ¬D1∧¬D2 =` hidden Johnson. **W1 (define the screen as `D1∨D2`) is therefore
mandatory; the modes are an orthogonal recovery-depth axis, not part of the screen's definition.**

### 6.5 Trichotomy skeleton — scoping + connector (2026-06-01)

**Scoping result: the skeleton's *induction* already exists.** `cascadeComposition_pathFixing` (Theorem
3a, [`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean), axiom-clean) is the common
induction: it chains per-layer `LayerStep`s from a base, the depths add (`cumulative_card_le`), and it
reduces the *whole* of recoverability to a single per-layer hypothesis **`hwit`** — "at every layer the
residual orbit map is realized by a path-fixing automorphism (support disjoint from the committed set)."
Its own doc-comment already isolates "the *existence* of those witnesses … the remaining deep work … the
sole hypothesis." So the trichotomy skeleton is **not** new induction to build; it is exactly this, with:
- layers `T_i, S_i` from the trichotomy (each (c)-step adds `S_i`); depth `b(g) = |T k| ≤ Σ|S_i|`;
- `hwit` = the **screen `D1∨D2` ⟹ path-fixing witnesses** bridge — the open content, = cascade-1b
  generalized (`CFILayerGadgetFlippable`), reached via the support trichotomy not σ-coherence.

**Built this step (axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green):** the
**connector** from Theorem 3a's `Discrete` output to the harvest-window's *stated* conclusion
`RecoverableByDepth adj P (b g)`:
- `recoverableByDepth_of_pathFixing_layers` — discrete-at-`T k` ⟹ `RecoverableByDepth adj P b` for any
  `b ≥ |T k|` (witness `T k`, via `cellsAreOrbits_of_discrete`). Lands the harvest-window conclusion on
  the existing machinery, isolating `hwit` as the sole residual.
- `recoverableByDepth_of_cascadeComposition_cfi` — the CFI corollary (via the Stage-3 gadget flips),
  conditional only on the (cascade-1b) per-layer cycle existence.

**Net.** `recoverableByDepth_of_findable` = `recoverableByDepth_of_pathFixing_layers` once `hwit` is
supplied by the screen. The remaining content is exactly two things, both deferred to dedicated steps:
(1) **define `D1`/`D2` as Lean predicates** (research-design — must be abstract/non-circular per the
seal); (2) **the bridge `D1∨D2 ⟹ hwit`** (= leg-A/B completeness / cascade-1b generalized — the open
core, exported to leg C on failure). The induction and the conclusion-connector are done.

### 6.6 D2 defined in Lean — abelian residual (2026-06-01)

Chosen def (option D2-A, abelian residual; D2-C/ConfigSwap rejected to avoid re-importing σ-coherence).
Built in [`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean), axiom-clean
(`[propext, Quot.sound]` — no `Classical.choice`), full build green:

- `ResidualAut adj P S π` — the residual-automorphism predicate (`IsAut ∧ P-preserving ∧
  FixesPointwise S`); `OrbitPartition = ∃ π, ResidualAut ∧ π v = w` (`orbitPartition_iff_residualAut`).
- **`ResidualAbelian adj P S`** (= **D2**) — any two `ResidualAut`s commute. Stated *relative to `S`*
  (CFI's full `Aut` is non-abelian; the residual `Z₂^β` after `S` kills `Aut(H)` is abelian).
- `residualAbelian_of_isBase` — **trichotomy base case**: a trivial residual is abelian (recursion
  bottom).
- `residualAbelian_mono` — **D2 is inherited down the chain** (`S ⊆ S'`: a subgroup of an abelian group
  is abelian) — the property the trichotomy induction needs to carry D2 deeper.

Note the negation is clean: `¬ResidualAbelian` = "∃ two non-commuting residual autos" = the non-abelian
residual, which (with `¬D1`) is the leg-C Johnson fingerprint — exported, not proved here.

### 6.7 D1 + the screen `Findable` defined in Lean (2026-06-01)

Chosen def (option D1-A, visible / cells=orbits chain to a base). Built in
[`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean), axiom-clean
(`[propext, Classical.choice, Quot.sound]`), full build green:

- **`VisiblyRecoverable adj P S₀ bound`** (= **D1**, *refined — see below*) — a **single-vertex** chain
  `T 0 = S₀`, each `T (i+1) = insert v (T i)`, with `0 < k` and `CellsAreOrbits adj P (T i)` at **every**
  step `i ≥ 1`, `|T k| ≤ bound`. The three conjuncts (`0 < k`, single-vertex increments, cells=orbits
  throughout) make D1 exclude **both CFI and Johnson**: `0 < k` kills the trivial-∅ recovery (cells =
  orbits holds vacuously at `∅` for any vertex-transitive graph — *Johnson included*), single-vertex
  steps forbid jumping to discreteness, and cells = orbits at every step forces the chain through depth
  1, where CFI and Johnson both fail.
  > **Refinement (this turn):** the earlier `IsBase`-to-a-base form over-shot the proved depth-1 scheme
  > recovery *and* admitted trivial-∅ (Johnson). The recovery-depth form above matches the proved
  > instance and the §6.3 `b(g)` framing. (3rd pass — early-stage, def-swapping is cheap.)
- `recoverableByDepth_of_visiblyRecoverable` — the **D1 leg** of the harvest-window lemma, *free* from
  the def (cells=orbits sits at step `k`). Faithful to "exposable by symmetry-only individualization."
- **`visiblyRecoverable_scheme`** — **the D1 instance check, validated in Lean**: a rank-2 / `|J|=1`
  schurian scheme satisfies `VisiblyRecoverable adj P ∅ 1` via the one-step chain `∅ → {v}`, with
  `CellsAreOrbits adj P {v}` supplied by the proved `orbitRecoverable_scheme`
  (`theorem_2_HOR_concrete_rank_two_J_singleton`). The D1 analogue of Cases 1/2, now a Lean theorem.
- **`Findable adj P S₀`** (= the **screen `D1 ∨ D2`**) — `(∃ bound, VisiblyRecoverable …) ∨
  ResidualAbelian …`. Bound-free (D1's depth quantified existentially) = the pure negation-complete
  classification; `recoverableByDepth_of_findable_visible` discharges the D1 disjunct's recoverability
  now, the D2 disjunct awaiting the bridge.

**Asymmetry recorded:** `D1 ⟹ recoverable` is *free* (def bakes in cells=orbits), so D1's genuine content
is the per-class instance check — **the scheme positive direction is done in Lean
(`visiblyRecoverable_scheme`)**.

### 6.8 D1 made multi-step — the correct (non-false-walling) form (2026-06-01)

A first pass closed the loop for a *one-step* def (cells = orbits at every step), but the iff it produced
(`VisiblyRecoverable adj P ∅ bound ↔ ∃v, CellsAreOrbits{v}`) revealed that form collapses D1-from-∅ to
**one-step (depth-1) recovery** — correct for rank-2 schemes (depth 1) and CFI (fails depth 1), but it
**false-walls depth-≥2-recoverable graphs** (the Johnson / Hamming *graphs* — recoverable DRGs, *not* the
hidden-Johnson *wall*): `¬D1` + non-abelian ⟹ wrongly `¬screen`. So the def was revised to the correct
**multi-step** form ([`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean), axiom-clean,
build green):

- **`VisiblyRecoverable`** (multi-step) — a single-vertex chain where each step is **symmetry-only** (the
  individualized vertex's cell at that node is a single `Aut`-orbit — no real decision), reaching
  `CellsAreOrbits` only at the **end**. Admits depth-≥2 recovery; still excludes CFI / hidden-Johnson
  (their intermediate cells are coarser than orbits, so symmetry-only steps can't be certified past depth
  1 — the chain gets stuck).
- `recoverableByDepth_of_visiblyRecoverable` — D1-leg, still **free**.
- **`cellsAreOrbits_empty_of_schurian`** — vertex-transitivity `CellsAreOrbits adj P ∅`, proved from
  `SchurianSchemeGraph.schurian_transitive` at the diagonal relation `R₀` (auto transported via
  `matching`, P-preservation via `hP_invariant`). The unblocker the previous turn flagged.
- **`visiblyRecoverable_scheme`** — re-proved in the multi-step def: the `∅ → {v}` step is symmetry-only
  by transitivity, with `CellsAreOrbits {v}` from `orbitRecoverable_scheme`. The scheme instance now sits
  in the *correct* def, no false-wall.

**Dropped** (one-step-specific, false under multi-step): `not_visiblyRecoverable_of_depth_one_fails`,
`visiblyRecoverable_empty_iff`. The multi-step **negative** (CFI / hidden-Johnson `¬D1`) has no clean
one-liner — it's "the symmetry-only chain gets stuck before recovery," needing CFI's coarser-cells fact —
and stays the isolated structural residual.

Both screen predicates and the screen are in Lean, with the scheme positive instance in the correct def.

### 6.9 SMOKE-TEST FINDING — the flat screen is INCOMPLETE (mixed graphs escape) (2026-06-01)

**Adversarial audit (look for findable-but-`¬D1∧¬D2`, non-Cameron). Found a real escape: `CFI(Kₘ)` for
`m ≥ 3`** — the *central findable example* — is `¬Findable adj P ∅` under the current **flat** `D1 ∨ D2`,
grounded entirely in existing facts:

- **Recoverable, not Cameron:** `recoverableByDepth_cfi` proves `RecoverableByDepth adj P (cfi_depth_bound)`.
- **`¬D1` (`¬VisiblyRecoverable adj P ∅`):** CFI recovers via the **discretizing** mode
  (`recoverableByDepth_cfi` carries the `Discrete` conjunct), *not* a symmetry-only chain; its intermediate
  cells are *strictly coarser than orbits* (CascadeOracle §"CellsAreOrbits … fails at generic intermediate
  nodes"), so no per-step symmetry-only certificate exists — the chain gets stuck.
- **`¬D2` (`¬ResidualAbelian adj P ∅`):** `Aut(CFI(Kₘ)) = Z₂^β ⋊ Sₘ`, and `Sₘ` (m ≥ 3) is **non-abelian**.

So `¬D1 ∧ ¬D2` on a recoverable, non-Cameron graph ⟹ **the seal's `¬(D1∨D2) = Cameron` claim fails for the
flat single-node reading.**

**Root cause — granularity.** CFI(Kₘ) is **mixed**: a *visible* `Sₘ` (a D1) over a *hidden abelian* `Z₂^β`
(a D2). The flat reading fails because `VisiblyRecoverable` demands **full** symmetry-only recovery (the
`Z₂^β` blocks it) and `ResidualAbelian` demands the **whole** residual be abelian (the `Sₘ` blocks it). The
seal's *intended* structure is **sequential** — deferred-decisions §1's "**consume symmetry first**":
consume the visible `D1` (`Sₘ`), *then* the residual `Z₂^β` is `D2`. That is exactly what the trichotomy
**induction** (`cascadeComposition`) does. So the seal is fine *read sequentially*; the **Lean `Findable`
instantiated the flat single-node reading, which is incomplete.**

**The fix (granularity — not yet done):**
1. **Re-granularize `D1` to per-decision** — "the *target cell* at this node is a single `Aut`-orbit"
   (one symmetry-only step available), **not** full recovery. `VisiblyRecoverable` (full symmetry-only
   recovery) should become the *derived* all-D1-steps special case.
2. **Make `Findable` per-decision-along-the-descent**, with `cascadeComposition` doing the consume-visible-
   then-classify-residual sequencing — so mixed graphs are covered.
3. Apply `ResidualAbelian` (D2) to the **post-D1-consumption residual**, not the `∅`-residual.

**Bounds are fine** (numeric): D1's `bound ≤ n` is polynomial; mixed-case depth `|Sₘ| + |Z₂^β| ≤ n`. The
issue is **structural (flat vs sequential), not numeric**.

**Side-insight:** this shows the induction (`cascadeComposition_pathFixing`) is **load-bearing for
completeness**, not just plumbing — it does the visible-then-hidden sequencing the flat screen can't
express.

**RECOMMENDATION:** re-granularize `Findable`/`D1` (above) **before** building the D2 bridge on top of an
incomplete screen. This is the top open item.

---

### 6.10 The CONFIRMED sequential screen — precise D1/D2 and soundness audit (2026-06-01)

Acting on §6.9, with the goal of **fixing the definitions before three legs of proof (D1, D2, Cameron
contrapositive) depend on them.** The audit confirms the screen is logically sound and exhaustive
**modulo one precision fix to D2** (a non-triviality guard). Grounded in the real predicates:
`CellsAreOrbits := ∀ v w, same-cell → OrbitPartition` and `OrbitPartition := ∃ residual-aut π, π v = w`
(so `orbit ⊆ cell` is free via `subset_warmRefine`; thus `∀` same-cell `u`, `OrbitPartition v u` ⟺
`cell(v) = orbit(v)`).

**The precise definitions.**

- **D1 — per-decision `SymmetryOnlyStep adj P S v`:** `v`'s cell is **non-singleton** *and* a **single
  orbit** — `(∃ u ≠ v, same-cell u v) ∧ (∀ u, same-cell u v → OrbitPartition adj P S v u)`. The
  non-singleton conjunct is **load-bearing**: without it, every singleton cell satisfies the orbit
  condition vacuously (`u = v`), so `∃v SymmetryOnlyStep` would be trivially true and the recursion
  could spin on no-op steps. This is the step-condition already inside `VisiblyRecoverable` (Cascade.lean
  lines 528–530), lifted out as the primitive; `VisiblyRecoverable` becomes the derived all-D1-steps
  closure.
- **D2 — `ResidualAbelian adj P S ∧ ¬ IsBase adj P S`** (the fix). `¬IsBase` ⟺ a non-identity residual
  automorphism exists (`residualAut_eq_one_of_isBase` gives `IsBase ⟹` trivial residual) ⟺ "**a symmetry
  exists**" — the seal's standing conditioning, now a *predicate* conjunct.
- **Sequential screen:**
  `Findable S := CellsAreOrbits S ∨ (ResidualAbelian S ∧ ¬IsBase S) ∨ (∃ v, SymmetryOnlyStep S v ∧ Findable (insert v S))`,
  terminating (each `SymmetryOnlyStep` strictly refines the partition; ≤ n steps).

**The soundness obligations (each checked).**

1. **Termination** — `SymmetryOnlyStep` needs a non-singleton cell; individualizing splits it; cells
   strictly increase, bounded by `n`. ✓
2. **Exhaustiveness / no fourth species** — `¬Findable` ⟹ every maximal symmetry-only descent bottoms at
   `¬CellsAreOrbits ∧ ¬∃v SymmetryOnlyStep` ⟹ no cell is a single orbit ⟹ residual orbits *strictly
   refine* cells = **hidden**. The residual is then exactly one of {trivial, non-trivial abelian,
   non-trivial non-abelian} — a partition of all groups; exhaustive by tautology, modulo the per-node EOL
   for the last. ✓
3. **D1 soundness** (`D1-recursion ⟹ recoverable`) — a `SymmetryOnlyStep` chain ending at `CellsAreOrbits`
   *is* `VisiblyRecoverable ⟹ RecoverableByDepth` (free); chains ending at D2 reduce to the D2 bridge. ✓
4. **D2 soundness** (`D2 ⟹ recoverable`) — **THE FIX.** Non-trivial abelian residual ⟹ each orbit is a
   regular abelian action ⟹ a *unique* candidate twist per orbit ⟹ the linear oracle reads + verifies a
   **real** automorphism ⟹ recoverable. **Without `¬IsBase` this is false:** `ResidualAbelian` is
   *vacuously true* on a **trivial** residual, and `trivial residual ∧ ¬CellsAreOrbits` is precisely the
   **multipede / IR-blind-spot** — refinement-stuck, NOT recoverable. Bare `ResidualAbelian` would assert
   the blind-spot is D2-recoverable. The guard excludes it. ✓ (with fix)
5. **Composability** — the residual at `insert v S` is a point-stabilizer subgroup; `ResidualAbelian` is
   inherited (`residualAbelian_mono`). A step that trivializes the residual lands on `CellsAreOrbits`
   (discrete) or a blind-spot — never spuriously D2. ✓
6. **Escape = the leg-C residual, cleanly** — `¬Findable` bottoms at *hidden* residuals split by **order**:
   trivial ⟹ IR-blind-spot flag, non-trivial non-abelian ⟹ Cameron flag — exactly
   [exhaustive-obstruction §0.6](./chain-descent-exhaustive-obstruction.md)'s two flag causes. The
   `¬IsBase` guard is what makes that residual-order separation a **predicate-level** fact.

**Why the D2 fix is binding for the project target.** Under "polynomial-or-flag-on-blind-spot/Cameron,"
bare `ResidualAbelian` folds the multipede into D2 (a category error against §0.6's *Cameron = unconsumed
symmetry; multipede = absence of symmetry*). The `¬IsBase` guard keeps the multipede in `¬Findable`
(residual-order trivial), so **when a rigid solver is later added for the blind spot, the Cameron leg is
already exactly "hidden ∧ non-trivial ∧ non-abelian"** — no re-derivation. Catching it now avoids proving a
*false* D2 bridge.

**Test cases under the precise screen.** scheme → one step → `CellsAreOrbits` (D1); **GRR** → one step →
regular ⟹ trivial stabilizer ⟹ discrete (**D1**, not D2 — correct); CFI/rigid base → no step, abelian
non-trivial (**D2**); **CFI(Kₘ)** → consume `Sₘ` via ~m−1 steps → `Z₂^β` abelian non-trivial (**D2**, §6.9
resolved); Johnson → no step, non-trivial non-abelian (**escape = Cameron**); **multipede** → `¬CellsAreOrbits`,
no step, `IsBase` ⟹ D2 guard fails ⟹ **¬Findable = blind-spot flag** (bare D2 would wrongly say Findable).

**NEXT (implementation). — DONE (2026-06-01, axiom-clean).** Built in `Cascade.lean`: `SymmetryOnlyStep`
(D1 primitive), `symmetryOnlyStep_of_cellsAreOrbits` + `symmetryOnlyStep_empty_scheme` (scheme validation),
the **inductive** `Findable` (`recovered`=`Discrete` per §6.11 F1, `abelian`=`ResidualAbelian ∧ ¬IsBase`,
`step`=`SymmetryOnlyStep` + recurse). Design note: `Findable` is realised as a **least-fixed-point inductive**
(not a well-founded recursive `def`) — no termination proof, and the `step` constructor's non-singleton guard
forces `v ∉ S`. The old explicit-chain `VisiblyRecoverable` + `visiblyRecoverable_scheme` were **retained**
(not re-expressed) as the unconditional-D1 / structural witness.

---

### 6.11 Composite-graph audit — two definitional fixes (F1, F2) (2026-06-01)

Adversarial audit (8 agents: analyze + skeptic per case) of the §6.10 screen on **composite** graphs —
CFI(Multipede), Multipede+small-Z₂, Cameron×Cameron (swap join), disjoint normal⊔Cameron. **Result: the
seal/workflow is confirmed — NO composition manufactures a hidden non-Cameron non-abelian "fourth species";
in every case symmetry is stripped to the Cameron / IR-blind-spot section in poly time** (the user's stated
workflow). The pass found **two precision bugs in the §6.10 *definitions* (not the concept)** and corrected
one prediction.

**F1 — the "recovered" base case must be `Discrete`, NOT bare `CellsAreOrbits`.** `CellsAreOrbits S :=
∀ v w, same-cell → same-orbit` is **vacuously true** whenever there is one cell = one orbit — i.e. **at ∅
for ANY vertex-transitive graph, including Johnson.** So the §6.10 `Findable` first disjunct `CellsAreOrbits S`
would fire at ∅ for the **Cameron wall itself**, falsely marking Johnson Findable. `CellsAreOrbits` is
recovery-meaningful only *at a base* (`discrete_of_cellsAreOrbits_base`, Cascade.lean:73: `CellsAreOrbits ∧
IsBase ⟹ Discrete`). **FIX:** stop disjunct = `Discrete (warmRefine adj P (individualizedColouring n S))`
(≡ `CellsAreOrbits S ∧ IsBase S`). Sound + non-false-walling: at a `CellsAreOrbits` non-discrete node the
non-singleton cell *is* a single orbit ⟹ a `SymmetryOnlyStep` exists ⟹ recursion continues to `Discrete`
(scheme reaches it via symmetry-only steps; Johnson gets stuck first — correct). So the corrected screen is
`Findable S := Discrete(…) ∨ (ResidualAbelian S ∧ ¬IsBase S) ∨ (∃v, SymmetryOnlyStep S v ∧ Findable (insert v S))`.
*Side-check:* the existing `RecoverableByDepth := ∃S, CellsAreOrbits S` has the same latent depth-0 vacuity
for transitive graphs — likely harmless (completeness not soundness; used at bases) but worth confirming guarded.

**F2 — the *operational* residual-order flag signal is abelian-blind.** §0.6 / strategy §14's "non-trivial
residual ⟹ Johnson-like" checks *order*, not abelian-ness. An unconsumed **abelian** residual (CFI over an
unbounded-tw base) is non-trivial *and abelian*, so the order-signal would tag it Johnson-like though it is
not Cameron. The **predicate-level** screen is fine (abelian ⟹ D2, never reaches the order test); the
separator must be stated **"non-trivial *non-abelian* ⟹ Cameron"** (which §6.10 obl. 6 does), and the
*operational* signal needs an abelian check, not just order. Same theme as the D2 `¬IsBase` fix and F1: all
three are "meaningful only with the right base/abelian guard." (Recorded also in exhaustive-obstruction §0.6.)

**CFI(Multipede) — prediction corrected.** "IR-resistance starves the linear oracle" was *wrong*: CFI
discretization is governed by **tw(H) alone**, not Aut(H) (orbit-recovery Fact A / Cai–Fürer–Immerman; the
linear oracle reads the gauge off H's *cycle space*, not by canonizing H). Rigid + *bounded-tw* base ⟹ gauge
consumed, `D2 ⟹ recoverable` holds (clean). Only *unbounded-tw* blocks it = the already-documented flagged
region (exhaustive-obstruction §2 gap B) — a poly-*time* escape, not a symmetry misclassification, and not
composition-induced.

**Positive insight — rigidity *decouples*.** A rigid core cannot *lend* its refinement-resistance to a
symmetry: any automorphism's support is *forced off the rigid core* (it can't move core vertices), so an
added symmetry lives off-core and its footprint singletonizes ⟹ stays consumable (Multipede+Z₂ = CLEAN).
This is §0.6's orthogonality, here **forced** by the rigidity hypothesis rather than assumed.

---

### 6.12 Phase 0 — de-vacuated soundness + the D2-bridge interface, index-grounded (2026-06-01)

Investigating the D2 bridge against `PublicTheoremIndex.md` produced two corrections and a clean Phase-0 fix.

**The vacuity (now fixed).** The first soundness `recoverableByDepth_of_findable : Findable S → ∃ b,
RecoverableByDepth adj P b` is **vacuous** — `recoverableByDepth_univ` proves `RecoverableByDepth adj P n`
for *every* graph (individualize `univ` ⟹ discrete), so the `∃ b` conclusion holds with no hypotheses. The
project convention (stated at `RecoverableByDepth`'s def and `recoverableByDepth_cfi`) is that **only a
*specific* bound carries content.** **FIX (built, axiom-clean):** `FindableWithin adj P S b` — bound-indexed
(`recovered`→`b=S.card`; `step` propagates `b`; **`abelian` carries `RecoverableByDepth adj P b` as a field**)
— with `recoverableByDepth_of_findableWithin : FindableWithin S b → RecoverableByDepth adj P b` (non-vacuous,
the carried `b`) and `findable_of_findableWithin` (forgetful to the bound-free classification). The reverse
(Findable → FindableWithin) needs the bridge, so `FindableWithin` is strictly stronger — exactly because it
carries it.

**The D2-bridge interface is now concrete: the `RecoverableByDepth adj P b` field of `FindableWithin.abelian`.**
Two index-grounded corrections to the *route*:
- **It is the *discretizing* recovery, not the structural connector.** `cascadeComposition_pathFixing` needs
  `CellsAreOrbits (T 0)` at layer 1 — but D2 is *hidden* (cells coarser than orbits), so layer 1 is not
  `CellsAreOrbits`. The right prototype is **`recoverableByDepth_cfi`** (discretizing mode, §6.3): individualize
  the residual's base, `warmRefine` there is `Discrete`. The connector is for *composites* (cascade-outer +
  path-fixing-inner).
- **CFI(odd-deg) is a *proved* instance**, not just a scaffold: `recoverableByDepth_cfi` /
  `cfi_cascades_polynomially_oddDeg` (axiom-free) *is* "hidden `Z₂^β` gauge ⟹ recoverable at `baseSize`." The
  general bridge is its abelian generalisation, **= `AbelianSufficiencyHolds` (LinearOracle §L.6) = cascade-1b
  `hwit`** (one open core), and **substrate-conditional** (CFI-over-multipede / high-tw = gap-B: abelian yet
  only discretizes at large depth — the bound is the tractable/flagged discriminator, so the bridge is *not*
  an unconditional `∀ S, abelian ⟹ recoverable`). The twin regime is **D1** (`cellsAreOrbits_of_twin_cells`,
  visible), not a D2 beachhead.

**NEXT:** Phase 1 — wire `recoverableByDepth_cfi` as the proved D2-bridge instance (discharge
`FindableWithin.abelian`'s field for the CFI gauge). **✓ DONE — §6.13.** Then Phase 2 — isolate the
general nut (`AbelianDiscretizes`, the `cfi_cascades`-generalisation), stated conditionally.

---

### 6.13 Phase 1 — the D2-bridge anchor for the CFI gauge: DONE (2026-06-01)

**Built in [`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean), axiom-clean
(`[propext, Classical.choice, Quot.sound]` — *no* project axioms, in particular **not**
`AbelianSufficiencyHolds`; full serial build green, all three `#print axioms` confirmed):**

- **`findableWithin_cfi_gauge`** — the anchor. For an odd-degree CFI graph, whenever the residual at a
  committed set `S` is the hidden non-trivial abelian gauge (`ResidualAbelian adj P S ∧ ¬ IsBase adj P S`,
  the screen's D2 predicate), it builds `FindableWithin adj P S (cfi_depth_bound h)` via the `abelian`
  constructor, **discharging the recoverability field with the axiom-free `recoverableByDepth_cfi`**.
- **`recoverableByDepth_of_cfi_gauge`** — the end-to-end soundness routed *through* the screen
  (`recoverableByDepth_of_findableWithin ∘ findableWithin_cfi_gauge`): the D2 leg is non-vacuous.
- **`findable_cfi_gauge`** — the bound-free corollary: the CFI gauge lands in `Findable`'s `abelian`
  disjunct, **closing the §6.9 escape at the predicate level** (the central recoverable, non-Cameron
  example `CFI(Kₘ)` that slipped the *flat* screen is now in the D2 leg of the *sequential* screen).

**This is the D2 analogue of the D1 anchor `visiblyRecoverable_scheme`:** the abelian leg's recoverability
obligation is met by *proved* math on the central CFI example, not a placeholder. Two index-grounded facts
made this the right wiring (§6.12): CFI recovery is **discretizing** (prototype `recoverableByDepth_cfi`,
*not* the structural `cascadeComposition_pathFixing` — which needs `CellsAreOrbits` at layer 1, false for a
*hidden* D2 residual); and `recoverableByDepth_cfi` is **axiom-free for `OddDegree` with no `P`-invariance
hypothesis**, so the field is free at `cfi_depth_bound h` for *every* `S`.

**Honest scope (what stays a hypothesis).** `ResidualAbelian` and `¬ IsBase` are the screen's **D2
predicate** — *consumed, never decided* (deciding it is GI-hard; the oracle flags on budget-exceed, §3).
Discharging `ResidualAbelian` *unconditionally* for a real CFI residual would need the
`Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` **surjectivity** (a `Z₂^β` upper bound on the residual), deliberately **not**
built (`CFI.lean §15` builds only generator *existence*). The asymmetry with the D1 anchor is **intrinsic**:
D1's positive content (cells = orbits) is *refinement-visible* hence provable; D2's (residual is abelian) is
*hidden* hence needs unbuilt group structure. So Phase 1 anchors the **recovery half** (the genuinely hard
field) with proved math, leaving the abelian *classification* as the screen input it is designed to be.

**NEXT:** Phase 2 — isolate the **general** D2 nut as a marked conditional (`AbelianDiscretizes` /
`AbelianSufficiencyHolds`), with the depth bound as a hypothesis (the unbounded-tw caveat, §6.11/§6.12 —
CFI over an unbounded-treewidth base is abelian yet discretizes only at large depth, so the bridge is *not*
an unconditional `∀ S, abelian ⟹ recoverable`). The CFI(odd-deg) anchor above is its proved instance.
