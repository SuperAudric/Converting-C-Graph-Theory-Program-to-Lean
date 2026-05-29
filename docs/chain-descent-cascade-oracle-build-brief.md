# Chain descent — a-priori cascade oracle build brief (temporary)

> **Temporary doc — archive after the build.** This grounds the spec
> ([`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md))
> in the actual C# harness and gives a milestone-by-milestone build
> order. Once built and the spec's open decisions are resolved, fold the
> findings back into the spec (§8) and archive this file — exactly as the
> linear oracle build brief was.

**Purpose.** The C# build's job is **to de-risk the Lean discharge**,
not to chase speed. Per the standing decision (user, 2026-05-28): *the
proof program is the priority; the goal is a **proven** never-flagging
polynomial canonizer.* So this brief is organized around **what is
defensible in a proof** (§1) — every milestone is tagged by whether it
produces a proof-backed artifact, a proof target, an undischarged
obligation, or empirical-only de-risking.

**Empirical bar (the de-risking signal, not the goal) — MET 2026-05-28.**
CFI(K7): the linear oracle alone left **941** explored leaves with **555**
non-singleton-footprint branching nodes ([linear-oracle.md §8.1](./chain-descent-linear-oracle.md)).
After M2: **K7 → 1 leaf, 0 branching** (`BranchStarved = 0`); K6 76 → 1;
Petersen 22 → 2; Rook3x3 47 → 3 (residual = genuine decisions, not
starvation). Correctness/|Aut|/Even≠Odd preserved; scramble-invariant
through K7. Recursion depth ≈ tw(H), far below the `n` bound. So the
mechanism is **confirmed on CFI**; the build is done (M1–M5), the Lean
discharge (§8 below) is the remaining step.

---

## 1. What is defensible in a proof (the spine of this brief)

The Lean bar is a `CascadeOracleSpec` + a validity predicate, parallel
to the linear oracle's `LinearOracleSpec`/`LeafTwistSpec`
([ChainDescent.lean §15.8](../GraphCanonizationProofs/ChainDescent.lean)).
Each property the build touches falls into one of four buckets:

| Property | Bucket | Basis |
|---|---|---|
| **Soundness** — every harvested map is a verified automorphism; merging the reps it relates never skips the lex-min | **PROOF-BACKED** | `IsAutomorphism` edge-check + path-fixing pruning. Same shape as `LeafTwistSpec`. Unconditional. |
| **Termination** — recursion reaches discreteness within ≤ n levels | **PROOF-BACKED** | Each level individualizes one vertex; discreteness by n. Trivial. |
| **Polynomial bound** — single-path is O(n³) per call | **PROOF-BACKED** | `depth · n²` with `depth ≤ n`. Any polynomial depth works (§4). |
| **Completeness on OddDegree CFI** — one rep per orbit, all generators found | **PROOF TARGET** | `theorem_1_HOR_cfi_oddDeg` (axiom-free) + spine. Defensible *modulo wiring* the recursion to it. |
| **Completeness on rank-≤2 schurian schemes** | **PROOF TARGET** | `theorem_2_HOR_concrete_rank_two_J_singleton` (axiom-free) + spine. |
| **Completeness on the general cascade class** | **CONJECTURAL** | Tier-3 / orbit-recovery open content. |
| **Verdict iso-invariance** — canonical/flag output is labelling-independent | **UNDISCHARGED OBLIGATION** | `WarmPartition.CellOf` ids are iso-invariant, but the group-level obligation is unproven (strategy §15 gap 2). Shared with the linear oracle. |
| **Effectiveness** — the recursion actually collapses K7 | **EMPIRICAL ONLY** | M5's leaf-collapse bar. De-risks completeness; is not itself a proof. |

**The headline:** the cascade oracle's *full correctness — soundness +
completeness + polynomial bound — is already defensible in a proof on
exactly the subclasses where orbit recovery is proved* (OddDegree CFI,
rank-≤2 schemes). The soundness half is unconditional and class-blind.
The build's role is to **de-risk extending completeness** (does
single-path find a complete generating set in practice, on CFI(K7)?),
and to confirm the construction before the Lean effort is committed.

**What the build does NOT prove:** effectiveness on the general class,
and verdict iso-invariance. These stay open after the build; the build
informs them but does not close them.

---

## 2. Reuse inventory — what already exists in the harness

The linear oracle shipped most of the machinery
([ChainDescent.cs](../GraphCanonizationProject/ChainDescent.cs),
default-on `EnableLinearOracle`):

| Piece | Location | Role for the cascade oracle |
|---|---|---|
| `RefinementFootprint.Compute` | [RefinementFootprint.cs](../GraphCanonizationProject/RefinementFootprint.cs) | Parent↔child split-cell diff + `AllSingletons` gate + `CoupledVertices()`. **Reused unchanged.** |
| `TwistConstruction.TryConstruct` | [TwistConstruction.cs](../GraphCanonizationProject/TwistConstruction.cs) | Canonical-id sub-cell matching on all-singleton footprint. **The orbit-map construction — reused unchanged** (type-agnostic: produces whatever the forced matching gives). |
| `HarvestTwists` | [ChainDescent.cs ~193](../GraphCanonizationProject/ChainDescent.cs#L193) | Explore `r_1`, footprint, per-`r_j` construct+verify+`AddGenerator`. **The all-singleton harvest — extended by M2's recursion.** |
| `IsAutomorphism` | [ChainDescent.cs ~331](../GraphCanonizationProject/ChainDescent.cs#L331) | O(n²) edge-check. **The soundness anchor — reused unchanged.** |
| `CoveredByPathFixingAut` | [ChainDescent.cs ~251](../GraphCanonizationProject/ChainDescent.cs#L251) | Path-fixing-orbit pruning from harvested generators. **Consumes the cascade oracle's harvest identically.** |
| branch loop / harvest placement | [ChainDescent.cs ~178](../GraphCanonizationProject/ChainDescent.cs#L178) | Post-`r_1`, pre-unexplored-reps. **The cascade recursion hooks here.** |
| `PermutationGroup` | [PermutationGroup.cs](../GraphCanonizationProject/PermutationGroup.cs) | Schreier–Sims chain. **Harvest sink — unchanged.** |

So the **all-singleton path is already built and proof-relevant**: the
construction is forced (provable) and verification anchors soundness
(provable). The cascade oracle's M1 is mostly *validation* of existing
code.

---

## 3. The delta — what's genuinely new

Only the **bounded-depth recursion** (spec §4.4):

- when `AllSingletons(K)` is false, descend one level into an
  iso-invariantly-chosen non-singleton sub-cell, **exploratory (on
  copies)**, **single-path** (one rep, mirror-read the rest), re-attempt
  the harvest on the refined footprint;
- a `depth_bound` give-up cutoff that **degrades to the k-way branch**
  (not a flag — the flag is downstream, from the budget).

**Critical invariant for the proof and the cost:** the recursion must be
**single-path** — explore exactly one representative per level, never
branch over reps. A branching recursion is `cell_size^depth`
(exponential, = the a-posteriori descent it replaces); single-path is
`depth · n²` (polynomial). This is the entire point (spec §4.6).

---

## 4. Milestones (tagged by proof-defensibility)

### M1 — Validate the all-singleton harvest certifies orbit maps
**[PROOF-BACKED soundness · EMPIRICAL effectiveness] · ~0–20 lines**

Confirm `HarvestTwists`'s construct+verify already certifies
true-symmetry **orbit maps**, not just abelian twists — the construction
is type-agnostic, so this should hold with no code change. Add an
assertion/diagnostic that every harvested generator passes
`IsAutomorphism` (it must, by construction).

- *Proof-relevant artifact:* the empirical `LeafTwistSpec` evidence,
  now for orbit maps. The soundness here is the cleanest part of the
  Lean discharge.
- *De-risk:* none new — this is validation.

### M2 — Bounded-depth single-path recursion
**[PROOF-BACKED soundness+termination · PROOF TARGET completeness-on-subclass · CONJECTURAL general · EMPIRICAL effectiveness] · ~200–300 lines**

The new content. When the footprint is non-singleton, recurse
(exploratory, on copies, single-path) into one iso-invariant
non-singleton sub-cell; re-attempt the harvest on the refined footprint.

- *Proof-backed now:* soundness (verify-gated) and termination
  (discreteness ≤ n) hold for **any** input, unconditionally.
- *Proof target:* that single-path finds a **complete** generating set
  is `theorem_1_HOR_cfi_oddDeg` / `theorem_2_HOR_concrete_rank_two_J_singleton`
  + the spine — defensible on those subclasses, the Lean wiring being
  the recursion ↔ orbit-recovery-depth correspondence.
- *Empirical (M5):* whether it collapses CFI(K7)'s 555 non-singleton
  nodes — the de-risking signal that single-path is effective beyond
  the toy cases.
- **Gotcha:** must NOT branch over reps. One rep per level; mirror-read
  the cellmates. A `for r_j` loop that *explores* `r_j` (rather than
  reading it off `r_1`'s mirror) silently reintroduces the exponential.

### M3 — Iso-invariant sub-cell selection
**[FIRM mechanism · UNDISCHARGED verdict obligation] · ~40 lines**

Pick the non-singleton sub-cell `C` by canonical `CellOf` id. The
explored rep `c_1` **need not** be canonical — the mirror-read is
choice-symmetric (different `c_1` → same generated group → same verdict,
spec §4.4).

- *Firm:* `CellOf` ids are iso-invariant (existing harness property).
- *Undischarged:* that the harvested **group** (hence the canonical/flag
  verdict) is labelling-independent is the §15-gap-2 obligation — the
  build keeps the mechanism iso-invariant but does not discharge the
  obligation. Don't introduce any vertex-index dependence in selection.

### M4 — Depth-bound + degrade-to-branch
**[PROOF-BACKED soundness · EMPIRICAL efficiency] · ~30 lines**

Wire `depth_bound`; past it, **return the cell's reps unmerged
(over-split)** and let the harness branch — *not* a flag. The flag is
the existing budget mechanism, downstream, when real branches stack.

- *Proof-backed:* over-split is sound (coverage preserved — the safe
  direction). The degrade never causes a wrong answer.
- *Reshapeable:* `depth_bound` value. Start with the trivial `n` (always
  sound, O(n³)); tighten to `tw(H)` only if the CFI base is
  identifiable. The value is an efficiency knob, not a correctness one.

### M5 — Empirical bar (de-risking completeness)
**[EMPIRICAL ONLY] · measurement, not code**

CFI(K4…K7), oracle off vs on (cascade recursion enabled):

- **Branching-node attribution** — the decisive metric: how many nodes
  still branch at non-singleton footprints (was 555/555 on K7). Target
  → ~0.
- **Leaf count** — collapse from 941 (linear-only) toward O(β).
- **Correctness** — canonical form, |Aut|, Even≠Odd preserved; exhaustive
  size-5/6 canonical-uniqueness; scramble-invariance.

- *What it de-risks:* completeness/effectiveness — does single-path
  find enough generators to collapse the tree on a real CFI base. This
  is the empirical stand-in for the general-class completeness
  conjecture; **it is not a proof.**

---

## 5. Cost accounting to verify

- **Per oracle call:** footprint diff O(n²) + construction O(n²) +
  verify O(n²), single-path over ≤ `depth_bound` levels → **O(depth·n²)**.
- **Open question to resolve in the build:** is the exploratory
  recursion **reused** as the committed descent path (total O(n³)) or
  **re-done per node** (total O(n⁴))? Both polynomial — the *proof* only
  needs "polynomial," so either suffices for the Lean bound — but pin it
  down for the implementation and record it for the fold-back. Prefer
  reuse (carry harvested generators forward; `CoveredByPathFixingAut`
  already prunes, so re-exploration should short-circuit).
- **Instrument:** branching-node count (M5's key metric) and recursion
  depth distribution, to confirm single-path and measure how far below
  `depth_bound` the cascade class actually bottoms out.

---

## 6. Constraints and gotchas

- **Single-path is mandatory** (§3). The one way to break the design:
  let the recursion branch over representatives. One rep per level,
  mirror-read the rest.
- **Verification is the sole soundness anchor** (spec §4.5). Never
  harvest an unverified candidate; a failed `IsAutomorphism` → reps stay
  separate (over-split), not an error.
- **Degrade, don't flag** (M4). The recursion returns over-split; the
  budget flags downstream. The recursion itself always terminates.
- **Exploratory on copies.** The recursion individualizes on local
  partition copies to read footprints and harvest generators; it does
  not commit descent steps. Harvested generators go into
  `PermutationGroup`; the harness's committed branching is separate.
- **Iso-invariance** (M3). Sub-cell by `CellOf` id; no vertex-index
  dependence. The verdict obligation stays undischarged — do not pretend
  the build closes it.
- **`depth_bound` is an efficiency knob, not correctness** (M4). Trivial
  `n` is always sound.

---

## 7. Test plan

- **Leaf + branching-node counts**, oracle off/on, CFI(K4, K33,
  Petersen, Rook3×3, K6, K7). Primary signal: non-singleton branching
  nodes → ~0; leaves → O(β).
- **Correctness regression:** the full existing suite green, including
  exhaustive size-5/6 canonical-uniqueness and |Aut| / Even≠Odd on all
  CFI bases.
- **Scramble-invariance:** canonical form and flag verdict identical
  across random relabellings — the iso-invariance *empirical* check
  (not the proof, but a necessary signal).
- **Single-path assertion:** instrument that each oracle call explores
  exactly one representative per recursion level (guard against an
  accidental branching loop).

---

## 8. Done criteria + fold-back to the spec and Lean

**Done — 2026-05-28.** M1–M5 complete (M3/M4 folded into M2). M5 bar met:
CFI(K7) branching 555 → 0, leaves 941 → 1; correctness preserved through
K7; scramble-invariant. C# build complete; only the Lean discharge remains.

**Folded back into [cascade-oracle.md](./chain-descent-cascade-oracle.md)
(§8.1 build status, §10 risk 1, §9 constraint table):**
- **Unification decision (§1.4):** YES — the all-singleton harvest is
  identical for orbit maps and twists (construction type-agnostic,
  verification class-blind). Shipped as **one component** (extended
  `HarvestTwists`; linear oracle = depth-0 case), no separate class.
- **Cost accounting (§5):** the recursion is **exploratory, re-done per
  node → O(n⁴)** total. The O(n³) committed-reuse is a deferred
  optimization (K7 is ~78 s/canonization — polynomial, untuned).
- **Effectiveness verdict:** single-path **collapsed every CFI base**
  (K4…K7) — `BranchStarved = 0`, recursion depth ≈ tw(H). Strong evidence
  for the general-class completeness conjecture *on CFI*; it does **not**
  prove it beyond CFI/schemes (Tier-3). The mirror-read shortcut was
  dropped for lockstep per-rep single-path (circular — see spec §4.1); no
  footprint under-harvested on the measured bases.

**Then the Lean discharge** ([cascade-oracle.md §8.2](./chain-descent-cascade-oracle.md)),
in proof-defensibility order:
1. **`CascadeOracleSpec` + validity predicate** — the soundness half.
   PROOF-BACKED; mirrors `LeafTwistSpec`. Do this first; it is the
   cleanest and class-blind.
2. **Completeness on OddDegree CFI / rank-≤2 schemes** — wire the
   recursion's bottoming-out to `theorem_1_HOR_cfi_oddDeg` /
   `theorem_2_HOR_concrete_rank_two_J_singleton`. PROOF TARGET; the
   subclasses where it is *already* defensible.
3. **Leave open, explicitly:** general-class completeness (Tier-3
   conjecture) and verdict iso-invariance (§15 gap 2). The build and the
   subclass discharge do not close these; name them as the residual
   proof obligations.

**Then archive this brief.**

---

## 9. Cross-references

- [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) —
  the spec this grounds (§4 the recursion, §8 the build/Lean plan, §9
  the constraint table).
- [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
  §8.1 — the starvation finding (the empirical bar's baseline) and the
  shared harvest core.
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) —
  `theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_concrete_rank_two_J_singleton`:
  the proof targets M2's completeness wires to.
- [`chain-descent-deferred-decisions.md`](./chain-descent-deferred-decisions.md) —
  the scheduling layer to be built *after* this oracle; it reuses this
  oracle's classification unchanged.
- C#: [ChainDescent.cs](../GraphCanonizationProject/ChainDescent.cs),
  [RefinementFootprint.cs](../GraphCanonizationProject/RefinementFootprint.cs),
  [TwistConstruction.cs](../GraphCanonizationProject/TwistConstruction.cs),
  [ITransversalOracle.cs](../GraphCanonizationProject/ITransversalOracle.cs),
  [CascadeOracle.cs](../GraphCanonizationProject/CascadeOracle.cs).
- Lean: [ChainDescent.lean](../GraphCanonizationProofs/ChainDescent.lean)
  §15.8 (`LinearOracleSpec`/`LeafTwistSpec` to parallel),
  `theorem_1_HOR_at_depth`; [CFI.lean](../GraphCanonizationProofs/ChainDescent/CFI.lean),
  [Scheme.lean](../GraphCanonizationProofs/ChainDescent/Scheme.lean).
