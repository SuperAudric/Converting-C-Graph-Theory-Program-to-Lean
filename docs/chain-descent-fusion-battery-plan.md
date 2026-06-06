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

## 0. One-line goal

Close leg C's **largeness** antecedent by **deriving** it from a battery-validated **no-fusion** witness, via
the landed order identity `|Aut| = ∏ basic-orbit sizes`. Largeness goes from a free hypothesis on
`exhaustiveObstruction_scheme` to *derived-from-a-witness*, tightening "leg C ⟹ Cameron" to "modulo (cited
Babai classification + the no-fusion witness + the separate primitivity witness)".

## 1. The proof path (this is what defines the battery)

Work backward from what we would build *if* the battery shows no fusion. The key: **largeness becomes
derivable on already-landed machinery.**

- **PP1 — Name the property as a witness.** `NoFusion` / `DeferralComplete`: under a *defer-all-reals*
  policy (consume only certifiable/recovered symmetries, never make a genuine decision), the symmetry-only
  harvest finds the **full** `Aut_S`. Equivalently: the stuck-state residual is **never small-but-non-trivial**
  — only *trivial* (IR-core) or *large*. A witness predicate, in the `RecoverableByDepth` mould.
- **PP2 — Prove the separable case unconditionally.** Disjoint / non-shared-cell structure ⟹ deferral
  separates symmetry from rigidity, via `forcedNode` / `movedSet` (the forced node individualizes only the
  moved support, deferring the rigid part) + Tier-0 component decomposition + `recoverableAt_base_iff_discrete`
  (at a base, recovery ⟺ discreteness — the symmetry axis and the IR-stickiness axis are independent
  coordinates). This is the part that is **not** substrate-conditional; the battery's friendly + disjoint
  controls are its empirical shadow.
- **PP3 — Derive largeness (the payoff, on landed machinery).** By `card_autP_eq_prod_of_base`
  (`Cascade.lean` Part A, **landed**), `|Aut| = ∏ basic-orbit sizes` along the recovery base sequence. Under
  `NoFusion` the consumption path is *symmetry-only*, so its cost **is** that orbit-size product. Hence
  **¬D1 (not consumed at poly cost) ∧ NoFusion ⟹ ∏ orbit-sizes super-poly ⟹ `|Aut|` super-poly = large.**
  No Babai needed for this step — the order identity does it. *(The multipede escapes cleanly: it has no
  symmetry-only path, so its cost is all real decisions, not orbit sizes — `NoFusion` does not apply, it is
  the IR-core, trivial residual.)*
- **PP4 — Carry the entangled case as a battery-backed witness.** Unconditional `NoFusion` = unconditional
  decomposability = the wall, so the entangled regime stays a witness (the battery is its evidence, exactly
  as the cascade backs `recoverableByDepth_cfi`). The structural bridge for the separable part is PP2.
- **PP5 — Wire to the capstone.** `exhaustiveObstruction_scheme` (`Scheme.lean` §12) with **largeness now
  derived** (PP3) → "leg C ⟹ Cameron" modulo (cited Babai classification + `NoFusion` witness + the
  *separate* primitivity witness). Primitivity stays its own depth-graded line (Shrikhande-evidenced; the
  battery may measure "imprimitive ⟹ recovers" as a secondary signal but it is **not** the largeness target).

**Net endpoint:** largeness is *derived from a battery-validated witness via the landed order theorem*, with
the genuinely-open residual (the entangled case) honestly witnessed rather than ground out. This is a real
tightening of leg C, not a closure of the wall.

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

- **Recovery-only mode.** A descent that consumes only certifiable/recovered orbits and *stops* a branch
  rather than making a genuine decision (sidesteps the a-posteriori-needs-leaves tension). Reuses the
  cascade/recovery oracle; the new pieces are the defer-reals control flow + the residual-size classifier.
- **Ground truth.** Brute-force `Aut(G)` (independent of the canonizer), as the Cameron battery already does;
  compare `|recovery-only harvest|` to `|Aut|`.
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
