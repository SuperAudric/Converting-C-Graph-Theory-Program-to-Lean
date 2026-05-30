# Tier 3a / B1 — Lean build plan (cascade composition)

> **STATUS: planning doc.** Concrete Lean buildout plan for **B1** of
> [`chain-descent-tier3-tractable-buildout.md`](./chain-descent-tier3-tractable-buildout.md)
> — the Lean discharge of **Theorem 3a (cascade composition)**. Supersedes the
> rough §9 phase sketch in
> [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
> with a decomposition tuned to the machinery now in hand (Part A + the cascade
> contract). Fold into the Tier-3a doc once B1 lands.

## 0. Goal

Prove, axiom-clean, that the cascade depths of layered cascade-class subgroups
**add**: if `Aut(G)` admits a cascade-class normal chain `H₀ ⊵ … ⊵ H_k = {1}`
with per-layer depth bounds `f_i`, then 1-WL on `(G, S)` for some `S` with
`|S| ≤ Σ f_i` is **discrete** (reaches the trivial orbit partition).

"Done" = a theorem `cascadeComposition` in `ChainDescent/Group.lean` (or a new
`ChainDescent/Cascade.lean`) with `#print axioms` showing only the standard basis
(`propext, Classical.choice, Quot.sound` + `refineStep, refineStep_iff` via
`warmRefine`).

## 1. The pivotal formalization decision

**Do NOT recurse on the quotient graph as a re-typed `AdjMatrix mᵢ`.** The paper's
§4.2 recursion ("apply the theorem to `G₁ = G/H₁`") would require materializing each
`Gᵢ` on a fresh vertex type (the orbit-type → `Fin m` re-indexing deferred in A4) and
proving 1-WL commutes with the quotient at every level — a multi-month slog dominated
by bookkeeping that the canonizer otherwise avoids (label choice).

**Instead: stay on `Fin n` and telescope cumulative individualization sets.** The
conclusion only needs that warm refinement at the *final* cumulative set
`T_k := S₁ ∪ … ∪ S_k` is `Discrete`. That decomposes:

- **(C1) Finish.** `CellsAreOrbits adj P T_k` (cells ⊆ Aut_{T_k}-orbits — proved on
  the cascade class) **+** `T_k` is a **base** (`OrbitPartition adj P T_k v w → v = w`,
  i.e. `Aut_{T_k}` acts trivially / `H_k = {1}`) **⟹** `Discrete (warmRefine … T_k)`.
  *Trivial:* `CellsAreOrbits` turns same-cell into same-orbit, the base condition
  turns same-orbit into equality, so same-cell → equality = `Discrete`.
- **(C2) Construction.** The per-layer recoverability theorems + `warmRefine_refines`
  (monotonicity, proved) + `OrbitPartition.mono` (fixing more shrinks orbits, proved)
  assemble `CellsAreOrbits` at `T_k` with `|T_k| ≤ Σ|S_i| ≤ Σ f_i`. The real induction.

The quotient enters **only** inside (C2)'s per-layer step — exactly the paper's
**§4.2.5** ("1-WL on a cell = 1-WL on the quotient vertex"). A4's
`cell_iff_orbitMk_eq` already supplies the *vertex* correspondence; the missing piece
is the *refinement-transfer*. We isolate it as one hypothesis and discharge it last.

## 2. What's already in hand

| Ingredient | Where | Role |
|---|---|---|
| `warmRefine_refines` (1-WL monotone in indiv. set) | `ChainDescent.lean` | (C2) monotonicity |
| `OrbitPartition.mono` (fix more ⟹ finer orbits) | `CascadeOracle.lean` | (C2) telescoping |
| `OrbitPartition.subset_warmRefine` (orbits ⊆ cells, free dir.) | `ChainDescent.lean` | everywhere |
| `CellsAreOrbits` + `cellsAreOrbits_of_discrete` | `CascadeOracle.lean` | the per-level object + anchor |
| `RecoverableByDepth` + `_cfi` / `_scheme` instances | `CascadeOracle.lean` | per-layer cascade-class bounds |
| `cell_iff_orbitMk_eq` (cell = quotient-vertex) | `Group.lean` §A4 | §4.2.5 vertex half |
| `OrbitQuotient` / `quotientAdj` / `orbitQuotientEquivAutGroup` | `Group.lean` §A4 | quotient graph (for transfer) |
| `AutGroup` / `LayerChain` / `orbitPartition_iff_autGroup` | `Group.lean` §A1–A3 | group-theoretic interpretation |

## 3. Phased plan

> **STATUS — Phases A + C DONE (2026-05-30).** Built in
> [`ChainDescent/Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean)
> (module `ChainDescent.Cascade`, axiom-clean, no `sorry`); theorem map in
> `PublicTheoremIndex.md` §"ChainDescent/Cascade.lean". The headline
> `cascadeComposition` ("depths add") is proved **conditional on the per-layer
> `LayerStep` hypotheses** (= §4.2.5 transferred); the cardinality companion
> `cumulative_card_le` gives `|T_k| ≤ Σ fᵢ`. **Phase D (the transfer) is the remaining
> work** and the headline does not depend on it. Note: `RelativeRecoverable` collapsed
> to `LayerStep` (`CellsAreOrbits T → CellsAreOrbits (T ∪ S)`) — the cleanest interface
> the induction consumes; the induction is seeded by layer-1's *unconditional*
> recoverability (`CellsAreOrbits` at `T 0`), avoiding a false `CellsAreOrbits ∅` base.

### Phase A — abstraction (`CascadeClass` + relative recoverability) — ~150 lines, low risk

- **`CascadeClass`**: a predicate/structure on `(adj, P)` carrying a depth bound `f`
  and a witness that `RecoverableByDepth adj P (f …)` holds. Tier 1 (`recoverableByDepth_cfi`)
  and Tier 2 (`recoverableByDepth_scheme`) become instances — re-export, no new math.
- **`RelativeRecoverable adj P T S`** := the per-layer step object. Cleanest form that
  stays on `Fin n`:
  > given `CellsAreOrbits adj P T` (cells at `T` = Aut_T-orbits), individualizing the
  > increment `S` refines those cells to the *next* layer's orbits:
  > `CellsAreOrbits adj P (T ∪ S)`.
  This is literally `CellsAreOrbits adj P (T ∪ S)` — so "relative recoverability of the
  cumulative set" *is* `CellsAreOrbits` at the larger set. The content is that it holds
  with a *small* increment `|S| ≤ f`, which the per-layer cascade theorem (transferred,
  Phase D) provides. Phase A just names the interface.
- **Base predicate** `IsBase adj P T` := `∀ v w, OrbitPartition adj P T v w → v = w`
  (the chain bottoms out at `{1}`); + bridge `IsBase ↔ Aut_T trivial` via
  `orbitPartition_iff_autGroup` (ties to A1, optional).

### Phase C — the composition theorem — ~200–400 lines, low–medium risk. **HEADLINE.**

- **(C1)** `discrete_of_cellsAreOrbits_base : CellsAreOrbits adj P T → IsBase adj P T →
  Discrete (warmRefine adj P (individualizedColouring n T))`. Trivial chain of the two
  hypotheses. (Possibly already a one-liner against existing lemmas.)
- **(C2)** `cellsAreOrbits_compose`: by induction on the layer list, from per-layer
  `RelativeRecoverable` (= `CellsAreOrbits` at each cumulative `Tᵢ`) conclude
  `CellsAreOrbits adj P T_k`. Telescopes via monotonicity; the *increments* are where
  the per-layer hypotheses plug in. **Crucially, takes the per-layer recoverability as
  hypotheses** — no quotient/transfer here, so it is axiom-clean and self-contained.
- **(C-card)** `|T_k| ≤ Σ f_i` via `Finset.card_biUnion_le` / `card_union_le`.
- **`cascadeComposition`** = (C1) ∘ (C2) ∘ (C-card): the headline. States "depths add"
  *conditional on the per-layer relative-recoverability*, which §4.3 confirms is the
  paper's actual structure (4.2.5 is the only genuinely new content). This deliverable
  alone is the bulk of B1's value and is genuinely tractable.

### Phase D — discharging `LayerStep` (§4.2.5) — the hard residual, isolated

> **STATUS — Phase D infrastructure DONE (2026-05-30); full per-layer discharge (step 5)
> remains.** Built in
> [`ChainDescent/Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean)
> §"Phase D" (axiom-clean). Steps 1–4 below are done: set-monotonicity
> (`warmRefine_indiv_mono`, via `signature_refines`), the reduction
> (`layerStep_of_witnessUpgrade`), the trivial instances, and the support-backbone
> bridge (`witnessUpgrade_of_pathFixing`). **Step 5 — connecting `WitnessUpgrade` to the
> Tier-1/Tier-2 theorems for a concrete layer class — is the genuine remaining work.**

Discharge `LayerStep adj P T S` (`CellsAreOrbits T → CellsAreOrbits (T ∪ S)`) — the
per-layer step. This is the one place the quotient bites.

**Approach decision (2026-05-30).** Two routes were weighed:

- **(A) Materialized quotient — REJECTED.** Build `G_T : AdjMatrix m` via
  `Fintype.equivFin` and prove `warmRefine` commutes with the quotient. `refineStep` is
  an **axiom** specified only by `refineStep_iff` (signatures = multisets over *all*
  vertices); the quotient changes the vertex set and reweights neighbour multiplicities,
  and there is no API relating `refineStep` at size `n` to size `m`. Needs new
  axiom-level machinery — high risk, likely intractable.
- **(B) Intrinsic, on `Fin n` — CHOSEN.** Never materialize `G_T`. Reduce `LayerStep` to
  a **witness-upgrade** via set-monotonicity, reusing the existing `refineStep_iff` API.

**Phase D structure (Approach B):**

1. **Set-monotonicity of warm refinement** (the load-bearing, independently-valuable
   lemma — the docs mis-cite `warmRefine_refines` for this; that lemma actually relates
   `warmRefine` to its *initial* colouring, not two individualization sets):
   - `Refines χ₁ χ₂ := ∀ a b, χ₁ a = χ₁ b → χ₂ a = χ₂ b`.
   - `signature_refines` — `Refines χ₁ χ₂` ⟹ `signature χ₁` separations carry to
     `signature χ₂` (the coarsening-map argument: `sig χ₂ = (sig χ₁).map G` for a
     coarsening `G` built from `Refines`). The crux.
   - `refineStep_refines` (via `refineStep_iff` + `signature_refines`),
     `warmRefine_refines_initial` (iterate `n`).
   - `individualizedColouring_refines` (`T ⊆ T'` ⟹ `Refines (indiv T') (indiv T)`),
     `warmRefine_indiv_mono` (the payoff: same `T∪S`-cell ⟹ same `T`-cell).
2. **The reduction.** `WitnessUpgrade adj P T S` := for same-`T`-orbit, same-`(T∪S)`-cell
   `v, w`, conclude `OrbitPartition adj P (T ∪ S) v w`. Then
   `layerStep_of_witnessUpgrade` (uses `warmRefine_indiv_mono` + `CellsAreOrbits T`).
3. **Trivial instances** (real corollaries, validate interface): `layerStep_empty`,
   `layerStep_subset` (`S ⊆ T`), `layerStep_of_cellsAreOrbits`, `layerStep_of_discrete`
   (the recursion bottom).
4. **Support-backbone sufficient condition.** `witnessUpgrade_of_pathFixing`: if every
   such `v, w` admits a `P`-preserving automorphism with support disjoint from `T ∪ S`
   (fixing the committed path) realizing `v ↦ w`, the upgrade holds (via
   `orbitPartition_of_support_disjoint`). This is exactly what harvested/verified
   generators (cascade + linear oracle) produce — the bridge to the algorithm.
5. **Full discharge per layer class — the genuine remaining work.** Connect
   `WitnessUpgrade` to the Tier-1/Tier-2 theorems for an actual layer (the existence of
   the path-fixing witnesses). Easiest-first: rigid base (vacuous) → Tier-2 depth-1 →
   CFI. Each yields an unconditional composition corollary.

> **STATUS — step 5 synthesis DONE (2026-05-30); concrete per-class witness existence
> remains.** Built `cascadeComposition_pathFixing` and `cascadeComposition_twoLayer` in
> [`ChainDescent/Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean)
> (axiom-clean). **The whole of Theorem 3a is now reduced to a single hypothesis**: at
> every layer the residual orbit symmetry is realized by **path-fixing automorphisms**
> (support disjoint from the committed set) — i.e. the harvested-generator picture
> (calculator §2). The rigid/trivial layer is `layerStep_empty` (done).
>
> **What genuinely remains (the deep work):** the *existence* of the path-fixing
> witnesses for a concrete layer class. Analysis during the build clarified *why* this
> is the residue and not more: any layer dischargeable by a whole-graph Tier theorem is
> already covered by `cascadeComposition_single` (no composition needed); composition's
> value is layers dischargeable only *relative* to the previous level, whose witnesses
> are exactly the path-fixing automorphisms `hwit` abstracts. Constructing them
> concretely (CFI gadget twists; scheme automorphisms) needs the gadget/scheme
> machinery and a concrete layered graph — a multi-session effort, correctly isolated as
> the single hypothesis of `cascadeComposition_pathFixing`. The linear oracle's verified
> twists (B2 `canonicalTwistOracle`) are a candidate witness source for the abelian/CFI
> layer, pending a support-disjointness bound on `candidateTwist`.

## 4. The group-chain interpretation (faithfulness bridge) — optional, ~80 lines

The core (Phases A–C) is stated combinatorially (cumulative individualization sets +
`CellsAreOrbits`). To honor the paper's `H₀ ⊵ … ⊵ H_k` framing, add a bridge:
the cumulative `Tᵢ`'s stabilizer is `H_i` — i.e. `H_i`-orbits = `OrbitPartition adj P Tᵢ`,
via A1's `orbitPartition_iff_autGroup` and the support backbone. This *interprets* the
combinatorial layers as the normal chain's quotients but is not load-bearing for the
theorem. Build it to connect `LayerChain` (A3) to the composition, not before.

## 5. Recommended first concrete step

**Phase A + Phase C** (the conditional headline), in that order, as the first
deliverable. It is axiom-clean, self-contained, needs nothing from Phase D, and proves
the paper's actual content ("depths add" given per-layer 4.2.5). Then Phase D layer (b)
(Tier-2 depth-1 transfer) to produce the first *unconditional* composition corollary and
validate the transfer architecture on the smallest nontrivial case, before the CFI
transfer.

## 6. Risks & deferrals

- **Transfer lemma (Phase D)** is the genuine risk — medium-to-high, the quotient
  bookkeeping the Tier-3a doc §9 flags. Mitigated by: (i) isolating it so the headline
  doesn't depend on it; (ii) the intrinsic route avoiding re-indexing; (iii) discharging
  trivial/Tier-2 layers before CFI.
- **Polynomial-runtime is NOT in scope.** B1 proves *depth ≤ Σ f_i* (a completeness /
  orbit-recovery statement); turning that into a polynomial *runtime* bound still rests
  on the unformalized `tw` bound (tractable-buildout §0.1) and is separate.
- **The wall stays out of scope.** B1 is conditional on a cascade-class chain *existing*
  (sub-claim 2 / (O*)). `cascadeComposition` is an implication; it never claims a chain
  exists.

## 7. Cross-references

- [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
  §4.2 (proof), §4.3 (4.2.5 = only new content), §9 (original phases).
- [`chain-descent-tier3-tractable-buildout.md`](./chain-descent-tier3-tractable-buildout.md)
  — B1's place in the buildout; Part A (now complete) is the substrate.
- `ChainDescent/Group.lean` §A4 — `cell_iff_orbitMk_eq`, `OrbitQuotient`, `quotientAdj`.
- `ChainDescent/CascadeOracle.lean` — `CellsAreOrbits`, `RecoverableByDepth` + instances,
  `OrbitPartition.mono`.
