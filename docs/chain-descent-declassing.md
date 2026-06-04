# Chain descent — the de-classing turn: non-class-specific orbit recovery via the saturation engine

> **STATUS (2026-06-02): the organizing strategy for orbit recovery *and* oracle firing.** Read this
> **after** the overview/strategy/calculator and **before** the per-class material in
> [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md). It reframes that doc's
> tier/rank narrative as a **witness layer**, and it reframes the calculator/overview's *two separate
> oracles* (cascade + linear) as **one recovery-based harvest** — both are the current model; the
> older framing is superseded here.
>
> **The thesis.** Recovery (and the oracle firing built on it) was being discharged *class by class* —
> CFI odd-degree then even, schemes rank-2/3/4, *and* the linear oracle's CFI-gadget completeness.
> There are **unboundedly many classes**, so that ladder stalls. The turn: prove recovery
> **non-class-specifically**, once, behind a generic engine, with per-class theorems demoted to
> *witnesses* of an abstract predicate — and **fold both oracles' firing into that one recovery-based
> harvest**, so class-specificity is quarantined into a single *depth* witness.
>
> **What is built (all axiom-clean `[propext, Classical.choice, Quot.sound]`; full build green):**
> - **Engine** (`Saturation.lean`, §2) — an *extensive* `Finset` operator saturates to a fixpoint in
>   bounded rounds (`exists_iterate_isFixed_within`). One lemma, every consumer.
> - **Schemes** (`Scheme.lean`, §3) — `EdgeGenerates` + **`theorem_2_HOR_of_pPolynomial`**: the entire
>   metric / distance-regular family (cycles, Johnson, Hamming, all DRGs) in **one theorem**.
> - **Leg A** (`Cascade.lean`, §4, §7) — the support induction to a base (`exists_isBase_saturated`),
>   the tight bound `base(g) ≤ |support|` (`exists_isBase_saturated_support`), the choice-free
>   iso-invariant **forced node** (`forcedNode`, `forcedNode_relabel`), and the recovery-axes
>   separation (`recoverableAt_base_iff_discrete`: recovery ⟺ `Discrete` at the base).
> - **Leg B** (`Cascade.lean`, `CascadeOracle.lean`, §5) — the linear oracle's firing **folded into the
>   colour-model recovery/harvest** (`harvest_fires_of_cellsAreOrbits_discrete`); the precise D2
>   predicate `ResidualInvolutive` (+ `residualAbelian_of_involutive`, wiring in the orphaned
>   `ResidualAbelian`); the order-model firing now **legacy**.
> - **Unified oracle** (§6) — both oracles fire through *one* mechanism: recovery → colour-match →
>   verify; the seal's D1 / D2 / wall becomes a **depth** distinction.
>
> **M-B + M-C + M-D LANDED (2026-06-02/03, axiom-clean, `CascadeOracle.lean §C.4/§C.5/§C.6` +
> `Cascade.lean`):** the concrete `colourMatchPerm` / `matchOracle` (construct-and-check) firing *both*
> oracles — soundness (`OrbitMapSpec`) unconditional, completeness reduced to the depth witness +
> localisation, flag iso-invariance free; the multi-step `indivWithSet` (+ transport + lifted bricks +
> `colourMatchPermSet`) so the harvest fires at a *set*-discretized footprint; and the multi-step oracle
> `matchOracleSet` (+ unconditional soundness, conditional completeness) with the **lockstep discharged**
> — `lockstepExpand_forcedExpand` proves the exploration rule's equivariance via Leg A's `movedSet_image`,
> so the only remaining completeness hypothesis is the depth witness.
>
> **§C.7 + §C.8 LANDED + the discretizing-oracle limit (2026-06-03, axiom-clean).** §C.7 made `matchOracle`'s
> completeness *honest* (fire at the discretizing depth, propagate via `OrbitPartition.mono`; the orbit pair
> is consumed directly, so no `CellsAreOrbits`). §C.8 built **Leg 1** — the level-coloured sequence
> (`indivWithSeq`, A1-reducible `hdiscSeq`, A2 position-transport) and the oracle `matchOracleSeq`. But
> `lockstep_disc_imp_stab_trivial` proves its hypotheses `LockstepExpandSeq ∧ hdiscSeq ⟹ stab(v)=1`:
> **the discretizing colour-match cannot harvest a multi-step moved orbit** (no iso-invariant ordering of
> an orbit exists). **Open frontier — where a fresh reader picks up (§9):** the **cross-branch /
> stabilizer-chain (Schreier–Sims, Part A)** harvest — now *required* for multi-step hidden symmetry,
> not optional; the single-rep localisation-`hco`/1b; the structural-mode scheme oracle; the
> **IR-stickiness axis** (multipede, flagged); and the **wall** (¬D1∧¬D2, Cameron/Johnson). The first
> three are bounded; the last two are the honest boundary.
>
> **Part A progress (2026-06-04, axiom-clean — see [schreier-sims](./chain-descent-schreier-sims.md)).** The
> cross-branch group object is built, **both harvest directions**: `StabilizerAt` (residual `Aut_S^P` as a
> `Subgroup`); the harvest **soundness** seam (fold-in ⊆ residual, prune sound); the rigid verdict (trivial
> ⟺ base); the full `order = ∏ basic-orbit sizes` (`card_autP_eq_prod_of_base`); **and the harvest
> *completeness* seam** (`closure_eq_stabilizerAt_empty_of_coversOrbits`: `closure gens = StabilizerAt ∅`
> under a path-fixing coverage witness `CoversOrbits`, so the folded chain reproduces the residual group
> *and* its order). **The coverage witness is now DE-CLASSED** (2026-06-04, axiom-clean):
> `coversOrbits_of_residualInvolutive` / `closure_eq_stabilizerAt_of_residualInvolutive` discharge
> `CoversOrbits` for the **whole exponent-2 / elementary-abelian-(`Z₂^d`)-residual class in one theorem** —
> the cross-branch analogue of `theorem_2_HOR_of_pPolynomial`, sidestepping the per-class `Aut(CFI)≅Z₂^β⋊Aut(H)`
> structure theorem (the harvested involutions generate the residual whatever their internal description, no
> `Φ(σ)` lift). **The remaining content is per-class: supply `ResidualInvolutive` at a gauge-regime `S`** (for
> CFI, the seeds kill the `Aut(H)` factor) — a single focused predicate, *not* GI-hard — and the concrete
> computable BSGS (A4, validation-only). The abstract cross-branch mechanism toward "reaches a rigid or
> Cameron residual on all classes" is grounded.
>
> Companions: [orbit-recovery](./chain-descent-orbit-recovery.md) (the witness layer this generalizes),
> [harvest-window](./chain-descent-harvest-window.md) (the Leg-A lemma this realizes),
> [cascade-oracle](./chain-descent-cascade-oracle.md) + [linear-oracle](./chain-descent-linear-oracle.md)
> (the two oracles, **unified here** — those docs' order-model firing is now legacy),
> [exhaustive-obstruction](./chain-descent-exhaustive-obstruction.md) §0.5 (the seal: `EdgeGenerates`/
> `PPolynomial` are concrete **D1**).

---

## 1. The problem with classes

The chain-descent canonizer is correct and budget-bounded for *any* oracle; the open content is
**T-C** — discovering each cell's orbit partition cheaply
([`chain-descent-calculator.md`](./chain-descent-calculator.md) §4). The tractable side of T-C is
**orbit recovery**: after a bounded number of fresh-colour individualizations, 1-WL cells coincide
with `Aut`-orbits, so refinement *computes* the orbit partition. The standalone development of this
is [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md).

That development proceeded **class by class**, and the proofs are real (axiom-clean): CFI over
odd-degree bases (`theorem_1_HOR_cfi_oddDeg`, a 10-case cascade), schurian schemes at rank 2, then
rank 3 (the 7-cycle), rank 4 (the 9-cycle) via an "isolation bootstrap." Each rung is a multi-week
Lean grind, and **the rungs never end** — every new graph family is a new class. A canonizer whose
correctness proof is "one theorem per family" does not converge.

**The de-classing turn (this doc):** identify the *one* abstract fact each class was really
witnessing, prove the reduction to it once, and supply that fact for whole *structural* families at
a stroke. The class-specific proofs remain — as **witnesses**, the bottom layer — but they are no
longer the strategy.

---

## 2. The engine: bounded-round saturation of an extensive operator

[`ChainDescent/Saturation.lean`](../GraphCanonizationProofs/ChainDescent/Saturation.lean) (depends
only on Mathlib, so both schemes and Leg A can use it). The single load-bearing lemma:

> **`exists_iterate_isFixed_within`.** Let `f : Finset α → Finset α` be **extensive**
> (`∀ s, s ⊆ f s`) and preserve an `f`-invariant bound `B ⊇ s₀`. Then iterating `f` from `s₀`
> reaches a **fixpoint within `|B| − |s₀|` rounds** (`∃ k ≤ |B| − |s₀|, f (f^[k] s₀) = f^[k] s₀`).

The proof is the strict-cardinality-growth pigeonhole: each non-fixpoint round strictly grows the
set (extensive + `≠` ⟹ `⊊`), bounded by `|B|`, so a fixpoint is hit in `≤ |B| − |s₀|` steps. The
`B = univ` corollary is `exists_iterate_isFixed` (bound `|α| − |s₀|`). Plus the reusable primitives
`iterate_subset_succ`, `iterate_mono`, `iterate_eq_of_isFixed`, `iterate_subset_of_invariant`.

**Why this is the right shape.** Two very different recovery arguments are both "a *bootstrap
closure* reaches the top within a bounded number of rounds":

| | carrier `α` | operator `f` | fixpoint means | bound `B` |
|---|---|---|---|---|
| **Schemes** | relations `Fin (rank+1)` | add relations pinned by counts into the isolated set | every relation isolated | `occursFromV` (≤ n) |
| **Leg A** | vertices `Fin n` | individualize a moved / symmetry-only vertex | base reached / no step left | support (or `univ`) |

Same engine, same termination proof, different operator. That is the whole point: the recovery
*reasoning* is class-agnostic; only the operator's per-round content differs.

---

## 3. Schemes de-classed — `EdgeGenerates` and the metric family

`Scheme.lean §10.12–§10.13`. The class-specific input each per-rank scheme proof was witnessing is:
**the edge relation generates the scheme** — by iterated common-neighbour counting, every relation
becomes detectable from the edge.

### 3.1 The closure and `EdgeGenerates`

- `isolationStep G v j0 Iso` — one closure round: keep `Iso`, add every relation occurring from `v`
  that is **uniquely pinned** by `Iso` (`IsoPinned`: unique among non-diagonal relations with its
  `(edge-membership, intersection-counts into Iso)` signature — exactly the `hsep` hypothesis of the
  existing `relIsolatedAt_succ` bootstrap). It is **extensive** and preserves the bound
  `occursFromV` (the relations actually occurring from `v`, `≤ n` — the honest carrier, since
  empty/non-occurring relations are *vacuously* isolated, `relIsolatedAt_of_not_occurs`).
- **`EdgeGenerates G v j0`** — the closure of `{R₀, R_{j0}}` reaches every occurring relation.
- `stage_relIsolatedAt` — the bridge: relations in the `m`-th closure round are isolated at depth
  `m+1` (wrapping `relIsolatedAt_succ`).
- **`theorem_2_HOR_of_edgeGenerates`** — the engine bounds the closure depth at `≤ n`, the stage
  lemma turns it into full isolation, `convergence_of_all_isolated` finishes. *The uniform
  interface: the old `…rank_two_J_singleton` / `…intersectionSeparates` / `…intersectionSeparates3`
  theorems are now special cases.*

### 3.2 The structural class: P-polynomial (metric / distance-regular) schemes

`EdgeGenerates` is still a hypothesis. `PPolynomial` discharges it for an **entire structural
family**:

> **`PPolynomial G v j0`** — the relations are a distance ladder `R 0 = R₀, R 1 = j0, …, R rank`
> (bijective onto all relations, each occurring from `v`) with a **tridiagonal** intersection array
> (`intersectionNumber (R a) j0 (R k) = 0` for `|a−k| ≥ 2`) and **nonzero subdiagonal**
> (`c_k = intersectionNumber (R (k−1)) j0 (R k) ≠ 0`). This is the abstract form of
> *distance-regular*.

`pPolynomial_pinned`: distance `R k` is uniquely pinned by the strictly-closer distances — a rival
`R m` dies to a single off-band zero (`m > k`: count into `R(k−1)` vanishes while `c_k ≠ 0`;
`m < k`: its own `c_m ≠ 0` clashes with the off-band zero into `R(m−1)`). A closure-fixpoint
induction (via `IsoPinned.mono` — pinning is monotone in the isolated set) walks the ladder out to
`EdgeGenerates`. Hence:

> **`theorem_2_HOR_of_pPolynomial`** — orbit recovery for **every P-polynomial schurian scheme
> graph**: cycles, Johnson `J(m,k)`, Hamming, all DRGs — *one theorem, no per-scheme data.*

### 3.3 Honest scope (do not over-claim)

Unconditional "all schurian schemes converge" is **false**, and correctly so: an imprimitive scheme
whose edge cannot resolve a sub-scheme makes the closure **deadlock** — and there 1-WL genuinely
does *not* recover orbits (`Step2` fails). `EdgeGenerates` is the exact *necessary* condition;
`PPolynomial` is the clean *structural sufficient* one. The de-classing widens the proved class from
"rank ≤ 4 by hand" to "all metric/DRG", not to "everything".

---

## 4. Leg A transplanted — the same engine drives visible-symmetry recovery

`Cascade.lean`. **Leg A** of the oracle-capability seal is the *visible / unconditional* (D1) case:
a symmetry exposed by symmetry-only individualization
([`chain-descent-harvest-window.md`](./chain-descent-harvest-window.md)). The scheme work is its
rehearsal; the transplant:

### 4.1 The general support induction (every graph reaches a base)

A subtlety the transplant forced into the open: **"visible symmetry ⟹ symmetry-only step" is
false** — CFI moves points yet its cells are *coarser* than orbits (that is exactly `¬D1`). So the
honest, class-agnostic induction tracks **moved** vertices, weaker than symmetry-only:

- `MovedAt adj P S v` — some residual automorphism (fixing `S`) moves `v`. Immediately `v ∉ S`.
- `movedStep` — individualize a moved vertex if one exists; extensive; its fixpoint is exactly a
  **base** (`isBase_of_no_moved`: no moved vertex ⟺ trivial residual).
- **`exists_isBase_saturated`** — from any `S₀`, individualizing moved vertices **reaches a base
  within `≤ n − |S₀|` rounds**, for *every* graph. This is the faithful, class-agnostic
  formalization of the harvest-window §2 trichotomy's **termination** ("case (c) strictly shrinks
  the residual's support, bottoming out at the base").

The companion `exists_symmetryOnly_saturated` does the same for the *symmetry-only* (strict D1)
chain (`soStep`); it saturates but, in the hidden case, at a non-recovered node (→ D2 / the wall).

### 4.2 Metric D1 for free (the scheme win feeds Leg A)

Schemes recover at **depth 1** for the whole metric family (§3.2; schemes are algebraic, so 1-WL
captures them after one individualization regardless of diameter). So the one-step chain `∅ → {v}`
is visibly recoverable:

> **`visiblyRecoverable_pPolynomial`** — D1 (`VisiblyRecoverable`) for **every P-polynomial scheme
> graph**, generalizing the rank-2 `visiblyRecoverable_scheme` to all Johnson/Hamming/cycle/DRG
> schemes. Leg-A's D1 is now class-general on the metric class.

### 4.3 `EdgeGenerates` is a concrete D1; `PPolynomial` is *graded* D1

The seal's **D1** ([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)) is
"the symmetry is exposed by a poly-length symmetry-only process." `EdgeGenerates` *is* that for
scheme graphs (the edge exposes everything by bounded-round counting); `PPolynomial` is the
**graded** form (distance leveling = BFS exposure). This is the template for eventually reformulating
the Leg-A screen predicates (`Findable`/`VisiblyRecoverable`) in saturation-closure style.

---

## 5. Leg B de-classed — the linear oracle's firing folded into recovery

`Cascade.lean`, `CascadeOracle.lean`. **Leg B** of the seal is the *hidden-abelian* (¬D1 ∧ D2) case:
a true symmetry 1-WL cannot see (CFI gauge twists). The **linear oracle** is its component. It was
designed *early*, before the recovery framework, so it grew a parallel completeness machinery routed
**class by class** through CFI gadgets — the same drift the scheme ladder had, in a different file.

### 5.1 The early-design drift

The linear oracle fired in the **order model**: read a unique candidate twist off one branch's
reverse-symmetric propagation, relabel the canonical leaf matrix (`canonAdj`), and prune
(`RealizableFlip` / `ConfigSwap`). Discharging that for CFI ran through `CFIGadgetFlippable` /
`CFIParityDecisionFlippable` (gadget cycle-space, `tw(H)`) — **per class** — and bottomed out at
**σ-cell-coherence**, a property `cell_split_uniform_false` proves *false* in exactly the regime the
oracle must handle (the decision pair shares a 1-WL cell). The abstract D2 predicate `ResidualAbelian`
was left **orphaned** — defined but unused by the firing story.

### 5.2 The fold (the colour model)

The fix mirrors Leg A's spine-vs-semantic resolution (§4.1): bypass the order-model packaging and fire
in the **colour model**, straight from recovery. The colour-model harvest needs only the orbit *map*
`g r₁ = r₂` (not a *swap*), so the order-model σ-coherence never arises:

- **`harvest_fires_of_cellsAreOrbits_discrete`** (`CascadeOracle.lean §C.2`) — at a recoverable +
  discrete footprint, *any* colour-match candidate verifies (it equals the orbit automorphism, via
  `harvest_isAut_of_discrete` + `warmRefine_transport`). **`colourMatch_exists_of_cellsAreOrbits`** —
  the firing certificate *exists* (the orbit automorphism *is* a colour-match). Together: Leg B fires,
  **order-free and class-agnostic**.
- The order-model machinery (`ConfigSwap`, `CFIGadgetFlippable`, `canonAdj`-firing, `RealizableFlip`)
  is now **legacy** — kept for the order-model *soundness* story, *not* the firing path. The
  σ-coherence route (`C1b.3`) is **retired**, not pending.

### 5.3 The precise D2 predicate (wiring `ResidualAbelian` in)

`ResidualAbelian` (commuting) is too weak to make an orbit *map* a *swap*; the precise D2 is exponent-2:

- **`ResidualInvolutive`** — every residual automorphism is an involution (the honest `Z₂^d` /
  elementary-abelian form, exactly CFI's gauge group).
- `residualAbelian_of_involutive` — exponent-2 ⟹ abelian, so the orphaned `ResidualAbelian` is now
  *implied* by the precise predicate.
- `orbitPartition_swap_of_involutive` / `swap_of_cellsAreOrbits_involutive` — an involutive orbit
  witness is automatically a *swap* (`g a = b ∧ g b = a`); at a recoverable node every same-cell pair
  has one. (The *swap* is what the legacy order model needs; the colour model (§5.2) needs only the
  map — which is exactly why the swap turned out to be order-model packaging.)

---

## 6. The unified oracle: one harvest, two faces; the seal as depth

With both legs folded into recovery, the **cascade oracle** (Leg A, visible) and the **linear oracle**
(Leg B, hidden-abelian) are **one mechanism, two faces** ([cascade-oracle §1.4](./chain-descent-cascade-oracle.md)):
at a recoverable node, construct the colour-match permutation from the two branch colourings, verify
it edge-by-edge, harvest it before branching. The only differences are *what the verified map turns
out to be* (a visible orbit map or a hidden gauge twist) and *how deep* one individualizes to reach
recovery. The calculator/overview "two oracles" framing is the pre-fold view.

So the seal's **D1 / D2 / ¬D1∧¬D2** trichotomy is now a **depth** distinction on one recovery axis:

- **D1 (visible)** — recovery at depth `base(g)` (the symmetry's own support; Leg A).
- **D2 (hidden-abelian)** — recovery at a deeper *concealment* depth (`tw(H)` for CFI; Leg B).
- **¬D1 ∧ ¬D2 (the wall)** — recovery never at *polynomial* depth (non-abelian / hidden Johnson).

Class-specificity is thereby quarantined into a **single depth-witness predicate** (`CascadesAt` /
`recoverableByDepth`); the firing argument itself is class-agnostic. The per-class theorems (CFI
`tw(H)`, schemes depth-1) are *witnesses* populating that predicate — see §8.

---

## 7. What is proved vs. open

**Proved (axiom-clean, full build green):**
- The engine (`Saturation.lean`).
- Scheme general convergence `theorem_2_HOR_of_edgeGenerates`; the metric structural class
  `theorem_2_HOR_of_pPolynomial`.
- Leg A: support-induction termination `exists_isBase_saturated`; D1-chain termination
  `exists_symmetryOnly_saturated`; metric D1 `visiblyRecoverable_pPolynomial`.
- **Tight support bound** `base(g) ≤ |support|` — `exists_isBase_saturated_support`: the
  moved-vertex closure reaches a base within `≤ |movedSet adj P S₀|` rounds (the residual
  *support* at `S₀`), not the full `n`. Supporting pieces: the **interval-invariant** engine
  variant `exists_iterate_isFixed_within'` / `iterate_subset_of_invariant'`
  (`Saturation.lean`); `MovedAt.anti` (the moved-set shrinks as `S₀` grows — the residual at
  `S ⊇ S₀` is a residual at `S₀`); `movedSet` / `movedStep_subset_bound` (the bound is
  `S₀ ∪ movedSet`, interval-invariant under `movedStep`). All axiom-clean.
- **Leg A recovery-axes separation** — `recoverableAt_base_iff_discrete` /
  `forcedNode_recoverable_iff_discrete` (recovery ⟺ `Discrete` at the base; the symmetry axis closed,
  the IR-stickiness axis the sole residual), `movedSet_eq_nonsingletonCells_of_recoverable`
  (`forcedNode` refinement-computable where recovery holds), and the full relabel equivariance
  `forcedNode_relabel` (the forced node commutes with *any* `σ`). All axiom-clean.
- **Leg B fold + D2 predicate** — `harvest_fires_of_cellsAreOrbits_discrete` /
  `colourMatch_exists_of_cellsAreOrbits` (the colour-model firing, §5.2); `ResidualInvolutive`,
  `residualAbelian_of_involutive`, `orbitPartition_swap_of_involutive`,
  `swap_of_cellsAreOrbits_involutive` (the D2 predicate + swap certificate, §5.3). All axiom-clean.
- **M-B — the concrete colour-match oracle** (`CascadeOracle.lean §C.4`, all axiom-clean): `colourMatchPerm`
  (the rankPerm composition), `colourMatchPerm_eq_of_orbit` (`= g` via `vertexRank_comp`),
  `matchOracle : CascadeOracleSpec` (construct-and-check), `matchOracle_orbitMapSpec` (**unconditional**
  soundness), `matchOracle_cellComplete` / `_cascadeComplete` (completeness reduced to discretizing-depth
  + `CellsAreOrbits`), `matchOracle_verdictIsoInvariant` (flag iso-invariance, free). `vertexRank_comp` /
  `rankPerm_comp` relocated to `ChainDescent.lean`.
- **M-C — multi-step depth** (`CascadeOracle.lean §C.5`, all axiom-clean): `indivWithSet` (+
  `indivWithRep_eq_indivWithSet` singleton bridge), `indivWithSet_transport`, the lifted harvest bricks
  (`IsColourMatchSet`, `colourMatchSet_complete`, `colourMatchSet_unique`, `harvestSet_isAut_of_discrete`),
  `colourMatchPermSet` + `colourMatchPermSet_eq_of_orbit`, and `colourMatchSet_exists_of_cellsAreOrbits` —
  the harvest fires at a *set*-discretized footprint (CFI `tw(H)` depth over a sequence).
- **M-D — the multi-step oracle + the lockstep discharged** (`CascadeOracle.lean §C.6` + `Cascade.lean`,
  all axiom-clean): `matchOracleSet expand : CascadeOracleSpec` (multi-step `matchOracle`),
  `matchOracleSet_orbitMapSpec` (**unconditional** soundness), the `LockstepExpand` predicate (equivariance
  of the exploration rule), `matchOracleSet_cellComplete` / `_cascadeComplete` / `_verdictIsoInvariant`
  (completeness + flag iso-invariance reduced to set-footprint discreteness + `CellsAreOrbits` +
  `LockstepExpand`), and the **discharge** `forcedExpand` + `lockstepExpand_forcedExpand` (the lockstep is a
  *theorem* via `movedSet_image`, not a hypothesis). So the multi-step oracle's only open completeness
  input is the depth witness ("B's core").
- **Depth-witness bridge (single-rep) — LANDED 2026-06-03, axiom-clean** (`CascadeOracle.lean §C.4b`):
  `samePartition_indivWithRep_insert` (the single-rep footprint `indivWithRep D r` has the *same
  partition* as the indexed `individualizedColouring (insert r D)` — `r` marked uniquely either way),
  `warmRefine_samePartition` (warmRefine respects `samePartition`, via `warmRefine_agree_off'`),
  `discrete_of_samePartition`, and **`discrete_indivWithRep_of_discrete_insert`** — M-B's depth witness
  `hdisc` *follows* from discreteness of the **indexed** `individualizedColouring (insert r D)`, i.e. from
  the `RecoverableByDepth` / discretizing-depth framework, **class-agnostically**. Motivated and validated
  by the feasibility probe (`docs/Archive/ChainDescent/{probe,cfi}.lean`). **Asymmetry the probe pinned:**
  the bridge is single-rep *only* — the multi-step *uniform* `indivWithSet D R` (`|R|≥2`, one block) is
  strictly coarser than the indexed `individualizedColouring (D ∪ R)`, so M-D's `hdiscSet` has *no* such
  bridge (CFI(K4): indexed seeds discretize at the empty commit, uniform-block seeds do not). The single
  rep is the discretizing-mode harvest's natural unit.
- **§C.7 — honest single-rep completeness (LANDED 2026-06-03, axiom-clean):** `matchOracle`'s
  capstone `matchOracle_cascadeComplete` quantifies its two hypotheses (`hdisc`, `hco`) over *every*
  node, which is **false at shallow CFI nodes**. §C.7 restates it the way the descent actually works:
  `matchOracle_fires_of_insertDiscrete` fires on a genuine `Aut_D` orbit pair from **only** the indexed
  (`recoverableByDepth`-shaped) discreteness — *no* `hco`, since construct-and-check consumes the orbit
  witness directly; `matchOracle_orbit_of_fire_mono` propagates a deep certification to shallower
  decision nodes via `OrbitPartition.mono`; `matchOracle_certifies_iff_orbit_of_insertDiscrete` is the
  exact-orbit-decider iff *at the discretizing depth*. Net: the two false ∀-node hypotheses are replaced
  by one honest "fire deep, prune shallow" obligation, isolating localisation-1b cleanly.
- **§C.8 — Leg 1: the level-coloured sequence (LANDED 2026-06-03, axiom-clean), and its wall.** The
  indexed-sequence reformulation declassing §9 item 3 called for. **A1** (`indivWithSeq`,
  `samePartition_indivWithSeq`, `discrete_indivWithSeq_of_discrete_union`) colours the exploration by
  *position* `n+1+i`, so its depth witness `hdiscSeq` **is** A1-reducible to `recoverableByDepth` (the
  §C.4b bridge generalized to sequences). **A2 transport** (`idxOf_map_of_injective`,
  `indivWithSeq_transport`, the lifted `colourMatchPermSeq` / `…_exists`) works because `map` preserves
  position under an injection. The full oracle `matchOracleSeq` (sound unconditionally; complete modulo
  `hdiscSeq` + `hco` + `LockstepExpandSeq`) is assembled. **But the obstruction is conserved, not
  removed:** `lockstep_disc_imp_stab_trivial` proves `LockstepExpandSeq ∧ hdiscSeq ⟹ stab_{Aut_D}(v) = 1`
  — the two completeness hypotheses are **jointly satisfiable only in the single-rep regime**. For
  genuine multi-step CFI (`tw ≥ 2`) they are *incompatible*: no iso-invariant ordering of a moved orbit
  exists (that would itself be a canonizer), so all three colourings (uniform → `hdiscSet` false; indexed
  → transport false; position → `LockstepExpandSeq` false) are stuck. **The multi-step moved orbit cannot
  be harvested within-cell by the discretizing colour-match; it belongs to the cross-branch
  (stabilizer-chain / Schreier–Sims) harvest.** This bounds the discretizing oracle's reach to exactly
  the single-rep / `stab(v)=1` case (`matchOracle`, §C.7) and **corrects the "one harvest fires both
  legs" thesis (§6): the unified colour-match covers single-step (visible Leg A, depth-1 schemes) but
  *not* multi-step hidden (Leg B at `tw ≥ 2`).**

**Leg A's own frontier — now closed except the flagged residual.** What was the deep Leg-A frontier
(the tight support bound, forced-node iso-invariance, the recovery-axes reduction, arbitrary-relabel
equivariance) all **landed (2026-06-02)** — see the Proved list above. The single Leg-A residual is
**3b — the IR-stickiness axis**: "is `warmRefine` discrete at the
base?" is unconditionally *false* (multipede / IR-blind-spot, strategy §15 gap 5) — correctly
*flagged*, not solved; per-class it is the existing `CascadesAt` / `recoverableByDepth` witnesses.

**The full current frontier (both legs), and where to pick up, is §9.** It includes 3b above plus the
Leg-B items (M-B, M-C, "B's core") and the cross-cutting flag-iso-invariance and wall.

---

## 8. How this reframes the older docs

A fresh reader should treat the class-specific material as the **bottom (witness) layer**, not the
plan:

- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) — the tier-1/tier-2 /
  rank-by-rank / OddDegree-CFI proofs are **witnesses** populating the abstract predicates
  (`CascadesAt`, `EdgeGenerates`, `VisiblyRecoverable`). They are correct and load-bearing as
  examples; they are not "the proof obligation list". The general theorems above subsume the
  scheme ladder for the metric class.
- [`chain-descent-harvest-window.md`](./chain-descent-harvest-window.md) — the harvest-window
  lemma's **termination** half is now *proved* class-agnostically (`exists_isBase_saturated`); its
  D1 screen is realized for the metric class. The "depth = `base(g)`" claim is the support induction
  here; the *tight* bound is open item (1).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3/§5 — "cascade" as a class is
  de-classed for metric schemes: no per-family certification predicate is needed there. **§6 (the
  linear oracle) and §9's "two oracles"** describe the **order-model** firing (read a twist off
  propagation, relabel `canonAdj`); that is now **legacy / soundness-only** — firing is the unified
  colour-model harvest (§5–§6 here). Treat calculator §6 as the order-model soundness story, not the
  current firing path.
- The gentle intro is now [`00-START-HERE.md`](./00-START-HERE.md) (the old
  `simplified-overview` §6/§7 likewise framed cascade and linear as two mechanisms with §7's
  order-model twist-reading; that overview is archived — the current firing is the one harvest, §6 here).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §12/§13 — `warm_6_2` / the spine /
  invariant 6.2 are **proved and load-bearing**, but their stated *role* as "what the linear oracle
  fires on" (coupled component, provenance) is the legacy order model; in the current model they back
  the substrate, and firing iso-invariance attaches to the forced node (`forcedNode_relabel`).
- [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.5 — the
  seal's **D1/D2/wall** has concrete realizations (`EdgeGenerates`, `PPolynomial`) and is now a
  **depth** distinction (§6); the seal itself (exhaustiveness, leg C) is unchanged.

**Bottom line for a fresh reader.** The project's recovery-and-firing story is no longer "enumerate
graph classes and grind each in Lean," nor "two separate oracles." It is: *one engine; one reduction
to an abstract recovery predicate; structural theorems discharging it for whole families; one
recovery-based harvest firing both oracles; and per-class proofs only as witnesses populating a single
depth predicate.* The work left (§9) is genuine — the construction unit M-B, the depth witnesses, and
the wall — not another rung on a class ladder.

---

## 9. Where to pick up — the current frontier

For a fresh reader continuing the work. Every item is *isolated* by the de-classing; the first four
are bounded (not GI-hard), the last two are the honest boundary.

1. **M-B — the concrete colour-match oracle — LANDED 2026-06-02, axiom-clean.** Built in
   `CascadeOracle.lean §C.4` (construct-and-check, *not* the existential-shortcut trap): `colourMatchPerm`
   = the rankPerm composition `(rankPerm χ_w)⁻¹ * (rankPerm χ_v)` from the two discrete branch colourings;
   `colourMatchPerm_eq_of_orbit` (= `g` via `rankPerm_inv_mul_eq_of_match` ← `vertexRank_comp` +
   `colourMatch_complete`); `matchOracle : CascadeOracleSpec` (constructs `colourMatchPerm`, returns it
   **iff** it verifies `IsAut ∧ P-preserving ∧ fixes D ∧ v↦w`). **Soundness `matchOracle_orbitMapSpec`
   (`OrbitMapSpec`) is unconditional** — the checks *are* the `OrbitPartition` witness. **Completeness**
   `matchOracle_cellComplete` / `_cascadeComplete` (`CellComplete`/`CascadeComplete` via
   `cascadeComplete_of_cellsAreOrbits`) is reduced to exactly the two named-open hypotheses: every node
   one-step-discretizing (= the exposure-depth witness, items 2–3) and `CellsAreOrbits` everywhere (=
   localisation). **Flag iso-invariance** falls out free (`matchOracle_verdictIsoInvariant` via
   `verdictIsoInvariant_of_complete` — item 4 discharged on the recoverable class). `vertexRank_comp` /
   `rankPerm_comp` relocated `LinearOracle.lean` → `ChainDescent.lean`. The single M-B residual is the
   *depth witness* (items 2–3), not the construction.
2. **M-C — multi-step depth — LANDED 2026-06-03, axiom-clean** (`CascadeOracle.lean §C.5`).
   `indivWithSet n S R` (M-B's `indivWithRep` generalized to an explored *set* `R`, **uniformly**
   coloured — the only transport-compatible choice, since an orbit aut moves `R` so distinct/index
   colours break `χ₂∘g=χ₁` and a `g`-dependent distinct colouring is unavailable to the oracle);
   `indivWithRep_eq_indivWithSet` (singleton bridge); `indivWithSet_transport` (the `indivWithRep_transport`
   generalization). The harvest bricks lift verbatim (the generic `colourMatch_eq_aut`/`_isAut` + the new
   transport): `IsColourMatchSet`, `colourMatchSet_complete`, `colourMatchSet_unique`,
   `harvestSet_isAut_of_discrete`; plus `colourMatchPermSet` + `colourMatchPermSet_eq_of_orbit` (the
   multi-step `colourMatchPerm = g`) and `colourMatchSet_exists_of_cellsAreOrbits` (the firing certificate
   exists for any exploration set, partner = `R₁.image g`). **The harvest now fires at a footprint
   discretized by a *set* (a sequence), not just one rep.** The remaining piece — the multi-step *oracle*
   `matchOracleSet` and the **lockstep** argument that branch-`w`'s independently chosen exploration set
   equals `(branch-v's).image g` — is **M-D** (below / cascade-oracle §2.6).
3. **"B's core" — the depth witness.** That an abelian (D2) residual's footprint discretizes within
   *polynomial* depth. **Substrate-conditional** (CFI `tw(H)`, schemes depth-1 are the witnesses); NOT
   provable unconditionally (false for unbounded treewidth) — this is the tractable/flagged
   discriminator, the honest residual of completeness.
   *Refined 2026-06-03 (feasibility probe + the single-rep bridge, §7).* Two findings sharpen this:
   (i) The **single-rep** depth witness `hdisc` is now *reduced* to the indexed-recovery framework by
   `discrete_indivWithRep_of_discrete_insert` — it follows from `Discrete (warmRefine (individualizedColouring
   (insert r D)))`, the discretizing-recovery shape `recoverableByDepth_cfi`/`_scheme` speak about. So the
   remaining single-rep work is supplying that *indexed* discreteness (a `Discrete`-at-recovery witness for
   the discretizing mode) — **not** a new per-class cascade ladder. (ii) The probe established the **mode
   capability boundary** (the answer to the oracle-conflation concern): the colour-match oracle is the
   *discretizing* mode (needs a discrete footprint); CFI satisfies that but its cells equal its gauge orbits
   only at the recovery depth, while **schemes recover *structurally*** (cells = orbits at non-singleton
   cells) and so are *not* consumed by `colourMatchPerm` at all — the structural mode needs a different
   concrete construction. (iii) The **multi-step uniform** `hdiscSet` has *no* bridge (uniform marking of a
   `≥2` set is strictly coarser than indexing it). **The indexed-sequence reformulation this called for was
   built (§C.8 / Leg 1) and proven to fail (2026-06-03).** `matchOracleSeq` colours the exploration by
   *position* (A1-reducible `hdiscSeq`) and transports (`indivWithSeq_transport`), but
   `lockstep_disc_imp_stab_trivial` shows its two completeness hypotheses `LockstepExpandSeq ∧ hdiscSeq ⟹
   stab_{Aut_D}(v) = 1` — **jointly satisfiable only in the single-rep regime.** The obstruction is
   *conserved*: uniform → `hdiscSet` false; indexed → transport false; position → `LockstepExpandSeq`
   false; the boundary (an iso-invariant ordering of a moved orbit) does not exist, since that *is* a
   canonizer. **Conclusion (the redirect): the multi-step moved (hidden-abelian, `tw ≥ 2`) orbit is NOT
   harvestable within-cell by any discretizing colour-match. It must go through the cross-branch
   transversal harvest — the stabilizer-chain / Schreier–Sims object (Part A), now established as
   *required*, not merely consolidating.** The discretizing oracle's reach is exactly the single-rep /
   `stab(v)=1` case (`matchOracle`, §C.7). Remaining open content is then: the **cross-branch/Part-A
   harvest** for multi-step hidden symmetry, the localisation/`hco` half (1b, single-rep, NOT GI-hard),
   and the structural-mode oracle for schemes.
4. **Flag iso-invariance** ([strategy §15 gap 2](./chain-descent-strategy.md)) — the constructed
   oracle's verdict as a function of iso-invariant ids. `colourMatchPerm` is built from iso-invariant
   colourings, so it *should* hold by construction; the obligation is undischarged.
5. **The IR-stickiness axis (3b)** — "is `warmRefine` discrete at the base?" Unconditionally *false*
   (multipede / IR-blind-spot, strategy §15 gap 5); correctly **flagged**, not solved.
6. **The wall (leg C)** — hidden non-abelian (¬D1 ∧ ¬D2, Cameron/Johnson); `(O*)-existence` ≡ GI ∈ P.
   Out of scope by design (the seal classifies it; it does not solve it).
