# Chain descent — the de-classing turn: non-class-specific orbit recovery via the saturation engine

> **STATUS (2026-06-02): the organizing strategy for orbit recovery.** Read this
> *before* the per-class material in
> [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) — it reframes
> that doc's tier-1/tier-2/rank-by-rank narrative as a **witness layer**, not the plan.
>
> **The thesis.** Orbit recovery was being discharged *class by class* (CFI odd-degree, then
> even/saturated; schemes rank-2, then rank-3, rank-4, …). There are **unboundedly many
> classes**, so that ladder stalls the project. The turn: prove recovery **non-class-specifically**
> — once, behind a generic engine — with the per-class theorems demoted to *witnesses* that
> populate an abstract predicate.
>
> **What is built (all axiom-clean `[propext, Classical.choice, Quot.sound]`; full build green):**
> - **The engine** — [`ChainDescent/Saturation.lean`](../GraphCanonizationProofs/ChainDescent/Saturation.lean):
>   an *extensive* `Finset` operator saturates to a fixpoint in bounded rounds
>   (`exists_iterate_isFixed_within`). One lemma, two consumers.
> - **Schemes de-classed** — `Scheme.lean §10.12/§10.13`: `EdgeGenerates` (the uniform
>   condition) and **`theorem_2_HOR_of_pPolynomial`** — *the entire metric / distance-regular
>   family (cycles, Johnson, Hamming, all DRGs) in one theorem*, no per-rank data.
> - **Leg A transplanted** — `Cascade.lean`: the support induction (`exists_isBase_saturated`),
>   the D1-chain termination (`exists_symmetryOnly_saturated`), and metric D1
>   (`visiblyRecoverable_pPolynomial`) — the *same engine* now drives Leg A.
>
> **Tight support bound — LANDED (2026-06-02).** `base(g) ≤ |support|` is now proved
> (`exists_isBase_saturated_support`, `Cascade.lean`), via an **interval-invariant** engine
> variant (`exists_iterate_isFixed_within'`, `Saturation.lean`) — invariance required only on the
> `f`-reachable sets `S₀ ⊆ s ⊆ B`, not all of `B`. Axiom-clean. See §5.
>
> **Forced-node iso-invariance — LANDED (2026-06-02), not via the spine.** The choice-free
> canonical base is `forcedNode adj P S₀ := S₀ ∪ movedSet adj P S₀` (individualize the whole
> residual support): `forcedNode_isBase` (a base, no `Classical.choice`) + `forcedNode_image` /
> `movedAt_image_iff` (automorphism-equivariant, hence iso-invariant). The spine route is blocked
> (its `defaultColouring` is index-based, not aut-invariant); the *semantic* `movedSet` is directly
> equivariant. Axiom-clean. See §5.
>
> **Recovery axes separated — LANDED (2026-06-02).** `recoverableAt_base_iff_discrete` /
> `forcedNode_recoverable_iff_discrete`: at the canonical base, orbit recovery is *exactly*
> `Discrete (warmRefine …)`, so the two axes (symmetry / IR-stickiness) are formally separated and
> the flag is pinned to `¬ Discrete`. Plus `movedSet_eq_nonsingletonCells_of_recoverable`:
> `forcedNode` is refinement-computable where recovery holds. Axiom-clean. See §5 item 3.
>
> **Arbitrary-relabel equivariance — LANDED (2026-06-02).** The `(adj, P)`-relabel action
> (`relabelAdj` / `relabelP`) is built and `forcedNode_relabel` proves the forced node commutes
> with **any** relabelling `σ` (not just `σ ∈ Aut`) — full canonization-sense iso-invariance.
> Axiom-clean. See §5 item 3c.
>
> **Open (the remaining frontier):** only the IR-stickiness axis itself (3b — the multipede
> boundary, correctly *flagged*, not solved; per-class it is the existing `CascadesAt` witnesses).
> See §5.
>
> Companions: [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) (the witness
> layer this generalizes), [`chain-descent-harvest-window.md`](./chain-descent-harvest-window.md)
> (the lemma this realizes — Leg A), [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
> §0.5 (the seal: `EdgeGenerates`/`PPolynomial` are concrete **D1**).

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

## 5. What is proved vs. open

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

**Open (the deep frontier — each needs genuine design, not a quick add):**
1. ~~**Tight support bound** `base(g) ≤ |support|`.~~ **DONE (2026-06-02)** —
   `exists_isBase_saturated_support`, above. The engine variant whose invariance hypothesis is on
   `f`-*reachable* sets (⊇ `S₀`), not all of `B`, is `exists_iterate_isFixed_within'`; it is
   reusable as predicted.
2. ~~**Forced-node iso-invariance.**~~ **DONE (2026-06-02), via a cleaner route than the spine.**
   `soStep`/`movedStep` use `Classical.choice`, so their endpoint is not canonical. The fix
   bypasses the choice entirely: `forcedNode adj P S₀ := S₀ ∪ movedSet adj P S₀` individualizes
   the **whole residual support** at once, which is already a base (`forcedNode_isBase` — fixing
   every moved point trivializes the residual group), and it is **automorphism-equivariant**
   (`forcedNode_image` / `movedAt_image_iff`, via the conjugate `g π g⁻¹`), hence a canonical
   function of iso-invariant data — not an arbitrary choice. `forcedNode_residual_invariant`: the
   node is fixed by the very symmetry it resolves. All axiom-clean. **Why not the spine** (the
   originally-anticipated route): the spine reaches discreteness of the *index-based*
   `defaultColouring`, which is **not** automorphism-invariant, so it cannot constrain the
   semantic residual group (the Fact-B bridge `orbit_iff_eq_of_discrete_warmRefine` only fires
   through `individualizedColouring`, matching `defaultColouring` only at `D = univ`). The
   semantic `movedSet` is directly equivariant — no spine needed. *Remaining* (folds into item 3):
   the arbitrary-relabelling form (any `σ`, not just `σ ∈ Aut`) is the same conjugation over an
   `(adj, P)`-relabel action; refinement-*computing* `forcedNode` is the recovery content below.
3. **Full recovery** tying the two **orthogonal axes** (harvest-window §2.3): symmetry consumed
   (= base reached) **and** no IR-stickiness ⟹ `Discrete` at the base ⟹ `CellsAreOrbits`. Now
   **separated into pieces** (most of it landed 2026-06-02):
   - **3a — the reduction, DONE.** `recoverableAt_base_iff_discrete` /
     `forcedNode_recoverable_iff_discrete`: at a base (in particular `forcedNode`), orbit recovery
     is *exactly* `Discrete (warmRefine …)`. This **separates the two axes formally** — once the
     symmetry is consumed, the *only* remaining obstruction is IR-stickiness, and the flag is
     pinned to `¬ Discrete` at the canonical node. (`⟸` is `cellsAreOrbits_of_discrete`; the base
     upgrades it to an iff.) Axiom-clean.
   - **3d — computability of the support, DONE.**
     `mem_movedSet_iff_nonsingleton_cell_of_recoverable` /
     `movedSet_eq_nonsingletonCells_of_recoverable`: at a recoverable node, `v` is moved iff it
     sits in a **non-singleton 1-WL cell**, so `movedSet`/`forcedNode` are refinement-computable
     exactly where recovery holds — the bridge from math object to algorithm input. Axiom-clean.
   - **3b — the stickiness axis (the flagged boundary), OPEN by design.** "Is `warmRefine`
     discrete at the base?" is unconditionally *false* (multipede / IR-blind-spot, strategy §15
     gap 5) — correctly *flagged*, not solved. For specific classes it is the existing `CascadesAt`
     / `recoverableByDepth_cfi`/`_scheme` witnesses; deliverable is to wire those in, not prove it
     unconditionally.
   - **3c — arbitrary-relabel equivariance, DONE (2026-06-02).** The `(adj, P)`-relabel action is
     built (`relabelAdj` / `relabelP`), residual automorphisms transport across a relabelling both
     ways (`residualAut_relabel` / `_symm`, via the conjugate `σ π σ⁻¹`), and the canonical node
     commutes with **any** `σ` (not just `σ ∈ Aut`): `forcedNode_relabel : forcedNode (relabel… σ)
     (S₀.image σ) = (forcedNode adj P S₀).image σ` (through `movedAt_relabel_iff` /
     `movedSet_relabel`). This is full canonization-sense iso-invariance of the forced node.
     Axiom-clean.

**Still genuinely hard / out of scope** (unchanged by this turn): the **wall** — hidden
non-abelian (`¬D1 ∧ ¬D2`, Cameron/Johnson), and `(O*)-existence` (≡ GI ∈ P).

---

## 6. How this reframes the older docs

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
  de-classed for metric schemes: no per-family certification predicate is needed there.
- [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.5 — the
  seal's **D1** has concrete realizations (`EdgeGenerates`, `PPolynomial`); the seal itself
  (exhaustiveness, leg C) is unchanged.

**Bottom line for a fresh reader.** The project's recovery story is no longer "enumerate graph
classes and grind each in Lean". It is: *one engine; one reduction to an abstract "the closure
reaches the top" predicate; structural theorems that discharge that predicate for whole families;
and per-class proofs only as witnesses.* The work left is genuine (the §5 frontier and the wall),
not another rung on a class ladder.
