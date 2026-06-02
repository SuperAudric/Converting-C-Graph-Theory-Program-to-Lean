# Chain descent — the harvest-window lemma (support-bounded orbit recovery)

> **Update (2026-06-02) — the termination is now PROVED class-agnostically; see
> [`chain-descent-declassing.md`](./chain-descent-declassing.md) for the current approach in full.**
> The trichotomy's *termination* half (§2: "case (c) strictly shrinks the residual's support,
> bottoming out at the base") is now a theorem — `exists_isBase_saturated` (`Cascade.lean`), for
> **every** graph — via a generic saturation engine (`Saturation.lean`) that also de-classed the
> scheme rank ladder. Leg-A's D1 now holds for the whole metric / distance-regular family
> (`visiblyRecoverable_pPolynomial`, generalizing the rank-2 `visiblyRecoverable_scheme`). The
> seal's **D1** has concrete realizations: `EdgeGenerates` = D1, `PPolynomial` = *graded* D1. Note
> a correction the build forced: "visible symmetry ⟹ symmetry-only step" is **false** (CFI), so the
> general induction tracks *moved* vertices, not symmetry-only ones. **Update (2026-06-02):** the
> *tight* support bound `base(g) ≤ |support|` and forced-node iso-invariance both **landed**
> (`exists_isBase_saturated_support`, `forcedNode`/`forcedNode_relabel`); the recovery axes are
> formally separated (`recoverableAt_base_iff_discrete`), leaving only the **IR-stickiness axis**
> (multipede, flagged). The current frontier is **de-classing doc §9**. The original STATUS below
> stands for the lemma's own development.

> **STATUS: concept VALIDATED; screen predicates + Phase-0/Phase-1 anchors BUILT in
> Lean, axiom-clean. Open core = "B's core" (the general D2 bridge).**
>
> The harvest-window lemma is a **class-agnostic** reframing of why the cascade /
> linear oracles find their symmetry within a bounded depth: the bound comes from the
> **support** of the symmetry (a stabilizer-chain induction), with the per-class bounds
> (`tw(H)` for CFI, depth-1 for schemes) as corollaries. It routes through the
> footprint-matching harvest, so it **never invokes σ-cell-coherence** (the `C1b.3`
> blocker the abelian-sufficiency handoff stalled on). In seal terms it is **legs A+B
> in one object** ([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)).
>
> **Built in Lean** (`ChainDescent/Cascade.lean`, all `[propext, Classical.choice, Quot.sound]`):
> the screen is the inductive **`Findable`** (`recovered` = `Discrete` / `abelian` =
> `ResidualAbelian ∧ ¬IsBase` / `step` = `SymmetryOnlyStep` + recurse) — the
> **sequential** screen, not the flat `D1∨D2` (which was incomplete; see §6). Its
> primitives `SymmetryOnlyStep` (D1) and `ResidualAbelian` (D2) are defined; the
> bound-carrying **`FindableWithin`** + `recoverableByDepth_of_findableWithin` give
> *non-vacuous* soundness; **`findableWithin_cfi_gauge`** discharges the D2 leg's
> recoverability field for the odd-degree CFI gauge via the axiom-free
> `recoverableByDepth_cfi` (the D2 analogue of `visiblyRecoverable_scheme`). The
> explicit-chain `VisiblyRecoverable` is retained as the unconditional-D1 / structural
> witness.
>
> **Leg (a) — the harvest *argument* — is PROVED and class-agnostic (2026-06-02).**
> `colourMatch_eq_aut` / `harvest_isAut_of_discrete` (`CascadeOracle.lean` §C.2, axiom-clean):
> at a **discrete** footprint the colour-match candidate *equals* the orbit automorphism `g`
> (forced by `warmRefine_transport` + injectivity), so it verifies — **no σ-coherence, no
> cycle construction, no rank rebasing** (hence no conjugation gap). The decisive consequence
> (the re-orientation, §2.4): **class-specificity lives only in the *witness* that a graph has
> a polynomial-depth harvest window** (satisfies `CascadesAt` / D1∨D2), *never in the harvest
> itself*. The seal **is** that characterization (D1/D2 are abstract), so the spine
> `Findable ⟹ RecoverableByDepth ⟹ CellComplete [leg-(a)] ⟹ CascadeComplete` is class-agnostic *at
> the reduction level* — its two ends and leg-(a) are proved; **the concrete `CellComplete` wiring
> (`colourMatchPerm` + `matchOracle`) is the open unit M-B**, planned in
> [cascade-oracle §2.6](./chain-descent-cascade-oracle.md). The single irreducible class-specific
> remainder is **leg B's depth** — hidden-abelian: *how
> deep until the gauge becomes visible* (CFI's `tw(H)`, via cycle-space; **substrate-conditional**) —
> *not* leg A (visible: depth = `base(g)`, the symmetry's own support, seal-characterizable). The
> per-class CFI/scheme theorems are **witnesses**, and CFI's cycle-space proof is specifically the
> leg-B depth witness.
>
> **Open (= the next priority, "B's core").** The **general D2 bridge** —
> `ResidualAbelian ⟹ recoverable` beyond the CFI(odd-deg) anchor — is the load-bearing
> open core, equal to `AbelianSufficiencyHolds` (LinearOracle §L.6) and the cascade-1b
> obligation generalized. It is **substrate-conditional** (CFI over an unbounded-treewidth
> base is abelian yet only discretizes at large depth, so the bound is the
> tractable/flagged discriminator — not an unconditional `∀ S, abelian ⟹ recoverable`).
> Also open: the multi-step **D1 negative** (CFI / hidden-Johnson `¬D1` — the
> symmetry-only chain gets stuck). Neither is GI-hard.
>
> **Build/check:** `cd /workspace && bash scripts/build.sh` (serial, ~25s); `lake env
> lean` a file with `#print axioms <name>` for axiom-cleanliness.
>
> **Development history** — how the screen, the sequential fix, F1/F2, and the
> Phase-0/1 anchors were reached, dated exchange-by-exchange — is archived at
> [`Archive/ChainDescent/chain-descent-harvest-window-journal.md`](./Archive/ChainDescent/chain-descent-harvest-window-journal.md);
> §6 below distills its conclusions.
>
> Origin: user reconstruction of the harvest-window argument (2026-06-01), refined over
> several exchanges into the induction form of §2; hoisted to this clean statement form
> 2026-06-02.
> Companions: [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
> (the per-class results this generalizes — and whose forward-compat note §1 *asks* for
> this statement), [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
> §1.1/§3/§4.4 (the recursion whose depth this bounds),
> [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
> §0.5 (the seal — this is legs A+B in one object),
> [`chain-descent-abelian-sufficiency-handoff.md`](./chain-descent-abelian-sufficiency-handoff.md)
> §0 (what it supersedes).

---
## 0. The one-sentence contribution

The cascade oracle's harvest depth was *defined* as "how deep must I individualize before the
refinement **footprint singletonizes**" ([cascade-oracle §1.1](./chain-descent-cascade-oracle.md));
the per-class proofs bound it by treewidth (CFI) or scheme-depth or — for the linear leg — re-derive
it through σ-cell-coherence. **The claim of this doc: that depth is bounded for *any* findable
symmetry by the size of its support, via a stabilizer-chain induction, with the per-class bounds as
corollaries — and the bound doubles as the hidden-Johnson screen.** It routes through the
footprint-matching harvest, so it **never invokes σ-coherence** (the `C1b.3` blocker).

> **Refined (§2.4).** Sharper than first stated: the class-agnostic, now-*proved* part is the harvest
> **argument** (leg-(a) — "a symmetry with a harvest window is harvested"). The support bound
> `base(g)` is the depth for the **visible** (leg-A) case; a **hidden-abelian** (leg-B) symmetry's
> window closes at its **concealment** structure (CFI's `tw(H)`, via cycle-space, *substrate-conditional*),
> *not* its support. So "depth = support" is the leg-A reading; the depth is a class-specific witness,
> the argument is not.

---

## 1. The harvest window, restated

At a true-symmetry / apparent-decision cell the oracle (cascade or linear — same core,
[cascade-oracle §"Central design claim"](./chain-descent-cascade-oracle.md)) does:

1. **Explore** one representative `r₁` (individualize, warm-refine → child partition).
2. **Read the footprint** — the cells that split parent → child.
3. **All-singleton footprint** ⟹ construct the orbit-map `r₁ ↦ r_j` by canonical-id sub-cell
   matching, **verify it edge-by-edge on `adj`**, harvest before the branch loop reaches `r_j`.
4. **Non-singleton footprint** ⟹ **recurse** one level deeper and re-attempt.

The depth of step-4 recursion is the **harvest window**. Two facts pin its meaning:

- **All-singleton footprint = unique candidate twist.** Singletons match uniquely, so the read-off
  map is forced. This is the abelian / non-Johnson side of [calculator §6](./chain-descent-calculator.md)'s
  boundary. The recursion deepens precisely *to make the candidate unique*.
- **Verification is against `adj`, not the individualized state.** So individualizing a support
  vertex to *expose* the symmetry never "loses" it — the harvested map is certified on the original
  graph. This removes the naive worry that individualization breaks `g`.

The existing depth bounds are instances: `≈ tw(H)` for CFI (`theorem_1_HOR_cfi_oddDeg`), depth 1 for
schurian schemes (`recoverableByDepth_scheme`), `≤ n` trivially. The thesis of §2 is that all of
these are shadows of one support-counting bound.

---

## 2. The lemma (induction form)

Let `g` be a **residual symmetry** at a descent node — an automorphism of `adj` fixing the committed
path (the individualized singletons), acting non-trivially on the current partition. Write `S =
support(g)` (its moved points) and `base(g)` for the base size of its residual action (the number of
individualizations needed to kill it; `≤ |S|`). A **target pair** (w.r.t. `g`) is a within-cell
decision pair `{v, g(v)}`.

> **Harvest-window lemma (proposed).** If `g` **satisfies the screen `D1 ∨ D2`** (§3 — i.e. `g` is
> unconditional, *or* hidden with a unique candidate), then descending the spine, every decision falls
> into a trichotomy *relative to the current residual `g`*:
>
> - **(a) target pair of `g`** → `g` is **harvested** (footprint-matching, verified on `adj`);
> - **(b) outside `support(g)`** → `g` survives **unchanged**, descend;
> - **(c) within `support(g)`, not a target pair** → `g` **transforms**: pass to a residual `g′`
>   with `support(g′) ⊊ support(g)` (a stabilizer / conjugate).
>
> The induction (case (c) strictly shrinks the support) bottoms out at a **forced node** — unique
> and iso-invariant by the spine — from which **every** branch harvests the residual. The conclusion
> is `RecoverableByDepth adj P (b(g))` with `b(g)` the **recoverability depth** (§6) — small in the
> structural recovery mode, the discretizing depth in the discretizing mode; *mode is orthogonal to
> the `D1∨D2` screen* (§6).

### 2.1 Why each leg holds

- **(a)** is the cascade/linear harvest of §1 — **PROVED class-agnostic** (`colourMatch_eq_aut` /
  `harvest_isAut_of_discrete`, §2.4): at a discrete footprint the colour-match candidate *is* the
  orbit automorphism `g` (via `warmRefine_transport` + injectivity), so verification succeeds. D1
  gives a cascade (structural or discretizing) certification, ¬D1∧D2 the linear unique-twist read.
- **(b)** is immediate: `g` fixes the individualized vertex, so it remains an automorphism of the
  refined coloured graph.
- **(c)** is the **transforming case** — the one that makes this an induction rather than a flat
  pigeonhole. See the grounding example below.
- **Termination + the forced node.** Each (c) step strictly shrinks the support; (b) steps leave it;
  (a) ends it. Once the residual's support is the only non-singleton structure left, the next
  within-cell decision is forced to be (a) or another (c) — and convergence bottoms out at the
  residual base. By the **spine** (`spine_branch_independent` / `warmRefine_agree_off'`): the tree of
  *partitions* is a path, the partition at a node is a function of the *decision set* not its order,
  and the target-cell selector is partition-invariant — so "the node where only the residual's
  support remains" is a **unique, iso-invariant** node, and **every exit from it harvests** ⟹ the
  verdict is choice-independent (**iso-invariance via exhaustive convergence**).

### 2.2 Grounding example — the transforming case is benign

**k-prism vs. k-cycle-with-a-pendant-on-every-vertex.** Both carry the order-`k` rotation `g`; they
differ only in how much 1-WL forces for free (pendants self-distinguish cycle vertices; the prism
keeps its two rings 1-WL-identical). After individualizing cycle vertex `0`, a "diagonal" decision
`{i, k−i}` is **not** a target pair of the *rotation* — but it **is** a target pair of the
*reflection through 0*, the residual symmetry once `0` is fixed. So it harvests a *different* group
element (case (c) → harvest), and the descent terminates cleanly in **both** graphs. This is the
witness that case (c) does not stall: a within-support non-target decision passes to a residual whose
target pair is then forced.

### 2.3 The bound: `base(g)` vs `n − |S|`, and the IR-deficiency caveat

The sharp depth is **`base(g) ≤ |S|`** (individualize within the support to pin `g`). The cruder
`n − |S|` envelope ("individualize the whole complement, then the support is forced as a cell")
coincides with `base(g)` only when **1-WL cells = orbits**. The gap between them is
**1-WL-sticky fixed points** — non-support vertices refinement cannot singletonize. That gap is the
**IR-deficiency axis** (the multipede / IR-blind-spot direction, [strategy §15 gap 5](./chain-descent-strategy.md)),
*not* the symmetry axis. Keep them separate: the harvest-window bound is about symmetry; the
stickiness is a different (orthogonal) failure cause. Both are polynomial, so the *polynomial claim*
survives either way.

There is a **third** reason `base(g)` can undershoot the recovery depth, and it is neither
stickiness nor a different symmetry: a **hidden** symmetry, where 1-WL cells ≠ orbits at `base(g)`
not because refinement is stuck but because the symmetry is *concealed* (CFI's gauge — visible only
after `tw(H)` individualizations break the cycle space). For such a symmetry the recovery depth is the
**concealment** structure, not `base(g)` (a single gauge flip has `base = 1` yet stays hidden to depth
`tw(H)`). This is the leg-B / hidden-abelian case of §2.4, and it is **substrate-conditional**
(unbounded `tw` breaks the bound). So the depth has three regimes — `base(g)` (visible / leg A),
concealment (hidden-abelian / leg B), and the orthogonal IR-stickiness — only the first of which is
support-bounded.

### 2.4 Class-agnostic argument vs. class-specific witness (the seal-driven split)

The lemma decomposes into two halves with **opposite** dependence on the graph class:

- **The harvest *argument* — "harvest window ⟹ harvested" — is class-agnostic, and proved.**
  Leg (a) is `colourMatch_eq_aut` (`CascadeOracle.lean` §C.2): if a genuine orbit automorphism `g`
  exists and the footprint is **discrete**, the colour-match candidate `t` (§1 step 3) satisfies
  `t = g` — forced by `warmRefine_transport` (automorphism-equivariance) + injectivity of a discrete
  colouring — so `t` verifies. That is the whole of "exit ⟹ harvest," and it touches no class
  structure: no σ-coherence, no cycle, no rank rebasing (so it sidesteps both the `C1b.3` blocker and
  the linear oracle's conjugation gap, which were artifacts of the σ-/rank *packaging*). The sole
  hypothesis it consumes is **discreteness of the footprint**.

- **The class-specificity is entirely in the *witness* that the graph *has* a polynomial-depth
  harvest window** — that `CascadesAt adj P k` holds for polynomial `k` (cells = orbits at a bounded
  `S`). `theorem_1_HOR_at_depth` (proved, axiom-free) already turns `CascadesAt k` into orbit recovery
  class-agnostically; the per-class `cfi_cascades_polynomially_oddDeg` (CFI, `tw(H)`) and the scheme
  analogue (depth 1) are **witnesses populating `CascadesAt`**, not steps of the harvest argument.

**Why the seal *is* the characterization.** Because `D1`/`D2` are defined *abstractly* ("∃ a
poly-length symmetry-only individualization exposing the symmetry" / "one branch exposes a unique
candidate" — [exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)), the chain

```
   Findable (D1∨D2)  ⟹  RecoverableByDepth  ⟹  CellComplete  ⟹  CascadeComplete
        seal predicate      (has harvest window)   (leg-(a))        (harvested)
```

is class-agnostic end-to-end at the *reduction* level: `recoverableByDepth_of_findableWithin` and
`complete_of_cellComplete_recoverable` are proved, and leg-(a) (`colourMatch_eq_aut` + the M-A bricks
`colourMatch_complete`/`_unique`) is the **engine** for the `CellComplete` step. **Status (be
precise):** the `CellComplete` *step for a concrete oracle is not yet discharged* — that is the open
unit **M-B** (build `colourMatchPerm` + `matchOracle`; see
[cascade-oracle §2.6](./chain-descent-cascade-oracle.md) for the plan and the circularity trap to
avoid). What *is* settled is that the graph class enters *only* by populating the disjuncts of
`Findable` — as the witness, not the reasoning. That is the sense in which the harvest window is
"defined by the seal."

**Where class-specificity is irreducible — and it is leg B, not leg A.** The depth `k` at which the
window closes splits by leg:

- **Leg A (visible / D1, *any* group incl. non-abelian — Johnson, schemes).** `k = base(g) ≤ |support(g)|`,
  bounded by the **symmetry's own support**. "Visible ⟹ window at `base(g)`" leans only on the
  symmetry being refinement-exposable (D1's definition), so it is seal-characterizable — the target
  for a class-agnostic leg-A.
- **Leg B (hidden abelian / ¬D1∧D2 — CFI).** `k` = *how deep until the hidden gauge becomes visible*,
  which is **not** `base(g)` (a single gauge flip has small support yet stays hidden until its whole
  cycle is broken). It is a property of the *hiding structure* — `tw(H)` for CFI, via cycle-space —
  and is **substrate-conditional** (unbounded `tw` breaks the polynomial bound; the tractable/flagged
  discriminator). This is the only place CFI's cycle-space theory is irreducible, and it is exactly
  **"B's core"** (`AbelianSufficiencyHolds` / the general D2 bridge).

So the harvest window **unifies legs A and B**, but they differ precisely where the seal would want:
A's depth is the *symmetry*, B's depth is the *concealment*. Leg C (hidden non-abelian) is the
absence of a window — the wall.

---

## 3. The screen = the seal's `D1 ∨ D2` (the hidden-Johnson boundary)

> **Provenance.** This statement is where the two specialization tests and the seal landed the screen.
> Earlier drafts said "the footprint singletonizes" (too narrow — only the discretizing mode, §6),
> then "`CellsAreOrbits` within `b(g)`" (correct but *vacuous as a screen* — it equals "recoverable",
> §6). The screen proper is the predicate below; the modes are an orthogonal recovery-depth axis.

The lemma's one load-bearing hypothesis — the **screen** — is, conditioned on *a symmetry exists*, the
oracle-capability seal's discriminator disjunction **`D1 ∨ D2`**
([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)):

- **`D1` — unconditional.** `g` is consumable by symmetry-only individualization, *without* committing a
  real decision ([deferred-decisions §5](./chain-descent-deferred-decisions.md)). The cascade leg (A).
- **`¬D1 ∧ D2` — hidden, unique candidate.** `g` is invisible to refinement, but one branch's
  propagation exposes a *unique* twist (⟺ abelian / `Z₂` per decision —
  [calculator §6](./chain-descent-calculator.md)). The linear leg (B).
- **`¬D1 ∧ ¬D2` = `¬screen`** — hidden, non-abelian, no unique candidate: many automorphisms resolve the
  decision (`A_k` / hidden Johnson), constructible only by cross-branch triangulation. The
  split-or-Johnson wall. The Cameron leg (C) — **the flag, exported as data.**

Why this is the right form — and why neither earlier candidate was:

- **Negation-complete ⟹ exhaustiveness is free.** `D1 ∨ (¬D1∧D2) ∨ (¬D1∧¬D2)` is a tautology; there is
  no fourth species. "The screen holds, or we are at the wall" needs *no* classification — the seal's
  structural improvement.
- **Neither false-in-regime nor vacuous.** σ-coherence was machine-checked false where it was needed;
  "`CellsAreOrbits` within `b`" / the mode-disjunction are vacuously *true* (= "recoverable at some
  depth", §6). `D1∨D2` is structural — both sides populated — and is the actual oracle-capability
  boundary.
- **The recovery modes are orthogonal to it (§6).** Mode (structural/discretizing) is governed by
  point-stabilizer granularity and describes recovery *depth*; the screen is governed by visibility +
  uniqueness. Independent axes (GRR = `D1` + discretizing).

**The screen doubles as the flag — operationally.** We never *decide* the screen (that needs the orbit
partition = GI-hard). The cascade/linear oracles *attempt* to certify (construct + edge-verify the
witnesses) and **flag on budget-exceed** — sound by construction. `D1∨D2` ⟹ certification succeeds within
budget; `¬screen` ⟹ it exhausts the budget = the flag. The flag is distinguished from the IR-blind-spot
flag at flag time by **residual group order** (non-trivial ⇒ Johnson-like; trivial ⇒ IR blind spot —
[strategy §14](./chain-descent-strategy.md)), and the un-certified residual is the **data exported to leg
C** ([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)).

The target theorem this enables — *"every symmetry except hidden-Johnsons-of-the-class is removed"* — is
**legs A + B of the seal in one object**, class-agnostic. The seal's remaining leg — **leg C**
(`¬D1∧¬D2`) — is, dually, the **consistency check on this screen's D1/D2**: a *recoverable* graph (or any
demonstrably non-Cameron one) that lands in `¬D1∧¬D2` is a D1/D2 **leak**, not a Cameron section. The
`CFI(Kₘ)` flat-screen escape of §6 was exactly such a catch (remediated by a D1/D2 refinement; in general a
leak may instead be closed by a new oracle or re-routed into an existing one). See
[exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md), the diagnostic reading.

---

## 4. What it is for, and what it supersedes (if valid)

**For:**
- **Leg A (cascade capability) in general form.** Orbit recovery for *any* findable symmetry, not
  per-class. Today general convergence of the footprint recursion is **axiomatic** (only odd-degree
  CFI + schurian schemes are axiom-free — [orbit-recovery status](./chain-descent-orbit-recovery.md));
  a proved support/base bound replaces that axiom for the whole findable class at once. This is
  exactly the class-agnostic restatement the orbit-recovery doc's forward-compat note §1 requests.
- **Folding leg B into leg A.** The abelian/linear mechanism becomes "the special case where the
  footprint singletonizes fast," not a separate program.

**Supersedes (if valid):**
- **The σ-cell-coherence route / `C1b.3`.** The harvest at a target pair is footprint-matching, not a
  `ConfigSwap`; the σ-coherence conjunct was an artifact of the order-individualization *packaging*.
  This route is recorded reciprocally as **option 5 of [handoff §0.5](./chain-descent-abelian-sufficiency-handoff.md)**
  (which logs it as substantiating that doc's option 1 — "the `ConfigSwap` over-specifies"). The
  `CFIParityDecisionFlippable` / `swapsConfig_off_pair_of_local` line is not needed for firing.
- **The per-class depth derivations** (`tw(H)` for CFI, scheme-depth) become **corollaries**
  (specializations of `base(g)`), not independent proofs.

**Does NOT supersede / reuse:**
- The **soundness** chain (`canonAdj_eq_of_configSwap`, etc.) — orthogonal, still the soundness story.
- The **C1b construction** `exists_even_triangle` / `exists_even_cycle` — these build the gadget `g`
  and show it acts on the pair (the "target pair exists / `g` acts" half). Only the coherence wrapper
  drops; the construction is reusable as the `g`-exists witness.

---

## 5. The three gaps (status)

| Gap | What | Status |
|---|---|---|
| **1** | Firing requires `CellsAreOrbits adj P S` at the residual base (cells coincide with orbits). | **= the hypothesis = the screen** (§3). **Corrected by §6:** the condition is `CellsAreOrbits`, achieved by *either* mode — discretizing (singletons, `cellsAreOrbits_of_discrete`) or structural (non-singleton cells, `orbitPartition_swap_of_twin` / scheme transitivity). "Footprint singletonizes" is only the discretizing case. Load-bearing; the wall boundary relocated, not removed. |
| **2** | Is the recursion single-path (cost `O(depth)`) or exploratory (`O(n^depth)`) at the bound? | **RESOLVED — not a parked discrepancy.** The cascade-oracle build review (cascade-oracle §4.4) settled it: the recursion is **lockstep, `k`-additive single-path** — each rep descends its own single path along the same iso-invariant cell-id sequence, cost `O(k · tw(H) · n²)`. The linear-oracle §8.1 "mirror-read" was the aspirational form, *corrected away* at build time. The only residual is the `O(n³)`-vs-`O(n⁴)` committed-reuse optimization — not a soundness or polynomiality gap. |
| **3** | Path-determinism / iso-invariance of "the forced node." | **Spine + (c)-induction.** Spine gives the *path* is deterministic and the forced node is unique+iso-invariant; the (c)-induction gives the forced node *exists* under premature support decisions (it's "residual support is all that remains," not literally "complement individualized"). Closing step: every exit harvests ⟹ choice-independent. |

---

## 6. Validation + current state (summary)

> The dated, exchange-by-exchange development log this section distills is archived at
> [`Archive/ChainDescent/chain-descent-harvest-window-journal.md`](./Archive/ChainDescent/chain-descent-harvest-window-journal.md)
> (old §6.1–§6.13). What follows is the settled state.

**The two specialization tests passed — and revealed a two-mode structure.** The
lemma was first checked against the two proved instances, at the conclusion level
`RecoverableByDepth adj P b`:

- **Schurian scheme** (`recoverableByDepth_scheme`, `b = 1`) — the **structural**
  mode: `CellsAreOrbits` holds at *non-singleton* cells via the scheme's transitivity,
  no discretization needed.
- **Odd-degree CFI** (`recoverableByDepth_cfi`, `b = baseSize`) — the **discretizing**
  mode: `CellsAreOrbits` holds only at discreteness (`cellsAreOrbits_of_discrete`); the
  bound is genuine CFI-theory content, not derivable from a generic support-induction.
  The mode split is visible in the signatures (CFI's theorem carries a `Discrete`
  conjunct; the scheme's does not).

So `b(g)` is the **recoverability depth** (least `|S|` with `CellsAreOrbits adj P S`),
*not* the support `|S|` and not uniformly the residual-group base. The trichotomy
induction is the class-agnostic skeleton; each forced node is discharged by *either* a
structural witness *or* a discretizing-depth bound. (The induction itself already exists
as `cascadeComposition_pathFixing`; the connector to this doc's conclusion is
`recoverableByDepth_of_pathFixing_layers`.)

**The screen is the seal's `D1∨D2`, and the modes are orthogonal to it.** The screen
(the load-bearing hypothesis) is the oracle-capability seal's discriminator
([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)): `D1`
(unconditional — exposable by symmetry-only individualization, the cascade leg),
`¬D1∧D2` (hidden but unique-candidate ⟺ abelian, the linear leg), `¬D1∧¬D2`
(`¬screen` = the Cameron / leg-C flag). It is negation-complete, so exhaustiveness is
free. The recovery *mode* (structural / discretizing) is an orthogonal recovery-*depth*
axis governed by point-stabilizer granularity — **not** the screen (a **GRR** is the
`(D1, discretizing)` off-diagonal that refutes any mode ≡ leg identity; `structural ∨
discretizing` is exhaustive, hence vacuous as a screen).

**The screen is *sequential*, not flat — the central correction.** The flat
single-node `D1∨D2` is **incomplete**: `CFI(Kₘ)` (`m ≥ 3`) is recoverable yet
`¬D1∧¬D2` under it, because it is **mixed** (a visible `Sₘ` over a hidden abelian
`Z₂^β`). The fix is the **sequential** screen — consume the visible `D1` first
(`cascadeComposition` does this), *then* classify the residual `Z₂^β` as `D2`. Three
precision points the audits forced:

- **D1 is per-decision** (`SymmetryOnlyStep`: a non-singleton cell that is a single
  `Aut`-orbit), not full recovery; `VisiblyRecoverable` is the derived all-D1-steps
  closure.
- **D2 needs the `¬IsBase` guard** (`ResidualAbelian ∧ ¬IsBase`). Bare `ResidualAbelian`
  is *vacuously true on the multipede* (trivial residual), which would assert the IR
  blind spot is D2-recoverable — false. The guard keeps the multipede in `¬Findable`
  (residual-order trivial), so leg C's escape is exactly *non-trivial non-abelian*.
- **F1:** the stop disjunct is **`Discrete`**, not bare `CellsAreOrbits` (which is
  vacuously true at `∅` for any vertex-transitive graph — would falsely mark Johnson
  Findable). **F2:** the *operational* "non-trivial residual ⟹ Johnson-like" flag signal
  is abelian-blind; the predicate-level separator is "non-trivial *non-abelian* ⟹
  Cameron."

**Phase 0 / Phase 1 (soundness + the D2 anchor).** `FindableWithin` carries a *specific*
bound (the flat `∃ b` form was vacuous via `recoverableByDepth_univ`), so
`recoverableByDepth_of_findableWithin` is non-vacuous. `findableWithin_cfi_gauge`
discharges the D2 leg's recoverability field for the CFI gauge with the **axiom-free**
`recoverableByDepth_cfi` — the D2 analogue of the D1 anchor `visiblyRecoverable_scheme`.
The `ResidualAbelian`/`¬IsBase` *hypotheses* stay the consumed-not-decided D2 predicate
(deciding them is GI-hard; the oracle flags on budget-exceed).

**Leg C audits this screen.** Because the screen *is* the seal's negation-complete
`D1∨D2`, the seal's **leg C** (`¬D1∧¬D2`) doubles as a **consistency check on the
D1/D2 definitions** ([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md),
the diagnostic reading): a recoverable graph landing in `¬D1∧¬D2` is a D1/D2 *leak*, not
a Cameron section. The `CFI(Kₘ)` flat-screen escape above was exactly such a leak,
caught and fixed — here by a D1/D2 refinement; in general a leak may instead be closed
by a new oracle, or by re-routing the case into an existing one (the diagnostic does not
dictate which).

**Naming map (provisional → as-built).** The planning sub-sections used provisional
names; as built: the flat `Findable := (∃ b, VisiblyRecoverable …) ∨ ResidualAbelian`
became the **inductive sequential `Findable`**; the single `recoverableByDepth_of_findable`
split into the bound-free `Findable` (classification) + bound-carrying `FindableWithin`
+ `recoverableByDepth_of_findableWithin` (non-vacuous soundness); `VisiblyRecoverable` is
retained as the explicit-chain unconditional-D1 witness.

**Open (= B's core).** The general D2 bridge (`ResidualAbelian ⟹ recoverable` beyond
CFI(odd-deg) = `AbelianSufficiencyHolds` = cascade-1b generalized, substrate-conditional)
and the multi-step D1 negative. See the STATUS block.

## 7. Honest caveats (so the concept does not over-claim)

- **The wall is not removed.** The screen (`D1∨D2`, §6/§6) is doing all the hard-boundary work; it
  *is* the seal's `D1∨D2` boundary, with `¬screen = ¬D1∧¬D2` the split-or-Johnson wall. The win is
  **organizational and general** — proving the bound the per-class / σ-coherence routes couldn't, and
  unifying legs A+B — not an escape from the open hard core.
- **It is a hypothesis until §6 passes.** The induction's termination + the forced-node iso-invariance
  are argued, not proved; the specialization test is the gate.
- **`b(g)` is the recoverability depth, and it is mode-dependent (§6).** Resolved by the tests: it is
  the least `|S|` with `CellsAreOrbits` — small in the structural mode (scheme `b=1`), the discretizing
  depth in the discretizing mode (CFI `b=baseSize`). Not the support, not uniformly the group base. The
  per-class bound is supplied by whichever mode fires; only the trichotomy skeleton is class-agnostic.

---

## 8. Pointers

- **Lean (specialize against):** `spine_branch_independent` / `SpineChain.branch_independent`,
  `warmRefine_agree_off'` (`ChainDescent.lean` §15); `recoverableByDepth_scheme`,
  `recoverableByDepth_cfi` (`CascadeOracle.lean`); `theorem_1_HOR_cfi_oddDeg`,
  `cfi_cascades_polynomially_oddDeg` (`CFI.lean`); `OrbitPartition`, `CellsAreOrbits`
  (`CascadeOracle.lean`).
- **Lean (the avoided blocker):** `cell_split_uniform_false` (`ChainDescent.lean:464–491`) — the
  σ-coherence falsity this route sidesteps; `samePartition_pair` (`~2776`).
- **Lean (reusable `g`-construction):** `exists_even_triangle` / `exists_even_cycle`,
  `IsCFI'.cfiFlipAut` (`CFI.lean §15`).
- **Docs:** [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) (per-class, leg A),
  [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) (the recursion),
  [`chain-descent-abelian-sufficiency-handoff.md`](./chain-descent-abelian-sufficiency-handoff.md) §0
  (the superseded σ-coherence route),
  [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.5 (the
  seal — legs A/B/C).
