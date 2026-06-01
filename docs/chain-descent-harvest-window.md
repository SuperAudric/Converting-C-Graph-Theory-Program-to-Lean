# Chain descent — the harvest-window lemma (support-bounded orbit recovery)

> **STATUS: PROPOSED concept (2026-06-01), not yet validated.** This doc records a
> class-agnostic reframing of why the cascade/linear oracles find their symmetry within a
> bounded depth — the **harvest window** — derived from the *support* of the symmetry rather
> than from per-class structure (treewidth, σ-coherence). It is a **hypothesis with a designed
> first test** (§6): if it specializes to the two already-proved instances
> (`recoverableByDepth_scheme`, `theorem_1_HOR_cfi_oddDeg`) it is the general tool and they are
> corollaries; if one resists, the resisting case names the missing tool. Written before the
> test so the concept is recorded at peak clarity.
>
> Origin: user reconstruction of the harvest-window argument (2026-06-01), refined over three
> exchanges into the induction form of §2. The motivating concern: the abelian-sufficiency proof
> ([handoff](./chain-descent-abelian-sufficiency-handoff.md)) stalled at a **known-false-in-general**
> σ-cell-coherence conjunct (`C1b.3`), and that conjunct looks like an artifact of the `ConfigSwap`
> *packaging* — not the actual firing condition. This doc is the alternative route that never
> touches σ-coherence.
>
> Companions: [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) (the per-class
> results this generalizes — and whose forward-compat note §1 *asks* for exactly this statement),
> [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) §1.1/§3/§4.4 (the recursion
> whose depth this bounds), [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
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

> **Harvest-window lemma (proposed).** If `g` is **footprint-singletonizing** (§3 — the screen),
> then descending the spine, every decision falls into a trichotomy *relative to the current
> residual `g`*:
>
> - **(a) target pair of `g`** → `g` is **harvested** (footprint-matching, verified on `adj`);
> - **(b) outside `support(g)`** → `g` survives **unchanged**, descend;
> - **(c) within `support(g)`, not a target pair** → `g` **transforms**: pass to a residual `g′`
>   with `support(g′) ⊊ support(g)` (a stabilizer / conjugate).
>
> The induction (case (c) strictly shrinks the support) bottoms out at a **forced node** — unique
> and iso-invariant by the spine — from which **every** branch harvests the residual. Total depth
> to harvest ≤ `base(g)` ≤ `|S|`.

### 2.1 Why each leg holds

- **(a)** is the cascade/linear harvest of §1, under the footprint-singletonizing hypothesis.
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

---

## 3. The footprint-singletonizing hypothesis = the hidden-Johnson screen

The lemma's one load-bearing hypothesis is that `g`'s residual action **singletonizes its footprint
within the residual base bound**. This is *not* a free assumption — it is the wall boundary wearing a
different coat:

- **Findable (in-scope):** the footprint singletonizes within `base(g)` ⟹ unique candidate ⟹ harvest.
- **Hidden Johnson (the wall):** individualizing within the orbit leaves large symmetric sub-cells —
  the footprint **stays non-singleton** past the bound. No unique candidate from one branch
  (cross-branch triangulation needed — exponential).

So **the depth bound doubles as the screen**: a residual whose footprint has not singletonized by
`base(g)` *is* the hidden-Johnson fingerprint, and the run flags. No separate Johnson detector is
needed — this is the "polynomial-or-flag" shape the design already wants. The flag is distinguished
from the IR-blind-spot flag at flag time by **residual group order** (non-trivial ⇒ Johnson-like;
trivial ⇒ IR blind spot — [strategy §14](./chain-descent-strategy.md)), and the un-singletonizing
residual is the **data exported to leg C** (the Cameron leg —
[exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)).

The target theorem this enables — *"every symmetry except hidden-Johnsons-of-the-class is removed"* —
is **legs A + B of the seal in one object**, class-agnostic.

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
  `ConfigSwap`; the σ-coherence conjunct was an artifact of the order-individualization *packaging*
  ([handoff §0.5 option 1](./chain-descent-abelian-sufficiency-handoff.md), now substantiated). The
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
| **1** | Firing requires the footprint to singletonize (unique candidate). | **= the hypothesis = the screen** (§3). Load-bearing; must be *stated* as the residual property, not assumed. It is the wall boundary relocated, not removed. |
| **2** | Is the recursion single-path (cost `O(depth)`) or exploratory (`O(n^depth)`) at the bound? | **Parked sub-investigation.** Docs say exploratory `O(n⁴)` (cascade-oracle §4.4/§4.6); build brief says "lockstep single-path." Reconcile — it's the difference between cheap-at-any-depth and needing a base-size cost argument. C# hasn't hit it empirically (depths bottom out `≈ tw(H)`), but not proof-worthy. |
| **3** | Path-determinism / iso-invariance of "the forced node." | **Spine + (c)-induction.** Spine gives the *path* is deterministic and the forced node is unique+iso-invariant; the (c)-induction gives the forced node *exists* under premature support decisions (it's "residual support is all that remains," not literally "complement individualized"). Closing step: every exit harvests ⟹ choice-independent. |

---

## 6. Validation plan — the designed first test

Before any formalization, **state the lemma against the existing Lean objects and check it
specializes to the two proved instances.** This is decisive either way.

1. **Schurian schemes** — `recoverableByDepth_scheme` (depth-1 witness at the decision node). Check it
   is the lemma with **case (c) terminating at depth 1** (base size 1: one individualization
   singletonizes the footprint).
2. **Odd-degree CFI** — `theorem_1_HOR_cfi_oddDeg` (`k ≤ tw(H)`). Check it is the lemma with
   **`base(g) = tw(H)`** (the gadget flip's residual base = treewidth).

Outcomes:
- **Both fall out** ⟹ the induction is the general tool; the per-class proofs are corollaries; proceed
  to formalize the induction-form lemma.
- **One resists** ⟹ the resisting case names the missing tool exactly (e.g. the CFI proof's structure
  doesn't expose `base(g)` — then we learn the bound needs a different handle than treewidth). Record
  it as a gap entry here and re-plan.

Either outcome is a win and neither commits to the stuck σ-coherence model.

---

## 7. Honest caveats (so the concept does not over-claim)

- **The wall is not removed.** The footprint-singletonizing hypothesis (§3) is doing all the
  hard-boundary work; it *is* the seal's D2 / split-or-Johnson line. The win is **organizational and
  general** — proving the bound the per-class / σ-coherence routes couldn't, and unifying legs A+B —
  not an escape from the open hard core.
- **It is a hypothesis until §6 passes.** The induction's termination + the forced-node iso-invariance
  are argued, not proved; the specialization test is the gate.
- **`base(g)` must be made a usable handle.** "Residual base size" is the right *quantity*, but the
  Lean proofs may expose treewidth / scheme-depth instead. Reconciling those with `base(g)` is part of
  §6, and a mismatch is informative, not fatal.

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
</content>
</invoke>
