# Chain descent — the harvest-window lemma (support-bounded orbit recovery)

> **STATUS: PROPOSED concept (2026-06-01); both specialization tests PASSED — they reveal a two-mode
> structure (§6.1–§6.3).** This doc records a
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
> is `RecoverableByDepth adj P (b(g))` with `b(g)` the **recoverability depth** (§6.3) — small in the
> structural recovery mode, the discretizing depth in the discretizing mode; *mode is orthogonal to
> the `D1∨D2` screen* (§6.4.1).

### 2.1 Why each leg holds

- **(a)** is the cascade/linear harvest of §1, under the screen (`D1∨D2`): D1 gives a cascade
  (structural or discretizing) certification, ¬D1∧D2 gives the linear unique-twist read.
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

## 3. The screen = the seal's `D1 ∨ D2` (the hidden-Johnson boundary)

> **Provenance.** This statement is where the two specialization tests and the seal landed the screen.
> Earlier drafts said "the footprint singletonizes" (too narrow — only the discretizing mode, §6.1),
> then "`CellsAreOrbits` within `b(g)`" (correct but *vacuous as a screen* — it equals "recoverable",
> §6.4.1). The screen proper is the predicate below; the modes are an orthogonal recovery-depth axis.

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
  depth", §6.4.1). `D1∨D2` is structural — both sides populated — and is the actual oracle-capability
  boundary.
- **The recovery modes are orthogonal to it (§6.4.1).** Mode (structural/discretizing) is governed by
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
**legs A + B of the seal in one object**, class-agnostic.

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
| **1** | Firing requires `CellsAreOrbits adj P S` at the residual base (cells coincide with orbits). | **= the hypothesis = the screen** (§3). **Corrected by §6.1:** the condition is `CellsAreOrbits`, achieved by *either* mode — discretizing (singletons, `cellsAreOrbits_of_discrete`) or structural (non-singleton cells, `orbitPartition_swap_of_twin` / scheme transitivity). "Footprint singletonizes" is only the discretizing case. Load-bearing; the wall boundary relocated, not removed. |
| **2** | Is the recursion single-path (cost `O(depth)`) or exploratory (`O(n^depth)`) at the bound? | **Parked sub-investigation.** Docs say exploratory `O(n⁴)` (cascade-oracle §4.4/§4.6); build brief says "lockstep single-path." Reconcile — it's the difference between cheap-at-any-depth and needing a base-size cost argument. C# hasn't hit it empirically (depths bottom out `≈ tw(H)`), but not proof-worthy. |
| **3** | Path-determinism / iso-invariance of "the forced node." | **Spine + (c)-induction.** Spine gives the *path* is deterministic and the forced node is unique+iso-invariant; the (c)-induction gives the forced node *exists* under premature support decisions (it's "residual support is all that remains," not literally "complement individualized"). Closing step: every exit harvests ⟹ choice-independent. |

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

### 6.8 D1 correctness loop — closed at the current (one-step) scope (2026-06-01)

The negative direction, now in [`Cascade.lean`](../GraphCanonizationProofs/ChainDescent/Cascade.lean)
(axiom-clean, build green):

- `visiblyRecoverable_of_cellsAreOrbits_singleton` — positive direction generalised (`CellsAreOrbits adj
  P {v} ⟹ VisiblyRecoverable adj P ∅ 1`); `visiblyRecoverable_scheme` is its scheme corollary.
- **`not_visiblyRecoverable_of_depth_one_fails`** — the **loop-closer**: `(∀ v, ¬CellsAreOrbits adj P
  {v}) ⟹ ¬VisiblyRecoverable adj P ∅ bound`. A chain from `∅` must take a single-vertex first step
  `{v}` needing cells=orbits there; depth-1 failure (CFI's / the hidden Johnson's fingerprint) kills it.
- **`visiblyRecoverable_empty_iff`** — the crisp characterisation: `VisiblyRecoverable adj P ∅ bound ↔
  ∃ v, CellsAreOrbits adj P {v}` (for `bound ≥ 1`). So `¬D1 ⟺ ∀v ¬CellsAreOrbits{v}` — the screen's
  D1-negation lands *exactly* on depth-1 failure.

**What "closed" means, honestly.** The iff *also documents a limitation*: the current def collapses
**D1-from-`∅` to one-step (depth-1) recovery**. That is correct for the current formalised scope —
rank-2 schemes recover at depth 1 (`visiblyRecoverable_scheme`), CFI fails at depth 1 — so the loop is
closed *there*. But it **mis-tiles depth-≥2-recoverable graphs** (the Johnson / Hamming *graphs* —
recoverable DRGs, **not** the hidden-Johnson *wall*): they would be `¬D1` and, if non-abelian, wrongly
`¬screen` (a false wall). The fix is the **multi-step** form (per-step symmetry-only: the individualised
*cell* is a single orbit, reaching cells=orbits at the end), whose scheme instance needs vertex-
transitivity — now known **derivable from `SchurianSchemeGraph.schurian_transitive` at relation 0**
(checked this turn). That generalisation is the flagged next refinement.

The concrete CFI discharge — `∀v, ¬CellsAreOrbits adj P {v}` (CFI's depth-1 cells-coarser-than-orbits
fact) — stays the isolated structural residual (needs CFI gadget analysis, not formalised).

Both screen predicates and the screen are in Lean. **Remaining: the D2 bridge (`ResidualAbelian ⟹
hwit`, = cascade-1b generalized); the multi-step D1 generalisation (+ scheme transitivity); the concrete
CFI ¬D1 discharge.**

---

## 7. Honest caveats (so the concept does not over-claim)

- **The wall is not removed.** The screen (`D1∨D2`, §6.4/§6.4.1) is doing all the hard-boundary work; it
  *is* the seal's `D1∨D2` boundary, with `¬screen = ¬D1∧¬D2` the split-or-Johnson wall. The win is
  **organizational and general** — proving the bound the per-class / σ-coherence routes couldn't, and
  unifying legs A+B — not an escape from the open hard core.
- **It is a hypothesis until §6 passes.** The induction's termination + the forced-node iso-invariance
  are argued, not proved; the specialization test is the gate.
- **`b(g)` is the recoverability depth, and it is mode-dependent (§6.3).** Resolved by the tests: it is
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
</content>
</invoke>
