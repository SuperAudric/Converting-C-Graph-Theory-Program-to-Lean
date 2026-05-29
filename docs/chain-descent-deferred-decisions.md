# Chain descent — deferred decisions and the rigid-residue hand-off

A scheduling architecture for the descent: **consume all symmetric
decisions first (deferring the real ones), then enumerate the rigid
residue exhaustively.** Two payoffs — the oracle calls become
polynomial (the exponential is confined to an oracle-free phase), and
the rigid residue is handed off *whole* to a potential global solver
rather than guessed at layer-by-layer.

> **Status: BUILT — complex version, default ON 2026-05-28.** Implemented as
> the `EnableDeferral` flag on `ChainDescent` (**default true**): target-cell
> selection prefers a cell the a-priori oracle collapses to one orbit (consume),
> defers real decisions, Phase 2 branches the residue. **Complex version**: real
> decisions are cached (`_knownReal`, path-scoped) and classified once, so the
> oracle work **detaches from the Phase-2 enumeration** (the rigid-residue /
> multipede case — `O(n⁴)·(n−k) + 2^k` instead of `O(n⁴)·2^k·(n−k)`). Foundation
> `real_stays_real` is **proved in Lean**
> ([ChainDescent/CascadeOracle.lean](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean)
> `OrbitPartition.mono` / `real_stays_real`, axiom-light); the cache adds **no new
> Lean obligation** (a cache hit can only over-split — the sound direction per the
> `ITransversalOracle` coverage contract). Sound + iso-invariant: full fast suite
> green incl. exhaustive size-5/6 unique-canonical counts + scramble-invariance +
> Even≠Odd on Petersen / Rook3x3 / K6. The two off==on brute-force cross-checks
> pin `EnableDeferral=false` (they validate oracle pruning on the fixed schedule;
> that transfers to the deferral path since the pruning code is identical).
>
> **Correction to §4 (found while building).** Deferral does **not** reach the
> same lex-min as the lowest-id schedule: the *schedule fixes the leaf
> labelling* (the individualisation order determines `P`, which determines the
> refinement numbering at each leaf), so reordering yields a **different — but
> still iso-invariant — canonical form**. Measured: Rook3x3 (deferral reorders
> at the residual → canonical changes), Petersen (no reorder → canonical
> unchanged). Both stay scramble-invariant and distinguish Even/Odd. Hence
> deferral is **off by default** (preserves the established canonical and the
> off==on oracle cross-check); it is a valid *alternative* canonicaliser, not a
> pure speedup. On CFI it rarely reorders (the cascade oracle already consumes
> every cell except the lone residual), so its real value remains the
> rigid-residue hand-off (§7) for mixed graphs.
>
> *Original note:* a scheduling layer above the two per-decision oracles
> (cascade, linear); it reuses their per-decision classification and changes
> *when* decisions are resolved. Its *clean two-phase* efficiency is
> conditional on the decomposability hypothesis (§5).

For the oracles this schedules:
[`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
(true symmetry), [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
(abelian false symmetry). For the hypothesis its clean form rests on:
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
§8.1 (the (O\*) self-detection lemma / "residue is rigid"). For the
descent and budget it modifies:
[`chain-descent-strategy.md`](./chain-descent-strategy.md).

---

## 1. The idea

The current descent, at every node, refines, picks a target cell, asks
the oracle, and **branches immediately** if the decision is real
(non-symmetric). Real branches recurse, and the oracles run again inside
each of them. So a symmetric decision sitting *below* a real one is
re-discovered and re-consumed in every branch of that real decision.

The deferred-decision workflow splits the descent into two phases:

- **Phase 1 — symmetry consumption.** Walk the decisions. For each, call
  the oracle **once** to classify it:
  - *symmetric* (cascade certifies one orbit, or linear harvests a
    twist) → **consume** it: harvest the generator, reduce the residual.
  - *real* (multiple orbits, no relating automorphism) → **defer** it:
    set it aside, leave its cell unresolved, move on.
  Continue until no symmetric decision remains anywhere.
- **Phase 2 — rigid enumeration.** What's left is a graph whose
  remaining decisions are all real — a **rigid residue** with its orbit
  structure already computed. Branch over the deferred decisions
  exhaustively, **with no oracle calls** (a real decision stays real;
  §2).

The descent's correctness is unchanged; what changes is the *order* of
resolution and *where* the oracle work lands.

---

## 2. Foundation — real stays real

> **Real-stays-real.** If a pair `{u, v}` in a cell is a *real* decision
> (no path-fixing automorphism swaps `u` and `v`), it remains real under
> any further individualization.

*Why.* Individualizing more vertices grows the path; the stabilizer
shrinks (`Aut_{path'} ⊆ Aut_{path}` for `path' ⊇ path`). A swap absent
from the larger group is absent from the smaller one. So a
non-symmetric pair can never *become* symmetric.

This is **general** — a monotonicity fact about point stabilizers,
independent of warm refinement or fresh-colour individualization (those
are just *how* a point gets fixed; the shrinkage is a property of the
group). Elementary group theory; not yet a named Lean lemma, but a clean
one to state.

**Consequence:** deferring a real decision is always safe. It will still
be real when Phase 2 reaches it, so no symmetry is lost by setting it
aside — only *conditional* symmetry below it is postponed (§5).

---

## 3. The efficiency insight — hoisting symmetry above real branching

This is the point of the restructuring, stated precisely:

> In the current flow, a real decision `R` *above* a symmetric decision
> `S` in the tree forces `S` to be re-discovered in **every branch** of
> `R`. Deferring `R` **hoists `S` above the real branching**, so `S` is
> consumed **once**.

Cost comparison:

| | Oracle calls | Exponential part |
|---|---|---|
| **Current flow** | run at *every node* of the descent tree | oracle work **×** (exponential node count) |
| **Deferred flow** | run *once per decision* on a single deferred path (polynomial, ≤ `O(n²)` pair-decisions) | rigid enumeration with **zero** oracle calls |

The deferred flow moves the oracle work **out of** the exponential. This
is the design's "sum, not product" applied one level up — to *oracle
scheduling* rather than to graph structure or decisions. Each piece of
symmetry is consumed once, before any real branching multiplies the
node count.

The exponential does not disappear — real decisions still branch — but
it is now an **oracle-free enumeration** over a residue whose structure
is fully known, not an exponential tree with oracle calls at every node.

---

## 4. Soundness

The workflow is a pure scheduling change:

1. **Deferring reals is safe** (§2): a deferred decision stays real, so
   no symmetry is dropped by postponing it.
2. **Phase 1 only consumes verified symmetry** — each merge is a
   verified automorphism (the oracles' soundness anchor, unchanged). No
   over-merging.
3. **Phase 2 enumerates a rigid residue** — exhaustive branching over
   real decisions reaches *a* lex-min over a complete leaf set, just
   without redundant oracle calls.

At worst the workflow over-branches (treats conditional symmetry as
real — §5), which is the safe direction. It never produces a wrong
answer and never flags a graph the current flow would canonize.

> **Correction (build, 2026-05-28).** An earlier version of point 3 said
> "reaches the lex-min, **exactly as the current exhaustive descent does**."
> That is **false**: the consumption schedule fixes the leaf labelling (the
> individualisation order determines `P`, hence the refinement numbering at
> each leaf), so reordering decisions changes *which* matrix is the lex-min.
> Deferral produces a **different** canonical form than the lowest-id schedule
> whenever it reorders (measured on Rook3x3; not on Petersen, which never
> reorders). What *is* preserved is what matters for correctness:
> **iso-invariance** (relabellings canonize identically) and **distinguishing**
> (Even≠Odd) — both verified. So deferral is a sound *alternative*
> canonicaliser, not a canonical-preserving speedup.

---

## 5. The crux — conditional vs. unconditional symmetry

The clean two-phase separation (polynomial oracle phase, oracle-free
rigid phase) holds **iff all symmetry is unconditional** — consumable
without committing any real decision.

**The deferral mechanic that creates the subtlety.** Deferring a real
decision `R` means **not writing its `P` entry** — its cell stays
coarse. The spine's order-independence (`warmRefine_agree_off'`) applies
only to *committed* decisions; an uncommitted one **blocks refinement
below it**, so any sub-cells of `R`'s cell stay hidden. Therefore:

- **Unconditional symmetry** — a symmetric decision `S` available
  *without* committing `R` — is hoisted above the real branching and
  consumed once (§3).
- **Conditional symmetry** — a symmetric decision that only *appears*
  after `R` is committed (symmetry relative to a real choice) — stays
  hidden behind `R`. Deferring `R` defers it too; it resurfaces during
  Phase-2 enumeration, where it would need oracle calls again (or cause
  over-branching).

**This is exactly the decomposability hypothesis, operationalized.**
"All symmetry is unconditional" = "after consuming it the residue is
rigid" = the (O\*) self-detection lemma of
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
§8.1. The deferred-decision workflow is the *algorithm*; "residue is
rigid" is its *correctness condition for the clean two-phase form*. If
the hypothesis holds, deferral gives the polynomial oracle phase for
free. If it fails (a hidden Johnson — non-abelian *false* symmetry the
oracles can't catch), that symmetry is never consumed in Phase 1 and
manifests as exponential branching in Phase 2 — caught by the budget as
a flag.

**So deferral does not bypass the wall; it isolates it to Phase 2.**
And even when the hypothesis fails, the *unconditional* symmetry is
still hoisted — the workflow is never worse than the current flow, and
usually better.

---

## 6. Graceful degradation

Because the workflow degrades to the current behaviour exactly where the
hypothesis fails:

- **Cascade class / decomposable graphs** → all symmetry unconditional →
  polynomial Phase 1 + clean rigid hand-off (§7).
- **Hidden Johnson** → non-abelian false symmetry uncatchable by either
  oracle → not consumed in Phase 1 → Phase 2 branching stacks → budget
  flags. Same flag the current flow gives, reached the same way.
- **IR blind spots** (rigid, refinement-resistant —
  [strategy §15 gap 5](./chain-descent-strategy.md)) → genuinely rigid,
  no symmetry to consume → Phase 1 is trivial, Phase 2 is the hard
  exhaustive enumeration. The workflow correctly identifies these as
  *all-residue, no-symmetry* (distinct from hidden Johnson, which has
  uncon­sumed symmetry) — a useful diagnostic.

---

## 7. The rigid-residue hand-off (the architectural payoff)

The most valuable byproduct: after Phase 1, the workflow produces a
clean, first-class intermediate state —

> **the complete rigid residue, with its orbit structure already
> computed**: every remaining decision is known-real, and the orbits
> within each are known.

The current layer-by-layer flow never has this state, because it
interleaves symmetry consumption with real branching and never reaches
"all symmetry consumed, here is the rigid core." The deferred workflow
makes it an explicit artifact, which opens a **much larger slot for a
global rigid solver** — one that sees the whole rigid problem at once
rather than making local, partial-information guesses level by level:

- a **bounded-degree Luks-style** solver (which needs the global
  structure, not a per-node cell);
- a **constraint / SAT-style** enumerator over the rigid residue;
- a **global lex-min search** that exploits the complete orbit-annotated
  structure.

This is the natural home for the "rigid decision solver" slot noted in
the algorithm-flow discussion: the third decision component, sitting in
Phase 2, consuming the residue the two symmetry oracles leave behind.
Its hard cases (IR blind spots) need a paradigm outside
individualization-refinement (e.g. Luks) — but the hand-off gives such a
solver the best-possible interface.

---

## 8. The sharper sub-question

The deferred workflow reframes the open content into a more attackable
form. The polynomial guarantee lives exactly at the
unconditional/conditional line, so the question to settle is:

> **Which symmetry is unconditional (hoistable above real branching),
> and which is conditional on a non-symmetric choice?**

This is sharper than "is there a hidden Johnson," because it asks
specifically *how* an automorphism of `G` can be conditional on a real
decision — i.e., exist only in the stabilizer of one branch of a
non-symmetric split. Characterizing that is a concrete structural
question about the interaction of `Aut(G)` with the descent's cell tree,
and a positive answer (all symmetry unconditional, on some class) gives
the clean two-phase guarantee on that class directly.

A plausible attack: show that on the cascade class, every generator the
oracles would harvest is available from refinement *before* any real
split (because orbit recovery exposes orbits in the partition, which is
order-independent by the spine). That would make all cascade-class
symmetry unconditional and the two-phase form polynomial there.

---

## 9. Implementation sketch (post-cascade-oracle)

This is a harness-scheduling change, layered over the built oracles:

1. **Decision queue.** Replace immediate branching with a worklist of
   open decisions. Pop a decision, classify via the oracle(s).
2. **Consume or defer.** Symmetric → harvest generator into the
   `PermutationGroup`, refine, push newly-exposed decisions. Real →
   push onto a *deferred* list, do **not** branch, do **not** commit its
   `P` entry (keep the cell coarse).
3. **Phase boundary.** When the worklist holds only deferred (real)
   decisions, Phase 1 is done. Emit the rigid residue + orbit
   annotations.
4. **Phase 2.** Hand the residue to the rigid enumerator (initially the
   existing exhaustive branch; later a global solver, §7). No oracle
   calls.

**Reuses, unchanged:** the cascade + linear oracle classification, the
`PermutationGroup` chain and `CoveredByPathFixingAut` pruning, the
verification gate, the budget/flag.

**New:** the worklist scheduling, the deferred list, the Phase-1/Phase-2
boundary detection, and the rigid-residue emission.

**Empirical bar.** On CFI (where all symmetry is abelian/unconditional),
Phase 1 should consume every twist in a single polynomial pass (no
re-consumption across branches), and Phase 2 should be trivial (residue
rigid). Compare oracle-call counts vs. the per-node flow — the win is
oracle calls dropping from ~(node count) to ~(decision count).

---

## 10. Risks and open questions

1. **Conditional symmetry exists (§5).** The clean two-phase form is
   conditional on the decomposability hypothesis. Where it fails, Phase
   2 is not oracle-free. **Sound regardless**; the question is the
   efficiency guarantee. This is the same open content as Tier 3.
2. **Phase-1 termination / completeness.** Need to confirm Phase 1 can
   always reach "only real decisions remain" — i.e., that deferring
   reals never *blocks* consuming an unconditional symmetric decision
   elsewhere. Plausible (you can guess in any other cell), but owed a
   precise argument.
3. **Iso-invariance of the schedule.** The order of consuming symmetric
   decisions must not affect the canonical/flag verdict. The spine gives
   partition order-independence for committed decisions; the deferred
   worklist must be driven by iso-invariant cell ids
   ([strategy §15 gap 2](./chain-descent-strategy.md)), same obligation
   as the oracles.
4. **Rigid-residue solver is unspecified.** §7 names the slot; the
   actual global solver (Luks-style or otherwise) is separate future
   work. The hand-off is the contribution; the solver is not.
5. **The budget is a Phase-2-only mechanism.** Phase 1 is
   *unconditionally polynomial*: both oracles are bounded-work-or-degrade
   (the cascade oracle's single-path recursion is `O(n³)` whether or not
   it certifies; the linear oracle is `O(n²)` per decision), and Phase 1
   makes polynomially many such calls on a single non-branching deferred
   path. So Phase 1 **cannot exhaust the budget** — it always runs to
   completion. The exponential lives entirely in Phase 2's rigid
   enumeration, so the node budget bounds Phase 2 alone, and **every flag
   originates in Phase 2**. (This sharpens the two-phase picture: a
   guaranteed-polynomial symmetry-consumption phase, then a
   budget-bounded enumeration phase — the budget handshake of
   [strategy §15 gap 1](./chain-descent-strategy.md) only has to be
   reasoned about for Phase 2.)

---

## 11. Cross-references

- [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) —
  the true-symmetry classifier this schedules; build this first.
- [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) —
  the abelian-false-symmetry classifier this schedules.
- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §8.1 — the (O\*) / "residue is rigid" hypothesis that the clean
  two-phase form is the operational realization of.
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §6 (budget),
  §9–§12 (the `(A, P)` substrate, spine, partition order-independence),
  §15 (gap 1 budget handshake, gap 2 flag iso-invariance, gap 5 IR blind
  spots).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3
  (the single hurdle / sum-not-product), §8 (the harness this layers
  over).
