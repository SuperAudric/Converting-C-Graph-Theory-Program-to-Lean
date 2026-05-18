# Flip-validation strategy (forward record + backward flip-validation)

A candidate graph canonizer aimed at polynomial worst-case time. The defining
feature is that information **flows between two passes** through a recorded
guess stack, so the backward pass can correct wrong choices made greedily by
the forward pass instead of branching on them.

Built on top of
[`CanonGraphOrdererPartialOrderSinglePair`](../GraphCanonizationProject/CanonGraphOrdererPartialOrderSinglePair.cs)
(which provides the single-pair guess + 1-WL propagation core) and in the
same lineage as the v1
[`supplant-strategy-v1.md`](./supplant-strategy-v1.md) (which also recorded
guesses and reconciled them at the end, via a more complex multi-pass
"supplant" rather than per-guess flip-validation). The pair-event roles and
multi-pass reconciliation of v1 are replaced here by single-pair guesses
plus a single backward sweep.

## Algorithm at a glance

1. **Forward pass.** Greedy: at each step pick one guess (within-cell or
   between-cell, by a deliberately simple lex-min-by-index rule that may
   not currently be iso-invariant on cells hosting multiple pair-orbits — see §3.2
   and §6.5), write it into `P`, propagate, record what was done. Repeat
   until `P` is total. The architectural commitment is that the *forward
   pass need not make iso-invariant pair choices*; correcting wrong
   choices is the backward pass's job.
2. **Backward pass.** Walk the guess stack from deepest to shallowest. For
   each primary guess, decide via a polynomial-time local test whether its
   two endpoints are automorphic given everything decided below it. If yes,
   the guess was an arbitrary tie-break — lock it. If no, flip it,
   re-propagate downward, lex-min, lock the resolved direction.
3. **Pair-orbit recovery (PLANNED, §6.5).** When the wrong-direction flip
   of step 2 doesn't recover the canonical form because the *pair-orbit
   choice itself* was non-canonical (and not just its direction), an
   additional backward-pass mechanism — not yet specified — switches the
   representative within the cell. Without this, the algorithm is **not
   a correct canonizer on graphs with multi-orbit cells**, which
   includes the disjoint-CFI test family.

Each primary guess is touched once per pass. The forward pass is
`O(n³)`-per-step × `O(n)` steps; the backward pass is `O(n²)`-per-test ×
`O(n)` tests, plus a polynomial re-propagation cost on each flip. The total
is polynomial **iff** the invariants in §6 hold and §6.5's mechanism
ships polynomial.

The final bar of correctness is a Lean proof in the
[`GraphCanonizationProofs`](../GraphCanonizationProofs) project, after the
C# implementation has been shown empirically correct on the
isomorphism-stability test bed and on the CFI hard cases — see §8.

---

## 1. State

The **only persistent state** is

```
P : n×n matrix over {Less, Unknown, Greater}
```

held antisymmetric and transitively closed at all times. `P` begins all
`Unknown` apart from order forced by vertex types. The vertex partition into
cells is re-derived from `(A, P)` at every step — never stored.

The algorithm additionally maintains a **transient guess record** consumed
only by the backward pass:

```
guesses : stack of GuessRecord
GuessRecord = {
    kind          : PRIMARY (chosen) | DERIVED (forced by closure)
    a, b          : the two vertices
    direction     : LESS (a<b) or GREATER (a>b)
    driver        : index of the PRIMARY that completed the chain
                    (DERIVED only)
    cell_snapshot : enough of the cell tree at guess time to rerun a
                    local test (see §3.5)
}
```

The guess record is a *transcript of how P was built*; the canonical form
itself depends only on `(A, P_final)`.

---

## 2. The cell tree (mental model)

`P` is a flat matrix but it *induces* a hierarchical tree of nested cells.
This is the user-facing model and the one the backward pass navigates.

- **Tier 0** (root): the whole vertex set.
- **Tier k** cells: the cells of 1-WL on `(A, P_k)`, where `P_k` is the
  partial-order matrix after the first `k` primary guesses have been
  written and propagated.
- **Children of a cell C at tier k**: the sub-cells of C produced by
  refining 1-WL once another primary guess has touched C or its
  P-neighbourhood. A child is born either by a within-cell individualisation
  (one vertex of C is split off as the cell minimum) or by a between-cell
  ordering whose propagation cascaded into C.
- **Leaves**: singleton cells. Every vertex eventually becomes a leaf.

Order between cells is layered:

- **Sibling cells** (same parent) are ordered by either a `PRIMARY`
  between-cell guess or by closure from within-cell guesses elsewhere. If
  neither has touched them, they are *P-incomparable* and the forward pass
  will eventually emit a between-cell guess to resolve them (§4).
- **Cousin cells** (different parents at the same tier) inherit their order
  from their parents' order — uniformly, because the parents are cell-
  respecting in `P`.

**Equivalence with SinglePair's flat `P`.** SinglePair stores `P` flat and
never materialises the tree. The two views are equivalent: the tree at any
moment is exactly the 1-WL partition lattice of `(A, P)` restricted to
cells the algorithm has actually visited. For the flip-validation pass we
need to look at *cell snapshots* (see §3.5), so the tree must be
reconstructable from the guess record; the matrix-only view is not
sufficient for the backward pass on its own.

---

## 3. Operations

### 3.1 Refine (free; reads `P`, never writes it)

1-WL colour refinement on the coloured graph
`(A, edge_label = (adj[u,v], P[u,v]))`. Each vertex's colour is the sorted
multiset of `(neighbour_colour, edge, Prel)` tuples, iterated to fixpoint.
**Split-only**: refinement never orders cells and never writes to `P`. Cells
are numbered in canonical signature order, so any "lex-min cell / pair"
rule below is isomorphism-invariant.

This is the propagation engine. 1-WL is the chosen strength; higher-`k`-WL
is out of scope (each additional `k` adds `n` to the exponent without
improving worst case on the families that defeat 1-WL).

### 3.2 Within-cell primary guess

When some cell `C` has `|C| ≥ 2` and contains an internal `Unknown` pair,
pick the lex-min `a, b ∈ C` (lex-min by vertex index). Write
`P[a,b] = LESS`. Push a `PRIMARY` with `a, b, LESS`.

The lex-min-by-index rule is **deliberately simple and not iso-invariant
on cells that contain multiple pair-orbits** (e.g. C4's vertex-orbit
contains the adjacent and diagonal pair-orbits separately, and the
adjacent-vs-diagonal choice depends on input labelling). This is *not*
patched at the pair-selection step — patching it would push the burden
onto whatever discriminator builds the "canonical pair" rule, and the
whole architectural premise of this design (§6) is that the discriminator
need not be strong enough to identify structure. The intended fix lives
in the backward pass and is described in §6.5 — "every canonical form is
reachable from any pair selection." That mechanism is **planned but not
yet implemented**, so the current code will fail iso-invariance on graphs
whose cells host multiple pair-orbits. The failure is visible in the size
6 corpus and on the disjoint-CFI tests; see §9 / §11.

### 3.3 Between-cell primary guess (sibling-ordering)

When `P` is not total but every cell is internally resolved (no within-cell
`Unknown` left), pick the lex-min P-incomparable cell pair `(X, Y)` (lex-min
by canonical cell id). Write `P[x,y] = LESS` for **one** representative
pair `x ∈ X, y ∈ Y` (lex-min by vertex index). Push a `PRIMARY` with
`x, y, LESS`.

Same caveat as §3.2: representative selection by vertex index isn't iso-
invariant when `X` and `Y` host non-singleton cross-orbit structure. The
§6.5 mechanism is the intended fix.

Closure (§3.4) will not promote this to "all of X below all of Y" — that is
the block guess of `PartialOrderIR` and would discard interleavings. Here
the relation is between a single pair; if every `(x', y')` with `x' ∈ X,
y' ∈ Y` should eventually be `LESS`, that is the forward pass's job, one
guess at a time. This is what gives the algorithm freedom to reach
interleaved canonical orders (§7) and is a precondition for §6.5.

### 3.4 Derived guess (transitive closure)

After every write to `P`, run a Floyd-Warshall closure. For each `(i, k, j)`
with `P[i,k] = LESS`, `P[k,j] = LESS`, and `P[i,j] = UNKNOWN`: set
`P[i,j] = LESS` and push a `DERIVED` record with `driver` = the most-recent
`PRIMARY` whose write completed the chain (formally: the unique `PRIMARY`
whose insertion of an edge took the `(i, j)`-reachability count from zero
to positive in this round; ties broken by primary index — see §11.3 for the
specification corner). Contradiction (a cycle or `P[v,v] = LESS`) marks the
current branch dead.

DERIVED records exist only so the backward pass can unwind a chain when
its driving primary flips (§5). At most `n(n−1)` exist at any time.

### 3.5 Cell snapshot

Captured per primary at guess time, sufficient to re-run the local orbit
test (§3.6) without recomputing the world. Minimally:

- The cell `C` being split (just its member list).
- For each `c ∈ C`, the cell id `c` was in at the parent tier.
- The mapping of `C`'s sub-cells (after this guess and its closure) to
  members.

Storage is `O(n)` per guess, `O(n²)` total.

### 3.6 Local orbit test

Given a primary guess `g = (a, b, direction)` that, at guess time, split a
cell `C` into sub-cells `A ∋ a` and `B ∋ b` (plus, optionally, untouched
siblings `R`):

> Is the pairing of `A` to `B` induced by deeper guesses an automorphism of
> the full graph that fixes everything outside `C`?

The pairing is computed by walking the cell tree below `g`: every leaf of
`A`'s sub-tree was individualised by some chain of deeper primaries; the
isomorphic chain inside `B`'s sub-tree (same guess kinds in the same
relative positions) names that leaf's partner. If `|A| ≠ |B|`, no pairing
exists and the test trivially fails.

If a pairing exists, build the permutation σ that swaps each `(a_i, b_i)`
pair and is the identity outside `C`, then verify `σ · A · σᵀ = A` and that
every locked `P` relation outside `C` is σ-stable. `O(n²)` total. The test
is *sound* (a passing σ really is an automorphism); it is sound-but-
incomplete (a "no" can miss orbit-equivalence realised by a non-
transposition automorphism). Incompleteness only triggers a lex-min
recompute that yields the same canonical form either way, so it does not
break correctness.

**Transposition pre-check.** Before constructing the pairing, test whether
the bare transposition `(a b)` is an automorphism of `(A, P_at_g)`. If so,
lock `g` immediately without building the pairing. This is a polynomial
fast path that handles the common case where the guess split a true two-
element orbit.

**Practical note: the transposition pre-check is the whole test for this
algorithm.** Both within-cell and between-cell primary guesses write a
single `P` entry involving the chosen pair, and refinement uses that
unique entry to individualise both vertices into their own sub-cells. So
`A` and `B` are always singletons `{a}` and `{b}`, the sub-tree pairing
collapses to `(a, b)`, and the σ of the general test is exactly the
transposition `(a b)`. The general sub-tree-pairing description is kept
above so the algorithm extends cleanly to future variants that produce
non-singleton sub-cells (e.g. block guesses for performance), but the
first implementation only needs the transposition test.

---

## 4. Forward pass

```
refine to fixpoint
loop:
    if P is total: break                       # leaf reached
    if some cell C has internal Unknown pair:  # within-cell
        pick lex-min (a, b) in lex-min such C
        push PRIMARY(a, b, LESS)
        P[a,b] := LESS;  P[b,a] := GREATER
    else:                                      # between-cell
        pick lex-min P-incomparable cell pair (X, Y)
        pick lex-min (x, y) with x in X, y in Y
        push PRIMARY(x, y, LESS)
        P[x,y] := LESS;  P[y,x] := GREATER
    transitive-close P (pushing DERIVED records)
    refine to fixpoint
```

**Termination.** Every guess strictly grows the resolved set of `P`, bounded
by `n(n−1)/2`. Singleton cells are reached in `O(n)` within-cell guesses;
final cross-cell ordering takes `O(n)` more between-cell guesses; total
primary count is `O(n)`. (The naïve worst case is `O(n²)` primaries — every
cell-pair distinct — but closure collapses most pairs into chains as the
total order grows.)

**Cell tree extension.** Each guess extends the cell tree: a within-cell
guess adds a single child split of its cell; a between-cell guess adds an
ordering edge between two existing siblings (no new cell).

---

## 5. Backward pass

```
for i = len(guesses) − 1 down to 0:
    g := guesses[i]
    if g.kind == DERIVED: continue              # rides with its driver

    if transposition_test(g.a, g.b, P_at(i)):   # fast path
        g.locked := VALID
        continue
    if local_orbit_test(g):
        g.locked := VALID
        continue

    # Wrong-direction candidate. Re-propagate from position i with the
    # other direction, take lex-min of the two resulting canonical forms.
    re-propagate from i with direction reversed
    if lex(M_reverse) < lex(M_current):
        rewrite g and its DERIVED descendants
        adopt M_reverse
    g.locked := RESOLVED
```

The re-propagation rewrites everything from position `i` onward: the
deeper primaries themselves stay in place (their `(a, b)` pairs are still
in the same cells by invariant 6.2), but their `DERIVED` descendants are
recomputed from scratch under the flipped direction. By invariant 6.3 no
deeper primary's `VALID` lock is invalidated, so the work is bounded.

---

## 6. Invariants

The algorithm is **correct** iff (6.1) plus (6.4) plus the planned (6.5)
all hold. It is **polynomial** iff (6.2) and (6.3) additionally hold.

The architectural commitment driving this whole section is that **the
discriminator (1-WL) does not need to identify structure completely.**
That would itself require a canonizer. Instead, when 1-WL is insufficient
to single out an iso-invariant choice, the algorithm makes a non-iso-
invariant guess and *the backward pass + flipping* is what restores iso-
invariance of the final output. The "one guess collapses one symmetry
(true or apparent)" framing in §2 is the tiered-groups expression of
this: each guess is a single symmetry-collapse step; the backward sweep
sorts out which collapses were structural vs. arbitrary.

### 6.1 Iso-invariance of cell ids (correctness building block)

Canonical cell ids (from canonical 1-WL signature order) are functions of
`(A, P)` only, so the *set of candidate cells* and the *set of candidate
cell pairs* at any node are iso-invariant. That is what `PartialOrderIR`
and `SinglePair` rely on for their iso-invariance argument.

**What this does *not* give us, and what the prior version of this doc
silently assumed.** Picking the lex-min representative *within* a cell by
vertex index is iso-invariant **only when the cell is a single pair-
orbit**. A 1-WL cell can host multiple pair-orbits (C4: adjacent vs.
diagonal pairs; C6: distance-1 / 2 / 3 pairs; CFI on Cycle4/K4: many more
subtle orbit splits that 1-WL on pairs cannot separate). When that
happens, lex-min by index can land in different pair-orbits across input
scramblings, and the resulting canonical form differs across scramblings
unless (6.5) compensates.

So 6.1 alone is **not sufficient for correctness** on graphs with multi-
orbit cells. The correctness chain needs (6.4) for closure consistency
and (6.5) for the pair-orbit recovery.

### 6.2 Weakened symmetry of propagation (polynomial)

> For every pair `(v, w)`, `v` and `w` are in the same cell after
> propagating `a<b` iff they are in the same cell after propagating `b<a`.

The *partition coarseness* is direction-independent; only labels and the
roles of `a, b` swap. This is what allows a backward flip to reuse the
deeper cell structure verbatim instead of re-discovering it.

**Why it holds for 1-WL.** The equivalence relation 1-WL computes is the
coarsest equitable refinement of the initial colouring. Swapping a single
`Less` for a single `Greater` is a relabelling of signature *symbols*, not
a change in their structural information content. Empirically verified on
`C4` with `(0 1)` non-Aut, on the 6-vertex asymmetric graph
`{0-1, 0-2, 0-3, 1-4, 2-5}` with `(1 2)` non-Aut, and on `K3`. No
counterexample is known.

**Why it holds across closure.** Within a cell, all vertices have identical
Prel profiles, so closure derives *the same* new relations for every cell-
mate (everyone in the cell gains a `Less` to some target, or no one does).
The within-cell symmetry is preserved by closure when it was preserved
before. Closure-derived asymmetries only affect vertices that were
*already* distinguished, and partition coarseness survives.

**Status.** Empirical on small cases; not formally proven. CFI is the
sharpest test (§8).

### 6.3 Deeper-guess locks survive shallow flips (polynomial)

> A `VALID` lock on a deeper primary remains correct after flipping a
> shallower primary, provided weakened symmetry holds.

By 6.2 the cell snapshot of the deeper guess is the same set of vertices
in both shallow directions; the local orbit test reads (cell members, A
restricted to them, P restricted to them) which all transport unchanged.

**Status.** The single most fragile claim and the load-bearing one for the
polynomial bound. The diagnostic in §9 detects a violation directly.

**Alternative if 6.3 fails.** Per shallow flip, detect *which* deeper
locks the flip actually affects rather than re-running every deeper local
orbit test in full. The cell snapshot (§3.5) records which entries of `P`
each deeper test consumed; if the shallow flip touches none of them, that
deeper lock is preserved. Re-test only the affected locks. Cost: `O(n)`
deeper locks × `O(n²)` per re-test = `O(n³)` extra per shallow flip,
`O(n⁴)` total — the polynomial bound survives a 6.3 failure as long as
the affected-set detection is itself polynomial, which it is (a snapshot-
versus-flip comparison is `O(n²)` per snapshot).

### 6.4 Closure as guess (correctness + polynomial)

Without explicit tracking, transitive closure can produce a chain of
length `O(n)` whose every relation traces back to a single primary; if
that primary later flips, naïvely unrolling the chain is `O(n!)` in the
limit. To bound this:

- Every closure-written relation becomes a `DERIVED` record with a
  `driver` pointer.
- The backward pass skips `DERIVED` records; they ride with their driver.
  A primary flip re-runs closure from scratch under the new direction —
  the new chain replaces the old one.
- At most `n(n−1)` `DERIVED` records exist at any time, so bookkeeping is
  polynomial.

**Why closure asymmetry between non-automorphic pairs is not a problem.**
A non-automorphic pair `(u, v)` is in different cells by definition. Once
they are in different cells, every locked direction between them is
*forced* by structure rather than chosen — flipping the primary that put
them on opposite sides of a split derives the *opposite* forced direction,
not an inconsistency. Closure asymmetries are confined to pairs whose
ordering descends from a primary guess; flipping the primary flips the
chain.

### 6.5 Every canonical form reachable from any pair selection (PLANNED, correctness)

> For any input scrambling and any starting pair the forward pass might
> commit to, the algorithm's exploration reaches every canonical form
> that any other starting pair could reach.

This is the load-bearing correctness invariant under the architectural
commitment in the header of §6 — it is what makes 1-WL's *failure to
identify pair orbits* survivable. If two scramblings commit to pairs
from different pair-orbits, both runs must end up considering the same
set of candidate canonical forms; the lex-min then resolves them to a
common output.

**This is planned but not implemented.** The direction-flip mechanism
already in the backward pass (§5) is the right shape for it but is
restricted to flipping a single guess's *direction*, not its *pair-
orbit choice*. The next planning iteration (separate document) will
specify the actual mechanism — candidates we have discussed include
branching over pair-orbits with work-sharing between branches, a richer
backward-pass "swap representative" step, and explicit propagation
discipline that makes the < and > branches share enough state to make
the search polynomial.

**Until 6.5 is in, the implementation is not a correct canonizer on
graphs that contain multi-orbit cells.** The size 4–6 corpus contains
such graphs (C4 + K2 at size 6 #56 is the smallest example); the
disjoint-CFI tests on Cycle4 and K4 are the larger and more important
ones. The failure is intentional in the current code — it is the
diagnostic that 6.5 needs to fix, not a bug to be patched at the pair-
selection step.

---

## 7. Why single-pair `a<b` does not prune interleavings

This was a stated worry: if vertices `A, B, C` are non-automorphic and the
forward pass commits to `A < B`, can it still reach the canonical order
`A < C < B`?

**Yes.** A single-pair guess `A < B` writes one cell of `P` and *only* that
one cell — it constrains `A`'s position relative to `B` only. `C` is
unaffected by this write. The total orders consistent with `A < B` include
`A < B < C`, `A < C < B`, *and* `C < A < B`. The forward pass continues to
make further guesses (within-cell or between-cell, §3.2 / §3.3); whichever
of these total orders the propagation settles on is what gets recorded.

The contrast is with **block guesses** in `PartialOrderIR`, which write the
entire block "every member of A's lineage below every member of B's
lineage" in one step. That *does* eliminate interleavings like `A < C < B`.
The single-pair design here was kept exactly to avoid that — see the
[`CanonGraphOrdererPartialOrderSinglePair`](../GraphCanonizationProject/CanonGraphOrdererPartialOrderSinglePair.cs)
header note for the original motivation.

**What does change with the choice of guess pair** is the *order in which
sub-orbits get resolved*, not the *set of total orders reachable*. The
forward pass picks one specific path through the search tree; the backward
pass corrects wrong-direction commitments. Picking `(A, B)` vs `(A, C)` as
the first guess can change which canonical form is reached (because the
greedy ordering of subsequent guesses differs), but the result is still an
iso-invariant complete canonical form for any deterministic choice rule.
It need not be the global lex-min over all permutations — and that's fine,
because any iso-invariant complete canonical form is valid by definition.

---

## 8. Path to proof

This algorithm is a candidate polynomial-time graph canonizer. GI ∈ P is
an open problem, so the bar for accepting the polynomial claim is high.
The intended path:

1. **Empirical C# implementation.** Build the algorithm on top of
   `CanonGraphOrdererPartialOrderSinglePair`. Validate against the
   existing `KnownGraphs` size 4–7 corpus for iso-invariance and
   completeness (matches the size-4 `TwoDisjointPair` and the size-7
   1044-graph tests already exercised against `PartialOrderIR`).
2. **CFI / Miyazaki stress.** Run on the hard 1-WL-resistant families
   (§9). The diagnostic counters in §9 — especially the
   *locked-then-invalidated* counter — will either show the polynomial
   structure holding or pinpoint the specific invariant that breaks.
3. **Lean formalisation.** Once the C# version is empirically correct on
   the test bed *and* on CFI, port to the
   [`GraphCanonizationProofs`](../GraphCanonizationProofs) Lean project
   alongside `LeanGraphCanonizerV4` and prove (a) correctness (6.1 + 6.4)
   and (b) the polynomial bound (6.2 + 6.3). The proof is the final bar.

The complexity arithmetic, if 6.1–6.4 all hold:

- Forward pass: `O(n)` primaries × `O(n³)` per propagation = `O(n⁴)`.
- Backward pass: `O(n)` primaries × `O(n²)` per local orbit test +
  `O(n⁴)` worst-case re-propagation per flip = `O(n⁵)`.
- DERIVED records: `O(n²)` rewrite cost amortised over the backward
  pass.

Total `O(n⁵)`.

---

## 9. Validation strategy (empirical bar)

Run on:

- **The existing `KnownGraphs` corpus** at sizes 4–7 for regression: every
  graph must scramble-invariantly produce one canonical form, and the
  number of distinct canonical forms must equal the number of distinct
  graphs.
- **CFI(K_m)** for `m = 3, 4, 5, 6`, using
  [`CfiGraphGenerator`](../GraphCanonizationProject/CfiGraphGenerator.cs).
- **Miyazaki graphs** at growing sizes (generator to be added).

Diagnostic counters per run:

| Metric | What a failure looks like |
|---|---|
| Primary guess count | Super-linear in `n` ⇒ forward pass leaks |
| `DERIVED` count | Super-quadratic in `n` ⇒ closure-as-guess leaks |
| Backward-pass flips | Should be `O(n)` |
| **Locked-then-invalidated guesses** | **Any non-zero count falsifies 6.3** |
| Wall-clock scaling | Super-polynomial trend on CFI/Miyazaki |
| Canonical-form stability across scramblings | Disagreement falsifies 6.1 |

The locked-then-invalidated counter is the single most diagnostic. A
deeper primary that was marked `VALID` and later turns out to have been
wrong-direction is direct evidence that flipping a shallower guess
changed the deeper structure — i.e. the deeper-lock-survival invariant
(6.3) failed and the polynomial bound has collapsed.

---

## 10. Implementation notes

Build on `CanonGraphOrdererPartialOrderSinglePair`:

- **Reuse:** `Refine`, `TransitiveClose`, `SeedFromTypes`, `IsTotal`,
  `ReadPermutation`, and the basic guess plumbing.
- **Replace:** `Search` (exhaustive recursion) with `ForwardPass` (greedy
  stack build) followed by `BackwardPass` (single sweep).
- **Add:**
  - `GuessRecord` with `PRIMARY` / `DERIVED` distinction and `driver`
    pointer.
  - `cell_snapshot` capture inside the guess step.
  - Between-cell primary guess branch in the forward pass (the only place
    where the algorithm needs cross-cell guesses; SinglePair handles this
    implicitly via recursion).
  - `TranspositionTest(a, b, P)` — fast pre-check.
  - `LocalOrbitTest(g)` — pairing-via-sub-tree + permutation check.
  - Diagnostic counters from §9 exposed for tests.

**Useful intermediate milestone.** Implement only the forward pass + final
read-off, no backward pass. This is already a complete canonizer if 6.1
plus 6.2 are enough — i.e. the "trust the first direction" version. Run it
against the size-4/5/6/7 known-graphs corpus and compare to
`PartialOrderIR`. If outputs are stable across scramblings and distinct
across non-isomorphic graphs, the backward pass is purely about correcting
wrong choices and the polynomial-time claim narrows to "are wrong choices
rare enough that the backward pass stays linear."

Test scaffolding analogous to
[`GraphCanonTests.PartialOrderIR.cs`](../GraphCanonizationProject.Tests/GraphCanonTests.PartialOrderIR.cs)
should be added with the diagnostic counters exposed.

---

## 11. Open questions and gaps

These need either a definitive specification or empirical resolution
before the polynomial claim can be staked. None of them currently block
an initial implementation — they are either resolved by a placeholder
rule and an empirical check (5, 8, 9), or only matter on falsification
paths the algorithm need not handle in its first version (3, 4, 6, 7).

1. **Prove 6.2 across closure.** Empirically holds; needs a written
   proof for the Lean formalisation.
2. **Prove 6.3.** The load-bearing claim. Even if 6.2 holds, deeper-lock
   survival is a separate fact.
3. **DERIVED driver assignment.** "The unique PRIMARY whose insertion
   took the `(i, j)`-reachability count from zero to positive in this
   closure round" is well-defined when one primary edge per round
   completes the chain, but a single closure pass can complete several
   `(i, j)` paths simultaneously through the same primary. Tie-breaking
   by primary index is iso-invariant but the *correctness* of "ride with
   the driver" depends on every contributing primary giving the same
   verdict; this needs a precise statement.
4. **Both directions dead.** If both forward directions of a primary
   contradict on closure, neither branch produces a canonical form. The
   algorithm needs a defined error mode and, ideally, a structural
   argument that this can never happen on connected graphs.
5. **Between-cell and within-cell representative selection.** "Lex-min
   by vertex index" is not iso-invariant when the cell hosts multiple
   pair-orbits. Patching it at the selection step (e.g. by adding a
   pair signature) would deepen reliance on 1-WL's identifying power,
   which is precisely what the architecture rejects. The real fix lives
   in §6.5 and is planned, not implemented.
6. **Cell snapshot completeness.** The cell snapshot stored per
   guess must contain enough to re-run the local orbit test after deeper
   flips. The minimal sufficient information is given in §3.5 but the
   exact requirement should be re-derived from the local-orbit-test
   pseudocode once implemented.
7. **Local-orbit-test sub-tree pairing well-definedness (deferred).**
   Dissolves for the algorithm as specified: every primary guess
   individualises its endpoints into singleton sub-cells, so the local
   orbit test is exactly the transposition test (§3.6, practical note).
   The sub-tree-pairing concern only resurfaces if a future variant
   introduces block guesses or some other mechanism that produces
   non-singleton `A` or `B`; pin the rule down then.
8. **The between-cell guess is needed.** Originally listed as "verify
   whether within-cell alone suffices," but the 2K2 trace settles it:
   after `0<1` within `{0,1,2,3}`, refinement gives cells
   `{0},{1},{2,3}`, and a second within-cell guess on `{2,3}` leaves
   `{0,1}` vs `{2,3}` P-incomparable. So between-cell guesses really
   are required in the forward pass for any graph with multiple
   automorphism-equivalent components. Specified in §3.3; the open
   sub-question is the iso-invariance of the representative-pick rule
   (item 5).
9. **Lex-min-by-index iso-invariance argument was wrong as stated.**
   The earlier note here said "two 1-WL-equivalent vertices are in the
   same cell, so lex-min by index picks an automorphism-equivalent
   representative." That step is only valid for the *vertex* orbit,
   not the *pair* orbit. A 1-WL cell is one vertex-orbit but can be
   several pair-orbits. Subsumed by item 5 and §6.5.
