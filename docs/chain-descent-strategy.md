# Flip-validation strategy — superseded (earlier generation of chain descent)

A candidate graph canonizer aimed at polynomial worst-case time. The defining
feature is that information **flows between two passes** through a recorded
guess stack, so the backward pass can correct wrong choices made greedily by
the forward pass instead of branching on them.

> **Superseded (chain-descent rewrite) — read before the rest of this doc.**
> This is the *earlier generation* of the design: the two-pass "flip-validation"
> strategy (a greedy forward record plus a backward correction sweep). The
> current design is a single recursion — **chain descent**. The authoritative
> spec is [`chain-descent-simplified-overview.md`](./chain-descent-simplified-overview.md); the
> implemented code is the chain-descent harness (`ChainDescent.cs`,
> `CanonGraphOrdererChainDescent.cs`, …). The two-pass machinery below — the
> forward/backward passes (§4–§5), the §6.5 rotation mechanism, the §8
> complexity arithmetic, the §10 implementation notes — is **not** what was
> built; read it as historical.
>
> This doc is retained for two things the overview relies on but does not
> re-derive: **invariant 6.2** (warm refinement is direction-symmetric on the
> partition) — the load-bearing dependency of the linear oracle,
> [`chain-descent-simplified-overview.md`](./chain-descent-simplified-overview.md) §7 — and the
> lineage and rationale of the single-pair, 1-WL-only design choices.

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
   between-cell, by a deliberately simple lex-min-by-index rule that is
   not iso-invariant on cells hosting multiple pair-orbits — see §3.2
   and §6.5), write it into `P`, propagate, record what was done. Repeat
   until `P` is total. The architectural commitment is that the *forward
   pass need not make iso-invariant pair choices*; correcting wrong
   choices is the backward pass's job.
2. **Backward pass — direction and pair rotation.** Walk the guess stack
   from deepest to shallowest. For each primary, enumerate branches over
   `{direction × first-vertex-rotation × second-vertex-rotation}` from
   the cell snapshot taken at guess time (§3.5), replay each branch,
   lex-min over the resulting canonicals, adopt the winner. Direction
   rotation handles "wrong-way guess on a true symmetry"; vertex
   rotation handles "guessed pair was in a different pair-orbit than the
   canonical one." See §6.5 for the mechanism in detail.
3. **Pair-orbit recovery (§6.5).** When the wrong-direction flip alone
   doesn't recover the canonical because the *pair-orbit choice itself*
   was non-canonical (not just its direction), the backward pass also
   enumerates alternative within-cell representatives `(a', b')`,
   lex-mins across the resulting canonicals, and adopts the winner.
   This is what makes 1-WL's failure to separate pair-orbits survivable.

Each primary guess is touched once per pass (modulo §6.5's rotation
factor). The forward pass is `O(n³)`-per-step × `O(n)` steps; the
backward pass is `O(n²)`-per-test × `O(n)` tests, plus §6.5's pair
rotation. The naive first-cut total is `O(n⁸)`; the planned dependency
calculator (§11.10) brings it down by sharing state across branches.

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
contains the adjacent and diagonal pair-orbits separately). Patching it
at the pair-selection step would push the burden onto a stronger
discriminator, which the architectural premise of this design (§6)
rejects. The fix lives in the backward pass — see §6.5 — which enumerates
alternative representatives within the cell snapshot and lex-mins across
the resulting canonicals. The forward pass therefore commits to the
lex-min-by-index pair as an arbitrary starting choice that §6.5
rotates away.

### 3.3 Between-cell primary guess (sibling-ordering)

When `P` is not total but every cell is internally resolved (no within-cell
`Unknown` left), pick the lex-min P-incomparable cell pair `(X, Y)` (lex-min
by canonical cell id). Write `P[x,y] = LESS` for **one** representative
pair `x ∈ X, y ∈ Y` (lex-min by vertex index). Push a `PRIMARY` with
`x, y, LESS`.

Same caveat as §3.2: representative selection by vertex index isn't iso-
invariant when `X` and `Y` host non-singleton cross-orbit structure.
§6.5's pair rotation enumerates `(x', y')` alternatives within
`(X-at-guess-time, Y-at-guess-time)` and lex-mins.

Closure (§3.4) will not promote this to "all of X below all of Y" — that is
the block guess of `PartialOrderIR` and would discard interleavings. Here
the relation is between a single pair; if every `(x', y')` with `x' ∈ X,
y' ∈ Y` should eventually be `LESS`, that is the forward pass's job, one
guess at a time. This is what gives the algorithm freedom to reach
interleaved canonical orders (§7) and is a precondition for §6.5.

### 3.4 Derived guess (transitive closure)

After every write to `P`, transitively close. For each `(i, k, j)`
with `P[i,k] = LESS`, `P[k,j] = LESS`, and `P[i,j] = UNKNOWN`: set
`P[i,j] = LESS` and push a `DERIVED` record with `driver` = the most-recent
`PRIMARY` whose write completed the chain (formally: the unique `PRIMARY`
whose insertion of an edge took the `(i, j)`-reachability count from zero
to positive in this round; ties broken by primary index — see §11.3 for the
specification corner). Contradiction (a cycle or `P[v,v] = LESS`) marks the
current branch dead.

The closure algorithm itself doesn't matter to the spec — only the final
closed `P`. The v1 implementation uses incremental closure: after a single
new LESS edge `x → y`, only the cross-product `ancestors(x) × descendants(y)`
needs to be processed (`O(n²)` per insertion), vs Floyd-Warshall's
`O(n³)`. Both produce the same closed relation.

DERIVED records exist only so the backward pass can unwind a chain when
its driving primary flips (§5). At most `n(n−1)` exist at any time.

### 3.5 Cell snapshot

Captured per primary at guess time, sufficient both to re-run the local
orbit test (§3.6) and to drive §6.5's pair rotation without recomputing
the world. A **cell-tree fragment** containing:

- `C_a`: the cell containing `a` at guess time (full member list).
- `C_b`: the cell containing `b` at guess time (member list;
  `C_a = C_b` for within-cell guesses, distinct for between-cell).
- For each `c ∈ C_a ∪ C_b`, the cell id `c` had at the parent tier.
- The mapping of `C_a`'s and `C_b`'s sub-cells (after this guess and its
  closure) to members.

Storage is `O(n)` per guess, `O(n²)` total. The richer scope (beyond the
"members only" form needed for §3.6's transposition test) is what §6.5
rotates over and what the §6.3 snapshot-diff alternative compares
against.

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

    # Enumerate branches over {direction × a' ∈ C_a × b' ∈ C_b}
    # using the cell-tree fragment captured at guess time (§3.5).
    best := current canonical
    for (dir, a', b') in branches(g):
        if a' == b': continue
        if (a', b', dir) == (g.a, g.b, g.direction): continue   # baseline
        re-propagate from i with primary i replaced by (a', b', dir)
        if lex(M_branch) < lex(best):
            best := M_branch
            winner := (dir, a', b')
    if winner exists:
        rewrite g (and its DERIVED descendants); adopt best
    g.locked := RESOLVED
```

Direction rotation handles "guess made the wrong way on a true symmetry"
(the transposition test's case from §3.6, which could be re-introduced
as a fast path to skip both direction branches when σ = (a b) is an
automorphism — omitted in v1 for code uniformity); vertex rotation
handles "guessed pair was in a different pair-orbit than the canonical
one" (§6.5). By invariant 6.2 the deeper cells survive a branch swap;
by 6.3 (or its snapshot-diff alternative) deeper `VALID` locks are
preserved or selectively re-tested.

---

## 6. Invariants

The algorithm is **correct** iff (6.1), (6.4), and (6.5) all hold. It
is **polynomial** iff (6.2) and (6.3) additionally hold; the first-cut
implementation of (6.5) is `O(n⁸)` (still polynomial), and §11.10's
planned dependency calculator brings it down further.

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

**This is specifically a claim about the warm refinement actually used
by the implementation** — see the "warm vs fresh" note below. Fresh 1-WL
on the post-guess matrix can produce different partitions under the two
directions; warm refinement (started from the pre-guess steady-state
colouring) cannot.

**Why warm refinement preserves it.** Warm refinement is split-only: it
can only further partition the cells of its starting colouring, never
merge them. That much is proven (`warmRefine_refines` in
`ChainDescent.lean`).

> ⚠️ **Correction (2026-05-21).** The argument originally continued: "the
> splits induced by a single guess + TC are uniform within each cell —
> every member of a cell gains the *same* new `Less`/`Greater` entries,
> so cells stay intact or split identically". The first half is **false**.
> Cell-coherence is a *multiset* property — cell-mates relate identically
> to every *cell* — but a guess `(a, b)` acts on individual *vertices*,
> and TC chains run through individual vertices. Two cell-mates can relate
> symmetrically to `a`'s cell yet asymmetrically to `a` itself, so the
> `a → b` edge reaches one and not the other: **a cell genuinely splits**.
> This is machine-checked by `cell_split_uniform_false` in
> `ChainDescent.lean`. The honest claim is only the *second* half — a cell
> splits **into the same sub-cells under either direction**, order labels
> aside — and proving *that* is the open content of 6.2 (see Status).

**Why it would fail for fresh 1-WL on between-cell guesses.** Fresh
1-WL re-runs colour refinement from a trivial initial colouring on the
post-guess matrix, which can produce a *coarser* partition than warm
refinement when asymmetric TC chains in one direction add entries that
distinguish vertices that the other direction's lack-of-entries leaves
indistinguishable.

Minimal counterexample (fresh 1-WL only): 3 vertices `{0, 1, 2}`, no
edges, `P_pre(2, 0) = <`. Steady state: `{0}, {1}, {2}` (all singletons).
Apply between-cell guess `(0, 1, <)`: TC chains `2 → 0 → 1`, adding
`P(2, 1) = <`, giving total order. Fresh 1-WL: `{0}, {1}, {2}`. Apply
`(0, 1, >)`: no TC chain. Fresh 1-WL of the resulting P sees `1` and
`2` with identical signatures and merges them into `{1, 2}`. Partitions
differ.

Warm refinement starting from `{0}, {1}, {2}` cannot merge `1` and `2`
in either direction, so the discrepancy disappears: both runs end at
`{0}, {1}, {2}`.

**Why it holds across closure.** Within a cell, all vertices have identical
Prel profiles *as multisets over cells* — but, per the correction above,
**not** identical relations to the individual guessed vertices `a, b`. So
closure does **not** derive the same new relations for every cell-mate; a
cell-mate with a chain into `a` is pulled out of its cell. The surviving
statement is the direction-symmetric one: whatever split closure induces,
it induces the *same* split (sub-cells, not labels) under `a<b` and `b<a`.
The unconditional σ-relabel shortcut for this — `transitiveClose` commutes
with the `less ↔ greater` swap — is itself **false** (`closeStep`'s
`less`-first tie-break is not σ-symmetric; machine-checked by
`transitiveClose_swap_false`), so the closure case needs the direct
argument, not a relabel.

**Strong version (vertex-by-vertex label coincidence) does not follow.**
Even under warm refinement, the actual colour *values* `χ^<(v)` and
`χ^>(v)` differ — the signatures include the direction-dependent
`Less`/`Greater` label of the `(a, b)` entry. A "label coincidence"
version, `χ^<(v) = χ^>(σ_ab(v))` for some explicit `σ_ab`, would
require `σ_ab` to be a true automorphism of `(A, P_pre)` — i.e., `(a, b)`
to be a transposition-orbit pair, which is exactly the §3.6
transposition-test case. The weak (partition) version is the most that
holds for arbitrary `(a, b)`, and is sufficient for §6.3's deeper-lock
survival argument.

**Status — `warm_6_2` is proved (2026-05-21).** Lean development in
[`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean).

The proof uses the model settled in design discussion:

- **Transitive closure relegated.** A guess writes a single `P` entry; an
  inconsistent partial order is handled as a *lex-min ranking* criterion,
  not a propagation step (equivalent in practice — a non-lex-min branch is
  never chosen, so being-ranked-worse ≡ being-pruned). So no `transitiveClose`
  sits in the refinement loop, and `P⁻`/`P⁺` differ at only the `(a,b)`/`(b,a)`
  entries. *This makes 6.2 provable:* off `{a,b}` no refinement signature can
  even see the guess.
- **Individualisation = fresh colour.** The guessed pair starts as singletons
  — the "`A`, `B` are always singletons" property §3 already relies on, now
  true by construction.

Lean results:
- `warm_6_2` (the §6.2 partition claim) — **proved**. `P⁻` and `P⁺` differ
  only inside `{a,b}`; off-pair vertices refine identically across the two
  directions; `a, b` stay singletons throughout, so they never satisfy a
  partition-equality test. Induction on the refinement round.
- `warmRefine_refines` (warm refinement is split-only) — **proved**;
  supplies the singleton-preservation lemma.
- `transitiveClose_swap` (σ-relabel commutes with TC) — **disproved**
  (`transitiveClose_swap_false`, witness `conflictMatrix`). Moot under TC
  relegation; kept as a record — the σ-relabel route to 6.2 was not taken.
- `cell_split_uniform` (cell-mates keep equal post-guess signatures) —
  **disproved** (`cell_split_uniform_false`, witness `witnessP0`); the
  abandoned *no-split* route.

Empirically verified on `C4` with `(0 1)` non-Aut, on the 6-vertex
asymmetric graph `{0-1, 0-2, 0-3, 1-4, 2-5}` with `(1 2)` non-Aut, and
on `K3`. The fresh-1-WL counterexample above does not arise under the
warm-refinement implementation. CFI is still the sharpest empirical
test (§8) but is currently impractical at the §6.5 implementation's
`O(n⁸)` per-sweep bound; see §11.10.

### 6.3 Deeper-guess locks survive shallow flips (polynomial)

> A `VALID` lock on a deeper primary remains correct after flipping a
> shallower primary, provided weakened symmetry holds.

By 6.2 the cell snapshot of the deeper guess is the same set of vertices
in both shallow directions; the local orbit test reads (cell members, A
restricted to them, P restricted to them) which all transport unchanged.

**Status.** The single most fragile claim and the load-bearing one for the
polynomial bound. The diagnostic in §9 detects a violation directly.

**Alternative if 6.3 fails.** Per shallow flip *or §6.5 rotation*,
detect *which* deeper locks the change actually affects rather than
re-running every deeper local orbit test in full. The cell snapshot
(§3.5) records which entries of `P` each deeper test consumed; if the
shallow change touches none of them, that deeper lock is preserved.
Re-test only the affected locks. Cost: `O(n)` deeper locks × `O(n²)`
per re-test = `O(n³)` extra per shallow change, `O(n⁴)` total — the
polynomial bound survives a 6.3 failure as long as the affected-set
detection is itself polynomial, which it is (a snapshot-versus-change
comparison is `O(n²)` per snapshot). The same machinery underwrites
§6.5's rotation branches: most rotations touch a small subset of `P`,
so deeper-lock invalidation is the exception, not the rule.

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

### 6.5 Every canonical form reachable from any pair selection (correctness)

> For any input scrambling and any starting pair the forward pass might
> commit to, the algorithm's exploration reaches every canonical form
> that any other starting pair could reach.

This is the load-bearing correctness invariant under the architectural
commitment in the header of §6 — it is what makes 1-WL's *failure to
identify pair orbits* survivable. If two scramblings commit to pairs
from different pair-orbits, both runs must consider the same set of
candidate canonical forms; the lex-min then resolves them to a common
output.

**Mechanism.** Extend each primary's backward-pass evaluation from
`{direction-flip}` to `{direction-flip × first-vertex-rotation ×
second-vertex-rotation}`. For primary `i = (a, b, dir, kind)` with cell
snapshot `(C_a, C_b)` (captured at guess time, see §3.5):

- **Direction axis:** `dir ∈ {LESS, GREATER}`.
- **First-vertex axis:** `a' ∈ C_a` (a's cell at guess time, including
  `a` itself).
- **Second-vertex axis:** `b' ∈ C_b`, with `a' ≠ b'`.

For each `(dir, a', b')`, replay primaries `0..i-1`, apply
`(a', b', dir)` as a substitute for primary `i`, continue the forward
pass via the normal guess loop, and lex-min the resulting canonical
against the running best. Adopt the winner; rewrite primaries `i..`
accordingly.

**Why this addresses pair-orbit ambiguity.** If `(a, b)` and
`(a', b')` are in the same pair-orbit, both branches produce equivalent
canonicals and lex-min picks one idempotently. If they're in different
pair-orbits, both candidates surface and lex-min picks the smaller,
iso-invariant by construction. The σ-orientation question (which
direction of a swap σ on `(a, b)` to commit to when σ has two valid
mappings) dissolves: enumerating `(a, b')` and `(a', b)` covers both
swap orientations of any such σ.

**Fixpoint iteration.** A single deepest-first sweep of the backward
pass is not sufficient: adopting a branch at a shallow primary `i`
replaces primaries `i+1..end` with fresh primaries from
`ContinueForward` (the prefix+deeper machinery in §10), and those have
not been backward-processed. The implementation iterates the backward
pass until a full sweep adopts zero branches. Termination is guaranteed
because every adoption strictly decreases the canonical's lex value
and canonicals form a finite set. The dependency calculator (§11.10)
replaces this iteration with a one-shot diagram read.

**Complexity (first-cut, naive replay).** Branches per primary:
`|C_a| × |C_b| × 2 ≤ 2n²`. Primaries: `O(n²)` from the P-entry bound
(see §11.4 / paragraph below on false-count). Total branch evaluations
per sweep: `O(n⁴)`. Each evaluation is `O(n⁴)` replay → `O(n⁸)` per
sweep. The number of sweeps until fixpoint is bounded only by
canonical-lex monotonicity (worst case exponential in `n²`, but
empirically small — converges in 2–3 sweeps on the size 4–6 corpus).
§11.10's planned dependency calculator collapses both the per-sweep
cost and the iteration count by sharing state across branches that
differ only in a small subtree of `P`.

**False-count bound (why guess count stays polynomial).** Every guess
writes at least one `P` entry to enter the record; `P` has `O(n²)`
entries, so primary count — including false-symmetry guesses caught by
the backward pass — is bounded by `O(n²)`. Most rotation branches will
prove iso-equivalence rather than discover alternatives; a cheap
iso-equivalence pre-filter (deferred to the calculator) would skip the
bulk.

**Eager vs lazy.** The implementation enumerates the rotation branches
eagerly (every primary, every iteration), rather than only when the
direction-flip fails to improve the canonical. Lazy would be faster in
the true-symmetry-heavy common case but introduces a control-flow
split that could hide bugs where the direction flip happens to look
fine but the rotation would have been correct.

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

The complexity arithmetic, with 6.1–6.5 all holding and the v1
implementation (warm-refined partition, incremental TC, precomputed
prefix-P stack — see §10):

- Forward pass: `O(n²)` primaries × `O(n²)` per refine + apply = `O(n⁴)`.
- Backward pass per sweep: `O(n²)` primaries × `O(n²)` rotation branches
  per primary × `O(n⁴)` per branch evaluation (clone prefix state, apply
  branch, apply deeper, continue forward) = `O(n⁸)`.
- Fixpoint iterations: bounded by canonical-lex monotonicity; empirically
  2–3 on the size 4–6 corpus, no proven polynomial bound without §11.10.

Total per fixpoint pass: `O(n⁸)`. The planned dependency calculator
(§11.10) collapses this by sharing state across branches and removing the
need for fixpoint iteration; target is `O(n⁵)`–`O(n⁶)`.

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

The v1 implementation lives in
[`CanonGraphOrdererFlipValidation.cs`](../GraphCanonizationProject/CanonGraphOrdererFlipValidation.cs)
plus [`IncrementalPartition.cs`](../GraphCanonizationProject/IncrementalPartition.cs).
Lineage: built on top of `CanonGraphOrdererPartialOrderSinglePair`,
replacing its exhaustive recursive `Search` with a greedy `ContinueForward`
plus a `BackwardPass` that iterates to fixpoint.

Key components:

- **`Primary` record** (within `CanonGraphOrdererFlipValidation`): `(A, B,
  Direction, BetweenCell, CellSnapshotA, CellSnapshotB)`. The snapshots
  are vertex-membership lists of the two cells at guess time, captured
  inside `PickAndApplyGuess`. They're what §6.5 rotates over.
- **`WarmPartition`** (in `IncrementalPartition.cs`): the partition data
  structure. Carries `CellOf` and `NumCells` as state; `Refine(adj, p)`
  runs 1-WL refinement to fixpoint, **warm-starting** from the existing
  `CellOf` rather than from an all-zero coloring. When `CellOf` was
  already converged for a similar `P` state, refinement converges in 1–2
  rounds instead of `O(n)`.
- **`ApplyOne` + `CloseAfterInsert`**: incremental transitive closure.
  Each `ApplyOne` writes one P entry and closes via the
  `ancestors × descendants` cross product (`O(n²)` per insertion).
- **`BuildPrefixStack`**: precomputes `(pPrefix[i], partPrefix[i])` for
  every position `i` in the current record at sweep start. Each branch
  evaluation in the backward pass clones the cached pair instead of
  re-applying primaries `0..i-1` from scratch.
- **`TryReplayFromState`**: per-branch evaluator. Clones the cached
  prefix state, applies the branch primary, applies deeper primaries
  (refining the partition after each to keep warm-refine cheap), then
  `ContinueForward` to a total `P`. Returns the suffix record + final
  `P` so the caller doesn't have to replay again.
- **`BackwardPass`**: deepest-first walk; per primary, enumerates `(dir ×
  a' ∈ CellSnapshotA × b' ∈ CellSnapshotB)` branches (with within-cell
  dedup for `a' < b'`), evaluates each via `TryReplayFromState`, lex-mins
  over the resulting canonicals, adopts the winner.
- **Fixpoint loop in `Run`**: backward pass is invoked repeatedly until a
  sweep adopts zero branches. Termination by canonical-lex monotonicity.
- **Diagnostic counters**: `LastPrimaryCount`, `LastWithinCellGuesses`,
  `LastBetweenCellGuesses`, `LastBackwardFlips`, `LastPairRotationsAttempted`,
  `LastLockedThenInvalidated`. The last is the §9 most-diagnostic.

**Deferred to later versions** (named for grep-ability):

- **`DERIVED` records with driver pointers** (§6.4). v1 re-runs closure
  from scratch on each replay rather than tracking which primary forced
  each closure-derived edge. Polynomial-bound argument needs this in.
- **§3.6 transposition fast path / general local orbit test.** v1's eager
  rotation enumeration subsumes the transposition test's case as one
  branch among many. Reintroducing it as a fast path would let us skip
  both direction branches when `(a b)` is a true automorphism.
- **§6.3 snapshot-diff alternative** for deeper-lock re-validation.
- **Dependency calculator** (§11.10).

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
5. **Representative selection in forward pass.** Closed by §6.5: the
   forward pass's lex-min-by-index is an arbitrary starting choice;
   the backward pass rotates representatives within the cell snapshot
   and lex-mins the resulting canonicals. Patching at the selection
   step (e.g. via a pair signature) was deliberately rejected — it
   would deepen reliance on 1-WL's identifying power, which the
   architecture rejects.
6. **Cell snapshot scope.** §3.5 now specifies a cell-tree fragment
   sufficient for both the §3.6 transposition test and §6.5's rotation
   enumeration. The minimal scope can be tightened later once the
   §6.3 snapshot-diff alternative is implemented.
7. **Local-orbit-test sub-tree pairing.** *Resolved.* Every primary
   individualises its endpoints into singleton sub-cells, so the local
   orbit test is exactly the transposition test (§3.6 practical note).
   The sub-tree-pairing concern only resurfaces if a future variant
   introduces block guesses.
8. **Between-cell guess necessity.** *Resolved.* The 2K2 trace settles
   it: after `0<1` within `{0,1,2,3}`, refinement gives cells
   `{0},{1},{2,3}`, and a second within-cell guess on `{2,3}` leaves
   `{0,1}` vs `{2,3}` P-incomparable. Between-cell guesses are
   required for any graph with multiple automorphism-equivalent
   components. Specified in §3.3.
9. **Lex-min-by-index iso-invariance argument was wrong as stated.**
   *Resolved.* A 1-WL cell is one vertex-orbit but can be several
   pair-orbits; the earlier note conflated them. Subsumed by §6.5's
   rotation mechanism.
10. **Dependency-relation calculator (planned optimization on §6.5).**
    The first-cut §6.5 mechanism replays a full forward pass per
    branch, giving `O(n⁸)`. A future iteration will build an `O(n²)`
    boolean-style dependency state diagram that encodes, for each
    guessed relation, which cells move under `<` vs `>` and how those
    moves interact with other guesses. Lex-min then reads the canonical
    off the diagram without re-replaying. Until built, naive replay
    suffices to validate §6.5 empirically; failure cases discovered
    during validation feed the calculator's design.
