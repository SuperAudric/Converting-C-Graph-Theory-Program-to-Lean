# Chain-descent canonizer — algorithm and requirements

This doc specifies the chain-descent graph canonizer **as a whole**: the
algorithm, the requirements it must satisfy to be correct, the budget that makes
it polynomial-or-flag, and the propagation substrate the whole thing runs on.

The hardest single component — the **oracle** that sorts a cell into orbits, the
one piece whose polynomial bound is open — has its own doc:
[`chain-descent-calculator.md`](./chain-descent-calculator.md). The current
oracle architecture — de-classed (non-class-specific) recovery and the unified
oracle that the cascade and linear faces fold into — lives in
[`chain-descent-declassing.md`](./chain-descent-declassing.md); read it as a key
companion to this doc. A gentle, build-from-nothing introduction is
[`chain-descent-simplified-overview.md`](./chain-descent-simplified-overview.md).

> **Lineage.** The current design is *chain descent* — a single budgeted
> recursion. An earlier generation was a two-pass "flip-validation" strategy (a
> greedy forward record plus a backward correction sweep). That generation is
> recorded in §13, because the current design inherits its load-bearing pieces:
> **invariant 6.2**, the **single-pair / 1-WL** propagation substrate, and
> **closure-as-guess**. Where §13 conflicts with the rest of this doc, the rest
> of this doc wins.

The final bar of correctness is a Lean proof in the
[`GraphCanonizationProofs`](../GraphCanonizationProofs) project, after the C#
implementation has been shown empirically correct on the isomorphism-stability
test bed and on the CFI hard cases (§11–§12).

---

# Part I — The algorithm

## 1. What we are computing

A **canonical form** of a graph `G`: a relabelling of its vertices chosen so
that two graphs get the *same* labelled adjacency matrix exactly when they are
isomorphic.

The defining recipe: among all `n!` ways to label the vertices `0..n-1`, write
down the adjacency matrix of each, and take the lexicographically smallest. That
smallest matrix is the canonical form, and it is isomorphism-invariant for free
— relabelling the input does not change the *set* of `n!` matrices, so it does
not change their minimum.

Enumerating all `n!` labellings is too slow. The entire algorithm is about
computing that minimum **without** enumerating them.

## 2. The search space: individualization-refinement

Instead of choosing a whole labelling at once, build it up.

**Cells.** *Color refinement* (1-WL) repeatedly recolors every vertex by the
multiset of its neighbors' colors, until colors stop changing. Vertices that end
up the same color form a **cell**. Refinement is cheap, deterministic, and
isomorphism-invariant: the cells, and their canonical numbering, depend only on
`G`'s structure, never on the input labelling. Refinement never makes a mistake
— but it is *incomplete*: it can leave vertices in the same cell that the graph
actually treats differently.

**Leaves.** If every cell is a single vertex, the labelling is fully determined
(cell `#i` is vertex `#i`) — a **leaf**.

**Individualization.** If some cell `C` has ≥ 2 vertices, refinement is stuck.
Pick one vertex `v ∈ C`, *individualize* it — declare "`v` is the smallest
vertex of `C`" — and refine again. The new information about `v` often
propagates: `v`'s neighbors become distinguishable, then theirs, and so on.

**The IR tree.** Each choice of which vertex to individualize is a branch.
Recursing on every choice builds the **individualization-refinement tree**; its
leaves are full labellings, and the canonical form is the lex-smallest leaf
matrix. This is how nauty and similar tools work. **The catch:** the IR tree can
be exponentially large — nauty is provably exponential in the worst case
(Neuen–Schweitzer) on CFI-derived graphs.

## 3. True vs. false symmetry

At a branch point — a cell `C` with several vertices to individualize — there
are exactly two situations:

**True symmetry.** The vertices of `C` are genuinely interchangeable: the graph
has an **automorphism** carrying one to another. Then individualizing `v` or
individualizing `w` leads to the *same* canonical form — the two subtrees are
mirror images. **You may pick any one vertex, descend, and never look at the
rest.**

**False symmetry — a genuine decision.** The vertices of `C` are genuinely
different: there is *no* automorphism carrying one to another, so different choices
give different canonicals and you genuinely have to compare them.

**Refinement cannot tell these apart** — both present as a cell 1-WL cannot split,
an **apparent decision**; deciding which it is is the oracle's job. A true symmetry
can be *hidden* (CFI gauge cells look like decisions but are true symmetries the
linear oracle exposes — calculator §5/§6), so "genuine decision" strictly means
*no automorphism exists*.

If every branch were a true symmetry, canonization would be a single descending
path — polynomial. **Exponential blow-up is apparent decisions piling up.** The
whole algorithm is organized around cheaply telling a (possibly hidden) true
symmetry from a genuine decision.

## 4. The algorithm: chain descent

Descend the IR tree — but at each cell, *before* branching, sort the cell's
vertices into **orbits** (maximal groups of genuinely-interchangeable vertices)
and branch on **one representative per orbit only**.

- Cell is one orbit (true symmetry) → one representative → no branching, just
  descend.
- Cell is `k` orbits → `k` representatives → a `k`-way fork; canonize each
  branch, take the lex-min.

The recursion, per node:

1. **Refine** the partition (warm 1-WL, §9). If discrete → a leaf; read off the
   matrix.
2. Pick the **target cell** — the lex-min non-singleton cell by canonical cell
   id. This choice is iso-invariant (§7).
3. Ask the **oracle** (§5) which target-cell vertices to branch on — one
   representative per orbit.
4. For each representative `v`: individualize `v`, recurse, collect the leaf
   matrix.
5. Return the lex-min over the branches.
6. **Harvest:** when two branches reach the same leaf matrix, the relabelling
   between them is an automorphism — verify it and fold it into the residual
   group (§6, the chain).

Three components make this work — the oracle (§5), the budget (§6), and the
chain (built as the harvest of §4 step 6). They are the subject of Part II.

---

# Part II — The requirements

The algorithm above is correct and polynomial-or-flag *only if* its components
satisfy specific requirements. This part states them. They are deliberately
separated from the algorithm because the design's whole structure is to **pin
each requirement to one named, swappable component** rather than smear it across
the algorithm.

## 5. The oracle interface

The **oracle** is the component that, given a target cell `C`, returns its
partition into orbits. It is reached through one interface (`ITransversalOracle`
in code); the algorithm makes no other assumption about it. The oracle itself —
how it certifies orbits, the cascade and linear faces of one recovery-based
harvest (see [`chain-descent-declassing.md`](./chain-descent-declassing.md) §6) —
is the subject of
[`chain-descent-calculator.md`](./chain-descent-calculator.md). What the
*algorithm* requires of any oracle:

> **Soundness.** Never put two vertices in the same orbit without a *proof* — an
> actual automorphism, verified edge-by-edge, that maps one to the other.

Why this rule and not the reverse: if the oracle *splits* one true orbit into
two, the algorithm branches once more than necessary — slower, still correct. If
the oracle *merges* two real orbits, it drops a representative — and the dropped
branch might have held the true minimum. So the oracle is allowed to be
over-cautious; it is never allowed to be over-confident. (This is the
*completeness* half of §7 restated as a constraint on the oracle.)

> **Iso-invariance.** The oracle's output depends only on graph structure —
> never on the input labelling, and never on the order branches happen to be
> visited.

> **Bounded work, or flag.** The oracle does *bounded* work. When it can certify
> the orbits cheaply, the descent continues. When it cannot, the run **flags** —
> it does *not* fall back to brute force. A returned canonical form therefore
> always means "computed cheaply"; a flag means "this graph needs a tool this
> oracle does not have."

Discovering orbits cheaply is the hard problem — equivalent in full generality
to GI ∈ P. The design does not solve it; it isolates it behind this interface.
See the calculator doc for what is and is not tractable.

## 6. The budget

Many small forks at many levels could still multiply into an exponential tree.
So the descent carries a **polynomial node budget `B(n)`**. Every node of the
descent tree spends from it; when it is exhausted, the run flags
(`CanonizationFlaggedException`).

The budget is what makes "polynomial or flag" a *guarantee* rather than a hope:
the algorithm physically cannot run longer than `B(n)`. A graph canonizes iff
its certified descent fits inside the budget.

**The chain (the budget's companion structure).** Every true-symmetry orbit
comes with the automorphisms that witnessed it. Stacked level by level as the
recursion returns, these automorphisms generate `Aut(G)` — organized as a
**stabilizer chain** (a base of individualized vertices, plus, at each level,
the orbit of that vertex). This is expected: computing a canonical form,
deciding isomorphism, and computing `Aut(G)` are polynomial-time-equivalent, so
a canonizer produces the group for free. The chain is also *useful mid-run*: an
automorphism found deep in the tree, if it fixes a shallow level's path,
certifies orbits at that shallow level. The chain is the calculator's central
object — see [`chain-descent-calculator.md`](./chain-descent-calculator.md) §2.

## 7. Correctness

The algorithm must return an isomorphism-invariant, complete canonical form — or
flag — for *every* input, regardless of which oracle is plugged in. Three
requirements, each resting only on the oracle's soundness/iso-invariance rules
(§5) and on refinement being isomorphism-invariant.

**Invariant 6.1 — iso-invariance of cell ids.** Canonical cell ids (from
canonical 1-WL signature order) are a function of graph structure only. So the
*set of candidate cells* and the choice of target cell at any node are
iso-invariant. This is the reference frame everything else stands on.

A subtlety this frame does *not* by itself remove: a 1-WL cell is a single
candidate *vertex*-orbit, but it can host several distinct *pair*-orbits (C4:
adjacent vs. diagonal pairs; C6: distance-1/2/3 pairs; CFI bases: subtler splits
1-WL on pairs cannot separate). Picking a representative *pair* by vertex index
is therefore *not* iso-invariant. Chain descent sidesteps the trap by branching
over the whole iso-invariant target cell and delegating the orbit split to the
oracle — never to an index rule. (The earlier flip-validation design instead
made a non-iso-invariant pair guess and repaired it afterwards; §13.)

**Output iso-invariance.** Cells and their canonical numbering are
iso-invariant; the target cell is chosen by canonical id (6.1); and the oracle
is *required* to be iso-invariant (§5). So two labellings of the same graph
produce the *same* descent tree, hence the same set of leaf matrices, hence the
same minimum.

**Completeness.** Because the oracle never merges two real orbits (soundness),
its representatives hit every orbit of the target cell; the lex-min over
representatives equals the lex-min over the whole cell. No labelling that could
yield a smaller matrix is ever skipped. A leaf matrix determines the graph up to
isomorphism, so equal canonical forms ⇔ isomorphic graphs.

**Flag iso-invariance.** The descent must reach the *same* verdict — canonize,
or flag — on every labelling of a graph. Because "exceeds `B(n)`" is a function
of the node count, the node count must not depend on the input labelling. This
is sharper now that the linear oracle is *online* (calculator doc §6): its
branch-traversal and twist-discovery must be a deterministic function of
iso-invariant cell ids. In the current (folded) model this iso-invariance
obligation attaches to the recovery / forced-node layer (`forcedNode_relabel`,
[`declassing`](./chain-descent-declassing.md) §4/§7); the "twist-discovery"
phrasing above is the legacy order model, but the obligation itself stands —
only its target is retargeted. Invariance must hold by construction; it is a
proof obligation (§12).

Correctness is **independent of which oracle is plugged in** and independent of
the budget — exhausting the budget only ever causes a flag, never a wrong
answer.

## 8. Why it is polynomial when it works

Cost is a **sum, not a product**:

```
total work  =  Σ over the nodes of the descent tree ( oracle work at that node )
```

and the budget bounds the node count. The old IR-search design's cost was a
*product* — the size of a fully-explored tree — because it explored every branch
and only noticed redundancy afterwards. **Replacing the product with a sum is
the entire point of the rewrite.**

This sum is genuinely polynomial exactly when the oracle certifies every node
cheaply. Three supporting facts — **T-A, T-B, T-C** — keep the accounting
honest; they are defined and discussed in
[`chain-descent-calculator.md`](./chain-descent-calculator.md) §4:

- **T-A** — the chain and its transversals are polynomial-size (you store
  generators, never group elements). A citation.
- **T-B** — the descent has ≤ `n` levels. A citation.
- **T-C** — polynomial work per node. *This is the oracle, and the only open
  factor.*

The design's contribution to the polynomial question is to pin the difficulty
to T-C — one named, swappable component — instead of smearing it across the
algorithm.

---

# Part III — The propagation substrate

The descent of Part I individualizes vertices and refines. Underneath, those
individualizations accumulate as a partial order, refinement propagates them,
and the *pattern* of that propagation is what the linear oracle (calculator doc
§6) reads to discover symmetry. This part specifies that substrate. It is the
model **invariant 6.2** is proved against and the model the linear oracle
consumes.

## 9. State and operations

**State.** The only persistent state is

```
P : n×n matrix over {Less, Unknown, Greater}
```

held antisymmetric. `P` begins all `Unknown` apart from order forced by vertex
types. The cell partition is re-derived from `(A, P)` at every step — never
stored. A flat matrix, but it *induces* a hierarchical **cell tree**: the root
is all vertices; a cell's children are the sub-cells 1-WL produces once a guess
touches it; leaves are singletons. The tree is the navigable mental model; the
matrix is the storage. The cells are **P-coherent**: any two members of a cell
have the same multiset of `(cell, A-edge, P-relation)` triples over all vertices
— so the induced tree is exactly the 1-WL partition lattice of `(A, P)`, and
order propagates through it cell-respectingly (a cell's order relative to
another cell is inherited uniformly by all its members).

**The state is the output; the path to it is not.** A leaf's canonical matrix is
a function of `(A, P_final)` alone. The order in which guesses built `P`, and
the provenance record (§10), are a *transcript* of how that state was reached —
never an input to the matrix. This "only the final state matters, not the path
to it" property is load-bearing for the proofs.

**Refine** — free; reads `P`, never writes it. 1-WL colour refinement on the
coloured graph `(A, edge_label = (adj[u,v], P[u,v]))`: each vertex's colour is
the sorted multiset of its neighbours' `(colour, edge, Prel)` tuples, iterated
to fixpoint. Refinement is **split-only**: it never orders cells and never
writes `P`. Cells are numbered in canonical signature order, so every "lex-min
cell" rule is iso-invariant.

The implementation uses **warm refinement** — refinement re-started from the
previous step's converged colouring rather than from scratch. Warm refinement is
split-only by construction (it can only further partition the cells of its
starting colouring, never merge them — `warmRefine_refines` in `ChainDescent.lean`,
proved). This property is what makes invariant 6.2 hold (§10); fresh 1-WL would
break it.

1-WL is the chosen refinement strength; higher-`k`-WL is out of scope — each
additional `k` adds `n` to the exponent without improving the worst case on the
families that defeat 1-WL.

**Guess.** Individualizing a vertex is a **guess**. In the substrate model a
guess writes a *single* `P` entry: pick a pair `(a, b)` with `a, b` in the same
cell (or in two P-incomparable cells), write `P[a,b] = Less`, refine. This
single-pair shape is deliberate — see §11. The guessed vertex is individualized
as a fresh colour, so `a` and `b` start as singletons after the guess.

A guess pairs two vertices of the *same* cell (a **within-cell** guess) or two
vertices of *distinct, P-incomparable* cells (a **between-cell** guess).
Between-cell guesses are **necessary**, not a convenience: a graph with several
automorphism-equivalent components — `2K2` is the minimal case — reaches a state
where every cell is internally resolved yet `P` is not total, because the
components' cells are mutually P-incomparable. Only a between-cell guess can
order them.

## 10. Closure as a guess

After a write to `P`, the partial order can be **transitively closed**: for each
`(i, k, j)` with `P[i,k] = Less`, `P[k,j] = Less`, `P[i,j] = Unknown`, set
`P[i,j] = Less`. A closure-derived relation is recorded as a **`DERIVED`
record** carrying a `driver` pointer — the index of the primary guess whose
write completed the chain. A contradiction — a cycle, or `P[v,v] = Less` — marks
the branch dead.

Only the **final closed `P`** is part of the spec: the closure *algorithm*, and
the *order* in which derived relations are written, do not affect it
(incremental closure over `ancestors(x) × descendants(y)`, `O(n²)` per
insertion, and Floyd–Warshall both yield the same closed relation). This is the
§9 "state is the output, path is not" property applied to closure.

**Why the provenance matters — invariant 6.4.** Without driver tracking, closure
can produce an `O(n)`-long chain of relations all tracing to one guess; the
provenance record — *which guess forced which derived relation* — is what lets a
**between-cell ordering** decision's coupled component be delineated where TC
genuinely chains. At most `n(n−1)` `DERIVED` records exist at any time, so the
bookkeeping is polynomial.

> **Correction (2026-05-28).** An earlier version called this provenance "the
> linear oracle's required state." That overstated its role for the oracle's
> primary (CFI / within-cell) target: there the cascade propagates by
> **refinement**, not transitive closure, and TC produces no derived entries to
> track (under relegated TC there is no in-loop closure; in the implementation a
> within-cell guess on a uniform-type graph chains nothing — measured zero). The
> linear oracle delineates its coupled component from the **refinement
> footprint** (the parent↔child partition diff), per
> [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §3. TC
> provenance remains the right tool for between-cell ordering, but it is not the
> linear oracle's critical-path state.

**Closure asymmetry on non-automorphic pairs is sound.** A genuine decision
makes closure run differently in its two branches — a chain reaches one vertex
in one branch and not in the other. This is not an inconsistency to be repaired.
A non-automorphic pair `(u, v)` is, by definition, in *different* cells; once it
is, every order relation between them is *forced by structure*, not chosen.
Closure asymmetries are therefore confined to pairs whose ordering descends from
a guess — and there the asymmetry *is* the genuine decision the oracle exists to
resolve, not a fault. The `driver` pointer attributes each derived relation to
the guess that forced it, so the two branches of a decision carry cleanly
separated derived chains and a flag is never a stranded contradiction.

**Two models, one substrate.** The implementation runs closure with `DERIVED`
records as above. The *proof* of invariant 6.2 (§10 of this list — see next
section) uses a cleaner **relegated-TC model**: a guess writes one `P` entry and
*no* transitive closure sits in the refinement loop; an inconsistent partial
order is handled as a lex-min *ranking* criterion, not a propagation step. The
two are equivalent in practice — a non-lex-min branch is never chosen, so
being-ranked-worse ≡ being-pruned — and relegating TC is what makes 6.2
provable, because off the guessed pair no refinement signature can see the
guess. The σ-relabel shortcut "`transitiveClose` commutes with the
`less ↔ greater` swap" is **false** (`transitiveClose_swap_false` in
`ChainDescent.lean`, witness `conflictMatrix`); it is moot under TC relegation.

**A fidelity gap between the two TC operators.** The Lean `closeStep` /
`transitiveClose` **resolves** order conflicts as part of producing the closed
relation; the C# `TransitiveClose` (`ChainDescent.cs` ~lines 592–615) is
**partial** — on a cycle or direction conflict it returns `false` and the caller
prunes the branch. The two agree in practice (a conflicting branch is dead
either way), but they are *different operators*, and the distinction matters for
C#-side validation and any future reconciliation of the two implementations.

## 11. Why single-pair guesses do not prune interleavings

A guess writes **one** `P` entry, not a block. This was a deliberate choice, and
a stated worry was: if `A, B, C` are non-automorphic and a guess commits to
`A < B`, can the descent still reach the canonical order `A < C < B`?

**Yes.** A single-pair guess `A < B` constrains `A`'s position relative to `B`
only — `C` is untouched. The total orders consistent with `A < B` include
`A < B < C`, `A < C < B`, *and* `C < A < B`; further guesses settle which. The
contrast is with **block guesses**, which write "every member of `A`'s lineage
below every member of `B`'s lineage" in one step — *that* eliminates
interleavings. The single-pair design is kept exactly to avoid that, so the
descent can reach interleaved canonical orders.

What changes with the choice of guess pair is the *order in which sub-orbits get
resolved*, not the *set of total orders reachable*. This is also why the linear
oracle's reverse-symmetric-propagation argument (calculator doc §6) is a clean
statement about a single pair's two directions.

## 12. Invariant 6.2 — reverse-symmetric propagation

The load-bearing property of the substrate, and the dependency the linear oracle
(calculator doc §6) rests on.

> **Invariant 6.2.** For every pair `(v, w)`, `v` and `w` are in the same cell
> after propagating `a < b` iff they are in the same cell after propagating
> `b < a`.

The *partition coarseness* is direction-independent; only the order labels, and
the roles of `a, b`, swap. This is what lets the linear oracle treat a genuine
decision's two branches as one shared partition with mirrored order — the
**coupled component** of the calculator doc.

**It is a claim about warm refinement specifically.** Fresh 1-WL on the
post-guess matrix can produce *different* partitions under the two directions:
asymmetric closure chains in one direction can add entries that distinguish
vertices the other direction leaves indistinguishable. (Minimal fresh-1-WL
counterexample: 3 vertices, no edges, `P_pre(2,0) = <`; guess `(0,1,<)` chains
`2→0→1` and fresh 1-WL keeps `{0},{1},{2}`, while guess `(0,1,>)` has no chain
and fresh 1-WL merges `1,2`.) Warm refinement, being split-only, cannot merge
`1` and `2` in either direction, and the discrepancy disappears. 6.2 is true for
warm refinement, false for fresh 1-WL.

> ⚠️ **Correction (2026-05-21).** An earlier argument claimed the splits a guess
> induces are *uniform* within each cell — every cell-mate gains the same new
> `Less`/`Greater` entries. The first half is **false**. Cell-coherence is a
> *multiset* property (cell-mates relate identically to every *cell*), but a
> guess `(a,b)` acts on individual *vertices*, and TC chains run through
> individual vertices. Two cell-mates can relate symmetrically to `a`'s cell yet
> asymmetrically to `a` itself, so the `a→b` edge reaches one and not the other:
> **a cell genuinely splits**. Machine-checked by `cell_split_uniform_false` in
> `ChainDescent.lean`. The honest claim is only the *second* half — a cell
> splits **into the same sub-cells under either direction**, order labels aside.
> That weaker, direction-symmetric split statement is the genuine content of
> 6.2; the no-split statement `cell_split_uniform` is not 6.2 and is false.

**The strong (label-coincidence) version does not follow.** Even under warm
refinement, the actual colour *values* `χ^<(v)` and `χ^>(v)` differ — signatures
include the direction-dependent `Less`/`Greater` label. A "`χ^<(v) = χ^>(σ(v))`
for an explicit `σ`" version would require `σ` to be a true automorphism of
`(A, P_pre)` — i.e. `(a,b)` to be a transposition-orbit pair, exactly the
true-symmetry case. The weak (partition) version is the most that holds for
arbitrary `(a,b)`, and is what the linear oracle needs.

**Status — `warm_6_2` is proved (2026-05-21).** Lean development in
[`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean), under the
model of §10: relegated TC (a guess writes one `P` entry, no TC in the
refinement loop) and fresh-colour individualisation (the guessed pair starts as
singletons). Lean results:

- `warm_6_2` (the §12 partition claim) — **proved**. `P⁻` and `P⁺` differ only
  inside `{a,b}`; off-pair vertices refine identically across the two
  directions; `a, b` stay singletons throughout. Induction on the refinement
  round.
- `warmRefine_refines` (warm refinement is split-only) — **proved**; supplies
  the singleton-preservation lemma.
- `transitiveClose_swap` (σ-relabel commutes with TC) — **disproved**
  (`transitiveClose_swap_false`). Moot under TC relegation; kept as a record.
- `cell_split_uniform` (cell-mates keep equal post-guess signatures) —
  **disproved** (`cell_split_uniform_false`); the abandoned no-split route.

Empirically verified on `C4` with `(0 1)` non-Aut, on the 6-vertex asymmetric
graph `{0-1, 0-2, 0-3, 1-4, 2-5}` with `(1 2)` non-Aut, and on `K3`.

**6.2 generalised — the descent spine.** `warm_6_2` flips *one* decision;
`warmRefine_agree_off'` (proved, `ChainDescent.lean`) flips *any set* at once: if
two `P`-matrices agree on every entry with an endpoint outside a decision set
`D`, and `D`'s vertices are `χι`-singletons, warm refinement gives the *same
partition* under both — even when the two starting colourings agree only up to
partition, which is what lets the argument chain across descent levels.

Its consequence is the **descent spine**. With a target-cell selector that reads
only the partition (not raw refined colour ids), induction down the descent
shows every branch at level `k` shares the same partition, target cell, and
decision set: the tree of *partitions* is a **path** of length ≤ `n`, and the
`2^d`-way branching lives entirely in the order labels overlaid on it. Hence:

- *Refinement is `O(n)` passes for the whole tree, not `O(2^d)`* — the spine is
  computed once, by a single non-branching pass with every guess set `less` (any
  direction gives the same partition). This sharpens the §8 cost accounting.
- *Cascade is direction-blind* — a sub-decision forced in one branch is forced
  identically in its mirror; the genuine-decision set depends only on `D`.
- *Implementation requirement* — for cross-branch sharing to be sound the
  target-cell selector **must be partition-invariant**: across a decision's two
  directions the refined colour *values* diverge, so a "lowest raw cell id" rule
  can pick different cells in the two branches though the partition is identical.
  The reuse key is the *decision set*, not the colouring.

The spine shares the *refinement* work, not the *leaves* — each leaf is still a
distinct order on `D` (for a rigid graph all `2^d` are distinct; §15 gap 5). It
reduces the descent to "polynomially many refinements + a residual `Z₂^d` label
optimisation", handing the linear oracle
([`chain-descent-calculator.md`](./chain-descent-calculator.md) §6) one fixed
partition to optimise over. **(Role note.)** The spine, invariant 6.2, and 6.4
below are **proved** and remain the load-bearing substrate; but their stated
role as *what the linear oracle rests on to fire* is the **legacy order model**.
In the current model firing is the unified colour-model harvest
([`declassing`](./chain-descent-declassing.md) §6) and these invariants back the
substrate, not the firing mechanism. The proofs are unaffected. Proved:
`warmRefine_agree_off` and its composable
form `warmRefine_agree_off'`, `target_direction_blind`, `target_agree_off`,
and — the recursion stringing them across the descent — `spine_branch_independent`
(trace form) / `SpineChain.branch_independent` (chain form) in
`ChainDescent.lean` §15, under existential `IndivStep` individualisation.
The spine is **not yet implemented in the C#** (the descent re-refines per
node). Full account:
[`ChainDescent.md`](../GraphCanonizationProofs/ChainDescent.md) §11.

**What the spine does *not* rest on.** Symmetric "forcing" — the idea that a
guess's two directions force each other into a fixed order — is **not** a viable
foundation for branch reduction. It is only an order-*label* claim, and it is
valid solely in the abelian / `Z₂^d` regime; outside it there is no such forcing
to lean on. The viable foundation is the **automorphism-equivariance of
`warmRefine`** — the `*_invariant_of_isAut` / `*_transport` lemmas — which is
what `warm_6_2` and the spine results above actually use. That positive
foundation is documented elsewhere and is not re-derived here
([`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) §13.5,
[`chain-descent-abelian-sufficiency-handoff.md`](./chain-descent-abelian-sufficiency-handoff.md)
§4 M1a); only the rejection of forcing and its abelian-regime scoping are
recorded here. (Not to be conflated with orbit-recovery §313's "Q3", which is a
different question — universal early-recovery for `CFI(H)`.)

---

# Part IV — Status

## 13. Lineage: the flip-validation generation

The current design — a single budgeted recursion plus an oracle seam — was
reached through an earlier generation, recorded here for the design choices it
established and the load-bearing pieces the current design still uses. (A second
wrong turn, the unbounded nauty-IR calculator and the boolean-class era, is
recorded in [`chain-descent-calculator.md`](./chain-descent-calculator.md) §10.)

**What flip-validation was.** A *two-pass* canonizer over the `P`-matrix
substrate. A **forward pass** made greedy single-pair guesses by a deliberately
simple, non-iso-invariant lex-min-by-index rule, writing each into `P` and
recording it. A **backward pass** then walked the guess stack deepest-first and,
per guess, enumerated branches over `{direction × first-vertex-rotation ×
second-vertex-rotation}` from a cell snapshot taken at guess time, replayed each,
and lex-min'd the resulting canonicals — correcting wrong greedy choices instead
of branching on them. The architectural premise was that **the discriminator
(1-WL) need not identify structure completely**: when 1-WL could not single out
an iso-invariant choice, the forward pass guessed and the backward sweep
restored iso-invariance. The first-cut cost was `O(n⁸)` per sweep, with a
planned "dependency calculator" to bring it down. Implemented in the
since-deleted `CanonGraphOrdererFlipValidation.cs`, built on
[`CanonGraphOrdererPartialOrderSinglePair`](../GraphCanonizationProject/Archive/Exploration/CanonGraphOrdererPartialOrderSinglePair.cs).

**Why it was superseded.** The two-pass correction sweep was replaced by chain
descent's single budgeted recursion. The backward pass's job — reconciling
non-canonical greedy choices — is done in chain descent by branching on the
oracle's representatives and taking the lex-min directly, with the budget
guaranteeing termination. The backward pass's `§6.5` "pair rotation" mechanism
(enumerate alternative representatives, lex-min across canonicals) survives,
re-housed: in the stabilizer-chain model it *is* lex-leader descent over a
per-level transversal — see [`chain-descent-calculator.md`](./chain-descent-calculator.md)
§2. The flip-validation `§6.3` "deeper-lock survival" invariant and the `O(n⁸)`
arithmetic were tied to the backward pass and are not part of the current
design.

**What the current design inherited from it** — and where it now lives:

- the **`P`-matrix / single-pair / warm-1-WL substrate** (§9) — the partition
  engine;
- **closure-as-guess** with `DERIVED`/`driver` records, the old `§3.4`/`§6.4`
  (§10) — substrate provenance state (legacy: the linear oracle's provenance state);
- **invariant 6.2**, the old `§6.2` (§12) — a substrate invariant, since proved
  as `warm_6_2` (legacy: the linear oracle's firing dependency — see §12 role note);
- **invariant 6.1**, iso-invariance of cell ids (§7);
- the **single-pair-does-not-prune-interleavings** rationale, the old `§7` (§11).

### The invariant ledger

The earlier generation organised its correctness and complexity claims as a
numbered family `§6.1`–`§6.5`. The names `6.1`, `6.2`, `6.4` are still used in
this doc and in the Lean development; so that nothing is silently dropped, here
is where each landed.

| Old | Statement | Where it is now |
|---|---|---|
| 6.1 | Iso-invariance of cell ids | **Live** — §7, a correctness building block. |
| 6.2 | Reverse-symmetric propagation of warm refinement | **Live** — §12; proved as `warm_6_2`; a substrate invariant (legacy role: the linear oracle's firing dependency — see §12 role note). |
| 6.3 | Deeper-guess locks survive shallow flips | **Retired** — a property of the flip-validation backward pass; chain descent has no backward sweep and no "deeper locks" to survive. |
| 6.4 | Closure as a guess (`DERIVED` records + `driver`) | **Live** — §10; substrate provenance state (legacy: the linear oracle's provenance state). |
| 6.5 | Every canonical form reachable from any pair selection | **Live, re-housed** — the invariant *the branch representatives cover every orbit of the target cell* is the §7 **completeness** requirement; the enumerate-and-lex-min operation is lex-leader descent over a per-level transversal ([`chain-descent-calculator.md`](./chain-descent-calculator.md) §2). The flip-validation backward-pass implementation (replay, fixpoint iteration) is retired. |

The old `§6` header decomposed the claims as *correct iff 6.1 + 6.4 + 6.5;
polynomial iff 6.2 + 6.3*. In current terms: **correctness** rests on
iso-invariant cell ids (6.1, §7), oracle soundness (§5), and completeness (the
6.5 content, §7); the **polynomial bound** rests on the budget (§6) and a
polynomial-per-node oracle (T-C, calculator §4). Note that **6.2 moved out of
the complexity column** — it is no longer a backward-pass speed argument but a
*correctness* dependency of the linear oracle.

## 14. Validation strategy

The empirical bar, before and alongside the Lean proof. Run on:

- **The `KnownGraphs` corpus** at sizes 4–7 for regression: every graph must
  scramble-invariantly produce one canonical form, and the number of distinct
  canonical forms must equal the number of distinct graphs (matches the size-4
  `TwoDisjointPair` and size-7 1044-graph tests).
- **CFI(K_m)** for `m = 3, 4, 5, 6`, via
  [`CfiGraphGenerator`](../GraphCanonizationProject/CfiGraphGenerator.cs).
- **Miyazaki graphs** at growing sizes (generator to be added) — the
  Neuen–Schweitzer multipede family, the IR blind spot (§15 gap 5).

Diagnostic signals per run:

| Signal | What a failure looks like |
|---|---|
| Canonical form across scramblings | Disagreement falsifies output iso-invariance |
| Flag verdict across scramblings | Disagreement falsifies flag iso-invariance |
| Descent node count vs `B(n)` | Exceeds budget on a graph that should canonize ⇒ Tier-1 target unmet |
| Node count by depth (`NodesByDepth`) | Super-polynomial growth ⇒ genuine decisions stacking |
| Residual group order at flag time | Non-trivial ⇒ Tier-2-like; trivial ⇒ IR blind spot (§15 gap 5) |

The two scramble-invariance signals are the correctness bar; the node-count
signals are the polynomial bar.

## 15. Path to proof, and gaps

**Path to proof.** (1) The chain-descent harness, validated for iso-invariance
and completeness on the §14 corpus. (2) CFI / Miyazaki stress — the node-count
signals either show polynomial structure or pinpoint the broken requirement.
(3) Lean formalisation in [`GraphCanonizationProofs`](../GraphCanonizationProofs)
alongside `ChainDescent.lean`: correctness (§7) and, conditional on the oracle,
the polynomial bound (§8). The proof is the final bar; GI ∈ P is open, so the
bar for the polynomial claim is high.

**Algorithm-level gaps.** Recovery is now proved *non-class-specifically*
([`declassing`](./chain-descent-declassing.md)), so per-class completeness is
the witness layer rather than a standalone gap. The current oracle frontier —
M-B, depth witnesses, flag iso-invariance, and the wall — is in
[`declassing`](./chain-descent-declassing.md) §9.

1. **Budget / soundness handshake.** If the budget interrupts the oracle
   mid-certification, the oracle must flag — never return a partially-built,
   possibly-unsound orbit partition. The handshake between "out of budget" and
   "oracle soundness" must be specified so a flag can never be silently
   downgraded to a wrong answer.

2. **Flag iso-invariance must hold by construction.** §7 *requires* the node
   count — hence the flag verdict — to be labelling-independent. With the linear
   oracle online (calculator doc §6), this means its traversal and
   twist-discovery must be deterministic functions of iso-invariant cell ids. A
   proof obligation, not a checkable afterthought.

3. **`DERIVED` driver assignment.** "The primary whose write completed the
   chain" is well-defined when one primary edge per closure round completes a
   given `(i,j)` path; a single pass can complete several paths through the same
   primary. Tie-breaking by primary index is iso-invariant, but "ride with the
   driver" needs every contributing primary to give the same verdict — a precise
   statement is owed.

4. **Component combination (Tier 0).** Disjoint graphs are split into
   components, each canonized, then reassembled in a sorted order. The sort key
   being a *complete* invariant across all vertex-type regimes is assumed, not
   proven — a small pre-existing gap inherited from the prior code.

5. **The flagged region exceeds Tier 2.** Tier 2 (no cascade + a non-abelian
   factor — a **Cameron section**, of which a Johnson / `A_k`-on-subsets group
   is the leading `d=1` case; product actions are the non-Johnson instances) is
   the genuine hard core, aligned with Babai's split-or-Johnson obstruction —
   flagging it is honest hardness. **Two distinct claims must not be conflated
   here** (the disentangling is
   [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
   §0): *(O\*)-existence* — that such an obstruction *never arises* from the
   descent — is the **construction question**, equivalent in strength to
   **GI ∈ P**, and correctly excluded (no Lean obligation, the boundary); whereas
   *(O\*)-classification*, the **Exhaustive-Obstruction Lemma** — that *if* a
   non-cascade, non-abelian residual arises it *is* a Cameron section — is
   **Cameron-hard, not GI-hard**: a finite target with a genuine Lean obligation,
   not part of the wall. The near-theorem — you cannot hide a Johnson as a
   graph's *visible* symmetry — is written up in
   [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
   (Pieces A and B proved, Piece C scoped; the existence/classification split and
   its O'Nan–Scott / Cameron grounding are in that doc's §7). But the
   flagged region also contains **IR blind spots**: rigid,
   refinement-resistant graphs (the Neuen–Schweitzer multipede family) with *no*
   symmetry at all. These are hard for the individualization-refinement
   *method* — chain descent included — yet almost certainly polynomial for graph
   isomorphism by other means (bounded degree ⇒ Luks). The algorithm flags them
   not because they are hard but because IR is incomplete on them, and no oracle
   of this design can fix it — there is no symmetry to consume. The honest claim
   is "flagged region ⊇ Tier 2 ∪ IR-blind-spots", not "= Tier 2". The two are
   distinguishable at flag time by the residual group order (§14): non-trivial ⇒
   Tier-2-like, trivial ⇒ IR blind spot.

   > **Endpoint statement (oracle-capability seal, 2026-05-31).** State the goal
   > as **two separate guarantees**, never one — the IR core has *no* symmetry, so
   > it must not be folded into the Tier-2 / Cameron case:
   > **(1) symmetry completeness** — *every symmetry is consumed by an oracle **or**
   > is a Cameron section* (residual non-trivial); **(2) polynomial time** — *poly
   > **unless** a Cameron section **or** an IR blind spot* (residual trivial). The
   > seal proves (1); the IR-core escape in (2) is orthogonal and is the slot for a
   > future Phase-2 blind-spot handler. See
   > [exhaustive-obstruction §0.6](./chain-descent-exhaustive-obstruction.md).

6. **Both-directions-dead error mode.** If both directions of a guess contradict
   on closure, neither branch produces a canonical form. The algorithm needs a
   defined error mode and, ideally, a structural argument that this cannot arise
   on connected graphs.

**"Canonizes every graph" is not a property of this design.** The claim is
"canonizes every graph it does not flag, in polynomial time." Closing the
flagged region — even with Babai's quasipolynomial method — is explicitly out of
scope.
