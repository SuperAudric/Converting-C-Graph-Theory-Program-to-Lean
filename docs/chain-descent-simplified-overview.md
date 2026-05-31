# Chain-descent canonizer — a simplified overview

A plain-language introduction to the project: what it computes, why the obvious
method is too slow, the one idea the design turns on, and how the pieces fit
together. It builds from nothing and is meant to be read first.

This is **not** a build spec — it deliberately stays at the level of ideas. Two
companion docs carry the detail:

- [`chain-descent-strategy.md`](./chain-descent-strategy.md) — the algorithm as
  a whole, and the requirements it must satisfy to be correct and (when it
  works) polynomial.
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) — the
  **oracle**, the hardest single component, specified on its own so it can be
  worked on directly.

The aim of this doc is that after reading it, those two read easily.

---

## 1. What we are computing

A **canonical form** of a graph `G`: a relabelling of its vertices chosen so
that two graphs get the *same* labelled adjacency matrix exactly when they are
isomorphic.

The standard recipe: among all `n!` ways to label the vertices `0..n-1`, write
down the adjacency matrix of each, and take the lexicographically smallest. That
smallest matrix is the canonical form. It is isomorphism-invariant for free —
relabelling the input does not change the *set* of `n!` matrices, so it does not
change their minimum.

Enumerating all `n!` labellings is too slow. Everything below is about computing
that minimum **without** enumerating them.

---

## 2. The search space: individualization-refinement

Instead of choosing a whole labelling at once, build it up.

**Cells.** *Color refinement* (1-WL) repeatedly recolors every vertex by the
multiset of its neighbors' colors, until colors stop changing. Vertices that end
up the same color form a **cell**. Refinement is cheap, deterministic, and
isomorphism-invariant: the cells, and their canonical numbering, depend only on
`G`'s structure, never on the input labelling. Refinement never makes a mistake
— but it is *incomplete*: it can leave vertices in the same cell that the graph
actually treats differently.

**When refinement is enough.** If every cell is a single vertex, the labelling
is fully determined (cell `#i` is vertex `#i`) — we have a **leaf**.

**Individualization.** If some cell `C` has ≥ 2 vertices, refinement is stuck.
Pick one vertex `v ∈ C`, *individualize* it — declare "`v` is the smallest
vertex of `C`" — and refine again. The new information about `v` often
propagates: `v`'s neighbors become distinguishable, then theirs, and so on.

**The IR tree.** We do not know which vertex of `C` to pick, so each choice is a
branch. Recursing on every choice builds the **individualization-refinement
tree**. Its leaves are full labellings; the canonical form is the lex-smallest
leaf matrix.

This is how nauty and similar tools work. **The catch:** the IR tree can be
exponentially large — nauty is provably exponential in the worst case
(Neuen–Schweitzer) on CFI-derived graphs.

---

## 3. The one idea that changes everything: true vs. false symmetry

Look again at a branch point — a cell `C` with several vertices to individualize.
There are exactly two situations:

**True symmetry.** The vertices of `C` are genuinely interchangeable: the graph
has an **automorphism** (a self-relabelling that preserves every edge) carrying
one to another. Then individualizing `v` or individualizing `w` leads to *the
same canonical form* — the two subtrees are mirror images. **You may pick any
one vertex, descend, and never look at the rest.**

**False symmetry — a genuine decision.** The vertices of `C` are genuinely
different: there is *no* automorphism carrying one to another, so different choices
give different canonicals and you genuinely have to compare them.

**The catch: refinement cannot tell these two apart.** Both present to 1-WL as the
same thing — a cell it cannot split. Call such a cell an **apparent decision**.
Deciding whether an apparent decision is *really* a true symmetry (prune) or
*really* a genuine decision (compare) is the oracle's whole job. And a true
symmetry can be **hidden**: in CFI graphs the branch points look like genuine
decisions but are actually true symmetries — gauge "twists" refinement is blind to.
Exposing those hidden true symmetries is what the linear oracle does (§7). So
"genuine decision," strictly, means *no automorphism exists* — and many apparent
decisions are not genuine.

If every branch were a true symmetry, canonization would be easy: descend one
vertex at each of ≤ `n` levels, never branching — polynomial. **Exponential
blow-up is apparent decisions piling up** — and the whole algorithm is organized
around cheaply telling a (possibly hidden) true symmetry from a genuine decision.

---

## 4. The algorithm: chain descent

Descend the IR tree — but at each cell, *before* branching, sort the cell's
vertices into **orbits** (maximal groups of genuinely-interchangeable vertices)
and branch on **one representative per orbit only**.

- Cell is one orbit (a true symmetry) → one representative → no branching, just
  descend.
- Cell is `k` orbits → `k` representatives → a `k`-way fork; canonize each
  branch, take the lex-min.

Three pieces make this work.

### 4.1 The oracle — the part that sorts a cell into orbits

The **oracle** is the component that, given a cell `C`, returns its partition
into orbits. It must obey one rule:

> **Soundness.** Never put two vertices in the same orbit without a *proof* — an
> actual automorphism, verified edge-by-edge, that maps one to the other.

Why this rule and not the reverse: if the oracle *splits* one true orbit into
two, the algorithm just branches once more than necessary — slower, still
correct. If the oracle *merges* two real orbits, it drops a representative — and
the dropped branch might have held the true minimum. So the oracle is allowed to
be over-cautious; it is never allowed to be over-confident.

The oracle does **bounded** work. When it can certify the orbits cheaply, the
descent continues. When it cannot, the algorithm **flags and stops** — it does
*not* fall back to brute force. A returned canonical form therefore always means
"computed cheaply"; a flag means "this graph needs a tool this oracle does not
have."

Discovering orbits cheaply is the hard problem — in full generality it is
equivalent to the open question GI ∈ P. The design does not solve it; it
**isolates** it behind one swappable interface. The oracle is the subject of its
own doc, [`chain-descent-calculator.md`](./chain-descent-calculator.md); the
first version ships a single oracle, for the *cascade* case (§6).

### 4.2 The budget — the hard ceiling

Many small forks at many levels could still multiply into an exponential tree.
So the descent carries a **polynomial node budget `B(n)`**. Every node of the
descent tree spends from it; when it is exhausted, the run flags.

The budget is what makes "polynomial or flag" a *guarantee* rather than a hope:
the algorithm physically cannot run longer than `B(n)`. A graph canonizes iff
its certified descent fits inside the budget.

### 4.3 The chain — the free byproduct

Every true-symmetry orbit comes with the automorphisms that witnessed it.
Stacked level by level as the recursion returns, these automorphisms generate
`Aut(G)`, the automorphism group — organized as a **stabilizer chain** (a base
of individualized vertices, plus, at each level, the orbit of that vertex). This
is expected: computing a canonical form, deciding isomorphism, and computing
`Aut(G)` are equivalent problems, so a canonizer produces the group for free.
The chain is also *useful mid-run*: an automorphism found deep in the tree, if
it fixes a shallow level's path, certifies orbits at that shallow level.

---

## 5. Worked example: a cycle

Take `C₆`, the 6-cycle `0–1–2–3–4–5–0`.

1. **Refine.** Every vertex has two same-colored neighbors; refinement never
   separates anyone. One cell, `{0,1,2,3,4,5}`.
2. **Target cell `{0..5}`.** The oracle checks: one orbit? Yes — the rotations
   of the cycle map any vertex to any other, and each rotation is a verified
   automorphism. **True symmetry.** Pick representative `0`, record the 6
   rotations as this level's transversal, descend into "`0` individualized".
3. **Refine again.** With `0` pinned, vertices split by distance from `0`:
   `{0}, {1,5}, {2,4}, {3}`.
4. **Target cell `{1,5}`.** Oracle: with `0` fixed, is `{1,5}` one orbit? Yes —
   the reflection of the cycle through `0` swaps `1` and `5` and fixes `0`;
   verified automorphism. **True symmetry.** Pick `1`, record the reflection,
   descend.
5. **Refine.** Now `{2,4}` splits too; everything is a singleton. **Leaf.** Read
   off the canonical matrix.

The descent was a **single path** — two levels, both true symmetries, no genuine
decision. The chain built: level 1 (base `0`, orbit size 6), level 2 (base `1`,
orbit size 2) ⇒ `|Aut(C₆)| = 6 × 2 = 12`, the dihedral group. Cost is two cheap
certified levels — polynomial, with nothing exponential anywhere.

**Contrast — a genuine decision.** In a *rigid* graph (no symmetry at all), the
oracle, after its bounded check, finds no automorphism and reports every cell
vertex as its own orbit. The descent then genuinely forks — but each leaf is
reached fast, the forks do not stack, and the budget holds. The graph canonizes,
by honest comparison, still polynomially.

**Contrast — a flag.** A graph that piles genuine decisions deep — e.g. CFI over
a large base — makes the descent tree grow; the budget runs out; the run
**flags**. No wrong answer, no exponential run: an honest "not handled."

---

## 6. Why it is polynomial when it works

Cost is a **sum, not a product**:

```
total work  =  Σ over the nodes of the descent tree ( oracle work at that node )
```

and the budget bounds the node count. The old design's cost was a *product* —
the size of a fully-explored tree — because it explored every branch and only
noticed redundancy afterwards. **Replacing the product with a sum is the entire
point of the rewrite.**

This sum is genuinely polynomial exactly when the oracle certifies every node
cheaply. The regime where it does:

- **Cascade.** Individualizing one vertex makes refinement collapse the graph
  quickly — subtrees stay shallow, so the oracle resolves each cell with a small
  bounded amount of work. Cycles, strongly regular graphs, Johnson graphs, and
  CFI over cycles all cascade. This is the first oracle's target.
- **Linear (CFI on richer bases).** The residual symmetry is elementary-abelian
  — generated by local involutions ("twists"). The apparent decisions it produces
  are hidden true symmetries, defused by discovering those twists from propagation
  patterns: the **linear oracle** (§7).

Three supporting facts, standard from computational group theory, keep the
*rest* of the accounting free: the chain is polynomial-size (you store
generators, not group elements); the descent has ≤ `n` levels; and — the only
open factor — the work per node is polynomial. That last one *is* the oracle.
The strategy and calculator docs name these facts T-A, T-B, T-C and treat them
properly; the point for now is that the design pins the whole difficulty to one
named component instead of smearing it across the algorithm.

---

## 7. The hidden-symmetry case: the linear oracle

§4's oracle handles true symmetries whose orbit refinement *exposes* — certify one
orbit, descend. This section is the other way a cell can be a true symmetry: the
symmetry is **hidden** from refinement. The cell looks like a genuine decision —
1-WL leaves a fork — but a verified automorphism shows the two branches are
equivalent. These hidden abelian symmetries are what make naive IR search
exponential on CFI graphs (each fork looks like a fresh decision); the linear
oracle defuses them by exposing the automorphism. It is *specified and built* (C#,
plus a Lean soundness contract) — the calculator and linear-oracle docs have the
full spec.

### 7.1 What a hidden-symmetry decision looks like

The simplest one: a target cell with two vertices `{e, f}` that 1-WL cannot
separate. Individualizing `e` means "`e < f`"; individualizing `f` means "`f < e`",
so the two branches are the two *directions* of one ordering decision. 1-WL cannot
tell whether the two directions are equivalent (a hidden symmetry) or genuinely
different (a real decision) — the linear oracle determines which.

### 7.2 Reverse-symmetric propagation

Refinement has a key property — **invariant 6.2**, stated and proved in
[`chain-descent-strategy.md`](./chain-descent-strategy.md): propagating `e < f`
and propagating `f < e` produce *the same partition of the vertices* (the same
cells split into the same sub-cells) and differ only in the *order labels* on
those splits.

So when branch-`e` propagates and splits a chain of further cells, branch-`f`
splits exactly the same cells, order reversed. Call that set of cells the
**coupled component**. Across it: partition shared, order mirrored.

### 7.3 Components are independent — the genuine "sum"

Such a decision propagates only as far as the constraints carry it; cells
outside its coupled component are untouched. Distinct coupled components
therefore do not interact — the canonical form decomposes
component-by-component, each solved on its own. Independent decisions resolve
**additively**. That is the §6 "sum, not product" made concrete, one level down:
applied to *decisions* rather than to disconnected pieces of the graph.

### 7.4 The mechanism: discover the twist, verify it, collapse

The shared-partition / reversed-order pattern does **not** by itself prove
branch-`e` ≅ branch-`f` — invariant 6.2 is a statement about the *partition*,
not about the labelled graph. What it gives is a **localized candidate**: a
concrete vertex-pairing over the coupled component — a candidate automorphism
`t` (a "twist"). The mechanism:

1. Explore branch-`e`, propagating; record the coupled component.
2. Read the candidate twist `t` off the reverse-symmetric pattern.
3. **Verify `t` is an automorphism of `G`, edge by edge.** Mandatory — this is
   what makes the step sound, since 6.2 alone does not give it.
4. A verified `t` certifies branch-`e` ≅ branch-`f`: branch-`f` is pruned
   *without being explored*. Being a global automorphism, `t` also collapses
   every other decision coupled to it.

Discover one twist per such decision — each from a *single* branch's
propagation, *before* any leaf — and the twists generate the residual group. The
descent collapses to a single path; for CFI, the `2^d` IR tree becomes a path of
length `d`.

This is why the linear oracle is part of the *search*, not a pre-pass: the
symmetry it needs is exactly the one refinement missed, so it cannot be found
until a branch is explored. The contrast with the pre-rewrite code is sharp —
that code discovered automorphisms only *after the fact*, from collisions
between completed leaves; this mechanism reads a generator off a single branch's
*intermediate* propagation, before any leaf. That is the whole difference
between polynomial and exponential here.

### 7.5 The boundary: where it stops working

Step 2 — reading a candidate off one branch's pattern — works only when that
pattern determines a **unique** candidate. That uniqueness is the boundary.

- **Unique candidate.** The symmetry resolving the decision is essentially one
  element: a single twist swaps `e` and `f`. One branch's pattern pins it;
  verify and consume. CFI's symmetry is many such decisions, each with a unique
  candidate — fully inside the boundary.
- **No unique candidate.** Many automorphisms resolve the decision — a large
  non-abelian action (the "hidden Johnson" case). One branch's pattern cannot
  single one out; constructing the generator would need cross-branch
  triangulation, which itself branches — exponential. The budget flags.

The line is the *size of the per-decision residual symmetry*: tiny and abelian →
consumed; large and non-abelian → flagged. This is the same boundary as Babai's
split-or-Johnson obstruction — the design's tractable/wall split landing there
is not a coincidence.

---

## 8. Why the answer is correct (when it returns one)

Two properties, both resting only on the oracle's soundness rule and on
refinement being isomorphism-invariant:

- **Isomorphism-invariance.** Cells and their canonical numbering are
  isomorphism-invariant; the target cell is chosen by canonical number; and the
  oracle is *required* to be isomorphism-invariant. So two labellings of the
  same graph produce the *same* descent tree, hence the same set of leaf
  matrices, hence the same minimum — and the same flag decision.
- **Completeness.** Because the oracle never merges two real orbits, its
  representatives hit every orbit of the target cell; the lex-min over
  representatives equals the lex-min over the whole cell. No labelling that could
  yield a smaller matrix is ever skipped. A leaf matrix determines the graph up
  to isomorphism, so equal canonical forms ⇔ isomorphic graphs.

Correctness is **independent of which oracle is plugged in** and independent of
the budget — exhausting the budget only ever causes a flag, never a wrong
answer. The strategy doc states these as formal requirements and what proving
them entails.

---

## 9. What is settled, and what is not

The design's honest claim is **not** "canonizes every graph." It is: *canonizes
every graph it does not flag, in polynomial time* — and the polynomial bound
itself is a target, not yet a theorem.

What is settled: the algorithm is correct (it returns an isomorphism-invariant,
complete canonical form, or an honest flag — never a wrong answer), and it is
budget-bounded (it can no longer run exponentially). What is not: whether the
oracle can certify orbits cheaply enough that graphs we *want* canonized fit
inside the budget rather than flagging. That is the open problem — equivalent in
full generality to GI ∈ P — and the design's contribution is to isolate it in
one component, not to close it.

Two places carry the precise list of what is incomplete or unproven:

- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 — algorithm-level
  gaps: the budget/soundness handshake, flag isomorphism-invariance, component
  combination, and the shape of the flagged region (which includes not only the
  genuine hard core but also rigid "IR blind spot" graphs that have no symmetry
  to consume).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §9 — the oracle
  gaps: the open per-node problem (T-C), the precise definition of "cascade", and
  general-class (Tier-2/3) completeness of the now-built oracles.

Read those two next; this overview was written to make them legible.
