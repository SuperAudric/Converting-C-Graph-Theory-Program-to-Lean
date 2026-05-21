# Chain-descent canonizer — how it works (theory)

A plain-language description of the rewritten calculator (the "chain-descent"
design from the implementation plan). It is the spec the rewrite implements and
the structure that correctness/complexity proofs will be written against.

Companion to [`flip-validation-strategy.md`](./flip-validation-strategy.md) and
[`flip-validation-calculator.md`](./flip-validation-calculator.md); it is
intended to become the basis of the calculator doc's rewrite. Where it conflicts
with those, this doc wins.

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

**False symmetry — a genuine decision.** The vertices of `C` merely *look* alike
to refinement; the graph really does treat them differently. Different choices
give different canonicals, and you genuinely have to compare them.

If every branch were a true symmetry, canonization would be easy: descend one
vertex at each of ≤ `n` levels, never branching — polynomial. **Exponential
blow-up is genuine decisions piling up.** The whole algorithm is organized around
telling the two apart cheaply.

---

## 4. The algorithm: chain descent

Descend the IR tree — but at each cell, *before* branching, sort the cell's
vertices into **orbits** (maximal groups of genuinely-interchangeable vertices)
and branch on **one representative per orbit only**.

- Cell is one orbit (a true symmetry) → one representative → no branching, just
  descend.
- Cell is `k` orbits → `k` representatives → a `k`-way fork; canonize each
  branch, take the lex-min. (The companion docs call this lex-leader descent.)

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

Discovering orbits cheaply is the hard problem — it is **T-C**, and in full
generality it is equivalent to the open problem GI ∈ P. The design does not
solve it; it **isolates** it behind one swappable interface. Phase 1 ships a
single oracle, for the *cascade* case (§6).

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

- **Cascade (Tier 1).** Individualizing one vertex makes refinement collapse the
  graph quickly — subtrees stay shallow, so the oracle resolves each cell with a
  small bounded amount of work. Cycles, strongly regular graphs, Johnson graphs,
  and CFI over cycles all cascade. This is the Phase-1 oracle's target.
- *(Future)* **Linear (CFI on richer bases).** The residual symmetry is a
  `Z₂`-vector space; orbits are a Gaussian-elimination computation. A second
  oracle, not yet written.

Three supporting facts, standard from computational group theory, keep the
*rest* of the accounting free:

- **T-A** — the chain and its transversals are polynomial-size (you store
  generators, never group elements).
- **T-B** — the descent has ≤ `n` levels (a base of a permutation group has
  ≤ `n` points).
- **T-C** — polynomial work per node. *This is the oracle, and the only open
  factor.*

T-A and T-B are citations. T-C is the research problem; the design's
contribution is to pin it to one named, swappable component instead of smearing
it across the whole algorithm.

---

## 7. Why the answer is correct (when it returns one)

Two properties, both resting only on the oracle's soundness rule and on
refinement being isomorphism-invariant:

- **Isomorphism-invariance.** Cells and their canonical numbering are
  isomorphism-invariant; the target cell is chosen by canonical number; and the
  oracle is *required* to be isomorphism-invariant — its output depends only on
  graph structure, never on the input labelling and never on the order branches
  happen to be visited. So two labellings of the same graph produce the *same*
  descent tree, hence the same set of leaf matrices, hence the same minimum —
  and the same flag decision.
- **Completeness.** Because the oracle never merges two real orbits, its
  representatives hit every orbit of the target cell; the lex-min over
  representatives equals the lex-min over the whole cell. No labelling that could
  yield a smaller matrix is ever skipped. A leaf matrix determines the graph up
  to isomorphism, so equal canonical forms ⇔ isomorphic graphs.

Correctness is **independent of which oracle is plugged in** and independent of
the budget — exhausting the budget only ever causes a flag, never a wrong
answer.

---

## 8. Gaps

Where the theory is incomplete, or load-bearing but unproven:

1. **The oracle is the open problem.** Sorting a cell into orbits cheaply, in
   general, is equivalent to GI ∈ P. The design isolates this; it does not close
   it. Every gap below is a consequence.

2. **"Cascade" is not yet precisely defined.** Refinement gives cells that are
   *supersets* of orbits; certifying that a cell *is* a single orbit needs more
   than refinement. The cascade oracle's exact certification predicate — what
   bounded check it runs, and what it guarantees — is undefined design work.
   This is the first thing to nail down: both the Tier-1 proof and the oracle's
   code depend on it.

3. **Tier 1 → polynomial is a target, not a theorem.** Even if every node
   certifies cheaply, genuine decisions could in principle still stack. The
   budget *catches* that — but by *flagging* a graph we wanted canonized.
   Whether genuinely-Tier-1 graphs fit a polynomial budget under the cascade
   oracle is the unproven Tier-1 theorem. The design makes it cleanly
   *targetable* (a per-node, inductive statement); it does not prove it.

4. **Budget / soundness interaction.** If the budget interrupts the oracle
   mid-certification, the oracle must flag — never return a partially-built,
   possibly-unsound orbit partition. The handshake between "out of budget" and
   "oracle soundness" must be specified so a flag can never be silently
   downgraded to a wrong answer.

5. **The flag must be isomorphism-invariant.** §7 *requires* the oracle (and all
   pruning) to be fully order-invariant, including timing, so node counts —
   hence "exceeds `B(n)`" — do not depend on the input labelling. The old
   a-posteriori pruning was result-invariant but timing-dependent. The new
   oracle must be invariant by construction; this is a proof obligation, not an
   automatic property.

6. **No linear/abelian oracle.** Phase 1 ships only the cascade oracle, so CFI
   over non-cascading bases flags until a Gaussian-elimination oracle is
   written. A known scope limit, not a surprise.

7. **Tier 2 is flagged, not solved.** When a cell genuinely resists
   certification (no cascade, non-abelian symmetry), the design flags. It does
   not canonize such graphs. Closing that — even with Babai's quasipolynomial
   method — is explicitly out of scope. "Canonizes every graph" is *not* a
   property of this design; the claim is "canonizes every graph it does not
   flag, in polynomial time."

8. **Component combination (Tier 0).** Disjoint graphs are split into
   components, each canonized, then reassembled in a sorted order. The sort key
   being a *complete* invariant across all vertex-type regimes is assumed, not
   proven — a small pre-existing gap inherited from the current code.
