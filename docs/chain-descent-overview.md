# Chain-descent canonizer — how it works (theory)

A plain-language description of the rewritten calculator (the "chain-descent"
design from the implementation plan). It is the spec the rewrite implements and
the structure that correctness/complexity proofs will be written against.

This is the current, authoritative design doc.
[`chain-descent-strategy.md`](./chain-descent-strategy.md) and
[`chain-descent-calculator.md`](./chain-descent-calculator.md) are earlier-
generation companions — superseded, retained for lineage and for detail this
doc summarizes (notably invariant 6.2, which §7 depends on). Where they
conflict with this doc, this doc wins.

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
- **Linear (CFI on richer bases).** The residual symmetry is elementary-abelian
  — generated by local involutions ("twists"). The genuine decisions it produces
  are defused by discovering those twists from propagation patterns: the
  **linear oracle**, specified in §7. Not yet implemented.

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

## 7. The genuine-decision case: the linear oracle

§4's oracle handles **true-symmetry** cells — certify one orbit, descend. This
section is the other case: a **genuine decision**, a cell that splits into
`k ≥ 2` orbits. Genuine decisions are what make naive IR search exponential on
CFI graphs; this is the mechanism that defuses them for the abelian case.

### 7.1 What a genuine decision looks like

The simplest one: a target cell with two vertices `{e, f}` that 1-WL cannot
separate but that the graph treats differently given the path already fixed.
Individualizing `e` means "`e < f`"; individualizing `f` means "`f < e`". So the
two branches are the two *directions* of one ordering decision.

### 7.2 Reverse-symmetric propagation

Warm refinement has a key property — **invariant 6.2** of
[`chain-descent-strategy.md`](./chain-descent-strategy.md): propagating
`e < f` and propagating `f < e` produce *the same partition of the vertices*
(the same cells split into the same sub-cells) and differ only in the *order
labels* on those splits.

So when branch-`e` propagates and splits a chain of further cells, branch-`f`
splits exactly the same cells, order reversed. Call that set of cells the
**coupled component**. Across it: partition shared, order mirrored.

### 7.3 Components are independent — the genuine "sum"

A genuine decision propagates only as far as the constraints carry it; cells
outside its coupled component are untouched. Distinct coupled components
therefore do not interact — the canonical form decomposes
component-by-component, each solved on its own. Independent decisions resolve
**additively**. That is the §6 "sum, not product" made concrete: the Tier-0
component-decomposition argument applied one level down, to *decisions* rather
than *connected components*. (The coupled component is generally large — its
dimension is the cycle rank of the constraint structure — not a single partner
cell.)

### 7.4 The mechanism: discover the twist, verify it, collapse

The shared-partition / reversed-order pattern of §7.2 does **not** by itself
prove branch-`e` ≅ branch-`f` — 6.2 is a statement about the *partition*, not
about the labelled graph. What it gives is a **localized candidate**: a concrete
vertex-pairing over the coupled component — a candidate automorphism `t` (a
"twist"). The mechanism:

1. Explore branch-`e`, propagating; record the coupled component.
2. Read the candidate twist `t` off the reverse-symmetric pattern.
3. **Verify `t` is an automorphism of `G`, edge by edge.** Mandatory — this is
   what makes the step sound, since 6.2 alone does not give it.
4. A verified `t` certifies branch-`e` ≅ branch-`f`: branch-`f` is pruned
   *without being explored*. Being a global automorphism, `t` also collapses
   every other decision coupled to it.

Discover one twist per genuine decision — each from a *single* branch's
propagation, *before* any leaf — and the twists generate the residual group.
Orbit pruning with that group turns every coupled decision into a `k = 1` step,
and the descent collapses to a **single path**. For CFI, the `2^d` IR tree
becomes a path of length `d`, each node `O(n²)`.

### 7.5 Why this is the oracle, not a pre-pass

§4 described the oracle as if it sorted a cell into orbits *before* branching.
The linear oracle cannot work that way — the symmetry it needs is exactly the
one refinement *missed*. It is **online**: it explores a branch, and that
branch's own propagation pattern either yields a verified generator (→ consume
the symmetry, collapse) or does not (→ a real branch). The oracle and the search
are one process. The budget bounds their combined work; a generator that never
gets discovered surfaces as budget exhaustion — a flag.

The contrast with the pre-rewrite code: it discovered automorphisms only *a
posteriori*, from collisions between completed leaves. This mechanism reads a
generator off a single branch's *intermediate* propagation — before the leaves.
That is the whole difference between polynomial and exponential here.

### 7.6 The boundary: where it stops working

Step 2 — reading a candidate off one branch's pattern — works only when that
pattern determines a **unique** candidate. That uniqueness is the boundary.

- **Unique candidate.** The symmetry resolving the decision is essentially one
  element — `Z₂`: a single non-identity twist swaps `e` and `f` within the
  coupled component. One branch's pattern pins it; verify and consume. CFI's
  `Z₂^d` is `d` such decisions, each with a unique candidate — fully inside the
  boundary.
- **No unique candidate.** Many automorphisms resolve the decision — a large
  non-abelian action (`A_k` on the cell: the "hidden Johnson" case). One
  branch's pattern cannot single one out; constructing the generator would need
  cross-branch triangulation, which itself branches — exponential. The budget
  flags.

The line is the *size of the per-decision residual symmetry*: tiny and abelian
→ consumed; large and non-abelian → flagged. This is the same boundary as
Babai's split-or-Johnson obstruction — the design's tractable/wall split landing
there is not a coincidence.

### 7.7 What the linear oracle requires

- **State.** A descent node must carry not just `P` but a **provenance record**
  — which guess forced which derived relation — so the coupled component can be
  delineated and the candidate twist built. This is the
  `DERIVED`-record-with-driver structure of strategy-doc §6.4.
- **Invariant 6.2**, including across transitive closure, so §7.2's
  partition-sharing is rigorous. Its load-bearing core is a *direction-symmetric
  split* lemma — a guess splits a cell into the **same sub-cells** under either
  direction. Note this is **not** the lemma originally named `cell_split_uniform`
  in `ChainDescent.lean`: that lemma (cell-mates keep *equal* signatures — i.e.
  no split at all) is machine-checked **false** there. 6.2 needs the genuine,
  weaker split-symmetry statement, still unproven (`warm_6_2` is `sorry`).
- **Cheap candidate construction** (step 2) — turning a propagation pattern into
  a vertex permutation — is the one genuinely unspecified piece and the main
  implementation risk.

---

## 8. Why the answer is correct (when it returns one)

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

## 9. Gaps

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

5. **The flag must be isomorphism-invariant.** §8 *requires* the oracle (and all
   pruning) to be fully order-invariant, including timing, so node counts —
   hence "exceeds `B(n)`" — do not depend on the input labelling. This is
   sharper now that the linear oracle (§7) is *online*: its branch-traversal and
   twist-discovery must be a deterministic function of iso-invariant cell ids,
   or the node count varies with labelling. The pre-rewrite a-posteriori pruning
   was result-invariant but timing-dependent. Invariance must hold by
   construction; it is a proof obligation.

6. **The linear oracle is specified but not built.** §7 specifies it; Phase 1
   still ships only the cascade oracle, so CFI over non-cascading bases flags
   until the linear oracle is implemented. Its open piece is cheap
   candidate-twist construction (§7.7) — the rest of §7 is a spec, not yet code.

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

9. **The flagged region exceeds Tier 2.** Tier 2 (no cascade + a non-abelian
   `A_k` automorphism factor) is the genuine hard core, aligned with Babai's
   split-or-Johnson obstruction — flagging it is honest hardness. But the
   flagged region also contains **IR blind spots**: rigid, refinement-resistant
   graphs (the Neuen–Schweitzer multipede family) with *no* symmetry at all.
   These are hard for the individualization-refinement *method* — chain descent
   included — yet almost certainly polynomial for graph isomorphism by other
   means (bounded degree ⇒ Luks). The algorithm flags them not because they are
   hard but because IR is incomplete on them, and no oracle of this design can
   fix it — there is no symmetry to consume. So the honest claim is "flagged
   region ⊇ Tier 2 ∪ IR-blind-spots", not "= Tier 2". The two are
   distinguishable at flag time by the residual group order: non-trivial ⇒
   Tier-2-like, trivial ⇒ IR blind spot.
