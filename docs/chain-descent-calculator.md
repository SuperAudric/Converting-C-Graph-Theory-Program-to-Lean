# Chain-descent calculator — the oracle

The chain-descent canonizer descends the individualization-refinement tree, and
at every branch node it calls one component to decide which vertices to branch
on. That component is the **calculator** — equivalently, the **oracle**. It is
the most complicated part of the algorithm and the only part whose polynomial
bound is open, so it gets its own doc, to be worked on directly.

This doc is the oracle's spec: the stabilizer-chain model, the hardness map, the
T-A/T-B/T-C decomposition, the two concrete oracles (cascade and linear), and
the construction question. For the algorithm that *calls* the oracle — the
descent, the budget, what the algorithm requires *of* the oracle — see
[`chain-descent-strategy.md`](./chain-descent-strategy.md). For a gentle
introduction to the whole project, start with
[`chain-descent-simplified-overview.md`](./chain-descent-simplified-overview.md).

---

## 1. What the calculator is, and what it isn't

The calculator is not a general-purpose canonization algorithm. Its scope is one
operation, invoked once per branch node of the descent:

> Given a **target cell** `C` (a group of vertices 1-WL cannot tell apart),
> return its partition into **orbits** — maximal groups of genuinely
> interchangeable vertices — so the descent can branch on one representative per
> orbit instead of on every vertex.

The honest framing: **the calculator's polynomial bound is equivalent in
strength to GI ∈ P.** Computing a generating set of `Aut(G)`, deciding graph
isomorphism, and computing a canonical form are all polynomial-time equivalent;
a polynomial calculator for arbitrary graphs would resolve a famous open
problem. The project's bet is that the *specific structured input* the descent
produces — a refined cell together with the individualization path that reached
it — may admit a polynomial procedure where free-form canonization does not.
That bet is unproven, and this doc marks exactly where it is load-bearing.

The design does not *solve* this hard problem; it **isolates** it behind one
swappable interface, the `ITransversalOracle` seam. Everything else in the
canonizer is correct and polynomial-or-flag regardless of which oracle is
plugged in (see [`chain-descent-strategy.md`](./chain-descent-strategy.md) §5,
the oracle interface, and §7, correctness).

---

## 2. The model: the calculator is a stabilizer chain

**The canonical form is an orbit-minimum.** It is `min` over the `S_n`-orbit of
the graph. Orbit-minima need the orbit's *generating structure* — a group. Every
boolean class the project tried (AND-of-XOR, Horn, monotone — see §10.2) is a
*constraint* language: it describes sets of satisfying assignments. None is an
*orbit* language. That mismatch — not a wrong variable basis, not a fixable
detail — is why the boolean approach failed structurally.

So the calculator's object is **the residual symmetry, represented as a
permutation group** — concretely a *stabilizer chain*: a base of individualized
points, plus a transversal of coset representatives at each level. The
calculator's operation is **lex-leader descent**: walk the chain, and at each
level pick the transversal element that yields the lex-min canonical prefix,
then descend.

Consequences that fall straight out of this model:

- **True symmetries are transversal elements / generators.** When the descent
  finds that branching on `v` lands in an `Aut`-equivalent world to branching on
  `w`, that equivalence is an element of the residual group. Base + transversals
  generate `Aut(G)` (standard). The true-symmetry detections are not noise to
  discard — they are the generating set, the **chain** the descent builds as a
  byproduct.
- **False symmetries are the genuine decisions** — the points where lex-leader
  must actually compare canonicals.
- **The per-level transversal is the orbit of that level's base point.** Sorting
  the target cell into orbits (§1) and discovering a chain level's transversal
  are the same operation.
- **XOR was the abelian special case.** Gaussian elimination over `Z₂` is
  exactly Schreier–Sims specialised to elementary-abelian groups. CFI's gadget
  group *is* `Z₂ᵐ`. That is why XOR "almost worked" on CFI and nothing else: the
  project had found the abelian corner of the group model. The generalisation
  from `Z₂`-linear to general permutation groups is the move from Gaussian
  elimination to computational group theory. The **linear oracle** (§6) is that
  abelian corner, done properly.

---

## 3. The hardness map: cascade, factors, and the single hurdle

### Two axes

Canonization hardness has two independent axes:

1. **Cascade** — after individualising a vertex and running refinement, does
   refinement reach *single-orbit* cells? Equivalently: does local
   individualization propagate globally?
2. **Composition factors** of the residual group.

### Three cases

- **Cascade → polynomial, regardless of the group.** Refinement reaches
  single-orbit cells, so every branch is a true symmetry, the chain's
  transversals shrink, and lex-leader descent is a *sum* of polynomial-size
  transversals (not a product). Cycles, strongly regular graphs, C4+K2, **and
  all Johnson graphs** live here.
- **No cascade + abelian factors** (CFI: `Z₂ᵐ`) **→ polynomial** via linear
  algebra. The residual symmetry is elementary-abelian — generated by local
  involutions ("twists"). This is the **linear oracle**'s regime (§6).
- **No cascade + a non-abelian factor → the genuine wall.** The factor is a
  **Cameron section** — an `Aₖ`-on-`k`-subsets (Johnson) group is the leading
  `d=1` case, but product actions (`Aₖ^d`, non-Johnson) belong here too, so the
  honest name for the class is *Cameron*, not *Johnson*.
  Quasipolynomial (Babai, `2^O(log³n)`); polynomial is open (≡ GI ∈ P).
  Two claims hide under "the wall" and must be kept apart (see
  [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
  §0): whether such an obstruction *ever arises* (the existence/construction
  question, ≡ GI ∈ P, excluded) versus *classifying* one that does arise as a
  Cameron section (Cameron-hard, **not** GI-hard — a finite target).

### Tiers

- **Tier 0 — disjoint / decomposable.** `Aut(G₁ ⊔ … ⊔ G_c) = (∏ Aut(Gᵢ)) ⋊ S_c`.
  Components are independent; the stabilizer chain factors; cost is linear in the
  number of components. The fix for the old code's superpolynomial blowup on
  disjoint CFI — it ran the descent over the whole union and manufactured
  coupling that isn't there — is component decomposition, done in
  `CanonGraphOrdererChainDescent.cs` before the harness is invoked.
- **Tier 1 — 1-WL deficiency, cascade resolves.** 1-WL is blind initially
  (vertex-transitive / strongly regular), but individualization + refinement
  cascades. C4+K2 #56, CFI(Cycle3), Johnson graphs, triangular graphs. This is
  the cascade oracle's target (§5).
- **Tier 2 — the wall.** No cascade and a non-abelian-simple factor. Not
  exercised by any instance currently in the test bed (see §7).

### The single hurdle

Everything reduces to one operation:

> Given a node in the individualization tree (a partial individualization),
> determine **in polynomial time which child leads to the lexicographically
> smallest canonical — without recursively canonizing each child.**

If this is polynomial, you descend one root-to-leaf path (≤ `n` levels, ≤ `n`
children each, polynomial evaluation) → polynomial → GI ∈ P. Storage of the
group is free (T-A/T-B, §4). Discovering generators, the size of the IR tree,
local-vs-global generators — all either dissolve or reduce to this one
operation.

Inside the stabilizer-chain model, the hurdle has a precise home: **discover
each level's transversal** — the orbit of the level's base point, i.e. the new
coset representatives. This is polynomial when refinement exposes the orbit
(cascade / Tier 1) or the coupling is linear (CFI); it is the wall otherwise.

---

## 4. The theorems the bound rests on: T-A, T-B, T-C

Three structural theorems are what the calculator's polynomial bound rests on.
The calculator does lex-leader descent down the stabilizer chain; its cost is,
schematically:

```
   total  =  (number of chain levels)
           × (transversal size at each level)
           × (work to discover that level's transversal and lex-select it)
```

For the total to be polynomial, **each of the three factors must be
polynomial** — and each theorem pins exactly one:

- **T-A** bounds the *representation* — each level's transversal, and the chain
  as a whole, are polynomial-size.
- **T-B** bounds the *number of levels*.
- **T-C** bounds the *work per level*.

Drop any one and the bound collapses. The payoff of the stabilizer-chain model
is that **T-A and T-B become free citations**, isolating the entire difficulty
in T-C.

### T-A — polynomial-size representation (free)

> Each chain level's transversal, and the stabilizer chain as a whole, are
> polynomial-size.

A theorem of computational group theory (Sims): every subgroup of `S_n` —
**whatever its order, up to `n!`** — has a base of `≤ n` points and a strong
generating set of `O(n²)` elements. You never store group *elements*; you store
*generators*. `S_s` acting on `s` points is 2 generators, not `s!` stored
objects.

### T-B — polynomially many levels (free)

> The stabilizer chain has polynomially many levels.

A base of a subgroup of `S_n` has `≤ n` points, so the chain has `≤ n` levels;
the genuine decisions (false symmetries) are a subset of those. A citation, not
a conjecture.

### T-C — polynomial work per level (the single hurdle)

> Each level's transversal can be *discovered* and *lex-leader-selected* in
> polynomial time.

This is the load-bearing claim, and it is exactly the single hurdle of §3. It is
polynomial on the easy side (cascade / abelian / bounded-width) and the open
problem otherwise. The asymmetry that pins the difficulty: **Schreier–Sims
builds the whole chain in polynomial time *given a generating set*** — so the
chain *machinery* is not the problem. T-C is entirely the *missing input*:
discovering each level's transversal — the new coset representatives — when
refinement does not expose it for free.

The two concrete oracles below are the two cases where T-C is tractable: §5
(cascade) and §6 (abelian / linear).

---

## 5. The cascade oracle (Phase 1)

The cascade oracle handles **true-symmetry** target cells — the cell is a single
orbit, and the only job is to certify that and descend on one representative.

A cell *cascades* when individualising one of its vertices makes refinement
collapse the graph quickly — subtrees stay shallow, so the residual symmetry is
resolved with a small bounded amount of work. Cycles, strongly regular graphs,
Johnson graphs, and CFI over cycles all cascade. This is Tier 1.

**Phase-1 status.** The shipped `CascadeOracle` certifies *nothing a priori*:
`Classify` returns every vertex of the target cell. The real orbit pruning is
done a posteriori by the harness — `ChainDescent` skips a candidate once a
harvested, edge-verified automorphism shows it redundant. Together, harness
search + this oracle behave as a budget-bounded IR search: they finish within
the node budget exactly on graphs that cascade, and flag otherwise.

This is honest but not the final form. A genuine cascade oracle would run a
**bounded certification check** *before* branching and return one representative
per certified orbit directly. Its exact certification predicate — what bounded
check it runs, and what it guarantees — was undefined design work (§9); it is now
specified in [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
as the linear oracle's verified-footprint-map harvest wrapped in a bounded-depth
recursion (depth ≤ `tw(H)` for CFI, 1 for schemes, via the orbit-recovery
theorems). The a-priori cascade oracle became the binding constraint once the
linear oracle was built and measured *starved* (2026-05-28) — 100% of CFI(K7)
residual branching sat at non-singleton footprints the recursion would resolve.
It was then **built (M1+M2, 2026-05-28)** as a lockstep per-rep single-path
recursion and **resolved that starvation**: CFI(K7) collapsed 941 → 1 leaf,
555 → 0 branching nodes, recursion depth ≈ `tw(H)` (correct + scramble-invariant
through K7). The Tier-1 polynomial proof now has its constructive code; the
remaining gap is the Lean discharge of the certification predicate.

The boundary of the cascade oracle is also the boundary of "cell *is* a single
orbit" being cheaply certifiable. When the cell is **not** a visibly single orbit —
an apparent decision — §6 takes over.

---

## 6. The linear oracle (the hidden-abelian-symmetry case)

The cascade oracle (§5) handles true symmetries refinement makes *visible* as a
single-orbit cell. This section is the other way a cell can be a true symmetry: an
**apparent decision** — a target cell 1-WL cannot split — whose two branches turn
out to be related by a *hidden* abelian automorphism (a CFI gauge "twist"). These
hidden symmetries are what make naive IR search exponential on CFI graphs (each
fork looks like a fresh decision); the linear oracle is the mechanism that defuses
them, by exposing and verifying the twist. A genuine decision proper — *no*
automorphism — is resolved by neither oracle (exhaustive branching). It is
**specified here and built** (C#, and a Lean soundness contract) — see
[`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §8 and
§9 item 4 below.

> The consolidated spec + design — including the precise candidate-twist
> construction predicate, the uniqueness test (the abelian/wall boundary), the
> verification protocol, and the implementation plan — is in
> [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md). This
> section is the prose overview that doc makes precise.

### What an apparent decision looks like

The simplest apparent decision: a target cell with two vertices `{e, f}` that
1-WL cannot separate. Individualizing `e` means "`e < f`"; individualizing `f`
means "`f < e`", so the two branches are the two *directions* of one ordering
decision. 1-WL cannot tell whether the two directions are equivalent (a hidden
symmetry the oracle can expose) or genuinely different (a real decision).

### Reverse-symmetric propagation

Warm refinement has a key property — **invariant 6.2** of
[`chain-descent-strategy.md`](./chain-descent-strategy.md): propagating `e < f`
and propagating `f < e` produce *the same partition of the vertices* (the same
cells split into the same sub-cells) and differ only in the *order labels* on
those splits.

So when branch-`e` propagates and splits a chain of further cells, branch-`f`
splits exactly the same cells, order reversed. Call that set of cells the
**coupled component**. Across it: partition shared, order mirrored. The coupled
component is generally large — its dimension is the cycle rank of the constraint
structure — not a single partner cell.

### Coupled components are independent — the genuine "sum"

Such a decision propagates only as far as the constraints carry it; cells
outside its coupled component are untouched. Distinct coupled components
therefore do not interact — the canonical form decomposes
component-by-component, each solved on its own. Independent decisions resolve
**additively**: that is the §3 "sum, not product" made concrete — the Tier-0
component-decomposition argument applied one level down, to *decisions* rather
than *connected components*.

### The mechanism: discover the twist, verify it, collapse

The shared-partition / reversed-order pattern does **not** by itself prove
branch-`e` ≅ branch-`f` — invariant 6.2 is a statement about the *partition*,
not about the labelled graph. What it gives is a **localized candidate**: a
concrete vertex-pairing over the coupled component — a candidate automorphism
`t` (a "twist"). The mechanism:

1. Explore branch-`e`, propagating; record the coupled component.
2. Read the candidate twist `t` off the reverse-symmetric pattern.
3. **Verify `t` is an automorphism of `G`, edge by edge.** Mandatory — this is
   what makes the step sound, since invariant 6.2 alone does not give it.
4. A verified `t` certifies branch-`e` ≅ branch-`f`: branch-`f` is pruned
   *without being explored*. Being a global automorphism, `t` also collapses
   every other decision coupled to it.

Discover one twist per such decision — each from a *single* branch's
propagation, *before* any leaf — and the twists generate the residual group.
Orbit pruning with that group turns every coupled decision into a `k = 1` step,
and the descent collapses to a **single path**. For CFI, the `2^d` IR tree
becomes a path of length `d`, each node `O(n²)`.

### Why this is the oracle, not a pre-pass

The cascade oracle sorts a cell into orbits *before* branching. The linear
oracle cannot work that way — the symmetry it needs is exactly the one
refinement *missed*. It is **online**: it explores a branch, and that branch's
own propagation pattern either yields a verified generator (→ consume the
symmetry, collapse) or does not (→ a real branch). The oracle and the search are
one process. The budget bounds their combined work; a generator that never gets
discovered surfaces as budget exhaustion — a flag.

The contrast with the pre-rewrite code: it discovered automorphisms only *a
posteriori*, from collisions between completed leaves. This mechanism reads a
generator off a single branch's *intermediate* propagation — before the leaves.
That is the whole difference between polynomial and exponential here.

### The boundary: where it stops working

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

The line is the *size of the per-decision residual symmetry*: tiny and abelian →
consumed; large and non-abelian → flagged. This is the same boundary as Babai's
split-or-Johnson obstruction — the design's tractable/wall split landing there
is not a coincidence. The flagged side is a **Cameron section** (Johnson is the
`d=1` instance); *classifying* the flagged residual as such is the
Exhaustive-Obstruction Lemma
([`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)),
which is Cameron-hard but **not** GI-hard — distinct from the GI-hard question of
whether the flagged case arises at all.

### What the linear oracle requires

- **State.** A descent node must let the oracle delineate the coupled
  component and build the candidate twist. The mechanism is the **refinement
  footprint** — the parent↔child partition diff (the cells that split when the
  representative is individualized). *Correction (2026-05-28):* an earlier
  version named the `DERIVED`-record-with-driver TC provenance of
  [`chain-descent-strategy.md`](./chain-descent-strategy.md) §10 as the required
  state. That TC provenance is **inert** for the within-cell cascade the linear
  oracle targets (under relegated TC there is no in-loop closure; in the
  implementation a within-cell decision on a uniform-type graph chains nothing —
  measured zero). The cascade propagates by **refinement**, so the footprint is
  read from the partition diff. TC provenance stays meaningful only for
  between-cell ordering guesses, off the oracle's critical path. Full treatment:
  [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §3.
- **Invariant 6.2** — so the partition-sharing above is rigorous. Its
  load-bearing core is a *direction-symmetric split* lemma: a guess splits a cell
  into the **same sub-cells** under either direction. This is `warm_6_2` in
  [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean), **proved**
  — under the relegated-TC model (a guess writes one `P` entry, no transitive
  closure in the refinement loop) with fresh-colour individualisation. See the
  strategy doc's invariant-6.2 section for the full statement and Lean status.
  Generalised by the **descent spine** (`warmRefine_agree_off`, proved): all
  `2^d` leaves of a `d`-decision subtree share *one* partition, so the linear
  oracle is handed a single fixed partition with a clean `Z₂^d`
  label-optimisation rather than `2^d` distinct refinement worlds — see
  [`chain-descent-strategy.md`](./chain-descent-strategy.md) §12.
- **Cheap candidate construction** (step 2) — turning a propagation pattern into
  a vertex permutation — is the one genuinely unspecified piece and the main
  implementation risk (§9).

---

## 7. The construction question: is the wall reachable?

> **Existence vs. classification (read once).** This section is about
> *(O\*)-existence* — does a Tier-2 obstruction ever arise from the descent? —
> which is the wall, equivalent in strength to GI ∈ P, and the thing the project
> deliberately routes around. It is **not** the same question as *classifying* an
> obstruction that does arise as a Cameron section (the Exhaustive-Obstruction
> Lemma, [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)),
> which is Cameron-hard but not GI-hard. "Prove the wall is never reached" is
> GI ∈ P; "if reached it is a named, flaggable Cameron section" is a finite
> target. Keep them apart.

Tier 2 is the only thing standing between the project and a polynomial bound. A
natural strategy: instead of solving it, prove it never arises from the descent.
Progress so far:

- **CFI applied to a Johnson base**, and **a Johnson graph with each vertex
  replaced by a CFI graph**, both produce
  `(Z₂ᵐ, refinement-resistant) ⋊ (S_n, cascading)` — a *decomposable*
  semidirect product. You resolve the cascading `S_n` layer first (it does not
  depend on the parity), and the `Z₂ᵐ` layer is then a plain linear system. Two
  polynomial tools, one per factor. **Neither is Tier 2.**
- **Near-theorem:** if `Aut(G)` *is* a Johnson group, then `G`'s edge set is
  `S_k`-invariant, hence a union of Johnson-association-scheme classes, hence `G`
  is a scheme graph — and refinement computes the scheme, so individualization
  cascades. **You cannot hide a Johnson group as the full automorphism group of
  a graph.** Rigorous treatment in
  [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md): the
  edges-are-a-scheme half (Pieces A, B) is proved, the cascade half (Piece C) is
  scoped, and the doc delimits what this does *not* cover — only the *visible*
  Johnson is ruled out, not the encoded (CFI-style) one.
- **Matroid framing of the propagation closure** — **CLOSED 2026-05-23**;
  full record in [`chain-descent-matroid.md`](./Archive/ChainDescent/chain-descent-matroid.md).
  Both partition-based `cl` and TC-based `cl_prov` tested; neither satisfies
  the matroid exchange axiom. `cl_prov` IS a topological closure (CL0–CL3 hold)
  but matroid M3 refuted via machine-checked `decide`. The binary-closure
  conjecture as originally framed is not provable through this route.
- **Tier-2 structure-tree decomposition** — **CLOSED 2026-05-26**; record in
  [`chain-descent-tier2-decomposition-experiment.md`](./Archive/ChainDescent/chain-descent-tier2-decomposition-experiment.md).
  Empirically confirmed that the CFI ladder (C₃, K₄, Petersen) is all
  Tier-1, not Tier-2 — restating the decomposability claim of this section.
  The experiment surfaced F7 (1-WL recovers Aut_v orbits at depth 1 for
  many CFI bases), which spun off the orbit-recovery program.
- **Orbit-recovery for CFI** — active, see
  [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md).
  Theorem 1: for CFI(H), 1-WL after ≤ tw(H) fresh-colour individualizations
  recovers Aut_S orbits. Proof via classical CFI cascade. Delivers
  polynomial T-C for CFI with bounded tw(H) (the "Corollary 1" of that doc).
  Tier-2 (association schemes) sketched as next paper target.
- **CFI is a `Z₂`-hiding gadget.** No `Aₖ`-hiding gadget is known. Hiding a
  non-abelian simple group requires *fusing* refinement-resistance with
  non-abelianness in one non-decomposable obstruction; layered products
  decompose. This asymmetry is real, and it is part of why GI stayed open and
  why Babai works in the abstract String-Isomorphism setting rather than with a
  clean graph family.
- **Detection is not free.** "The descent detects every automorphism, so nothing
  can be hidden" assumes its conclusion: detecting all of `Aut(G)` in polynomial
  time *is* GI ∈ P. The descent detects automorphisms cheaply only when
  refinement *verifies* them. A hidden Johnson is exactly the case where
  verification is GI-hard.
- **Higher-WL lever.** The descent uses 1-WL. A `k`-WL refinement makes
  Johnson-*scheme* cells cascade (Johnson schemes have bounded WL-dimension),
  widening Tier 1. It does **not** cross the true wall, which has unbounded
  WL-dimension.

**Bottom line:** no clean hidden-Johnson graph construction is known — weak
positive evidence that Tier 2 may not arise from the descent. But "no known
construction" ≠ "impossible," and Babai needs the quasipolynomial branch, so it
arises *somewhere*. The proof target is: show every obstruction the descent
produces decomposes as `(resistant-abelian) ⋊ (cascading)`. A counterexample
would be the first clean hidden-Johnson graph.

A paper-first plan for this proof target is sketched in
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md),
which decomposes it into three sub-claims (abelian-stripping, residual
cascade, layered composition) and records a sibling visibility / no-hidden-
symmetry framing for inversion arguments.

---

## 8. Implementation

The calculator is implemented as the oracle seam of the **chain-descent
harness**. The algorithm that drives it is specified in
[`chain-descent-strategy.md`](./chain-descent-strategy.md); this doc is the
oracle's design detail. The code:

- **`ITransversalOracle.cs`** — the **T-C seam**. At a branch node the oracle's
  `Classify` says which target-cell vertices to descend into (a
  `TransversalDecision`). Swapping the oracle swaps the calculator; correctness
  and the budget bound hold for any oracle (strategy doc §"Correctness").
- **`CascadeOracle.cs`** — the Phase-1 oracle (§5). Certifies nothing a priori,
  so the harness behaves as a budget-bounded IR search.
- **`ChainDescent.cs`** — the harness: a recursive descent of the
  individualization-refinement tree carrying a polynomial node **budget**. A run
  that exceeds the budget **flags** (`CanonizationFlaggedException`) instead of
  continuing — an honest "not handled", never a wrong answer. Automorphisms are
  harvested from coinciding leaves into a `PermutationGroup`; both the oracle and
  the a-posteriori pruning consume it.
- **`CanonGraphOrdererChainDescent.cs`** — Tier-0 component decomposition plus
  dispatch to the harness.
- **`PermutationGroup.cs`** — `Perm` algebra + Schreier–Sims chain; the concrete
  stabilizer chain. Verified on S₃–S₇, D₄, D18 = Aut(C18), and
  D9≀Z2 = Aut(C9⊔C9).

**Status.** The implementation is **correct** (scramble-invariant + complete)
and **budget-bounded** (polynomial-or-flag — it can no longer run
exponentially). It is **not proven polynomial**: that is T-C. The open
follow-ons:

- the **linear oracle** (§6) — a-priori transversal certification for the
  no-cascade-abelian (CFI) case; the second `ITransversalOracle` implementation;
- the **Tier-1 polynomial proof** — T-C for the cascade class, which would pin
  the budget `B(n)`;
- the **Johnson / poly-split detector** — flag a run as Tier-2 once a proven
  `B(n)` exists.

---

## 9. Gaps and open questions

Oracle-specific gaps. Algorithm-level gaps (budget/soundness handshake, flag
iso-invariance, Tier-0 sort key) live in
[`chain-descent-strategy.md`](./chain-descent-strategy.md) §15.

In rough priority order:

1. **T-C is the open problem.** Sorting a cell into orbits cheaply, in general,
   is equivalent to GI ∈ P. The design isolates this; it does not close it.
   Every gap below is a consequence.

2. **"Cascade" is not yet precisely defined.** Refinement gives cells that are
   *supersets* of orbits; certifying that a cell *is* a single orbit needs more
   than refinement. The cascade oracle's exact certification predicate — what
   bounded check it runs, and what it guarantees — is undefined design work
   (§5). This is the first thing to nail down: both the Tier-1 proof and the
   oracle's code depend on it.

3. **Tier 1 → polynomial is a target, not a theorem.** Even if every node
   certifies cheaply, genuine decisions could in principle still stack. The
   budget *catches* that — but by *flagging* a graph we wanted canonized.
   Whether genuinely-Tier-1 graphs fit a polynomial budget under the cascade
   oracle is the unproven Tier-1 theorem. The design makes it cleanly
   *targetable* (a per-node, inductive statement); it does not prove it.

4. **The linear oracle is built; the a-priori cascade oracle is the open piece.**
   §6 specifies the linear oracle; it was **built and validated through CFI(K7)
   (2026-05-28)** — [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
   §8.1. Note (measured 2026-05-28) the a-posteriori path already canonizes
   CFI(K4…K6) under the default budget, keeping leaf counts well below `2^β`; the
   binding constraint at larger bases is the `O(leaves · n²)` leaf cache, not the
   node budget. The linear oracle collapses the leaf count (~7× on K7) but does
   **not** reach `O(β)`: it is *starved* — 100% of residual CFI(K7) branching is
   at non-singleton footprints where no forced map exists. The
   **a-priori cascade oracle** ([`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)) —
   bounded-depth recursion that resolves those footprints into all-singleton ones,
   feeding the linear oracle's (working) harvest — was **built 2026-05-28** (lockstep
   per-rep single-path) and **eliminated the starvation**: CFI(K7) collapsed 941 → 1
   leaf, 555 → 0 residual branching, recursion depth ≈ `tw(H)` (correct +
   scramble-invariant through K7). The implementation risk is closed *on CFI*; the
   remaining work is the Lean discharge and general-class (Tier-2/3) completeness.

5. **Is the wall reachable from the descent's output?** The construction
   question (§7). Target: prove every obstruction the descent produces
   decomposes as `(resistant-abelian) ⋊ (cascading)` — or find a counterexample,
   which would be the first clean hidden-Johnson graph. This is *(O\*)-existence*
   (≡ GI ∈ P). Its separable sibling — *classifying* a non-cascade, non-abelian
   residual as a **Cameron section** (Cameron-hard, not GI-hard) — is the
   Exhaustive-Obstruction Lemma, scoped in
   [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md);
   do not fold the two together.

6. **Restricted-class polynomiality.** Prove decomposability / a polynomial
   bound on bounded-degree, bounded rank-width, bounded treewidth. Achievable,
   provable, validates the architecture.

7. **The higher-WL lever** — how far does a `k`-WL refinement widen Tier 1? It
   absorbs all Johnson-scheme cells; quantify the gain. It does not cross the
   true wall.

8. **Relation to Babai's bound.** If the descent's residual obstructions are
   always Johnson-type, matching `2^O(log³n)` via a properly group-theoretic
   calculator is itself a non-trivial standalone result.

---

## 10. Lineage: two wrong turns

The current shape was reached through two wrong turns. Both are kept on the
record because their failure modes are subtle and easy to repeat.

### 10.1 The nauty-IR calculator

**What it was.** An earlier calculator — the `GroupCalculator` class, since
deleted — was a top-down recursive **IR search**: branch over a target cell's
vertices, recurse, prune a branch when a harvested automorphism showed it
redundant, take the lex-min leaf. It was **correct** — scramble-invariant and
complete — and it passed the whole test corpus. That is exactly what made it
dangerous: a correct canonizer *looks* like progress toward a polynomial one.

**Why it was a departure.** Correct, but not the intended algorithm, in three
load-bearing ways:

- **Unbounded.** It explored the IR tree to exhaustion. An IR search is
  nauty-shaped, and nauty is exponential worst-case (provably — Neuen &
  Schweitzer); on a hard input it simply ran exponentially. A polynomial
  canonizer must be *polynomial-or-honest-flag*, never silently exponential. The
  IR-search shape had quietly substituted exhaustive exploration for T-C — the
  very hurdle the calculator exists to face.
- **Decorative chain.** It built a `PermutationGroup`, but the search did not
  route through it as a stabilizer chain — the chain was a byproduct, not the
  spine.
- **No seam.** There was nowhere to plug in a-priori transversal certification —
  so no route from the exhaustive search to genuine lex-leader descent.

**How chain descent corrected it.** The rewrite kept the top-down recursion (not
a departure — see below) and fixed the three faults: a polynomial node
**budget** makes every run polynomial-or-flag; the `PermutationGroup` chain is
**load-bearing** (the oracle and the pruning consume it); and the
**`ITransversalOracle` seam** is where a-priori certification plugs in — the
deferred linear oracle is what turns the bounded search into genuine lex-leader
descent.

**What was *not* a departure.** Two shipped choices looked like deviations but
were forced-correct, and the harness keeps them:

- *Top-down recursion, not literal bottom-up Schreier–Sims construction.* A
  literal bottom-up construction needs each level's transversal *already
  discovered* to take its inductive step — and transversal discovery *is* T-C.
  Top-down recursion that discovers transversals by exploring is what is
  buildable. Schreier–Sims stays inside `PermutationGroup`, organizing
  discovered automorphisms — the analysis lens, not the control flow.
- *Branching over a target cell's vertices, not a single pair.* An early attempt
  branched on one within-cell pair chosen by vertex index; the tree shape then
  depended on the input labelling and **failed scramble-invariance** (C4: an
  edge-first guess discretizes in one step → 2 leaves; a diagonal-first guess
  leaves a 2-cell → 4 leaves). Branching over the whole, iso-invariant target
  cell is the standard correct IR shape, forced by iso-invariance.

**The lesson.** "Correct" and "polynomial" are different properties, and an IR
search delivers the first while silently failing the second. The budget is what
makes the gap *visible* — a flag instead of an exponential run — and the oracle
seam is what keeps a route open to closing it.

### 10.2 The boolean-class era

The arc, compressed:

**The original bet.** The calculator's per-entry formulas would stay AND-of-XOR
(linear over `Z₂`); LexMin via Gaussian elimination.

**Phase 2 result: ~0% XOR-fit on every graph, including CFI** — both with
rotation variables and with a clean direction-only basis. Ruling out "wrong
variable basis" forced a structural diagnosis.

**Structural impossibility.** Two reasons AND-of-XOR cannot fit: (1) transitive
closure without driver tracking is OR-of-ANDs, not AND-of-XOR; (2) the
rank-based canonical reading is non-linear in the `P` entries — rank itself is
linear (a count, `Σ`), but the *selector + matrix-lookup* makes the canonical
`XᵀAX`, a **quadratic** form (the quadratic-assignment problem). Linear
assignment is polynomial; quadratic assignment is NP-hard; canonical labelling
is the latter.

**Horn / LP dead ends.** TC's implication shape *is* Horn — but "total order" is
not Horn-definable, and Horn says nothing about the objective. The constraint
side is LP-friendly (order constraints are totally unimodular), but the LP
relaxation over the Birkhoff polytope equals fractional isomorphism, which
equals 1-WL (Ramana–Scheinerman–Ullman / Tinhofer); Sherali–Adams / Lasserre
need `Ω(n)` levels on CFI. No relaxation shortcut exists.

**Why it all pointed to the group reframe.** Boolean and algebraic classes are
*constraint* languages. The canonical is an *orbit-minimum*. An orbit needs a
group, not a formula. XOR came closest only because `Z₂`-vector-spaces *are*
groups (abelian ones) — the project had the abelian special case and mistook it
for the general tool. That is §2.

---

## 11. What "the calculator is done" looks like

- The chain-descent calculator canonizing Tier 0 / Tier 1 / CFI in *proven*
  polynomial time. (Today: implemented and budget-bounded, but T-C unproven.)
- C4+K2 #56 and CFI(Cycle3) pass; disjoint CFI is linear in #components.
- T-A and T-B cited from computational group theory; T-C either resolved, or
  honestly scoped to a restricted class with the Tier-2 detector flagging the
  rest.
- The CFI family validated against an external canonizer.
- The doc set (overview / strategy / calculator) self-contained for an external
  reader.

Anything short of this is a research checkpoint.

### Status snapshot

- **Settled:** the calculator is a stabilizer-chain lex-leader descent. T-A and
  T-B are free (computational group theory); all difficulty is isolated in
  T-C — per-level transversal discovery.
- **Settled:** the tier classification (0 / 1 / 2) and the cascade ×
  composition-factor hardness map.
- **Implemented:** the chain-descent harness, the `ITransversalOracle` seam, the
  Phase-1 `CascadeOracle`, the **linear oracle** (§6), and the **a-priori cascade
  oracle** — all correct and budget-bounded; the a-priori cascade oracle
  eliminated linear-oracle starvation and collapsed every measured CFI base
  (K4…K7) to a single path (§9 item 4).
- **Open:** T-C in general; the polynomial-bound Lean discharge; whether Tier 2
  arises from the descent at all (the construction question).
