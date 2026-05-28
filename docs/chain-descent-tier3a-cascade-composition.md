# Chain descent — Tier 3a paper plan (cascade composition)

A paper-first plan for **Theorem 3a (cascade composition)**: the
cascade depths of layered cascade-class subgroups add. Generalizes
Tier 1 (CFI cascade) and Tier 2 (scheme cascade at depth 1) to
compositions — CFI of CFI, CFI of Scheme, Scheme of CFI, Scheme of
Scheme, and any future cascade-class layered atop them.

This is a **planning doc**, not a paper. It scopes the theorem, the
inductive proof shape, the concrete instances it unifies, the
subtleties around layer-chain validity, and the Lean discharge path
once paper-rigorous.

For the broader Tier-3 framing see
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md);
Theorem 3a is Tier 3a, the paper-tractable stepping stone scoped in
that doc's §10.2. For Tier 1 and Tier 2 see
[`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md);
for the cascade oracle and cost model see
[`chain-descent-calculator.md`](./chain-descent-calculator.md).

---

## 1. Headline

> **Theorem 3a (cascade composition).** Let `G` be a connected graph
> whose automorphism group admits a normal chain
>
> `Aut(G) = H_0 ⊵ H_1 ⊵ … ⊵ H_k = {1}`
>
> where each successive quotient `H_{i-1}/H_i` is in a *cascade class*
> with depth bound `f_i` — i.e., for the quotient graph `G_i := G/H_i`
> (with `G_0 := G`), there exists `S_i ⊆ V(G_{i-1})` with `|S_i| ≤ f_i(|V(G_{i-1})|)`
> such that 1-WL refinement on `(G_{i-1}, S_i)` recovers
> `H_{i-1}/H_i`-orbits.
>
> Then `G`'s cascade depth is at most `Σ_i f_i`.

In the canonical case `Aut(G) = N ⋊ Q` with `N` and `Q` in known
cascade classes, this gives cascade depth `f_N + f_Q`. Iterated `k`
times, an `Aut(G) = N_1 ⋊ N_2 ⋊ … ⋊ N_k` layered group has cascade
depth `Σ f_i`.

**Corollary 3a (polynomial cost for layered graphs).** If every `f_i`
is polynomial and `k` is polynomial in `n`, the chain-descent canonizer
runs in `poly(n)` on `G`.

---

## 2. Motivation

Tier 1 and Tier 2 give cascade-depth bounds for two specific graph
families:

- **Tier 1.** `CFI(H)` cascades in `≤ tw(H)` individualizations.
- **Tier 2.** Schurian scheme graphs cascade in `1` individualization.

A natural family of "harder" cases involves compositions — CFI applied
to a scheme graph, schemes built on top of CFI residues, CFI of CFI,
etc. Each composition has a layered automorphism group:

| Composition | Layered `Aut` structure |
|---|---|
| CFI(CFI(H)) | `Z_2^{β_outer} ⋊ (Z_2^{β_inner} ⋊ Aut(H))` |
| CFI(Scheme_G) | `Z_2^β ⋊ Aut(Scheme_G)` |
| Scheme on CFI residue | `Aut(Scheme_outer) acts on N-orbits, with N ≤ Z_2^β` |
| Iterated CFI tower `CFI^d(H)` | `Z_2^{β_1} ⋊ Z_2^{β_2} ⋊ … ⋊ Z_2^{β_d} ⋊ Aut(H)` |

Without Theorem 3a, each composition requires its own cascade analysis
— bookkeeping multiplies. With Theorem 3a, each composition's cascade
depth is *automatically* the sum of its layers' depths (whichever
cascade-class theorem covers each layer).

**Strategic value.** Theorem 3a does not add a new cascade class; it
**composes** the existing ones (and any future ones). Future cascade
classes — Hamming, distance-regular extensions, the higher-rank scheme
cases of Tier 2 — slot in without re-proving composition.

---

## 3. Setup

### 3.1 Cascade class

A graph family `𝓒` (with a function `f_𝓒 : ℕ → ℕ`) is a **cascade
class with depth bound `f_𝓒`** if for every `G ∈ 𝓒`, there exists
`S ⊆ V(G)` with `|S| ≤ f_𝓒(|V(G)|)` such that:

- 1-WL refinement on `(G, S)` (fresh-colour individualization of `S`)
  reaches a partition equal to the `Aut(G)_S`-orbit partition.

The cascade depth bound `f_𝓒` is polynomial for tractable classes:
constant for Tier 2 (`f = 1`), bounded by `tw(H)` for Tier 1
(`f = tw(H) ≤ n_H`).

### 3.2 Layered group structure

`G` has **layered group structure** `(H_0, H_1, …, H_k)` if
`Aut(G) = H_0 ⊵ H_1 ⊵ … ⊵ H_k = {1}` is a normal subgroup chain.

For each `i`, the **quotient graph** `G_i = G/H_i` has automorphism
group containing `Aut(G)/H_i = H_0/H_i`. The successive quotient
`H_{i-1}/H_i` acts on `G_{i-1}` (the previous quotient graph) as a
"layer of symmetry" to be stripped.

In the typical case (semidirect product), `H_i = N_{i+1} ⋊ … ⋊ N_k`
and the successive quotients are `H_{i-1}/H_i ≅ N_i`.

### 3.3 Cascade-class layer

A layer chain `(H_0, …, H_k)` is **cascade-class** if for each
`i = 1, …, k`, the quotient action `H_{i-1}/H_i ↷ G_{i-1}` falls in
a known cascade class with depth bound `f_i`.

Specifically: there exists `S_i ⊆ V(G_{i-1})` with `|S_i| ≤ f_i(|V(G_{i-1})|)`
such that 1-WL on `(G_{i-1}, S_i)` recovers the `H_{i-1}/H_i`-orbit
partition on `V(G_{i-1})`.

### 3.4 Stripping

After step `i`, the individualization set has stripped the symmetry
down to `H_i`. The residual cells (= `H_i`-orbits on `V(G_{i-1})`) are
the vertices of `G_i`. Continuing with `S_{i+1}` individualizations on
`G_i` reaches the `H_{i+1}`-orbit partition.

---

## 4. Theorem 3a — statement and proof outline

### 4.1 Formal statement

> **Theorem 3a.** Let `G` be a connected graph with cascade-class layer
> chain `(H_0, …, H_k)` and per-layer depth bounds `f_1, …, f_k`. Then
> there exists `S ⊆ V(G)` with `|S| ≤ Σ_{i=1}^k f_i(|V(G_{i-1})|)`
> such that 1-WL refinement on `(G, S)` reaches a partition equal to
> the `Aut(G)_S`-orbit partition (which is `{1}` since `H_k = {1}`,
> hence the discrete partition).

### 4.2 Proof outline

By induction on `k`.

**Base case (`k = 0`).** `Aut(G) = {1}`, so the discrete partition is
already the orbit partition; `S = ∅` works.

**Inductive step (`k → k + 1`).** Assume the theorem holds for chains
of length `≤ k`. Given a chain `(H_0, …, H_{k+1})`:

1. **Outer strip.** The pair `(H_0, H_1)` is a cascade-class layer with
   depth `f_1`. So there exists `S_1 ⊆ V(G)` with `|S_1| ≤ f_1(|V(G)|)`
   such that 1-WL on `(G, S_1)` reaches the `H_0/H_1`-orbit partition
   on `V(G)`. These orbits are exactly the vertices of `G_1 = G/H_1`.

2. **Residual chain.** `(H_1, …, H_{k+1})` is a cascade-class chain of
   length `k` on `G_1`. By induction, there exists
   `S_1' ⊆ V(G_1) = H_0/H_1` with `|S_1'| ≤ Σ_{i=2}^{k+1} f_i(|V(G_{i-1})|)`
   such that 1-WL on `(G_1, S_1')` reaches the discrete partition.

3. **Lift to `G`.** Each `H_0/H_1`-orbit is a cell of the 1-WL partition
   on `(G, S_1)`. Individualizing one representative per orbit in `S_1'`
   means picking one `G`-vertex from each chosen `H_0/H_1`-orbit. Call
   this lift `S_2 ⊆ V(G)`; `|S_2| = |S_1'|`.

4. **Combine.** Set `S := S_1 ∪ S_2`. Then `|S| ≤ |S_1| + |S_2| ≤
   f_1(|V(G)|) + Σ_{i=2}^{k+1} f_i(|V(G_{i-1})|)`.

5. **1-WL on (G, S) discretizes.** Because 1-WL is **monotone in the
   individualization set** (`warmRefine_refines`, proved), the
   partition on `(G, S_1 ∪ S_2)` refines the partition on `(G, S_1)`
   (which has cells = `H_0/H_1`-orbits). On each such orbit (cell),
   adding `S_2`-individualizations replays the inductive-hypothesis
   1-WL on `G_1` and discretizes. Combined: 1-WL on `(G, S)` reaches
   the discrete partition. ∎

### 4.3 What the proof leverages

| Ingredient | Status | Source |
|---|---|---|
| `warmRefine_refines` (1-WL monotonicity in individualizations) | Proved | [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean) |
| Tier 1 cascade (CFI layer at depth `≤ tw(H)`) | Proved (OddDegree, axiom-free) | [orbit-recovery §5](./chain-descent-orbit-recovery.md) |
| Tier 2 cascade (scheme layer at depth 1) | Proved (rank ≤ 2 + |J| ≤ 1) | [orbit-recovery §14.3](./chain-descent-orbit-recovery.md) |
| Layered-group setup (chain `H_0 ⊵ … ⊵ H_k`) | New, paper-easy | This doc |
| Quotient-graph construction `G_i = G/H_i` | Standard group theory | — |
| Lift of `G_i`-individualization to `G`-individualization | Routine | This doc |

The only genuinely new mathematical content is **the combination
step (4.2.5)** — that 1-WL on `(G, S_1 ∪ S_2)` reaches the discrete
partition by replaying the inductive `(G_1, S_1')` cascade on each
cell. This reduces to monotonicity (proved) plus the observation that
1-WL on a cell coincides with 1-WL on the corresponding `G_1`-vertex
set — a routine but bookkeeping-heavy lemma.

### 4.4 Subtleties to address in the paper

1. **`H_{i-1}/H_i` acts on `G_{i-1}`, not on `G`.** The "layer
   stripping" individualizations are vertices of `G`, but the cascade-
   class theorem for layer `i` is stated for `G_{i-1}`. The lift in
   step 4.2.3 needs to be made precise — typically a choice of
   representative per orbit, which is iso-invariantly settled by the
   canonical chain-descent picker
   ([orbit-recovery §3](./chain-descent-orbit-recovery.md)).
2. **`k ≤ n` automatically.** Theorem T-B
   ([calculator §4](./chain-descent-calculator.md)) bounds the
   stabilizer chain length at ≤ `n`, so total individualizations
   `|S| ≤ n` trivially. Combined with `|S| ≤ Σ f_i` and `f_i ≥ 1` per
   non-trivial layer, this gives `k ≤ Σ f_i ≤ n`. No separate
   hypothesis on `k`'s polynomial growth is needed — the polynomial-
   bound question reduces entirely to **each `f_i` being polynomial**,
   which each cascade class (Tier 1, Tier 2, future) delivers
   individually. For `CFI^d(H)`, this also means `d ≤ n` is automatic,
   though the cumulative `Σ tw(CFI^{i-1}(H))` may still blow up
   super-polynomially when the tower's treewidth grows — the
   polynomial bound is "all `f_i` polynomial," not just "few layers."
3. **`H_{i-1}/H_i` may not be in *one* known cascade class.** A layer
   could combine CFI and scheme structure. The theorem statement is
   robust to this: as long as *some* cascade-class bound applies to
   each layer's quotient action, the sum works.
4. **The proof runs on warm refinement of `(A, P)`, not pure 1-WL on
   `A` alone.** The partial-order `P`-matrix substrate is **load-
   bearing**: warm refinement on `(A, P)` is split-only
   (`warmRefine_refines`), direction-symmetric (`warm_6_2`), and
   compatible with the descent spine (`warmRefine_agree_off'`) — all
   load-bearing for §4.5's reordering / implicit-discovery argument.
   Pure 1-WL on adjacency alone is not direction-symmetric and would
   break the reordering step ([strategy §10](./chain-descent-strategy.md)
   spells out a fresh-1-WL counterexample on 3 vertices). Empirically
   confirmed via an edge-case check.

### 4.5 Implicit discovery — the chain is a proof artifact

A consequence of §4.2 + the descent spine machinery: **the layer
chain doesn't need to be discovered by a separate algorithm**. The
chain descent (cascade + linear oracles, lex-leader descent) achieves
the Theorem 3a bound implicitly, because:

1. **Selection is irrelevant for correctness.** All layer chains end
   at `{1}`. Whichever chain the descent's behaviour traces, the
   resulting canonical form is the same — the lex-min over
   relabellings (strategy §7, completeness).

2. **Selection is automatic for the bound.** The descent doesn't
   pre-select a chain. It just runs: at every node, the cascade
   oracle certifies a target cell's orbit structure (when possible),
   the linear oracle reads a candidate twist off a single branch's
   propagation pattern (when possible), and the algorithm processes
   cells in canonical id order. The implicit chain — the sequence
   of subgroups that the descent's stripping happens to trace —
   gives *some* `Σ f_i` ≤ the cascade depth of *whichever* admissible
   chain the descent traversed.

3. **Construction is automatic.** Every cascade oracle invocation
   that certifies an orbit harvests a generator into the
   `PermutationGroup` chain ([calculator §2](./chain-descent-calculator.md));
   every linear oracle invocation that verifies a twist harvests a
   generator. The accumulated generators witness the implicit chain
   — they generate `H_0`, their action quotients to `H_1`, and so on
   down to `H_k = {1}`. No explicit chain-identification step is
   needed.

4. **Reordering is paper-only.** §4.2's proof rearranges the
   `S_i`-individualizations in a specific order to make the
   induction clean. The *algorithm* doesn't reorder — it processes
   cells in canonical id order, and the descent spine
   (`warmRefine_agree_off'`) guarantees the partition is independent
   of order. The reordering argument is a proof tool to bound `|S|`,
   not an algorithmic step.

**Corollary 3a' (implicit best-chain bound).** Let `G` be a graph
admitting *at least one* cascade-class layer chain (i.e., satisfying
Theorem 3a's hypothesis for some `H_0 ⊵ … ⊵ H_k`). Then the chain
descent's cascade depth on `G` is at most
`min { Σ_i f_i : (H_0, …, H_k) is an admissible cascade-class chain }`.

The minimum is taken over all admissible chains — the algorithm gets
the *best* chain's bound for free, without having to identify which
chain is best.

**What this collapses.** The original §8.3.1 (layer-chain
discoverability) reduces to the single question: *does an admissible
chain exist?* That's the broader Tier 3 question (existence of a
cascade-class normal chain — equivalent to no-hidden-Johnson on `G`).
Selection and construction are no longer separate sub-problems.

**What this depends on.** Corollary 3a' has two halves of "automatic
discovery": the cascade-oracle half (certify orbits a-priori, harvest
true-symmetry generators) and the linear-oracle half (discover abelian
twists from one branch's footprint).

- **Linear-oracle half — built and validated (2026-05-28).** The linear
  oracle is implemented and correctness-preserving through CFI(K7)
  ([linear-oracle §8.1](./chain-descent-linear-oracle.md)). Where it
  gets an all-singleton footprint it collapses the decision completely.
  Sub-claim 1's abelian-stripping mechanism is empirically confirmed
  for the all-singleton case.
- **Cascade-oracle half — the binding constraint.** The *shipped*
  cascade oracle is the Phase-1 **a-posteriori** version (certifies
  nothing before branching; prunes after, via harvested automorphisms).
  The **a-priori** cascade oracle — certify one rep per orbit *before*
  branching — is unbuilt ([calculator §5/§9](./chain-descent-calculator.md)).
  Measured consequence: on CFI(K7) **100% of residual branching is at
  non-singleton footprints**, where the linear oracle is *starved*
  (no forced twist). The a-priori cascade oracle would resolve the
  residual symmetry before branching → all-singleton footprints → the
  linear oracle finishes them → the tree collapses toward the
  depth-bounded path.

So the implicit-discovery argument's linear-oracle half is confirmed;
the cascade-oracle (a-priori) half is now the gap, and the path to
polynomial CFI. See §9.

---

## 5. Concrete instances

Each instance follows from Theorem 3a by exhibiting the layer chain
and applying Tier 1 / Tier 2 / future cascade-class results to each
layer.

### 5.1 CFI of CFI — `CFI(CFI(H))`

**Layer chain.** `Aut(CFI(CFI(H))) = Z_2^{β_outer} ⋊ Z_2^{β_inner} ⋊ Aut(H)`.

- Layer 1 (outer CFI): `H_0/H_1 = Z_2^{β_outer}`, depth `f_1 = tw(CFI(H))` by Tier 1.
- Layer 2 (inner CFI): `H_1/H_2 = Z_2^{β_inner}`, depth `f_2 = tw(H)` by Tier 1.
- Layer 3 (base symmetry): `H_2/H_3 = Aut(H)`. If `Aut(H)` is itself in a cascade class (e.g., `H` is rigid → `Aut(H) = {1}`; `H` is a scheme → Tier 2), include further layers; otherwise this is the residue.

**Cascade depth.** `tw(CFI(H)) + tw(H) + (depth bound for Aut(H))`.

**Caveat.** `tw(CFI(H))` grows roughly as `2 · tw(H)` plus
gadget-related terms — so for `CFI^d(H)`, the cumulative bound is
`O(tw(H) · 2^d)`. Theorem 3a gives this cleanly, but it is exponential
in tower depth `d`. Polynomial-in-`n` follows when `d` is constant or
`d = O(log n)`.

### 5.2 CFI of Scheme — `CFI(G_scheme)`

**Layer chain.** `Aut(CFI(G_scheme)) = Z_2^β ⋊ Aut(G_scheme)`.

- Layer 1 (outer CFI): depth `tw(G_scheme)` by Tier 1.
- Layer 2 (inner scheme): depth `1` by Tier 2.

**Cascade depth.** `tw(G_scheme) + 1`.

**Concrete example.** `CFI(Petersen)` has `tw(Petersen) = 4`, so
cascade depth `≤ 5`. Compare: direct Tier 1 gives the same bound (`≤
tw(Petersen) = 4` for the outer CFI plus the trivial scheme of
Petersen is its full structure, which 1-WL already captures), but the
compositional argument makes the *reason* explicit and generalizes.

### 5.3 Scheme on CFI residue

**Setup.** A graph `G` whose vertex set is the `H`-orbits of `CFI(H)`
for some `H ≤ Aut(CFI(H))`, and whose edges form a scheme on those
orbits. This is rare in practice but useful as a "Scheme-of-CFI" case.

**Layer chain.** `Aut(G) = Aut(G_scheme) ⋊ H` (with `H ≤ Z_2^β` typically).

- Layer 1 (outer scheme): depth `1` by Tier 2.
- Layer 2 (inner CFI residue): depth bounded by inner CFI's tw.

**Cascade depth.** `1 + tw(inner base)`.

### 5.4 Scheme of Scheme — `Scheme(G_scheme)`

**Setup.** A scheme on a scheme — formally, a coherent algebra on the
orbits of another coherent algebra. The classical "fusion scheme"
construction.

**Layer chain.** Both layers are Tier-2, so cascade depth `≤ 1 + 1 = 2`.

**Practical note.** Most "scheme of scheme" constructions in the
literature collapse to a single scheme (the join). The two-layer
treatment is correct but unnecessarily granular for graphs known to
admit a single Tier-2 description.

### 5.5 Iterated CFI tower — `CFI^d(H)`

The original "CFI-tower" target.

**Layer chain.** `Aut(CFI^d(H)) = Z_2^{β_d} ⋊ Z_2^{β_{d-1}} ⋊ … ⋊ Z_2^{β_1} ⋊ Aut(H)`.

**Cascade depth.** `Σ_{i=1}^d tw(CFI^{i-1}(H)) + (depth bound for Aut(H))`.

**Polynomial bound regime.** Holds when `d` is bounded and `tw(H)` is
bounded — i.e., for constant-depth towers over bounded-treewidth
bases. Unbounded `d` or unbounded `tw(H)` gives super-polynomial bounds
even under Theorem 3a, which is consistent with chain descent flagging
high-treewidth or high-tower-depth CFI as outside the cascade class.

---

## 6. Coverage map

A compact table of which graph classes Theorem 3a covers, in
combination with Tier 1 and Tier 2:

| Class | Layer chain | Cascade depth |
|---|---|---|
| Rigid graph | `Aut = {1}` (k=0) | 0 |
| Scheme graph (Tier 2) | `Aut = G_action`, 1 layer | 1 |
| CFI(H), `H` rigid | `Z_2^β`, 1 layer | `tw(H)` |
| CFI(H), `H` scheme | `Z_2^β ⋊ Aut(H)`, 2 layers | `tw(H) + 1` |
| CFI(CFI(H)), `H` rigid | 2 layers | `tw(CFI(H)) + tw(H)` |
| CFI(Scheme_G) | 2 layers | `tw(G_scheme) + 1` |
| Scheme(CFI residue) | 2 layers | `1 + tw(inner base)` |
| Scheme(Scheme) | 2 layers (collapsible) | `2` (or `1` after collapse) |
| `CFI^d(H)` tower | `d + 1` layers | `Σ_{i=0}^{d-1} tw(CFI^i(H)) + depth(Aut(H))` |
| Hamming `H(d, q)` (future Tier 2 extension) | 1 layer | `1` (once depth-2+ convergence lands) |
| Mixed unknowns | Whatever decomposes | Σ of known + unknown residue |

The pattern: every known cascade class is a one-layer instance of
Theorem 3a, and every composition adds layers with summed depths.

---

## 7. What changes from "CFI-tower" to "cascade composition"

The original Tier 3a target was iterated CFI alone. The composition
framing is **strictly more general** with **zero additional proof
effort** in the inductive step — the same argument (cascade is
monotone, 1-WL on a cell = 1-WL on the quotient vertex) handles all
layer types uniformly.

What the composition framing buys:

- **Unified statement.** One theorem, not "CFI-tower theorem +
  CFI-of-Scheme corollary + Scheme-of-CFI corollary + …".
- **Forward compatibility.** Future cascade classes (Hamming,
  distance-regular extensions, higher-rank schemes) automatically
  compose without re-proving.
- **Cleaner Lean formalization.** A single `CascadeClass` typeclass +
  one `composition` lemma, instantiated per known class.

What it does *not* buy:

- **Tighter cascade depths.** The compositional bound is `Σ f_i`,
  which is the same as the natural direct bound for most known cases.
  Theorem 3a is about *coverage*, not *sharpness*.

---

## 8. Risks and open questions

### 8.1 Where the proof could resist

| Step | Risk |
|---|---|
| 4.2.3 (lift `S_1'` from `G_1` to `S_2` in `G`) | Low — routine; the canonical chain-descent picker handles the iso-invariance |
| 4.2.5 (1-WL on cell = 1-WL on quotient vertex) | Low — follows from 1-WL's definition restricted to a cell + the quotient-graph definition |
| Reordering of individualizations (4.5.4) | Low — relies on the descent spine + warm refinement on `(A, P)`; pure 1-WL on `A` alone would not suffice |
| Polynomial bound when `k` grows | Class-dependent — bounded `k` for natural graphs, unbounded for CFI towers |

Discoverability of the chain is **not** on this list — §4.5 collapses
selection and construction into the algorithm's natural behaviour.

### 8.2 Where the hypothesis could fail

The cascade-class layer hypothesis can fail if:

1. **A layer's quotient action is non-cascade.** E.g., a hidden Johnson
   layer. By definition, Theorem 3a doesn't apply — this is exactly
   the Tier-2 wall.
2. **No admissible cascade-class chain exists.** This is the strong
   form of existence — equivalent in scope to the broader Tier 3
   decomposability claim, and the open mathematical content. (§4.5's
   implicit-discovery argument needs *some* such chain to exist; if
   none does, the algorithm flags rather than canonizing.)
3. **The chain is unbounded (`k` super-polynomial).** Cumulative
   depth still bounded by `Σ f_i`, but no longer polynomial. Out of
   scope for cascade-class graphs.

### 8.3 Open questions worth flagging

1. **Existence of an admissible cascade-class chain.** The genuine
   open Tier-3 content. Theorem 3a is conditional on existence;
   §4.5's implicit-discovery argument makes selection/construction
   automatic *given* existence. A counterexample (a graph admitting
   *no* cascade-class normal chain) is a hidden-Johnson witness — same
   as the broader construction question of
   [calculator §7](./chain-descent-calculator.md).
2. **Relation to GI lower bounds.** A graph that resists Theorem 3a
   for *every* choice of layer chain is exactly a Tier-2 / hidden-
   Johnson candidate. Counterexamples to Theorem 3a's hypothesis are
   the same counterexamples as to the Tier 3 decomposability claim.
3. **Sharpness of `Σ f_i`.** For specific compositions, tighter bounds
   may hold (e.g., overlapping individualizations could serve multiple
   layers). The implicit best-chain corollary (Corollary 3a') already
   gives the `min` over admissible chains — but tighter bounds may
   come from accounting for individualization overlap *within* a
   single chain.

---

## 9. Lean discharge

**Effort estimate.** Significantly less than Tier 1 or Tier 2's
discharge — Theorem 3a is a composition theorem on top of existing
results, not a new cascade lemma.

**Phased plan.**

1. **Phase A — abstraction.** Define a `CascadeClass` typeclass /
   structure parametrising graph families by depth bound. Re-package
   Tier 1 and Tier 2 as instances. ~500 lines, axiom-clean (uses
   existing theorems).
2. **Phase B — layer chain.** Define `LayerChain G` as a normal
   subgroup chain with quotient-graph maps. ~300 lines of group-
   theoretic infrastructure (Mathlib has `Subgroup.Normal`, the
   composition is standard).
3. **Phase C — composition lemma.** The Theorem 3a proof itself,
   induction on chain length, using `warmRefine_refines` for
   monotonicity. ~500-1000 lines.
4. **Phase D — instance applications.** Concrete corollaries for
   `CFI(CFI(H))`, `CFI(Scheme)`, etc. Each ~100-200 lines (just
   instance verification + Theorem 3a application).

**Total estimate.** ~1500-3000 lines, multi-week but tractable. All
load-bearing content (cascade lemmas) already proved; new content is
the composition framework.

**Risk.** Low — every component is either proved or routine. The
biggest risk is bookkeeping around the quotient-graph construction in
Lean, which Mathlib does not have packaged for general normal
subgroups.

---

## 10. What's settled, next, and risky

### 10.1 Settled (going into Tier 3a)

- `warmRefine_refines` (1-WL monotonicity) proved.
- Tier 1 cascade (CFI, OddDegree case) proved axiom-free.
- Tier 2 cascade (schurian schemes, `rank ≤ 2 ∧ |J| ≤ 1`) proved
  axiom-free.
- Composition framing's only new mathematical content is routine
  bookkeeping (4.2.5).
- Implicit-discovery argument (§4.5): the algorithm doesn't need to
  identify a chain — descent does it automatically given existence.
- Partial-order `(A, P)` substrate is load-bearing for the
  reordering / implicit-discovery argument (§4.4 point 4); pure 1-WL
  on `A` alone would not suffice.

### 10.2 Next (paper-first order)

1. **Paper draft of Theorem 3a** — this doc upgraded to paper-rigorous,
   with full proof of 4.2.5 spelled out and §4.5's implicit-discovery
   argument made precise (in particular: the linear oracle's
   harvested generators as witnesses to the chain).
2. **Concrete instance write-ups** — `CFI(CFI(H))`, `CFI(Scheme_G)`,
   `Scheme(Scheme)` worked through end-to-end as worked examples.
3. **Cover map verification** — for each row of §6, spell out the
   layer chain and confirm Theorem 3a's hypothesis is met.
4. **A-priori cascade oracle** — see §10.4 below; the linear oracle is
   now built but *starved* by the shipped a-posteriori cascade oracle.
   The a-priori cascade oracle is the next implementation lever and the
   path to polynomial CFI.
5. **Lean phase** — only after paper is reviewed. Phases A-D as in §9.

### 10.3 Risky

- **Existence of an admissible cascade-class chain** (open question
  8.3.1) is the only remaining mathematical risk. Theorem 3a is
  conditional on existence; the implicit-discovery argument of §4.5
  makes selection and construction automatic *given* existence. The
  existence question is the broader Tier-3 open content — equivalent
  in scope to the calculator §7 construction question, not a separate
  Tier-3a sub-problem.

### 10.4 The a-priori cascade oracle is the next lever

**Linear oracle — done (2026-05-28).** Built, validated through
CFI(K7), correctness-preserving; collapses every all-singleton
footprint ([linear-oracle §8.1](./chain-descent-linear-oracle.md)).
It remains load-bearing for Tier 3 sub-claim 1 (abelian-stripping),
Tier 3a Corollary 3a' (abelian-layer half), Tier 3 sub-claim 3
(alternation), and calculator §6 (its original target) — and it
discharges all of these for the all-singleton case.

**The binding constraint shifted to the a-priori cascade oracle.**
The measured result: the linear oracle is *starved*, not weak — on
CFI(K7), 100% of residual branching is at non-singleton footprints,
where the residual symmetry hasn't been stripped before branching.
The shipped cascade oracle is Phase-1 a-*posteriori* (certifies
nothing before branching; prunes after). The a-*priori* cascade
oracle — certify one representative per orbit *before* branching, the
unbuilt piece of [calculator §5/§9](./chain-descent-calculator.md) —
would feed clean all-singleton footprints to the linear oracle.

This is the same a-priori orbit-harvesting the **spine** fact enables
(read orbits off one branch's mirror), and it is exactly the
cascade-oracle half of §4.5's implicit-discovery argument. Building it
is the next concrete algorithmic step and the path to polynomial CFI.

The orbit-recovery program (Tier 1 `theorem_1_HOR_cfi_oddDeg`, Tier 2
`theorem_2_HOR_concrete_rank_two_J_singleton`) is precisely the
*correctness foundation* for an a-priori cascade oracle: it proves
1-WL recovers orbits at bounded depth, so certifying one rep per orbit
a-priori is sound on the cascade class. The implementation gap is
turning those existence theorems into a before-branching certification
procedure.

Designing and implementing the linear oracle is the next concrete
algorithmic step. Its construction predicate — turning a propagation
pattern into a candidate twist — is the one genuinely unspecified
piece ([calculator §9](./chain-descent-calculator.md), item 4), now
spec'd in [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md).
Multi-week effort, but with growing payoff as the proof program
references it more.

---

## 11. Cross-references

- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §10.2 — Tier 3a's role as a stepping stone in the broader Tier 3
  plan.
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) —
  Tier 1 (§5) and Tier 2 (§14.3) as the base cascade-class theorems
  Theorem 3a composes.
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §12 —
  `warmRefine_refines` (1-WL monotonicity), the proof's load-bearing
  lemma.
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §4 —
  T-A/T-B/T-C decomposition; Theorem 3a contributes to T-C for the
  layered cascade-class.
- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) §6 —
  the encoded-Johnson case is exactly when Theorem 3a's cascade-class
  layer hypothesis fails; Theorem 3a does not address it, leaving
  that to sub-claim 2 of the broader Tier 3 plan.
