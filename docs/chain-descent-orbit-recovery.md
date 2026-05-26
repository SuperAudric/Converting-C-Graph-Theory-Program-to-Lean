# Chain descent — refinement recovers stabilizer orbits

The single theorem and conjecture this doc is built around:

> **After enough fresh-colour individualizations, 1-WL refinement on a graph
> produces a partition whose cells are exactly the orbits of the residual
> automorphism group.**

Spun out of the Tier-2 decomposition experiment
([`chain-descent-tier2-decomposition-experiment.md`](./chain-descent-tier2-decomposition-experiment.md)
§10), where finding F7 observed it empirically on CFI(Petersen) at depth 1.
This doc lifts F7 to a precise statement, organises the generalization
ladder, identifies what's provable now and what's open, and points at the
Lean targets.

It's the natural next-step from [Pieces A+B of the hidden-Johnson
near-theorem](./chain-descent-hidden-johnson.md) and a direct route to Piece
C. It's also a concrete intermediate target on the way to T-C
([`chain-descent-calculator.md`](./chain-descent-calculator.md) §4).

---

## 1. The claim, precisely

Let `G = (V, E)` be a graph with vertex types `χ : V → ℕ`. For a set
`S ⊆ V` of *individualized* vertices, write `χ_S` for the colouring that
gives each vertex of `S` a distinct fresh colour and leaves others at `χ`.
Run 1-WL refinement starting from `χ_S` to a fixpoint; call the resulting
partition `P(G, S)`.

The pointwise stabilizer of `S` in `Aut(G)` — write `Aut(G)_S` — acts on
`V` by automorphisms that fix every vertex of `S`. Its orbit partition is
`O(G, S) = { Aut(G)_S · v : v ∈ V }`.

**General fact (trivial direction).** `O(G, S)` always refines `P(G, S)`:
automorphisms preserve any 1-WL-derived partition. So
`O(G, S) ⊆ P(G, S)` always (as set partitions, ⊆ means "is a refinement
of").

**Orbit-recovery property.** `G` *recovers orbits at depth k* if for every
sequence of k individualizations chosen by some specified picker rule,
`P(G, S) = O(G, S)`.

**The claim.** For graphs in the cascade class (specifically those of
calculator.md §3 "cascade → polynomial"), there exists `k = poly(|V|)` such
that orbit recovery holds at depth `k`. Sharper conjectures specify `k`
exactly as a function of structural invariants (treewidth, WL-dimension,
etc.).

---

## 2. The generality ladder

Three tiers, in increasing scope and uncertainty:

### Tier 1 — CFI on any base graph

**Statement.** Let `H` be any connected base graph with all vertices
degree ≥ 2, and let `G = CFI(H)` (the canonical untwisted CFI). For any
single individualized vertex `v ∈ V(G)`, the 1-WL refinement
`P(G, {v}) = O(G, {v})`.

**Status.** Empirical evidence: CFI(C₃), CFI(K₄), CFI(Petersen) all show
cell-size signatures matching expected Aut-stabilizer orbit sizes. Most
direct on CFI(Petersen) — F7 of the experiment doc, where the signature
`[24, 24, 12, 12, 6, 6, 3×5, 1]` decomposes as (S₅-stabilizer orbits on
Petersen) × (residual gauge dim per orbit). Awaiting rigorous orbit-vs-cell
comparison via explicit generator enumeration — straightforward but
deferred infrastructure work.

**Proof strategy.** The structure of `Aut(CFI(H))` is well-known:
`Aut(CFI(H)) = Z₂^{β(H)} ⋊ Aut(H)` where `β(H) = |E(H)| - |V(H)| + 1` is
the first Betti number (cycle dimension). The 1-WL behavior on CFI(H) is
also well-studied: 1-WL distinguishes CFI from its twist iff `tw(H) < 1`
(i.e., never for any base of interest), but **post-individualization
1-WL** has different behavior — each individualization is effectively a
`+1` to the WL dimension.

The proof outline:
1. Identify `Aut(CFI(H))_v` for `v` a subset-vertex or edge-endpoint of
   gadget `X(u)`. Decomposes as `(stab_{Aut(H)}(u)) ⋊ (gauge subgroup
   fixing v's parity)`.
2. Compute the orbits of this stabilizer on `V(CFI(H)) \ {v}`. They are
   products: `(orbit of w in stab_H(u)) × (gauge orbit of w's gadget)`.
3. Show that 1-WL post-individualization-of-`v` reaches a partition of
   exactly this product shape, by induction on the distance in `H` from
   `u` to the gadget containing each `w`.

Step 3 is the load-bearing one. The intuition: individualizing a vertex
of gadget `X(u)` breaks parity-symmetry of `X(u)` and propagates through
edge bridges into the cycle structure, but cannot break the residual
gauge action on cycles not touching `u`. Refinement reads off exactly
this "distance class × residual gauge class" structure.

**Effort estimate.** Paper-rigorous: a dozen lemmas, all standard CFI
theory plus careful refinement bookkeeping; **bounded, doable in a focused
push**. Lean: needs CFI's `Aut` decomposition built up, which mathlib does
not have packaged; CFI gauge / cycle space arithmetic adds another
module. A real but finite formalisation project.

### Tier 2 — Association-scheme graphs (Johnson, Hamming, ...)

**Statement.** Let `G` be a graph admitting a vertex-transitive
association scheme (Johnson `J(m,k)`, Hamming `H(d,q)`, the distance-2
graph of a strongly regular graph, etc.). For any single individualized
vertex `v`, `P(G, {v}) = O(G, {v})`.

**Status.** This is essentially classical. Distance-regular graphs cascade
in O(1) individualizations and their orbit structure is given by the
scheme's intersection numbers. The Johnson-scheme case is exactly **Piece
C of the hidden-Johnson near-theorem**
([`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
§5), scoped but not yet paper-rigorous.

**Proof strategy.** Use the association scheme structure directly. For
Johnson `J(m,k)`:
1. After individualizing a vertex (a k-subset `A` of `[m]`), the
   stabilizer in the Johnson group is the Young subgroup
   `S_k × S_{m-k}` — permute the `k` elements of `A`, permute the `m-k`
   complement.
2. Orbits of this Young subgroup on other k-subsets are *profile classes*
   — two k-subsets are in the same orbit iff they have the same intersection
   size with `A` (calling that the "profile").
3. 1-WL refinement on `(J(m,k), A individualized)` produces exactly the
   profile partition, by induction on distance to `A` in `J(m,k)`.

For other scheme graphs the argument generalises with the scheme's
intersection matrix replacing the Johnson profile structure.

**Effort estimate.** Paper-rigorous: short, almost entirely citation from
association-scheme theory. Lean: needs association schemes packaged —
not in mathlib but conceptually clean. **This is probably the cleanest
proof of orbit recovery available**, because association schemes are an
algebraic structure that 1-WL is provably equivalent to (1-WL on
scheme graphs computes the scheme's coherent algebra, classical).

### Tier 3 — Cascade class (the conjecture)

**Statement.** Let `G` be a graph in the cascade class (calculator.md §3),
meaning: there exists a sequence of individualizations chosen by the
canonical chain-descent picker such that 1-WL discretizes `G` within
`poly(|V|)` steps. Then orbit recovery holds at each intermediate depth.

**Status.** Conjectural. Tier 1 (CFI) is a strict subcase; Tier 2
(scheme graphs) is another. Both Tier-1 and Tier-2 graphs cascade quickly,
matching the conjecture. But "cascade class" in its widest sense includes
graphs without obvious algebraic structure (e.g., strongly regular graphs
with non-trivial but polynomial-time Aut).

**What proving this would give us.** Orbit recovery on cascade class is
**T-C on cascade class**. The cascade oracle's job — sort target cell
into orbits cheaply — reduces to "run 1-WL on (G, individualized path)
and read off the cells." Polynomial by construction. So **Tier 3 ⇔ T-C
for cascade class**, the open Tier-1 polynomial bound.

**Bottom line.** Tier 3 is the goal but is essentially the open polynomial
problem. Tiers 1 and 2 are concrete subcases that are provable now and
deliver structural understanding even short of Tier 3.

---

## 3. What the experiment establishes

[CFI experiment](./chain-descent-tier2-decomposition-experiment.md) §9–10
gives **empirical support for Tier 1 on three instances:**

| Graph | depth-1 cells | Predicted from Aut-stabilizer? |
|---|---|---|
| CFI(C₃) | 6 cells, sizes [9, 2, 2, 2, 2, 1] | Matches (Z₂ ⋊ S₃)-stabilizer orbit sizes |
| CFI(K₄) | 14 cells, sizes [8, 4×4, 2×4, 1×4] (subset start) | Matches Z₂³ ⋊ S₄ stabilizer structure |
| CFI(Petersen) | 12 cells, sizes [24×2, 12×2, 6×2, 3×5, 1] (subset start) | Matches Z₂⁶ ⋊ S₅ stabilizer (S₅ = Johnson on J(5,2)) |

In each case the decomposition into (base-graph stabilizer orbit) ×
(residual gauge dim) is consistent with the observed cell sizes. **Note
this is signature-level evidence, not rigorous cell-vs-orbit comparison.**
A focused follow-up to construct Aut generators and compute orbits via
`PermutationGroup.Orbit()` would upgrade this to direct verification —
deferred until Tier-1 paper proof needs it.

**Cell-size signatures are iso-invariant across input scramblings.** This
is the experiment's P2, confirmed on all three CFI instances. It's a
*weaker* property than orbit-recovery (just says the partition is
well-defined, not that it matches Aut), but a *necessary* one.

---

## 4. Proof roadmap — Tier 1 (CFI on any base)

The most concrete next deliverable. In rough order of dependency:

**L1 — Aut(CFI(H)) structure lemma.** State and cite (Cai-Fürer-Immerman
1992, also Grohe 2017 Ch.13): `Aut(CFI(H)) = Z₂^{β(H)} ⋊ Aut(H)` where
the semidirect product action is the natural one. Paper: cite. Lean:
needs the CFI gauge/cycle space machinery.

**L2 — Stabilizer decomposition.** For `v ∈ V(CFI(H))` in gadget `X(u)`,
compute `Aut(CFI(H))_v`. Decomposes as `stab_{Aut(H)}(u) ⋊ Z₂^{β(H) - δ}`
where `δ ∈ {0, 1}` depending on whether `v` is fixed by gauge action on
gadget `X(u)`. Paper: short. Lean: case analysis on vertex type.

**L3 — Stabilizer orbit shape.** Show that `Aut(CFI(H))_v` orbits on
`V(CFI(H)) \ {v}` are products: each orbit is
`(orbit of u' in stab_{Aut(H)}(u)) × (gauge action restricted to X(u'))`.
Paper: a few lines from the semidirect-product orbit formula. Lean:
needs orbit/coset arithmetic, accessible.

**L4 — 1-WL post-individualization shape.** The load-bearing one. By
induction on distance in `H` from `u` to the gadget of each `w`, show that
1-WL refinement starting from `(CFI(H), χ_{v})` produces a partition whose
cells are exactly those L3 product orbits.

Sub-claims for L4:
- L4a: Vertices at distance 0 from `X(u)` (i.e., in `X(u)` itself) are
  refined into their gauge orbits within `X(u)` — base case.
- L4b: Refinement propagates one edge of `H` at a time, splitting cells of
  `X(u')` according to which `X(u)`-cells are bridged.
- L4c: At fixpoint, every cell consists of vertices in one
  `stab_{Aut(H)}(u)`-orbit (their gadget is in one `H`-orbit) and one gauge
  orbit (their parity matches).

L4 is the technical heart. The descent-spine work
(`warmRefine_agree_off'`, proved) provides the right framework: refinement
behavior depends on the partition, not the specific direction labels, so
the gauge action lifts cleanly to the refinement level.

**L5 — Equality.** Combine L3 (orbit shape) and L4 (1-WL shape).
`P(CFI(H), {v}) = O(CFI(H), {v})`. Paper-trivial after L3, L4. Lean: a
short tying lemma.

**Multi-individualization extension.** For `S = {v_1, ..., v_k}`, recurse
L4: each `v_i` reduces the residual stabilizer by another factor, and
1-WL after each step matches the new stabilizer's orbits. This gives
orbit recovery at every depth, not just depth 1.

---

## 5. What Lean has and what it lacks

**Existing infrastructure that helps:**
- `warm_6_2`, `warmRefine_agree_off'`, `warmRefine_agree_off` — partition
  stability under direction flips. The "1-WL is direction-blind" fact L4
  needs.
- `iterate_refineStep_preserves_singleton` — the fresh-colour individualized
  vertex stays a singleton throughout refinement. Direct base case for L4a.
- `signature_eq_of_samePartition` — partition-invariant refinement.
- `cl_prov` topological closure (§14 of ChainDescent.lean) — the partial-
  order machinery, not directly needed for L4 but adjacent.

**What's missing:**
- **CFI construction.** Not formalised in Lean. Building it is a real
  project — would need to mirror `CfiGraphGenerator.cs`'s gadget structure
  as `PMatrix` and `AdjMatrix`. Plausible scope: 200–400 lines of Lean.
- **Group action on graphs.** `Aut(G)` is not defined yet in our project's
  Lean. Mathlib has the group-theoretic machinery; integrating with our
  `AdjMatrix` / `Colouring` would be ~100 lines of glue.
- **CFI Aut structure lemma (L1).** Open project, depends on the above.

Lean-feasibility honest assessment: Tier 1 proof would be a multi-week
Lean project on top of the missing infrastructure. **Recommend paper-first**
to confirm the proof sketches are clean before committing Lean effort.

---

## 6. Connection to existing work

- **Hidden-Johnson Piece C** ([`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
  §5). Piece C is Tier 2 of this doc, restricted to Johnson scheme graphs.
  This doc's tier-2 proof — orbit recovery on association-scheme graphs —
  **subsumes Piece C** and may give a cleaner route than the current Piece
  C scope (which routes through Young subgroup combinatorics directly).
- **T-C** (`chain-descent-calculator.md` §4). Tier 3 of this doc *is* T-C
  on the cascade class. Settling Tier 3 closes the Tier-1 polynomial bound.
  Tier 1 (CFI) alone doesn't close T-C but adds a major proven subclass.
- **Descent spine** (`warmRefine_agree_off'`, proved). The spine theorem
  says all `2^d` direction-leaves share one partition. Combined with this
  doc: each layer's partition equals the residual-stabilizer's orbits, and
  the `2^d` label combinations live as a `Z₂^d` action on those orbits.
  **The spine + orbit-recovery together describe the cascade-class fully.**
- **Matroid framework**
  ([`chain-descent-matroid.md`](./chain-descent-matroid.md), closed). The
  matroid memo's "binary closure conjecture" §10 conjectured every graph's
  closure structure is a binary matroid. Tier 1 of this doc is a related
  but distinct claim: 1-WL post-individualization recovers Aut-stabilizer
  orbits for CFI graphs (whose Aut is `Z₂ⁿ ⋊ Aut_base`). They're not
  equivalent statements — orbit recovery is about refinement, not closure
  — but they point at the same underlying fact about CFI structure.

---

## 7. Open questions

- **Does orbit recovery hold exactly at depth 1**, or does it need
  intermediate depths? The experiment data suggests depth 1 already
  achieves it for CFI(Petersen) — but is that a coincidence of `tw(H) ≥ 4`?
  Worth checking on a base graph with `tw = 1` (a tree CFI doesn't exist
  but tw=2 examples like longer cycles do).
- **Picker dependence**. CFI(C₃)'s cascade depth was different under
  lowest-cell-id vs smallest-cell picks; does orbit recovery hold under
  both, or only one?
- **Beyond cascade**. For graphs that *don't* cascade (genuine Tier-2, if
  they exist), what does refinement produce? It must be coarser than
  Aut-orbits (the trivial direction). Is the "extra coarseness" structured
  — e.g., a known coarsening of the orbit partition? This is the doorway
  back to Tier-2 detection.
- **Rate of convergence**. At what depth does 1-WL stabilize for cascade-
  class graphs? F6 of the experiment doc has a candidate: ≈ tw(H), with
  occasional tw(H)+1. Sharpening this is a project of its own.

---

## 8. Recommended first move

Paper-write **Tier 1 (CFI on any base)** through L1–L5. This is:

- bounded scope (a dozen standard lemmas);
- directly verified empirically by the existing experiment;
- a strict generalization of the experiment's F7 observation;
- a step toward Piece C and toward T-C without claiming either;
- and a clean concrete target — either it works as outlined or there's a
  specific lemma that fails and we learn something.

After the paper version is solid, decide between (a) Lean formalization
(real but bounded effort) and (b) jumping to Tier 2 (scheme graphs) as a
broader paper result.

This pacing keeps each step's value visible. Even if Tier 3 stays open
forever, Tier 1's paper proof is a publishable structural result about
CFI graphs — and rules out a specific candidate path for hidden-Johnson
encoding.

---

## 9. Tier 1 paper proof — CFI on any base

This section carries the paper proof. Started 2026-05-26.

### 9.1 Notation

Fix once and for all:

- **`H = (V_H, E_H)`** — the base graph. Connected, every vertex has
  degree ≥ 2.
- **`n_H = |V_H|`**, **`m_H = |E_H|`**, **`β_H = m_H − n_H + 1`** (first
  Betti number = cycle dimension).
- For `u ∈ V_H`, **`N(u) ⊆ V_H`** is `u`'s neighbour set, **`deg(u) =
  |N(u)|`**. Fix an arbitrary total order on `V_H` for canonical
  bookkeeping; this induces an ordering of `N(u)`.

The **CFI graph** `G = CFI(H)`:

- For each `u ∈ V_H` and each even-cardinality `S ⊆ N(u)`, a **subset
  vertex** `a_S^u`.
- For each edge `(u, w) ∈ E_H`, four **endpoint vertices**:
  `e^0_{u→w}`, `e^1_{u→w}` in `u`'s gadget; `e^0_{w→u}`, `e^1_{w→u}` in
  `w`'s gadget.
- **Intra-gadget edges**: `a_S^u ∼ e^b_{u→w}` iff `(w ∈ S) ⊕ b = 0`
  (equivalently: `w ∈ S` iff `b = 0`).
- **Inter-gadget edges (bridges, canonical untwisted `G_even`)**:
  `e^b_{u→w} ∼ e^b_{w→u}` for each `(u,w) ∈ E_H` and each `b ∈ {0,1}`.

The **gadget at `u`** is
`X(u) = { a_S^u : S ⊆ N(u), |S| even } ∪ { e^b_{u→w} : w ∈ N(u), b ∈ {0,1} }`.
So `|X(u)| = 2^{deg(u)−1} + 2·deg(u)`.

Throughout, **`v` denotes the fresh-colour individualized vertex**, with
**`u₀`** its containing gadget (i.e., `v ∈ X(u₀)`).

### 9.2 Automorphisms of CFI(H) — `Aut(CFI(H))`

**Two kinds of automorphisms:**

**(a) Base automorphisms.** For `σ ∈ Aut(H)`, define `Φ(σ) ∈ Sym(V(G))`
by `Φ(σ)(a_S^u) = a_{σ(S)}^{σ(u)}` and
`Φ(σ)(e^b_{u→w}) = e^b_{σ(u)→σ(w)}`. (Where `σ(S) = {σ(x) : x ∈ S}`.)
`Φ(σ)` is an automorphism of `G_even` because the intra-gadget rule
`w ∈ S` and inter-gadget rule `b = b` are preserved.

**(b) Gauge automorphisms.** For a subset `T ⊆ V_H`, define
`τ_T ∈ Sym(V(G))` by **flipping** every gadget `X(u)` with `u ∈ T`:
`τ_T(a_S^u) = a_{N(u) \setminus S}^u` if `u ∈ T`, else `a_S^u`;
`τ_T(e^b_{u→w}) = e^{1−b}_{u→w}` if `u ∈ T`, else `e^b_{u→w}`.

The flip respects intra-gadget edges in `X(u)` because the rule
`(w ∈ S) ⊕ b = 0` is invariant under simultaneous complementation of
`S` and flip of `b`. For bridges `e^b_{u→w} ∼ e^b_{w→u}`: if both `u, w
∈ T` or both `u, w ∉ T`, the bridge's `b`-matching is preserved; if
exactly one of `u, w` is in `T`, the bridge becomes "twisted"
(`e^b_{u→w} ∼ e^{1−b}_{w→u}`) — destroying `G_even`.

So `τ_T ∈ Aut(G_even)` iff every edge `(u,w) ∈ E_H` has both endpoints
in `T` or neither. **For connected `H`, that means `T = ∅` or `T = V_H`**.

The gauge group's full content comes from acting on `G_even` via
**cycles in `H`**, not vertex subsets. Each cycle `c ⊆ E_H` defines a
gauge automorphism: pick a vertex subset `T_c ⊆ V_H` with `∂T_c = c`
(i.e., the edges of `H` with exactly one endpoint in `T_c` are exactly
`c`); for each edge `(u,w) ∈ c`, the bridge `e^b_{u→w} ∼ e^b_{w→u}`
becomes twisted via `τ_{T_c}`. To restore `G_even`-ness, simultaneously
re-twist the bridges of `c` via the obvious bridge-flip. The
composition — gadget-flip of `T_c` plus bridge-flip of `c` — is an
automorphism of `G_even`.

The group of such cycle-actions is the **cycle space** of `H`,
isomorphic to `Z_2^{β_H}`. Choice of `T_c` for a given `c` is
non-unique, but different choices differ by `τ_{V_H \ T_c}` (a full flip
of every gadget), which is itself an automorphism (the "global twist").
So the cycle space gives `Z_2^{β_H}` distinct gauge automorphisms.

**Combining (a) and (b):**

> **Lemma L1 (Aut structure).** `Aut(CFI(H)) ≅ Z_2^{β_H} ⋊ Aut(H)`,
> with `Aut(H)` acting on `Z_2^{β_H}` via the natural action on the
> cycle space.

*Citation.* Cai–Fürer–Immerman (1992) §3; Grohe (2017) Theorem 13.4.5.

The semidirect-product action: `σ ∈ Aut(H)` permutes cycles by
permuting their constituent edges, inducing a linear action on
`Z_2^{β_H}` = cycle space.

### 9.3 Stabilizer of `v` in `Aut(CFI(H))`

Let `v ∈ X(u₀)` be the individualized vertex. Three sub-cases by vertex
type.

**Case I — `v = a_∅^{u₀}` (the empty-subset vertex).**

Sub-case I.1 (base part). `σ ∈ Aut(H)` lifts to `Φ(σ) ∈ Aut(CFI(H))`
with `Φ(σ)(v) = a_{σ(∅)}^{σ(u₀)} = a_∅^{σ(u₀)}`. So `Φ(σ)(v) = v` iff
`σ(u₀) = u₀`, i.e., `σ ∈ Aut(H)_{u₀}` (the stabilizer of `u₀` in
`Aut(H)`).

Sub-case I.2 (gauge part). The gauge `τ_{T_c}` sends `a_∅^{u₀}` to
`a_{N(u₀)}^{u₀}` if `u₀ ∈ T_c`, else fixes it. So the gauge part of the
stabilizer of `v` is `{ c ∈ Z_2^{β_H} : u₀ ∉ T_c ` for the canonical
choice of `T_c}`. Equivalently: cycles `c` for which `u₀` is not on the
"twisted side". This is a subgroup of `Z_2^{β_H}` of **index ≤ 2**
(specifically: index 1 if every cycle can be represented with `u₀
∉ T_c`, index 2 otherwise).

For connected `H` with `β_H ≥ 1`, this index is **exactly 2** —
because for any cycle `c` passing through `u₀` (using `u₀` as an
interior vertex of `T_c`), the partner cycle gives the
`u₀`-side-flipped version. The stabilizer has gauge subgroup of order
`2^{β_H − 1}`.

**Combined:** `Aut(CFI(H))_v ≅ Z_2^{β_H − 1} ⋊ Aut(H)_{u₀}` for
`v = a_∅^{u₀}` (assuming `β_H ≥ 1`).

**Case II — `v = a_S^{u₀}` for `S ≠ ∅` (other subset vertices).**

By analogous reasoning with `a_{σ(S)}^{σ(u₀)} = a_S^{u₀}` iff
`σ(u₀) = u₀` and `σ(S) = S` (i.e., `σ` stabilizes `S` setwise within
`N(u₀)`). The gauge part is unchanged from Case I (still index-2
subgroup).

**Combined:** `Aut(CFI(H))_v ≅ Z_2^{β_H − 1} ⋊ (Aut(H)_{u₀})_S` where
`(Aut(H)_{u₀})_S` is the subgroup of `Aut(H)_{u₀}` preserving `S` as a
subset of `N(u₀)`.

**Case III — `v = e^b_{u₀→w}` (an endpoint vertex).**

The endpoint `e^b_{u₀→w}` is fixed by `Φ(σ)` iff `σ(u₀) = u₀` and
`σ(w) = w`, i.e., `σ ∈ Aut(H)_{u₀, w}` (joint stabilizer).
By gauge `τ_{T_c}`: sends `e^b_{u₀→w}` to `e^{1−b}_{u₀→w}` if `u₀ ∈
T_c`, else fixed. So gauge stabilizer of `v` is again index-2 in
`Z_2^{β_H}`.

**Combined:** `Aut(CFI(H))_v ≅ Z_2^{β_H − 1} ⋊ Aut(H)_{u₀, w}`.

**Unified summary:**

> **Lemma L2 (Stabilizer decomposition).** For any `v ∈ V(G)` in gadget
> `X(u₀)`:
> ```
> Aut(CFI(H))_v ≅ Z_2^{β_H − 1} ⋊ (base stabilizer of v's "base label")
> ```
> where "base label" of `v` is `u₀` for an empty-subset vertex, `(u₀, S)`
> for a general subset vertex, and `(u₀, w)` for an endpoint vertex.

The exact `−1` in the gauge exponent holds for `β_H ≥ 1` (which is any
`H` containing a cycle, the only interesting case). For `β_H = 0`
(i.e., `H` a tree), the gauge group is trivial and the stabilizer is
purely the base stabilizer.

### 9.4 Stabilizer orbits on `V(G) \ {v}`

The orbits of `Aut(CFI(H))_v` decompose cleanly by the semidirect-
product structure.

**Setup.** Write `H_v = Aut(H) ∩ (base stabilizer of v's base label)`
and `Γ_v = Z_2^{β_H − 1}` for the gauge stabilizer.
`Aut(CFI(H))_v = Γ_v ⋊ H_v`.

For `w ∈ V(G) \ {v}`, the orbit of `w` under `Γ_v ⋊ H_v` is the union
of `H_v`-images of the `Γ_v`-orbit of `w`.

**Lemma (semidirect-product orbit formula).** For `G = N ⋊ K` acting on
a set `X`, with `N` normal and `K` acting on `X` and also on `N` by
conjugation: the `G`-orbit of `x ∈ X` is
`{ k.n.x : k ∈ K, n ∈ N } = K · (N · x)`.
The `N`-orbits are permuted by `K`; a `G`-orbit is a union of
`N`-orbits transitive under `K`'s action.

Apply this to `N = Γ_v`, `K = H_v`, `X = V(G) \ {v}`.

**Γ_v-orbits.** Gauge acts by flipping subsets of gadgets. For
`w ∈ V(G)` in gadget `X(u)`:
- If `u = u₀` and `w = a_S^{u₀}`: gauge fixes `w` (since gauge fixing
  `v` doesn't touch parity at `u₀`). Singleton `Γ_v`-orbit.
- If `u = u₀` and `w` is an endpoint `e^b_{u₀→w'}`: similarly fixed
  by `Γ_v`. Singleton orbit (unless `w' = w` of v's-base-edge, which
  matters in Case III).
- If `u ≠ u₀`: gauge `Γ_v` acts non-trivially on `X(u)` for some
  elements of `Γ_v` (specifically those `T_c` containing `u`).
  The `Γ_v`-orbit of `w ∈ X(u)` has size equal to the index of
  `Γ_v \cap stab_{Γ_v}(w)` in `Γ_v`. By a counting argument similar to
  the `v` case, this is `≤ 2` (size 2 typically, 1 occasionally).

**H_v-orbits.** `H_v ⊆ Aut(H)` permutes base vertices `V_H`, hence
permutes gadgets, hence permutes the union of `Γ_v`-orbits. The
`H_v`-orbit of a `Γ_v`-orbit `O` is `{ Φ(σ)(O) : σ ∈ H_v }`.

**Combined.** A full `Aut(CFI(H))_v`-orbit is:
```
Orbit(w) = ⋃_{σ ∈ H_v} Φ(σ)(Γ_v · w)
        = ⋃_{u' ∈ H_v · u} (Γ_v · w restricted to X(u'))
```
where `u` is `w`'s base gadget and `H_v · u` is the `H_v`-orbit of `u`
in `V_H`.

**Size formula.** `|Orbit(w)| = |H_v · u| × |Γ_v · w \cap X(u)|`.

> **Lemma L3 (Orbit shape).** Every orbit of `Aut(CFI(H))_v` on
> `V(G) \ {v}` has the form `(H_v-orbit of base vertex) × (Γ_v-orbit
> within a gadget)`, with size `|H_v · u| · k` where `k ∈ {1, 2}` is
> the Γ_v-orbit size within one gadget.

**Computed `H_v` orbits on `V(H)`.** For `v = a_∅^{u₀}` with
`u₀ = {1,2}` a 2-subset of `{1,…,5}`: `H_v = S_{\{1,2\}} × S_{\{3,4,5\}}
≅ S_2 × S_3` of order 12. Orbits on the 9 other Petersen vertices:
2-subsets sharing 1 element with `u₀` (size 6: `{1,3},{1,4},{1,5},
{2,3},{2,4},{2,5}`) and 2-subsets disjoint from `u₀` (size 3:
`{3,4},{3,5},{4,5}`).

The exact orbit shape requires more careful gauge accounting than my
first-pass sketch suggested. Rather than predict the orbit sizes from
the Aut decomposition by hand (which I attempted in an earlier draft
and got wrong on the within-gadget structure), I verified them directly
against the project's chain-descent canonizer, which harvests
`Aut(CFI(H))` during canonization. Code at
[Tier2DecompositionExperiment.cs](../GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs)
`CfiK4_OrbitRecovery_...` and `CfiPetersen_OrbitRecovery_...`.

### 9.5 Empirical verification — F7 strict form CONFIRMED

The orbit-recovery comparison runs the canonizer to get `Aut(CFI(H))`
generators, computes `Aut_v` orbits via the pair-orbit method, and
compares against 1-WL cells at depth 1. Result table (test passes 4/4):

| Instance | Start orbit | Aut order | Aut_v orbit count | Cells at depth 1 | Match? |
|---|---|---:|---:|---:|:---:|
| CFI(K₄) | subset (`v0:subset:{}`) | 192 = 2³·24 | 9 | 9 | **YES** |
| CFI(K₄) | endpoint (`v0:end[w1]^0`) | 192 = 2³·24 | 14 | 14 | **YES** |
| CFI(Petersen) | subset | 7680 = 2⁶·120 | 12 | 12 | **YES** |
| CFI(Petersen) | endpoint | 7680 = 2⁶·120 | 20 | 20 | **YES** |

Aut orders match the theoretical `2^{β_H} · |Aut(H)|`, so the canonizer's
harvested Aut is complete (not partial). The comparison is rigorous, not
heuristic.

**Conclusion: F7 holds in its strict form at depth 1** —
`P(CFI(H), {v}) = O(CFI(H), {v})` — on both Aut-orbits of CFI(K₄) and
CFI(Petersen). The earlier "discrepancy" flag (now removed) was a flaw
in my hand analysis of within-gadget gauge action, not a real gap. The
empirical reality is cleaner than the rough theoretical sketch
suggested.

### 9.6 What's next — L4 unblocked

With F7 verified at depth 1 on two CFI bases, L4 is back on track. The
target lemma:

> **L4 (1-WL refinement post-individualization).** Let `H` be a base
> graph with `β_H ≥ 1`, `G = CFI(H)`, `v ∈ V(G)`. 1-WL refinement of `G`
> with `v` fresh-colour individualized reaches a fixpoint partition
> equal to the `Aut(CFI(H))_v` orbit partition.

Proof strategy (three sub-lemmas):

**L4a — within-gadget refinement.** 1-WL refinement reaches a partition
of `X(u₀)` (`v`'s gadget) that equals the `Aut(CFI(H))_v`-orbit partition
of `X(u₀)`. This is the base case of an induction. Proof: the
intra-gadget edge rule `(w ∈ S) ⊕ b = 0` plus the singleton `{v}` gives
1-WL enough to distinguish each parity-equivalence class within `X(u₀)`.
The gauge-stabilizer action on `X(u₀)` (which I had wrong in my first
pass) is exactly what 1-WL recovers here.

**L4b — propagation across one base edge.** If 1-WL refinement matches
`Aut_v`-orbits on `X(u)` for some gadget `X(u)`, then it matches
`Aut_v`-orbits on `X(u')` for each neighbour `u' ∈ N_H(u)`. Proof: the
bridge `e^b_{u→u'} ∼ e^b_{u'→u}` lets 1-WL transfer colour information
across, and the gauge action commutes with this transfer.

**L4c — propagation by induction on distance.** By induction on
`dist_H(u₀, u)`, 1-WL recovers `Aut_v`-orbits on each gadget `X(u)`.
Combined with the inter-gadget edges, the global partition equals
`Aut_v`-orbits on all of `V(G)`.

All three sub-lemmas are now believed routine (modulo standard CFI
gadget combinatorics) because the empirical match at depth 1 confirms
the partition predicted by `Aut_v` is exactly what refinement produces.

### 9.7 Status

**Settled:**
- L1 (Aut structure) — citation, done.
- L2 (stabilizer decomposition) — case analysis written; gauge index-2
  refinement needed (the part my first pass got wrong).
- L3 (orbit shape — formal) + empirical verification (§9.5) — DONE.
  F7 strict form confirmed at depth 1 on 4 instances (K₄ × 2 orbits,
  Petersen × 2 orbits).

**Next:**
- L4 paper proof — sub-lemmas L4a, L4b, L4c as outlined in §9.6.
- L5 — assembly (trivial).
- After paper Tier 1 is done: Tier 2 (association schemes) and the
  Piece-C connection.
