# Linear oracle — C# build brief (temporary)

> **Status: temporary build brief.** Working notes for the C#
> implementation of the linear oracle. Archive or fold into a permanent
> doc once the implementation lands. The authoritative spec is
> [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md);
> this brief grounds that spec in the *actual current code* and gives a
> concrete, milestone-ordered build path.

**Read first, in order:**
1. [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) — the spec (what the oracle does, §4 construction, §4.3 boundary, §4.5 verification).
2. This brief — how it maps onto the existing harness.
3. [`chain-descent-strategy.md`](./chain-descent-strategy.md) §9–§12 — the substrate (`P`-matrix, warm refinement, invariant 6.2, the spine) if you need the theory.

---

## 1. Codebase orientation (what exists today)

All paths under `GraphCanonizationProject/`.

| File | Role | Key facts for this build |
|---|---|---|
| [`ChainDescent.cs`](../GraphCanonizationProject/ChainDescent.cs) | The descent harness | `Search` (one node), `Branch` (individualize + recurse), `HandleLeaf` (harvest auts a-posteriori), `CoveredByPathFixingAut` (a-posteriori pruning), `TransitiveClose` (Floyd–Warshall, **no provenance**), `IsAutomorphism` (the O(n²) edge check — reuse for verification). |
| [`WarmPartition.cs`](../GraphCanonizationProject/WarmPartition.cs) | Warm 1-WL refinement on `(adj, P)` | `CellOf[]`, `NumCells`, `Refine(adj, p)`, `Clone()`. Cell ids iso-invariant (canonical lex-sort of signatures). The signature already packs `(neighbour-color, edge-label, Prel)` per neighbour. |
| [`ITransversalOracle.cs`](../GraphCanonizationProject/ITransversalOracle.cs) | The oracle seam | `Classify(n, adj, targetCell, path, knownGroup) → TransversalDecision` (a representative list). Called **before** branching. |
| [`CascadeOracle.cs`](../GraphCanonizationProject/CascadeOracle.cs) | Phase-1 oracle | Returns the whole cell; all pruning is a-posteriori. The linear oracle is the second implementation. |
| [`PermutationGroup.cs`](../GraphCanonizationProject/PermutationGroup.cs) | Residual group | `AddGenerator`, `Orbit`, `Contains`, Schreier–Sims chain, `Order`. Already consumed by `CoveredByPathFixingAut`. |
| [`CanonGraphOrdererChainDescent.cs`](../GraphCanonizationProject/CanonGraphOrdererChainDescent.cs) | Entry point | `RunConnected` builds the `CascadeOracle` at line ~83. Swap/augment here. |
| [`CfiGraphGenerator.cs`](../GraphCanonizationProject/CfiGraphGenerator.cs) | Test graphs | `Generate("K4"|"K33"|"Petersen"|"Rook3x3"|"Cycle{n}")` → `CfiPair(Even, Odd, …)`. |

**The `P`-matrix substrate already exists.** `sbyte[] p`, indexed
`p[i*n + j]`, values `LESS = -1`, `UNKNOWN = 0`, `GREATER = 1`, held
antisymmetric. This is the spec's `PMatrix`. Good — no substrate to
build.

**What does NOT exist yet:**
- **Coupled-component extraction.** The coupled component must be read
  from the **refinement footprint** (parent↔child partition diff), not
  from TC provenance. **Build item M1.** *(Correction 2026-05-28: an
  earlier draft proposed TC `DERIVED`/`driver` provenance on
  [`TransitiveClose`](../GraphCanonizationProject/ChainDescent.cs#L257).
  The build branch measured that TC produces **zero** derived entries
  for within-cell decisions on uniform-type graphs — cellmates are
  unordered among themselves, other cells P-incomparable — so TC
  provenance is provably empty here. The cascade propagates through
  refinement, so read the footprint from the partition diff. See spec
  §3.)*
- **Any a-priori twist discovery.** Automorphisms are only harvested a-posteriori from leaf collisions ([`HandleLeaf`](../GraphCanonizationProject/ChainDescent.cs#L212)).

---

## 2. The key integration insight

**The linear oracle is the a-priori version of machinery that already
exists a-posteriori.**

The harness already prunes redundant branches via
[`CoveredByPathFixingAut`](../GraphCanonizationProject/ChainDescent.cs#L181):
once a path-fixing automorphism is in `Automorphisms`, any
representative reachable from an explored one is skipped. Today those
automorphisms arrive *late* — harvested from coinciding leaves, after
the exponential damage is done.

The linear oracle's job is to **harvest the automorphism early** — read
it off the *first explored representative's refinement*, verify it, and
add it to `Automorphisms` *before* the branch loop reaches the other
representatives. Then the existing `CoveredByPathFixingAut` prunes them
for free.

So the build does **not** need a new pruning mechanism. It needs:
1. **refinement-footprint extraction**, to delineate the coupled
   component (parent↔child partition diff — *not* TC provenance);
2. a twist-construction step, to build the candidate permutation from
   the explored branch's refined sub-cells (canonical-id matching);
3. verification (reuse `IsAutomorphism`) — the unconditional soundness
   gate;
4. a hook that runs this after exploring the first representative and
   feeds verified, path-fixing twists into `Automorphisms`.

This is a much smaller change than "build a new oracle from scratch."
**Soundness rests entirely on step 3** — the construction (step 2) may
be heuristic; a wrong candidate just fails verification.

---

## 3. The spec-vs-implementation gap (read carefully)

The spec ([linear-oracle.md §4](./chain-descent-linear-oracle.md))
describes a **single-pair** decision `{e, f}` with two directions
(`e < f` vs `f < e`) and reverse-symmetric propagation. The **current
harness does not branch on single pairs** — [`Branch`](../GraphCanonizationProject/ChainDescent.cs#L159)
individualizes a representative `v` *below all its cellmates* at once
(the whole-cell branching of [calculator §10.1](./chain-descent-calculator.md),
which is forced-correct for iso-invariance).

**Do not refactor the harness to single-pair guesses.** That is a large,
risky change and is not needed. Instead, bridge the gap like this:

- The harness branches over the target cell's representatives
  `[r_1, r_2, …]`.
- Explore `r_1` (individualize it, refine). This plays the role of
  "explore one branch."
- The candidate twist you construct maps `r_1 ↦ r_j` for an unexplored
  `r_j` — i.e. a path-fixing automorphism carrying `r_1`'s subtree onto
  `r_j`'s. This is exactly the input `CoveredByPathFixingAut` wants.
- Reverse-symmetric propagation (the spec's theory) is the
  *justification* that `r_1` and `r_j` have mirror-image refinements;
  the implementation just needs to *construct the candidate* and
  *verify it edge-by-edge*. Verification (§4.5) is what makes it sound
  regardless of how the candidate was guessed.

So: the spec's "twist swapping `e, f`" becomes, in this harness, "a
path-fixing automorphism mapping the explored representative to an
unexplored one." Same object, framed for the actual control flow.

**Cell size — soundness vs. proof backing (resolves a build-branch
question).** Two different bars:

- **Soundness (the implementation):** works for a cell of **any size**.
  Verification (§4.5) gates every harvested twist — a wrongly
  constructed candidate for a size-`k` cell just fails the edge-check
  and is discarded. So *attempt construction at any size*; it can never
  produce a wrong answer, and attempting costs only an `O(n²)` verify.
- **Clean proof backing (the Lean discharge):** `warm_6_2` is the
  **size-2** result (the two directions of one pair — which is exactly
  branching on `r_1` vs `r_2` of a 2-cell). For size-`k>2`, branching
  on `r_i` is `k` different individualizations; the backing is the
  spine (`warmRefine_agree_off'`, partition-sharing for a decision
  set), which gives the *candidate* but not the automorphism property
  — verification closes that.

So: **implement construction at any cell size** (sound via verify);
**scope the Lean Phase-1 proof to size-2** (clean `warm_6_2` backing).
Do not *restrict the implementation* to size-2 — that would forgo sound
pruning that costs only a verify to attempt. Empirically CFI decision
cells are commonly size-2, so size-2 covers K4/K33/Petersen regardless;
attempting larger cells is free upside.

**A second, orthogonal axis — sub-cell singletons — is the real gate
([viability plan](./chain-descent-extended-twist-viability.md)).** Target
*cell* size (above) is about which `warm_6_2`/spine backing applies. The
*footprint's sub-cell* structure is a different axis and is what gates the
**construction itself**: the `r_1 ↦ r_j` match is iso-invariantly forced
**iff every coupled sub-cell is a singleton**. A non-singleton sub-cell is
refinement-indistinguishable, so an index-based within-cell match would be
sound (verify gates it) but would make the **flag verdict
labelling-dependent** — breaking flag iso-invariance
([strategy §15 gap 2](./chain-descent-strategy.md)). So "attempt at any
size" means *run the oracle at every decision regardless of target-cell
size and construct directly when the footprint is all-singletons* — **not**
*index-match within non-singleton sub-cells*. Non-singleton sub-cells are
handled by **recursion** (the normal descent branch, which re-fires the
oracle deeper), which is iso-invariant and, on the cascade class, provably
terminates (orbit recovery). See M5.

---

## 4. Build milestones (ordered)

Each milestone is independently testable. Stop and validate before
proceeding.

### M1 — Refinement-footprint extraction
*(Replaces the abandoned TC-provenance plumbing — TC is inert here,
§1 / spec §3.)*
- Capture the **parent partition** (before the branch) and the **child
  partition** (after individualizing the representative + warm
  refining), and diff them.
- The **coupled component** is the set of cells that newly split
  between parent and child — the cells the decision propagated to.
- Suggested shape: both partitions are already `WarmPartition.CellOf`
  arrays; the footprint is "which parent cells map to >1 child cell."
  No closure changes, no `driverOf` array.
- **Test (mechanism smoke):** on `CFI(Cycle3)`, individualizing one
  vertex and refining splits cells (the cascade propagates); the
  footprint is the non-empty set of cells that split. This validates
  the diff mechanism — `Cycle3` cascades by distance, so it has no
  genuine parity decision; the *meaningful* footprint is M3's on
  `CFI(K4)`.

### M2 — Coupled-component sub-cell structure
- For each cell in the footprint, record its child sub-cells (by
  canonical id). This is the data M3 matches against the mirror branch.
- **Test:** on `CFI(K4)`, at a genuine decision the footprint's split
  cells break into singleton sub-cells (the all-singletons case M3
  needs); `CFI(Cycle3)` smoke-tests that sub-cells are recorded
  per split cell in canonical-id order.

### M3 — Twist construction (the core, §4.2)
*(Reframed — no P order-labels exist; refinement is split-only. Match
by canonical-id structure, sound via verification.)*
- For an unexplored rep `r_j`: construct candidate `t` carrying
  `r_1 ↦ r_j` by matching `r_1`'s child sub-cells (M2) to `r_j`'s
  mirror sub-cells **by canonical-id structure** (same refined-colour
  signature), vertex-by-vertex within matched sub-cells. Identity
  outside the footprint. **Construct `t` path-fixing by design** (it
  must fix every individualized path vertex).
- Start with the **all-singletons** case (§4.3): if any sub-cell has
  ≥ 2 vertices, return "no unique candidate" (M5 handles it). The
  matching is then forced.
- For CFI this is "flip the parity of every gadget on the coupled
  cycle."
- **Test target: `CFI(K4)`, not `CFI(Cycle3)`.** A cycle base has
  β = 1 realized as graph *topology* (odd = one 18-cycle, even = two
  9-cycles); within canonizing the 18-cycle there is **no genuine
  abelian decision** — it is pure cascade (D18, ~9 nodes), so there is
  no parity twist for M3 to construct. The genuine `Z_2^β`
  false-symmetry decisions first appear at **treewidth-≥3 bases**:
  `CFI(K4)` (β = 3). **Test:** on `CFI(K4)`, the construction yields a
  candidate `t` carrying one explored parity rep onto an unexplored
  one that passes `IsAutomorphism` (a gadget-parity flip on the coupled
  cycle).
- **Note:** the construction is a heuristic made sound by M4's verify;
  it need not be provably correct to be safe to attempt. Run the oracle
  at decisions of **any target-cell size** (§3). But the **construction
  itself fires only when the footprint is all-singletons** — that match
  is the iso-invariantly forced one. Do **not** index-match within a
  non-singleton sub-cell: it is sound but breaks flag iso-invariance
  ([viability plan](./chain-descent-extended-twist-viability.md), §4.2
  note). Non-singleton ⇒ return "no candidate" and let M5's recursion
  handle it.

### M4 — Verification + harvest
- Verify `t` with the existing `IsAutomorphism`
  ([ChainDescent.cs:246](../GraphCanonizationProject/ChainDescent.cs#L246)).
  On success, `Automorphisms.AddGenerator(t)`.
- Hook: in `Search`, after exploring the first representative, run
  M2+M3+M4 for the just-explored rep against each unexplored rep
  *before* the loop continues. The existing `CoveredByPathFixingAut`
  then prunes the covered reps.
- **Test:** on `CFI(K4)` (genuine `Z_2^3` decisions, not the cascading
  cycle base), the descent canonizes with parity decisions collapsed
  a-priori; the explored **leaf count drops** below the a-posteriori
  baseline (16, per M6), scramble-invariantly, still distinguishing
  Even from Odd. (`CFI(Cycle3)` remains a useful smoke test for the
  M1/M2 footprint mechanism, but has no twist to discover.)

### M5 — Uniqueness test + graceful degradation (recursion)
- When M3 finds a non-singleton sub-cell (no forced candidate), the
  oracle returns nothing and the harness proceeds as the normal `k`-way
  branch. **This branch *is* the recursion** ([linear-oracle.md §4.4](./chain-descent-linear-oracle.md)):
  individualizing into the sub-cell refines the footprint, and the oracle
  **re-fires at the deeper level** once the sub-cell has cascaded to
  singletons. It is iso-invariant (the descent branches over the whole
  sub-cell) and, on the cascade class, provably terminates by the
  orbit-recovery depth (`theorem_1_HOR_cfi_oddDeg` ≤ tw(H);
  `theorem_2_HOR` depth 1). If it has *not* cascaded by then (rigid IR
  blind spot or non-abelian wall), the budget flags. **This is correct,
  not a failure.**
- **Implement the *behaviour*, do not assert the *boundary*.** The
  claim "all sub-cells singleton ⟺ abelian / non-singleton ⟺ the
  non-abelian wall" is **Tier-3 / orbit-recovery open content, not
  proven** (spec §4.3). What is unconditionally sound is the behaviour:
  singleton → unique candidate the verifier checks; non-singleton →
  fall back to budget-bounded search (always correct). Code the
  behaviour; don't claim the boundary is established.
- **Test:** the harness still canonizes everything it canonized before
  (no regressions on the `KnownGraphs` corpus / existing tests).

### M6 — Empirical bar (the payoff: leaf-count collapse + construction validation)

> **The bar is leaf count, not "stops flagging."** Measured 2026-05-28:
> CFI(K4…K6) *already* canonize under the default budget via the
> a-posteriori path — the build brief's original "they currently flag"
> premise was false. A-posteriori pruning keeps leaf counts well below
> `2^β` (Petersen β=6: 29 leaves vs 64; K6 β=10: 378 vs 1024). The path
> first strains only at CFI(K7, n=308), and there the binding constraint
> is the `_seen` leaf cache (`O(distinct-leaves · n²)`, ~760 KB/leaf at
> n=308), **not** the node budget. So the linear oracle's measurable job
> is to collapse the explored **leaf count** — which both removes that
> memory wall and is the empirical analogue of the Lean `LeafTwistSpec`
> this build exists to de-risk.

Three things to demonstrate:

1. **Construction validation (the de-risking evidence — primary goal).**
   On CFI(K4/K33/Petersen), canonical-id sub-cell matching (§4.2)
   constructs a candidate twist that passes `IsAutomorphism`. This is
   the direct empirical stand-in for `LeafTwistSpec` (a verified twist
   relabels one branch's canonical onto another's,
   [linear-oracle.md §2.3](./chain-descent-linear-oracle.md))
   — the green light for the Lean discharge.

2. **Leaf-count collapse (the scaling signal).** A-priori harvesting
   drops the explored leaf count toward ~`O(β)` (one resolved decision
   per coupled component, not a growing tree), and `_seen` stays
   `O(n)`-small. Measured a-posteriori baseline to beat (odd graph,
   default budget, 2026-05-28):

   | base | β | n | a-posteriori leaves | nodes |
   |---|---|---|---|---|
   | K4 | 3 | 40 | 16 | 40 |
   | K33 | 4 | 60 | 42 | 116 |
   | Petersen | 6 | 100 | 29 | 115 |
   | Rook3x3 | 10 | 144 | 412 | 652 |
   | K6 | 10 | 156 | 378 | 695 |
   | K7 | 15 | 308 | ≥1835 (memory-capped, did not complete) | ≥3163 |

3. **Correctness invariants preserved.** Scramble-invariance (same
   canonical across relabellings) and Even ≠ Odd (non-isomorphic
   distinguished) must still hold.

**Payoff target.** CFI(K7) — and a fresh CFI(K8) — canonize with leaf
count and `_seen` memory bounded, where the a-posteriori path hits the
leaf-cache wall. That is the real before/after, replacing the false
"K4 flags."

### M6 — Results (measured 2026-05-28)

The oracle is wired in (`EnableLinearOracle`, default on) and validated.
The `_seen` leaf cache was switched to a 64-bit hash key (memory
`O(leaves·n)` not `O(leaves·n²)`), so K7 completes and the *true* leaf
counts are measurable. Full suite green incl. exhaustive size-5/6
canonical-uniqueness.

**Leaf count, off vs on (odd graph):**

| base | β | n | leavesOff | leavesOn | ratio |
|---|---|---|---|---|---|
| K4 | 3 | 40 | 16 | 12 | 0.75 |
| K33 | 4 | 60 | 42 | 22 | 0.52 |
| Petersen | 6 | 100 | 29 | 22 | 0.76 |
| Rook3×3 | 10 | 144 | 412 | 47 | 0.11 |
| K6 | 10 | 156 | 378 | 76 | 0.20 |
| K7 | 15 | 308 | 6531 | 941 | 0.14 |

Correctness, `|Aut|`, and Even≠Odd preserved throughout (validated
through K7). The construction-validation goal is **met**: every
all-singleton decision yields a twist that passes `IsAutomorphism`
(K4: 16/16) — the empirical `LeafTwistSpec` evidence.

**But the O(β) path-collapse is *not* reached** (K7 on = 941 leaves, not
~β). The reduction is a large constant factor (~7× at β≥10) — possibly a
mild exponent improvement (on ≈ 2^0.73β vs off ≈ 2^0.82β over β=10→15),
but both still grow steeply; polynomial-vs-quasipolynomial is unresolved
by this sample (the K_m family couples n and β).

**Attribution (K7 on, why 941 leaves):**

| branching nodes | extra reps | cause |
|---|---|---|
| 0 (all-singleton footprint) | 0 | linear oracle fired → fully collapsed |
| 555 (non-singleton footprint) | 940 | linear oracle starved → recursion branches |

**100 %** of the residual branching is at **non-singleton footprints**:
the linear oracle is *starved*, not weak — wherever it gets a clean
footprint it collapses the node completely (941 twists harvested, 0
branching). The leaf-count growth is entirely decisions whose coupled
component still carries unresolved residual symmetry, so no forced twist
exists. Per `theorem_1_HOR_cfi` that symmetry is always resolvable for
CFI (no wall); the descent resolves it *a-posteriori* by branching rather
than *a-priori* by certifying one rep per orbit.

**Conclusion / next lever.** The linear oracle is the necessary first
half and works exactly as designed. The binding constraint is now the
**a-priori cascade oracle** (the unbuilt piece of
[calculator §5/§9](./chain-descent-calculator.md)): resolve the residual
symmetry before branching → footprints become all-singleton → the linear
oracle finishes them → the tree collapses toward the depth-bounded path.
This is the same a-priori orbit-harvesting the **spine** fact enables
(read orbits off one branch's mirror). It is the path to polynomial CFI.

---

## 5. Constraints and gotchas

- **Verification is mandatory (§4.5).** Never harvest an unverified
  candidate. `warm_6_2` gives the candidate, not its correctness. A
  candidate that fails `IsAutomorphism` is silently discarded (return
  nothing), not an error.
- **Iso-invariance (strategy §15 gap 2).** The twist construction must
  read from canonical-id-ordered cells (`WarmPartition` ids are already
  iso-invariant) so the descent's flag/canonical verdict is
  labelling-independent. Don't introduce any vertex-index-order
  dependence in M3.
- **Soundness of pruning.** Only *path-fixing* automorphisms may prune
  (the harvested `t` must fix every individualized path vertex).
  `CoveredByPathFixingAut` already enforces this; if you harvest `t`
  into `Automorphisms` it will be filtered there, but prefer to only
  construct path-fixing candidates in the first place.
- **Don't refactor to single-pair guessing** (see §3).
- **Graceful degradation is a feature.** Returning "no twist" is always
  safe — it falls back to budget-bounded IR search. Correctness never
  depends on the oracle succeeding; only performance does.
- **Reuse, don't duplicate.** `IsAutomorphism`, `CoveredByPathFixingAut`,
  `PermutationGroup.AddGenerator`, the `P`-matrix, `WarmPartition` all
  exist. The genuinely new code is M1 (refinement-footprint diff) and
  M3 (canonical-id construction).

---

## 6. Suggested file layout

- New `LinearOracle.cs` — but note it can't be a pure pre-branch
  `ITransversalOracle.Classify` (it's online, §3 + [linear-oracle.md §6.1](./chain-descent-linear-oracle.md)).
  Recommended: a helper class `TwistDiscovery` invoked from
  `ChainDescent.Search` after the first branch, rather than forcing it
  behind the `Classify` seam. Keep the `ITransversalOracle` interface
  unchanged for now.
- The refinement footprint (parent vs child `CellOf`) is computed in
  `ChainDescent.Search`/`Branch` where both partitions are in hand — no
  new closure plumbing, no `driverOf` array.
- Tests in `GraphCanonizationProject.Tests/` alongside the existing
  `GraphCanonTests.ChainDescent.cs`; mirror the `CD_CfiCycle3_*`
  pattern for K4/K33/Petersen.

---

## 7. Definition of done

- M1–M6 complete.
- **Construction validated (primary):** on CFI(K4/K33/Petersen), §4.2
  canonical-id sub-cell matching constructs a twist that passes
  `IsAutomorphism` — the empirical stand-in for `LeafTwistSpec`, and the
  green light for the Lean contract discharge (spec
  [§10 risk 1](./chain-descent-linear-oracle.md),
  [§8.2](./chain-descent-linear-oracle.md)).
- **Leaf count collapses** from the M6 a-posteriori baseline toward
  ~`O(β)`: `LastLeafCount` drops sharply and `LastNodesByDepth` shows the
  descent reduced to ~a path; `_seen` stays `O(n)`-small.
- CFI(K7)/CFI(K8) canonize within bounded leaf-cache memory (the
  a-posteriori wall), scramble-invariantly, distinguishing Even from Odd.
- No regressions on the existing test suite.
