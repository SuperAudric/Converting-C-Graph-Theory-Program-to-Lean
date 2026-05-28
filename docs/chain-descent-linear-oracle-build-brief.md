# Linear oracle — C# build brief (temporary)

> **Status: temporary build brief.** Working notes for the C#
> implementation of the linear oracle. Delete or fold into a permanent
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
- **Provenance.** `TransitiveClose` ([ChainDescent.cs:257](../GraphCanonizationProject/ChainDescent.cs#L257)) writes derived `LESS`/`GREATER` entries but records *no* `DERIVED`/`driver` info. The coupled component cannot be delineated without this. **Build item 1.**
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
1. provenance, to delineate the coupled component;
2. a twist-construction step, to build the candidate permutation from
   the refinement + provenance;
3. verification (reuse `IsAutomorphism`);
4. a hook that runs this after exploring the first representative and
   feeds verified twists into `Automorphisms`.

This is a much smaller change than "build a new oracle from scratch."

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

---

## 4. Build milestones (ordered)

Each milestone is independently testable. Stop and validate before
proceeding.

### M1 — Provenance plumbing
- Extend the closure to record, per derived `P` entry, the **driver**:
  the primary guess (the `(v, cellmate)` write in `Branch`) that
  completed its chain.
- Suggested shape: a parallel `int[] driverOf` of length `n*n`
  (driver entry index, or −1 for primaries / unknown), maintained by a
  provenance-aware closure that replaces the bare `TransitiveClose`
  inside `Branch`. Keep the existing `TransitiveClose` for the
  type-seed path; only the in-descent closure needs provenance.
- **Test:** on `CFI(Cycle3)`, after individualizing one parity rep,
  the derived entries forced around the cycle all share one driver.

### M2 — Coupled-component extraction
- `CoupledComponent(driver) → cells + order labels`: scan `driverOf`
  for entries with the given driver; collect the cells those entries
  split and the order direction on each.
- **Test:** on `CFI(Cycle3)`, the coupled component is the whole cycle
  of gadgets.

### M3 — Twist construction (the core, §4.2)
- From the explored representative `r_1`'s refined partition + the
  coupled component, construct the candidate permutation `t` by
  mirror-matching: within each split cell, map each sub-cell to its
  order-mirror; everything outside the component is fixed.
- For CFI this is "flip the parity of every gadget on the coupled
  cycle." Start with the **all-singletons** case (§4.3): if any
  split sub-cell has ≥ 2 vertices, return "no unique candidate" (M5
  handles the consequence).
- **Test:** on `CFI(Cycle3)`, the constructed `t` is the parity-flip
  involution.

### M4 — Verification + harvest
- Verify `t` with the existing `IsAutomorphism`
  ([ChainDescent.cs:246](../GraphCanonizationProject/ChainDescent.cs#L246)).
  On success, `Automorphisms.AddGenerator(t)`.
- Hook: in `Search`, after exploring the first representative, run
  M2+M3+M4 for the just-explored rep against each unexplored rep
  *before* the loop continues. The existing `CoveredByPathFixingAut`
  then prunes the covered reps.
- **Test:** on `CFI(Cycle3)` odd (18-cycle), the descent canonizes
  with the parity decisions collapsed; `LastPrunedBranches` reflects
  a-priori pruning (compare against the a-posteriori-only baseline).

### M5 — Uniqueness test + graceful degradation
- When M3 finds a non-singleton sub-cell (no unique candidate), the
  oracle returns nothing; the harness proceeds as the normal `k`-way
  branch (and ultimately the budget flags if the exponential stacks).
  **This is correct, not a failure** — see [linear-oracle.md §4.4](./chain-descent-linear-oracle.md)
  option 1, [§6.3](./chain-descent-linear-oracle.md).
- **Test:** the harness still canonizes everything it canonized before
  (no regressions on the `KnownGraphs` corpus / existing tests).

### M6 — Empirical bar (the payoff)
- `CFI(K4)`, `CFI(K33)`, `CFI(Petersen)` should now **canonize without
  flagging** (they currently flag — only the cascade oracle ships).
- Scramble-invariance must hold (same canonical across relabellings).
- Even/Odd pairs must still produce **different** canonicals
  (non-isomorphic).
- Node count should drop toward `O(n · β)` from exponential.

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
  exist. The genuinely new code is M1 (provenance) and M3 (construction).

---

## 6. Suggested file layout

- New `LinearOracle.cs` — but note it can't be a pure pre-branch
  `ITransversalOracle.Classify` (it's online, §3 + [linear-oracle.md §6.1](./chain-descent-linear-oracle.md)).
  Recommended: a helper class `TwistDiscovery` invoked from
  `ChainDescent.Search` after the first branch, rather than forcing it
  behind the `Classify` seam. Keep the `ITransversalOracle` interface
  unchanged for now.
- Provenance fields (`driverOf`) live in `ChainDescent` (or a small
  `ProvenancePMatrix` wrapper) since closure happens there.
- Tests in `GraphCanonizationProject.Tests/` alongside the existing
  `GraphCanonTests.ChainDescent.cs`; mirror the `CD_CfiCycle3_*`
  pattern for K4/K33/Petersen.

---

## 7. Definition of done

- M1–M6 complete.
- `CFI(K4)`, `CFI(K33)`, `CFI(Petersen)` canonize without flagging,
  scramble-invariantly, distinguishing Even from Odd.
- No regressions on the existing test suite.
- Node-count instrumentation (`LastNodesByDepth`) shows the descent
  collapsed toward a path on these CFI cases.
- The twist-construction approach (§4.2 mirror-matching) is confirmed
  working on real CFI graphs — this is the empirical validation the
  spec's §10 risk 1 asks for, and the green light for the Lean
  contract discharge.
