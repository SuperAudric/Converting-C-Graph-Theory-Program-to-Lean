# Converge Loop — History-Tracking Extension (proposal)

Proposal to extend the path-multiset refinement performed by `convergeLoop` so
it separates the cycle-CFI inputs that the current algorithm cannot. Targets
the specific failure class catalogued in
[OrbitCompleteAfterConv.md](OrbitCompleteAfterConv.md) under
`Cycle3 / Cycle5 / Cycle7` (1b ❌). Does **not** address `K4` (1b ❌, base
treewidth 3) — see "Scope and limits" below.

This is a spec / motivation document. Implementation lives in a follow-up.

---

## Failure class being addressed

The 1b probe builds `G = Even ⊕ Odd` for a CFI pair, runs one `convergeLoop`,
and asserts that no rank value is shared between the two halves. For
odd-cycle bases (Cycle3/5/7) the CFI Even component is `2 · C_{3n}` (two
disjoint odd cycles), the Odd component is `C_{6n}` (one even cycle of double
length), and both halves get assigned the same rank value (rank 0 in
practice).

The structural reason: in the disjoint union `2·C_{3n} ⊕ C_{6n}`, any vertex
`v` in either half sees a partition of the 4·(3n) other vertices into shells
that — when summarised as a multiset of cell-rank values — happens to coincide
between `v ∈ C_{3n}` and `v ∈ C_{6n}` at every depth `d`. The current cell
signature at depth `d`,

  `cell_sig[d, v, u] := (ranks[u], sorted multiset over mid of (BR[d-1, v, mid], edge[mid, u]))`,

uses only the most-recent `BR[d-1]` rank, and that rank repeatedly conflates
"shell `k` of the small cycle" with "shell `k'` of the large cycle" in a way
the next iteration can't undo.

## Why the most-recent rank is not enough

Walks of length `L` from `v` to `u` in `C_n` and `C_{2n}` are related by

  `walks_{C_n}(L, δ) = walks_{C_{2n}}(L, δ) + walks_{C_{2n}}(L, δ + n)`.

When `2n` is even, `C_{2n}` has 0 walks of any odd `L` between vertices of
non-matching parity displacement. Those zeros, plus the disjoint-union zeros
from the cross-component cells, line up exactly to make the multiset of
single-`L` walk counts identical between `v ∈ C_n` and `v ∈ C_{2n}`. The
identity of *which* `u` produced which walk count differs, but a multiset
hides that.

The same coincidence carries through under refinement: `BR[d-1]` is a dense
rank of cell signatures, so it inherits whatever multiset coincidences existed
one level down. At depth `d` the cell signature consults `BR[d-1]` only, so a
coincidence at `d-1` is consumed without the algorithm having seen it
contradicted at any earlier depth.

The walk-count-history of cell `(v, u)` — the vector
`(BR[0, v, u], BR[1, v, u], …, BR[d, v, u])` — does **not** collapse the same
way. In `2·C_9 ⊕ C_{18}`, the `(v, v)` history `(1, 0, 2, 0, 6, 0, 20, 0, 70, 2, …)`
appears once in the `v ∈ C_9` multiset; the `v ∈ C_{18}` multiset has
`(1, 0, 2, 0, 6, 0, 20, 0, 70, 0, …)` once *plus* an antipode history
`(0, 0, 0, 0, 0, 0, 0, 0, 0, 2, …)` once. As elements of a multiset of
vectors those are three distinct entries; their pointwise sum equals the `C_9`
diagonal history, but a multiset over vectors does not equate sums to
elements.

So the principled fix is: **make the cell signature consult the full history
of `BR` ranks, not just the most recent one.**

---

## Specification

The change is local to the cell-signature definition. Everything else
(`assignRanks`, `FromRanks`, `convergeOnce`, `convergeLoop`, `breakTie`,
`OrderVertices`) is untouched.

### Variant A — minimal (two-depth window)

Smallest change that handles the cycle-CFI cases. Adds the previous depth's
rank to the per-`mid` tuple.

```
For d = 0:        cell_sig[0, v, u] := (ranks[u], …)              -- as today
For d = 1:        cell_sig[1, v, u] := (ranks[u],
                    sorted multiset over mid of (BR[0, v, mid], edge[mid, u]))
For d ≥ 2:        cell_sig[d, v, u] := (ranks[u],
                    sorted multiset over mid of
                      (BR[d-1, v, mid], BR[d-2, v, mid], edge[mid, u]))
BR[d, v, u]      := dense rank of cell_sig[d, v, u] over all (v', u') at depth d
FromRanks[d, v]  := unchanged (sorted multiset of BR[d, v, *])
```

Why two suffices for Cycle3/5/7: the failure is specifically a parity
asymmetry between an odd-length cycle and an even-length cycle of double the
length. At any odd `d`, the diagonal cell of the even-length cycle has 0
walks while the diagonal of the odd-length cycle has positive walks. A
two-depth window straddles one even and one odd `d`, breaking the parity-only
multiset coincidence.

### Variant B — full history

Robust against arbitrary cover relationships, not just parity.

```
For d ≥ 1:        history(v, mid, d) := (BR[0, v, mid], BR[1, v, mid], …, BR[d-1, v, mid])
                  cell_sig[d, v, u] := (ranks[u],
                    sorted multiset over mid of (history(v, mid, d), edge[mid, u]))
```

Comparison of `history` tuples is lexicographic on `(BR[0], BR[1], …)`. Two
mids agree only when their *entire* refinement trajectory through depth `d-1`
agrees.

Variant A is Variant B truncated to a 2-element prefix. The truncation
handles 2-fold covers; longer prefixes handle higher-fold covers. The cycle
CFI cases are 2-fold (`C_{2n}` covers `C_n` 2-to-1), so Variant A is
sufficient *for that input class*. Anything with a `k`-fold cover structure
for `k ≥ 3` would need a window of width `≥ k`, or Variant B.

### Recommendation

Implement Variant B. The asymptotic cost is the same (see below), and it
removes the empirical question of "is the window wide enough" — Variant A is
correct for parity covers but invites a second debugging round if a 3-fold or
higher cover surfaces in a future test base. The existing test suite plus the
1b sweep gives clear go/no-go signal either way.

---

## Cost

Per `ConvergeOnce` iteration:

  Current: per cell, signature has `n + 1` long-sized slots → O(n³) cells ×
  O(n log n) sort = O(n⁴ log n) per `ConvergeOnce`. (`n` depths × n² cells ×
  n-element sort.)

  Variant A: per-cell tuple is one slot wider (one extra `int`); sort cost
  unchanged asymptotically. Same O(n⁴ log n).

  Variant B: per cell, the per-`mid` tuple grows from `O(1)` to `O(d)` because
  it carries `(BR[0], …, BR[d-1])`. Sort comparison becomes `O(d)` instead of
  `O(1)`. Total: `O(n)` depths × `n²` cells × `n`-element sort ×
  `O(n)` per-comparison = O(n⁵ log n) per `ConvergeOnce`.

That's a factor of `n log n` over today's algorithm; on the test sizes in
play (n up to a few hundred for the long CFI cases), that's tractable.

The fast variant (`CanonGraphOrdererV4Fast`) packs each per-`mid` tuple into
a single `long`. Variant B breaks that — the tuple is no longer a fixed-size
primitive. Either:

  - keep packing, but emit one long per (mid, depth) pair into the signature
    array (storage doubles to triples per signature); or
  - replace the long-comparator with a span-comparator (no packing, per-mid
    tuple compared element-by-element).

The second is cleaner for Variant B; the first stays closer to the current
hot-path layout.

---

## Why this fix is sound (not just empirically motivated)

The forward direction of `convergeLoop` correctness — same Aut-orbit ⇒ same
converged value, proved as `convergeLoop_Aut_invariant` — is preserved by
either variant. The proof uses:

  - `cell_sig` is determined by structural data (ranks, edges) that
    automorphisms preserve.
  - `BR` and `FromRanks` are dense ranks of `cell_sig`, equivariant by
    construction.

Both properties hold equally for the extended `cell_sig`: it is still
determined by structural data, so automorphisms still preserve it.

The reverse direction (`OrbitCompleteAfterConv_general`) was the open
half. Variant B strictly refines the partition produced by the current
algorithm — every distinction the current algorithm makes is preserved (any
difference at depth `d-1` is visible to the new cell sig at depth `d`), and
new distinctions become possible. So:

  - Every empirical pass of the current algorithm remains a pass.
  - Every empirical fail of the current algorithm *may* now pass (and does,
    for cycle CFI; doesn't, for K4).

---

## Scope and limits

The 1b table's verdict at the level of base treewidth is unchanged in
character. What changes:

| Base   | Treewidth | Current 1b | After Variant B (predicted) |
|--------|-----------|------------|------------------------------|
| Cycle3 | 2         | ❌          | ✅ (parity cover, 2-fold)     |
| Cycle4 | 2         | ✅          | ✅                            |
| Cycle5 | 2         | ❌          | ✅                            |
| Cycle6 | 2         | ✅          | ✅                            |
| Cycle7 | 2         | ❌          | ✅                            |
| K4     | 3         | ❌          | ❌ (treewidth 3, beyond 2-WL) |

This fix moves the algorithm one rung up the WL ladder — from "1-WL with
pair info" to roughly "1-WL with pair info plus walk-count history per
pair", which on the cycle-cover input class is enough. Any CFI base of
treewidth `≥ 3` (K4 first, then K33, Petersen, K6, K7) remains a fail; those
require structurally different remediation (individualization-and-refinement
per [OrbitCompleteAfterConv.md:264-279](OrbitCompleteAfterConv.md#L264-L279)).

The proof obligation `OrbitCompleteAfterConv_general` therefore does **not**
become true under this extension — K4 alone falsifies it. The honest framing
remains hoist-as-hypothesis (Approach D in the discharge plan), with this
extension narrowing the empirical gap from "fails on cycles and K4 and
beyond" to "fails on K4 and beyond". That's a smaller gap, and one that
aligns with a well-understood place on the WL hierarchy.

---

## Verification plan

Once implemented, run in order:

  1. **Existing tests (regression).** All `KnownGraphsdifferentScramblings`,
     `AllPermutations_UniqueCanonicalCount`, `RandomGraphs_…` tests must
     continue to pass. A pass means the refinement still respects
     isomorphism (forward direction, never in question, but worth confirming
     against the implementation).

  2. **1b sweep.** `CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint` over
     `Cycle3..Cycle7` and `K4`. Predicted: Cycle3/5/7 flip ❌→✅, K4 stays ❌,
     Cycle4/6 stay ✅.

  3. **1c sweep.** `CfiPair_DisjointUnion_DifferentScramblings_ProduceSameCanonical`
     same set. Predicted: Cycle3/5/7 flip ❌→✅. (1c is the σ-invariance
     check; the failure on odd cycles was driven by 1b's collapse, so fixing
     1b should fix 1c too on these bases.)

  4. **1a sweep on extended bases.** `K33`, `Petersen`, `K6`, `K7` — currently
     pass under 1a. Predicted: still pass (1a is full-pipeline, more
     forgiving than 1b).

If any of (1)–(4) deviates from prediction, that's the signal to debug the
implementation against the spec, not to revisit the spec.

---

## Open questions

  - **Variant choice.** The spec recommends Variant B for robustness;
    Variant A is enough for the empirically-failing cases. Decide based on
    whether the cost factor of `n log n` is acceptable for the long-running
    CFI tests (`K33`, `Petersen`, `K6`, `K7` at the fast canonizer). If the
    long-running times explode under B but A passes the 1b sweep, ship A.

  - **Lean alignment.** The Lean reference (`LeanGraphCanonizerV4.lean`)
    has its own `comparePathSegments` that today peeks at
    `betweenRanks d-1 start end`. Variant A adds one extra peek
    (`d-2`); Variant B replaces the single peek with a list comprehension
    over `d`. The equivariance lemmas in `Equivariance/CompareEquivariant.lean`
    will need updating but the proof shape is preserved.

  - **Naming.** `BR[d, v, u]` is fine in this doc but the field in
    `RankState` is `betweenRanks` and is conceptually unchanged. If
    Variant B is adopted, the per-mid tuple stored in `PathSegment.inner`
    grows from `(edgeType, subDepth, subStart, subEnd)` to
    `(edgeType, [subDepth_0, …, subDepth_{d-1}], subStart, subEnd)` — which
    is a real schema change worth thinking about before coding.
