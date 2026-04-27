# `OrbitCompleteAfterConv_general` — discharge plan

The single remaining sorry in the FullCorrectness chain. Phase 6 closed the
σ-equivariance half of canonizer correctness; this document records what's needed
to close the other half (algorithmic completeness of the path-multiset color
refinement).

---

## The obligation

```lean
def OrbitCompleteAfterConv_general (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (mid : Array VertexType), mid.size = n →
    ∀ v₁ v₂ : Fin n,
      (convergeLoop (initializePaths (G.permute σ)) mid n).getD v₁.val 0 =
      (convergeLoop (initializePaths (G.permute σ)) mid n).getD v₂.val 0 →
      ∃ τ_step ∈ (G.permute σ).TypedAut
                  (convergeLoop (initializePaths (G.permute σ)) mid n),
        τ_step v₁ = v₂
```

In words: **on any graph, two vertices with equal `convergeLoop` output values lie
in the same `TypedAut`-orbit of that converged array** (i.e., there is an
automorphism of `G.permute σ` preserving the converged typing that maps `v₁` to `v₂`).

Equivalently: the algorithm's path-multiset refinement separates every pair of
non-orbit-equivalent vertices.

The forward direction (same orbit ⇒ same value) is `convergeLoop_Aut_invariant` ✅.
This file is about the **reverse direction** — the deep half.

## Single sorry site

`FullCorrectness/Main.lean:89` — `run_swap_invariant_fwd` σ ∉ Aut G branch.

The hypothesis is consumed by `runFrom_VtsInvariant_eq_strong_general`
(`FullCorrectness/Equivariance/OrderVerticesGeneral.lean`) as input to its outer
induction's Case 2 (orbit-bridging step).

---

## Empirical evidence the algorithm is complete

The algorithm has been validated outside Lean:

  - **Exhaustive on n ≤ 7:** every isomorphism class of graphs up to 7 vertices
    was checked manually. The Lean tests cover up to `countUniqueCanonicals 4 == 11`;
    the C# precursor extended the exhaustive sweep to n = 7 against OEIS A000088.
  - **Random on n = 30:** randomized testing on size-30 graphs (in the C# precursor).
    No counterexamples observed.

The Lean port of this project exists *to formally verify* what the empirical sweeps
suggest. So the question is not "is the algorithm correct in practice" but
"can we **prove** correctness in Lean, and if not, why not."

---

## Why the obligation is research-level

`OrbitCompleteAfterConv_general` asserts that the algorithm's color refinement
is a *complete* orbit detector. Color-refinement-style algorithms are known to be
**incomplete in general**:

  - **1-WL** (Weisfeiler–Leman, neighbor-color-multiset refinement) cannot
    distinguish the Cai–Furer–Immerman family of pairs.
  - **k-WL** for any constant *k* is also incomplete; the W-L hierarchy strictly
    increases in expressive power but never reaches all graphs.
  - Practical canonizers (nauty, bliss, traces, saucy) achieve completeness via
    **individualization-and-refinement**: when refinement plateaus, they fork on
    a vertex of the smallest non-singleton color class and recurse. The refinement
    *alone* is not the source of correctness.

The pipeline here uses **path-multiset refinement** (multiset of all paths from a
vertex up to depth n−1), which is a richer invariant than 1-WL. Whether this is
*complete* — i.e. strictly stronger than the entire W-L hierarchy in expressive
power — is the open question. The empirical sweeps say "yes for n ≤ 7" and "yes
for random n = 30," but a counterexample at any *n* would falsify the obligation
unconditionally.

This means **the obligation may or may not be true**. Three outcomes are possible:

  1. **It is true** and provable in Lean: requires building the full color-refinement
     completeness proof for path-multiset refinement.
  2. **It is true** but a Lean proof is intractable: the obligation remains an axiom
     of canonizer-correctness, accepted on empirical grounds.
  3. **It is false**: there exists a graph (probably large) where path-multiset
     refinement merges two non-orbit-equivalent vertices. Discovering such a graph
     is itself a contribution.

---

## Roadmap to a Lean proof (assuming outcome 1)

Sketch of what a direct discharge would require, ordered by depth.

### Step 1 — characterize `convergeLoop` as a fixed point of a refinement operator (~200 lines)

Define a typing-refinement operator
```
refine : (Fin n → α) → (Fin n → α′)
```
where the codomain `α′` is `(typing of v) × (multiset of typings of paths from v)`
or a hashed version thereof. Show:

  - `refine` is monotone: if two vertices receive distinct types under `refine·t`,
    they had distinct types under `t` already ⇒ refining never collapses classes.
  - `convergeLoop` reaches a fixed point of `refine` (modulo dense-rank renaming).
  - At the fixed point, two vertices have equal type iff their refinement signatures
    are equal at all depths.

Helper file: `FullCorrectness/Refinement.lean` (new, ~200 lines).

### Step 2 — characterize the fixed-point typing as a complete orbit invariant (~research)

Show that two vertices with equal fixed-point type are `Aut(G)`-orbit-equivalent.
Equivalent statements that any of would suffice:

  - **Path-multiset completeness.** `path_multiset G v₁ = path_multiset G v₂ ⇒
    ∃ σ ∈ Aut G, σ v₁ = v₂`. This is the central open question for this algorithm.
  - **Inductive bisimulation construction.** Given vertices with equal fixed-point
    types, *constructively* build the bridging σ by greedily extending a partial
    automorphism using the type-matching at each depth. Standard for "stable
    coloring" algorithms; needs Mathlib `Equiv` machinery.

This step is where the depth lives. If path-multiset refinement is not complete,
no proof here will succeed.

Possible structure: try the constructive approach (sub-step b above). At each
recursion level, pick the lowest-numbered unmatched vertex; show that its type
class (under the current refinement) is a singleton or that its members are all
isomorphism-equivalent within `Aut G`. If they aren't, you've found a
counterexample (outcome 3).

Helper file: `FullCorrectness/CompletenessOfPathRefinement.lean` (new, hundreds of
lines if successful; possibly impossible).

### Step 3 — refine `Aut(G)` to `TypedAut(conv mid)` (~50 lines)

Once we have σ ∈ Aut(G) with σ v₁ = v₂ and v₁, v₂ have the same conv value, show
σ ∈ TypedAut(conv mid). Direct from `convergeLoop_Aut_invariant`: σ ∈ Aut G ⇒ σ
preserves conv values pointwise.

### Step 4 — assemble (~30 lines)

Plug Steps 1–3 into the definition of `OrbitCompleteAfterConv_general`. Discharge
in `Main.lean:89`.

**Total:** ~300 lines of Lean **plus** a research-level mathematical proof at Step 2
(unknown size; may not exist).

---

## Roadmap if Step 2 stalls (outcome 2)

If a Lean proof of completeness proves intractable, fall back to one of:

### B1 — Hoist the assumption into the theorem statement

Make `OrbitCompleteAfterConv_general` an explicit hypothesis of
`run_canonical_correctness`:

```lean
theorem run_canonical_correctness (G H : AdjMatrix n)
    (hOrbit : ∀ σ, OrbitCompleteAfterConv_general G σ) :
    G ≃ H ↔ run zeros G = run zeros H
```

Honest framing: the σ-equivariance work is fully proved; the completeness piece
is a stated assumption. No `sorry` at all.

### B2 — Bounded variant for small n

State and prove a bounded version:

```lean
theorem run_canonical_correctness_le_n (G H : AdjMatrix n) (hn : n ≤ 7) :
    G ≃ H ↔ run zeros G = run zeros H
```

Discharge `OrbitCompleteAfterConv_general` for `n ≤ 7` by exhaustive case analysis
(decidable by finiteness of `Aut G`). Combine with the unconditional Phase 6
machinery. Yields a verified canonizer for `n ≤ 7`, which matches the empirical
testing scope already done.

Estimated effort: ~100–200 lines per *n* (bounded by the size of `Aut G` for that *n*).

### B3 — Counterexample search

If Step 2 reveals a structural reason the algorithm might fail, write a search
procedure to look for a counterexample at larger *n*. Lean is poorly suited to
this; offload to the C# precursor with extended graph generators.

---

## Recommended posture

The current `Main.lean:89` sorry is an honest record of the situation:

> Phase 6 proves that the canonizer is *equivariant* (its output transforms
> consistently under graph relabelings). What's missing is that the canonizer is
> *complete* (its output distinguishes all non-isomorphic graphs).
>
> Equivariance is the Lean-tractable half. Completeness is research-level for
> arbitrary *n* but empirically validated for n ≤ 7 (exhaustive) and n = 30 (random)
> via the C# precursor.

Concrete next actions, in priority order:

  1. **Discharge for bounded n** (Path B2). Yields a clean, fully-Lean-proved
     canonizer for graphs of size ≤ 7. Matches the existing empirical scope.
     Self-contained, no research prerequisites. Estimated: 1–2 weeks.

  2. **Attempt Step 2 constructively** (Path A.2 sub-step b). If it works for
     small examples, the proof structure may scale. If it fails on a specific
     graph, that's a counterexample (outcome 3). Estimated: open-ended; abandon
     after ~2 weeks if no progress.

  3. **Hoist the assumption** (Path B1) as a fallback if both above are
     unfruitful. Two-line edit; produces an unconditional Lean theorem with a
     named external hypothesis.

---

## Pointers

  - The hypothesis is defined in
    [FullCorrectness/Equivariance/OrderVerticesGeneral.lean](FullCorrectness/Equivariance/OrderVerticesGeneral.lean)
    (`OrbitCompleteAfterConv_general`).
  - The single consumer is `runFrom_VtsInvariant_eq_strong_general` in the same file.
  - The single sorry that discharges it is in
    [FullCorrectness/Main.lean:89](FullCorrectness/Main.lean#L89)
    (`run_swap_invariant_fwd` σ ∉ Aut G branch).
  - The forward-direction `convergeLoop_Aut_invariant` is in
    [FullCorrectness/Equivariance/ConvergeLoop.lean](FullCorrectness/Equivariance/ConvergeLoop.lean).
  - The path-multiset machinery (`calculatePathRankings`, `comparePathsFrom`,
    `comparePathsBetween`) lives across `Equivariance/CompareEquivariant.lean`,
    `Equivariance/PathEquivariance.lean`, and `Equivariance/PathEquivarianceRelational.lean`.
