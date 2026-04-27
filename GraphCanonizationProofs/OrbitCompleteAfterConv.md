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

[FullCorrectness/Main.lean:89](FullCorrectness/Main.lean#L89) — `run_swap_invariant_fwd`,
σ ∉ Aut G branch.

The hypothesis is consumed by `runFrom_VtsInvariant_eq_strong_general`
([FullCorrectness/Equivariance/OrderVerticesGeneral.lean](FullCorrectness/Equivariance/OrderVerticesGeneral.lean))
as input to its outer induction's Case 2 (orbit-bridging step).

---

## Empirical evidence the algorithm is complete

The algorithm has been validated outside Lean:

  - **Exhaustive on n ≤ 7:** every isomorphism class of graphs up to 7 vertices
    was checked manually. The Lean tests cover up to `countUniqueCanonicals 4 == 11`;
    the C# precursor extended the exhaustive sweep to n = 7 against OEIS A000088.
  - **Random on n = 30:** randomized testing on size-30 graphs (in the C# precursor).
    No counterexamples observed.

Neither sweep targets the *structural* cases known to be hard for refinement-based
algorithms. Those cases are sparse, regular, and have heavy local symmetry; random
Erdős–Rényi sampling effectively never produces them, and exhaustive enumeration
caps below their minimum size.

---

## Why the obligation is research-level

`OrbitCompleteAfterConv_general` asserts that the algorithm's refinement is a
*complete* orbit detector. The Cai–Furer–Immerman (CFI) construction produces, for
every k, a non-isomorphic pair of graphs that the k-dimensional Weisfeiler–Leman
algorithm cannot distinguish. Practical canonizers (nauty, bliss, traces, saucy)
sidestep this via individualization-and-refinement: when refinement plateaus, they
fork on a vertex of the smallest non-singleton color class and recurse. The
refinement *alone* is not the source of correctness.

This pipeline uses **path-multiset refinement** indexed on `(depth, start, end)`
triples — see [CoreAlgorithm.md](CoreAlgorithm.md) for the data-structure detail.
Whether this refinement is complete, and where it sits relative to the WL hierarchy,
is the open question. The empirical sweeps say "yes" within their scope, but a
counterexample at any *n* would falsify the obligation unconditionally.

This means **the obligation may or may not be true**. Three outcomes are possible:

  1. **It is true** and provable in Lean: requires building the full
     bisimulation-lift proof (Approach A below).
  2. **It is true** but a Lean proof is intractable: the obligation remains an
     external hypothesis of canonizer-correctness.
  3. **It is false**: there exists a graph where path-multiset refinement merges
     two non-orbit-equivalent vertices. Discovering such a graph is itself a result.

---

## Plan of attack — two steps, in order

### Step 1 (in progress) — CFI counterexample test

Before investing in a proof, **falsify or de-risk the obligation by direct test**.
Build a series of CFI pairs in the C# precursor and run them through `CanonGraphOrdererV4`.
If a CFI pair collapses to the same canonical, the obligation is false (outcome 3),
and the proof attempt is moot.

  - Generator stub:
    [GraphCanonizationProject/CfiGraphGenerator.cs](../GraphCanonizationProject/CfiGraphGenerator.cs)
    — methods, base-graph factories, and verification helpers laid out, bodies pending.
  - Test wiring: a `CfiPair_ProducesDifferentCanonical` `[Theory]` in
    `GraphCannonTests.cs` (sketch included at the bottom of the generator file).
  - Coverage targets: K_4 base (12 vertices, classical 1-WL counterexample),
    K_{3,3} / Rook 3×3 / Petersen bases (defeat 2-WL), and at least one
    higher-treewidth base (defeat k-WL for larger k). Each pair must be verified
    non-isomorphic before drawing conclusions about the canonizer.

The empirical claim from the existing test sweeps is that the algorithm is *not*
analogous to any constant-k WL — Step 1 is what tests that claim. No correctness
property of the algorithm is asserted here on the basis of WL classification; that
classification is what's being checked.

**Possible outcomes of Step 1:**

  - All CFI pairs are correctly distinguished ⇒ raises confidence that the
    algorithm is genuinely beyond the WL hierarchy. Proceed to Step 2.
  - Some CFI pair collapses ⇒ the obligation as stated is false. Pivot to
    pivot-and-refinement: introduce a backtracking fork for non-singleton classes,
    re-state and re-prove the modified theorem.

### Step 2 (later) — Approach A: bisimulation lift

The path the rest of this document is organized around. Conceptually:

  1. **Refinement-operator framing.** Define a typing-refinement operator
     `refine : (Fin n → α) → (Fin n → α′)` whose codomain encodes
     `(typing of v) × (multiset of typings of paths from v)`. Show
       - `refine` is monotone (no class is collapsed),
       - `convergeLoop` is its fixed-point iterator,
       - at the fixed point, the equivalence `v ~ w ⇔ c[v] = c[w]` is an
         **equitable partition** (local refinement-stability condition).
     New file: `FullCorrectness/Refinement.lean` (~200 lines).

  2. **Bisimulation construction.** From the equitable-partition condition,
     build the bridging automorphism τ depth-by-depth. At each step:
       - Choose a not-yet-matched vertex `x` reachable from already-matched
         territory.
       - Use the path-multiset equality to find a partner `y` for `x` such that
         the partial map extends without contradiction.
       - Iterate until every vertex is mapped.
     The crux is consistency: showing the local choices can be made coherently.
     This is exactly where CFI graphs break analogous attempts for 1-WL — Step 1
     is what tells us whether they break this construction too.
     New file: `FullCorrectness/CompletenessOfPathRefinement.lean`. Length and
     feasibility depend on Step 1's verdict.

  3. **TypedAut refinement.** Once a witness σ ∈ Aut G with `σ v₁ = v₂` exists,
     show σ ∈ TypedAut(conv mid). Direct from `convergeLoop_Aut_invariant`.
     ~50 lines.

  4. **Assembly.** Plug 1–3 into the definition of `OrbitCompleteAfterConv_general`,
     discharge in `Main.lean:89`. ~30 lines.

**Total for Step 2:** ~300+ lines of Lean *plus* the bisimulation lift, which is
a research-level mathematical proof of unknown size.

---

## Fallback (Approach D) — Hoist as hypothesis

If Steps 1–2 do not produce a closed proof, hoist `OrbitCompleteAfterConv_general`
as an explicit named premise on `run_canonical_correctness`:

```lean
theorem run_canonical_correctness (G H : AdjMatrix n)
    (hOrbit : ∀ σ, OrbitCompleteAfterConv_general G σ) :
    G ≃ H ↔ run zeros G = run zeros H
```

Honest framing: the σ-equivariance work is fully proved; the completeness piece is
a stated assumption. No `sorry` at all, but the assumption's truth depends on the
empirical/CFI results.

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
  - Algorithm-side context: [CoreAlgorithm.md](CoreAlgorithm.md).
  - CFI generator stub:
    [GraphCanonizationProject/CfiGraphGenerator.cs](../GraphCanonizationProject/CfiGraphGenerator.cs).
