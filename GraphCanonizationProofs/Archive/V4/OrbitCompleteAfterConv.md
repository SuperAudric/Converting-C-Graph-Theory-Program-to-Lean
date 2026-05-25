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
  - **CFI sweep, treewidth 2–5 bases:** every active and manually-verified CFI
    pair is correctly distinguished — `Cycle3`, `Cycle4`, `K4`, `K33`, `Petersen`,
    and (single-run) `K6`. These are precisely the *structural* hard cases that
    the previous two bullets miss. See "Step 1" below for the test wiring;
    coverage now extends through the 3-WL counterexample base (treewidth 5).

The first two sweeps do not target the *structural* cases known to be hard for
refinement-based algorithms — those cases are sparse, regular, and have heavy
local symmetry; random Erdős–Rényi sampling effectively never produces them, and
exhaustive enumeration caps below their minimum size. The CFI sweep does, which
is why it carries the most weight against `OrbitCompleteAfterConv_general`.

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
triples — see [ConvergeLoopAlgorithm.md](ConvergeLoopAlgorithm.md) for the data-structure detail.
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
Build a series of CFI pairs in the C# precursor and run them through the canonizer.

Three complementary tests are wired. **As of 2026-04-28 the obligation is
empirically falsified** — both 1b and 1c fail on at least one wired CFI base
(see "Empirical state" below for the full table). The obligation as currently
stated is false; the canonizer additionally fails σ-invariance on disjoint
unions of odd-cycle CFI bases under the *full* `Run` pipeline, which is a
separate (stronger) finding than the obligation's narrow falsification.

#### 1a. `CfiPair_ProducesDifferentCanonical` — full-pipeline cross-graph check

Runs `Run` (the full pipeline: `ConvergeLoop` + `OrderVertices` tiebreak loop +
`LabelEdgesAccordingToRankings`) on `Even` and `Odd` separately, asserting the
emitted canonical strings differ.

**What it catches:** the full pipeline fails to distinguish the two CFI graphs
(direct collapse). All currently wired bases pass.

**What it does *not* catch directly:** the obligation is about `convergeLoop`
output values *internal to one graph*. `Run` interposes `BreakTie` between
`ConvergeLoop` calls in `OrderVertices`, and `BreakTie` commits to an
index-based choice when classes have ties. So `Run` distinguishing `Even` from
`Odd` is *necessary* for the obligation but not *sufficient* — `BreakTie`'s
arbitrary choice can paper over a refinement failure inside `convergeLoop`,
producing different canonicals for the wrong reason.

#### 1b. `CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint` — direct probe

Builds `G = Even ⊕ Odd` as a disjoint union, runs *one* `ConvergeLoop` call
(no `BreakTie`, no `OrderVertices` outer loop), and asserts that the rank
values assigned to vertices in the `Even` half and the `Odd` half are
disjoint sets.

**Why this directly probes the obligation.** In `G = Even ⊕ Odd` with both
components connected and non-isomorphic, `Aut(G) = Aut(Even) × Aut(Odd)` —
no automorphism crosses components. `TypedAut(G, typing) ⊆ Aut(G)` for any
typing, so no `TypedAut`-orbit contains both an `Even`-vertex and an
`Odd`-vertex. The obligation says: equal `convergeLoop` value ⇒ same
`TypedAut`-orbit. Contrapositive: different orbits ⇒ different value. So if
any rank value is shared between the two halves, that pair of vertices is a
direct counterexample to `OrbitCompleteAfterConv_general` — no reliance on
`BreakTie` cascade behaviour, no σ-invariance proxy.

**Scope.** This catches *cross-component* refinement failures (the algorithm
fails to separate `Even` from `Odd` before tiebreak would have to step in).
It does not directly catch *within-component* refinement failures (two
non-orbit vertices inside `Even` alone get tied).

#### 1c. `CfiPair_DisjointUnion_DifferentScramblings_ProduceSameCanonical` — full-pipeline canonicity probe

Builds `G = Even ⊕ Odd`, runs the *full* `Run` pipeline on the unscrambled
union to get a baseline canonical, scrambles the union under several random
relabelings σ, and asserts every `Run(σ(G))` matches the baseline. `Run` is
graph-isomorphism-invariant by contract, so any divergence is a defect.

**Why this is a strictly stronger probe than 1b.** A 1b failure says
`convergeLoop` alone fails to separate the halves, which `BreakTie`'s
index-based commitment in `OrderVertices` could in principle still recover
from. A 1c failure says even the full pipeline (`ConvergeLoop` + `BreakTie`
cascade) fails to produce a canonical form on the disjoint union — which
makes it a direct contradiction with the canonizer's stated contract, not
just the obligation's stated form.

**Scope.** Cross-component, but probes the full pipeline rather than just
`ConvergeLoop`.

#### Common machinery

  - Generator:
    [GraphCanonizationProject/CfiGraphGenerator.cs](../GraphCanonizationProject/CfiGraphGenerator.cs)
    — `Generate(baseName)` produces a `CfiPair(Even, Odd, BaseGraphName,
    BaseTreewidth, VertexRoles)`, plus `AssertWellFormedPair`, `VerifyNonIsomorphic`,
    `DescribePair`, and `BuildDisjointUnion` (used by 1b). Available bases:
    `Cycle{n}` (treewidth 2), `K4` (3), `K33` (3), `Rook3x3` (4),
    `Petersen` (4), `K6` (5), `K7` (6).
  - Canonizer under test: 1a runs against `ICanonGraphOrderer` (defaulting to
    [`CanonGraphOrdererV4Fast`](../GraphCanonizationProject/CanonGraphOrdererV4Fast.cs)).
    1b is wired only against `CanonGraphOrdererV4Fast` — it calls
    `RunConvergeLoopForTesting` to obtain the converged ranks directly,
    bypassing the `OrderVertices` tiebreak loop. The reference orderer is
    not exposed for this entry point; the equivalence-class behaviour is
    identical so the fast variant is sufficient for falsification.
  - 1a: `CfiPair_ProducesDifferentCanonical` runs `Cycle3`, `Cycle4`, `K4`
    by default; `K33` (60v), `Petersen` (100v), `K6` (156v), `K7` (308v)
    behind `[Trait("Category","LongRunning")]` in `GraphCanonLongTests.cs`.
  - 1b: `CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint` runs `Cycle3`–`Cycle7`
    and `K4` by default; the `K33`/`Petersen`/`K6`/`K7` long cases live in
    `GraphCanonLongTests.cs`. Asymptotically cheaper than 1a (one `ConvergeLoop`
    instead of `n × ConvergeLoop` in the `OrderVertices` tiebreak loop).
  - 1c: `CfiPair_DisjointUnion_DifferentScramblings_ProduceSameCanonical` runs
    `Cycle3`–`Cycle7` and `K4` by default. Each case does 5 scrambles under the
    full `Run` pipeline — cost is ~5× a single `Run` on a 2n-vertex graph. No
    long-running variant wired yet.
  - Coverage targets (under this doc's convention "treewidth-(k+2) base ⇒
    defeats k-WL"): cycle bases (1-WL, smallest; cheapest to test), `K4` and
    `K33` (1-WL via treewidth 3), `Rook3x3` and `Petersen` (2-WL via
    treewidth 4), `K6` (3-WL via treewidth 5), `K7` (4-WL via treewidth 6).
    Each pair is verified non-isomorphic via `AssertWellFormedPair`
    (well-formedness) and `VerifyNonIsomorphic` (brute-force for n ≤ 9,
    otherwise relies on the construction's published proof).

The empirical claim from the existing test sweeps is that the algorithm is *not*
analogous to any constant-k WL — Step 1 is what tests that claim. No correctness
property of the algorithm is asserted here on the basis of WL classification; that
classification is what's being checked.

**Empirical state as of 2026-04-28.** Summary table over the bases run under
the default profile, fast canonizer:

| Base   | 1a (Run on E vs O distinct) | 1b (ConvergeLoop ranks disjoint on E ⊕ O) | 1c (Run σ-invariant on E ⊕ O) |
|--------|----------------------------|-------------------------------------------|-------------------------------|
| Cycle3 | ✅ pass                     | ❌ **fail** (rank 0 shared)                | ❌ **fail**                    |
| Cycle4 | ✅ pass                     | ✅ pass                                    | ✅ pass                        |
| Cycle5 | ✅ pass                     | ❌ **fail**                                | ❌ **fail**                    |
| Cycle6 | ✅ pass                     | ✅ pass                                    | ✅ pass                        |
| Cycle7 | ✅ pass                     | ❌ **fail**                                | ❌ **fail**                    |
| K4     | ✅ pass                     | ❌ **fail** (ranks 0, 1 shared)            | ✅ pass                        |

The pattern: 1b fails on every odd-cycle base tested, on every same-parity
pairing of fail/pass between 1b and 1c, and on K4. 1c fails on exactly the
odd-cycle bases (Cycle3/5/7); even cycles and K4 pass. The long-running
extended cases (`K33`, `Petersen`, `K6`, `K7`) for 1a are still consistent
with 1a's pass record (`K6` passed once manually under fast in ~3000s);
the same long cases for 1b have not yet been run.

**What this means.**

  1. **The obligation `OrbitCompleteAfterConv_general` is empirically false.**
     1b's failure on Cycle3 alone is sufficient: a non-isomorphic CFI pair
     forms a disjoint union whose `convergeLoop` output assigns equal value to
     vertices in different `Aut(G)`-orbits (cross-component pairs cannot share
     an orbit when components are connected and non-isomorphic). The Lean
     proof attempt for the obligation as currently stated is moot — Step 2
     (bisimulation lift below) cannot succeed without re-stating the
     obligation.

  2. **The canonizer additionally fails σ-invariance on a structurally
     specific class of inputs.** 1c's failure on odd-cycle CFI disjoint unions
     means the full pipeline (`Run` end-to-end) is not always canonical: the
     same graph under different relabelings produces different output strings.
     This is a strictly stronger negative result than (1) — it isn't merely
     "the proven invariant doesn't cover this case," it's "the algorithm's
     output contract is violated on this case." `Run` is supposed to be a
     canonical form, and on `Cycle3`/`Cycle5`/`Cycle7` CFI disjoint unions it
     isn't.

  3. **K4 is the one currently-known case where (1) holds without (2).** 1b
     fails (so the obligation is false on K4 too), but 1c passes (so the
     full pipeline does happen to produce a canonical form on K4 disjoint
     union under the scrambles tested). This may or may not survive larger
     scramble counts; it is the configuration most consistent with "the
     obligation needs restating but the algorithm is still correct."

**Possible outcomes of Step 1 (revised after 2026-04-28 results).**

  - **(Original — now obsolete)** All CFI pairs are correctly distinguished by
    the full pipeline ⇒ confidence the algorithm is beyond the WL hierarchy.
    No longer applicable: 1c falsifies this for odd-cycle bases.
  - **(Original — partially confirmed, now sharpened by 1b)** Some CFI pair
    collapses under the full pipeline ⇒ the obligation as stated is false.
    1b's findings already establish this; 1c's findings establish more.
    Pivot to pivot-and-refinement: introduce a backtracking fork for
    non-singleton classes, re-state and re-prove the modified theorem.

## Next steps — root-cause investigation

The immediate question is whether the observed failures are:

  - **(A) Algorithmic.** This path-multiset refinement + index-tiebreak design
    genuinely cannot canonize disjoint unions of odd-cycle CFI graphs — the
    algorithm as specified is incorrect on this input class. Remediation
    requires changing the algorithm itself (e.g., introduce
    individualization-and-refinement: when refinement plateaus, fork on a
    vertex of the smallest non-singleton class and recurse; this is what
    nauty/bliss/traces do).
  - **(B) Implementation.** The C# canonizer (or the Lean spec it mirrors)
    has a bug somewhere that doesn't reflect the intended algorithm — for
    example a subtle ordering issue in `BreakTie`, a missing edge case for
    disconnected graphs in `InitializePaths`, or an off-by-one in the
    `OrderVertices` tiebreak loop's `target` advancement. Remediation is
    local: find and fix the bug.

Distinguishing (A) from (B) is the next step. Suggested investigation order:

  1. **Reduce.** `Cycle3` is the smallest base that fails 1b (n = 18 per
     half, n = 36 disjoint). Manually inspect the `convergeLoop` output on
     that disjoint union: which Even-vertices and which Odd-vertices end up
     sharing rank 0? Compare to vertex roles (gadget structure) — are the
     shared vertices of the same gadget role, or different?

  2. **Cross-check with the reference orderer.** The 1b/1c findings are on
     `CanonGraphOrdererV4Fast`. Run 1c on `CanonGraphOrdererV4` (the
     Lean-aligned reference) for `Cycle3` to confirm the failure isn't a
     fast-variant-only divergence. The fast variant claims behaviour-level
     parity with the reference; if 1c fails only on the fast variant, the
     bug is in the fast variant.

  3. **Cross-check with the Lean specification.** If `CanonGraphOrdererV4`
     also fails 1c on `Cycle3`, port the same disjoint-union test to Lean's
     `runFrom` (the algorithmic kernel) and run it under `#eval` on the
     same input. Three outcomes:
     - Lean `runFrom` ≠ canonical too: bug is at the algorithm level
       (outcome A), or at the spec level which is the same thing for our
       purposes.
     - Lean `runFrom` is canonical but the C# is not: bug is in the C#
       implementation (outcome B).
     - Lean `runFrom` is canonical and C# is too: the failure was harness
       artifact; debug the C# test wiring.

  4. **Cycle-parity hypothesis.** The 1c failure is exclusively on odd
     cycles (3, 5, 7) and not on even cycles (4, 6). If the algorithm is
     genuinely cycle-parity-sensitive, that points strongly toward (A) and
     toward a structural fix (the forking step from
     individualization-and-refinement). If it's parity-sensitive only in
     the C# implementation, (B). Either way, `Cycle3` is the right
     reduction target.

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
  - CFI generator (implemented):
    [GraphCanonizationProject/CfiGraphGenerator.cs](../GraphCanonizationProject/CfiGraphGenerator.cs).
  - Canonizer implementations:
    [`CanonGraphOrdererV4`](../GraphCanonizationProject/CanonGraphOrdererV4.cs)
    (Lean-aligned reference) and
    [`CanonGraphOrdererV4Fast`](../GraphCanonizationProject/CanonGraphOrdererV4Fast.cs)
    (flat-buffer reimplementation; same equivalence-class behaviour, default in tests).
