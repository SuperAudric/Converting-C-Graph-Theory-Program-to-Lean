# Flip-validation calculator (route 2: symbolic tier evaluation)

A supplement to [`flip-validation-strategy.md`](./flip-validation-strategy.md)
covering the polynomial-bound piece of the algorithm — the "calculator" that
replaces the current `O(n⁸)`-per-sweep naive replay in §6.5's backward pass
with a symbolic representation that admits polynomial-time LexMin
evaluation. The calculator is the unproven-polynomial component the whole
algorithm's bound rests on.

The strategy doc covers what the algorithm *does* and why each invariant is
load-bearing. This doc covers *how the calculator must be shaped* to make
the polynomial bound achievable, *which structural theorems* the bound
depends on, and *where each theorem currently stands*. Together with
[`CanonGraphOrdererFlipValidation.cs`](../GraphCanonizationProject/CanonGraphOrdererFlipValidation.cs)
(the current replay-based implementation), the three documents are
intended to be a complete picture of the project's state.

---

## What the calculator is, and what it isn't

The calculator is not a general-purpose canonization algorithm. Its scope is
narrower: given the *structured output of the forward pass* (primaries,
their cell snapshots, the precomputed prefix state stack), decide which of
§6.5's branches produces the lex-smaller canonical, without re-running the
forward pass per branch.

This narrowing matters for the polynomial-bound argument. The calculator
operates on inputs that are already structured by 1-WL refinement and the
forward pass's deterministic guess selection. It does not face "arbitrary
graph, find canonical" — it faces "given this prefix state plus these
rotation candidates, which wins LexMin?" The forward pass has already done
the easy parts.

The honest framing: the calculator's polynomial bound is equivalent in
strength to GI ∈ P (one implies the other, see strategy §6 preamble). The
*specific shape* of the calculator's input may admit a polynomial procedure
where free-form canonization does not — that is the project's bet.

---

## Architectural form: priority-tier swap-condition rules per P entry

The calculator represents the canonical symbolically. For each P entry
`P[u, v]`, its direction in the final canonical is the forward pass's
commitment, possibly inverted by a tiered list of conditions on shallower
guesses' directions:

```
direction(P[u, v]) = forward_commitment(u, v)
                     ⊕ tier_1_condition(g_a, ..., g_k)
                     ⊕ tier_2_condition(...)
                     ⊕ ...
```

In words: "I match the forward pass's call for (u, v), unless tier 1's
condition on some earlier guesses says to flip; unless tier 2's says to
flip back; etc." The list is *priority-ordered* by depth (tier `k`'s
condition references only guesses shallower than the primary that wrote
`P[u, v]`), making the dependency graph acyclic when read top-down.

The full symbolic representation is the collection of these rule lists
over all O(n²) P entries. LexMin processes the canonical's entries in
row-major order; at each entry, the calculator evaluates that entry's
tier list under the constraint that shallower guesses have already been
fixed to whatever made earlier canonical entries minimal. Each tier's
evaluation is a structured-satisfiability query.

This form was selected over alternatives (BDDs, sum-of-products, algebraic
group representations) because:

- It matches the algorithm's natural granularity — one rule per primary
  contributing to one entry's tier list.
- It composes with TC chains (each link in a chain extends the relevant
  entries' tier lists by one).
- LexMin evaluation reads off directly without materialising any branch's
  full continuation.
- The structural class of formulas produced (priority-ordered decisions
  with bounded support) is the simplest candidate for being in a
  polynomial-satisfiability fragment.

---

## Theorems the polynomial bound requires

Three structural theorems beyond the strategy doc's §6 invariants are what
the calculator's polynomial bound rests on. They sharpen §6's claims into
the calculator's specific requirements.

### T-A (bounded support set per P entry)

> For every P entry `P[u, v]`, the set of primary guesses whose direction
> can change its final canonical value has size polynomial in `n`.

This bounds the tier list length per entry. O(n²) entries × poly tier list
= polynomial-sized symbolic representation. Without this, the
representation itself is exponential, and no clever evaluation rescues
it.

**Why it's plausible.** The forward pass's cell-tree has O(n) layers
worst case, O(log n) typical. Warm-refinement uniformity (§6.2) means
that within a cell tier, all members contribute the same kind of
constraint to downstream entries — they share a support-layer rather
than each contributing independently. A `P[u, v]` entry's support set is
bounded by "the cell-tier layers between `u`'s and `v`'s individualisation
points," which is at most the cell-tree depth.

**What's missing.** A formal proof that "support set growth is at-most-one
per cell tier crossed," with the warm-refinement uniformity argument
carried through closure. The Lean partial proof of §6.2 in
[`FlipValidation.lean`](../GraphCanonizationProofs/FlipValidation.lean)
is the relevant starting point.

**Design consequence.** The calculator tracks support sets at *cell-tier*
granularity, not primary granularity. Primary granularity gives O(n²)
support layers — not polynomial. Cell-tier gives O(n) — polynomial.

### T-B (bounded false-symmetry count, no double-counting)

> The number of primaries whose backward-pass adoption strictly improves
> the canonical (the "false-symmetry primaries") is bounded by `O(n²)` on
> any input, and each contributes exactly one tier rule.

This bounds the dependency chain's depth and rules out accidental
combinatorial blow-up via primary interactions.

**Why it's nearly trivial.** Every primary writes at least one P entry to
enter the record; `P` has `n(n-1)/2` entries; so total primary count is
bounded. False-symmetry count is a subset of total primary count.

**What's missing.** The "no double-counting" claim — that a single false
symmetry doesn't masquerade as multiple tier rules through clever
substitution — needs explicit statement and proof. Concrete; achievable.

**Design consequence.** The calculator's per-tier work must be polynomial,
and tier rules must not accumulate combinatorially across primaries.
Each primary contributes its own tier(s) independently, with no
combinatorial composition.

### T-C (polynomial-satisfiability of the tier-evaluation formula class)

> The boolean formulas produced by tier-evaluation — "does any guess
> assignment consistent with already-fixed earlier tiers make this tier's
> condition evaluate to `flip`?" — admit polynomial-time satisfiability
> checking.

This is the load-bearing claim. If the formulas are in 2-SAT, Horn,
linear over Z₂, FPC, or any other polynomial-satisfiability fragment, the
calculator's per-tier cost is polynomial. If they're arbitrary boolean,
the satisfiability check is NP-hard and the polynomial bound is
unreachable.

**Why it's plausible *for known cases*.** On graphs 1-WL handles, the
formulas reduce to FPC (fixed-point logic with counting), which has
polynomial-time model-checking. On CFI, the formulas reduce to linear
constraints over Z₂ (parity computation), polynomial-time satisfiable via
Gaussian elimination. The two known-hard regimes both produce structured
formulas.

**What's missing.** Characterising the formula class for *arbitrary*
inputs. Specifically:

1. What's the exact class of formulas the tier evaluation produces?
2. Does the warm-refinement uniformity (§6.2) constrain the class to a
   tractable fragment?
3. Is there a property of the forward pass not yet identified that
   restricts the formulas further?

These three are the remaining open research questions of the project.

**Design consequence.** Tier-by-tier evaluation (not joint enumeration)
is mandatory. The per-tier satisfiability check must be polynomial in
whatever class is characterised. The calculator's evaluation procedure
must operate within the structural fragment T-C identifies.

### Supporting invariants from the strategy doc

The strategy doc's §6 invariants are preconditions for the calculator's
operation. Their current status:

| Invariant | Status | Relevance to calculator |
|---|---|---|
| 6.1 (iso-invariant cell IDs) | Holds (standard) | Calculator's reference frame |
| 6.2 (weakened symmetry of propagation) | Partial Lean proof; `cell_split_uniform` and `transitiveClose_swap` are `sorry`'d | T-A's basis |
| 6.3 (deeper-lock survival) | Empirical; no structural proof | Backward-pass correctness; snapshot-diff alternative gives polynomial fallback |
| 6.4 (closure-as-guess) | Operational; DERIVED records not yet implemented | Direction-flip subproblem; tier-rule construction for closure-derived entries |
| 6.5 (every canonical reachable from any pair selection) | Established constructively by rotation mechanism | The calculator IS the polynomial replacement for naive rotation |

---

## How the theorems shape the design

The design decisions of the calculator are forced by the theorems' shape;
none are stylistic choices.

**Tiered evaluation per P entry, no joint enumeration.** Forced by T-C.
Joint enumeration over guess assignments is `2^O(n²)`, exponential. Tier-
by-tier evaluation defers each decision until LexMin needs it; each
tier's satisfiability check operates on the constrained subspace from
earlier tier resolutions. This is the structural reason the calculator
avoids the `2^k` blow-up that any naive enumeration would have on CFI.

**Support tracking at cell-tier granularity.** Forced by T-A. Tracking at
primary granularity gives O(n²) layers each potentially with O(n²)
support — not polynomial. Cell-tier granularity gives O(n) layers
worst case with O(n) support per layer — polynomial.

**DERIVED entries with driver pointers (planned).** Forced by §6.4 and
T-B. The direction-flip sub-problem is polynomial only if "all entries
flipped by primary `i`" is identifiable in O(n) time — which requires
tracking which primary drives each TC-derived entry. The current
implementation re-runs closure from scratch (correct, but loses the
direction-flip polynomiality).

**Priority-ordered (not arbitrary boolean) tier rules.** Forced by T-C
in its optimistic case. Priority ordering aligns with decision-tree /
monotonic-chain formula classes that admit polynomial satisfiability.
If T-C lands in 2-SAT or Horn, priority ordering is natural. Arbitrary
boolean formulas would defeat the polynomial bound regardless.

**Incremental construction, not bulk rebuild.** Forced by efficiency.
Each primary added to the forward record extends the calculator's
representation by one tier per affected P entry. Bulk rebuild on each
primary would be O(n²) per primary × O(n²) primaries = O(n⁴), still
polynomial but loses the per-primary incrementality the forward pass
already has.

**Cyclic dependencies via iteration-to-fixpoint with empirical
termination.** Permitted by T-B; forced by the algorithm's structure.
Cyclic dependencies are real (a guess's swap conditions can reference
each other transitively). Iteration terminates because the bounded
false-symmetry count (T-B) bounds the per-variable flip count.
Polynomial iteration is plausible empirically; the worst-case proof
would tie T-B to the iteration bound directly. Currently empirical.

---

## Implementation plateaus

The calculator is large and the implementation is staged. Each plateau is
independently valuable as a research checkpoint, with measurable
deliverables.

### Plateau A — Caching and measurement

A strict superset of the current replay-based implementation, adding a
`(prefix-state-hash, branch) → (outcome-hash, canonical)` cache to the
backward pass. No algorithmic change.

What it delivers:

- Cache hit rate per primary, per graph class. High rate on CFI(K_m) for
  growing `m` is empirical evidence that route 1's state count stays
  polynomial.
- Distinct outcome counts per primary, the cleanest empirical measure of
  "how many pair-orbits does this cell host?" Diagnostic for T-B.
- Per-entry support-set size (which primaries' directions, when flipped,
  change this entry). Diagnostic for T-A.
- Wall-clock unblocking for larger graphs (CFI(K3), CFI(K4)).

The plateau-A test scaffold lives in
[`GraphCanonTests.CalculatorViability.cs`](../GraphCanonizationProject.Tests/GraphCanonTests.CalculatorViability.cs).

### Plateau B — DERIVED tracking and per-primary split tables

Structural intermediate. Adds DERIVED-record bookkeeping (closes §6.4's
specification corner; see strategy §11.3 for tie-breaking) and
precomputes per-primary `(pair, direction) → (sub-cells, P entries)`
tables.

What it delivers:

- Direction-flip subproblem becomes O(1) per primary. The polynomial
  bound's "easy half" lands cleanly.
- Pair-rotation still replays but with cached per-step results; constant
  factor improvement on the inner loop.
- Concrete check that T-A holds on the test corpus — support set sizes
  computed from driver pointers are directly measurable.

This plateau is achievable in this project independently of whether T-C
is ultimately resolved. It's a structural improvement that pays off
regardless.

### Plateau C — Full tier representation

The polynomial-bound target. Replaces replay-based branch evaluation with
the priority-tier symbolic representation per P entry. LexMin via
tier-by-tier evaluation. No fixpoint iteration; the per-tier
satisfiability check resolves each tier directly.

What it requires:

- T-C's formula class characterised (or at least an empirical-polynomial
  satisfiability procedure for the cases tested).
- T-A and T-B held formally enough to bound the representation size.
- Lean formalisation aligned with the C# operational semantics.

This is the plateau that resolves the polynomial bound. Reaching it
requires the open theoretical work, not just engineering.

---

## Open questions

In priority order:

1. **T-C's formula class.** What's the structural class of boolean
   formulas the tier evaluation produces? Candidates to test: 2-SAT,
   Horn, monotone, linear over Z₂, FPC. A characterisation that lands in
   any of these closes the polynomial bound.
2. **T-A's formal proof.** Show that support sets are bounded by cell-
   tier depth × cell size, with warm-refinement uniformity carried
   through closure. Concrete Lean work, building on §6.2's partial proof.
3. **Cyclic dependency polynomial termination.** Empirical; structural
   proof would tie T-B's count bound directly to the iteration count.
4. **Multi-vertex rearrangements in tier form.** Verify on test inputs
   with explicit k≥3 orbit structure (triangle, K_4 vertex orbits, etc.)
   that the tiered decomposition into pairwise primaries doesn't lose
   information needed for canonical reconstruction.
5. **XOR-style coupling case (CFI).** Verify experimentally on CFI(K_m)
   that tier evaluation runs in polynomial time as the parity-formula
   characterisation predicts. Instrumented via plateau A.
6. **Relation to Babai's quasi-polynomial bound.** If T-C lands in a
   class strictly between FPC and arbitrary boolean — i.e., quasi-
   polynomial but not polynomial — the calculator's bound matches
   Babai's. This would not resolve GI ∈ P but would be a
   non-trivial standalone result.

---

## What "the calculator is done" looks like

The project's terminal state for this component is:

- Plateau C implemented in C# and in line with the strategy doc.
- T-A, T-B, T-C proven (or replaced by strictly weaker conditional
  versions) in Lean alongside §6.2's existing partial proof.
- The empirical bound on the existing test corpus matches the proven
  bound.
- The CFI test family runs in polynomial time, validated against an
  external canonizer.
- The doc trio (strategy / calculator / implementation) is self-
  contained for an external reader to verify the polynomial claim.

Anything short of this is a research checkpoint, not the terminal state.
The honest position: the project is currently between plateaus A and B
on the implementation side and well before the T-C resolution on the
theoretical side.
