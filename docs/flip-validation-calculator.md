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
narrower: given the *structured output of the forward pass* (the list of
primary guesses and the precomputed prefix state stack), decide which
direction assignment to the primaries produces the lex-smaller canonical,
without re-running the forward pass per direction combination.

This narrowing matters for the polynomial-bound argument. The calculator
operates on inputs that are already structured by 1-WL refinement and the
forward pass's deterministic guess selection. It does not face "arbitrary
graph, find canonical" — it faces "given this prefix state plus these
direction options, which wins LexMin?" The forward pass has already done
the easy parts.

The honest framing: the calculator's polynomial bound is equivalent in
strength to GI ∈ P (one implies the other, see strategy §6 preamble). The
*specific shape* of the calculator's input may admit a polynomial procedure
where free-form canonization does not — that is the project's bet.

---

## Architectural form: priority-tier swap-condition rules per P entry

> **Status (post-Phase 2 v2):** the AND-of-XOR class assumption underlying
> the description below has been empirically refuted on every tested graph,
> including 1-WL-handleable cases. The architectural form is still useful
> as a design target, but the specific class restriction (linear over Z₂)
> needs replacing. See "Structural impossibility" and "Alternative classes"
> sections below.

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
| 6.5 (every canonical reachable from any pair selection) | **Rotation mechanism stripped (2026-05-xx)** — empirically broke AND-of-XOR closure; backward pass reverted to direction-only flip per primary | Tests on multi-orbit cells (C4+K2 #56) now fail until calculator replaces what rotation was doing |

---

## How the theorems shape the design

> **Status note (post-Phase 2 v2):** The design decisions below are still
> structurally correct (tiered evaluation, support tracking, etc. all
> apply regardless of class). What's changed is the target class itself —
> "linear over Z₂" is empirically + structurally refuted. The decisions
> are reframed below under "if Horn / monotone / etc. is the class
> instead." See "Alternative classes" and the status snapshot.

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

### Plateau A — Single-flip probing and XOR-fit instrumentation

Instrumentation that surfaces the load-bearing measurements before any
algorithmic change. Implemented as two methods on
[`CanonGraphOrdererFlipValidation`](../GraphCanonizationProject/CanonGraphOrdererFlipValidation.cs):

- **`ProbeRotationsSingleFlip` (Phase 1).** Runs the forward pass to get
  a baseline P, then probes one direction flip per primary (the
  current backward-pass alternative space, post-§6.5-strip). Records
  per-probe affected-entry sets, per-entry coupling-candidate counts,
  and aggregate stats.
- **`ProbeXorCouplings` (Phase 2).** For each coupling-candidate entry
  (one affected by ≥ 2 primary-direction-flips), computes XOR fit
  coefficients from baseline + single-flip substitutions, verifies on
  pair-substitutions. Reports fit rate per graph.

The Plateau-A test scaffold lives in
[`GraphCanonTests.CalculatorViability.cs`](../GraphCanonizationProject.Tests/GraphCanonTests.CalculatorViability.cs).

Phase 2 was run in two versions:
- **v1** (pre-§6.5-strip): probed over rotation alternatives, naive
  representative-per-primary basis.
- **v2** (post-§6.5-strip): probed over direction flips only, clean
  variable basis.

Both versions empirically refuted the AND-of-XOR class assumption.
See "Empirical findings" and "Structural impossibility" sections.

What it delivers:

- Empirical diagnostic for T-A's "support set per entry" claim
  (Phase 1's coupling-candidate counts and per-entry probe affect-counts).
- Empirical diagnostic for T-B's "false-symmetry count" claim (Phase 1's
  false vs true symmetry probe counts).
- Empirical test of T-C's "AND-of-XOR class" claim under a chosen
  variable basis (Phase 2's fit rates).
- Wall-clock unblocking — CFI(Cycle3) now runs in ~10 s, vs minutes for
  the current backward-pass-with-fixpoint code.

Findings are recorded in the "Empirical findings" section below.

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

## Empirical findings (Phase 1 + Phase 2 v1)

### Phase 1: single-flip probing — what changed

Single-flip rotation probing was run on small graphs and on CFI(Cycle3).
Headline numbers:

| Graph | n | Primaries | TotalProbes | FalseSym | TrueSym | MaxAffected | CouplingCands | AvgAff(FS) |
|---|---|---|---|---|---|---|---|---|
| 2K2 | 4 | 5 | 15 | 10 | 5 | 8 | 12 | 4.40 |
| K4 | 4 | 5 | 15 | 10 | 5 | 8 | 12 | 4.40 |
| C4 | 4 | 6 | 16 | 11 | 5 | 8 | 12 | 4.36 |
| C4 + K2 | 6 | 13 | 23 | 18 | 5 | 8 | 18 | 4.44 |
| CFI(Cycle3) even | 18 | 149 | 453 | 301 | 152 | 230 | 306 | 52.25 |
| CFI(Cycle3) odd | 18 | 152 | 456 | 304 | 152 | 230 | 306 | 54.35 |

Observations:

- **PrimaryCount on CFI is near-maximal.** 152 primaries for n = 18
  (cap n(n−1)/2 = 153). Almost every P entry is a direct write; TC
  closure contributes very little. Polynomial in n² as T-B predicts,
  but the upper bound is tight.
- **CFI's per-probe impact is large** (avg 52 entries affected per
  false-symmetry probe; max 230 out of n² = 324). Each rotation cascades
  through many entries — the parity coupling.
- **Coupling-candidate density is high on CFI.** 306 of 324 P entries
  are touched by ≥ 2 probes. Most entries depend on multiple primary
  decisions.

These results are consistent with the calculator design's structural
expectations: false-symmetry count is polynomial-bounded, coupling
density is high.

### Phase 2 v1: XOR-fit under naive single-representative basis

For each coupling-candidate entry, Phase 2 v1 picks the first probe per
involved primary as a representative, computes XOR coefficients from
baseline + single substitutions, and verifies on all pair substitutions.

| Graph | Coupling Candidates | Fit Rate | Pair-match avg (non-fit) |
|---|---|---|---|
| 2K2 | 8 | 25% | 11% |
| K4 | 8 | 25% | 11% |
| C4 | 10 | **0%** | 13% |
| C4 + K2 | 16 | 12.5% | 9% |
| CFI(Cycle3) even | 296 | **0%** | 0.3% |
| CFI(Cycle3) odd | 302 | **0%** | 0.4% |

**XOR fit rate is essentially 0% across all tested graphs, including CFI
itself where parity (XOR) is the construction's defining algebraic
structure.** Pair-match rates on non-fitting entries average ~0.3% for
CFI — systematic mis-alignment, not random noise.

### Interpretation

The 0% fit rate doesn't directly falsify T-C. It falsifies the *naive
empirical test* of T-C — specifically, that single-representative-per-
primary is a workable variable basis.

The structural reason it fails: each primary in the algorithm has
*multiple* alternative rotations, and different alternatives within one
primary can have semantically different effects on entries. Picking one
arbitrary alternative as "the variable" mixes:
- Alternatives that flip a gadget bit cleanly;
- Alternatives that flip a different gadget bit;
- Alternatives that flip multiple bits;
- Alternatives in true-symmetry orbits that don't flip anything.

Testing XOR fit over this mish-mash basis gives essentially random pair
predictions, hence the systematic 0% match rate.

What the result tells us:

1. **The naive variable basis does not work.** Phase 2 must use a
   structurally-aware variable basis, not first-affecting-alternative.
2. **T-C remains untested.** Whether the underlying algebraic structure
   is XOR (or some other linear-poly-time-checkable class) is still
   open. The Phase 2 v1 result is a measurement bug, not a structural
   refutation.
3. **The calculator's variable model needs refinement.** Single-primary-
   level variables are too coarse. Either each alternative is its own
   variable (with mutual-exclusion constraints across alternatives at
   the same primary), or alternatives need to be grouped into
   equivalence classes based on their effect-fingerprints.

### Phase 2 v2: §6.5 strip + direction-only basis

After diagnosing that Phase 2 v1's naive variable basis mixed rotation
alternatives with semantically-different effects, we took the cleanest
fix: **strip §6.5 pair rotation entirely** and rerun with direction-only
variables. The expectation (matching the project's original mental
model) was that direction-only branching should suffice over the
partial order, and rotation was a workaround for greedy direction-flip
getting stuck on multi-orbit cells.

**Implementation changes:**

- `Primary` struct stripped of `CellSnapshotA`/`CellSnapshotB`.
- `PickAndApplyGuess` no longer captures cell snapshots.
- `BackwardPass` simplified to a single deepest-first sweep with
  direction-only flip per primary (no rotation enumeration, no fixpoint
  iteration).
- `Run` no longer iterates the backward pass to fixpoint (rotation was
  the reason fresh deeper primaries appeared mid-sweep).
- `ProbeRotationsSingleFlip` simplified: one probe per primary, the
  direction flip.
- `ProbeXorCouplings` updated: representative = the direction flip; one
  variable per involved primary.

**Test consequences:** 10/11 FV tests still pass. Only
`FV_KnownGraphs_DifferentScramblings_ProduceSameCanonical(size: 6)`
fails — specifically graph #56 (C4 + K2), the known multi-orbit-cell
case. This is the expected diagnostic that "calculator not yet built";
all 1-WL-handleable cases stay correct.

**Phase 2 v2 results (direction-only basis):**

| Graph | n | Primaries | Coupling Cands | FitRate | Pair-match avg (non-fit) |
|---|---|---|---|---|---|
| 2K2 | 4 | 5 | 4 | **0%** | 17% |
| K4 | 4 | 5 | 4 | **0%** | 17% |
| C4 | 4 | 6 | 6 | **33%** | 17% |
| C4 + K2 | 6 | 13 | 16 | 12.5% | 12% |
| CFI(Cycle3) even | 18 | 149 | 264 | **0%** | 0.4% |

The fit rate stayed essentially 0%. Some small-graph entries fit
(notably C4's k=2 entries at 33%), but CFI dropped to 0% with
near-zero pair-match rates.

**This rules out** the most plausible reading of Phase 2 v1's failure
— "wrong variable basis." With the cleanest possible variable basis
(direction-only, one per primary), the XOR fit still doesn't hold.

The structural impossibility section below explains why.

---

## Structural impossibility: why AND-of-XOR cannot fit (with rank-based canonical)

Walking the construction operations carefully reveals two independent
reasons the AND-of-XOR class is unreachable, independent of variable
basis choice. Both fall out of structural facts about the algorithm,
not measurement artefacts.

### Reason 1: TC closure without driver tracking is OR-of-ANDs

A direct-write primary `P[a, b] = d_i` contributes a single literal,
which is trivially in AND-of-XOR.

A TC-derived entry `P[u, v] = LESS` holds iff *there exists a chain*
`u → x₁ → ... → x_k → v` of LESS edges. Boolean form:

```
P[u, v]_LESS = ∨_{chains c} (∧_{link l ∈ c} l_LESS)
```

This is **DNF (OR-of-ANDs)**, not AND-of-XOR. The current
implementation re-runs TC from scratch (no canonical driver per
derived entry), so TC-derived entries' formulas are literally DNF.

**Fix candidates:**

- **Canonical driver tracking** (the §11.3 spec corner): assign a
  canonical chain per derived entry. Formula collapses to AND of
  literals — a degenerate AND-of-XOR. Works only when the driver
  chain is stable across direction flips. If the driver chain becomes
  broken, a different chain takes over and the formula re-acquires
  OR structure. Driver stability holds for graphs where chains don't
  overlap, fails in general.

- **TC relegation** (proposed reformulation): *every* P entry
  becomes a direct primary with its own direction variable. No TC
  derivation, no chains, no OR over chains. The TC consistency
  requirement (no cycles in P) is re-encoded as constraints the
  LexMin engine respects: `(P[u, x] = LESS) ∧ (P[x, v] = LESS) →
  (P[u, v] = LESS)`. Each such implication is a Horn clause
  (one positive literal). The full constraint system is **Horn-CNF**
  with `O(n³)` clauses over `O(n²)` variables. **Horn-SAT is in P**;
  the calculator's per-entry satisfiability check would be unit
  propagation in linear time. **This eliminates Reason 1 entirely**
  — no OR-of-ANDs anywhere — and lands the class in Horn-CNF, which
  is strictly richer than AND-of-XOR but still polynomial-satisfiable.

The TC relegation reformulation is the more structurally promising
of the two: it doesn't require driver-stability assumptions, and it
moves the calculator's class target to Horn-CNF (Horn structurally
matches the implications TC generates).

### Reason 2: canonical-from-rank is structurally non-linear in P entries

The canonical matrix at position (i, j) is
`adj[σ⁻¹(i), σ⁻¹(j)]`, where `σ` is determined by rank counts:
`rank(v) = #{u : P[u, v] = LESS}`.

Rank is an **integer count**, not a boolean. `σ⁻¹(i)` is "the vertex
whose rank is `i`" — an integer-dispatch from boolean P variables.

For canonical entries to be linear over Z₂ in P variables, the
position-to-value mapping would need to be XOR. But integer dispatch
from boolean variables is not linear: `σ⁻¹` cycles through
permutations, and the canonical entry at (i, j) depends on which
specific vertex landed at rank `i` and rank `j`, not on a XOR
combination of their P-entry directions.

This holds **regardless of variable basis**. Direction variables,
P-entry variables, rotation variables — they all enter `σ` non-
linearly through the rank-count integer-dispatch.

### Implication

The "AND-of-XOR over linear variables" form was the calculator's
load-bearing class assumption. **Both reasons above falsify it
structurally, not just empirically.** Reason 1 has a clean fix
(TC relegation; see above) that lands the class in Horn-CNF.
Reason 2 is independent and persists even after Reason 1 is
addressed — rank-based canonical reading is non-linear in P entries
regardless of how P is constructed.

This means the calculator's polynomial bound — *as originally
conceived as AND-of-XOR* — cannot be reached via XOR-SAT / Gaussian
elimination. But Horn-CNF (post-TC-relegation) is structurally close
and is polynomial-satisfiable. The remaining obstacle is Reason 2:
either the canonical definition needs to change to something
compatible with the chosen tractable class, or the rank-counting
mechanism needs explicit auxiliary-variable encoding that stays
polynomial-sized in the chosen class.

---

## Alternative classes considered

Three classes that are strictly broader than AND-of-XOR but still
admit polynomial-satisfiability under suitable restrictions. Each
has open questions about whether the algorithm's formulas actually
land in it.

### Horn (monotone-implication CNF) — current most-promising target

Each clause has ≤ 1 positive literal. Polynomial-satisfiability via
unit propagation, linear-time.

**Why it fits naturally — given TC relegation.** With every P entry
as a direct primary (the TC-relegation reformulation, see "Reason 1
fix candidates"), the TC consistency requirement becomes Horn-CNF
directly: `(P[u, x] = LESS) ∧ (P[x, v] = LESS) → (P[u, v] = LESS)`
is exactly a Horn clause. `O(n³)` such clauses, `O(n²)` variables.
This is the cleanest structural match for the algorithm's natural
constraint shape.

**What's not yet handled:** Rank-counting (Reason 2). Integer-
dispatch from boolean P entries to canonical positions requires
encoding "rank(v) = i" as auxiliary boolean indicators. "At-most-one"
is Horn-pairwise (mutex clauses); "at-least-one" is `X_1 ∨ X_2 ∨ ...
∨ X_k`, which is **not Horn** (all-positive clause). Encoding
rank-counting in pure Horn requires either:
- Auxiliary variables and clauses that simulate counting indirectly
  (e.g., comparator chains), polynomial-sized but bulky.
- Accepting a slightly broader class (e.g., dual-Horn or Krom-Horn
  hybrid) that's still polynomial-satisfiable.
- Or restructuring the canonical reading to avoid rank-counting
  altogether (see "Restructuring options").

**Empirical status:** untested. Phase 2 measured XOR fit; a Horn-fit
test would need separate instrumentation (unit-propagation verifier
rather than Gaussian elimination). Phase 3 in the natural sequence.

### Monotone boolean (positive AND/OR only)

No negation, so monotone-SAT is trivial (set all variables true).
Monotone-OPTIMIZATION (find lex-min satisfying assignment) is in P
for some cases (P-complete in general, but bounded-arity is easier).

**Why it might fit:** "P[u, v]_LESS" and "P[u, v]_GREATER" become
separate positive variables. TC chains compose positively. Direction
flip becomes "swap which variable is true."

**What breaks:** Rank-counting again. And antisymmetry (`P[u,v]_LESS`
and `P[u,v]_GREATER` can't both be true) requires negation or
mutual-exclusion. Encoding this in pure monotone form needs
auxiliary structure.

**Empirical status:** untested.

### Fixed-point logic with counting (FPC)

The natural logic for 1-WL. Polynomial model-checking. Captures the
strength of 1-WL refinement.

**Why it might fit:** 1-WL refinement IS the algorithm's
discriminator. The forward pass's deterministic guess selection from
canonical cell IDs is FPC-expressible.

**What breaks:** **CFI is FPC's textbook counterexample.** FPC fails
to distinguish CFI(K_m) for all m. So if the calculator's formulas
reduce to FPC, CFI canonization is impossible at that level. The
polynomial bound on FPC graphs is fine; CFI would need something
strictly stronger.

**Empirical status:** known-incomplete on CFI by Cai-Fürer-Immerman
1992. Not a viable target for the polynomial-on-all-graphs claim.

### Algebraic circuits over Z₂ (with structural restriction)

Closed under AND, OR, XOR, negation. Polynomial-size representation
via DAG with sharing. Construction operations all preserve this
class.

**Why it might fit:** structurally, any polynomial-time-computable
function has a polynomial-size circuit. So the canonical's
representation in this class IS polynomial-size if GI ∈ P.

**What breaks:** satisfiability of arbitrary polynomial-size
algebraic circuits is NP-hard. Without additional structural
restrictions (bounded depth, monotone gates, specific algebraic
patterns), no polynomial evaluation.

**Empirical status:** the structural restriction that would land
this in P is exactly the missing insight the calculator design
hasn't identified.

---

## Restructuring options for the algorithm itself

If no alternative class fits the *current* algorithm's formulas
cleanly, the algorithm itself can be restructured to produce
formulas in a tractable class. Three paths worth noting:

### TC relegation (every entry becomes a direct guess)

The forward pass currently runs TC after every primary, deriving
new entries from chains. The reformulation: never run TC during
forward; every P entry becomes a direct primary with its own
direction variable. The TC consistency requirement (no cycles in
P) is enforced by the LexMin engine as Horn-CNF constraints (see
"Reason 1 fix candidates" and the Horn class entry above).

**Cost:** the forward pass produces `O(n²)` primaries instead of
`O(n)`. Each primary contributes one direct write; no derived
entries. Forward pass is simpler but generates a larger record.

**Benefit:** the OR-of-ANDs structure from TC chains is eliminated
entirely. The calculator's class target shifts from AND-of-XOR
(refuted) to Horn-CNF (polynomial-satisfiable, structurally
matches the resulting constraints).

**Constraint count:** `O(n³)` Horn clauses (one per `(u, x, v)`
triple) on `O(n²)` variables. Manageable; unit propagation linear
in clause count.

This restructuring closes Reason 1. Reason 2 (rank-counting
non-linearity in the canonical reading) is independent and would
need either of the other two restructurings below to address.

### Stable primary sequence (fixed-order enumeration)

Currently the forward pass picks the next primary based on current
cell structure, which depends on prior direction choices. So the
"variable set" (primary positions) is dynamic.

**Restructured:** pre-determine the primary order by a deterministic
rule that doesn't depend on cell structure (e.g., iterate over
unordered pairs in lex order). Forward pass becomes "for each (a, b)
in lex order, guess direction if P[a, b] = UNKNOWN."

**Cost:** loses cell-based pruning. Forward pass becomes more like
nauty's "individualize and refine each leaf" with a fixed enumeration.
Search space grows; polynomial bound depends on different invariants.

**Benefit:** variable set is stable. Direction-flip is pure
substitution. AND-of-XOR closure preserved (modulo the rank issue).

### Canonical-form change (drop rank-based reading)

The rank-based canonical is non-linear in P entries. If we change
the canonical definition to something direction-invariant (e.g., a
multiset-style encoding, or a representation where directions
factor out cleanly), we sidestep Reason 2.

**Cost:** the canonical wouldn't be the lex-smallest n×n adjacency
matrix. Equivalence with the standard canonical would need separate
proof.

**Benefit:** canonical entries are linear in P variables.

Neither restructuring has been tried. Both are open research
directions.

---

## Open questions

In priority order:

1. **T-C's class characterisation (load-bearing, now sharper).** Phase 2
   v1 and v2 together rule out linear-over-Z₂ (AND-of-XOR) as the class
   the algorithm's formulas land in — structurally falsified by the
   two arguments in "Structural impossibility" above. **Most promising
   remaining target: Horn-CNF**, which arises naturally under TC
   relegation (every P entry as a direct guess; TC consistency
   re-encoded as Horn clauses). Horn-SAT is in P. Other candidates:
   monotone boolean, algebraic circuits with some structural
   restriction. **Resolving T-C now means: (a) decide whether to
   relegate TC, (b) characterise the resulting formula class
   empirically (Horn-fit instrumentation), (c) handle Reason 2
   (rank-counting non-linearity) separately.**
2. **Variable basis confirmation (resolved).** Phase 2 v2 with direction-
   only variables still gave 0% fit on CFI, so the failure is *not* a
   variable-basis artefact. The variable model is acceptable; the class
   is what's wrong.
3. **Choose between class change vs algorithm restructuring.** Two
   options:
   - Keep the algorithm; find a class strictly broader than AND-of-XOR
     that fits the algorithm's natural formulas and is polynomial-
     satisfiable. (Per "Alternative classes considered" — Horn looks
     most promising structurally.)
   - Restructure the algorithm to produce formulas in a known
     tractable class. (Per "Restructuring options" — stable primary
     sequence + canonical-form change.)
   Both have unresolved feasibility questions.
4. **DERIVED tracking (still pending, now structurally required).** The
   "TC produces OR-of-ANDs" finding makes driver tracking a prerequisite
   for any class-fit attempt, not just an optimization. Implementing it
   is concrete; correctness depends on §11.3's tie-breaking rule.
5. **T-A's formal proof.** Support sets bounded by cell-tier depth × cell
   size. Empirically supported by Phase 1 data; Lean proof concrete and
   achievable, building on §6.2's partial proof.
6. **C4+K2 #56 test correctness.** Currently red after §6.5 strip.
   Resolution path: calculator handles direction branching globally
   (current backward pass is greedy, which is incomplete on multi-orbit
   cells). Until the calculator works, this is the visible diagnostic
   for "calculator not yet built." Alternative interim: enable exhaustive
   2^k direction enumeration in backward pass — exponential but correct.
7. **Relation to Babai's quasi-polynomial bound.** If the algorithm's
   formulas land in a class strictly between FPC and arbitrary boolean
   — i.e., quasi-polynomial but not polynomial-satisfiable — the
   calculator's bound matches Babai's 2^O(log³ n). Non-trivial standalone
   result if achieved.

### Resolved / superseded since the prior doc revision

- *"Variable basis identification"* — Phase 2 v2 (direction-only) ruled
  out variable basis as the cause of the 0% fit rate. Superseded by the
  structural impossibility argument.
- *"Phase 2 v2 paths v2a/v2b/v2c"* — v2 turned out to be the §6.5 strip
  + direction-only basis, not the proposed alternatives. Results are
  what informed the structural impossibility section. The original v2a
  / v2b / v2c proposals are no longer the path forward.

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

## Current position (status snapshot, 2026-05-19)

### Implementation state

The current `CanonGraphOrdererFlipValidation` implementation:
- **Forward pass:** unchanged — greedy single-pair guess + warm-refine + TC.
- **Backward pass:** direction-only flip per primary, single deepest-first
  sweep, no rotation, no fixpoint iteration. (§6.5 pair rotation stripped.)
- **Run:** single forward + single backward, no fixpoint loop.
- **Plateau A instrumentation:** `ProbeRotationsSingleFlip` (Phase 1) and
  `ProbeXorCouplings` (Phase 2) both adapted to direction-only basis.

**Plateau B (DERIVED tracking, per-primary split tables) has not started.**
The §11.3 driver-pointer specification corner is open, and DERIVED
tracking is now structurally required (not just an optimization) per
the "Structural impossibility" finding.

### Test state

- 10/11 FV tests pass.
- `FV_KnownGraphs_DifferentScramblings_ProduceSameCanonical(size: 6)`
  fails on graph #56 (C4 + K2). Known multi-orbit-cell case;
  expected diagnostic for "greedy direction-flip backward pass is
  incomplete without the calculator."
- All Phase 1/2 calculator-viability tests pass (they're measurements,
  not regressions).
- PartialOrderIR tests pass (unaffected).

### Theory state

- **T-A** (bounded support set per entry): empirically consistent with
  Phase 1 data; no formal proof yet.
- **T-B** (bounded false-symmetry count): empirically holds (primary
  count ≤ n(n−1)/2 by construction); no formal proof yet.
- **T-C** (polynomial-satisfiability of the formula class):
  - The linear-over-Z₂ / AND-of-XOR specialisation is **empirically
    refuted on every tested graph** (Phase 2 v1 + v2).
  - Structurally refuted by two independent arguments (see "Structural
    impossibility"): TC closure without driver tracking is OR-of-ANDs,
    and rank-based canonical is non-linear in P entries regardless of
    variable basis.
  - Whether the algorithm's formulas land in any *other* polynomial-
    satisfiability class (Horn, monotone, restricted algebraic
    circuits) is **untested** and is the new T-C target.

### Where the development iteration left off

The empirical journey reached a turning point:

1. §6.5 pair rotation was added as a pragmatic fix for the C4+K2
   failure with greedy direction-flip.
2. Phase 1+2 instrumentation surfaced that rotation variables made the
   variable basis incoherent → 0% XOR fit.
3. §6.5 was stripped, restoring the original "direction-only branching"
   model.
4. Phase 2 v2 with the clean direction-only basis **also** gave 0% fit,
   ruling out the variable-basis hypothesis.
5. Structural impossibility argument: AND-of-XOR is unreachable
   regardless of variable basis, due to TC's OR structure and rank-
   counting non-linearity.

The natural next steps are along three axes:

**Axis A: TC relegation + Horn-fit empirical test.**
- Modify the forward pass to emit a direct primary for every P
  entry that gets resolved (whether currently a direct write or a
  TC-derived entry). No TC in forward pass; instead, the engine
  treats TC consistency as Horn-CNF constraints.
- Adapt `ProbeXorCouplings` to test Horn-CNF satisfiability
  (unit propagation) instead of XOR-CNF (Gaussian elimination).
  Re-run on small graphs + CFI(Cycle3).
- If Horn-fit succeeds on graphs where XOR did not, that's
  empirical evidence for Horn as the calculator's class.
- This is the most structurally promising next step. It directly
  addresses Reason 1 of the structural impossibility argument.
- Reason 2 (rank-counting) remains; will need separate handling
  before the polynomial bound is fully recovered.

**Axis B: algorithm restructuring to address Reason 2.**
- Try a canonical-form change: drop rank-based reading, use a
  direction-invariant canonical that avoids `σ` non-linearity.
  Equivalence with standard canonization needs separate argument.
- Or stable-primary-sequence variant. Less directly aimed at
  Reason 2 but adjacent restructuring.

**Axis C: accept quasi-polynomial.**
- Run Phase 2-style probing on disjoint CFI copies; characterise
  the growth rate. If it matches Babai's 2^O(log³ n), document as
  a known quasi-polynomial bound and move on.

**Recommended order:** Axis A first (TC relegation + Horn-fit). It's
the smallest structural change with the largest potential payoff: if
Horn fits, the calculator's class target is settled, Reason 1 is
truly closed, and only Reason 2 remains. If Horn-fit also fails, the
class is even more restrictive than expected and Axis B or C
becomes necessary.

### Reading order for context recovery

For a new development iteration picking this up:
1. Read [`flip-validation-strategy.md`](./flip-validation-strategy.md)
   for the algorithm's basic shape.
2. Read this doc through the "Structural impossibility" section for
   the central finding.
3. Read "Alternative classes" and "Restructuring options" for the
   path-forward options.
4. Check this status snapshot for the latest concrete state.

The current code in
[`CanonGraphOrdererFlipValidation.cs`](../GraphCanonizationProject/CanonGraphOrdererFlipValidation.cs)
matches the description in this snapshot; the FV and CV test files
exercise it.
