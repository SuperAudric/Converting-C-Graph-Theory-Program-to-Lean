# Tier-2 decomposition experiment

**Status:** experimental, expected to be folded into a permanent doc or deleted
once the experiment concludes. Sister to
[`chain-descent-matroid.md`](./chain-descent-matroid.md) (which closed the
matroid framing) and
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md) §6 (which
sharpened the encoded-Johnson gap).

---

## 1. Purpose

The matroid framework on `cl_prov` closed without producing a Tier-2 detector
(matroid memo §8.4). The natural follow-on is *structure-tree* canonization in
the Luks/Babai sense: detect an outer symmetry factor, quotient by it, recurse
on the quotient, lift back. The conjectured payoff: the encoded hidden Johnson
becomes a `(Z₂ᵐ, refinement-resistant) ⋊ (S_n, cascading)` decomposition
(calculator.md §7) made *operational* by chain-descent.

This experiment tests, on one concrete instance, whether the three load-bearing
pieces of that recursion are reachable from the existing chain-descent state:

> **Q1 (detection).** Does some polynomial, iso-invariant computable feature
> over chain-descent's state — most plausibly `cl_prov` circuit supports or 1-WL
> on individualized inputs — recover the gadget structure of a CFI-encoded
> Johnson graph?
>
> **Q2 (quotient).** Given a recovered gadget structure, can we construct a
> typed quotient graph H' such that canonical(H') + per-gadget twist data
> uniquely determines canonical(CFI(H))?
>
> **Q3 (post-quotient cascade).** Does the quotient H' canonize cheaply by the
> existing chain-descent oracle, i.e., does the Johnson layer cascade once the
> CFI layer is stripped?

If all three are yes on this instance, we have a candidate Tier-2 algorithm to
generalize and try to prove polynomial (or quasi-polynomial). If any is no, the
no localizes which piece is the bottleneck.

This is **not** an attempt to settle Tier-2 in general, nor to claim polynomial
bounds. It is a one-instance probe.

---

## 2. Test instances

The project already ships
[`CfiGraphGenerator`](../GraphCanonizationProject/CfiGraphGenerator.cs) with
named bases. Relevant sizes:

| Base graph | `|V|` of base | CFI vertex count | Notes |
|---|---:|---:|---|
| C₃ (triangle) | 3 | 18 | Smallest CFI; paper-tractable. Calibration. |
| K₄ | 4 | 40 | Aut(K₄) = S₄. Tractable on paper with effort. |
| Petersen = J(5,2) | 10 | 100 | **Main case.** Aut(Petersen) = S₅ acting as Johnson. |

**Sequence:**

1. **CFI(C₃) — paper calibration.** Small enough to enumerate every vertex's
   1-WL signature, every cl_prov closure of single-pair seeds, by hand. Confirms
   the gadget structure is *visible* somewhere in chain-descent's state.
2. **CFI(K₄) — code dry run.** Same measurements automated. K₄'s Aut(S₄) is
   nontrivial enough to test that the quotient construction handles `|Aut(H)|`
   bigger than the gadget count.
3. **CFI(Petersen) — the actual question.** S₅ acting as Johnson. This is the
   first instance where the *outer* group is a genuine Johnson — what we
   ultimately care about.

If CFI(C₃) already fails Q1 (gadget structure invisible), don't proceed; the
detection problem is harder than this experiment can probe.

---

## 3. The three measurements

### 3.1 Q1 — circuit / refinement detection of gadget structure

**Hypothesis.** For each pair `(u, v)` with both endpoints inside the same
gadget, `cl_prov({(u,v)})` is contained within that gadget (plus possibly its
immediate edge-bridge partners). For pairs crossing gadgets, the closure spans
both gadgets and their bridges. So gadget membership is recoverable from the
*support equivalence* of single-pair closures.

**What to compute.**

- For every unordered pair `{u, v}` in CFI(H) (or a tractable subset for
  Petersen — use a quotient of the symmetric pairs first), compute
  `cl_prov({(u, v)})`.
- Group pairs by support-set equality (or near-equality — within bridge
  thickness).
- Compare the induced partition of vertices against the known gadget assignment
  (available from `CfiPair.VertexRoles`).

**Pass condition.** The closure-support partition is a *refinement* of the
gadget partition (no cross-gadget mixing) and *coarse enough* to identify
gadgets uniquely (each gadget appears as one or a small bounded number of
support classes).

**Alternative if cl_prov is too coarse or too fine.** Try:
- 1-WL signatures on (CFI(H), individualized pair `(u, v)`) — recover gadget
  membership via the refinement structure rather than closure structure.
- Pair-warm-refinement signature multisets — finer than 1-WL, may resolve
  gadgets that 1-WL conflates.

These are fallback detectors that still satisfy the iso-invariance and
polynomial-time requirements. Record which one (if any) succeeds.

### 3.2 Q2 — quotient construction

**Hypothesis.** Given the gadget partition from Q1, the quotient operation:

1. Replace each gadget by one vertex carrying a `vertexType` = a polynomial
   invariant of the gadget's internal structure (for standard CFI this is just
   `degree(v) in H`, since all degree-d gadgets are isomorphic).
2. For each edge-bridge between gadgets, produce one edge in H' carrying an
   `edgeType ∈ {0, 1, ?}` recording the twist state. **First pass:** use `?`
   (Unknown) for every edge — this defers the Z₂-coset resolution to the linear
   oracle. **Second pass (optional):** fix an arbitrary canonical section
   (e.g., pick edgeType = 0 wherever possible, using a spanning tree of H to
   propagate); test whether the section is iso-invariant.

**Iso-invariance check.** Run quotient construction on two scramblings of the
same CFI(H); compare canonical(H'_1) vs canonical(H'_2). They must match. If
they don't, the gadget identification or the edge-type assignment isn't
canonical.

**Information loss check.** Given canonical(H') + per-gadget data, can we
reconstruct CFI(H) up to the Z₂-coset ambiguity? Reconstruct manually for
CFI(C₃) to verify.

### 3.3 Q3 — post-quotient cascade

**Hypothesis.** With H' = H typed by gadget+edge-twist invariants, the existing
chain-descent cascade oracle handles H' in polynomial time. For
H = Petersen, this should be near-trivial: Petersen is distance-regular,
cascades after one individualization. With edge labels in {0,1,?}, the question
is whether the labels disrupt that cascade — they shouldn't, because edge
labels only refine the partition, never coarsen it.

**What to compute.** Run `CanonGraphOrdererChainDescent.Run(H')` on the
quotient. Measure:
- Number of descent nodes
- Number of "Unknown" edges resolved by the (currently absent) linear oracle —
  for the first pass this counts how many ?-edges remained, which the linear
  oracle would have to handle
- Total budget consumed vs. `B(|V(H')|)`

**Pass condition.** Node count is polynomial in `|V(H')|`, not in `|V(CFI(H))|`.
The linear oracle's gap is recorded but not blocking — if Q3 passes
in everything except `?`-resolution, the linear oracle is the known
specified-but-not-built component (calculator.md §6) and is the right next
target.

---

## 4. Success criteria

| Outcome | Means | Next move |
|---|---|---|
| All three pass | Detection works; quotient is sound; inner cascades. | Generalize: build the detector + quotient as a wrapper around `ChainDescent.cs`. Re-test on more CFI bases. Open the linear-oracle workstream for ?-edge resolution. |
| Q1 fails | Closure/refinement features don't recover gadgets. | The detection problem is the bottleneck. Either find a stronger detector (pair-warm-refinement? cycle-space invariants?) or conclude the approach needs a non-chain-descent input. |
| Q1 passes, Q2 fails | Detection works but the quotient isn't iso-invariant or loses information. | Re-spec the quotient. Likely the issue is the edge-type assignment — switch from `?` to canonical section, or vice versa. |
| Q1+Q2 pass, Q3 fails | Quotient is right but Johnson layer doesn't cascade after stripping. | This would contradict calculator.md §7's decomposability claim — would be a real finding. Investigate which layer's residual symmetry blocks cascade. |

---

## 5. Phased enactment

**Phase A — paper calibration on CFI(C₃).** (1–2 days of focused work.)

1. Write out the 18 vertices of CFI(C₃) with `VertexRoles` annotations.
2. Compute 1-WL signatures by hand. Verify that subset-vertices and
   edge-endpoint-vertices are 1-WL-separable (they have different degrees).
3. For one representative pair from each "natural class" (intra-gadget subset
   pair, intra-gadget endpoint pair, inter-gadget bridge pair), compute
   `cl_prov` closure by hand. Tabulate support sets.
4. Assess Q1 pass/fail.
5. If Q1 passes: write down the quotient H' for C₃ by hand. Verify
   iso-invariance against one re-scrambling. Run mental cascade on H'.

No code in Phase A — purely pen and paper. The point is to know what the
experiment *should* show before any code runs.

**Phase B — automated probe.** (Code work, gated on Phase A.)

1. Add a small experiment harness in C# (probably a new test file under
   `GraphCanonizationProject.Tests/`, not production code) that:
   - Builds a CFI pair via `CfiGraphGenerator.Generate(baseName)`
   - For each pair (u,v), computes `cl_prov({(u,v)})` — port from Lean spec
     (`commitsToP` + `transitiveClose` + filter) or reimplement (it's
     ~30 lines).
   - Computes the support-equivalence partition.
   - Compares against `VertexRoles`-derived gadget partition.
2. For instances where Q1 passes, hand-code the quotient construction (also a
   test-bed utility, not production code).
3. Run chain-descent on the quotient. Compare against
   `CfiPair.Even.Canonical` / `CfiPair.Odd.Canonical` (the project's existing
   canonization paths).
4. Iterate: C₃ → K₄ → Petersen.

**Phase C — generalize or backtrack.** Decision point. If Q1/Q2/Q3 all pass on
Petersen, fold the detection + quotient into a permanent doc and start a real
implementation. If anything fails, document the failure and assess whether
another Tier-2 route (calculator.md §9) is more promising.

---

## 6. Out of scope

This experiment deliberately does not address:

- **Polynomial bound.** Even if all three questions pass, the cost of detection
  + quotient + recursion is not analyzed here. Quasi-polynomial is the natural
  starting bar (matching Babai); proving it is a separate workstream.
- **Iso-invariance proof.** Q2's iso-invariance check is empirical, on a few
  scramblings. A real proof obligation lives in strategy.md §15 #2.
- **IR blind spots.** Rigid IR-resistant graphs (Neuen–Schweitzer multipede)
  remain flagged. The decomposition recursion doesn't help — there's no outer
  symmetry to detect.
- **`A_k`-hiding constructions.** No known construction; the experiment can't
  test against one. If Petersen-based CFI passes, that's evidence the
  decomposition works for the *known* hidden-Johnson candidates, not proof it
  works for hypothetical worse ones.
- **Lean formalization.** This experiment is empirical. If it succeeds, the
  Lean side picks up the detection lemma and quotient construction.

---

## 7. Connection to existing work

- **`cl_prov` (ChainDescent.lean §14).** The detection probe uses `cl_prov`
  directly. The CL0–CL3 closure properties (now all proved in the recent
  branch) are what make support-equivalence a well-defined operation.
- **Descent spine (`warmRefine_agree_off'`, recently extended in Lean).** The
  spine theorem says all `2^d` directions of a `d`-decision subtree share one
  partition. If the quotient construction collapses one such subtree per
  gadget, the spine guarantees the result is direction-blind — i.e., the
  per-gadget twist choice doesn't affect the quotient partition. This is the
  cleanest formal hook the experiment leans on.
- **Hidden-Johnson Piece C (hidden-johnson.md §5).** Scoped but not proved. If
  this experiment passes Q3 on CFI(Petersen), it's empirical evidence Piece C
  is reachable — the cascading half of "Johnson scheme graphs cascade" would
  apply to the quotient.
- **Matroid memo §10.** "Binary closure conjecture: every graph's propagation
  closure is a binary matroid." Q1 is testing whether `cl_prov` supports
  cluster by gadget — a structural version of the binary-closure claim,
  without the matroid axioms.

---

## 8. Phase A — paper findings on CFI(C₃)

**Date:** 2026-05-26.

### 8.1 Construction summary

Numbering vertices 0–17 across three gadgets G₀, G₁, G₂ of 6 vertices each
(matches `CfiGraphGenerator.BuildCfiPair` conventions for a C₃ base).
Each gadget has 2 subset-vertices (`a_∅`, `a_full`) and 4 edge-endpoints
(`e^b_{vw}` for two adjacent base vertices and two parities). Every vertex
has degree 2; total 18 edges (12 intra-gadget + 6 inter-gadget bridges).

Crucial structural fact: each gadget's intra-graph is **two disjoint 3-paths**
(`a_∅` connecting to its two `e^1` endpoints; `a_full` connecting to its two
`e^0` endpoints). The two parities are intra-gadget-disconnected — they meet
only through inter-gadget bridges.

### 8.2 Refinement results

- **Pre-individualization 1-WL:** one cell. Completely blind.
- **After individualizing v0 = a_∅(G₀):** fixpoint partition has cell-size
  signature `(1, 2, 2, 2, 2, 9)`. Five non-singleton cells:
  - `B = {v3, v5}` (v0's neighbors)
  - `D = {v9, v15}` (B's inter-gadget neighbors)
  - `E = {v6, v12}` (a_∅ vertices in G₁ and G₂)
  - `G = {v11, v17}` (e^1_{12} endpoints in G₁ and G₂)
  - `H` (size 9): each gadget's "opposite parity" trio
    `{a_full, e^0_{e1}, e^0_{e2}}`.
- **After individualizing v0 and a second vertex (e.g., v3 ∈ B):** cascade
  fully discretizes. So **CFI(C₃) is Tier 1: 2 individualizations suffice.**

### 8.3 Q1 assessment

The refinement partition is **skew to the gadget partition** — non-singleton
cells contain ≤ 1 vertex per gadget (cells B, D, E, G) or exactly 3 per gadget
(cell H). Gadget membership is recoverable but indirectly: the H-trio per
gadget plus the unique pairing data from B/D/E/G fixes the gadget assignment
up to the global gadget-permutation symmetry.

So Q1's strict form ("refinement cells *are* gadgets") **fails**, but its
operational form ("gadget assignment is recoverable in poly time from
refinement data") **passes** via post-processing.

`cl_prov` turns out **not** to be the right detector here, contra the
experiment doc's initial framing. `cl_prov` is purely the transitive closure
of the commit matrix — it sees the partial order built by guesses, not the
refinement structure those guesses *induce*. The detection signal lives in
1-WL signatures post-individualization, not in `cl_prov` directly.

### 8.4 Tier-1 caveat

**CFI(C₃) is Tier 1, not Tier 2.** It cascades. The Aut group is Z₂ ⋊ S₃,
where S₃ is the standard symmetric action on 3 elements, *not* a Johnson
action on subsets. So CFI(C₃) probes the calibration question ("is gadget
structure visible at all?"), not the hypothesis question ("does the encoded
Johnson factor surface?").

This is consistent with calculator.md §3's hardness map: cascade-class graphs
are Tier 1 regardless of group. The Q1+Q2+Q3 experiment as currently
specified can confirm gadget recovery works on CFI(C₃), and that's a
necessary condition, but the actual Tier-2 question is only probed by
CFI(Petersen).

### 8.5 Patterns to track for Lean

Behaviors observed on CFI(C₃) that may generalize, with notes on conditions
that would generalize or fail:

**P1 — Pre-individualization blindness.** 1-WL is constant on CFI(H) for any
base H with all base-vertices of equal degree. Every CFI vertex has degree 2
(for degree-2 base vertices) or other constant degree, and the 1-WL signature
at round 1 is symmetric. **Generalizes when:** base graph is regular. **Fails
when:** base graph has mixed degrees — then gadget-vertex degrees differ and
1-WL distinguishes vertex types immediately (and may distinguish gadgets via
neighborhood degrees). This is a CFI-construction property, not a deep one.

**P2 — Post-individualization cell-size signature.** The cell-size partition
`(1, 2, 2, 2, 2, 9)` for CFI(C₃) is iso-invariant (the cells themselves
aren't, but their sizes are). Generalizing: for CFI(H), the post-
individualization cell-size signature is a function of (H, individualized
gadget). **Conjecture:** the signature, together with the cell-adjacency
graph at fixpoint, uniquely identifies the base H up to isomorphism.
**Lean target:** state and try to prove "cell-size signature of
warm-refined CFI(H) with one fresh-colour individualization in gadget X(v)
equals a function f(H, v)". The descent-spine theorem
(`warmRefine_agree_off'`) already provides the direction-blindness
sub-component.

**P3 — Parity asymmetry from individualization.** Individualizing one vertex
in a gadget breaks the internal Z₂-parity symmetry of that gadget, and the
break propagates through bridges into the rest. The "opposite parity" union
across gadgets stays large (cell H has 9 vertices, with 3 per gadget). The
size-3 within H is exactly `|gadget intra-component on opposite parity| = 3`
(one a_full + two e^0 endpoints). **Lean target:** show that the post-
individualization partition's largest cell, intersected with each gadget,
has size `|gadget| / 2`. Direct calculation; one lemma per CFI vertex type.

**P4 — Cascade after 2 individualizations for tree-base CFI.** CFI(C₃) and
CFI(C_k) for small k cascade quickly because individualizing one parity-pair
across one gadget propagates uniquely. **Generalizes when:** the base has
small treewidth (the CFI cascade threshold is `tw(H) + 1` individualizations,
classic result). **Fails when:** base has high treewidth. For CFI(K_4)
(tw=3) we'd expect 4 individualizations; for CFI(K_{3,3}) (tw=3) also 4;
for CFI(Petersen) (tw=4) probably 5. **Implication for the experiment:**
CFI(Petersen) won't fully cascade in 1–2 individualizations, so its
post-individualization refinement will leave non-singleton cells —
*and those residual cells are the encoded Johnson's footprint*.

**P5 — Refinement-vs-gadget skewness.** The refinement partition cuts across
gadgets rather than respecting them. This is a CFI-design feature: the
construction's whole point is that local gadget structure looks uniform
from outside, so refinement can't separate vertices by gadget. **Generalizes
when:** the encoding is gadget-uniform (CFI-class). **Fails when:** the
encoding has gadget-distinguishing features. In Q1's strict form
("refinement cells = gadgets") this is a failure pattern; in the operational
form ("gadgets recoverable from refinement") it's not.

### 8.6 Decision point — what to do next

Phase A on CFI(C₃) confirms gadget structure is recoverable from refinement
data, but reveals the detection isn't via `cl_prov`. Three next steps in
descending order of value:

1. **Apply P2's cell-size signature analysis to CFI(K₄) (40 vertices) by
   code.** K₄ doesn't fully cascade in 2 individualizations (treewidth 3
   needs 4), so the residual cell structure begins to probe what
   CFI(Petersen) will look like. Tractable to code-test; can verify
   conjectures P2, P3 numerically.
2. **Re-spec Q1.** The current Q1 names `cl_prov` as the candidate detector;
   replace with "1-WL signature post-individualization" or "cell-size
   signature at refinement fixpoint." Q2 and Q3 are unchanged.
3. **Proceed directly to CFI(Petersen) post-individualization signature.**
   The cell-size signature there will tell us whether the residual
   (after cascade hits its limit) reveals the Johnson structure or not.

Recommended order: (1) → (3), with (2) folded in as a doc cleanup once we
know which detector wins. Step (1) keeps the calibration ladder honest;
jumping straight to (3) risks misreading a complex partition.

---

## 9. Phase B step 1 — CFI(K₄) probe results

**Date:** 2026-05-26. Code lives in
[`GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs`](../GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs)
and runs with `dotnet test --filter Tier2DecompositionExperiment`.

### 9.1 Picker rule clarification

The probe uses the **canonical chain-descent picker**: lowest cell id among
non-singleton cells (cells are id'd by lex-sort rank of their 1-WL signature),
within that cell the vertex with lex-smallest `VertexRoles` string. The role
tiebreak uses ground-truth labels and is consistent across scramblings, so it
serves the calibration purpose.

A side finding: the C₃ hand-trace in §8.2 assumed picking from the *smallest*
cell (size 2), but the canonical picker descends into the *lowest-id*
non-singleton cell, which at depth 1 of CFI(C₃) is the size-9 H-cell. Under
the canonical picker C₃ does **not** discretize in 2 individualizations — it
goes 1 → 6 → 10 → 14 cells over depths 0 → 3. The "cascade after 2
individualizations" claim in §8.2 was an artifact of the alternative pick.
Both pickers are valid (lowest-id is iso-invariant, smallest-cell is also iso-
invariant up to ties); the canonical chain-descent design uses lowest-id.

### 9.2 CFI(K₄) — measured signatures

| Depth | Individualized                  | Cell count | Cell sizes (desc) |
|---:|---|---:|---|
| 0 | (none)                           | 1  | [40] |
| 1 | `v0:subset:{}` (subset start)     | 14 | [8, 4, 4, 4, 4, 4, 2, 2, 2, 2, 1, 1, 1, 1] |
| 2 | `v0:end[w1]^0`                   | 24 | [2 × 16, 1 × 8] |
| 3 | `v2:subset:{w0,w3}`              | 40 | [1 × 40] — **discrete** |

The endpoint-start probe (`v0:end[w1]^0` at depth 1) gives a different but
isomorphic-orbit signature at depth 1 and also discretizes at depth 3.

### 9.3 Findings

**F1 — Iso-invariance of cell-size signatures: CONFIRMED.** Across the
identity input and one seeded permutation (seed=4711), all four signatures
(both starts × identity/permuted) match at every depth. Empirical support
for P2 on CFI(K₄). Stronger evidence needed at larger scale before
generalizing.

**F2 — Cascade depth for CFI(K₄) = 3, not 4.** The treewidth of K₄ is 3.
P4's original "cascade by depth tw(H)+1" was too generous. Both depth-1
starting orbits (subset-vertex and edge-endpoint) cascade at depth 3.
**Revised P4:** cascade depth ≤ tw(H), reached by depth ≈ tw(H) for both
Aut-orbits' starts. This matches the WL-individualization heuristic (each
individualization is ~+1 WL dimension; CFI is k-WL-resistant for k < tw(H);
so tw(H) individualizations suffice).

**F3 — P3's exact form does NOT generalize.** On CFI(C₃) depth 1 the largest
non-singleton cell had `|gadget|/2 = 3` per gadget (the H-cell, 9 vertices).
On CFI(K₄) depth 1 the largest cell has 8 vertices = 4 + 4 spanning G₂ and
G₃ — *not* the individualized gadget G₀, and concentrated in **two**
gadgets, not all four. The "|gadget|/2 per gadget" pattern is C₃-specific.

The actual generalization appears to be **cells classified by (refined
position within gadget, distance class to individualized vertex)**. The
individualized gadget refines most (8 cells in G₀: sizes 4,2,2,1,1 — plus
the singleton v0). Other gadgets retain larger residual cells, often paired
by base-edge structure. Worth formalizing as **P3' — cell-gadget overlap
matrix is a function of the base graph's distance structure from the
individualized base-vertex**.

**F4 — P5 (refinement skew to gadgets) confirmed on K₄.** Many depth-1
cells span multiple gadgets (e.g., cell 7 in the dump: 4 vertices in G₂, 4
in G₃ — no overlap with G₀ or G₁). Cells concentrated in one gadget exist
too (e.g., cell 12: all 4 in G₀). The overlap matrix is heterogeneous; cells
are not aligned with gadgets, but the overlap structure is iso-invariant.

### 9.4 What this means for the experiment trajectory

The detection question (Q1) is in good shape for CFI(K₄):
- **Cell-size signatures fingerprint the input up to isomorphism** (F1).
- **Cascade reaches discrete at tw(H) individualizations** under the
  canonical picker (F2), which would beat the budget `B(n) = n^c` for any
  fixed c on the cascade-class CFI family if proved.
- **The refinement structure is iso-invariant but not gadget-aligned** (F4)
  — so gadget recovery isn't direct; needs a post-processing step that
  reads the cell-gadget overlap matrix.

Next move in priority order:

1. **Scale up to CFI(Petersen).** 100 vertices, tw=4, expected cascade by
   depth 4 (per F2). Confirms F1+F2 at the encoded-Johnson scale. This is
   the actual Tier-2 probe.
2. **State P3' precisely** — the cell-gadget overlap matrix's structure as
   a function of (refined vertex-type within gadget, base-graph-distance to
   individualized base-vertex). A Lean lemma at this level would be a
   strong intermediate result.
3. **Compare picker rules** — re-run CFI(K₄) with the smallest-cell picker
   to see whether cascade depth changes. If yes, the picker rule is
   load-bearing and the chain-descent design's lowest-id choice may need
   re-examination for cascade-class graphs.

(1) is the actionable next step. (2) and (3) are slower analytical work.

