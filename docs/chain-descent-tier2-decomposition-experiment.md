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
