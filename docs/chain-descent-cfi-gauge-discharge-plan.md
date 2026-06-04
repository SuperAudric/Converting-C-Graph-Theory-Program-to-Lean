# Build plan — discharging the CFI gauge nut (`ResidualInvolutive` via P-separation)

> **STATUS (2026-06-04): Lemma A LANDED (axiom-clean); Lemma B next.** The build plan for the one remaining CFI
> obligation left after the de-classed coverage landed. Authoritative companions:
> [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) §7 (Part A staging, CFI-cov.3),
> [`chain-descent-declassing.md`](./chain-descent-declassing.md) (the de-classing architecture),
> [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) (landed declarations). Where
> this doc disagrees with the Lean source, the source wins. Archive when CFI-cov.4 lands.

---

## 0. Context — what's already landed, and the nut

The cross-branch harvest (Part A) reproduces the residual `P`-preserving automorphism group `Aut_S^P`
(`StabilizerAt`) from harvested generators, **soundness + completeness**, with the order `= ∏ basic-orbit
sizes`. Completeness was de-classed: `coversOrbits_of_residualInvolutive` /
`closure_eq_stabilizerAt_of_residualInvolutive` discharge the coverage witness `CoversOrbits` for the
**whole exponent-2 (`Z₂^d`) residual class in one theorem**, given:

1. `ResidualInvolutive adj P S` — every residual automorphism is an involution (`g * g = 1`);
2. `gens` contains every involutive residual automorphism (free when `gens = {all involutions}`);
3. a base sequence terminating at `IsBase` (CFI: `cfi_exists_base_seq`, odd-degree).

For CFI this was wired (`cfi_coversOrbits` etc.) against the stronger **gauge-generation** hypothesis. But
the **faithful de-classed nut is (1): `ResidualInvolutive`** — strictly weaker than gauge-generation (need
`g² = 1`, *not* "`g` is a literal cycle-space flip `cfiFlipAut F`"). Discharging `ResidualInvolutive` for
CFI in the base-resolved regime is this plan.

### Why it is conditional (do not expect it at `S = ∅` for non-rigid bases)

`Aut(CFI(H)) = Z₂^β ⋊ Aut(H)` is **not** exponent-2 when `Aut(H)` has non-involutions. So
`ResidualInvolutive adj P S` holds only where the `Aut(H)` factor is **killed** — i.e. the base layer is
resolved. This is the decomposability premise (calculator §7): resolve the cascading base layer first
(visible/scheme leg), and the gauge `Z₂^β` is a clean exponent-2 residual. The hypothesis that encodes
"base layer resolved" is **`PSeparatesGadgets`** (§2). Discharging *that* for the descent's actual `P` is a
separate, later obligation (the orthogonal visible leg); this plan takes it as a hypothesis.

---

## 1. The approach (chosen over the alternatives)

Target `ResidualInvolutive adj P S` under a `PSeparatesGadgets` hypothesis. Two lemmas:

- **Lemma A — gadget-preservation from P** (low risk): a residual automorphism preserving a gadget-separating
  `P` fixes every gadget. *The key move that sidesteps the subtle structural "every CFI automorphism
  preserves gadgets" (call it L1): gadget-preservation comes from **P-preservation + S-fixing**, not from a
  graph-recovery argument.*
- **Lemma B — per-gadget involution** (medium risk): a gadget-fixing CFI automorphism squares to `1`.

Then `ResidualInvolutive` = A + B, fed to the landed `coversOrbits_of_residualInvolutive`.

### Alternatives rejected
- **Full kernel lemma → gauge-generation** (`g = cfiFlipAut F`): needs L1 + the explicit cycle-space
  construction (symmetric/even `F`, global assembly). Heaviest; `ResidualInvolutive` needs only `g²=1`.
- **Rigid-base specialization** (`Aut(H)=1`): clean but does **not** cover the real test bases (K₄, K₃,₃,
  Petersen are vertex-transitive).
- **Refinement route for gadget-preservation** (colour-class = gadget via `warmRefine_invariant_of_isAut`):
  **fails** — separating gadgets by refinement needs individualized seeds, which *kill* the gauge group
  (gauge flips move seeds); gauge-alive and refinement-separated are mutually exclusive for the odd-degree
  cascade. This is why gadget-preservation must come from `P`, not refinement.

The optional gauge-generation/kernel-lemma extension (recover `g = cfiFlipAut F`) can be added on top of
Lemma B later if the literal gauge statement is wanted; it is **not** needed for the harvest or the order.

---

## 2. `PSeparatesGadgets` — the honest "base-resolved" hypothesis

Write `gadgetOf h x := h.H.gadget (h.e x) : Fin h.m` (the base vertex of `x`'s CFI vertex).

The usable observation: a residual automorphism `g` (`ResidualAut adj P S g`) **fixes `S` pointwise** and
**preserves `P`**, so for every committed `s ∈ S`,
```
P (g x) s = P (g x) (g s)   [g s = s, FixesPointwise]
          = P x s            [P-preservation: P (g x)(g s) = P x s]
```
i.e. `g` preserves each vertex's **P-relations to the committed set `S`**. So if those relations determine
the gadget, `g` preserves gadgets. Hence the definition:

```
def PSeparatesGadgets (adj) (P) (S) (h : IsCFI' adj) : Prop :=
  ∀ x y : Fin n, (∀ s ∈ S, P x s = P y s) → gadgetOf h x = gadgetOf h y
```
"The committed set `S`, through the partial order `P` it induces, distinguishes gadgets" = the base layer is
resolved by the committed individualization. Honest, statable, and exactly what makes Lemma A a ~5-line
reduction instead of the multi-hundred-line structural L1.

---

## 3. Lemma A — `gadgetPreserving_of_pSeparates` (IMPLEMENTING NOW)

```
theorem gadgetPreserving_of_pSeparates (h : IsCFI' adj) {S : Finset (Fin n)}
    {g : Equiv.Perm (Fin n)} (hg : ResidualAut adj P S g)
    (hsep : PSeparatesGadgets adj P S h) :
    ∀ x, gadgetOf h (g x) = gadgetOf h x
```
**Proof.** Fix `x`. Apply `hsep (g x) x`; its hypothesis `∀ s ∈ S, P (g x) s = P x s` is discharged by
`hg.2.1 x s` (P-preservation: `P (g x)(g s) = P x s`) rewritten with `hg.2.2 s hs` (`g s = s`). *Risk: low —
no CFI gadget internals, pure `ResidualAut` algebra.*

Deliverables this step: `gadgetOf` (def), `PSeparatesGadgets` (def), `gadgetPreserving_of_pSeparates`
(Lemma A). Bar: builds, axiom-clean `[propext, Classical.choice, Quot.sound]`.

**✅ LANDED 2026-06-04** (`Cascade.lean`, CFI-cov.4), axiom-clean, compiled first try — the proof was exactly
the traced `refine hsep (g x) x (fun s hs => ?_); … rwa [hg.2.2 s hs] at (hg.2.1 x s)`.

---

## 4. Lemma B — `cfiAut_gadgetFixing_mul_self` (NEXT, medium risk)

```
theorem cfiAut_gadgetFixing_mul_self (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x) :
    g * g = 1
```
Sub-steps, on the gadget vertex API (`SubsetVertex`/`EndpointVertex`, `seedVertex`/`endpointVertex`/
`subsetVertex`, the `adj_…_eq_one_iff` characterizations, `cfiAdj_aEmpty_endpoint_diff_gadget`):

- **B1 — type preservation.** `g` maps subset↔subset and endpoint↔endpoint. A subset vertex has all
  neighbours inside its gadget; an endpoint has exactly one bridge neighbour in another gadget. Since `g`
  fixes gadgets, it preserves "has a cross-gadget neighbour" = endpoint-ness.
- **B2 — endpoint involution.** `g` maps the parity pair `{e⁰_{v→w}, e¹_{v→w}}` to itself (gadget `v` fixed;
  bridge target gadget `w` fixed, so the direction `w` is preserved) — acting as identity or swap, an
  involution. Mirrors `cfiFlipAut_swaps_endpointVertex`.
- **B3 — subset involution.** `g`'s action on `a_T^v` is determined by its action on the endpoints (subset
  adjacency `adj_subsetVertex_eq_one_iff`), hence also an involution.
- **B4 — assemble** `g² = 1` via `Equiv.ext`, casing on subset/endpoint vertex (through `h.e`).

*Risk: medium — the `Sum`/`Sigma` vertex encoding and the "rw motive is not type correct" gotcha (prove the
underlying data equality as a standalone `have`, then `Sigma.ext`/`Subtype.ext`/`congrArg`; see the handoff
§2 patterns).*

---

## 5. CFI-cov.4 capstone — `ResidualInvolutive` and the harvest

```
theorem cfi_residualInvolutive (h : IsCFI' adj) {S}
    (hsep : PSeparatesGadgets adj P S h) : ResidualInvolutive adj P S
  := fun g hg => cfiAut_gadgetFixing_mul_self h hg.1 (gadgetPreserving_of_pSeparates h hg hsep)
```
Then feed `coversOrbits_of_residualInvolutive` / `closure_eq_stabilizerAt_of_residualInvolutive` with
`gens = {involutive residual auts}` (or reuse the CFI `cfi_*` wiring with the gauge extension) to obtain the
harvest completeness and the order `|Aut_S^P| = ∏ basic-orbit sizes` in the base-resolved (`PSeparatesGadgets`)
regime — with **no** structural L1 and **no** explicit cycle-space construction.

---

## 6. Build order, bars, and the remaining obligation

1. **Lemma A** (`gadgetOf`, `PSeparatesGadgets`, `gadgetPreserving_of_pSeparates`) — this step.
2. **Lemma B** (`cfiAut_gadgetFixing_mul_self`, B1–B4) — the medium-risk grind.
3. **Capstone** (`cfi_residualInvolutive` + harvest wiring).
4. *(Optional)* gauge-generation extension: recover `g = cfiFlipAut F` (symmetric/even `F`) on top of B for
   the literal gauge statement.

Each step: builds green, axiom-clean; then regen+fill `PublicTheoremIndex.md`, update
`chain-descent-schreier-sims.md` §7 + STATUS, and the `MEMORY.md` Part A pointer.

**The remaining obligation after this plan:** discharge `PSeparatesGadgets` for the descent's actual `P` —
i.e. that the committed individualization resolves the base layer. That is the orthogonal **visible/cascade
leg** (scheme/`PPolynomial` recovery on the base graph), not part of this gauge plan. The honest scope of
CFI-cov.4 is: *the gauge `Z₂^β` residual is harvested + order-counted in the base-resolved regime.*
