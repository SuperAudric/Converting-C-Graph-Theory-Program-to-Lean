# Build plan — discharging the CFI gauge nut (`ResidualInvolutive` via P-separation)

> **STATUS (2026-06-04): Lemmas A + B + capstone + harvest wiring all LANDED (axiom-clean).** The build plan
> for the one remaining CFI obligation left after the de-classed coverage landed.
>
> **UPDATE (2026-06-06) — `PSeparatesGadgets` is the WRONG (vacuous) hypothesis; re-wired onto the colour
> model.** Scoping finding: `PSeparatesGadgets` is stated over `P`-relations, but the descent's CFI recovery
> runs on **trivial `P`** + colour individualization, where it is **vacuously false at every `S`** (no
> `P`-relation distinguishes anything; also vacuous at `S=∅`). The descent's separation lives in the
> `warmRefine` **colouring**, not in `P`. Fix (landed, axiom-clean, `Cascade.lean` CFI-cov.4): the colour-model
> `CellSeparatesGadgets` + Lemma A `gadgetPreserving_of_cellSeparates` (via `warmRefine_invariant_of_isAut`),
> re-wiring `cfi_residualInvolutive` → **`cfi_residualInvolutive_cell`** (Lemma B `cfiAut_gadgetFixing_mul_self`
> reused verbatim), with `cellSeparatesGadgets_of_discrete` (cascade bridge) and
> `cfi_closure_eq_stabilizerAt_of_cellSeparates` / `cfi_card_stabilizerAt_of_cellSeparates`. These **supersede**
> the `pSeparates` versions for the descent's actual mechanism. **DESIGN SETTLED:** `CellSeparatesGadgets` is
> carried as a substrate-conditional **witness** (gadget-level analogue of `RecoverableByDepth`); the structural
> projection foundation (`gadget_mem_neighbors_of_adj_cross` + `endpoint_crossGadget_gadget`) is landed; the full
> "1-WL identifies `H` ⟹ separates gadgets" implication (a base-relative CFI cascade) is deferred to a future
> witness-discharge. Full record: [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) STATUS.
> **The §2 `PSeparatesGadgets` material below is retained for the structural argument (Lemma A's shape), but read
> `CellSeparatesGadgets` as its live replacement.**
>
> Authoritative companions:
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

## 4. Lemma B — `cfiAut_gadgetFixing_mul_self` (NEXT, medium risk) — detailed plan

```
theorem cfiAut_gadgetFixing_mul_self (h : IsCFI' adj) {g : Equiv.Perm (Fin n)}
    (hAut : IsAut g adj) (hfix : ∀ x, gadgetOf h (g x) = gadgetOf h x) :
    g * g = 1
```
Worked at the **Fin n** level, reusing the comprehensive `adj_subsetVertex_eq_one_iff` /
`adj_endpointVertex_eq_one_iff` (which already encode the gadget combinatorics). Vertices are
`h.subsetVertex hS` / `h.endpointVertex hw b`; adjacency facts (exact, confirmed in source):
- `adj_endpointVertex_eq_one_iff`: `adj (endpointVertex hwa bₐ)(endpointVertex hwb b_b) = 1 ↔
  v_a = w_b ∧ w_a = v_b ∧ bₐ = b_b` (bridge form);
- `adj_subsetVertex_eq_one_iff`: `adj u (subsetVertex hS'@v') = 1 ↔ ∃ w' (hw':w'∈N v') b,
  decide(w'∈S')≠b ∧ u = endpointVertex hw' b` (subset neighbours are endpoints at the **same** gadget `v'`);
- `cfiAdj_bridge` / `mem_neighbors_symm` / `not_self_mem_neighbors` (the bridge partner `e^b_{w→v}`, in
  gadget `w ≠ v`).

### Building blocks (Cascade.lean, CFI-cov.4)

- **`gadgetOf_subsetVertex`** `gadgetOf h (h.subsetVertex hS@v) = v`; **`gadgetOf_endpointVertex`**
  `gadgetOf h (h.endpointVertex hw b@v) = v`. (`unfold gadgetOf …Vertex; simp [gadget, e_…Vertex]`.)
- **`exists_vertex_form`** (destructor) `∀ x, (∃ v S (hS:S∈even v), x = h.subsetVertex hS) ∨
  (∃ v w (hw:w∈N v) b, x = h.endpointVertex hw b)`. Via `cases h.e x`, `obtain` the Σ, then
  `x = e.symm (e x)` round-trip into the constructor (`subsetVertex`/`endpointVertex` are `e.symm ∘ subset`/
  `endpoint`, both defeq to the `Sum.inl/inr` form).
- **`isEndpt h x := ∃ y, adj.adj x y = 1 ∧ gadgetOf h y ≠ gadgetOf h x`** (has a cross-gadget neighbour).
  - `isEndpt_endpointVertex` : `isEndpt h (endpointVertex hw b)` — witness the bridge partner
    `endpointVertex (mem_neighbors_symm.mp hw) b`; its gadget is `w ≠ v` (`not_self_mem_neighbors`).
  - `not_isEndpt_subsetVertex` : `¬ isEndpt h (subsetVertex hS@v)` — every neighbour is `endpointVertex … @v`
    (`adj_subsetVertex_eq_one_iff` + `gadgetOf_endpointVertex`), so gadget = `v`, no cross neighbour.
  - `isEndpt_equivariant` : `isEndpt h (g x) ↔ isEndpt h x` for `g` aut + gadget-fixing — substitute
    `y = g z` (g bijective), `adj (g x)(g z) = adj x z` (`hAut`), gadgets via `hfix`.

### The three steps

- **B1 (type preservation).** `gadgetFixingAut_endpoint`: `g (endpointVertex hw b)` is an endpoint at gadget
  `v` — by destructor it is subset or endpoint; `isEndpt_equivariant` + `isEndpt_endpointVertex` make it
  `isEndpt`, and `not_isEndpt_subsetVertex` rules out subset; gadget `= v` by `hfix` + `gadgetOf_…`.
  Symmetric `gadgetFixingAut_subset`: `g (subsetVertex hS@v)` is a subset at gadget `v` (¬isEndpt side).
- **B2 (g² fixes endpoints).** `mulSelf_endpoint`: from B1, `g (endpointVertex hw b) = endpointVertex hw'
  b'` at gadget `v`. **Direction**: the bridge partner `y = endpointVertex (v∈N w) b @ w`; `g y` is an
  endpoint at gadget `w` (B1); `adj (g x)(g y) = adj x y = 1` (bridge) + `adj_endpointVertex_eq_one_iff` ⟹
  `w' = w`. So `g` maps `{endpointVertex hw false, endpointVertex hw true}` into itself; `g` injective +
  `endpointVertex … false ≠ … true` ⟹ a bijection of the 2-set ⟹ `g (g (endpointVertex hw b)) =
  endpointVertex hw b`. (Case on the two images.)
- **B3 (g² fixes subsets).** `mulSelf_subset`: `g²(subsetVertex hS@v)` is a subset at gadget `v` (B1 twice).
  `g²` preserves adjacency (`hAut.trans hAut`) and fixes every endpoint (B2), so `g²(x)` has the **same
  endpoint-adjacencies** as `x`: `adj (g² x) e = adj (g² x)(g² e) = adj x e`. A subset is determined by them
  (`adj_subsetVertex_eq_one_iff` with `b = false`: `endpointVertex hw false ~ subsetVertex hS ↔ w ∈ S`), so
  `S'' = S` on `N(v)`, hence `g²(subsetVertex hS) = subsetVertex hS`.
- **B4 (assemble).** `g * g = 1` via `Equiv.ext`: `(g*g) x = g (g x)` (`Equiv.Perm.mul_apply`); destructor on
  `x`; B2 / B3 give `g (g x) = x`.

*Risk: medium — the destructor round-trips and the `Sum`/`Sigma`/`Subtype` proof-irrelevance plumbing
(handoff §2 patterns: prove the data equality as a standalone `have`, avoid `rw` under dependent binders).
Build the building blocks first, check each, then assemble.*

**✅ LANDED 2026-06-04** (`Cascade.lean`, CFI-cov.4), axiom-clean, built in three chunks (data helpers →
type-preservation/direction → involution steps), each compiling cleanly. All declarations:
`gadgetOf_subsetVertex`/`_endpointVertex`, `exists_vertex_form`, `endpointVertex_bool_inj`/`_inj`,
`subset_mem_iff_adj`, `isEndpt` + `isEndpt_endpointVertex`/`not_isEndpt_subsetVertex`/`isEndpt_equivariant`,
`gadgetFixingAut_endpoint`/`_subset`/`_dir`, `mulSelf_endpoint`/`_subset`, `cfiAut_gadgetFixing_mul_self`.
The endpoint involution used the `bool_pigeon : x≠a → y≠x → y=a` (`by decide`) + `g.injective` argument as
planned; no surprises. The conjugation-to-CFIVertex alternative was not needed — the Fin n route reusing
`adj_subsetVertex_eq_one_iff` / `adj_endpointVertex_eq_one_iff` worked directly.

---

## 5. CFI-cov.4 capstone — `ResidualInvolutive` and the harvest

```
theorem cfi_residualInvolutive (h : IsCFI' adj) {S}
    (hsep : PSeparatesGadgets adj P S h) : ResidualInvolutive adj P S
  := fun g hg => cfiAut_gadgetFixing_mul_self h hg.1 (gadgetPreserving_of_pSeparates h hg hsep)
```
**✅ `cfi_residualInvolutive` LANDED 2026-06-04** (axiom-clean): `PSeparatesGadgets adj P S h →
ResidualInvolutive adj P S`, the direct Lemma A + Lemma B capstone, valid at any `S`.

Then feed `coversOrbits_of_residualInvolutive` / `closure_eq_stabilizerAt_of_residualInvolutive` with
`gens = {involutive residual auts}` to obtain the harvest completeness and the order `|Aut_S^P| = ∏
basic-orbit sizes` in the base-resolved (`PSeparatesGadgets`) regime — with **no** structural L1 and **no**
explicit cycle-space construction.

> **Note on the regime (do not wire the harvest at `S = ∅`).** `PSeparatesGadgets adj P ∅` is *vacuously too
> strong* — its premise `∀ s ∈ ∅, …` is trivial, so it would require *all* gadgets equal (false for `m ≥ 2`).
> The `PSeparatesGadgets` regime is meaningful only at a **nonempty** `S` (where `P`-relations to `S`
> distinguish gadgets). So the harvest capstone (closure = StabilizerAt, order) is stated at a nonempty
> base-resolved `S`, using a **base sequence from `S`** (`(allSeeds \ S).toList`, terminating at the cascade's
> `IsBase allSeeds` lifted by `isBase_mono`).

**✅ HARVEST WIRING LANDED 2026-06-04** (axiom-clean): `isBase_mono` (`IsBase` upward-closed),
`cfi_exists_base_seq_from` (base sequence from any `S`), **`cfi_closure_eq_stabilizerAt_of_pSeparates`**
(`closure {g | ResidualAut adj P S g ∧ g²=1} = StabilizerAt adj P S`) and
**`cfi_card_stabilizerAt_of_pSeparates`** (`|Aut_S^P| = ∏ basic-orbit sizes`) — both from `cfi_residualInvolutive`
+ the de-classed coverage over `cfi_exists_base_seq_from`. CFI-cov.4 is complete modulo `PSeparatesGadgets`.

---

## 6. Build order, bars, and the remaining obligation

1. **Lemma A** (`gadgetOf`, `PSeparatesGadgets`, `gadgetPreserving_of_pSeparates`) — ✅ LANDED.
2. **Lemma B** (`cfiAut_gadgetFixing_mul_self`, B1–B4) — ✅ LANDED (the medium-risk grind, no surprises).
3. **Capstone** `cfi_residualInvolutive` — ✅ LANDED. **Harvest wiring** (`isBase_mono`,
   `cfi_exists_base_seq_from`, `cfi_closure_eq_stabilizerAt_of_pSeparates`, `cfi_card_stabilizerAt_of_pSeparates`)
   — ✅ LANDED.
4. *(Optional)* gauge-generation extension: recover `g = cfiFlipAut F` (symmetric/even `F`) on top of B for
   the literal gauge statement.

**CFI-cov.4 is complete.** The sole remaining obligation for the CFI cross-branch harvest is discharging
**`PSeparatesGadgets`** for the descent's actual `P` (§6 below) — the orthogonal visible/cascade leg, a
separate thread.

Each step: builds green, axiom-clean; then regen+fill `PublicTheoremIndex.md`, update
`chain-descent-schreier-sims.md` §7 + STATUS, and the `MEMORY.md` Part A pointer.

**The remaining obligation after this plan:** discharge `PSeparatesGadgets` for the descent's actual `P` —
i.e. that the committed individualization resolves the base layer. That is the orthogonal **visible/cascade
leg** (scheme/`PPolynomial` recovery on the base graph), not part of this gauge plan. The honest scope of
CFI-cov.4 is: *the gauge `Z₂^β` residual is harvested + order-counted in the base-resolved regime.*
