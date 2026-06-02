# Handoff — abelian-sufficiency / linear-oracle completeness on CFI

**Status (2026-06-01): PAUSED at a foundational finding — read §0 first.** This doc lets a cold
reader pick up the in-flight proof that the **linear oracle is complete on CFI** (it fires whenever
it should). The Stage-3 gadget twist + most of cascade-1b are **built and axiom-clean**, but the
final step (`C1b.3`) hit a **known-false-in-general property at its core** (σ-cell-coherence). The
problem is paused there pending a decision on how to proceed. **§0 is the authoritative current-state
handoff**; §1–§7 are the historical detail it points into.

> **De-classing update (2026-06-02) — Stage 1 landed (the class-agnostic swap certificate).** The
> linear oracle was designed early (pre-recovery-framework), which is why the abstract D2 predicate
> `ResidualAbelian` was *orphaned* (zero uses in `LinearOracle.lean`) and completeness routed per-class
> through CFI gadget involutions. First de-classing step now in `Cascade.lean` (axiom-clean): the
> precise D2 predicate **`ResidualInvolutive`** (exponent-2 residual — the honest `Z₂^β` form;
> `ResidualAbelian` alone does not give involutions), `residualAbelian_of_involutive` (exponent-2 ⟹
> abelian, wiring the orphaned predicate in), **`orbitPartition_swap_of_involutive`** (an involutive
> orbit witness is a *swap* `g a = b ∧ g b = a` — closing the map-vs-swap gap class-agnostically), and
> **`swap_of_cellsAreOrbits_involutive`** (at a recoverable node, every same-cell pair has a swapping
> orbit automorphism — the "swap exists" certificate, from recovery + D2, replacing the per-class
> `CFIGadgetFlippable`/`cfiGadgetFlippableLocal_of_parity` derivation). **Scope:** this delivers the
> class-agnostic *symmetry* (the swap); the remaining order-model `ConfigSwap` coherence (`fixesχι` +
> off-pair σ-preservation) is the §0.4 model gap — *unchanged*, separately scoped. The σ-coherence
> blocker (C1b.3) is **bypassed for the swap half**, not resolved for the coherence half.

Authoritative companions: [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
§8.2 (the retargeting), [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
§2/§4.3 (the shared completeness gap). Lean lives in
[`GraphCanonizationProofs/ChainDescent/LinearOracle.lean`](../GraphCanonizationProofs/ChainDescent/LinearOracle.lean)
(`§L.1–L.7b`) on top of [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean).

> **Forward-compat (2026-05-31) — this proof is leg B of the oracle-capability
> seal** ([exhaustive-obstruction §0.5/§0.6](./chain-descent-exhaustive-obstruction.md)).
> "Abelian ⟹ the oracle fires" *is* the seal's leg B (bucket ¬D1 ∧ D2). Two things
> to preserve so the seal can consume this leg later: **(i)** keep the completeness
> statement class-agnostic — "abelian / unique-candidate ⟹ certified", not
> CFI-only — so it plugs in without re-derivation; **(ii)** when the converse fails
> (the conjugation gap / no unique candidate), **record *which property* fails** —
> that ¬D2 property is a positive input to the Cameron leg (leg C), not a dead end.
> The named nut already isolates this correctly (`hwit` + cascade-1b are shared and
> non-GI∈P); the seal just asks that the *failure boundary* be exported as data.

---

## 0. START HERE — current state, the reduction chain, and the open finding (2026-06-01)

### 0.1 The goal & the reduction chain

**Goal:** prove the linear oracle (and, via the same object, Tier-3a B1's `hwit`) **fires on every
CFI decision** ⟹ the descent collapses CFI to a single path ⟹ polynomial CFI. The C# already shows
this empirically through CFI(K7); this is the Lean proof.

**Approach C (chosen long ago, still right):** model the pruning certificate as a **`ConfigSwap`** —
a *vertex-space* automorphism `g` of `adj` that fixes the leaf colouring `χι` and carries the order
assignment `σ` onto its flip `flipPair σ a b`. This sidesteps the rank-alignment / conjugation nut
(§2). The whole completeness proof is a chain of reductions, **all axiom-clean
`[propext, Classical.choice, Quot.sound]`, all built except the last link**:

```
  CFI gadget twist  ──soundness──▶  ConfigSwap  ──▶  ConfigSwapRecoverable  ──capstones──▶  oracle fires
  (cfiFlipAut F)                    (configSwap_of_cfiFlipAut)                              (canonAdj_eq_…, realizableFlip_…)

  Discharging ConfigSwapRecoverable for CFI, reduced step by step:
    ConfigSwapRecoverable
      ◀── configSwapRecoverable_of_cfi        (CFIGadgetFlippable)
      ◀── …_of_cfi_local                      (CFIGadgetFlippableLocal — conditions decoupled to locality+coherence)
      ◀── cfiGadgetFlippableLocal_of_parity   (CFIParityDecisionFlippable — decisions are parity-pairs; swap pre-discharged)
      ◀── [C1b.3]  ← THE OPEN / BLOCKED STEP
```

Tier-3a B1 consumes the *same* gadget twist: `Cascade.cfiLayer_pathFixing_hwit` /
`cascadeComposition_cfi` ◀── `CFILayerGadgetFlippable` (the `hwit` analog of `CFIGadgetFlippableLocal`).

### 0.2 What is BUILT (axiom-clean; full serial build green, `scripts/build.sh`)

- **The Stage-3 gadget twist** = the **`Z₂^β` cycle-space generators**, NOT the full
  `Aut(CFI)≅Z₂^β⋊Aut(H)` iso (the surjectivity half no consumer needs). `CFI.lean §15`:
  - **Phases 0–5** — `cfiFlip F`/`cfiFlipEquiv` (even subgraph `F` ⟹ involution), `cfiFlip_isAut`
    (preserves `cfiAdj`), `IsCFI'.cfiFlipAut` + `isAut_cfiFlipAut` (an honest `Aut(adj)` involution on
    `Fin n`), `disjoint_support_cfiFlipAut` (support localised to `F`-touched gadgets),
    `cfiFlipAut_preserves_P` + `cfiFlipAut_pathFixing_witness` (the Tier-3a `hwit` existential).
  - **C1b.0** — `cfiFlip_endpoint`/`cfiFlipAut_swaps_endpointVertex`: the flip swaps the parity-pair
    `e^0_{v→w}/e^1_{v→w}` **iff `{v,w}∈F`** (and subset-pairs via `cfiFlip_subset`). The decision-pair
    swap is settled in advance.
  - **C1b.2a** — `exists_even_triangle`: the common-neighbour triangle, a concrete even `F` through
    `{v,w}` avoiding everything else (covers triangle-containing bases, e.g. K₄).
  - **C1b.2b** — `exists_even_cycle`: the **general** even subgraph via a **permutation-cycle** `σ`
    (vertex `p`'s F-neighbours `={σ p, σ⁻¹ p}`, so even-degree is immediate — no list arithmetic).
    Covers triangle-free bases. The cycle's *existence* in `H−Σ` (a `σ` fixing the forbidden set `Σ`)
    is the isolated graph-theoretic hypothesis where **treewidth/connectivity** enters.
- **Linear-oracle wiring** (`LinearOracle.lean §L.8–L.9`): `configSwap_of_aut` (general config-swap
  constructor), `configSwap_of_cfiFlipAut`, `CFIGadgetFlippable`, `configSwapRecoverable_of_cfi`; the
  **locality reduction** `swapsConfig_off_pair_of_local` (reduces the σ-off-pair condition to
  σ-cell-coherence + locality), `preserves_D_of_involutive_local`, `cfiFlipAut_fixesχι_of_support`,
  `configSwap_of_cfiFlipAut_local`, `CFIGadgetFlippableLocal`, `configSwapRecoverable_of_cfi_local`;
  **C1b.1** `CFIParityDecisionFlippable` + `cfiGadgetFlippableLocal_of_parity`.
- **Tier-3a wiring** (`Cascade.lean` Phase 6b): `CFILayerGadgetFlippable`, `cfiLayer_pathFixing_hwit`,
  `cascadeComposition_cfi`.

### 0.3 The open step (C1b.3) and the FINDING — read this carefully

`C1b.3` must discharge the remaining conjuncts of `CFIParityDecisionFlippable`, per decision `(a,b)`:
1. **decisions are parity-pairs** (`a=e^{b₀}_{v→w}`, `b=e^{¬b₀}`);
2. **σ-cell-coherence** `∀ u∉{a,b}, σ.σ a u = σ.σ b u`;
3. **χι-coherence** on the F-support;
4. the **Σ↔decided-gadgets** translation (mechanical).

> **MAJOR FINDING (the blocker).** The load-bearing piece **(2) σ-cell-coherence is the
> "cell-uniform signature" property the project has already machine-checked to be FALSE in general**
> — `cell_split_uniform_false` ([`ChainDescent.lean:464–491`](../GraphCanonizationProofs/ChainDescent.lean)).
> Cell-mates can relate symmetrically to a *cell* but **asymmetrically to an individual vertex in it**.
> The doc there states explicitly: *"a correct version needs `a,b` to be **singleton cells** … not the
> unindividualised partner in a k≥2 target cell — **which is exactly the regime the linear oracle must
> handle**."* The linear oracle's decision pair `{a,b}` **shares a χι-cell** (non-singleton — that's
> what 1-WL can't split), so the σ-coherence C1b.3 needs is squarely in the **known-false-in-general**
> regime. **`swapsConfig_off_pair_of_local` proves the gadget-flip `ConfigSwap` genuinely requires this
> coherence** (the `v=a, u∈D\{a,b}` case), so it is not optional in the current model.

Consequence: the σ-coherence conjunct in `CFIGadgetFlippable`/`CFIParityDecisionFlippable` **may be
unsatisfiable as stated** for real CFI decisions ⟹ those predicates could be vacuous and
`configSwapRecoverable_of_cfi` an undischargeable (though correct, axiom-clean) implication. Whether
CFI's gadget structure *rescues* coherence (the counterexample is a generic graph, not CFI) is unproven
and is the genuine hard content. Sub-piece (1) additionally needs the CFI WL-cascade analysis
(`cfi_cascades_polynomially_oddDeg` is proved axiom-free for odd degree but exposes **no intermediate
cell structure** — only final discretization).

### 0.4 A model subtlety the picker-upper MUST know

There are **two individualization mechanisms** in the descent, and conflating them causes confusion:
- **Colour-individualization** (`DescentTrace`/`IndivStep`, `ChainDescent.lean`): the selected cell is
  singletonized in `χ'`. `DescentTrace.singletons` ⟹ vertices in `D` are **χι-singletons** (distinct
  colours). `samePartition_pair`/`warmRefine_agree_off'` give that **all `DirAssignment`s over `(P₀,D)`
  yield the same partition when `D` is χι-singletonized** — i.e. branch order doesn't affect partition.
- **Order-individualization** (the **linear oracle** model, the `ConfigSwap` setting): the decision pair
  `{a,b}` **shares a χι-cell** (`χι a = χι b`) and is separated by the **order `σ`**, *not* by colour.
  So `ConfigSwap.fixesχι` (`χι(g a)=χι a` with `g a=b`, i.e. `χι a=χι b`) is consistent **only** in this
  model. Here `D` is **not** χι-singletonized, so `samePartition_pair` does **not** directly apply.

This gap is why the partition-level invariance (`samePartition_pair`, free) does **not** trivially
discharge the canonical-leaf equality, and why σ-coherence resurfaces.

### 0.5 Options forward (none is a quick win — a decision is needed before more building)

1. **Re-examine the soundness model (recommended first).** `samePartition_pair` gives *same partition*
   for free (in the colour-individualization model). The only genuinely open thing is the *canonical
   relabelling* (rank alignment). Investigate whether the gadget-flip `ConfigSwap` **over-specifies** —
   whether a partition-level or singleton-restricted route discharges CFI completeness **without** the
   false σ-coherence conjunct. This either unblocks C1b.3 or definitively characterizes the nut.
2. **Singleton-restricted re-modelling.** Re-cast the decision so one of `a,b` is the individualized
   rep (singleton), where coherence *does* hold (per the doc's note) — changes the `ConfigSwap` setup.
3. **Isolate σ-coherence + decision-char as named hypotheses** and land only the mechanical
   Σ-translation — honest but names a nut that's known-false-in-general (low value without option 1).
4. **Pause cascade-1b**, consolidate (the gadget-flip construction is complete and solid).
5. **The harvest-window route (proposed 2026-06-01, recommended exploration).** A class-agnostic
   support-counting argument that harvests via **footprint-matching** (the cascade/linear core), so it
   **never invokes σ-coherence** — substantiating option 1's "the `ConfigSwap` over-specifies." The
   firing condition becomes "footprint singletonizes within the residual base" (= the hidden-Johnson
   screen), and the `tw(H)` / σ-coherence derivations become corollaries. If valid this supersedes
   `C1b.3` outright. Concept + designed first test: [`chain-descent-harvest-window.md`](./chain-descent-harvest-window.md).

### 0.6 Key pointers

- **Lean (built):** `CFI.lean §15` (the whole gadget-flip program, C1b.0/2a/2b);
  `LinearOracle.lean §L.8–L.9`; `Cascade.lean` Phase 6b. Index: `PublicTheoremIndex.md` (search §15,
  §L.8, §L.9, Cascade Phase 6b, C1b).
- **Lean (the finding):** `cell_split_uniform_false` + the "needs singleton cells" note at
  `ChainDescent.lean:464–491`; `samePartition_pair` (`ChainDescent.lean ~2776`), `warmRefine_agree_off'`
  (`~882`), `DescentTrace.singletons`, `spine_branch_independent` (`~2400`), `warm_6_2` (`~704`).
- **Memory:** `project_cfi_gadget_flip_2026-06-01.md` (full Phase 0–6 + C1b detail + the finding).
- **Cascade-1b framing:** [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) §2
  (1a proved / 1b open). Cascade-1b is **CFI-specific** (schemes are done: `recoverableByDepth_scheme`
  gives the witness at the depth-1 decision node; CFI's recovery is only at the trivial discretizing
  depth).

---

## 1. The problem, in one paragraph

The linear oracle exposes a **hidden abelian symmetry** at an *apparent decision*: a
size-2 target cell `{a,b}` 1-WL can't separate, whose two branches are `σ` (= "`a<b`")
and `flipPair σ a b` (= "`b<a`"). When the twist verifies, the two branches are
equivalent — `{a,b}` was a true symmetry 1-WL couldn't see, not a genuine decision.
At a leaf both branches refine to **discrete** colourings; relabelling `adj` by colour-rank
gives each branch's canonical leaf matrix `canonAdj σ` / `canonAdj flip`. **Soundness** of
the oracle is fully proved (`§L.1–L.2`). The open question is **completeness on CFI**: does
the oracle *fire* (prune the redundant branch) on every CFI decision? Firing requires a
*verified twist*. This doc is the discharge of that for the CFI class.

Why it matters: firing on every CFI decision ⟹ the descent collapses CFI to a single path
⟹ polynomial CFI (the C# already shows this empirically; this is the Lean proof).

---

## 2. The key conceptual finding (read this before touching the code)

There are **two inequivalent twists**, and the choice decides everything:

- **Rank-space** `candidateTwist = π_flip · π_σ⁻¹` (where `π_σ`, `π_flip` are the leaves'
  rank permutations). This is what `§L.2` models. It *always* realizes the flip
  (`candidateTwist_realizesFlip`), but `IsAut candidateTwist adj` is the **rank-alignment
  nut** — see below.
- **Vertex-space** `g = π_flip⁻¹ · π_σ` (the path-fixing automorphism; for CFI it is the
  gadget parity-flip twist). This is what the **C# actually verifies** (confirmed in
  [`TwistConstruction.cs`](../GraphCanonizationProject/TwistConstruction.cs): it builds a
  vertex permutation by colour-matching and checks `IsAutomorphism` on `adj`). `IsAut g adj`
  is **trivially true when the decision is a real symmetry** — `g` *is* the gadget automorphism.

They are conjugate: `candidateTwist = π_σ · g⁻¹ · π_σ⁻¹` (proved: `candidateTwist_eq_conjugate`).
So `IsAut candidateTwist adj` asks whether the **`π_σ`-conjugate** of a genuine automorphism is
again an automorphism — the conjugation gap. It always lands in `Aut(canonAdj σ) = π_σ·Aut(adj)·π_σ⁻¹`
but escaping to `Aut(adj)` is not automatic; abstractly it is **provably not closable** (it has
counter-models) and is the formal shadow of Babai's split-or-Johnson wall.

**Conclusion that drives the plan:** model completeness via the **vertex** twist `g`
(= the cascade oracle's `OrbitPartition` automorphism), not the rank-space candidate. This
*sidesteps the rank-alignment nut* and reduces CFI firing to **orbit recovery** — which is
already proved for odd-degree CFI.

---

## 3. The plan (Approach C) and the alternates

**Chosen: Approach C — completeness via the vertex path-fixing automorphism.**
A pruning certificate is a `ConfigSwap`: an automorphism `g` of `adj` that fixes the initial
colouring `χι` and carries `σ.σ` onto `(flipPair σ).σ`. Then:
- **Soundness:** `ConfigSwap ⟹ canonAdj σ = canonAdj flip` (the branches give the identical
  canonical leaf), so pruning the flip branch loses nothing. **(BUILT — see §4.)**
- **Completeness on CFI:** "a `ConfigSwap` exists" = a swapping automorphism (`g a = b`,
  `g b = a`) = `OrbitPartition adj P S a b` at the decision node = **cells-are-orbits at the
  node** = the cascade oracle's localization obligation. The **reduction is landed** (`§L.8`):
  the closed `Z₂`-twin-swap instance (`configSwap_of_swap`) + the capstones reducing oracle
  effectiveness to `ConfigSwapRecoverable`. Its bounded-depth half (`recoverableByDepth_cfi`)
  is **proved**; the residual is (a) the **general gadget twist** (non-transposition `g`,
  needs Stage-3 `Aut(CFI)` = `hwit`) and (b) the **decision-node-depth** bridging
  (**cascade-1b**) — open-but-not-GI∈P and **shared with the cascade oracle**. **(BUILT the
  reduction — see §4/§5.)**

Alternates considered and rejected:
- **A — push the rank-space rank-alignment** (`IsAut (π_σ·g⁻¹·π_σ⁻¹) adj` for CFI). The
  irreducible conjugation nut; also needs a Stage-3 explicit-twist slice. High risk.
- **B — extract a swap from orbit recovery + the abelian Z₂ structure.** Gets `g a = b`;
  still rank-space for firing; subsumed by C.
- **D — `decide` on a concrete tiny CFI.** Off-style (the project is abstract-structural;
  `warmRefine`-to-discreteness isn't `decide`-friendly).

---

## 4. What is BUILT (all axiom-clean: `[propext, Classical.choice, Quot.sound]`; full build 1132 jobs)

Milestones, in dependency order:

- **M0 — `refineStep` concretized** (`ChainDescent.lean`, ~the old `axiom refineStep` site).
  Was an axiom specifying only the *partition* (`refineStep_iff`); the colour *order* was
  unspecified, which made `candidateTwist`'s value — hence abelian-sufficiency — *independent
  of the axioms* (counter-models). Now a concrete `def`:
  `refineStep adj P χ v := Encodable.encode (sigKey adj P χ v)`, with
  `sigKey = χ v :: Multiset.sort ((signature adj P χ v).map encTuple) (·≤·)` (the C#'s
  `WarmPartition.RefineRound`: own colour, then sorted encoded signature; `POE.toNat`:
  less<unknown<greater). `refineStep_iff` is now a **theorem**. Helpers: `POE.toNat`(`_injective`),
  `encTuple`(`_injective`), `sigKey`, `sigKey_eq_iff`. **Payoff: `refineStep`/`refineStep_iff`
  left the axiom basis project-wide** (`warm_6_2` is now `[propext, Classical.choice, Quot.sound]`).
  Design note: *encode-as-colour*, not rank-by-List-lex — `<` on `List ℕ` has an instance
  diamond (core `List.lt` vs Mathlib's lex). Partition is byte-identical to the C#; the cell-id
  *order* is a fixed canonical encoding (no theorem depends on it).
  New imports: `Mathlib.Data.Multiset.Sort`, `Mathlib.Data.Nat.Pairing`, `Mathlib.Logic.Equiv.List`.

- **M1a — cross-config transport** (`ChainDescent.lean` `§16.2b`, right after
  `warmRefine_invariant_of_isAut`). `signature_transport`, `sigKey_transport`,
  `refineStep_transport`, `iterate_refineStep_transport`, **`warmRefine_transport`**: if `g ∈
  Aut(adj)` carries `(P₁,χ₁)` to `(P₂,χ₂)` (`P₂ (g·)(g·) = P₁`, `χ₂∘g = χ₁`) then
  `warmRefine adj P₂ χ₂ (g v) = warmRefine adj P₁ χ₁ v`. The value-level generalisation of the
  `*_invariant_of_isAut` chain — newly provable *because* `refineStep` is concrete (unfold to
  `encode (sigKey …)`, reindex the signature multiset by `g`).

- **M1b — the reduction** (`LinearOracle.lean` `§L.7`). `ConfigSwap` (structure: `g`, `isAut`,
  `fixesχι`, `swapsConfig`), `vertexRank_comp` (`vertexRank (χ∘g) v = vertexRank χ (g v)`),
  `configSwap_rankPerm` (`π_σ = π_flip·g`) / `_flip` (`π_flip = π_σ·g⁻¹`),
  **`candidateTwist_eq_conjugate`** (`candidateTwist = π_σ·g⁻¹·π_σ⁻¹`),
  `isAut_candidateTwist_iff_conjugate` (the rank-space firing obligation = the conjugation nut).

- **M1c Approach C, steps 1–2 — vertex-model soundness** (`LinearOracle.lean` `§L.7b`).
  **`canonAdj_eq_of_configSwap`** (a `ConfigSwap` ⟹ `canonAdj σ = canonAdj flip`) and
  **`realizableFlip_of_configSwap`** (⟹ `RealizableFlip`, identity witness). The faithful
  C# soundness: pruning rests on a *real* automorphism, no rank-alignment.

- **M1c Approach C, step 3 — the cascade-1b bridge** (`LinearOracle.lean` `§L.8`).
  **`configSwap_of_aut`** (the *general* constructor, added 2026-05-31): **any** swapping
  automorphism `g` (`g a = b`, `g b = a`) that fixes `χι` and preserves `σ.σ` *off the flip
  pair* (`σ.σ (g v)(g u) = σ.σ v u` for `(v,u) ∉ {(a,b),(b,a)}`) *is* a `ConfigSwap` — `g` need
  **not** be a transposition; it may move the whole coupled component (the CFI gadget twist).
  The flip-pair cells are exactly where `flipPair` negates and `g` co-swaps, compensating via
  antisymmetry. This **removes the config-swap packaging from the open content**: once the
  gadget twist `g` + its off-pair `σ`-action are in hand, the `ConfigSwap` is built with no
  rank-alignment — `hwit` plugs straight in. **`configSwap_of_swap`** is now a thin
  transposition specialisation (σ-cell-coherence = off-pair preservation for a transposition);
  the `Z₂` twin-swap, simplest genuine abelian decision (real proof content: swap case-analysis
  + antisymmetry). **`ConfigSwapRecoverable`** (every leaf decision admits a config-swap = the
  linear oracle's decision-node recoverability) + capstones
  **`canonAdj_eq_of_configSwapRecoverable`** / **`realizableFlip_of_configSwapRecoverable`**
  reduce oracle effectiveness to that one hypothesis. The reduction is *landed*: a swapping
  automorphism (`g a = b`, `g b = a`) is an `OrbitPartition` witness specialised to the size-2
  cell, so this unifies linear-oracle completeness with the cascade oracle's localization.

- **Stage-3 gadget flip (the `hwit` construction) — BUILT 2026-06-01** (`CFI.lean §15` +
  `LinearOracle.lean §L.9` + `Cascade.lean`, axiom-clean, full build green). Scoped to the
  **`Z₂^β` generators, not the full `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` iso** (the surjectivity half no
  consumer needs). The generator is the **cycle-space flip** `cfiFlip F` for an even-subgraph `F`
  (toggle endpoint parities along `F`, complement subsets by `F`-incident neighbours; even degree
  keeps the even-subset invariant). Phases: **0** triangle prototype (`decide`-validated
  automorphism), **1** `cfiFlip`/`cfiFlipEquiv` + involution, **2** `cfiFlip_isAut` (preserves
  `cfiAdj`; the 4-case crux — endpoint parity + subset-`w` membership flip together, bridge edge
  one `F`-bit), **3** lift to `Fin n` `IsCFI'.cfiFlipAut` + `isAut_cfiFlipAut` (an honest
  `Aut(adj)` involution), **4** support/locality (`disjoint_support_cfiFlipAut` — fixes `F`-free
  gadgets), **5** `P`-preservation + `cfiFlipAut_pathFixing_witness` (the Tier-3a `hwit` shape),
  **6a** `configSwap_of_cfiFlipAut` (the flip IS a config-swap — linear oracle) + the locality
  reduction (`swapsConfig_off_pair_of_local` etc.), **6b** `cfiLayer_pathFixing_hwit` /
  `cascadeComposition_cfi` (Theorem 3a for CFI layers). Both oracles now fire through one
  construction, reduced to the shared cascade-1b `…GadgetFlippable…` existence hypothesis.

Earlier scaffolding still standing (`LinearOracle.lean` `§L.1–L.6`): `RealizesFlip`,
`TwistWitness`, `twistOracle`/`canonicalTwistOracle` + `LeafTwistSpec` discharge (soundness),
`candidateTwist`(`_realizesFlip`/`_unique`), `isAut_candidateTwist_iff_aligned`,
`canonicalTwistOracle_isSome_iff`, the §L.6 relativized-completeness scaffold
(`AbelianSufficiency`, `AbelianSufficiencyHolds`, `oracleFires_of_abelianSufficiency`).

---

## 5. Step 3 — BUILT (the reduction) + what remains (the named nut)

Step 3 wired "a `ConfigSwap` exists for a CFI decision" to the swapping-automorphism /
orbit-recovery picture. **The reduction landed** (`§L.8`, axiom-clean):

- **The swap-vs-map mismatch is resolved** the way §5 anticipated: `configSwap_of_swap`
  builds the full `swapsConfig` config relation from a *swapping* automorphism (`g a = b`,
  `g b = a`) plus σ-cell-coherence (`σ.σ a w = σ.σ b w` off the pair), proven by a direct
  case-analysis using `flipPair`'s definition + `σ.antisym` (no need to weaken `ConfigSwap`).
  The closed instance is the **transposition** (`g` fixes everything off `{a,b}`) — the `Z₂`
  twin-swap, simplest genuine abelian decision.
- **The existence target is named** as `ConfigSwapRecoverable` (every leaf decision admits a
  config-swap) and the **capstones** (`canonAdj_eq_of_configSwapRecoverable`,
  `realizableFlip_of_configSwapRecoverable`) reduce oracle effectiveness to it. This is the
  linear-oracle analog of `AbelianSufficiencyHolds`, and — since a swapping automorphism *is*
  an `OrbitPartition adj P S a b` witness specialised to the size-2 cell — it **unifies
  linear-oracle completeness with the cascade oracle's localization** (the doc's goal).
- **Twin bridge landed (2026-05-31).** `configSwap_of_twin` (`§L.8`) closes the genuine-twin
  `Z₂` decision class via the *same* twin hypothesis and the *same* transposition witness as the
  cascade oracle: an **(adj, σ)-twin** decision pair (adjacency-twin on a simple graph +
  σ-cell-coherent, `χι a = χι b`) ⟹ `ConfigSwap`, by feeding `configSwap_of_swap` the shared lemma
  `CascadeOracle.isAut_swap_of_twin`. LinearOracle now `import`s `ChainDescent.CascadeOracle`.
  Linear-oracle analogue of `cellsAreOrbits_of_twin_cells` — **both oracles fire on the same twin
  class through one shared lemma**, at decision-node depth, no `|Sᶜ|` bound, no rank-alignment.
  - **IMPORTANT scope correction (2026-05-31): this twin class is NOT CFI.** `CFI(H)` has no twins
    (`CFI.cfi_triangle_no_twins`, `native_decide`; general: unique bridge partner per endpoint,
    subset neighbourhoods encode the subset) — CFI's `Z₂` is a global gadget-flip involution, not a
    transposition. So the twin bridge does **not** discharge CFI; it covers the complementary
    genuine-twin / module class. CFI still needs remaining-point-1 below (the general
    non-transposition gadget twist via `configSwap_of_swap`). Remaining-point-2 (decision-node
    depth) is reduced only for the twin/module class, not for CFI.

**The gadget twist (`hwit`) is now BUILT — the named nut collapses to cascade-1b.**
Stage-3's gadget flip was constructed and proven sound for *both* oracles
([`CFI.lean §15`](../GraphCanonizationProofs/ChainDescent/CFI.lean), Phases 0–6, axiom-clean —
see §4 below). So of the two formerly-open pieces:

1. **The general gadget twist — DONE.** `IsCFI'.cfiFlipAut F` (the cycle-space flip) is an
   `Aut(adj)` involution with localised support, proven to satisfy `configSwap_of_aut`
   (`configSwap_of_cfiFlipAut`) — i.e. the CFI gadget twist genuinely fires the oracle, no
   rank-alignment. The full `Aut(CFI) ≅ Z₂^β ⋊ Aut(H)` iso was **not needed** — only the `Z₂^β`
   generators (the existence half). `hwit` is no longer open.
2. **Decision-node depth (cascade-1b) — the sole remaining open content.** The flip exists and
   fires; what's open is that a *decision-local* cycle `F` exists for every decision — mapping
   the pair, confined to `F`-free gadgets off the committed set, with cell-coherence
   (`σ.σ a w = σ.σ b w`, `χι` on the F-support). Isolated as `CFIGadgetFlippableLocal`
   (`LinearOracle.lean §L.9`) / `CFILayerGadgetFlippable` (`Cascade.lean`, Tier-3a `hwit`).
   **Open but not GI∈P**, **shared with the cascade oracle** (`cascade-oracle.md` §2: 1a proved,
   1b open).

Net: the genuine open content is now exactly **cascade-1b** (the decision-local even cycle's
existence + cell-coherence) — one object, shared by both oracles, neither GI∈P nor the
rank-alignment. Discharge for odd-degree CFI routes through `theorem_1_HOR_cfi_oddDeg`
([`CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean), axiom-free) once it is in place.

---

## 6. Lean gotchas already hit (save time)

- `refineStep` is now a `def` — use the `refineStep_iff` **theorem**; downstream partition
  proofs are unchanged.
- `<` on `List ℕ` is an instance diamond — don't rank by List-lex; encode to `ℕ`.
- `IsAut.symm h : IsAut g.symm adj`; `g⁻¹` is defeq `g.symm` but not syntactic — bind
  `have hinv : IsAut cs.g⁻¹ adj := IsAut.symm cs.isAut` so `rw` matches.
- `ext v` on an `Equiv.Perm` equality **over-applies** into `Fin.val` (coerces to `ℕ`); use
  `apply Equiv.ext; intro v` to stop at the `Fin n` level.
- `labelledAdj π adj` is defeq `relabelMatrix π adj.adj` but `rw` won't auto-close it — finish
  with an explicit `rfl`.

---

## 7. Pointers

- **Lean:** `LinearOracle.lean` (`§L.1–L.7b`); `ChainDescent.lean` (refineStep concretization;
  `§16.2b` transport; `OrbitPartition` ~L3473; `theorem_1_HOR_at_depth` ~L3732);
  `CascadeOracle.lean` (`CellsAreOrbits`, `recoverableByDepth_cfi`); `CFI.lean`
  (`IsCFI'`, `OddDegree`, `theorem_1_HOR_cfi_oddDeg`).
- **Index:** [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md)
  `§L.7`/`§L.7b` (this work), `§L.6` (relativized completeness scaffold).
- **Memory:** `project_refinestep_concretized_2026-05-30.md` (M0 + M1a/b/c progress, full detail),
  `project_linear_oracle_spec_2026-05-28.md` (§L.6 retargeting + the B2/M1–M4 plan),
  `project_cascade_oracle_spec_2026-05-28.md` (the shared cascade-1b frontier).
- **Build:** `cd GraphCanonizationProofs && lake build`. Check axioms with
  `#print axioms <name>` (target: `[propext, Classical.choice, Quot.sound]`).
