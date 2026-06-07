# Chain descent — Route B handoff: the imprimitive branch, and the open `hreach`/`hfiber` frontier

> **STATUS (2026-06-06): Route B's mechanical chain is LANDED, axiom-clean, full build green.** The seal's
> `hImprimitive` branch (imprimitive scheme residual ⟹ reaches rigid) is no longer an opaque hypothesis: it is
> **mechanically reduced** to two intrinsic coverage interfaces, `hreach` (quotient / block-reach) and `hfiber`
> (fiber / within-block). The entire wreath-decomposition machinery is proved; **the single remaining open
> content is discharging `hreach`/`hfiber`** from the imprimitive residual's recovery. This doc catches a fresh
> reader up to that point.
>
> **UPDATE (2026-06-07): seal rigid side made symmetric + class-agnostic `hreach`/`hfiber` suppliers LANDED
> (axiom-clean, `Cascade.lean`).** Two advances since the chain landed: **(1)** the *leg-A* branch `hCascade` is
> now discharged the same way `hImprimitive` is — `schemeReproduced_of_visibleRealizers` (leg-A mirror of
> `schemeReproduced_of_blockDecomposition`) + `reachesRigidOrCameron_viaCascadeHarvest`, and the combined
> `reachesRigidOrCameron_viaBlocksAndCascade` discharges **both** rigid-side legs at once, so both bottom out at
> the *same* per-level recovery interface. **(2)** a **class-agnostic supplier toolkit** for the Route B
> interfaces: `hreach_of_quotientRealizers` (`hreach` from quotient/block-accurate realizers — strictly weaker
> than full recovery), `hfiber_of_fiberRealizers` (`hfiber` from within-block realizers), `blockHarvest_of_realizers`
> (full orbit realizers ⟹ both, `β` unused = the non-vacuity floor / subsumption), and `blockHarvest_of_visibleRecovery`
> (recovery + visible realizers ⟹ both — the metric/CFI witnesses plug straight in; Route B analogue of
> `noFusion_of_visibleRecovery`). **The structural finding (do carry forward): whole-residual recovery FACTORS as
> quotient-recovery (`hquot`) + fiber-recovery (`hfib`), each on a strictly smaller/coarser object; the open
> general case is exactly the separability-number reduction-to-constituents (§4 item 5), and these suppliers ARE that
> shape — supply `hquot`/`hfib` from the constituents, assemble via the chain.** On a *fully* recoverable class
> the decomposition is subsumed (β unused), so its independent value is the regime where quotient/fiber recover
> at lower depth than the whole.
>
> **UPDATE (2026-06-07, cont'd): (a) the block system is now DERIVED from `¬IsPrimitive` — end-to-end firing
> LANDED (axiom-clean).** `exists_nontrivial_closedSubset_of_not_isPrimitive` (`Scheme.lean`: imprimitive ⟹ a
> non-trivial closed subset `I`) + `schemeEquiv_class_eq_iff` (`β u = β w ↔ schemeEquiv I u w`) +
> `blockHarvest_of_not_isPrimitive_of_visibleRecovery` (`Cascade.lean`: `¬IsPrimitive` + recovery ⟹ the full
> `hBlockHarvest` bundle, β = `schemeEquiv I`-block-class built internally) + `reachesRigidOrCameron_viaRecovery`
> (the **fully-fired seal**: both branches keyed on recovery, only the cited `PrimitiveCCClassification`
> external). So the imprimitive branch fires with **no hand-supplied block system**. **The single remaining open
> content is (b):** supplying `hquot`/`hfib` (equivalently the recovery witness) in the *non-whole-recovering*
> regime — the genuine `s(C)` content (handoff §4 item 5), where the quotient/fiber recover but the whole does
> not. That is the substrate-conditional frontier the whole project carries.
>
> **UPDATE (2026-06-07, cont'd): Approach A (recursive reduction) STARTED — base-sequence phase-split tool
> LANDED (axiom-clean, `Cascade.lean`).** `CoversOrbitsAlong` (partial coverage, no terminal base) +
> `coversOrbits_append` (glue `CoversOrbitsAlong bs₁ S` + `CoversOrbits bs₂ (foldl S bs₁)` ⟹ `CoversOrbits
> (bs₁++bs₂) S`) + `coversOrbitsAlong_of_coversOrbits`. This is the structural enabler for ordering the descent
> **block-representatives-first, then within-block** (handoff §5.3): the quotient phase is partial coverage, the
> fiber phase the full tail, each supplied by a different (smaller/coarser) constituent's recovery.
> **HONEST RECALIBRATION (correcting the §3 base-sequence claim):** tracing the chain
> (`coversOrbits_of_blockDecomposition` → `stabilizerAt_le_closure_gensAt_step`), coverage is consumed at the
> base-sequence prefix levels *starting at `S=∅`*, and each level genuinely needs that level's head
> *orbit-transversal realized* — which **cannot** be sourced from deeper recovery (a deep aut fixes too much to
> move a shallow orbit). So per-level orbit-realization is **intrinsic**; the base-sequence freedom does **not**
> give a free shallow-recovery win. What it *does* give is the phase-split above, which is the genuine Approach-A
> prerequisite. NEXT (Approach A proper): supply `hquot`/`hfib` from constituent recovery — quotient via
> block-`warmRefine`/`BlockRefinementVisible` (A2-ii), fiber via block-restricted `CellsAreOrbits` — using
> `coversOrbits_append` to sequence the two phases; carry primitive-constituent recovery as the witness.
>
> **UPDATE (2026-06-07, cont'd): per-level fiber half LANDED + a difficulty-flip finding (axiom-clean,
> `Cascade.lean`).** `hfiber_of_fiberVisibleRealizers` discharges `hfiber` from **within-block visible
> realizers** (same-`warmRefine`-cell pairs *within a block*) — clean, no new machinery, and **strictly weaker
> than whole recovery** (satisfiable when within each block cells=orbits even if globally cells⊋orbits;
> Shrikhande-relevant, since its 1-WL merges are *across* blocks). **FINDING — the difficulty is the reverse of
> §4.1's "hreach is easier":** `BlockRefinementVisible` ("cells ⊆ blocks") makes a same-cell realizer stay
> *within* a block (`β(gb)=β(b)`) — that supports the **fiber**, not block-*moves*. `hreach` needs realizers
> that *move* `b` toward an orbit-mate's (possibly different) block, and the only way to harvest block-moves
> without whole-graph recovery is to recover the **block-orbits** = a **block-level 1-WL** (a `blockCell` colour
> = block-image of `warmRefine`, with `blockCells = blockOrbits`). So **the fiber is the clean direction; the
> quotient (`hreach`) needs block-1-WL modelling** — the focused next step (define `blockCell`, prove the
> block-image refinement + block-orbit recovery ⟹ block-reach realizers ⟹ `hreach` via
> `hreach_of_quotientRealizers`).
>
> **Quality bar (unchanged):** every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; full build
> green (`bash scripts/build.sh`, serial ~30–130s); regen `PublicTheoremIndex.md` via
> `python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers` and hand-fill Descriptions; **do not
> commit** (the user commits between messages).
>
> **Companions:** [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.5
> (the oracle-capability seal), §0.7.2 (the bottom-up derivation that birthed the primitivity reduction), §0.7.6
> (the deep-research verdict + the Route B summary); `Scheme.lean §11` (the primitivity bridges) and §13 (the
> block-visibility predicates); `Cascade.lean` "Part A" (the harvest / `CoversOrbits` machinery).

---

## 1. The goal and where it sits

The project's top-level goal is the **oracle-capability seal** (`docs/00-START-HERE.md` §2, exhaustive-obstruction
§0.5): *every residual reaches a rigid residual or is a Cameron section.* Assembled as one theorem
(`reachesRigidOrCameron` / `_viaHarvest` / `_viaBlocks`, `Cascade.lean`), it routes the landed trichotomy
`¬IsPrimitive ∨ ¬NonCascade ∨ Cameron` into the dichotomy `ReachesRigid ∨ IsCameronScheme`. Three branches:

- **`¬NonCascade`** (the residual *cascades* / recovers at poly depth) → leg A (orbit recovery) → reaches rigid.
  Carried as `hCascade`, well-supported (`recoverableByDepth_pPolynomial`/`_cfi` witnesses).
- **Cameron** → flagged. Landed modulo the **cited** `PrimitiveCCClassification` (Babai 1981 / Sun–Wilmes 2015 —
  see §4 for the *rank caveat* and why our **largeness-keyed** form is the solid one).
- **`¬IsPrimitive`** (imprimitive) → **must reach rigid by refining on the block system.** This is the branch
  Route B addresses, formerly the opaque hypothesis `hImprimitive`.

**Why the imprimitive branch was the one open in-scope gap.** Imprimitive ⟹ there is a non-trivial closed
subset `I` (a block system). The descent wants to *see* the blocks and refine on them — but **block-visibility
is depth-graded, not depth-1** (refuted unconditionally by the **Shrikhande graph**: its rank-4 orbital scheme
has a genuine 4-block system that 1-WL-from-`v` cannot see; it recovers only at depth 2). So you cannot assume
the block is visible at the node you act on. The honest `ReachesRigid` must be *"the cross-branch harvest
reproduces `Aut_S`"* (`closure gens = StabilizerAt`) — **not** "reaches discrete eventually," which is
`cascadesAt_univ`, trivially true, hence vacuous.

---

## 2. What's landed — Route B's four layers (all axiom-clean)

The idea: an imprimitive `Aut_S` **permutes** a block system, so its orbit pairs *cross* block boundaries. The
group is a wreath-style extension of the **fiber** (block stabiliser acting on one block) by the **quotient**
(group acting on the set of blocks). Coverage of the whole group factors into fiber-coverage + block-swap
coverage. Crucially this is done **intrinsically on the original `Fin n`** — no sub-scheme is ever materialized.

| Layer | Lemmas (file) | What it proves |
|---|---|---|
| **0 — gate** | `schemeBlock_fiber_transitive`, `schemeBlocks_transitive` (`Scheme.lean §11.1`) | Fiber (block stabiliser on a block) and quotient (group on blocks) are **transitive**, hence **schurian** — the recursion stays in the schurian class. Via Mathlib `IsBlock.orbit_stabilizer_eq` + the landed `isBlock_schemeEquiv` + `schemeAutGroup_isPretransitive`. |
| **1 — heart** | `orbitCoverage_of_blockDecomposition`, `coversOrbits_cons_of_blockDecomposition` (`Cascade.lean`) | **Swap decomposition.** Full-orbit coverage of base point `b` factors into **block-reach** (`hreach`) + **within-block coverage** (`hfiber`); the realizer is the composite `h * σ` (block-swap `σ`, then fiber move `h`) living in the closure subgroup. |
| **2 — assembly** | `coversOrbits_of_blockDecomposition`, `reachesRigid_of_blockDecomposition` (`Cascade.lean`) | Iterate layer 1 down a base sequence ⟹ `CoversOrbits adj P gens bs S` ⟹ `closure (gensAt … S) = StabilizerAt adj P S` = **ReachesRigid**. Induction on `bs`, entirely on `Fin n`. |
| **3 — capstone wiring** | `SchemeReproduced`, `schemeReproduced_of_blockDecomposition`, `reachesRigidOrCameron_viaBlocks` (`Cascade.lean`) | Carry the graph-level result to the scheme seal via the `schemeAdj` bridge: `hImprimitive` is **supplied** (not hypothesized), reduced to `hreach`/`hfiber` bundled as `hBlockHarvest`. |

**The seal's free inputs are now exactly:** the cited `PrimitiveCCClassification`, `hCascade` (leg A recovery),
and `hBlockHarvest` (the imprimitive recovery, **Route-B-reduced to `hreach` + `hfiber`**).

### 2.1 The two load-bearing facts that made it work

1. **`CoversOrbits`'s coverage clause is keyed on `Subgroup.closure (gensAt …)` — a group, closed under
   composition** — not single generators (`Cascade.lean`, `def CoversOrbits`). *This is why the block-swap ∘
   fiber composition is legal.* The single-generator `NoFusion` form **cannot** do this; the closure form can.
   (Contrast: my earlier `noFusion_of_warmSeparatedPartition` handles only the *non-swapped* separable case,
   where orbits *respect* the partition — `hsep`. Route B handles the *swapped* case the wreath structure
   actually presents.)
2. **The intrinsic formulation sidesteps the rejected materialized-quotient route.** `hreach`/`hfiber` are
   **block-restricted quantifiers over the original `Fin n`**, so "recurse on quotient/fiber" lives in the
   *coverage predicate*, not in new `AssociationScheme`/`AdjMatrix` types. The materialized scheme quotient
   `S//I` (re-index `Fin n/~ → Fin m`, re-establish all 5 axioms incl. `intersectionNumber_well_defined`) was
   scoped **intractable** and **rejected** (exhaustive-obstruction §0.7.2 finding (ii); `tier3a-b1-build-plan`
   §4 Approach A). **Do not reopen it.** Route B avoids it by construction.

---

## 3. The open targets: `hreach` and `hfiber`

These are the *only* remaining open content for the imprimitive branch. In the graph-level lemma
`reachesRigid_of_blockDecomposition` (and bundled in `reachesRigidOrCameron_viaBlocks`'s `hBlockHarvest`), for a
partition `β : Fin n → ι` (the block-class function of a non-trivial closed subset `I`):

```lean
-- hreach (QUOTIENT / block-reach): the closure can send b into the BLOCK of every orbit-mate w.
∀ T : Finset (Fin n), ∀ b w,
  OrbitPartition adj P T b w →
  ∃ σ ∈ Subgroup.closure (gensAt adj P gens T), β (σ b) = β w

-- hfiber (FIBER / within-block): the closure realizes every SAME-BLOCK orbit pair.
∀ T : Finset (Fin n), ∀ u w,
  OrbitPartition adj P T u w → β u = β w →
  ∃ h ∈ Subgroup.closure (gensAt adj P gens T), h u = w
```

In the scheme setting (`reachesRigidOrCameron_viaBlocks`): `adj = schemeAdj S.toAssociationScheme`,
`P = (fun _ _ => POE.unknown)` (trivial), and `β v = {y | S.toAssociationScheme.schemeEquiv I v y}` (the
`schemeEquiv I`-block of `v`, so `β u = β w ↔ schemeEquiv I u w`, since blocks are equivalence classes).

**Read them as recovery on the two constituents:**
- `hreach` = *the quotient recovers* — the harvest reaches the correct block for every orbit-mate. The block
  partition is **coarser** than the orbit partition, so this should be *easier* than full orbit recovery.
- `hfiber` = *the fiber recovers* — the harvest covers within-block orbit pairs. This is recovery on a smaller
  action (the block, `|B| < n`).

`β` is **fixed** (the block system of the *original* scheme's `I`) and stays valid at every level `T`: a block
system of `G` is a block system of every subgroup, so as `T` grows and `Aut_T` shrinks, `β` remains a valid
(possibly refinable) block partition. So `hreach`/`hfiber` with fixed `β` are meaningful at all `T`.

---

## 4. Key insights to carry (durable context)

1. **`hreach` is the easier target, and it connects to the *coarse* block-visibility the project already
   isolated.** A closed subset `I` is closed under the **complex product = 1-WL's own counting operation**, so
   the coarse I/¬I boundary is "1-WL-closed by construction" in a way the fine orbit structure is not
   (exhaustive-obstruction §0.7.2 A2 analysis). The graded predicate is **`BlockRefinementVisible`** (`Scheme.lean
   §13`), discharged by **A2-ii** `blockRefinementVisible_of_schemePartSeparates` (holds whenever the depth-`n`
   counting partition `schemePart_at` separates the I-boundary — *off* the full-recovery class). The reduction
   `cell_splits_of_imprimitive` already turns block-visibility into refinement progress. **The natural attack on
   `hreach`: route block-reach through A2-ii block-visibility** (visible block ⟹ refinement-computable
   block-reach realizer), mirroring how `coversOrbits_of_visibleRealizers` /
   `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` turn recovery into computable coverage.
2. **`hfiber` is recovery restricted to a block.** The Phase-0 gate (`schemeBlock_fiber_transitive`) gives that a
   block is a *single fiber-orbit*, so within-block coverage is exactly the fiber action's recovery. The
   intrinsic challenge: state "recovery on a block" without materializing the block as a scheme. The existing
   recovery interface (`CellsAreOrbits`, `RecoverableByDepth`, `coversOrbits_of_realizers`) is the substrate;
   the block-restriction is `β u = β w`.
3. **Block-visibility — hence `hreach`/`hfiber` — is DEPTH-GRADED, not depth-1** (Shrikhande). The `∀ T`
   quantifier is essential: the realizers may appear only once enough is individualized (depth ≥ the
   WL-dimension). Choose/allow the base sequence `bs` to reach that depth. At discreteness everything is visible
   (trivially), so the interfaces are *satisfiable*; the content is doing it at *bounded* depth on a class.
4. **The de-risking gate is settled positively (do not re-litigate).** The deep-research non-schurity risk
   (Evdokimov–Ponomarenko arXiv:1012.5393) is about **abstract S-ring** generalized wreath products. The
   descent's residual is a **genuine group orbital scheme**; its fiber and quotient are *induced group actions*,
   hence transitive (Phase 0), hence schurian. So the recursion stays in-class. The risk does **not** bite.
5. **The deep-research verdict on the unconditional discharge (exhaustive-obstruction §0.7.6):** discharging
   `hreach`/`hfiber` *unconditionally* (for all schurian schemes) is the **`s(C)` / WL-dimension boundary** and is
   **genuinely open, not citably closeable.** The right vocabulary: every CC has a **separability number `s(C)`**
   (Evdokimov–Ponomarenko), with `s(C) ≤ m ⟺ C is determined by its m-dim intersection numbers ≈ WL-dimension`;
   the residual leak is *a schurian CC with high `s(C)`, imprimitive, non-abelian, non-Cameron*, and **no theorem
   bounds `s(C)` for such CCs.** So the realistic targets are: **(a)** discharge `hreach`/`hfiber` on a
   *recoverable class* (metric/DRG/CFI) as witnesses (like `recoverableByDepth_cfi`), and **(b)** keep the
   general case carried (the substrate-conditional frontier the whole project carries). Closing it in full ≈
   the WL-dimension question, GI-adjacent.
6. **Two corrections the deep research forced (already applied; don't reintroduce the errors):**
   - **Circulant WL-dimension is UNBOUNDED** (`≥ c√log n`, Wu–Ren–Ponomarenko arXiv:2507.10116, 2025) — *not*
     bounded. Only **prime-power order** is bounded (`≤3`, Ponomarenko 2206.15028). So **"abelian + vertex-
     transitive ⟹ bounded WL" is FALSE.** (The old "circulants bounded, Muzychuk" premise was wrong.)
   - **Leg-C citation:** the *all-rank* Babai minimal-degree dichotomy was **refuted** by Eberhard's rank-28
     counterexamples (2022); it is clean only at rank 3 (Babai 2014) / rank 4 (Kivva 2023). **But our
     `PrimitiveCCClassification` is keyed on *largeness* (super-poly Aut), which maps to the solid Sun–Wilmes
     large-Aut classification — not the refuted minimal-degree form.** So our citation is on robust ground; this
     also validates the project's "driver is largeness, not non-abelian" decision.

---

## 5. How to attack `hreach`/`hfiber` — concrete starting points

**Recommended first target: discharge on the recoverable class (witnesses), not the general case.**

1. **`hreach` via A2-ii block-visibility.** Build the analogue of `coversOrbits_of_visibleRealizers` for the
   *coarse block boundary*: where `BlockRefinementVisible` holds (discharged by
   `blockRefinementVisible_of_schemePartSeparates`), a block-reach realizer is refinement-computable, so the
   closure (which collects the refinement-visible realizers) satisfies `hreach`. The bridge to assemble:
   "block-visible at `T` ⟹ `∃ σ ∈ closure (gensAt … T), β (σ b) = β w`." This is where the *coarse* boundary's
   "1-WL-closed by construction" property is the lever.
2. **`hfiber` via within-block recovery.** Where the fiber recovers (cells = orbits *restricted to the block*),
   `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` makes the same-block realizer computable. Use the
   Phase-0 fiber-transitivity (`schemeBlock_fiber_transitive`) to know the block is one fiber-orbit.
3. **Pick the base sequence `bs` to respect the block hierarchy** (block representatives first, then within-block)
   so the depth-graded visibility is reached level by level — mirrors the `cascadeComposition` / `LayerChain`
   telescoping (`Cascade.lean`, the harvest-window machinery). `reachesRigid_of_blockDecomposition` already
   accepts any `bs` with a terminal base, so the freedom is yours.
4. **Witness classes to target first:** metric/DRG (already `recoverableByDepth_pPolynomial`), CFI gauge
   (`recoverableByDepth_cfi`), and the imprimitive vertex-transitive examples that *do* recover (cube `H(3,2)`,
   Johnson(6,3), circulants of low prime-factor count — see the A2-i battery, exhaustive-obstruction §0.7.2). The
   Shrikhande graph is the depth-2 (not depth-1) witness — useful as the *graded* test case.

---

## 6. What NOT to do (already-scoped dead ends)

- **Do NOT materialize the quotient/fiber as `AssociationScheme`/`AdjMatrix` objects.** Re-indexing `Fin n/~ →
  Fin m` + re-establishing all 5 scheme axioms is intractable (exhaustive-obstruction §0.7.2 (ii);
  `tier3a-b1-build-plan` §4 Approach A). Route B deliberately stays intrinsic on `Fin n`; keep it that way.
- **Do NOT pursue unconditional depth-1 block-visibility (A2-iii).** Refuted by Shrikhande. Only the **graded**
  form (A2-ii, `blockRefinementVisible_of_schemePartSeparates`) is available.
- **Do NOT try to discharge `hreach`/`hfiber` by citation.** The deep research (§0.7.6) established the
  unconditional case is genuinely open, not citably-impossible. Cameron's theorem closes leg C; there is **no**
  analogue for the imprimitive-non-abelian-high-`s(C)` quadrant.
- **Do NOT reintroduce** the "circulants bounded WL (Muzychuk)" premise or the all-rank Babai dichotomy (§4.6).

---

## 7. Reading order for a fresh reader

1. **This doc** — the goal, the four landed layers, the open `hreach`/`hfiber`.
2. [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) **§0.5** (the seal),
   **§0.7.2** (the bottom-up derivation + the full A2 / block-visibility saga — the *birthplace* of the
   primitivity reduction and the Shrikhande refutation), **§0.7.6** (the deep-research verdict + Route B summary).
3. `Scheme.lean` **§11** (`isBlock_schemeEquiv`, `isPreprimitive_iff_isPrimitive`, the primitivity↔block bridges),
   **§11.1** (the Phase-0 gate), **§13** (`BlockRefinementVisible`, `cell_splits_of_imprimitive`, A2-ii).
4. `Cascade.lean` "Part A" — `CoversOrbits` and the harvest machinery (`gensAt`,
   `stabilizerAt_eq_closure_gensAt_of_coversOrbits`, `coversOrbits_of_visibleRealizers`,
   `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits`), then the Route B lemmas (§2 above) and the seal
   capstone (`reachesRigidOrCameron*`).
5. [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) — the ground truth for *what is
   proved*; grep the lemma names in §2 above.
