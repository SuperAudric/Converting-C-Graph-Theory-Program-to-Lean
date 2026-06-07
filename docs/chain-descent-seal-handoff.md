# Chain descent — THE SEAL HANDOFF: current state and the gaps to "consumed-or-Cameron"

> **STATUS (2026-06-07): this is the authoritative handoff for the oracle-capability seal.** It **subsumes**
> [`chain-descent-routeB-handoff.md`](./chain-descent-routeB-handoff.md) (Route B is now one *partial* attack on
> one gap, G2-A below, and its capstones were found vacuous — see §3). Read this doc to pick up *any* of the
> open gaps. The goal is to close all of them, including pushing through the GI-adjacent frontier (G2).
>
> **Quality bar (unchanged):** every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; full build
> green (`bash scripts/build.sh`, serial ~20–60s); regen `PublicTheoremIndex.md` via
> `python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers` then hand-fill Descriptions and **delete
> stale rows by hand** (the tool keeps orphaned rows, reporting "no matching source decl"); **do not commit** (the
> user commits between messages).
>
> **Companions:** [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) (the EOL /
> leg-C theory + the bottom-up derivation §0.7), [`chain-descent-declassing.md`](./chain-descent-declassing.md)
> (recovery + the unified harvest), [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) (Part A,
> the cross-branch harvest), `Group.lean` (leg B), `Scheme.lean` (primitivity, blocks, the trichotomy),
> `Cascade.lean` (the harvest, the tower, the seal capstone).

---

## 0. How to read this — one rule

Treat every summary (this doc, MEMORY, older prose) as a *hypothesis* to confirm against the Lean source and
`PublicTheoremIndex.md`. The source wins. In particular, **§3's vacuity finding is the most important correction
in the project's recent history** — internalize it before forming any view, because most of the "seal is
complete" prose elsewhere predates it.

---

## 1. The goal — the two guarantees

The project canonizes a graph by descending the individualization–refinement tree and, at each cell, asking an
**oracle** to sort it into orbits so the descent branches on one representative per orbit (see
[`00-START-HERE.md`](./00-START-HERE.md), [`chain-descent-strategy.md`](./chain-descent-strategy.md)). The
end-state is stated as **two separate guarantees** ([strategy §15](./chain-descent-strategy.md)), never one:

1. **Symmetry completeness (the seal).** *Every residual symmetry is **consumed by an oracle** OR is a **Cameron
   section**.* "Consumed" has two faces:
   - **Leg A** — *visible / cascade recovery*: after bounded individualization, refinement (1-WL) cells coincide
     with `Aut`-orbits, so the orbit partition is *computed* and the harvest reproduces the group.
   - **Leg B** — *hidden abelian*: a `Z₂^d`/abelian symmetry 1-WL cannot see (CFI gauge twists), consumed by the
     **linear oracle** (read a unique candidate twist off one branch, verify, collapse).
   - **Leg C** — *Cameron section*: a large primitive non-abelian action (`Aₖ`-on-subsets / product actions);
     **flagged**, honest hardness.
2. **Polynomial time (two escapes).** Poly *unless* a Cameron section (residual non-trivial) *or* an **IR blind
   spot** (a multipede — refinement-resistant rigid core, *no* symmetry, residual trivial). The IR-core is the
   *¬∃-symmetry* flag and sits **outside** the seal (distinguished at flag time by residual-group order).

So the seal's honest dichotomy on the symmetric case is **`(legA ∨ legB) ∨ Cameron`**. This handoff is about
closing the seal to that statement.

---

## 2. Current Lean state of the seal

**The abstract capstone (genuine, untouched):** `reachesRigidOrCameron` and `reachesRigidOrCameron_viaHarvest`
(`Cascade.lean`) — parametric in an abstract `ReachesRigid : ∀ m, SchurianScheme m → Prop`; they *reduce*
`ReachesRigid ∨ IsCameronScheme` to two branch hypotheses + the classification. Their content depends entirely on
what `ReachesRigid` is instantiated to.

**The concrete headline:** `reachesRigidOrCameron_viaRecovery : SchemeRecovered n S ∨ IsCameronScheme n S`
(`Cascade.lean`), with `ReachesRigid := SchemeRecovered`. It reduces the goal to three carried inputs:

| Input | What it is | Status |
|---|---|---|
| `hClassify : PrimitiveCCClassification …` | cited Babai 1981 / Sun–Wilmes 2015: primitive, large, rank ≥ 3 ⟹ Cameron | cited; solid rank 3/4 (G3) |
| `hCascadeHarvest : ¬ NonCascadeViaHarvest IsLarge n S → SchemeRecovered n S` | **"small ⟹ recovered"** (see note) | carried (G1, G2) |
| `hImprimRecovery : ¬ S.…IsPrimitive → SchemeRecovered n S` | **"imprimitive ⟹ recovered"** | carried (G1, G2) |

**Note — what `NonCascade` actually is.** `NonCascadeViaHarvest IsLarge n S` (`Cascade.lean`) is
`∃ gens bs, hsound ∧ NoFusion … ∧ base ∧ IsLarge (Nat.card (closure gens))`. Its `NoFusion` clause is *orbit*-level
coverage, which is **vacuously satisfiable** (§3), so `NonCascadeViaHarvest ≈ IsLarge(|Aut|)` = "the group is
large." Hence `¬NonCascade ≈ small`. The trichotomy
`exhaustiveObstruction_scheme_nonCascade_trichotomy : ¬IsPrimitive ∨ ¬NonCascade ∨ Cameron` (`Scheme.lean`) is
therefore genuine — it is `primitive ∧ large ∧ rank≥3 ⟹ Cameron` (the classification) cased out. The
`LargenessBridge` / `largenessBridge_viaHarvest` (`NonCascade ⟹ IsLargeScheme`) is **tautological** (`IsLarge ⟹
IsLarge` once the vacuous coverage is stripped) — it does *not* derive largeness; the genuine "¬consumed ⟹ large"
is open (part of G2).

**`SchemeRecovered` (the rigid predicate), `Cascade.lean`:**
```lean
def SchemeRecovered : ∀ (m : Nat), SchurianScheme m → Prop :=
  fun m S => ∃ (gens : Set (Equiv.Perm (Fin m))) (bs : List (Fin m)),
    (∀ g ∈ gens, g ∈ StabilizerAt (schemeAdj S.toAssociationScheme) (fun _ _ => POE.unknown) ∅) ∧
    (∀ T, (∅ : Finset (Fin m)) ⊆ T → ∀ b w,                       -- VISIBLE realizers, every level
        warmRefine … (individualizedColouring m T) b = warmRefine … (individualizedColouring m T) w →
        ∃ g, g ∈ gens ∧ ResidualAut … T g ∧ g b = w) ∧
    IsBase … (bs.foldl (fun s b => insert b s) ∅)
```
`schemeRecovered_of_visibleRealizers` bundles the inputs into it; `schemeAutGroup_eq_closure_of_recovered` derives
`∃ gens, closure gens = SchemeAutGroup S` from it (the "group reproduced" payoff, earned not free).

**The logical skeleton is sound:** every scheme is `imprimitive` (→ hImprimRecovery) or `primitive`; if primitive,
`large` (→ Cameron) or `small` (→ hCascadeHarvest). So `SchemeRecovered ∨ Cameron`, *modulo the three inputs*.

---

## 3. The vacuity correction — orbit-level vs visible (READ THIS)

A wiring-verification pass (2026-06-07) found the previous rigid predicate
`SchemeReproduced := ∃ gens, closure gens = SchemeAutGroup S` is **vacuously true** for every scheme —
machine-checked: `⟨(↑SchemeAutGroup), Subgroup.closure_eq _⟩` proves it (every finite group is finitely generated).

**The deeper root cause — orbit-level coverage is vacuous.** Any condition of the shape
`OrbitPartition T b w → ∃ g ∈ gens, ResidualAut T g ∧ g b = w` is satisfiable by `gens = all automorphisms`,
because **orbit-mates are automorphism-related by definition**. So `NoFusion`, `CoversOrbits`, `hreach`/`hfiber`
(the Route B interfaces), and any `∃ gens, closure = group` packaged from them are **content-free as "the scheme
recovers."**

**The genuine, non-vacuous content is VISIBLE (refinement-computable) realizers:**
`warmRefine{T} b = warmRefine{T} w → ∃ g ∈ gens, …` ranges over **same-cell** pairs. A same-cell pair need *not* be
an orbit pair, and when cells ⊋ orbits (high `s(C)`) it has **no realizing automorphism** — so the clause is
**false**. Visible recovery holds exactly on the recoverable class and is genuinely unprovable for a non-recovering
scheme. That is why `SchemeRecovered` is keyed on visible realizers (machine-checked: the old trivial witness no
longer typechecks against it).

**Retired (proved trivially-true disjunctions):** `SchemeReproduced`, `schemeReproduced_of_blockDecomposition`,
`reachesRigidOrCameron_viaBlocks` / `_viaCascadeHarvest` / `_viaBlocksAndCascade`, the old
`schemeReproduced_of_visibleRealizers`, `blockHarvest_of_not_isPrimitive_of_visibleRecovery`.

**Kept valid (genuine *conditional* lemmas — it was the existential packaging that was vacuous, not these):**
`reachesRigid_of_blockDecomposition`, the suppliers `hreach_of_quotientRealizers` / `hfiber_of_fiberRealizers` /
`blockHarvest_of_realizers` / `blockHarvest_of_visibleRecovery`, `coversOrbits_*` / `coversOrbits_append` /
`CoversOrbitsAlong`, and especially **`hfiber_of_fiberVisibleRealizers`** (the *visible* fiber half — genuinely
non-vacuous).

**Lesson to carry:** when you state any "recovers / reaches rigid / reproduces" predicate, it MUST be keyed on
visible (warmRefine-cell) realizers or some other refinement-computable / depth-bounded quantity — never on an
unconstrained `∃ gens` over a group, and never on orbit-level coverage. Re-check non-vacuity by trying to prove it
with `gens = ↑(the group)` or `gens = all auts`; if that works, it's vacuous.

---

## 4. The gaps

Four gaps stand between the current state and the unconditional `(legA ∨ legB) ∨ Cameron`. Each subsection is
self-contained for a fresh reader attacking *that* gap.

### G1a — `SchemeRecovered` is depth-1-only; it must become depth-graded (leg A scope)

**The problem.** `SchemeRecovered` demands visible realizers at **every** level (`∀ T`). That is *per-level*
recovery = essentially **depth-1 / metric** recovery. A **depth-graded** scheme fails it: CFI recovers only at
depth `tw(H)`, Shrikhande only at depth 2 — at intermediate depths cells ⊋ orbits, so a same-cell non-orbit pair
breaks the clause. So even canonical *consumable* cases beyond the metric family are not captured.

**Why broadening is not free.** The right predicate is "recovers at **polynomial** depth" (`RecoverableByDepth`
shaped: `∃ S, S.card ≤ bound ∧ CellsAreOrbits S`). But the *unbounded* form is itself vacuous —
`recoverableByDepth_univ` proves `RecoverableByDepth adj P n` for every graph (individualize everything ⟹
discrete). **Non-vacuity requires the polynomial bound**, and "polynomial" is the project's central open factor
(T-C, [calculator §4](./chain-descent-calculator.md)). So G1a is partly a *modelling* improvement (depth-graded
beats per-level — captures CFI/Shrikhande) and partly the polynomiality boundary.

**What to build on.** `RecoverableByDepth`, `CellsAreOrbits`, `cellsAreOrbits_of_discrete` (`CascadeOracle.lean`);
witnesses `recoverableByDepth_pPolynomial` (metric/DRG, depth 1), `recoverableByDepth_cfi` (CFI, depth `tw`),
`recoverableByDepth_scheme` (rank-2). The **cross-branch harvest** turns recovery into the group:
`closure_eq_stabilizerAt_of_visibleRealizers`, `crossBranchHarvest_reproduces_residual`,
`autP_reproduced_of_visibleRealizers` (`Cascade.lean` Part A). The localisation core
`orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` is the bridge "recovery ⟹ visible realizers ≡ orbit
realizers."

**The honest subtlety (the localisation gap).** The harvest chain (`coversOrbits`) consumes coverage at
base-sequence *prefix* levels including shallow ones, and **per-level orbit-realization is intrinsic** — a deep
automorphism fixes too much to move a shallow orbit, so deep recovery does *not* supply shallow coverage for free
(established 2026-06-07; see [routeB-handoff §base-sequence recalibration]). So a depth-graded `SchemeRecovered`
keyed on a single bounded recovery set must be reconciled with the chain's per-prefix demand. The likely route:
the **tower / `cascadeComposition`** (G2-A's machinery) — recovery composes across layers with *depths add*, and
each prefix's coverage is a layer. This couples G1a to the tower.

### G1b — leg B (hidden abelian) is missing from the seal — THE most actionable gap

**The problem.** `SchemeRecovered` is visible-recovery only. An abelian-but-not-visibly-recovering scheme is
consumed by the **linear oracle** (leg B), not by refinement, so it fails `SchemeRecovered` *and* is not Cameron —
the seal cannot place it. Concretely this is real: **high-WL circulants** are abelian and **unbounded** WL-dimension
(`≥ c√log n`, Wu–Ren–Ponomarenko 2025; only prime-power order is bounded — see §6), so they do *not* visibly
recover, yet they are consumed (abelian ⟹ unique candidate ⟹ linear oracle). Without leg B the seal is `legA-only
∨ Cameron`, which is **false** on these.

**Why it is closeable — the proof core is landed and citation-free.** The bottom-up derivation
([exhaustive-obstruction §0.7.2](./chain-descent-exhaustive-obstruction.md)) proves *abelian ⟹ unique candidate ⟹
consumed* with no citation. The Lean core is in **`Group.lean`**:
- `stabilizer_eq_bot_of_isPretransitive_comm` (L1) — transitive abelian ⟹ regular.
- `existsUnique_smul_of_isPretransitive_comm` (L2) — unique group element moving `e ↦ f`.
- **`smul_eq_on_orbit_of_comm` (L3, load-bearing)** — any two candidates for a decision *agree on the whole
  orbit*; quotient/faithfulness-free, so it survives CFI's non-trivial global stabilizers.
- `aut_agree_on_orbit_of_comm`, `not_comm_of_orbit_disagree` (cell-disagreement ⟹ non-abelian),
  `card_eq_of_isPretransitive_comm`, `not_comm_of_isPreprimitive_card_lt` (large primitive ⟹ non-abelian).

**What to build (the task).** Define an `AbelianConsumed` (leg-B) predicate — the honest non-vacuous form is "the
residual on the cell is abelian (commuting), and the unique candidate is realized," keyed via L3 so it is *not*
orbit-level-vacuous (the uniqueness is the content). Then widen the rigid side: prove
`reachesRigidOrCameron_viaAB : (SchemeRecovered ∨ AbelianConsumed) ∨ IsCameronScheme`, routing the **¬D2** /
abelian branch to leg B. **Caution:** check non-vacuity exactly as in §3 — "abelian" as a bare predicate on the
group is fine (it's a real restriction), but make the *consumption* witness depend on the unique-candidate (L3),
not on an unconstrained `∃ gens`. The discretizing-oracle limit (§6) says multi-step abelian (`tw ≥ 2`) needs the
*cross-branch* harvest, so leg B's consumption witness for `tw ≥ 2` is the Part-A harvest at the recovery depth,
not a within-cell read — keep that in scope.

### G2 — the leaks: non-recovering ∧ non-Cameron (the open frontier)

`hImprimRecovery` and `hCascadeHarvest` are carried because they are **false in general** — imprimitive does not
imply recovery (Shrikhande), small does not imply recovery (high-WL structures). Their complement is the leak,
which (using `non-Cameron ⟹ ¬primitive ∨ small`, from the classification) splits into:

- **G2-A — Leak-A: imprimitive, non-recovering, non-Cameron.** The Route B target. The genuine content is
  *visible quotient + fiber recovery* composing to whole recovery without whole-graph recovery — the **`s(C)`
  reduction-to-constituents** ([exhaustive-obstruction §0.7.6](./chain-descent-exhaustive-obstruction.md): sought
  and not located). Landed pieces: `hfiber_of_fiberVisibleRealizers` (the **fiber half**, visible, non-vacuous);
  the conditional chain `reachesRigid_of_blockDecomposition`; block extraction
  `exists_nontrivial_closedSubset_of_not_isPrimitive` + `schemeEquiv_class_eq_iff` (`Scheme.lean`); block-visibility
  `BlockRefinementVisible` + `blockRefinementVisible_of_schemePartSeparates` (A2-ii) + `cell_splits_of_imprimitive`
  (`Scheme.lean §13`); the schurity gate `schemeBlock_fiber_transitive` / `schemeBlocks_transitive` (`Scheme.lean
  §11.1`); the phase-split `coversOrbits_append` / `CoversOrbitsAlong`. **Open sub-piece (the quotient half):** a
  **block-level 1-WL** — a `blockCell` colour (block-image of `warmRefine`) with `blockCells = blockOrbits` — to
  supply the *block-move* (quotient) realizers `hreach` needs. Finding (2026-06-07): block-visibility
  (`cells ⊆ blocks`) supports the *fiber* (same-cell stays in-block), **not** block-moves; the quotient genuinely
  needs the block-1-WL.

- **G2-B — Leak-B: small, primitive, non-abelian, non-recovering, non-Cameron.** The small-but-high-WL-dimension
  frontier (a primitive small non-cascading scheme; [exhaustive-obstruction §0.7.6](./chain-descent-exhaustive-obstruction.md)
  flags this exact quadrant). After leg B removes the abelian case, this is the non-abelian remainder. The
  bottom-up route claims *non-consumed ⟹ large* (so this quadrant would be empty), but that derivation rests on the
  largeness argument, which is **tautological** under the orbit-level vacuity (§2 note) — so it does **not** yet
  rule Leak-B out. Genuinely open.

**The well-foundedness that bounds G2-A** (do not mistake the recursion for infinite regress): an imprimitive
scheme decomposes into a **quotient** (`m < n` blocks) + **fiber** (`|B| < n` points), both strictly smaller and
schurian (the §11.1 gate). The recursion is the **imprimitivity block tower**, height ≤ log₂ n, bottoming at a
**primitive** piece (no finer blocks) handled by the seal's own trichotomy (leg A recover, or leg C Cameron, or
the G2-B leak). So G2-A reduces, via ≤ log n layers, to G2-B + the citation.

**The tower-collapse mechanism (use this, do not build level-by-level).** `cascadeComposition_pathFixing`
(`Cascade.lean`) already composes per-**layer** recovery into whole recovery with **depths add**: from a single
per-layer hypothesis `hwit` ("the layer's residual orbit symmetry is realized by a *path-fixing* automorphism")
plus a base, it yields `Discrete` at the cumulative set, depth `≤ Σ fᵢ` (`cumulative_card_le`). The block tower is
the natural layer sequence; per-layer `hwit` is the carried substrate-conditional content (the block-1-WL at *one*
layer, reused for all). **But (caveat from the §3 wiring check):** `cascadeComposition` outputs *recovery*
(`Discrete` / `CellsAreOrbits`), and connecting that to a non-vacuous group reproduction must go through *visible*
realizers — verify the `hwit → visible-realizer → SchemeRecovered` wiring is non-vacuous before relying on it (the
old `SchemeReproduced` route here was exactly what was vacuous).

### G3 — the citation

`PrimitiveCCClassification` (`Scheme.lean`) — primitive, large, rank ≥ 3 ⟹ Cameron. Carried as a `def`-Prop
hypothesis (never a fresh `axiom`); the project stays custom-axiom-free. Solid at **rank 3** (Babai 2014) and
**rank 4** (Kivva 2023); the all-rank minimal-degree dichotomy was **refuted** (Eberhard rank-28, 2022) — but our
form is keyed on **largeness** (super-poly Aut), which maps to the solid Sun–Wilmes large-Aut classification, not
the refuted form. The group-side bridge `isPreprimitive_of_isPrimitive` (`Scheme.lean §11`) converts the descent's
combinatorial `IsPrimitive` to Mathlib's `IsPreprimitive` the citation is stated against. This gap is "as closed
as it gets" without formalizing Cameron from scratch (years of work); leave it cited.

---

## 5. Reusable machinery (what's landed)

| Layer | Key decls (file) |
|---|---|
| Abstract seal | `reachesRigidOrCameron`, `reachesRigidOrCameron_viaHarvest` (`Cascade.lean`) |
| Concrete seal | `SchemeRecovered`, `schemeRecovered_of_visibleRealizers`, `schemeAutGroup_eq_closure_of_recovered`, `reachesRigidOrCameron_viaRecovery` (`Cascade.lean`) |
| Trichotomy / leg C | `exhaustiveObstruction_scheme(_of_nonCascade)(_nonCascade_trichotomy)`, `PrimitiveCCClassification`, `isPreprimitive_of_isPrimitive` (`Scheme.lean`) |
| Leg B core | `smul_eq_on_orbit_of_comm` (L3), `not_comm_of_isPreprimitive_card_lt`, L1/L2 + helpers (`Group.lean`) |
| Cross-branch harvest (recovery ⟹ group) | `closure_eq_stabilizerAt_of_visibleRealizers`, `crossBranchHarvest_reproduces_residual`, `autP_reproduced_of_visibleRealizers`, `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` (`Cascade.lean`) |
| Tower (depths add) | `cascadeComposition`, `cascadeComposition_pathFixing`, `cellsAreOrbits_compose`, `cumulative_card_le`, `LayerStep` (`Cascade.lean`) |
| Recovery witnesses | `RecoverableByDepth`, `recoverableByDepth_pPolynomial` / `_cfi` / `_scheme`, `cellsAreOrbits_of_discrete` (`CascadeOracle.lean`) |
| Block decomposition (conditional) | `reachesRigid_of_blockDecomposition`, `hreach_of_quotientRealizers`, `hfiber_of_fiberRealizers`, **`hfiber_of_fiberVisibleRealizers`**, `blockHarvest_of_realizers`, `blockHarvest_of_visibleRecovery`, `coversOrbits_append`, `CoversOrbitsAlong` (`Cascade.lean`) |
| Blocks / primitivity | `ClosedSubset`, `schemeEquiv(_equivalence)`, `IsPrimitive`, `exists_nontrivial_closedSubset_of_not_isPrimitive`, `schemeEquiv_class_eq_iff`, `BlockRefinementVisible`, `blockRefinementVisible_of_schemePartSeparates`, `cell_splits_of_imprimitive`, `schemeBlock_fiber_transitive`, `schemeBlocks_transitive` (`Scheme.lean`) |
| schemeAdj bridge | `schemeAdj`, `isAut_schemeAdj_iff`, `stabilizerAt_schemeAdj_empty_eq`, `gensAt_empty_eq` (`Cascade.lean`) |

---

## 6. Key conceptual insights (carry these)

1. **Orbit-level coverage is always vacuous; visible (refinement-computable) coverage is the content.** §3. This is
   the single most important re-orientation. Every "recovers/reproduces" predicate must be keyed on visible
   realizers or a polynomial depth bound, and re-checked for non-vacuity by the `gens = ↑group` test.
2. **`s(C)` (separability number) is the right vocabulary** (Evdokimov–Ponomarenko): `s(C) ≤ m ⟺ C determined by
   its m-dim intersection numbers ≈ WL-dimension. Recovery ⟺ low `s(C)`. The leaks are *high-`s(C)`* schemes. **No
   theorem in the corpus bounds `s(C)`** for imprimitive-non-abelian-non-Cameron CCs — that is the formal handle on
   G2.
3. **The imprimitivity recursion is well-founded** (block tower, height ≤ log₂ n, primitive floor) — not infinite
   regress. Discharge the *whole tower at once* via `cascadeComposition` (depths add), not level-by-level.
4. **The discretizing (within-cell) oracle provably cannot harvest a multi-step moved orbit**
   (`lockstep_disc_imp_stab_trivial`, `CascadeOracle.lean`): no iso-invariant ordering of a moved orbit exists. So
   multi-step hidden symmetry (CFI `tw ≥ 2`, leg B) **must** go through the cross-branch / Part-A harvest. Do not
   re-attempt a within-cell discharge for `tw ≥ 2`.
5. **Largeness is the Cameron driver, not non-abelian** (the C₇ trap): `C₇` is primitive, rank-3, *non-abelian*
   (D₇), yet cascades and is small ⟹ not Cameron. Any leg-C statement must key the Cameron branch on
   *largeness/non-cascade*, never *non-abelian* alone.
6. **Two corrections from the deep-research pass** (do not reintroduce): (a) circulant WL-dimension is **unbounded**
   (`≥ c√log n`, Wu–Ren–Ponomarenko 2025); only **prime-power order** is bounded (`≤ 3`, Ponomarenko 2022) — so
   "abelian + vertex-transitive ⟹ bounded WL" is **false** (this is *why* G1b's high-WL circulants exist). (b) The
   leg-C citation is solid only at rank 3/4 (G3).
7. **Per-level orbit-realization is intrinsic** — deep automorphisms fix too much to move shallow orbits, so the
   harvest's shallow-level coverage genuinely needs shallow recovery; the base-sequence freedom buys only the
   *phase-split* (`coversOrbits_append`), not a free shallow win. This is why G1a/G2-A route through the tower.

---

## 7. Dead ends / what NOT to do

- **Do not state a rigid/recovery predicate as `∃ gens, closure gens = group` or via orbit-level coverage** — it is
  vacuous (§3). Always key on visible realizers / a polynomial depth bound, and run the `gens = ↑group` non-vacuity
  test.
- **Do not materialize the quotient/fiber as `AssociationScheme`/`AdjMatrix` on a smaller `Fin m`** — re-indexing +
  re-establishing all 5 scheme axioms is intractable (exhaustive-obstruction §0.7.2 (ii); tier3a-b1-build-plan §4
  Approach A). Stay intrinsic on `Fin n`.
- **Do not pursue unconditional depth-1 block-visibility (A2-iii)** — refuted by Shrikhande. Only the **graded**
  form (A2-ii, `blockRefinementVisible_of_schemePartSeparates`) is available.
- **Do not try to discharge the leaks (G2) by citation** — the deep research established the
  imprimitive/small-primitive non-abelian high-`s(C)` quadrant is genuinely open, not citably impossible.
- **Do not re-attempt a within-cell harvest for multi-step (`tw ≥ 2`) hidden symmetry** — provably futile (insight
  4). Route through the cross-branch / Part-A harvest.
- **Do not build the tower level-by-level** — `cascadeComposition` collapses it (insight 3).
- **Do not reintroduce** "circulants bounded WL (Muzychuk)" or the all-rank Babai dichotomy (insight 6).

---

## 8. Reading order for a fresh reader

1. **This doc** — the goal, the state, the gaps.
2. The gap you are closing (§4), then its machinery in §5 and the relevant insight in §6.
3. The primary docs for context: [`00-START-HERE.md`](./00-START-HERE.md) → [`chain-descent-strategy.md`](./chain-descent-strategy.md)
   → [`chain-descent-declassing.md`](./chain-descent-declassing.md) (recovery + unified harvest) →
   [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) (§0.5 the seal, §0.7 the
   bottom-up derivation + leg-C theory, §0.7.6 the leak/`s(C)` verdict) →
   [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md) (Part A cross-branch harvest).
4. [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) — ground truth for what is proved;
   grep the decl names in §5.
5. [`chain-descent-routeB-handoff.md`](./chain-descent-routeB-handoff.md) — **superseded by this doc**; read only
   for the Route B (G2-A) blow-by-blow and the vacuity-correction note at its top.
