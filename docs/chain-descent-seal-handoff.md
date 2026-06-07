# Chain descent — THE SEAL HANDOFF: current state and the gaps to "consumed-or-Cameron"

> **STATUS (2026-06-07, rev. 2): this is the authoritative handoff for the oracle-capability seal.** It **subsumes**
> [`chain-descent-routeB-handoff.md`](./chain-descent-routeB-handoff.md) (Route B is now one *partial* attack on
> one gap, G2-A below, and its capstones were found vacuous — see §3). Read this doc to pick up *any* of the
> open gaps. The goal is to close all of them, including pushing through the GI-adjacent frontier (G2).
>
> **Rev. 2 (the closure-logic pass) folds in three findings — read §4.0 first.** (a) **No re-keying of the rigid
> predicate closes the seal** — closure is gated on the leaks (G2) under *any* keying (§4.0). (b) The tempting
> `Findable`/`FindableWithin` re-key **conflates leg B into leg A** and is the wrong vehicle for G1b; leg B needs a
> new L3-keyed `AbelianConsumed` (§4 G1b). (c) The leaks have an **anatomy**: non-recovery is *definitionally* a
> 1-WL-invisible real decision, its persistence requires a **linear (abelian) coupling**, and the lone theorem-route
> to closing G2 is the **self-detection lemma** (§4 G2 + §6). The live target is no longer "instantiate the seal at
> a better predicate" — it is the self-detection lemma / G2-B emptiness.
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
self-contained for a fresh reader attacking *that* gap. **Read §4.0 first — it is the through-line.**

### 4.0 — The closure logic: no re-keying closes the seal; the crux is G2

The abstract capstone `reachesRigidOrCameron` (`Cascade.lean`) is parametric in `ReachesRigid` and hard-wired to the
trichotomy `¬IsPrimitive ∨ ¬NonCascade ∨ Cameron`, so it **always** carries the same two branch reductions —
*whatever* `ReachesRigid` is instantiated to:

```
hImprimitive : ¬ IsPrimitive  → ReachesRigid     -- imprimitive ⟹ rigid
hCascade     : ¬ NonCascade   → ReachesRigid     -- small ⟹ rigid
```

So "re-keying the rigid predicate" changes the *target*, not the *count* of obligations. And under **any
non-vacuous** `ReachesRigid`, both reductions are **false on the leaks** (non-recovering ∧ non-Cameron) *by
construction* — "rigid-false" is exactly what "non-recovering" means (§G2 anatomy). Therefore:

> **The seal closes ⟺ both reductions are provable ⟺ the leaks (G2) are empty.** G2-A (imprimitive) reduces to
> G2-B (primitive) via the block tower (≤ log n layers). **G2-B closure = the self-detection lemma (§G2 anatomy).**
> No instantiation of `ReachesRigid` — `SchemeRecovered`, `Findable`, anything — changes this; the work is G2.

What re-keying / leg-B work *does* buy is **closure of slices** (depth-graded leg A captures CFI/Shrikhande; leg B
captures hidden-abelian), which shrinks the wall to exactly G2-B but does not eliminate it. The seal's honest
end-state is a conditional theorem `modulo {G3 cited classification + G2-B}`; the only thing that discharges G2-B is
the self-detection lemma, which is research, not engineering.

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
(established 2026-06-07; the base-sequence recalibration — per-level recovery is intrinsic, §6 insight 7). So a depth-graded `SchemeRecovered`
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

> **⚠️ Do NOT use `Findable`/`FindableWithin` as the leg-B vehicle (rev. 2 finding).** The existing D1/D2 screen
> (`Cascade.lean`, `inductive Findable … | recovered | abelian | step`) looks like the natural object, but it
> **conflates leg B into leg A**: `FindableWithin`'s `abelian` leg carries a `RecoverableByDepth b` field, which is
> `∃ S, S.card ≤ b ∧ CellsAreOrbits S` = **visible (1-WL) recovery** at depth `b` — exactly what genuinely-hidden
> abelian (the point of leg B) *lacks*. At a poly bound it only re-expresses leg A. And bound-free `Findable`'s
> `abelian` constructor concludes from `ResidualAbelian ∧ ¬IsBase` **with no consumption proof** (a soft vacuity:
> "should be consumable" asserted by fiat, not earned). So `AbelianConsumed` must be a *new* predicate keyed on the
> **unique candidate (L3)** + the cross-branch harvest — not `Findable`. Even done right, leg B closes the *abelian
> slice*, not the seal (§4.0).

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

- **G2-B — Leak-B: small, primitive, non-abelian, non-recovering, non-Cameron.** The irreducible core (G2-A bottoms
  out here). The bottom-up route claims *non-consumed ⟹ large* (so this quadrant would be empty), but that rests on
  the largeness argument, which is **tautological** under the orbit-level vacuity (§2 note) — so it does **not** yet
  rule Leak-B out. **Candidate-narrowing (rev. 2):** small ⟹ small base (`b(G) ≤ log₂|G|`, since `|G| = ∏` basic
  orbit sizes `≥ 2^b`); then O'Nan–Scott + poly-order collapses the candidates — most poly-order primitives are
  **2-transitive ⟹ rank-2 ⟹ recover trivially**, leaving essentially **bounded-dimension affine** `V⋊G₀`
  (`F_p^d`, `d=O(1)`) and a few classical subset/flag actions. So G2-B's only live family is bounded-dim affine +
  a handful of classical cases. The full anatomy (why it's open, the affine reduction, the one theorem-route) is
  the **§G2 anatomy** subsection below. Genuinely open.

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

### G2 anatomy — the refinement axis, self-detection, and the affine reduction (the live frontier)

This is where the work now is. Four moves turn "G2 is open" into a single, attackable conjecture.

**(1) Non-recovery is *definitionally* a 1-WL-invisible real decision.** Unfold `¬CellsAreOrbits adj P S`: ∃ `u,v`
in the same `warmRefine` cell with `¬OrbitPartition adj P S u v` — same 1-WL colour, **no** residual automorphism
`u↦v`. That is exactly a **genuine (real) decision the refinement cannot see**. So the refinement axis is high ⟺ a
hidden real decision exists — i.e. it is an **asymmetry** quantity, not a property of the symmetric group. ("The
only thing that raises the refinement axis is an asymmetry"; abelian symmetry enters only in (3).)

**(2) The contributor decomposition routes two of three to handlers.** A residual's non-recovery is attributable
to: (a) **real decisions (asymmetry)** — *proven extractable to the IR-core*: `real_stays_real` (a genuine decision
stays genuine, never consumed by symmetry) + the support induction `exists_isBase_saturated` (the descent
individualizes the residual support to a base) + `recoverableAt_base_iff_discrete` (at the base, non-discrete =
IR-core, residual-trivial). So asymmetry separates out, residual-trivial, flagged as IR-core. (b) **abelian
symmetry** — consumed by **leg B** (L1–L3, closeable). (c) **non-abelian symmetry** — the residual claim **A4: it
contributes *nothing* to the hidden-real-decision count** (recovers). A4 is G2-B restated. The decomposition is a
clean *separation* only when the structure decomposes (imprimitive = the block tower, G2-A); at the **primitive
floor** (G2-B) asymmetry and symmetry are potentially **entangled** — which is precisely why G2-B, not G2-A, is the
irreducible core.

**(3) Persistence requires a *linear* coupling — one mechanism, two faces.** A hidden real decision cannot persist
in isolation (1-WL would count a local difference and resolve it). To stay invisible across individualizations it
must be **coupled to a set of further decisions** (your "external decisions") whose *joint* configuration is
**homogeneous** — every parity assignment yields the same local intersection-number profile. The only couplings
with that property are **linear (F_p/F₂) codes** (equivalently, a **character/eigenvalue degeneracy** of the
scheme). Live-symmetric linear coupling = **CFI** (leg B); rigidified (full-rank) linear coupling = **multipede**
(IR-core). This is the unification of "abelian symmetry **or** asymmetry" — both are faces of the *linear-coupling
requirement*. It matches the literature exactly: [Lichter–Rassmann–Schweitzer (arXiv:2402.11531)](https://arxiv.org/abs/2402.11531)
state that **all known high-WL constructions are CFI/multipede = abelian-color-class**, and the abelian-color case
is **polynomial-time** — i.e. no non-linear high-WL construction is known.

**(4) The self-detection lemma = the lone theorem-route to closing G2** (your (2), made precise):

> **Self-detection (conjecture, with mechanism):** a persistent hidden real decision requires a linear /
> character-degenerate (abelian) coupling. A **non-abelian** coupling produces **asymmetric intersection numbers**,
> which 1-WL reads off and *resolves* the decision. Hence non-abelian symmetric structure cannot host a persistent
> hidden decision (closes A4 ⟹ closes G2-B ⟹ closes the seal, modulo G3).

Why this is *attackable* (unlike "characterize WL-hardness"): it is a statement about **intersection numbers of a
coherent configuration** — the exact objects `Scheme.lean` already models, and the same counting the
`isolationStep`/`EdgeGenerates` engine runs. The concrete proof route your "external decisions" framing predicts: the
support of a hiding coupling is itself a 1-WL-countable quantity **unless linear**, so the lemma may fall to
*"a non-abelian coupling leaves a parity-asymmetric intersection-number count."* That would be a project-internal
theorem, not a citation of the open WL-characterization.

**The affine reduction (the sharpest concrete test).** The bounded-dim affine family `V⋊G₀` is where (3)'s two
forces collide inside one group: `V` (translations, regular abelian — the *linear* part that could host a
degeneracy) vs `G₀` (non-abelian — predicted to forbid it). Findings:
- **The entanglement is genuine — affine is NOT leg B.** A decision `α↦β` has exactly `|G₀|` candidates
  (`(β−h(α), h)` for each `h∈G₀`); distinct candidates *disagree on the orbit* (`β + h₁(γ−α)` vs `β + h₂(γ−α)`), so
  `not_comm_of_orbit_disagree` fires — the residual is non-abelian and leg B does not consume it. The unique
  translation `t=β−α` is canonical *within* `V`, but the descent sees the full `V⋊G₀`.
- **But it is *tame*** — `V` regular normal abelian ⟹ the orbital scheme is a **translation scheme (Schur ring over
  `F_p^d`)**. So affine-G2-B lands in **Schur-ring separability theory** (Evdokimov–Ponomarenko), not a wild regime:
  > **affine-G2-B recovers ⟺ the schurian Schur ring of `G₀` over `F_p^d` is separable** (low `s(C)`).
- **Predicted verdict: recovers (no leak).** Self-detection + bounded `d` ⟹ only `O(1)` linear room for a character
  degeneracy ⟹ separable — mirroring Ponomarenko's prime-power circulant bound (`WL-dim ≤ 3`) and the
  Wu–Ren–Ponomarenko picture (high WL-dim needs *many* independent directions ↔ large `d`). **Honest gap:** schurity
  and separability are *independent* (Evdokimov–Ponomarenko), so a schurian non-separable S-ring over bounded `F_p^d`
  is exactly what a counterexample would be — whether it exists is the S-ring research frontier.

**The two next moves (theory + experiment).**
1. **Theory (the prize):** prove the self-detection lemma for translation/schurian schemes via the counting route —
   *does a non-abelian coupling provably leave an asymmetric intersection-number count?* Project-internal; closes A4.
2. **Experiment (decisive for affine, cheap):** enumerate non-abelian irreducible `G₀ ≤ GL(d,p)` for small
   `d∈{2,3}`, small `p`; build the orbital scheme; measure WL-dimension / recovery depth. **RAN 2026-06-07 (partial)
   — see the G2 attack board below; the affine floor came back *tame but mild*.**

### G2 attack board — probe results, the corrected target, the conservation route, and the threads

This subsection consolidates the work (2026-06-07) that turned the §G2-anatomy conjecture into a concrete program
with a result, a corrected theorem target, and a prioritized thread list. **It is the live to-do.**

**The affine probe RAN — affine floor is tame, but the result is *mild*.** `GraphCanonizationProject.Tests/AffineSchemeProbe.cs`
(two `[Fact]`s: a general `d≤5` enumeration + `Probe_CyclotomicFamily_Index3`) built translation schemes `V⋊G₀` over
`F₂^d` (relations = `G₀`-orbits, intersection numbers, primitivity = `G₀` irreducible, recovery = the `EdgeGenerates`
closure + greedy individualization depth). Results:
- The predicted danger zone — index-3 Singer/cyclotomic schemes (Clebsch family: `Z₅⊂GL(4,2)`, `Z₂₁⊂GL(6,2)`,
  `Z₈₅⊂GL(8,2)`; three equal-valency relations `(2^d−1)/3`) — is primitive, non-abelian-residual, and **fails depth-1
  recovery**: the equal-valency relations are interchangeable by an algebraic automorphism = the separability gap
  `Ĝ⊋G` made concrete (an `S₃`-on-relations the group only partly realizes). **But recovery depth is bounded and flat:
  4, 3, 3 across `|V| = 16, 64, 256`** (≈ base 2 + bounded stickiness, decreasing not growing) ⟹ leg-A depth-graded =
  consumed, **not** a counterexample.
- Across the enumeration this family's `d=4` member was the *only* primitive depth-1-non-recoverer; **all other
  primitives recovered at depth 1, and every persistent (high-rank) deadlock had reducible `G₀` (imprimitive)** — direct
  empirical support for "primitive ⟺ recovers" and P3 (deadlock ⟹ imprimitive).
- **CAVEAT (load-bearing):** the cyclotomic `G₀` are **cyclic (abelian)** Singer subgroups, so the gap is the
  **Galois/cyclotomy** gap — bounded by `d`, abelian-flavored. The probe strongly confirms the *expected easy case*
  (bounded-`d` abelian-multiplicative gaps are tame); the genuinely-**non-abelian-`G₀`** affine case (where the
  self-detection mechanism actually fires) and the non-affine types are **undertested** (~9 primitives; greedy depth is
  an upper-bound proxy). "Held but mild."

**The corrected target (forced by the probe).** Depth-1 `EdgeGenerates` is the *wrong* predicate — cyclotomic fails it
yet recovers. The target must be **bounded-depth recovery**: **primitive schurian ⟹ recovers at depth ≤ base + O(1)**
(`RecoverableByDepth`-shaped, not per-level). This **unifies the self-detection lemma with G1a** for the primitive floor
— the same statement.

**The clean theorem + piece decomposition.** The counting route's target is **determinacy**, not asymmetry:
non-recovery ⟺ the structure constants fail to determine the scheme = **non-separable** (high `s(C)`). Literature pins
it: **separable ⟹ WL-dim ≤ 2 (recovers)** ([1903.00409](https://arxiv.org/pdf/1903.00409)); **non-separability of
schurian S-rings = generalized-wreath = imprimitive** ([1709.03937](https://arxiv.org/pdf/1709.03937)); the *only*
bounded-rank elementary-abelian exceptions are **E₁₆=F₂⁴, E₃₂=F₂⁵** (concrete, 16/32 points). So the clean target is
**primitive schurian ⟹ separable ⟹ `EdgeGenerates` ⟹ recovers**, which **collapses all leaks onto G2-A (the block
tower)** plus a primitive floor that recovers. Pieces (mapped to `Scheme.lean`):

| P | Statement | Status |
|---|---|---|
| **P1** | separable ⟺ `EdgeGenerates`/recovery | provable; engine landed (`theorem_2_HOR_of_edgeGenerates`) |
| **P2** | ¬recovery ⟹ a proper WL-stable fusion `W` (isolation deadlock) | provable (`isolationStep` saturates below `EdgeGenerates`) |
| **P3** | the deadlock fusion `W` is a `ClosedSubset` (block) ⟹ imprimitive | **CRUX = the project's Gate-G**, now with wreath-literature support + a finite test |
| **P4** | primitive ⟹ no deadlock ⟹ recovers | follows P2+P3 |

**P3 is Gate-G.** The counting route reaches the project's existing Gate-G (exhaustive-obstruction §0.7.2) from the
structure-constant side, now backed by the wreath literature and a concrete falsification (E₁₆/E₃₂).

**The C₇ correction (do NOT reintroduce the naive counting route).** "non-abelian ⟹ asymmetric intersection-number
count" is **false**: a *symmetric* scheme has a **commutative** Bose–Mesner algebra (`p^k_{ij}=p^k_{ji}`) regardless of
the group — C₇'s scheme is symmetric/commutative though `D₇` is non-abelian, and it recovers via its *metric* structure.
So the counting route cannot key on algebra non-commutativity; the asymmetry (when present) is a *specific* count whose
form varies (metric for C₇), and exhibiting it is the genuine work. Content = determinacy/separability, not commutativity.

**Thread T2 — linear-coupling = block-system (the main provable thread).** A persistent (growing-depth) gap requires an
**F₂-linear coupling** = a `G₀`-invariant subspace `W ⊆ V` = a **block system** ⟹ **imprimitive**. **Primitive (`G₀`
irreducible) forbids it.** The cyclotomic case is the proof-of-concept: `Z₅` acts *irreducibly* on `F₂⁴`, so its only gap
is the *bounded* Galois one (depth 4). This may be a **near-theorem for the affine case via the wreath literature**: if
"non-separable schurian S-ring ⟹ proper `G₀`-invariant section," then `G₀` irreducible ⟹ separable ⟹ recovers.
**Dependency to verify:** is the wreath characterization clean at the needed generality (not just order-4p/odd/p-group)?
T2 generalizes off the affine case to *exactly* P3.

**The conservation route — the user's accounting instinct, made precise (the most promising attack).** A four-term
conservation governs recovery depth:

> `recovery depth  =  base(G)  +  log-scale(separability gap Ĝ/G)  +  IR-core(true decisions)`

with the three sources **separately budgeted** — none can masquerade as another. Three terms are landed: the vertex
partition `n = free + true + moved`; `|Aut| = ∏ basic-orbit sizes` (`card_autP_eq_prod_of_base`), base `≤ log₂|Aut|`
(`exists_isBase_saturated_support`); and `real_stays_real` (true decisions persist, never consumed by symmetry, extract
to the IR-core). The **stickiness** is the *fourth* term — the gap `Ĝ/G` between the symmetry that exists (`G`) and the
one 1-WL hallucinates (`Ĝ` = WL-closure automorphism group); the cyclotomic `S₃`-on-relations *is* this `Ĝ/G`.

The engine ("hiding requires external decisions"): to stay concealed through `k` individualizations a symmetry needs `k`
**independent** hidden generators, and **independence forces them toward commuting (abelian)** — CFI confirms it (its
`β`-dim concealment IS the abelian gauge `Z₂^β`). So **the concealable part of any symmetry is an abelian section (→ leg
B); the non-abelian part has no stackable concealment (→ leg A recovers it); the unstackable residue is asymmetric (→
IR-core).** That is A4.

**Why this is the payoff: the crux becomes the landed leg-B core, not the open WL-characterization.** "Concealment ⟹
abelian" has its *group side already proved* — `not_comm_of_orbit_disagree` (non-abelian ⟹ candidates disagree on the
orbit). The missing half is the **counting realization**: *candidate-disagreement ⟹ a 1-WL-visible intersection-number
asymmetry*. Two faces, both on landed machinery: **(group)** independently-stackable hidden generators commute;
**(counting)** disagreement leaves an asymmetric count (subject to the C₇ caution — not algebra-commutativity).
**Concrete first lemma (the two-vantage step):** take `s = g⁻¹h ∈ Stab(e)` (a non-trivial stabilizer element from a
non-abelian decision) and prove that `s` having non-trivial support forces an **asymmetric suborbit count from a second
base point** — the precise "a second vantage detects the disagreement" the cyclotomic `base+2` data hints at.

**THE THREAD BOARD (what's worth doing, by tier — regardless of immediacy).**
- **Tier 1 — bankable slice-closures (provable now, shrink the wall but don't close it):**
  - **(a) G1b — leg B** via a new L3-keyed `AbelianConsumed` (NOT `Findable`; §4 G1b). Closes the abelian wall-slice,
    citation-free. Most actionable. The conservation route now shows the abelian-concealable part *is* leg B.
  - **(b) G1a — depth-graded recovery** (`RecoverableByDepth` at base+O(1)). Captures CFI/Shrikhande; now the *same*
    target as the primitive-floor self-detection.
- **Tier 2 — the G2 attack (the only route that actually closes the seal):**
  - **(c) The conservation route** — prove "concealment is abelian" via the counting realization of
    `not_comm_of_orbit_disagree`; **first lemma = the two-vantage step** (above). Project-internal, on landed L3.
  - **(d) Thread T2** — primitive ⟹ separable via linear-coupling = block; **verify the wreath-characterization
    literature dependency** (could make affine-primitive ⟹ separable a near-theorem by citation).
  - **(e) The P1–P4 / Gate-G proof** of "primitive ⟹ separable" (P3 = the crux).
- **Tier 3 — decisive cheap experiments:**
  - **(f) The E₁₆/E₃₂ test** — are the non-separable schurian S-rings over `F₂⁴/F₂⁵` **imprimitive** (supports
    primitive⟹separable / P3) or **primitive + non-abelian** (a 16/32-vertex G2-B counterexample)? The sharpest
    falsification; small and decisive.
  - **(g) Extend `AffineSchemeProbe.cs`** to **non-abelian irreducible `G₀`** (the actual A4 mechanism, not the Galois
    gap) and higher `d` — the undertested zone (the existing probe is abelian-`G₀`/Galois only).
- **Tier 4 — doc-sync / record-keeping (the NoFusion over-claim):**
  - **(h)** The NoFusion/largeness-derivation track is **undercut by the orbit-level vacuity** (§3): `largenessBridge_viaHarvest`
    is *tautological* (the §2 note says so), but the `PublicTheoremIndex` descriptions of the `NoFusion` family and
    [exhaustive-obstruction §0.7.5](./chain-descent-exhaustive-obstruction.md) still claim "largeness derived from the
    harvest." The Lean is sound; the *prose over-claims*. Reconcile so future readers don't treat NoFusion as live
    evidence that G2-B is closeable (it isn't — that route is vacuous, confirming G2-B's open status).

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
8. **No re-keying closes the seal** (§4.0). The abstract capstone carries both branch reductions for *any*
   `ReachesRigid`; under any non-vacuous keying they are false on the leaks. Closure ⟺ leaks empty ⟺ self-detection
   lemma. Stop hunting for a better rigid predicate; the work is G2.
9. **Non-recovery is, definitionally, a 1-WL-invisible real decision** (`¬CellsAreOrbits` = a same-cell different-orbit
   pair). The refinement axis is an **asymmetry** quantity; abelian symmetry enters only as the **linear coupling**
   that lets an asymmetry *persist*. CFI (live) and multipede (rigidified) are the two faces of one linear-coupling
   mechanism — matching [Lichter et al. 2402.11531](https://arxiv.org/abs/2402.11531) (all known high-WL = CFI/multipede
   = abelian-color).
10. **The self-detection lemma is the lone theorem-route to G2** (§G2 anatomy): a persistent hidden decision needs a
    linear/character-degenerate coupling; a non-abelian coupling leaves *asymmetric intersection numbers* that 1-WL
    resolves. Attackable by intersection-number counting (project-internal), unlike the open WL-characterization.
    **affine-G2-B ⟺ separability of schurian Schur rings over bounded `F_p^d`** (predicted separable; the decisive
    cheap experiment is enumerating `G₀ ≤ GL(d,p)`).

---

## 7. Dead ends / what NOT to do

- **Do not state a rigid/recovery predicate as `∃ gens, closure gens = group` or via orbit-level coverage** — it is
  vacuous (§3). Always key on visible realizers / a polynomial depth bound, and run the `gens = ↑group` non-vacuity
  test.
- **Do not expect re-keying the rigid predicate to close the seal** (§4.0) — the two branch reductions are carried
  regardless of keying and are false on the leaks; closure ⟺ G2 empty. In particular **do not use
  `Findable`/`FindableWithin` as the leg-B vehicle** — its `abelian` leg requires `RecoverableByDepth` (visible
  recovery), conflating leg B into leg A; build a new L3-keyed `AbelianConsumed` instead (§4 G1b).
- **Do not materialize the quotient/fiber as `AssociationScheme`/`AdjMatrix` on a smaller `Fin m`** — re-indexing +
  re-establishing all 5 scheme axioms is intractable (exhaustive-obstruction §0.7.2 (ii); tier3a-b1-build-plan §4
  Approach A). Stay intrinsic on `Fin n`.
- **Do not pursue unconditional depth-1 block-visibility (A2-iii)** — refuted by Shrikhande. Only the **graded**
  form (A2-ii, `blockRefinementVisible_of_schemePartSeparates`) is available.
- **Do not try to discharge the leaks (G2) by citation** — the deep research established the
  imprimitive/small-primitive non-abelian high-`s(C)` quadrant is genuinely open, not citably impossible.
- **Do not key the counting route on algebra non-commutativity** ("non-abelian group ⟹ asymmetric intersection
  numbers") — false: symmetric schemes have *commutative* Bose–Mesner algebras regardless of the group (C₇/D₇ recovers
  via metric structure, not commutativity). The counting content is **determinacy/separability**, not commutativity
  (G2 attack board, "C₇ correction").
- **Do not use depth-1 `EdgeGenerates` as the recovery predicate** — the cyclotomic family fails it yet recovers; the
  target is **bounded-depth recovery** (base + O(1) / `RecoverableByDepth`), which also unifies with G1a.
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
