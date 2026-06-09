# Chain descent — THE SEAL HANDOFF: current state and the gaps to "consumed-or-Cameron"

> **STATUS (2026-06-07, rev. 3): this is the authoritative handoff for the oracle-capability seal.** It **subsumes**
> [`chain-descent-routeB-handoff.md`](./chain-descent-routeB-handoff.md) (Route B is now one *partial* attack on
> one gap, G2-A below, and its capstones were found vacuous — see §3). Read this doc to pick up *any* of the
> open gaps. The goal is to close all of them, including pushing through the GI-adjacent frontier (G2).
>
> **Rev. 3 (the separability deep-research pass, 2026-06-07) RESOLVES the crux-direction question.** A focused
> literature pass (99 agents, 24/25 claims confirmed under 3-vote adversarial verification, all primary sources;
> full record in [exhaustive-obstruction §0.7.6](./chain-descent-exhaustive-obstruction.md), and the §G2 attack
> board below) settles the "is the crux backwards?" caution that headed §G2 in rev. 2:
> - **The "imprimitive ⟹ recovers" reorientation is REFUTED.** Evdokimov–Ponomarenko's `s(C) ≤ 2` covers **only
>   imprimitive *3/2-homogeneous* schemes** (a narrow proper subclass), NOT all imprimitive homogeneous schemes.
>   General imprimitive homogeneous *schurian* schemes reach **unbounded** `s(C)` (circulants, WL-dim `≥ c√log n`,
>   Wu–Ren–Ponomarenko 2025). So §0.7.6 stands: imprimitive is **not** citably-recoverable.
> - **The high-`s(C)` region splits three ways** (the refined map): **abelian** — all known unbounded-WL examples
>   (circulants) live here → **leg B / G1b, citation-free**; **non-abelian primitive** → **G2-B, genuinely open, no
>   known witness, no citable bound**; **non-abelian imprimitive** → reduces via the block tower → G2-B; **rigid**
>   (multipede — high `s(C)` with *trivial* Aut) → IR-core, outside the seal.
> - **There is no citation for the self-detection target.** The Babai/Sun–Wilmes/Kivva structure theory bounds
>   `|Aut|` and *minimal degree*, **not** `s(C)` (RQ3); "non-abelian coupling ⟹ bounded WL-dim" is an empirical
>   "almost all known" hedge, **not a theorem** (RQ5). So G2-B is **project-internal-or-carried**, never cite.
>
> The net: after G1b removes the abelian slice (where *every known* high-`s(C)` example sits), the entire residual
> leak funnels to **G2-B (primitive non-abelian high-`s(C)`)** — open, witnessless, uncitable. The seal's honest
> end-state is a conditional theorem `modulo {G3 cited classification + G2-B}`.
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
>
> **⟶ For the G2-B / `hCascade` gap specifically (the sole irreducible open input), the live working doc is
> [`chain-descent-self-detection-plan.md`](./chain-descent-self-detection-plan.md):** Phase 1 is DONE — the seal is
> reduced (axiom-clean, landed) to the **single semantic proposition `SelfDetectsStably`** (`reachesRigidOrCameron_viaStableRecovery`,
> `Cascade.lean`): *primitive small ⟹ cells = orbits above a bounded base set*. The M2 reduction further reduces this
> to **"primitive small ⟹ bounded individualization discretizes"** (`selfDetectsStably_of_discretizes`, landed), and
> the depth-1 (`s(C)=1`) slice is closed (`reachesRigidOrCameron_viaDepthOneSeparable`). Its **§11 ("PICK UP HERE")**
> is the current implementation plan for the open `s(C)≥2` content: the route-scan verdict (affine-cyclic beachhead),
> the conceptual frame (the work is *1-WL over a bounded base*, NOT a k-WL climb), and the cyclotomic bound proof +
> wiring. (§9 is the earlier affine M0–M3 build plan; §10 the M1.1/M1.2 + gotchas handoff.) Read §11 for any G2-B
> work; the board below (§G2 anatomy / attack board) is the theory it formalizes.

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

**The abstract capstone (genuine):** `reachesRigidOrCameron` (`Cascade.lean`) — parametric in an abstract
`ReachesRigid : ∀ m, SchurianScheme m → Prop` and the `NonCascade`/`LargenessBridge` interface; it *reduces*
`ReachesRigid ∨ IsCameronScheme` to two branch hypotheses + the classification. Its content depends entirely on
what `ReachesRigid` is instantiated to. (The old `reachesRigidOrCameron_viaHarvest` headline was **excised**
2026-06-07 — see Tier-4 (h′) — along with the whole vacuous `NoFusion`/`largenessBridge_viaHarvest` family.)

**The concrete headline:** `reachesRigidOrCameron_viaRecovery : SchemeRecovered n S ∨ IsCameronScheme n S`
(`Cascade.lean`), with `ReachesRigid := SchemeRecovered`. It reduces the goal to three carried inputs:

| Input | What it is | Status |
|---|---|---|
| `hClassify : PrimitiveCCClassification …` | cited Babai 1981 / Sun–Wilmes 2015: primitive, large, rank ≥ 3 ⟹ Cameron | cited; solid rank 3/4 (G3) |
| `hCascadeHarvest : ¬ IsLargeSchemeViaAut IsLarge n S → SchemeRecovered n S` | **"small ⟹ recovered"** (see note) | carried (G1, G2) |
| `hImprimRecovery : ¬ S.…IsPrimitive → SchemeRecovered n S` | **"imprimitive ⟹ recovered"** | carried (G1, G2) |

**Note — what `NonCascade` actually is (post-excision).** The concrete capstones now instantiate the abstract
`NonCascade` directly at `IsLargeSchemeViaAut IsLarge n S = IsLarge (Nat.card SchemeAutGroup)` = "the group is
large," with the `LargenessBridge` supplied as the **identity** (`fun _ _ h => h`) — largeness honestly *carried*,
not derived. So `¬NonCascade` = "small," transparently. The trichotomy
`exhaustiveObstruction_scheme_nonCascade_trichotomy : ¬IsPrimitive ∨ ¬NonCascade ∨ Cameron` (`Scheme.lean`,
parametric in `NonCascade`/`hbridge`) is genuine — `primitive ∧ large ∧ rank≥3 ⟹ Cameron` (the classification)
cased out. (Previously `NonCascade := NonCascadeViaHarvest` carried a `NoFusion` clause whose orbit-level coverage
was vacuous, §3, making the largeness "derivation" tautological; that whole family is now removed.) The genuine
"¬consumed ⟹ large" stays open (part of G2).

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

**Update (2026-06-08) — the imprimitive input is now folded.** The Tier-1 slices (G1b leg B, G1a depth-graded) and the
scheme-seal wiring have landed (see §4 G1b / G1a / G2-A). The current headline is
`reachesRigidOrCameron_viaBlockRecovery : (SchemeBlockRecovered ∨ AbelianConsumed) ∨ IsCameronScheme` — the imprimitive
branch (`hImprim`) no longer carries an opaque "imprimitive ⟹ recovered"; its target is `SchemeBlockRecovered`, *earned*
from the fully-visible block decomposition. The **sole irreducible carried input** is now `hCascade` (small-primitive =
**G2-B**) + the cited classification (G3): the honest conditional seal `modulo {G3 + G2-B}`. The three-input table below
is the *historical* `…_viaRecovery` decomposition; the live form has `hImprimitive` reduced to block recovery.

**Update (2026-06-08) — THE FUSED SEAL is the single headline.** `reachesRigidOrCameron_viaFusedSeal` (`Cascade.lean`,
axiom-clean) fuses the two partial capstones into one statement:
`((SchemeBlockRecovered ∨ AbelianConsumed) ∨ SchemeRecoveredByDepth bound) ∨ IsCameronScheme`. Each non-Cameron branch is
discharged through its *strongest* form — the **primitive floor (cascade branch) is reduced to the SEMANTIC crux
`SelfDetectsStably`** (via `selfDetectsAtDepth_of_selfDetectsStably`; `viaBlockRecovery` had keyed it on block-recovery,
not self-detection), while the imprimitive branch stays on the earned `SchemeBlockRecovered ∨ AbelianConsumed`. It carries
exactly two inputs — `hSelfDetect` (the G2-B crux) + `hImprim` (landed/earned, tower-reducible to the same floor) — plus
cited G3, and subsumes both `reachesRigidOrCameron_viaStableRecovery` and `reachesRigidOrCameron_viaBlockRecovery`. This is
the conditional seal `modulo {G3 + self-detection}` as ONE object; the entire open content is the single semantic
proposition `SelfDetectsStably` (= G2-B), which Phase 2 (the affine-cyclic bound proof, self-detection-plan §11) attacks.

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

### G1a — depth-graded recovery (`SchemeRecovered` was depth-1-only) — LANDED (leg A scope)

**LANDED (2026-06-07, axiom-clean `[propext, Classical.choice, Quot.sound]`, `Cascade.lean`).** The depth-graded
model is built, via the **base-sequence phase split** (`coversOrbits_append`):
- **`SchemeRecoveredByDepth n S bound`** — splits the base sequence into a **bounded shallow phase** `∅ → S₀`
  (`|S₀| ≤ bound`, `CoversOrbitsAlong` orbit-coverage — the *carried localisation*) and a **deep phase** from `S₀`
  (visible realizers, satisfiable only where cells = orbits from `S₀` — the genuine recovery). Captures CFI (`tw`),
  Shrikhande (2), which `SchemeRecovered` (`∀ T ⊇ ∅`) could not.
- **`schemeAutGroup_eq_closure_of_recoveredByDepth`** — reproduces the **full root group** `SchemeAutGroup S`:
  deep `coversOrbits_of_visibleRealizers` + `coversOrbits_append` (glue shallow) + `closure_eq_stabilizerAt_empty_…`.
  The shallow ∅→S₀ coverage is the only carried input.
- **`schemeRecoveredByDepth_of_schemeRecovered`** — `SchemeRecovered → SchemeRecoveredByDepth … 0` (empty shallow
  phase): the depth-graded predicate **strictly generalizes** the per-level one.
- **`reachesRigidOrCameron_viaDepthRecovery`** — the depth-graded seal capstone
  `SchemeRecoveredByDepth … bound ∨ IsCameronScheme`, subsuming `reachesRigidOrCameron_viaRecovery`.

**Honest scope (what stays carried).** The split *localizes* but does not eliminate the localisation gap (insight 7):
the **shallow ∅→S₀ phase** is `CoversOrbitsAlong` orbit-coverage = the substrate-conditional content (shallow
orbit-realization is intrinsic — deep recovery does not supply it for free). The **bound** is the non-vacuity hinge:
unbounded ⟹ vacuous (`recoverableByDepth_univ`), so this is partly modelling (captures CFI/Shrikhande), partly the
polynomiality boundary (the bound = T-C).

**Shallow-phase discharge — IMPRIMITIVE case LANDED (2026-06-08).** When the structure is imprimitive, the shallow
phase factors through blocks: it is the **quotient** (block-representative) coverage `hreach`, and the deep phase the
**fiber**. Both are now supplied from **visible (refinement-computable) realizers** — `hreach_of_quotientVisibleRealizers`
(quotient/shallow, the named G2-A "next step") + `hfiber_of_fiberVisibleRealizers` (fiber/deep) — combined by
`reachesRigid_of_blockVisibleDecomposition` into a fully-visible, non-vacuous imprimitive recovery (see §4 G2-A). So
the shallow phase is discharged for imprimitive schemes from visible block recovery; the residual carried unit is the
block action's own recovery (block-level WL-dimension), localized to the smaller constituents. The **primitive** case
(no blocks) is the remaining frontier — there the shallow transversals are intrinsically refinement-invisible and
supplied only by the cross-branch leaf-collision harvest whose polynomial completeness is T-C (the genuine
localisation, GI-adjacent, out of scope).

**The problem (original).** `SchemeRecovered` demands visible realizers at **every** level (`∀ T`). That is *per-level*
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

### G1b — leg B (hidden abelian) — LANDED (was "the most actionable gap")

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

**LANDED (2026-06-07, axiom-clean `[propext, Classical.choice, Quot.sound]`, `Cascade.lean`).** The leg-B core is
in the seal:
- **`AbelianConsumed n S`** — the non-vacuous certificate: `¬ IsBase` (non-trivial root residual) ∧ *every decision
  is uniquely determined on its cell* (any two auts sending `a↦b` agree on `a`'s whole orbit). The determinacy is
  keyed via L3, **not** orbit-level coverage — it is genuinely *false* for a non-abelian residual with disagreeing
  candidates (`not_comm_of_orbit_disagree`), so it passes the §3 non-vacuity test (no `∃ gens`; a real restriction).
- **`abelianConsumed_of_residualAbelian`** — `ResidualAbelian (schemeAdj S) unknown ∅ ∧ ¬IsBase ⟹ AbelianConsumed`,
  **earned** via `aut_agree_on_orbit_of_comm` (L3), citation-free. This is the consumption *proof* the fiat
  `Findable.abelian` lacked.
- **`reachesRigidOrCameron_viaRecoveryOrAbelian`** — the widened capstone
  `(SchemeRecovered ∨ AbelianConsumed) ∨ IsCameronScheme`. Each non-Cameron branch now discharges via **either**
  visible recovery (leg A) **or** `ResidualAbelian ∧ ¬IsBase` (leg B): strictly weaker branch hypotheses, so an
  abelian-but-not-visibly-recovering residual (high-WL circulant, CFI `tw≥2`) is now placeable where
  `reachesRigidOrCameron_viaRecovery` failed. This closes the abelian wall-slice, citation-free.

**Scope note (honest boundary).** `AbelianConsumed` is the leg-B *symmetry-completeness* certificate (the unique
candidate is determined). The *polynomiality* of reading it — for multi-step abelian (`tw ≥ 2`) via the Part-A
cross-branch harvest at recovery depth, per the discretizing-oracle limit (§6) — is the orthogonal layer, not in this
predicate (mirroring recovery's correctness-vs-polynomiality split). The residual open content is unchanged: the seal
still cannot place a *non-abelian* non-recovering non-Cameron residual (the `s(C)` leak G2-B).

**Original task (for reference).** Define an `AbelianConsumed` (leg-B) predicate keyed via L3 so it is *not*
orbit-level-vacuous (the uniqueness is the content), then widen the rigid side to
`(SchemeRecovered ∨ AbelianConsumed) ∨ IsCameronScheme`, routing the abelian branch to leg B — done as above.

> **CAUTION — Do NOT use `Findable`/`FindableWithin` as the leg-B vehicle (rev. 2 finding).** The existing D1/D2 screen
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
  §11.1`); the phase-split `coversOrbits_append` / `CoversOrbitsAlong`. **Quotient half LANDED (2026-06-08, the
  shallow-phase discharge, imprimitive case):** `hreach_of_quotientVisibleRealizers` supplies `hreach` from a
  **visible block-move** hypothesis (`warmRefine{T} b = warmRefine{T} w → ∃ σ ∈ gens, ResidualAut T σ ∧ β(σb)=βw`)
  — the quotient analogue of the fiber half, completing refinement-computable supply for **both** halves.
  `reachesRigid_of_blockVisibleDecomposition` then reproduces `closure (gensAt … S) = StabilizerAt adj P S` from a
  **fully visible, non-vacuous** block decomposition (no sub-scheme materialized). Non-vacuity: same-block cell
  pairs are free (`σ=id`), the content is *cross-block* same-cell pairs = recovery of the **block action**. So the
  shallow phase (quotient/block-rep coverage) is discharged from visible block recovery, matching `SchemeRecovered`'s
  non-vacuity. The residual carried content is now just the two visible hypotheses `hqvis`/`hfvis` — whether the
  quotient + fiber **recover** (their block-level / within-block WL-dimension) — localized to the two smaller
  constituents (transitive/schurian by §11.1). (The full-`warmRefine`-cell form is a sound over-approximation of the
  genuine coarser `blockCell` block-1-WL; the block-cell form is a further refinement, not needed for the discharge.)
  Earlier finding (2026-06-07): block-visibility (`cells ⊆ blocks`) supports the fiber, not block-moves — which is
  why the quotient needed its own visible supplier, now landed.

  **SCHEME-SEAL WIRING LANDED (2026-06-08) — `hImprim` folded into the visible block decomposition.** The imprimitive
  branch is no longer an opaque carried hypothesis. `SchemeBlockRecovered` (`Cascade.lean`) packages the block-visible
  recovery (a `ClosedSubset I` block system `β_I v := {y | schemeEquiv I v y}` + the visible quotient/fiber coverage);
  `schemeAutGroup_eq_closure_of_blockRecovered` *earns* `closure gens = SchemeAutGroup` from it (via
  `reachesRigid_of_blockVisibleDecomposition` + the `schemeAdj` bridge); and `reachesRigidOrCameron_viaBlockRecovery`
  is the seal with rigid side `(SchemeBlockRecovered ∨ AbelianConsumed) ∨ Cameron`, the imprimitive branch concluding in
  `SchemeBlockRecovered` (block recovery), not opaque. **Non-vacuity is genuine:** keying `β` on a `ClosedSubset` forces
  a *primitive* scheme to trivial `β` ({0}⟹singletons⟹quotient=full recovery; univ⟹one block⟹fiber=full recovery), so
  it collapses to full recovery there — **false on the G2-B leak**, not vacuously true. It subsumes leg A
  (`SchemeRecovered`) as the `I={0}` case. **Net: the sole irreducible carried content is now `hCascade` = the
  small-primitive branch = G2-B**, plus the cited classification (G3) — the honest conditional seal `modulo {G3 + G2-B}`.

- **G2-B — Leak-B: small, primitive, non-abelian, non-recovering, non-Cameron.** The irreducible core (G2-A bottoms
  out here). The bottom-up route claims *non-consumed ⟹ large* (so this quadrant would be empty), but that rests on
  the largeness argument, which is **tautological** under the orbit-level vacuity (§2 note) — so it does **not** yet
  rule Leak-B out. **Candidate-narrowing (rev. 2):** small ⟹ small base (`b(G) ≤ log₂|G|`, since `|G| = ∏` basic
  orbit sizes `≥ 2^b`); then O'Nan–Scott + poly-order collapses the candidates — most poly-order primitives are
  **2-transitive ⟹ rank-2 ⟹ recover trivially**, leaving essentially **bounded-dimension affine** `V⋊G₀`
  (`F_p^d`, `d=O(1)`) and a few classical subset/flag actions. So G2-B's only live family is bounded-dim affine +
  a handful of classical cases. The full anatomy (why it's open, the affine reduction, the one theorem-route) is
  the **§G2 anatomy** subsection below. Genuinely open.

**Research-pass refinement (2026-06-07, the separability deep-research; STATUS rev. 3).** The verified literature
sharpens both quadrants:
- **G2-A is not citably-recoverable** (the rev. 2 "imprimitive ⟹ s≤2 ⟹ recovers" hope is refuted: `s(C)≤2` is
  *3/2-homogeneous*-only; general imprimitive homogeneous schurian schemes reach unbounded `s(C)`). But the unbounded
  examples are **abelian** (circulants) ⟹ **leg B (G1b)**, not a G2-A leak. So G2-A's genuine residue is *non-abelian*
  imprimitive, which the block tower reduces to G2-B. G2-A is a real but **derived** gap — closed once leg B + G2-B
  are.
- **G2-B has no known witness and no citable bound.** RQ2: no explicit primitive homogeneous schurian scheme with
  unbounded `s(C)` exists in the literature (so "primitive ⟹ separable" is unrefuted, just unproven). RQ3: the
  Babai/Sun–Wilmes/Kivva theory bounds `|Aut|` and *minimal degree*, **not** `s(C)` — the candidate-narrowing above
  (small ⟹ small base ⟹ bounded-dim affine + classical) stands as *heuristic*, but it is **not** a `s(C)` bound.
  RQ5: the self-detection lemma is uncitable. So G2-B is **project-internal-or-carried**, and the cheap decisive
  falsifier is the **Hanaki–Miyamoto small-primitive-scheme catalogue** (order 16: 6 primitive, 16 non-Schurian).

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
non-recovery ⟺ the structure constants fail to determine the scheme = **non-separable** (high `s(C)`). The target
statement is **primitive schurian ⟹ separable ⟹ `EdgeGenerates` ⟹ recovers**, decomposed into pieces P1–P4 below.

**CORRECTED (2026-06-07, separability deep-research) — the "wreath ⟹ imprimitive" support for P3 is abelian-specific,
NOT general; "primitive ⟹ separable" is a CONJECTURE, not a citable consequence, and the leaks do NOT collapse onto
G2-A.** The rev. 3 pass checked the literature this paragraph leaned on:
- **`non-separability = generalized-wreath = imprimitive` is an abelian-`p`-group result, not general.** Ryabov
  ([1709.03937](https://arxiv.org/pdf/1709.03937), [1812.11313]) classifies separability for *abelian p-group* S-rings
  (separable iff cyclic, `C₂×C_{2^k}`, `C₃×C_{3^k}`, `C₂³`, or `C₃³`) — so `F₂⁴`, `F₂⁵` are *non*-separable, but this
  is about abelian Cayley schemes, which are **leg B**, not the non-abelian primitive floor. There is **no theorem**
  "non-separable schurian scheme ⟹ imprimitive" at the generality P3 needs (RQ1/RQ2).
- **`E₁₆=F₂⁴ / E₃₂=F₂⁵` are multi-fiber, not homogeneous** — so they are *not* a homogeneous primitive G2-B witness;
  they do not falsify "primitive ⟹ separable" for schemes.
- Consequently **the primitive floor is the genuine leak (G2-B), not a recovered base case** — "collapses all leaks
  onto G2-A" was the refuted reorientation. The honest collapse is the opposite: G2-A's *non-abelian* residue reduces
  (via the block tower) onto **G2-B**, which is open.

Pieces (mapped to `Scheme.lean`):

| P | Statement | Status |
|---|---|---|
| **P1** | separable ⟺ `EdgeGenerates`/recovery | provable; engine landed (`theorem_2_HOR_of_edgeGenerates`) |
| **P2** | ¬recovery ⟹ a proper WL-stable fusion `W` (isolation deadlock) | provable (`isolationStep` saturates below `EdgeGenerates`) |
| **P3** | the deadlock fusion `W` is a `ClosedSubset` (block) ⟹ imprimitive | **CRUX = the project's Gate-G**; **NOT citable** (the wreath support is abelian-`p`-group-only, RQ1/RQ2) — project-internal counting proof, falsifier = the catalogue test |
| **P4** | primitive ⟹ no deadlock ⟹ recovers | follows P2+P3 (i.e. *conditional on the open P3*) |

**P3 is Gate-G.** The counting route reaches the project's existing Gate-G (exhaustive-obstruction §0.7.2) from the
structure-constant side. The rev. 3 research confirms it is **genuinely open** — no general wreath theorem closes it
(the support is abelian-`p`-group-specific), no known primitive homogeneous schurian counterexample refutes it, and
the cheap falsifier is the Hanaki–Miyamoto small-primitive-scheme catalogue (not E₁₆, which is multi-fiber).

**The C₇ correction (do NOT reintroduce the naive counting route).** "non-abelian ⟹ asymmetric intersection-number
count" is **false**: a *symmetric* scheme has a **commutative** Bose–Mesner algebra (`p^k_{ij}=p^k_{ji}`) regardless of
the group — C₇'s scheme is symmetric/commutative though `D₇` is non-abelian, and it recovers via its *metric* structure.
So the counting route cannot key on algebra non-commutativity; the asymmetry (when present) is a *specific* count whose
form varies (metric for C₇), and exhibiting it is the genuine work. Content = determinacy/separability, not commutativity.

**Thread T2 — linear-coupling = block-system (the affine instance of P3).** A persistent (growing-depth) gap requires an
**F₂-linear coupling** = a `G₀`-invariant subspace `W ⊆ V` = a **block system** ⟹ **imprimitive**; **primitive (`G₀`
irreducible) forbids it**. The cyclotomic case is the proof-of-concept: `Z₅` acts *irreducibly* on `F₂⁴`, so its only gap
is the *bounded* Galois one (depth 4). The rev. 2 hope was a **near-theorem via the wreath literature** ("non-separable
schurian S-ring ⟹ proper `G₀`-invariant section" ⟹ `G₀` irreducible ⟹ separable ⟹ recovers).
**Dependency CHECKED (2026-06-07, negative).** The wreath = imprimitive characterization is **abelian-`p`-group-specific**
(Ryabov 1709.03937/1812.11313), *not* clean at the schurian generality T2 needs — so there is **no citation** turning
"affine-primitive ⟹ separable" into a near-theorem. T2 stays a project-internal thread = the affine instance of P3, not a
citable shortcut.

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

**CORRECTION (2026-06-07, working the two-vantage step) — the concealment is the separability gap, NOT group
non-abelianness; do not anchor on `not_comm_of_orbit_disagree`.** Two findings from making the step precise:
- **The recovery gap reduces to `¬EdgeGenerates`, via landed `vProfile_iff_schemeOrbit`** (`Scheme.lean:576`): for a
  schurian scheme `relOfPair(e,·)`-classes **are** the `Stab(e)`-orbits, so from an individualized base there is **no
  orbit-vs-cell gap** — recovery fails *only* because the descent's edge relation `J` cannot reconstruct `relOfPair` by
  counting (`¬EdgeGenerates` = the separability gap `Ĝ⊋G`).
- **So `Stab(e)≠1` (the non-abelian decision) is the WRONG object** — it is normal suborbit structure (a suborbit of
  size > 1), produces no asymmetry, and `not_comm_of_orbit_disagree` proves *non-abelian ⟹ **not leg-B*** (¬D2 / not the
  unique-candidate case), which is the **consumption** statement, **not** the self-detection statement "non-abelian ⟹
  leg-A **recovers**." C₇ confirms: `D₇` non-abelian, `Stab(e)=Z₂≠1`, yet it recovers — because its edge *generates*
  (metric), nothing to do with `Stab(e)`.

**The corrected two-vantage step (multi-vantage isolation).** The step is genuinely **base + O(1)** (cyclotomic depth-4 =
base-2 + 2), in the `IsoPinned`/`relIsolatedAt_succ` engine: two relations `R_i,R_j` with the same single-base signature
(the gap) are separated by a second base `e'` iff a **two-base intersection count** distinguishes them
(`#{z : relOfPair(e,z)=R_i ∧ relOfPair(e',z)∈J} ≠ …=R_j…`). The gap **survives all bases** iff `R_i,R_j` are
**two-base-twins**. Splits into: **(realization, provable)** a distinguishing two-base count ⟹ `{e,e'}`-individualization
separates them (the two-base analogue of `Depth2Det`); **(existence, the crux)** a primitive scheme's gap is broken at
O(1) extra bases.

**Convergence — conservation = Thread T2 = P3 (one crux about the scheme's character structure).** The "concealment is
abelian" of the conservation route is correct, but **"abelian" means the gap's support is a linear / character
degeneracy (a block), NOT that the group `G` is abelian.** A gap that survives every base is **base-homogeneous =
supported by an invariant subspace / block system = imprimitive**; **primitive forbids it.** So the lone crux is:
> **primitive schurian ⟹ the separability gap is broken at O(1) extra bases** (`EdgeGenerates` at base+O(1) = bounded
> `s(C)`), because the gap's only base-homogeneous support is a block, which primitivity forbids.
This is *exactly* Thread T2 (affine: invariant subspace = block) and P3 (deadlock fusion = `ClosedSubset`). The
conservation route, T2, and P3 are **the same statement**.

**Concrete next lemma (Lean-ready, the sharpest form of P3):** *a relation-pair that is a two-base-twin at **every** base
pair generates a non-trivial `ClosedSubset`* — i.e. **base-homogeneous gap ⟹ imprimitive**, stated against `IsoPinned` +
`ClosedSubset` + `IsPrimitive`. Proving it closes the affine floor and the primitive floor together. The supporting
**realization lemma is LANDED** (2026-06-07, axiom-clean, `Scheme.lean §10.3b`): `schemePartFrom` (the depth-`k` counting
partition from an **arbitrary** initial colouring `χ₀` — `schemePart_at` generalized off the single base, since the base
is used only at depth 0) + `iterFrom_refines_schemePartFrom` (`iter[k] χ₀` refines it) + `iterSet_refines_schemePartFrom`
(the descent form: individualizing a base **set** `S` and warm-refining sees the multi-base counting partition). So *a
multi-base counting separation is realized as a warm-refinement split* — the easy half. The **crux remains** the converse
(primitive ⟹ the gap is broken at base + O(1)).

> **RESOLVED (2026-06-07, the separability deep-research pass).** The rev. 2 caution here — that the crux direction
> ("base-homogeneous gap ⟹ imprimitive", "primitive ⟹ separable") was likely *backwards* — has been checked against
> the primary literature (99 agents, 24/25 claims confirmed under 3-vote adversarial verification; full record in
> [exhaustive-obstruction §0.7.6](./chain-descent-exhaustive-obstruction.md)). **The "imprimitive ⟹ recovers"
> reorientation is REFUTED, and the prior `imprimitive`/`primitive` framing is replaced by a finer three-way map.**
>
> What the literature actually says:
> - **Evdokimov–Ponomarenko's `s(C) ≤ 2` is `imprimitive *3/2-homogeneous*`-only** (Thm 5.1, verified verbatim — a
>   narrow proper subclass: any two non-reflexive basis relations have equal degree), **not** all imprimitive
>   homogeneous schemes. Shrikhande is a 3/2-homogeneous `s(C)=2` witness, *not* evidence that all imprimitive
>   schemes recover.
> - **General imprimitive homogeneous *schurian* schemes reach unbounded `s(C)`** — circulants (Cayley over cyclic,
>   many imprimitive) have WL-dim `≥ c√log n` for infinitely many `n` (Wu–Ren–Ponomarenko 2025; prime-power order is
>   the bounded exception, `≤3`). So **imprimitive is NOT citably-recoverable; §0.7.6 stands.**
> - **But those unbounded examples are ABELIAN** (Cayley over cyclic) ⟹ consumed by **leg B**, not a non-abelian
>   leak. So the high-`s(C)` region splits: **abelian → leg B (G1b)**; **non-abelian primitive → G2-B (open)**;
>   **non-abelian imprimitive → block tower → G2-B**; **rigid (multipede) → IR-core**.
> - **No citation exists for the self-detection target.** Babai/Sun–Wilmes/Kivva bound `|Aut|` and *minimal degree*,
>   **not** `s(C)` (RQ3, high confidence); the link `|Aut| ↔ s(C)` is heuristic, not theorem-level. And "non-abelian
>   coupling ⟹ bounded WL-dim" is an explicit "almost all known" hedge in Lichter–Rassmann–Schweitzer, **not a
>   theorem** (RQ5). Multipedes (rigid, *trivial* Aut, arbitrarily high `s(C)`) prove high `s(C)` needs no symmetry
>   at all — so self-detection cannot be a pure group/Aut statement.
>
> **Consequence for the crux lemma.** The P3 direction ("primitive ⟹ separable / recovers") is *not* backwards — it
> is exactly the conjecture that G2-B is empty — but it is **not citable** and has **no known counterexample either**
> (RQ2: no explicit primitive homogeneous schurian scheme with unbounded `s(C)` is known). So if pursued it is a
> **project-internal counting proof with no citation safety net**, and the imprimitive case routes into it via the
> block tower (do not re-frame it as "imprimitive recovers, cite it" — that was the refuted reorientation). **The
> realization lemma (above) stands (direction-agnostic); the crux lemma is the genuine open G2-B / self-detection
> target, project-internal-or-carried.**
>
> **The cheap decisive falsifier** (replaces the abandoned point-twin route, and is sharper than the affine probe):
> the Hanaki–Miyamoto catalogue enumerates all association schemes with Schurian/primitive flags — **order 16 already
> has 6 primitive + 16 non-Schurian schemes**, computable. Check whether any *small primitive homogeneous* scheme is
> non-separable with small Aut: a witness is a 16-vertex seal counterexample (statement change); none is empirical
> support for G2-B emptiness (justifies the internal proof). Note the `E₁₆=F₂⁴ / E₃₂=F₂⁵` examples are **multi-fiber**
> (confirmed), so they are *not* a homogeneous G2-B witness — the catalogue, not E₁₆, is the falsifier.

**THE THREAD BOARD (what's worth doing, by tier — regardless of immediacy).**
- **Tier 1 — bankable slice-closures (provable now, shrink the wall but don't close it):**
  - **(a) G1b — leg B — LANDED (2026-06-07).** `AbelianConsumed` + `abelianConsumed_of_residualAbelian` (L3-earned,
    citation-free) + `reachesRigidOrCameron_viaRecoveryOrAbelian` (`Cascade.lean`, axiom-clean). Closes the abelian
    wall-slice; the seal is now `(SchemeRecovered ∨ AbelianConsumed) ∨ Cameron`. See §4 G1b.
  - **(b) G1a — depth-graded recovery — LANDED (2026-06-07).** `SchemeRecoveredByDepth` (two-phase: bounded shallow
    `CoversOrbitsAlong` + deep visible realizers) + group payoff + `reachesRigidOrCameron_viaDepthRecovery` + strict
    generalization of `SchemeRecovered` (`Cascade.lean`, axiom-clean). Captures CFI/Shrikhande; shallow ∅→S₀ phase
    carried (localisation, couples to the G2-A tower). Was (pre-landing):
    `RecoverableByDepth` at base+O(1); captures CFI/Shrikhande; now the *same*
    target as the primitive-floor self-detection.
- **Tier 2 — the G2 attack (the only route that actually closes the seal). The conservation route, Thread T2, and P3
  CONVERGE to one crux** (the corrected two-vantage analysis above): **base-homogeneous separability gap ⟹ imprimitive;
  primitive ⟹ gap broken at O(1) extra bases = bounded `s(C)`.** It is about the scheme's character/eigenvalue structure,
  **not** group commutativity (`not_comm_of_orbit_disagree` is ¬leg-B, a *different* statement — do not anchor on it).
  **Rev. 3: this crux is NOT citable** (no general wreath theorem; the support is abelian-`p`-group-only — RQ1/RQ2/RQ3),
  and has **no known counterexample** — so it is a **project-internal counting proof**, the genuine G2-B / self-detection
  target, with no citation safety net.
  - **(c) The sharpest-form P3 lemma (the target):** *a relation-pair that is a two-base-twin at every base pair generates
    a non-trivial `ClosedSubset`* — base-homogeneous gap ⟹ imprimitive (against `IsoPinned`/`ClosedSubset`/`IsPrimitive`).
    Warm-up **LANDED** (`Scheme.lean §10.3b`: `schemePartFrom` + `iterFrom_refines_schemePartFrom` +
    `iterSet_refines_schemePartFrom`) — the multi-base counting partition is realized by warm refinement. The converse
    (the crux) is the open conjecture; gate it behind the catalogue falsifier (f) before heavy Lean investment.
    **STATEMENT + SEAL-WIRING NOW LANDED (2026-06-10, axiom-clean, `Cascade.lean`).** The crux is named
    mechanism-agnostically (Frobenius-free, replacing the retracted `PowAffineSeparates`): **`PersistentTwinYieldsBlock`**
    (`¬ SeparatesAtBoundedBase → IsLarge ∨ ∃ nontrivial `ClosedSubset`` = base-homogeneous twin ⟹ block, general over any
    `SchurianScheme`), with the provable reduction `selfDetectsStably_of_persistentTwinYieldsBlock` (⟹ `SelfDetectsStably`)
    and the seal capstone `reachesRigidOrCameron_viaPersistentTwinBlock` (carries `hClassify`/`hImprim` + the open
    `hCrux`). Clebsch wired as the test (`CascadeAffine.lean`: `reachesRigidOrCameron_clebsch_viaPersistentTwinBlock`).
    Realization half (`no twin ⟹ separates`) = landed `discrete_of_kRoundRelationSeparates`, so this is the **only open
    half** of P3. **Only the converse *proof* remains open** (uncited G2-B); the intended route is the fusion/closed-subset
    closure (`schemeEquiv_trans`), not a forwards bound. Still gate heavy proof investment behind the catalogue (f).
    **CONVERSE PROOF LAYER 1 LANDED (2026-06-10, axiom-clean, `Cascade.lean`).** The fusion closure is **proved**:
    `intraCellRelations` (relations inside `warmRefine`-from-`S₀` cells) + **`intraCellRelations_isClosed`** (it is a
    `ClosedSubset` — generalizes `schemeEquiv_trans` via `intersectionNumber_well_defined` + cell-transitivity; any
    `AssociationScheme`) + `intraCellRelations_ne_univ_of_sep` (properness FREE for a base individualizing a point).
    Reduces the converse to the sharper kernel **`PersistentTwinGivesIntraCellBlock`** (`reachesRigidOrCameron_viaIntraCellBlock`),
    whose **only** open content is now **nontriviality** `≠ {0}` (a persistent twin ⟹ a *whole* intra-cell non-diagonal
    relation = a scheme congruence, not one same-cell pair). The closed-subset construction + properness are banked; the
    residue is the isolated nontriviality kernel = exactly where imprimitivity lives.
    **VACUITY BOUNDARY (2026-06-10, `intraCellRelations_eq_singleton_zero_of_primitive`).** Attacking nontriviality
    proved a decisive boundary: since `intraCellRelations` is always a `ClosedSubset`, a **primitive** scheme forces it to
    `{0}` (`≠ univ` is free for any nonempty base) — so the intra-cell block **identically vanishes on the primitive
    floor** and can never witness nontriviality there. It discharges only the *imprimitive* case (already handled by
    `hImprim`). **The open primitive floor (G2-B) is a WL-stable fusion that is NOT a scheme congruence** (the amorphic
    Clebsch `S₃`); no closed-subset/block object captures it. Attack routes scoped (self-detection-plan §11 tail): (A)
    base/s(C) split (`small ⟹ ∃ IsBase ≤ log₂|G|` then `recoverableAt_base_iff_discrete`) — provable group term + open
    s(C) term, but the base-size bound is a heavy from-scratch build and the reduction is otherwise redundant; (B)/(C)/(D)
    blocked (amorphic / Q1 wall / leg-A-covered). The hard core stays open — catalogue falsifier is the right next gate.
  - **(d) Thread T2** — the affine instance of (c): primitive ⟹ separable via invariant-subspace = block. **Dependency
    CHECKED negative (rev. 3):** the wreath = imprimitive characterization is abelian-`p`-group-only (Ryabov), *not* a
    citable near-theorem at schurian generality. T2 is a project-internal thread, not a citation shortcut.
  - **(e) The P1–P4 / Gate-G proof** of "primitive ⟹ separable" — (c) is its crux P3; open and uncitable (rev. 3).
- **Tier 3 — decisive cheap experiments:**
  - **(f) The Hanaki–Miyamoto catalogue test — RAN (2026-06-08, the decisive falsifier). VERDICT: NO G2-B WITNESS;
    G2-B EMPTINESS supported decisively.** `GraphCanonizationProject.Tests/CatalogueSchemeProbe.cs` ingests the catalogue's
    GAP data files (`data/hanaki/as<N>.gz`, gzipped, committed) and exhaustively analyzes **every** association scheme of
    orders **5–30** (2363 schemes, all parse-validated as genuine schemes via the homogeneity + well-defined-intersection-number
    gate). Result: **481 primitive (rank≥3) schemes, ALL 481 recover** (EdgeGenerates or bounded WL-depth ≤ base+O(1)),
    **0 G2-B candidates** (no primitive non-recovering scheme), **0 validation mismatches** — the probe's computed
    primitive-count matches the catalogue's *published* per-order primitive count **exactly for every order** (377/377 at order
    27, 5/5 at order 16, 20/20 at order 23, …; the data files omit only the thin regular-group schemes, which recover at depth 1
    and cannot be witnesses). Aut/Schurian machinery self-tested on the pentagon C₅ (|Aut|=10, schurian, non-abelian).
    This is the exhaustive analogue of the affine probe (g): where (g) swept a *constructed* family, (f) checks *all* small
    schemes directly — much stronger evidence. **Secondary finding:** 5 primitive schemes (order 16 #20/#21 rank-4; order
    25 #17/#18 rank-4, #39 rank-9) **fail depth-1 `EdgeGenerates` yet recover at bounded WL-depth** — empirical confirmation
    of the corrected target (bounded-depth recovery base+O(1), NOT depth-1; the Shrikhande/cyclotomic lesson generalizes).
    Note RQ4: `E₁₆=F₂⁴/E₃₂=F₂⁵` are multi-fiber (not homogeneous), so they are correctly *not* in the homogeneous catalogue
    as a witness; the catalogue (which IS the exhaustive homogeneous list) is the right object. **A genuine witness would
    have been a small primitive schurian non-abelian non-recovering scheme = a seal counterexample (statement change); none
    exists in orders 5–30.** Caveat (honest): the verdict rests on the EdgeGenerates/WL-depth recovery proxy = separability;
    since 0 candidates arose, the Aut/Schurian classifier ran only on the self-test, not a real candidate.
  - **(g) Non-abelian irreducible `G₀` — RAN (2026-06-08, route 1 strand (a)).** `AffineSchemeProbe.Probe_NonAbelianIrreducibleG0`
    sweeps the **Singer normalizer `ΓL(1,2^d) = ⟨Singer, Frobenius⟩`** and its subgroups `⟨gᵐ, φᵏ⟩` (`φgφ⁻¹ = g²` ⟹
    genuinely non-abelian — the actual A4 zone, not the Galois/cyclic gap). The probe builds the Frobenius `x↦x²` matrix
    the original probe skipped (full `F_{2^d}` field arithmetic), with a `φg=g²φ` sanity assert. **VERDICT (decisive): no
    G2-B witness.** Across `d=4,6,8` (`|V|=16,64,256`, 16× range): 14 primitive non-abelian schemes, **0 leak candidates**,
    and the primitive-candidate max recovery depth is **FLAT at 4** (not growing) — strong support for "small primitive ⟹
    recovers at base+O(1)". **Lockstep-completeness confirmed empirically:** 8 of 14 primitive non-abelian schemes are
    *x-branch* — depth-1 `EdgeGenerates` (the within-cell lockstep single-step) **misses** them, but the cross-branch /
    multi-step harvest recovers at bounded depth 3–4. This is `lockstep_disc_imp_stab_trivial` in the wild: single-step is
    insufficient for primitive non-abelian schemes (the *norm*, not a corner case), but the cross-branch (Part-A) harvest
    is sufficient and tame. (The full normalizer `ΓL(1,2^d)` itself is 2-transitive = rank-2 = `K_{2^d}` — its Cayley-graph
    IR-depth `n−1` is meaningless; the family signal tracks primitive rank≥3 candidates only.) **Remaining route 1:**
    strand (b), non-affine primitive types (`A₅`, `PSL(2,q)`, classical) — different infra (orbital schemes of
    permutation groups), the only zone not yet swept.
- **Tier 4 — doc-sync / record-keeping (the NoFusion over-claim):**
  - **(h) DONE (2026-06-07).** The NoFusion/largeness-derivation over-claim is **reconciled**: `largenessBridge_viaHarvest`
    is *tautological* (orbit-level vacuity, §2–§3), and the prose that claimed "largeness derived from the harvest" has
    been corrected with warning banners in `PublicTheoremIndex.md` (the `NoFusion` family: `NoFusion`, `reproducesResidual_of_noFusion`,
    `autP_reproduced_of_noFusion`, `isLargeAutP_of_noFusion`, `largenessBridge_viaHarvest`, `LargenessBridge`,
    `exhaustiveObstruction_scheme_of_harvest`, `reachesRigidOrCameron_viaHarvest`), in
    [exhaustive-obstruction §0.7.5](./chain-descent-exhaustive-obstruction.md) (top banner), and in
    [`00-START-HERE.md`](./00-START-HERE.md) §2. The Lean is sound (the theorems are true, just vacuous/tautological as
    *evidence*); future readers are now warned not to treat NoFusion as live evidence that G2-B is closeable.
  - **(h′) DONE (2026-06-07) — Lean excision complete, axiom-clean.** The vacuous `NoFusion`/largeness-derivation
    family is **removed** from `Cascade.lean`: deleted `NoFusion`, `reproducesResidual_of_noFusion`,
    `autP_reproduced_of_noFusion`, `noFusion_of_visibleRecovery`, `noFusion_of_warmSeparatedPartition`,
    `isLargeAutP_of_isLargeProd`, `isLargeAutP_of_noFusion`, `NonCascadeViaHarvest`, `largenessBridge_viaHarvest`,
    `exhaustiveObstruction_scheme_of_harvest`, `reachesRigidOrCameron_viaHarvest` (11 decls + their index rows).
    The 3 concrete capstones (`_viaRecovery`, `_viaRecoveryOrAbelian`, `_viaDepthRecovery`) were **re-wired** to
    call `reachesRigidOrCameron` directly with `NonCascade := IsLargeSchemeViaAut IsLarge` and the **identity**
    `LargenessBridge` (`fun _ _ h => h`) — largeness honestly carried, `¬IsLargeSchemeViaAut` = "small" the cascade
    antecedent. Kept the clean pieces (`schemeAdj`, `isAut_schemeAdj_iff`, `stabilizerAt_schemeAdj_empty_eq`,
    `IsLargeSchemeViaAut`, abstract `LargenessBridge`/`reachesRigidOrCameron`, the trichotomy) and the Route B
    block-decomposition family (separate, not NoFusion). Full build green, all capstones axiom-clean
    `[propext, Classical.choice, Quot.sound]`. **No vacuous hypothesis lingers in the source.**

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
| Abstract seal | `reachesRigidOrCameron` (parametric in `NonCascade`/`LargenessBridge`), `IsLargeSchemeViaAut`, `schemeAdj`/`isAut_schemeAdj_iff`/`stabilizerAt_schemeAdj_empty_eq` (`Cascade.lean`) |
| Concrete seal | `SchemeRecovered`, `schemeRecovered_of_visibleRealizers`, `schemeAutGroup_eq_closure_of_recovered`, `reachesRigidOrCameron_viaRecovery` (`Cascade.lean`) |
| Trichotomy / leg C | `exhaustiveObstruction_scheme(_of_nonCascade)(_nonCascade_trichotomy)`, `PrimitiveCCClassification`, `isPreprimitive_of_isPrimitive` (`Scheme.lean`) |
| Leg B core | `smul_eq_on_orbit_of_comm` (L3), `aut_agree_on_orbit_of_comm`, `not_comm_of_orbit_disagree`, `not_comm_of_isPreprimitive_card_lt`, L1/L2 (`Group.lean`) |
| Leg B in the seal (G1b) | `AbelianConsumed`, `abelianConsumed_of_residualAbelian`, `reachesRigidOrCameron_viaRecoveryOrAbelian` (`Cascade.lean`) |
| Depth-graded recovery (G1a) | `SchemeRecoveredByDepth`, `schemeAutGroup_eq_closure_of_recoveredByDepth`, `schemeRecoveredByDepth_of_schemeRecovered`, `reachesRigidOrCameron_viaDepthRecovery`, `coversOrbits_append`/`CoversOrbitsAlong` (`Cascade.lean`) |
| Imprimitive seal leg (scheme-seal wiring) | `hreach_of_quotientVisibleRealizers`, `reachesRigid_of_blockVisibleDecomposition`, `SchemeBlockRecovered`, `schemeAutGroup_eq_closure_of_blockRecovered`, `reachesRigidOrCameron_viaBlockRecovery` (`Cascade.lean`); `exists_nontrivial_closedSubset_of_not_isPrimitive`, `schemeEquiv`/`schemeEquiv_class_eq_iff` (`Scheme.lean`) |
| Cross-branch harvest (recovery ⟹ group) | `closure_eq_stabilizerAt_of_visibleRealizers`, `crossBranchHarvest_reproduces_residual`, `autP_reproduced_of_visibleRealizers`, `orbitRealizers_iff_visibleRealizers_of_cellsAreOrbits` (`Cascade.lean`) |
| Tower (depths add) | `cascadeComposition`, `cascadeComposition_pathFixing`, `cellsAreOrbits_compose`, `cumulative_card_le`, `LayerStep` (`Cascade.lean`) |
| Recovery witnesses | `RecoverableByDepth`, `recoverableByDepth_pPolynomial` / `_cfi` / `_scheme`, `cellsAreOrbits_of_discrete` (`CascadeOracle.lean`) |
| Block decomposition (conditional) | `reachesRigid_of_blockDecomposition`, `hreach_of_quotientRealizers`, `hfiber_of_fiberRealizers`, **`hfiber_of_fiberVisibleRealizers`** (fiber, visible), **`hreach_of_quotientVisibleRealizers`** (quotient, visible — the shallow-phase discharge), **`reachesRigid_of_blockVisibleDecomposition`** (both halves visible), `blockHarvest_of_realizers`, `coversOrbits_append`, `CoversOrbitsAlong` (`Cascade.lean`) |
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
4a. **Lockstep completeness is the algorithm-level seal condition — and the flag lives in the *harness*, not the
   lockstep (2026-06-08 code audit, `ChainDescent.cs`).** The lockstep (`HarvestTwists`→`DeepenAnchor`+`ReplayDeepening`)
   is genuinely **single-path, bounded-depth (≤ n), poly per node, never branches** — that much is class-agnostic. But it
   is a *harvest*, not the canonizer: it deepens an anchor along an arbitrary (lowest-id) path, replays the same sequence
   on each sibling, reads a candidate twist, and **edge-verifies** it (`IsAutomorphism`). It is **sound** (a candidate that
   fails verification is discarded — never a wrong merge) but **incomplete**: when a true symmetry isn't captured by the
   single-path replay (multi-step / high `s(C)`; `lockstep_disc_imp_stab_trivial`), the sibling is **not pruned**, so the
   *outer* `Search` falls back to k-way branching, and **that** branching trips the node budget (`Search`:
   `++_nodeCount > _budget`). So: the lockstep never flags and never branches; the **harness budget flags, tripped by the
   lockstep's under-pruning**. "Poly per node" (class-agnostic) ≠ "poly total" (class-conditional): the total is poly ⟺ the
   lockstep prunes every sibling ⟺ harvest completeness ⟺ the recovery/cascade condition (= bounded `s(C)`). This is the
   algorithm-level mirror of the seal's visible-realizer keying (`SchemeRecovered`): the non-vacuous content is exactly
   poly-recovery. Empirically (route 1 strand (a), §G2 board (g)): primitive non-abelian affine schemes are *mostly*
   lockstep-incomplete (8/14 "x-branch") yet recover at bounded depth via cross-branch — completeness needs the Part-A
   harvest, not the within-cell lockstep, and is then tame.
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
