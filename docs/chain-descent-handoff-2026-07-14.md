# HANDOFF — 2026-07-14 (the canonizer object: ①, ②, ③ and what is actually left)

> **Read this first if you are picking the project up.** It is the authoritative state of the **canonizer** track as
> of 2026-07-14. It supersedes the STATUS blocks of `chain-descent-mixed-composition.md`,
> `chain-descent-remaining-work.md` and `00-START-HERE.md` §2 wherever they disagree — and it records **two
> retracted claims** that a reader could otherwise re-derive and act on.
>
> **Quality bar (unchanged, non-negotiable):** every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`;
> full build green (`bash scripts/build.sh`, **~110 s**); no `sorry`; no fresh `axiom` (cited results are theorem
> hypotheses); **`native_decide` BANNED**; **`@[implemented_by]` AVOIDED** (it can assert a false equation).

---

## 0. The one-paragraph state

**①, ② and ③ all have real theorems about the real object, and every remaining gap is a *firing* gap — a question
of how much the two resolvers can actually see.** The canonizer is `Descend.descend`: a computable,
resolver-parameterized branching descent in `CostM`, whose executable, correctness proof and cost proof are three
projections of **one** definition. It is sound, iso-invariant, complete, and — once **stall-guarded** —
**unconditionally polynomial**, flagging exactly where neither resolver can act. The residue is *defined* as the
complement of a positive capability predicate, so it is not an asserted atom and it **shrinks** whenever a resolver
gets stronger, with no re-proof of anything. What is missing is resolver **strength**: the built oracle is a
*one-step* colour match that flags on a 7-cycle, and the built rigid key is a look-ahead heuristic. That is the
whole frontier.

---

## 1. The stack (all in `scripts/build.sh`, all axiom-clean, no `sorry`)

| Module | What it is |
|---|---|
| `ChainDescent/CanonicalForm.lean` | **the spec**: `IsCanonicalFormOpt = SoundOpt ∧ IsoInvariantOpt`. Completeness and flag-invariance are **free** (`complete_of_isCanonicalFormOpt`). |
| `ChainDescent/Descend.lean` | **THE OBJECT** — `descend`, `canonForm?`, `descentCost`. The **resolver contract** (`NarrowTransport`) and its **three** routes. Capstone `isCanonicalFormOpt_canonForm?` ⟹ ①a/①b/①c. |
| `ChainDescent/Refine.lean` | the **encode-free refiner** (`encodeFreeFast`). Discharges both refiner obligations ⟹ `exhaustive_canonizer` (unconditional). |
| `ChainDescent/Consume.lean` | the **oracle resolver** (`Covering` route). Untrusted `Supply` + decidable `IsColAut` ⟹ sound for **every** supply. Firing: `consume_singleton_of_cellIsOrbit`, `consume_narrows_of_wordReach`. |
| `ChainDescent/Force.lean` | the **rigid resolver** (`NarrowEquivariant` route), as `forceBy key`. Sole ① obligation: `KeyEquivariant`. Firing: `forceBy_singleton_of_separating`, `forceBy_narrows_of_key_ne`. |
| `ChainDescent/MatchSupply.lean` | the **cascade oracle as a `Supply`** — construct-and-check colour matching. `cellIsOrbit_matchSupply`. |
| `ChainDescent/Composite.lean` | **the MIXED resolver** `forceThenConsume` — both moves at one cell. |
| `ChainDescent/Cost.lean` | **②** — `descentCost_le_of_resolved`, `poly_of_cells_resolved`. |
| `ChainDescent/Stall.lean` | **the mutual-stall flag** (`guard`) ⟹ **unconditionally polynomial** (`descentCost_guard_le`). |
| `ChainDescent/Residue.lean` | **③** — `Handled` (positive), `Residue := ¬Handled`, `residue_if_flag`, `residue_nonvacuous`. |
| `ChainDescent/SealBridge.lean` | **P0 — THE VOCABULARY BRIDGE** (2026-07-14, second pass). `horb_of_cellsAreOrbits`: the seal's `CellsAreOrbits` **is** the supply's firing hypothesis. See §6.0. |
| `ChainDescent/SupplyTransport.lean` | **P1 — THE FLAG'S ISO-INVARIANCE** (2026-07-14, second pass). `stallEquivariant_forceThenConsume`, and **`matchSupply_guarded_canonizer` — the first CONCRETE mixed canonizer, no carried hypotheses.** See §6.0. |
| `ChainDescent/DeepMatchSupply.lean` | **P2 — THE BOUNDED-DEPTH ORACLE** (2026-07-14). `deepMatchSupply d`: enumerate every length-`≤ d` individualization sequence, colour-match all pairs. Equivariant **because it makes no choice**. `C₄`/`C₇` now answer. Cost `n^{O(d)}`. See §6.2. |
| `ChainDescent/OrbitPrune.lean` | **P3 FOUNDATION** (2026-07-14). §1–3 **the reduction** — `SameOrbits S₁ S₂` ⟹ the two guarded canonizers are the *same function* ⟹ `①` transfers with **no equivariance obligation on the second supply**. §4 **the pruning license** (`deepCandidate_left_mul` / `_right_mul`). See §6.2b. |
| `ChainDescent/PrunedSupply.lean` | **P3c FIRST HALF** (2026-07-16). `prunedSupply d` — reference-matching, `\|table\|` not `\|table\|²`; `SameOrbits` ⟹ ①/②/③ transfer. See §6.2b. |
| `ChainDescent/HandledBridge.lean` | **THE `Handled` POPULATION BRIDGE** (2026-07-16). `reaches_pathCol` (every reached node IS a `pathCol`) + **`handled_of_seal`** — the first theorem instances of `Residue.Handled`. See the §4 update box. |
| `ChainDescent/Select.lean` | **THE SEL REWRITE, increments 1+2** (2026-07-17). `NodeRes` (node resolver: children WITH their refined colourings, `[] = flag` = true mutual stall — §6.1 AND §6.4 in one interface), `descendS`, ★ `descendS_blind` (EXACT `CostM` equation vs `descend` — the safety net), `descendS_sound` (①a **unconditional**), `NodeTransport` + `descendS_transport` ⟹ capstone `isCanonicalFormOptS_canonFormS?`, and ★ `nodeTransport_blindNode` (**conservativity** — every proved `NarrowTransport` instance discharges the new contract at the blind instance). See §6.1's design-pass block. |
| `ChainDescent/Regression.lean` | the **build-gating** regression suite (~12 s). |
| `ChainDescent/PerformanceTest.lean` | measurements — **deliberately NOT in `build.sh`**; run with `lake build ChainDescent.PerformanceTest` (~4 min). |

---

## 2. ① — correctness (DONE, and it carries nothing)

**Spec = `Sound ∧ IsoInvariant`, full stop.** Completeness and flag-invariance are free.

**The resolver contract is `NarrowTransport`** — *the narrowed-branch aggregate transports under σ* — fed by
**three** sufficient conditions, which are the **same** condition against different reference lists:

| route | reference `N` | instance | discards are |
|---|---|---|---|
| `Covering` / `CoveringAt` | `branches` | **consume** | **redundant** (an automorphism maps them to a kept branch) |
| `NarrowEquivariant` | `narrow R` itself | **force** | genuinely **different** (the aggregate *changes, consistently*) |
| **`CoveringOfAt` + `NarrowFnEquivariant`** | **any equivariant `N`** | **the composite** (`N` = the forced set) | both |

> **⛔ DO NOT re-unify these under a single `Covering`.** `canonForm?_eq_deferAll_of_covering` **proves** a covering
> resolver is **value-invisible** — it computes exactly the exhaustive branch-min — so a single covering contract
> silently re-imports the retired `canonMin` anchor and **force could satisfy it only by already knowing the
> answer**.

**Why the third route had to exist:** the composite is **neither** `Covering` (force changes the aggregate) **nor**
`NarrowEquivariant` (consume's representative choice is deliberately non-equivariant). It is sound because
**`Force.mem_keepMin_of_aut`: the forced set is a union of orbits** — `KeyEquivariant` at an automorphism gives
`keyV_aut_invariant` (an equivariant key is **constant on orbits**), so the argmin never cuts an orbit and consume,
run inside it, cannot escape. **The order `force`-then-`consume` is forced *for the proof*** — the reverse is
value-equivalent but leaves a non-equivariant intermediate with no covering argument.

**Non-collapse (why this is not GI ∈ P):** `narrow_eq_branches_of_orbit` — equivariant narrowing is *impossible* on
an orbit cell ⟹ **force cannot fire on a symmetric cell and consume fires exactly there**. Complementary firing
domains; graphs where **neither** fires are the residue.

---

## 3. ② — cost (DONE, and **unconditional**)

> **Deferral is not a cheap mode of a healthy run — it IS the failure mode.** Every node either **consumes** (the
> supply connects the cell ⟹ a symmetry ⟹ no branching) or **forces** (the key separates it ⟹ a real decision, taken
> structurally). A node that can do **neither** has reached the **mutual stall** — *that node is the unhandled
> residue*. There is **no deferred-then-retried decision in the design**, hence **no exhaustive fallback to be
> polynomial *about***. A descent runs as a **single path** or it **stops**.

`Stall.guard R` flags at any node the resolvers leave with ≥ 2 branches ⟹ **`resolvedAll_guard` holds BY
CONSTRUCTION** ⟹ the descent is a **single path of ≤ `n+1` nodes on every input** — no exponential blow-up is
possible. **`poly` AND `flag`, never `poly` OR `exponential`.**

> **⚠ READ THE THEOREM EXACTLY.** `Stall.descentCost_guard_le` concludes `descentCost ≤ c₁ + (n+1)·(1+c₁+c₂)` *from*
> `hrf : (rf adj χ).2 ≤ c₁` and **`hR : ∀ χ, (R adj χ (branches χ)).2 ≤ c₂`**. What is unconditional is the **node
> count** (single path ⟹ ≤ `n+1` nodes, no dependence on the graph/supply/key). The **total** cost is polynomial
> **iff the per-node supply cost `c₂` is**. This matters: with `deepMatchSupply d` the supply's own per-call cost is
> `n^{O(d)}` (§6.2), so "unconditionally polynomial" is true of the *number of nodes* — and of the wall-clock only
> **per fixed `d`**. The `d = Θ(log n)` ladder-break (§6.2b, `P3c` second half) is what would make `c₂` small at
> growing depth.
>
> **✅ `c₂` IS DISCHARGED FOR EVERY BUILT CONSUME SUPPLY (2026-07-17, `ChainDescent/SupplyCost.lean`, axiom-clean,
> in `build.sh`).** Explicit closed-form bounds: `matchSupply ≤ matchSupplyBound n` (`O(n⁴)`);
> `deepMatchSupply d`/`partialMatchSupply d ≤ pairSupplyBound n d`; `prunedSupply d ≤ refSupplyBound n d` with
> candidate count `≤ tableBound n d = n·(n+1)^d` **not** `tableBound²` — the measured `|table|²→|table|` cut is now
> a theorem. End-to-end: `descentCost_guard_consume_*_le` per supply, the key-abstract mixed bound
> `descentCost_guard_mixed_le` (`kc` a parameter — F3's ring key drops in with one `keyCost` lemma), **★
> `descentCost_pruned_lookahead_le`** — the first end-to-end explicit-polynomial `descentCost` for the concrete
> canonizer of record (② companion of `prunedSupply_lookahead_canonizer`) — and the ②+③ capstone
> `handled_answers_poly` (`Handled` ⟹ answers ∧ within `pathBound`). All poly **per fixed `d`**.
>
> **⚠ THE `hR` WEAKENING THIS REQUIRED (2026-07-17) — the old form was UNSATISFIABLE.** The previous hypothesis
> `∀ χ B, (R adj χ B).2 ≤ c₂` quantified over **arbitrary** `B : List (Fin n)` (duplicating, unboundedly long),
> while **both** built resolvers bill per element of `B` (`consume`: per-candidate verification over `B`; `forceBy`:
> one key evaluation per element) — so **no finite `c₂` existed for any concrete resolver** and ②'s conditional form
> could not be instantiated (standing trap #8, caught in the wild). `descend` only ever calls the resolver at
> `B = branches χ` (`Cost.descend_cost_succ`), so the hypothesis now lives at that call site
> (`Cost.descend_cost_le_of_resolved`, `Stall.descentCost_guard_le{,_encodeFree}`, `Stall.guarded_force_canonizer`,
> `Cost.poly_of_cells_resolved` all weakened in place; no downstream breakage — nothing could have instantiated the
> old form).

**★ No `descend` signature change was needed.** `aggregate [] = none`, so a resolver **already has a flag channel**:
return the *empty* narrowing and the node emits `none`, which propagates to the root.

> **⚠⚠ THE NEW OBLIGATION THE FLAG CREATES — the supply must be EQUIVARIANT (`Stall.StallEquivariant`).**
> `consume`'s headline is that the supply is **untrusted** — `consume_canonizer` holds for *every* supply — because a
> covering resolver is **value**-invisible. **A flag is NOT value-invisible:** `stalled` reads the narrowing's
> *length*, which depends on how many orbits the supply's generators actually **prove**. A supply good on `G` and
> junk on `σ·G` makes `G` **answer** and `σ·G` **flag** ⟹ **①c is false.**
> - **Free** for the force-only route (its narrowing is equivariant by construction) and for `matchSupply` (a
>   structural function of `(adj, χ)`).
> - **Witnessed, not merely predicted:** `Regression.lean` §6 `#guard`s the counterexample — the fixed-generator
>   `dihSupply` makes `C₅` answer and `σ·C₅` flag. **That guard is the non-vacuity witness for `StallEquivariant`;
>   do not delete it.**

---

## 4. ③ — the residue (SHAPE DONE; the content is the frontier)

**Defined, never asserted.** `Residue.Handled key S adj` is the **positive capability predicate**: every non-discrete
cell is **either** supply-connected (consume's domain) **or** key-separated (force's domain). Everything is proved
*forwards*:

* **`answers_of_handled`** — a handled graph never flags (and was already unconditionally polynomial) ⟹ on `Handled`:
  sound, iso-invariant, complete, **polynomial**, and it **answers**.
* **`Residue := ¬Handled`** — a **definition**, not an `opaque` atom ⟹ **`residue_if_flag`** *is*
  `Publication.residue_if_flag` (③) for the real object, and **`residue_nonvacuous` is provable** (it was
  undischargeable **in principle** while the three `Publication` atoms were `opaque … : Prop`).
* **`Composite.forceThenConsume_stall`** — the **attribution**: every residual cell is assignable to **exactly one**
  side's weakness (the supply failed to connect an automorphic pair, or the key failed to separate a non-automorphic
  one).

**Methodological steer (user, and it is load-bearing):** define the residue as the complement of what the resolvers
**can** handle; never by asserting what they can't. Asserted atoms are how this project repeatedly manufactured
**vacuous** predicates (`hflag`, `SchemeReproduced`, `∃ gens, closure = group` were all vacuous). A residue that is
the complement of a positive, instantiated capability cannot be vacuous by accident — and it **shrinks** as the
resolvers strengthen, with no re-proof.

> **✅✅ UPDATE (2026-07-16) — `Handled` RE-BASED onto REACHABLE nodes, and POPULATED (`Residue.lean` +
> `HandledBridge.lean`, axiom-clean, in `build.sh`).** The 2026-07-16 blocker audit found the original `Handled`
> quantified over **all** colourings — **undischargeable in principle**: the seal corpus speaks only at committed
> paths (`SealBridge.pathCol`), `CellsAreOrbits` genuinely *fails* at generic colourings (its own docstring), and
> zero theorem instances existed. Fixed structurally, not by weakening the guarantees:
> - **`Descend.Reaches rf adj χ`** — the descent's reachable node colourings, **over-approximated
>   resolver-independently** (any branch vertex) so every instance survives future resolver strengthening;
>   `descend_ne_none_reaches` / `canonForm?_ne_none_reaches` = totality from properness on the reached set only.
> - **`Handled` now demands `CellResolved` only at reached nodes**; `answers_of_handled` / `residue_if_flag` /
>   `handled_congr` unchanged in strength. `residue_nonvacuous` re-proved at a genuinely **reached** node (the
>   empty 2-graph's root, non-discrete by refiner equivariance under the swap; ⚠ the old ∀-`adj` form is FALSE
>   under the new definition for root-discrete graphs — that is the definition working, see
>   `handled_of_root_discrete`).
> - **`HandledBridge.reaches_pathCol`** — the reachable-node induction (every reached node colouring **is** a
>   `pathCol`, definitionally via `Refine.refineV_encodeFreeFast`) — the statement `SealBridge` had only asserted
>   in prose.
> - **★★★ `HandledBridge.handled_of_seal` — the FIRST structural discharge:** depth (`CascadesAt adj (constP n) k`
>   — what `theorem_1_HOR_*`/the sealed families produce) **+** localisation at every committed set
>   (`∀ T, CellsAreOrbits adj (constP n) T`) ⟹ `Handled key (deepMatchSupply k)` for **every** key; transfers to
>   `prunedSupply` via `SameOrbits` with no new proof (`handled_of_seal_pruned`); showcase `seal_graph_answers`.
> - **★ THE WEAKEST HOOK (2026-07-17) — `handled_of_seal_selected` (+ `_pruned`).** Per-family localisation pared
>   to exactly what the descent consumes: only the **target cell** (the `SelectedCellIsOrbit` shape —
>   `Consume.CellIsOrbit` reads nothing else) and only at **validly-reachable** committed sets
>   (`HandledBridge.ValidPath`: each vertex drawn from the current target cell; carried by
>   `reaches_pathCol_valid`). The `∀ T` hook implies it (`selectedOrbits_of_cellsAreOrbits` — the lattice, in
>   code; `handled_of_seal` is now proved as its instance). **Populate a family through whichever it affords**:
>   `∀ T` when localisation is uniform; `_selected` when it is earned along the descent's own choices and fails
>   at unreachable sets (e.g. `C₆` never commits `{0,3}`) or non-target cells.
> - **First inhabited instances:** `handled_emptyAdj` (edgeless graphs, every `n`, every key — vertex-transitive,
>   so the supply genuinely fires) ⟹ with `residue_nonvacuous` **both halves of the endgame non-vacuity obligation
>   are theorems about ONE graph** (`adjE2`: residual with the certify-nothing resolvers, handled with the deep
>   oracle — the residue-shrinks story at theorem level, `adjE2_handled`).
> - **▶ The open item is now sharply named: PER-FAMILY LOCALISATION.** The HOR theorems deliver the **depth** half
>   (`CascadesAt` at bounded `k`) and localisation only at the **discrete endpoint**; populating `Handled` for a
>   sealed family = discharging localisation through **either hook**: `∀ T, CellsAreOrbits` (`handled_of_seal`) or
>   the strictly lighter target-cell-at-valid-paths form (`handled_of_seal_selected`, landed 2026-07-17 — see the
>   weakest-hook bullet below). That is the honest next increment, replacing the old vague "seal hypotheses at
>   every reachable node".
> - ⚠ A concrete 1-WL-rigid witness for `handled_of_root_discrete` via kernel `decide` is **blocked**:
>   `Multiset.sort` (inside `sigKey`) is well-founded recursion, which the kernel cannot reduce. Runtime evidence
>   stays in `Regression.lean` `#guard`s (which evaluate via the compiler, not the kernel — that is why they can
>   see `warmRefine` values and theorems cannot, without manual proofs).

---

## 5. ⛔⛔ TWO RETRACTED CLAIMS — do not re-derive them

### 5.1 "A perfect key cannot exist" — **WRONG, circular**
An earlier draft argued: *a key separating exactly the non-automorphic pairs would collapse every cell to one branch,
i.e. GI ∈ P, therefore it cannot exist.* **That presupposes GI ∉ P** — the very thing this project does not assume and
is in pursuit of refuting. It also violates the standing steer *"Polynomial is NOT a wall — it's the route's target."*
- **Correct statement — an EQUIVALENCE: a perfect key *is* GI ∈ P.** It is the **target**, not a barrier.
- **STANDING STEER: any argument of the form "X would give GI ∈ P, therefore X is impossible" is BANNED.**

### 5.2 "Fusion is dissolved" — **WRONG, and it hid a live gap**
An earlier draft misdefined fusion as *a meta-product over orderings* and claimed
`Stall.guarded_choice_transports` dissolved it. That theorem is true and useful (**the chosen branch is
iso-invariant**) but it is **not a no-fusion theorem**.

> **Fusion is a dependency of EXPOSURE.** A decision's *type* — symmetry or real decision — may only become
> **visible** once other decisions are resolved.
> * **A ring**: vertex-transitive ⟹ every *initial* decision is a symmetry; yet most of its decisions are **rigid**,
>   merely not exposed until `{root, direction}` are consumed (after which 1-WL discretizes them). Polar-affine
>   graphs: same story, far harder to exhibit.
> * **Chang-A — the converse**: 360 immediately-visible symmetries **plus 24 that become certifiable only after some
>   rigid decisions are made.**
> Fusion needs **deferral** to occur.

**⚠ AND IT HAS A LIVE BITE — see §6.1.**

---

## 6. WHAT IS LEFT — in priority order

### 6.0 ✅ DONE (2026-07-14, second pass) — `P0` + `P1`. **Read this before touching §6.2.**

**`P1` — `ChainDescent/SupplyTransport.lean`. The flag's iso-invariance is DISCHARGED, and there is now a
CONCRETE canonizer.** `Stall.StallEquivariant` was carried by all three `Residue` capstones and **instantiated by
nothing** — so `guarded_mixed_canonizer` had no instance at all, while `Regression.lean` §6 `#guard`s a genuine
counterexample. Closed by:
- **`GensEquivariant S`** — *the supply hands back the `σ`-conjugates on the relabelled graph*. **Free for a
  structural supply; IMPOSSIBLE for an accumulating one.** ⟹ **the Lean supply must be STATELESS.** (The C#
  harness's global, order-dependent `Automorphisms` group is safe there only because its harvest is a pure
  *covering* move and its flag is a **budget**; `Stall.guard`'s flag reads the narrowing's *length*, so the C#
  design **does not transfer**. This is a hard design constraint on the §6.2 supply.)
- **`Consume.rep_eq_iff_wordReach`** — `rep` merges **exactly** the orbit (the `→` half was missing). Hence the
  narrowing's **length counts ORBITS**, so it transports even though the least-index `rep` deliberately does not.
- Discharged for `matchSupply` (`gensEquivariant_matchSupply`, via `matchCandidate_conj`) ⟹
  **`matchSupply_guarded_canonizer`: encode-free refiner + `lookaheadKey` + `matchSupply`, ①a/①b/①c and
  unconditional polynomiality, NO carried hypotheses.** Everything still open is a *firing* question.

**`P0` — `ChainDescent/SealBridge.lean`. The seal corpus can now reach the supply.** The seal speaks
`warmRefine adj P (individualizedColouring n T)` / `CellsAreOrbits` / `ResidualAut`; the canonizer speaks
`Consume.IsColAut adj χ` / `branches χ`. They could not talk, so **every** seal result was unusable and any
consume-strength theorem would have had to be re-proved in parallel. Three gaps closed:
1. the two **refiners** agree as partitions (`warmRefineR_samePartition`);
2. the two **individualizations** agree (batch `individualizedColouring` vs interleaved index-free `indivOne`);
3. **★ CONFLUENCE** (`warmRefine_indivOne_confluent`) — *refining before individualizing does not change the
   stable partition*, because `warmRefine` is the **coarsest stable refinement**. The only non-bookkeeping step.

⟹ **`horb_of_cellsAreOrbits`**: `CellsAreOrbits` at the committed set **is** the `horb` hypothesis
`cellIsOrbit_matchSupply` already takes. `theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_*`, the four sealed form
families, `reachesRigidOrCameron_*`, Spielman's `SeparatesAtBoundedBase` are now **reusable as-is** — the seal
results are *imports*, not re-proofs. **This is the answer to "reusable, else re-provable as parallel theorems":
reusable.**

### 6.1 ⚠ The target-cell selector is BLIND to resolvability (fusion's live bite) — **design VALIDATED 2026-07-17; ordering REVERSED (do BEFORE F2/F3 and P3c-2nd-half); increments 1+2 LANDED (`Select.lean`)**

> **▶▶ 2026-07-17 DESIGN PASS (source-checked; supersedes the 2026-07-15 ordering box below — user approved the
> reversal).** The naive fused selector — *least colour whose cell some resolver collapses to `≤ 1`* — **is valid**,
> and two of the three feared complications dissolve on inspection:
> 1. **No new equivariance architecture.** `①b`/`①c` for the guarded object ALREADY route through
>    `Stall.StallEquivariant` (`Residue.narrowFnEquivariant_guardedRef` takes `hse`), so "per-cell resolvability
>    transports" is the **same hypothesis class**, discharged by the **same P1 instances** — their proofs use only
>    cell-transport facts that hold for *any* colour class, not just the least one. Colour values are canonical
>    (`targetColour_transport` is a value equality), so "least resolvable colour" transports.
> 2. **No `Supply` type change.** The resolver layer is already cell-generic (`Consume.consume` maps
>    `rep (verified S adj χ)` over the **passed** `B`; `verified` is cell-independent; `Force.keepMin` generic).
>    Only the supply *instances* harvest from `branches χ` internally — widen the harvest to **all non-singleton
>    cells**: cells partition the vertex set, so the widened table is `≤ n·(n+1)^d = tableBound n d`, the bound
>    `SupplyCost.lean` **already proves** (it only ever used `|branches| ≤ n`). The proved `②` bounds carry over
>    verbatim; equivariance keeps the same choice-free shape (the enumeration is still structurally characterised).
> 3. **⟹ the "probe per cell = product" risk does not materialize** (it assumed re-invoking the harvest per cell).
>    ONE all-cells harvest per node; the probe filters one shared `verified` list; per-cell orbit-BFS/`keepMin`
>    **sums over a partition of `V`** — the same form as today's consume term. **Hence the ordering argument
>    reverses**: every `branches`-anchored statement F2/F3/P3c-2nd-half add is future rework, so the interface
>    change comes FIRST (fold-tower plan already sequences F3 with it).
>
> **⚠ NO EXPONENTIAL IS REINTRODUCED — read the branching accounting exactly.** The widening enlarges the per-node
> **candidate table** (poly-bounded, billed in `CostM`), never the descent's fan-out: sel commits to **one** cell,
> and only one already narrowed to `≤ 1` branch — the guard's `resolvedAll_guard` is **absorbed into the selector**
> (`[] = flag` when NO cell qualifies = the true mutual stall). Single path of `≤ n+1` nodes exactly as today
> (each step still individualizes one vertex of a non-singleton cell ⟹ `ncol` strictly increases). The probe
> examines `≤ n` cells per node but **descends into one** — probe work is additive per node; there is no tree.
> Measured constants rise (the least cell is usually smaller than `n`); the proved asymptotics do not.
>
> **Design pins (binding for the build):**
> - "Makes progress" = **narrows to `≤ 1`** — NOT "narrows strictly" (a cell cut 5→2 is still a stall; poly-AND-flag).
> - **Anchor = the node-level narrowing** (`NarrowFn` — `①c` already works there via `guardedRef`): generalize
>   `descend` to a node resolver `adj → χ → CostM (List (Fin n × Colouring n))` (`[] = flag`), each kept child
>   **handed its already-computed refined colouring** — ONE interface change covers §6.1 **and** §6.4, and the
>   probe's refinements ARE the children's (the probe pays for itself). Obligations: **properness** (children lie
>   in one non-singleton cell; the handed colouring `= refineV rf (indivOne χ v)`, a proved per-instance equation)
>   + conditional **`NarrowFnEquivariant`**. Old object = the blind instance `fun adj χ => narrow R adj χ` +
>   per-child refine — an **exact `CostM` equation**, the migration safety net.
> - **Widen `Descend.Reaches.step`** (`v ∈ branches χ` → `v` in ANY non-singleton cell) and let
>   `ValidPath`/`handled_of_seal_selected` follow sel — else `reaches_pathCol`/`handled_of_seal` silently miss the
>   new object. The `∀ T CellsAreOrbits` hook absorbs the widening unchanged.
> - `Handled`/`CellResolved` become sel-aware ⟹ the residue **deflates** (the point of the fix).
>
> **▶▶ BUILD STATE (2026-07-17) — increments 1+2 LANDED (`ChainDescent/Select.lean`, in `build.sh`, axiom-clean;
> theorem index descriptions filled).** What exists, and exactly where a fresh reader continues:
> - **Inc 1 (the interface + the safety net):** `NodeRes` (`adj → χ → CostM (List (Fin n × Colouring n))`,
>   `[] = flag`), `descendS` + the four val/cost equations + `descendS_val_stall` (the flag channel, stated once),
>   `blindNode` (today's per-node step, packaged), ★ **`descendS_blind`** — `descendS (blindNode rf R) = descend
>   rf R` as an **exact `CostM` equation** (value AND cost), `canonFormS?_blind`/`descentCostS_blind` at top level,
>   and `NodeProper` (partner exists + the hand-forward equation `vc.2 = refineV rf (indivOne χ vc.1)`) with its
>   blind discharge.
> - **Inc 2 (the transport pass):** `descendS_sound` ⟹ `soundOptS_canonFormS?` (**①a unconditional** — soundness
>   never inspects the hand-forward), `NodeTransportAt`/`NodeTransport` (the fuel-graded node contract, exact
>   mirror of `NarrowTransport`), `descendS_transport`, capstone **`isCanonicalFormOptS_canonFormS?`** (①a/①b/①c
>   modulo `RefineEquivariant` + `NodeTransport`; `canonFormS?_complete` + `canonFormS?_flag_iso_invariant` free),
>   and the two feeding routes: `nodeTransport_of_nodeEquivariant` (equivariant instances) and ★
>   **`nodeTransport_blindNode`** (conservativity — every proved `NarrowTransport` instance, i.e. consume for every
>   supply / force via `KeyEquivariant` / the guarded composite, discharges the new contract at the blind instance
>   with no new proof).
> - **Inc 3 (NEXT — the fused instance `selNode key S`):** probe cells in colour order; commit to the least colour
>   whose cell the mixed resolver collapses to `≤ 1`; `[]` when none (= the true mutual stall). Needs (i) the
>   **all-cells harvest** variants of the supplies (widen `lookTable`/`deepTable` seeds from `branches χ` to all
>   non-singleton-cell vertices — same `tableBound n d`, `SupplyCost.lean` counting carries verbatim); (ii) its
>   `NodeTransport` discharge via the **covering argument mirroring `Residue.coveringOfAt_guarded`** (the consume
>   half's `rep` pick is not equivariant, so the equivariant route does NOT apply; the chosen-colour transport comes
>   from the same per-cell facts `StallEquivariant` already provides). **Acceptance criteria (bind the build to
>   these):** (a) *no strength increase* — the fused object answers wherever the guarded blind object answers
>   (same key, same supply): "SOME cell narrows to ≤ 1" is strictly weaker per node than "the LEAST cell narrows to
>   ≤ 1"; (b) an **exposure-dependency witness** in `Regression.lean` — a graph where the blind object flags and the
>   fused object answers (cell `A` unresolvable until individualizing in cell `B` exposes it); (c) *no exponential* —
>   fan-out `≤ 1` by construction, probe billed in `CostM`, measured in `PerformanceTest`.
> - **Inc 4:** widen `Reaches.step`/`ValidPath` (see the pin above). **Inc 5:** sel-aware `Handled`/`CellResolved`
>   (+ cost bounds via the `SupplyCost` counting). Contract-def migration (`Covering`/`CoveringAt`/`CoveringOfAt`
>   restated against the node anchor) can proceed lazily — the conservativity bridge means nothing blocks on it.

> **⊘ SUPERSEDED — ⚠ ORDERING (2026-07-15 audit): this comes AFTER `P3c`, not "together" as an earlier note said.** A
> resolver-aware selector must probe the supply **per cell**. With the unpruned `deepMatchSupply d` that probe is
> `n^{O(d)}` *per cell*, so the selector multiplies the supply cost by the cell count — the "product-not-sum risk"
> below, made concrete. With a **pruned** supply the probe reuses the already-harvested group, so the risk largely
> evaporates. Build the cheap supply first. *(The premise — per-cell harvest re-invocation — is what the 2026-07-17
> pass dissolved.)*

`descend` targets the **least non-singleton colour** (`branches`/`targetColour`) — a fixed rule that **does not ask
whether the resolvers can act on that cell**. The guard then flags if *that* cell is unresolvable. But a node can
carry several non-singleton cells, and exposure-dependency is exactly:

> cell `A` (least colour) is resolvable by **neither** route, while cell `B` **is** — and individualizing in `B`,
> then refining, **exposes** what `A` needed.

The object **flags at `A`**, on a graph an interleaved engine would canonize. A **spurious flag**: sound, polynomial,
needlessly weak. Consequences to keep straight:
- **`Stall.stalled` currently means "the LEAST-COLOUR cell stalled", NOT "the node stalled".** It is not yet the
  mutual stall.
- **`Residue.Handled` is therefore STRONGER than it should be**, so `Residue` is correspondingly **too big**.
  (`residue_if_flag` remains true; the residue it implies is inflated.)

**THE FIX (approved by the user):** make cell selection **resolver-aware** — pick the least-colour cell that is
**resolvable**, flag only at a **true mutual stall** (no cell resolvable). Retrying a cell and getting "still don't
know" is an **efficiency** problem, not a correctness one. Concretely: replace `branches` in `descend` by a
**selector parameter** `sel : AdjMatrix n → Colouring n → List (Fin n)` carrying
(i) an **equivariance** obligation (so `①c` survives — "least-colour *resolvable* cell" is still iso-invariant) and
(ii) a **properness** obligation (nonempty ⟺ non-discrete; contained in one cell).
`branches` becomes the default (blind) instance, so **everything built so far is its special case**.
⚠ This touches the contract definitions (`Covering`, `CoveringAt`, `CoveringOfAt`, `NarrowTransport` all mention
`branches`). It is the one remaining change to the **core object**.

### 6.2 ★ The oracle's REACH is fixed (`P2`); what is left is its **COST** (`P3c`)

> **▶ Status 2026-07-14, third pass.** The *reach* problem below is **SOLVED** by
> `DeepMatchSupply.deepMatchSupply d` — `C₄` flags at `d = 0` and **answers at `d = 1`**. What replaced it is a
> **cost** problem: `n^{O(d)}`, a 125× net loss on `C₇`. **The live item is `P3c` (§6.2b), not this section.**
> Everything from here to §6.2b is the *derivation* — read it for the dead routes, which are load-bearing.
`MatchSupply.matchSupply` is `matchOracle`'s **construct-and-check** colour match rebuilt over `(adj, χ)`. It is
honest and proved:
- **`matchCandidate_eq_of_isColAut`** — the construction does not merely *find* an automorphism, it **reconstructs
  exactly the one that exists**;
- **`cellIsOrbit_matchSupply`** — at a **`Discretizing`** node, an orbit cell is certified as one (the cascade
  oracle's `hdisc`-only firing, **no `CellsAreOrbits`, no localisation**);
- it is **structural**, so it also **repairs `①c`** (`StallEquivariant`).

> **⚠⚠ MEASURED: it FLAGS ON A 7-CYCLE.** *(⚠ This box UNDERSTATES the limit — see the SHARPER box immediately
> below, which supersedes its diagnosis. Retained because the measurement is real and `#guard`ed.)* `Discretizing` —
> the cascade oracle's `hdisc` — is **far stronger than it sounds: it EXCLUDES CYCLES.** Individualizing one vertex
> of `C₇` and refining leaves `{0},{1,6},{2,5},{3,4}` — **not discrete** — so the oracle constructs nothing, consume
> cannot fire, force cannot fire (orbit cell), and the descent stalls. `F12` *does* discretize in one step and
> answers. Both facts are `#guard`ed.

**⟹ The residue was inflated by this gap, not by anything hard.** `Residue.Handled` was far smaller than the
architecture intends, and a *cycle* was enough to expose it. (**Fixed by `P2`.**)

> **⚠⚠ SHARPER, AND IT CHANGES THE FIX (2026-07-14, second pass).** "It flags on a 7-cycle" *understates* the
> limit. If `α` is a colouring-preserving automorphism **fixing** a branch vertex `v`, it preserves `indivOne χ v`,
> hence (refiner equivariance) preserves its refinement; a **discrete** colouring preserved by `α` forces `α = 1`.
> So **`Discretizing` ⟹ every branch vertex has a TRIVIAL POINT STABILIZER**, and with `CellIsOrbit`
> (transitivity) `cellIsOrbit_matchSupply` fires **only on a REGULAR action**. `C₇` fails not because it is a
> cycle but because `Aut(C₇) = D₇` has a reflection fixing each vertex. ⟹ **the residue is inflated by every graph
> with a non-trivial point stabilizer — i.e. most of them.** (Direct corollary of
> `aut_trivial_of_discrete_warmRefine`; worth landing as a theorem to state the boundary precisely.)
>
> **And that says what the supply must DO: recover `stab(v)`.** The generators consume is missing live *inside the
> point stabilizer*, which comparing branch `v` to branch `w` can never produce. Hence "cross-branch".

**⛔ THE FIX IS *NOT* TO PORT `matchOracleSet` / `matchOracleSeq` (§C.6/§C.8) — THE PROJECT HAS PROVED THEM DEAD.**
`CascadeOracle.lockstep_disc_imp_stab_trivial` (axiom-clean, in the build) says: `LockstepExpandSeq ∧ hdiscSeq ⟹
stab_{Aut_D}(v) = 1`. I.e. **an equivariant (canonical-choice) multi-step deepening's two completeness hypotheses
are jointly satisfiable ONLY where one rep already kills the residual** — exactly the regime `matchSupply` already
covers. §C.8's own preamble adds that the *set* variant merely relocates the obstruction (`hdiscSet` false →
`LockstepExpandSeq` false). An earlier draft of this section cited that theorem as *motivation* and then pointed at
the very machinery it refutes; porting it buys **nothing provable**.

**Nor does the C# port survive.** `ReplayDeepening` individualizes `members[0]` — the **lowest-index** vertex of
the cell carrying the recorded id — which is *not* equivariant. It works empirically (K7 941 → 1) because an
unverifiable candidate simply leaves the reps separate (sound over-split); it is a **heuristic with verification**,
and it cannot support a completeness theorem of the `LockstepExpandSeq` shape.

**⛔⛔ AND THE STABILIZER CHAIN CANNOT BE THE GUARDED OBJECT EITHER — the deciding constraint (2026-07-14, P2).**
A stabilizer chain must **pick a vertex** inside a cell to recurse into. But a cell's members are *precisely* what
1-WL cannot distinguish, so **no iso-invariant function picks one** (lowest-index is labelling-dependent: `min(σ·C)
≠ σ(min C)` — this is the same error `indivOne`'s index-freeness exists to avoid). Hence the harvested generators
are **not `σ`-conjugates**, `SupplyTransport.GensEquivariant` fails, and — because `Residue.narrowFnEquivariant_
guardedRef` routes **`①b` AND `①c`**, not just the flag, through `Stall.StallEquivariant` — **the guarded object's
CORRECTNESS breaks**, not merely its cost. It would hold only *conditionally on the supply's own completeness*
(= localisation), which is circular for a `①` obligation. The C# escapes this only because its pruning is a pure
**covering** move (value-invisible ⟹ history-dependence is harmless) and its flag is a **budget**, not a stall.

> **⚠ DISTINGUISH: choosing a CELL is canonical; choosing a VERTEX inside one is not.** `targetColour` (least
> non-singleton *colour*) transports — colours are 1-WL values, a function of the coloured graph — so the
> **resolver-aware selector of §6.1 is perfectly valid**, and stacking "…that a resolver can act on" onto it keeps
> it canonical. It is the *within-cell vertex* pick that is illegal. (`Consume.rep` is such a pick and is openly
> non-equivariant — licensed **only** because covering makes it value-invisible.)

**⟹ THE FIX, BUILT: `ChainDescent/DeepMatchSupply.lean` — make NO choice at all.** Enumerate **every**
individualization sequence of length `≤ d` on both sides and colour-match all pairs. Equivariance is then *free*,
because the search space is characterised **purely by length** (`mem_allSeqs_map`), so `σ` maps it onto itself.
`lockstep_disc_imp_stab_trivial` does not apply: it refutes an equivariant *choice function*, and there is none.
- **Firing = `SeparatesAt adj χ d`** — every branch vertex plus *some* `≤ d` more discretizes. By **P0's
  confluence** this is the same condition as the cascade oracle's `CascadesAt` / the seal's `SeparatesAtBoundedBase`.
  **✅ P2b (step 1) LANDED — `ChainDescent/SealDepthBridge.lean` (2026-07-15, axiom-clean, in `build.sh`).** Until it,
  **no theorem produced `SeparatesAt`** (it was only `#guard`ed on cycles), so `SealBridge` bridged only
  **localisation** (`CellsAreOrbits → horb`) and the sealed families could not populate `Residue.Handled`. The bridge
  is one monotonicity fact — *individualizing more only refines, and refining a discrete colouring keeps it discrete*
  (`deepCol_cons_refines`, via `warmRefineR_mono` transferred through `SealBridge.warmRefineR_samePartition`):
  - **`separatesAt_of_cascadesFrom`** — `CascadesFrom adj χ k ⟹ SeparatesAt adj χ k`, **same bound `k`** (the witness
    sequence for *every* branch vertex is the one set `S₀.toList` — prepending the branch vertex only refines).
  - **`cellIsOrbit_of_cascadesFrom_of_horb`** — depth (`CascadesFrom`) + localisation (`horb`, imported by
    `SealBridge.horb_of_cellsAreOrbits`) ⟹ `deepMatchSupply k` **fires** at that node. The depth analogue of P0's
    `cellIsOrbit_of_cellsAreOrbits`.
  - **✅ P2c LANDED — same file, §4 (2026-07-15, axiom-clean).** The connection is a single **exact equality**, not a
    partition argument: **`deepCol adj (pathCol adj p) s = pathCol adj (s.reverse ++ p)`** (`deepCol_pathCol`) —
    deepening the descent's node colouring is *literally* the colouring at the longer committed path, because
    `pathCol adj (v :: p)` is definitionally `warmRefineR adj (indivOne (pathCol adj p) v)` = `deepCol`'s step. Then
    `SealBridge.pathCol_samePartition` reads the partition as `warmRefine ∘ individualizedColouring`, and a superset
    individualization stays discrete ⟹ **`cascadesFrom_pathCol_of_cascadesAt`**: the seal's `CascadesAt adj (constP n)
    k` gives `CascadesFrom` at **every** descent node from one global `S₀`. Packaged: **`cellIsOrbit_pathCol_of_seal`**
    — depth (`CascadesAt`) **and** localisation (`CellsAreOrbits`), both seal imports, fire `deepMatchSupply k` at the
    node. **⟹ `theorem_1_HOR_*` / the four form families / `viaSpielman` now literally import.** (`Refine.constP n` *is*
    `fun _ _ => POE.unknown`, the seal's own PMatrix — no translation needed.) ~~The remaining gap to `Residue.Handled`
    is now only that the seal hypotheses hold **at every reachable node** (a whole-descent statement), not vocabulary.~~
    **✅ CLOSED as a statement (2026-07-16, `HandledBridge.handled_of_seal` — see the §4 update box):** the
    whole-descent statement is now the theorem `CascadesAt + (∀ T, CellsAreOrbits) ⟹ Handled`, with the reachable-node
    induction (`reaches_pathCol`) discharged. What remains is **per-family localisation** — `∀ T, CellsAreOrbits` for
    each sealed family (the HOR theorems give depth + endpoint localisation only).
  - **▶ TODO — `viaSpielman` POC import (small; mostly proof-of-concept).** `Cascade.SeparatesAtBoundedBase S bound`
    is **definitionally** `CascadesAt (schemeAdj S) (Refine.constP n) bound` (same `∃ S₀ ≤ bound, Discrete(warmRefine ∘
    individualizedColouring)`; `constP n = fun _ _ => POE.unknown`). So `cascadesFrom_pathCol_of_cascadesAt` /
    `cellIsOrbit_pathCol_of_seal` apply **directly** at `adj := schemeAdj S`: a one-lemma bridge
    `SeparatesAtBoundedBase S bound → CascadesAt (schemeAdj S) (constP n) bound` (unfold) then the P2c capstone ⟹
    `deepMatchSupply bound` fires on the scheme's own adjacency at a localising node. This demonstrates the **full
    ladder including the sub-exp top** (Spielman's `bound = Õ(n^{1/3})` — ⚠ scope corrected 2026-07-16: that bound
    is citable for **claw-bounded** primitive SRGs only; the Neumaier-exceptional Steiner/Latin-square families have
    base `Θ(√n)` and exit via Cameron — see the corrected `viaSpielman` docstring / citation register); it is NOT the
    poly workhorse — the **poly**
    pieces (`theorem_1_HOR_cfi_oddDeg` at bounded tw, `theorem_2_HOR_*` for the metric/DRG family) are what the real
    construction is built from. ⚠ This fires on `schemeAdj S`, not yet on an arbitrary graph *realizing* S — that last
    hop is the `RouteCTransport.separatesAtBoundedBase_transport` layer, out of scope for the POC.
  `matchSupply` is the `d = 0` case (`separatesAt_zero_iff`) — a strict generalization.
- **MEASURED: `C₄` flags at `d=0` and ANSWERS at `d=1`** (`Regression.lean` §7 — do not delete); `C₇` likewise.
  **Nothing was re-proved**: `①`/`②` are quantified over an arbitrary `Supply`, so raising `d` moved only
  `Residue.Handled`'s boundary. That is the architecture working.
- **⚠ COST IS `n^{O(d)}`** — poly for bounded `d`, **quasipoly at `d = Θ(log n)`, sub-exp at Spielman's
  `d = Õ(n^{1/3})`: exactly the seal's ladder, and no better.** Measured on `C₇`: answers at `d=1` for **949 819**
  vs **7 568** exhaustive — a 125× **net loss**. *Firing is not paying*, again. Not a `②` problem (the bound is
  unconditional and the `n^d` sits honestly inside `c₂`); a **quality** problem.

### 6.2b ▶ P3 — the ORBIT-PRUNED FIXPOINT: how the `n^d` becomes a SUM

> **✅ P3a + P3b LANDED — `ChainDescent/OrbitPrune.lean` (2026-07-14). The foundation is built; only the fixpoint
> (P3c) remains, and it now carries ZERO `①` exposure.**
>
> **⚠ THE PLAN BELOW HAD A HOLE, AND THE FIX CHANGES THE SHAPE OF P3c.** A pruned enumeration keeps **one sequence
> per orbit** — i.e. it **picks a representative** — so its generator *list* is **not** pointwise `σ`-conjugate to
> the unpruned one (`σ` sends the chosen rep to a *different* rep of the conjugate orbit).
> **`SupplyTransport.GensEquivariant` is therefore UNAVAILABLE to any pruned supply**, and re-deriving `①c` from
> scratch for a fixpoint construction would be brutal. Do not attempt it.
>
> **The escape — `OrbitPrune.lean` §1, THE REDUCTION.** Everything downstream of the supply — `narrow`, `descend`,
> `canonForm?`, `Stall.stalled`, `Consume.CellIsOrbit`, `Residue.Handled` — reads the supply through **exactly one
> channel**: `Consume.rep (verified S adj χ)`, and `rep` is the least element of an **orbit**
> (`mem_orbit_iff_wordReach`). Hence
>
> > **`SameOrbits S₁ S₂` ⟹ the two guarded canonizers are the SAME FUNCTION** (`canonForm?_eq_of_sameOrbits`)
> > ⟹ **`①a`/`①b`/`①c` transfer wholesale** (`guarded_mixed_canonizer_of_sameOrbits`), and so do
> > `StallEquivariant`, `CellIsOrbit`, `Cost.CellResolved` and `Residue.Handled` — **the residue is unchanged.**
>
> **⟹ a pruned supply's ONLY obligation is the group-theoretic one: it proves the same orbits.** No equivariance
> proof, no `①` re-derivation. (And this reduction is reusable by **any** future supply optimization, not just this
> one.)
>
> **P3b — the license itself** (`OrbitPrune.lean` §4, and the identity below made precise, both directions):
> - **`deepCandidate v sv (g w) (g·sw) = g · deepCandidate v sv w sw`** (`deepCandidate_left_mul`)
> - **`deepCandidate (g v) (g·sv) w sw = (deepCandidate v sv w sw) · g⁻¹`** (`deepCandidate_right_mul`)
>
> for any `g` the supply has already **verified**. So a pruned-away candidate is `g · c` with **both** factors in
> the generated group ⟹ the group is unchanged. **Both sides of the enumeration may be pruned** (the `v`-side too —
> that is what makes it a sum and not merely a `|cell|`-fold saving). And `CellIsOrbit` is stated via **`WordReach`**
> — *a word in the generators* — so the pruned-away element survives as a **product**.
>
> **✅ P3c FIRST HALF LANDED — `ChainDescent/PrunedSupply.lean` (2026-07-16, axiom-clean, in `build.sh`).** The
> reference-matching supply: match from **one** discrete reference entry, not all pairs — `|table|` matches, not
> `|table|²`. The `SameOrbits` proof needed **no** online Schreier-Sims and **no** composition identity, because the
> enumeration is **length-closed** (`α·(v,s)` is a table entry for any automorphism `α`, `mem_allSeqs_map`): the two
> **verified sets are equal as membership sets** (`verified_mem_iff`) — pruned⊆deep (a reference match is an all-pairs
> candidate), deep⊆pruned (a verified `g` = `matchCol r (g·r)` by `matchCol_self_transport`, and `g·r` is a table
> entry). Equal verified sets ⟹ same `WordReach` (`wordReach_congr_mem`, membership-only) ⟹ `SameOrbits`
> (`sameOrbits_deepMatchSupply`) ⟹ `①`/`②`/`③` transfer via `guarded_mixed_canonizer_of_sameOrbits`
> (`prunedSupply_guarded_canonizer`, no equivariance proof on the pruned supply). **MEASURED (Cₙ root, d=1):**
> supplyCost `C₇ 192080 → 41160` (4.7×), `|verified| 1764 → 42` (42× — **subsumes the dedup win**). `Regression` §7
> `#guard`s `gPruned 1 C4 = gDeep 1 C4` (behavioural `SameOrbits`). **⚠ This kills the `|table|²` pairing but NOT the
> `n^d` inside `|table|`** (the sequence enumeration / refinement term — now the dominant cost, unchanged).
>
> **▶ WHAT IS LEFT (P3c second half):** collapse the `n^d` sequence enumeration to the measured `seqReps` (the online
> orbit-pruned sequence growth — the harder increment; see the design below). The reference-matching win and the
> sequence-pruning win **compose** (one cuts `|table|²→|table|`, the other cuts `|table|` itself).
>
> **✅ MEASURED — the headroom is REAL (2026-07-15 derisking, root colouring of `Cₙ`, `d=1`):**
>
> | graph | `T`=table | `#orbits(G)` | `vPruned` (v=rep) | `\|allSeqs\|` | `seqReps` (seqs up to `G`) | raw `\|G\|` | `\|G.dedup\|` |
> |---|---|---|---|---|---|---|---|
> | `C₅` | 30 | **1** | 6 | 6 | **2** | 400 | 10 (=`\|D₅\|`) |
> | `C₇` | 56 | **1** | 8 | 8 | **2** | — | 14 (=`\|D₇\|`) |
>
> Three findings, all load-bearing: **(a)** `#orbits(G) = 1` — full localisation confirmed (the whole cell is one
> orbit). **(b)** the **sequence enumeration collapses**: `seqReps = 2` while `|allSeqs 7 1| = 8` — the depth-`d`
> sequences are only a **handful of `G`-orbits**, not `n^d`. This is the `n^d → sum` collapse, *measured*, and it
> grows with `d`. **(c)** representative work `≈ vPruned · seqReps ≈ 8·2 = 16` entries vs `T = 56`, so the match term
> is `≈ reps² ≈ 256` vs `T² = 3136` — **~12× at `d=1`, widening with `d`.** ⟹ **P3c is viable; build it.**
>
> **⚠ THE §6.2b BATCH-FIXPOINT SKETCH IS SUPERSEDED — do ONLINE pruning instead (2026-07-15).** The earlier worry
> ("with `G=∅` no pruning until depth `d`, so a single pass pays `n^d`; only the *fixpoint* recovers it") is resolved
> by **online** pruning: maintain the growing verified group `G` *during* one pass and skip an entry the moment it is
> a `G`-orbit-mate of one already processed. `G` **saturates early** (after `≈ reps²` matches reveal `Dₙ`), and every
> later entry is skipped — so the discovery cost is `O(reps²)`, not `O(T²)`, in a **single pass, no batch re-run.**
> This wins even at `d=1` (which the batch-fixpoint could not). The `SameOrbits` proof still rides the **P3b license**:
> a skipped entry's candidate is `g·c` with `g` a verified word ⟹ the generated group is unchanged.
>
> **▶ ORTHOGONAL FREE WIN spotted while measuring:** `deepMatchSupply`'s raw candidate list is **massively
> duplicated** — `|G| = 400` where `|G.dedup| = 10` on `C₅`. A `List.dedup` on the candidate list (or emitting only
> distinct `matchCol` results) is a ~40× constant-factor cut on the harvest, independent of pruning, and needs **no**
> `SameOrbits` (same *set* of generators ⟹ same orbits trivially). Low-hanging; do it first.
>
> **✅ Brick landed (2026-07-16): `IsColAut` is a subgroup** — `IsColAut.one`/`comp` existed; `IsColAut.inv` added
> (`Consume.lean`). The pruning license needs this: a candidate reconstructed as a product/conjugate of verified
> generators must itself certify as an automorphism.
>
> **⚠⚠ THE SECOND HALF IS A GROUP-CLOSURE PROOF, NOT SET-EQUALITY — measured and pinned down (2026-07-16).** The first
> half worked because the verified sets were *equal* (`verified_mem_iff`). **Sequence pruning breaks that**, and the
> measurement shows exactly how: keeping the group-canonical sequences on `C₇`/`d=1` retains **14 of 56** entries, and
> matching *within* the kept set finds **10** automorphisms — **not all 14** (`|D₇|`). The missing 4 are **words** of
> the 10. So the pruned generators are a **strict subset** of the auto group that must be shown to **generate the same
> orbits** — a Schreier-Sims-grade closure, not the clean membership-equality of the first half. Concretely (the
> cleanest provable route found): reference-match with a **`W`-side orbit prune** — candidates `{matchCol ref q}` for
> `q` a rep of the found-group's orbit of `(branch, seq)` — and prove `⟨pruned⟩` reaches every `matchCol ref q` via
> **`OrbitPrune.matchCol_left_mul`** (`matchCol ref (g·q) = g · matchCol ref q`) closed under a **BFS on the found
> group** (the same convergence shape as `Consume.orbit_closed`). The circular "`g` is a verified word" is discharged
> by the online invariant (an entry is skipped only once its reducing `g` is already generated). This is real,
> de-risked work — but it is **~200+ lines of orbit-closure**, materially harder than everything in P3 so far.
>
> **⚠ NAIVE ORBIT-PRUNING OF ENTRIES IS WRONG — do not attempt it (2026-07-16).** "Keep one entry per `G`-orbit"
> destroys auto discovery: the autos come from matching an entry against its `G`-**image** (same orbit), which that
> pruning deletes, so matches between distinct orbit-reps yield only the identity. The correct object is **nauty-style
> tree pruning** (keep the search tree, harvest autos from ref-vs-node matches, prune the *subtrees* of nodes proven
> auto-equivalent to a kept node) — whose autos in a pruned subtree are **conjugates** of kept ones.
>
> **▶ SCOPE NOTE — the first half already closes the POLY regime.** At **bounded `d`** the reference-matching supply
> is already polynomial (`|table| = |cell|·n^d`, poly for fixed `d`); the `|table|²→|table|` cut is a constant-factor
> improvement there. The second half's payoff is the **quasipoly→poly** ladder-break at `d = Θ(log n)` (turning `n^d`
> into a sum), **conditional on localisation at every level** — the seal's own open hypothesis. So it is the
> high-value-but-conditional piece, not on the critical path for the poly-or-flag headline.
>
> **(Original sketch, retained for the mechanism — but see the trap above for why "prune the table" is the wrong
> object):** prune the `(branch, sequence)` table by the orbits of the group found so far; harvest; repeat until
> stable — monovariant = the number of orbits on the table, which strictly decreases, so `|table|` rounds suffice,
> exactly the shape of `Consume.orbit_closed`'s convergence proof.

---

**(Original P3 sketch, retained — the mechanism is unchanged, only the correctness route above is new.)**
Nauty's orbit pruning **is** canonical *at the group level*, and that is the escape. The key identity:

> **`rankSwap ψᵥ (g · ψ_w) = g · rankSwap ψᵥ ψ_w`** — changing a deepening choice *within an orbit of the group
> already found* changes the candidate only by **left-multiplication by a known element**, so the **generated
> group is unchanged**.

So one may enumerate **one sequence per orbit under the group found so far**, iterate to a fixpoint, and still get
a canonically-determined *group* — enough for `StallEquivariant` (which reads only the orbit partition, via
`Consume.rep_eq_iff_wordReach`), hence enough for the guard. Under **localisation** each level has one orbit, the
enumeration collapses to a **single path per branch**, and the cost becomes the **sum** `|cell| · d · n³`; without
localisation it degrades gracefully back to the full enumeration. Note `CellIsOrbit` is stated via **`WordReach`**
(a *word* in the generators), which is exactly what lets a pruned-away `α` survive as a product.
**This is the real prize, and it reuses every P2 brick** (`deepCol`, `deepCandidate`, the reconstruction theorem,
the equivariance machinery). Its poly bound will be *conditional on localisation* — which is fine: `②` stays
unconditional because `supplyCost` is whatever the supply reports.
**Standing notes for whoever builds `P3c`:**
- ⚠ **A `GensEquivariant` supply must be STATELESS** (a pure function of `(adj, χ)`) — an accumulating store breaks
  `①c`. **But the pruned supply does NOT use `GensEquivariant` at all** (it cannot; see the ⚠ box above): it runs on
  `OrbitPrune.SameOrbits` instead. It is still a pure function of `(adj, χ)` — the "state" is an internal fixpoint,
  not history carried across nodes.
- **The harvest must live INSIDE the `Supply`.** The guarded descent is a **single path** with no siblings, so there
  is no cross-branch structure left in the descent to hang it on. **⟹ the `Supply` IS the cascade+harvest engine,
  and its polynomial cost IS T-C.**
- **Termination of the fixpoint:** monovariant = the number of `⟨G⟩`-orbits on the `(branch, sequence)` table, which
  strictly decreases each non-stable round ⟹ `|table|` rounds suffice. Same shape as `Consume.orbit_closed`.
- **`supplyCost` bills the harvest into `descentCost`**, so any product-not-sum blow-up **shows up in the measured
  cost** rather than hiding. Measure it (`PerformanceTest.lean`) — do not assume it.
- ★ **`P0` means the seal's half is an IMPORT, not a re-proof.** The supply needs *localisation* (`CellsAreOrbits`)
  and *depth* (`SeparatesAt`); `SealBridge.horb_of_cellsAreOrbits` hands the first straight through from
  `theorem_1_HOR_*` / the sealed families / Spielman. Only the **harvest** is new work.
- **An unused free fact, recorded in case it is wanted:** `leafMatrix adj χ i j = adj.adj (rankInv χ i) (rankInv χ j)`,
  so two **discrete** colourings with **equal leaf matrices** have a `rankSwap` between them that is an automorphism
  **unconditionally**. (A leaf-comparing supply would get soundness free; the open crux is whether the constructed
  permutation preserves `χ` and maps `v ↦ w`. Not needed for `P3c` — verification already makes soundness free.)
- ⚠ The seal "consumes all visible symmetry except Cameron / node-4" is itself **modulo {G3 citation + `hImprim`}** —
  keep that in the statement.

### 6.3 The rigid key — **nothing exists beyond `lookaheadKey`**
§11.12's P1–P4 are **not started** in Lean. The force route's *only* ① obligation is `KeyEquivariant`; its **firing**
obligation is the exact dual of consume's: a `Force.KeySeparates` predicate (the key separates every non-automorphic
pair in the cell). **Build consume first** — force is its mirror, so a design error there will surface by comparison
(this is exactly how §6.2's one-step limitation was found).

### 6.4 The duplicate-refine loss — force FIRES but does not PAY
`lookaheadKey` computes, for each branch `v`, **exactly** the refinement the child node then recomputes from
scratch — and `matchSupply` computes it a **third** time. Measured on `F12`: exhaustive **22477**, forced **26066** —
a **net loss**. (The old "22477 → 5186" was an artifact of billing an arbitrary key a flat `n³`; `Key` now carries
its cost, and `②` can see the difference.) **Fix:** let a resolver **hand its look-ahead forward** — a `descend`
signature change, and **the same one §6.1 needs**. Do them together.
> **▶ 2026-07-17: "together" is now ONE interface, not two coordinated changes** — the §6.1 node resolver returns
> `List (Fin n × Colouring n)`, i.e. each kept child arrives WITH its refined colouring, so the hand-forward IS the
> selector signature. The resolvability probe computes exactly these refinements, so the probe pays for itself and
> the F12-style triple-computation collapses to one. See the §6.1 design-pass block.

### 6.5 The `Publication` opaque-swap — now unblocked
Substitute the real `Descend.canonForm?` for the `opaque` stub. `unhandledResidue_nonvacuous` was **unprovable in
principle** while the three residue atoms were `opaque … : Prop`; with `Residue.Residue` a **definition** it is now
provable (`Residue.residue_nonvacuous`). The atoms must be *defined* (as the complement of `Handled`), not asserted.

---

## 7. TRAPS — every one of these cost real time

1. **⚠ NEVER define anything of type `… → Colouring n`.** Lean compiles a def at the arity of its **TYPE**, and
   `Colouring n = Fin n → Nat` — so such a def **re-runs its body on every colour lookup**, and since each descent
   level closes over its parent's, the cost **multiplies per level**. `@[noinline]` does **not** fix it. **Cure:
   return a non-function-typed value** (`Refine.ColData`). *Bit three times, ~10⁴× each.*
   *Measurement traps that hide it:* a top-level `def` colouring **is** cached (isolated tests look fine), and `lean`
   **discards all `#eval` output on timeout** (one slow eval swallows the earlier ones — bisect one `#eval` per file).
2. **⚠ Recomputation you cannot see (same family).** `matchSupply` originally called `lookData adj χ v` inside *both*
   loops of its pair enumeration ⟹ **`|cell|²` refinements where `|cell|` suffice**. Materialising once cut
   `gMatch F12` from **3.5 min to ~4 s** — an **O(n) factor in the algorithm**, not the test.
3. **Vacuity is the recurring failure mode.** Check non-vacuity against probe data *before* building on any
   predicate. `NarrowProper` is satisfied by a resolver that returns the **whole cell** — soundness and totality
   certify **nothing** about firing. Every firing claim needs a **graded** theorem (partial power ⟹ partial progress)
   *and* an observed `#guard`.
4. **State firing GRADED first, endpoint second.** `consume_singleton_of_cellIsOrbit` / `forceBy_singleton_of_
   separating` are the **perfect endpoints**; alone they read as *"only a perfect solver counts"* and say **nothing**
   about the realistic middle. The unconditional graded forms (`rep_eq_of_wordReach`, `forceBy_narrows_of_key_ne`,
   `forceThenConsume_narrows_of_partial`) are what make the ② ledger **additive**.
5. **`omega` treats products as ATOMS** and does not normalize them: `(fuel+2)*K` and `(fuel+1+1)*K` are *different
   atoms*. Write auxiliary bounds in the goal's exact syntactic form.
6. **Scale discipline in tests.** `lookaheadKey` costs **~1 s per key evaluation at `n = 12`**. Force's firing needs a
   1-WL cell that is **not an orbit** — and **1-WL is a single cell on every regular graph** — so *any* regular
   **non-vertex-transitive** graph works. `Regression.G8` (cubic, 8 vertices) is ~8× cheaper than the Frucht graph.
   (F12 was originally chosen as the smallest *asymmetric* regular graph; **asymmetry was never needed**.)
7. **⚠ A CHOICE IS THE THING THAT BREAKS `①`, not statefulness.** Three separate designs died on it (the stabilizer
   chain, `matchOracleSeq`, the C# `ReplayDeepening`), each because it picked a **vertex inside a cell** — and cell
   members are exactly what 1-WL cannot distinguish. Before proposing any supply, ask: *does it choose?* If yes,
   either it is illegal, or it must run on `OrbitPrune.SameOrbits` (the choice is invisible to the **generated
   group**). **Choosing a CELL is fine** (`targetColour` transports); choosing a **vertex within** one is not.
8. **A conditional theorem whose hypothesis nothing satisfies is the recurring failure mode.** `hflag`,
   `SchemeReproduced`, `∃ gens, closure = group`, and **`StallEquivariant` until `P1`** were all uninstantiated.
   Every new obligation needs a *discharged instance* in the same pass, and a `#guard`ed non-vacuity witness.

---

## 8. Build / conventions

```
bash scripts/build.sh                      # serial full build, ~120 s, MUST be green
lake build ChainDescent.PerformanceTest    # the heavy measurements, OFF the build path (~4 min)
python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers --descriptions d.json
```
- **Run the index script from the repo root** (`/workspace`), not from `GraphCanonizationProofs/` — it fails silently
  otherwise.
- The **Description** column of `PublicTheoremIndex.md` is **human/agent-owned** (never auto-filled). Fill it for
  every row you add; the file currently has **zero blanks** in the canonizer modules.
- `Publication.lean` is the **only** file permitted `axiom`, and is deliberately **not** in `build.sh`.
