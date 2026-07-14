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
CONSTRUCTION** ⟹ **`Stall.descentCost_guard_le` is polynomial with NO hypothesis** (not on the graph, the supply, or
the key). **`poly` AND `flag`, never `poly` OR `exponential`.**

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

### 6.1 ⚠ The target-cell selector is BLIND to resolvability (fusion's live bite) — **design approved, not built**
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

### 6.2 ★ Consume is far weaker than the cascade oracle — **one step is not enough**
`MatchSupply.matchSupply` is `matchOracle`'s **construct-and-check** colour match rebuilt over `(adj, χ)`. It is
honest and proved:
- **`matchCandidate_eq_of_isColAut`** — the construction does not merely *find* an automorphism, it **reconstructs
  exactly the one that exists**;
- **`cellIsOrbit_matchSupply`** — at a **`Discretizing`** node, an orbit cell is certified as one (the cascade
  oracle's `hdisc`-only firing, **no `CellsAreOrbits`, no localisation**);
- it is **structural**, so it also **repairs `①c`** (`StallEquivariant`).

> **⚠⚠ MEASURED: it FLAGS ON A 7-CYCLE.** `Discretizing` — the cascade oracle's `hdisc` — is **far stronger than it
> sounds: it EXCLUDES CYCLES.** Individualizing one vertex of `C₇` and refining leaves `{0},{1,6},{2,5},{3,4}` —
> **not discrete** — so the oracle constructs nothing, consume cannot fire, force cannot fire (orbit cell), and the
> descent stalls. `F12` *does* discretize in one step and answers. Both facts are `#guard`ed.

**⟹ The residue is currently inflated by this gap, not by anything hard.** `Residue.Handled` is far smaller than the
architecture intends, and a *cycle* is enough to expose it.

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

**THE FIX — the supply must be a STABILIZER CHAIN.** The same theorem tells you why the index-choice is harmless
*once you know `stab(v)`*: two valid continuations differ by a stabilizer element, so the candidate is `α · s` —
still an automorphism carrying `v ↦ w`. And `stab(v)` is available, because in the descent's own vocabulary
**`Aut(adj, refineV (indivOne χ v))` IS `stab_{Aut(adj,χ)}(v)`**. So the supply recurses *down its own descent*,
harvests the stabilizer at the deeper node (where the cell is smaller and the recursion bottoms out at
discreteness), and uses it to canonicalize the colour-match at the current node. That is Schreier–Sims, and it is
what `SchemeRecoveredByDepth`'s two-phase `bs₁ ++ bs₂` already encodes.
- ⚠ **STATELESS, from `P1`.** `GensEquivariant` (which `①c` now provably needs) forbids an accumulating,
  history-dependent generator store. The supply must be a **pure function of `(adj, χ)`**.
- Cost is a **SUM**: `n` levels × `|cell|` reps × `n³` refinement — no product. `supplyCost` bills it into
  `descentCost`, so any product-not-sum blow-up would **show up in the measured cost** rather than hiding.
- Termination: the same `ncol`-increases monovariant `descend_ne_none` already uses; fuel `= n`.
- **A free algebraic fact worth exploiting** (leaf-compare variant): `leafMatrix adj χ i j = adj.adj (rankInv χ i)
  (rankInv χ j)`, so if two **discrete** colourings have **equal leaf matrices** then `rankSwap` between them is an
  automorphism **unconditionally**. Soundness of a leaf-comparing supply is therefore free, and its discreteness
  comes from *reaching a leaf*, not from a one-shot refinement — so `lockstep_disc_imp_stab_trivial` does not bite.
  The crux that could still kill it is whether the constructed permutation preserves `χ` and maps `v ↦ w`; that is
  a **cheap falsifier** (a self-contained lemma) and should be probed before building on it.
- **The cross-branch harvest can no longer live in the descent**: the guarded descent is a **single path** with no
  siblings. It must be internalized in the `Supply`. **⟹ the `Supply` IS the cascade+harvest engine, and its
  polynomial cost IS T-C.**
- ★ **`P0` means the seal's half is an IMPORT, not a re-proof.** The supply needs *localisation*
  (`CellsAreOrbits`) and *depth*; `SealBridge.horb_of_cellsAreOrbits` hands the first straight through from
  `theorem_1_HOR_*` / the sealed families / Spielman. Only the **harvest** is new work.
- **Reassurance on product-not-sum:** the descent can no longer branch at all and `supplyCost` is charged into
  `descentCost`, so any product-not-sum blow-up in the harvest **shows up directly in the measured cost**.
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

---

## 8. Build / conventions

```
bash scripts/build.sh                      # serial full build, ~110 s, MUST be green
lake build ChainDescent.PerformanceTest    # the heavy measurements, OFF the build path (~4 min)
python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers --descriptions d.json
```
- **Run the index script from the repo root** (`/workspace`), not from `GraphCanonizationProofs/` — it fails silently
  otherwise.
- The **Description** column of `PublicTheoremIndex.md` is **human/agent-owned** (never auto-filled). Fill it for
  every row you add; the file currently has **zero blanks** in the canonizer modules.
- `Publication.lean` is the **only** file permitted `axiom`, and is deliberately **not** in `build.sh`.
