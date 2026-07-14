# Mixed rigid + symmetric handling — the Lean composition track

> **What this is.** The scoping plan for pointing the **Lean** canonizer at the case that actually
> dominates: a residue with **both** symmetric decisions (consumed by Phase 1) **and** rigid decisions
> (solved by Phase 2) — i.e. `canonForm? = phase2 ∘ phase1`, proven correct on **mixed** inputs. It is the
> concrete content of the endgame's **Runtime Phase** (`chain-descent-endgame-spec.md` §3 "Runtime Phase",
> §4.3 "the consumption bridge"), sharpened by the 2026-07-10 finding that *almost every real residue is
> mixed*, so neither the pure-symmetric pole (the confinement `CertifiedSinglePath`) nor the pure-rigid pole
> (the multipede) is representative. Companion measurements + design corrections:
> `[[project_rru_cost_probe_2026-07-10]]`, `[[project_confinement_bundle_vacuity_2026-07-10]]`.
>
> **Note (2026-07-12): `phase2 ∘ phase1` is the fusion-free special case; the general model is the INTERLEAVED
> fixpoint** `…∘phase2∘phase1…` (§1 Refinement box; IR §11.11), so Stage 2's composition is a **fold over alternation
> depth**, not one append. **RRU is retired** (the sequential one-shot handoff is superseded by the mutual-stall
> fixpoint): Stage 3 plugs the rigid solver into the surviving **`Phase2.Solver` contract** (`Phase2Handoff.lean`); the
> `RRU` reachability apparatus in that file is abandoned.

---

## STATUS (read first)

> **▶ STAGE 0 STARTED — the correctness framework is LANDED (2026-07-11, `ChainDescent/CanonicalForm.lean`, in
> `build.sh`, axiom-clean `[propext, Classical.choice, Quot.sound]`).** The spec is deliberately **not** "= the
> global lex-min" (deferral gives a *different* iso-invariant canonical form; user correction 2026-07-11). Built:
> `IsCanonicalForm C := Sound C ∧ IsoInvariant C` and the payoff **`complete_of_isCanonicalForm`** — *sound ∧
> iso-invariant ⟹ complete* (`C G = C H ↔ GraphIso G H`), so ①b costs nothing and the ONLY real obligation is
> iso-invariance of the construction (the X3 content). Plus the generic selection combinator `lexMin` +
> `isCanonicalForm_lexMin`: a lex-min over a candidate family is a canonical form given (i) every candidate is a
> relabelling (`sound_lexMin`) and (ii) **`cand (relabelAdj σ G) = cand G`** (`isoInvariant_lexMin`) — the honest
> iso-invariance obligation, surfaced as candidate-**set** equality (NOT "cand = all of Perm"; for deferral it
> holds because a reached leaf's matrix is a function of the σ-invariant abstract refinement) — a valid but, as of
> **2026-07-13, OPTIONAL** technique.
>
> **▶▶ OBJECT REVISED (2026-07-13) — read §1 before building; this supersedes the `cand`/`lexMin` NEXT above.** The
> `canonMin` / reified-candidate-set route is **retired**: the spec is **`Sound ∧ IsoInvariant`, full stop**
> (completeness free, flag-invariance free), and the descent **defines** the canonical form rather than searching for a
> pre-existing global lex-min — chasing *which* leaf it reaches, just to prove it always reaches the same one, is a
> rabbit hole. The object is **ONE computable `CostM` descent parameterized over a list of `Resolver`s**, with consume
> and force unified by a single **branch-covering** contract (narrowing is sound because discarded branches are
> *redundant*, not because they *lose* — which is exactly what lets force be proved **without knowing the answer**).
> The **executable is a projection** of that same definition, not a separate track. `complete_of_isCanonicalForm` is
> construction-agnostic and survives untouched.
>
> **▶ Stage 0a's `Option`-LIFT LANDED (2026-07-13, `CanonicalForm.lean`, in `build.sh`, axiom-clean, full build green).**
> `SoundOpt` / `IsoInvariantOpt` / `IsCanonicalFormOpt` + `complete_of_isCanonicalFormOpt` (①b free) +
> `flag_iso_invariant_of_isoInvariantOpt` (①c free) + `isCanonicalFormOpt_guardBy` (the flag costs nothing beyond
> **"stalled" being equivariant**). **The framework is DONE: ①a/①b/①c reduce to exactly two facts about `descend`
> — `SoundOpt` and `IsoInvariantOpt`.**
>
> **▶▶▶ STAGES 0b + 1 + 2 ARE DONE, AND THE CONTRACT IS HARDENED (2026-07-13, `ChainDescent/Descend.lean`, in
> `build.sh`, axiom-clean, no `sorry`, full build green 98s).** `descend` — the **computable,
> resolver-parameterized branching** descent in `CostM` — exists, **runs** (`#eval`: K3/path canonize), and is
> **PROVED a canonical form**: **`isCanonicalFormOpt_canonForm?`** = sound ∧ iso-invariant ⟹ **①a/①b/①c all
> discharged for the real object**, modulo exactly two carried hypotheses: **`RefineEquivariant`** (the refiner) and
> **`NarrowTransport`** (the resolver).
>
> **★ THE CONTRACT HARDENING (2026-07-13) — read §1.3 before touching a resolver.** The earlier single
> **`Covering`** contract was **too strong and is retired**: `canonForm?_eq_deferAll_of_covering` *proves* a
> covering resolver is **value-invisible** (it computes exactly the exhaustive branch-min) ⟹ covering silently
> re-imported the retired `canonMin` anchor, and **force could satisfy it only by already knowing the answer**.
> Replaced by the weaker **`NarrowTransport`** (fuel-graded, IH-threaded) with **two** sufficient conditions —
> **`Covering`** (consume: non-equivariant choice, redundant discards) and **`NarrowEquivariant`** (force:
> structural choice, genuinely-different discards, a *different but equally valid* canonical form).
> **`narrow_eq_branches_of_orbit` proves the two routes have complementary firing domains** (equivariant narrowing
> is *impossible* on an orbit cell) — which is why the design does **not** collapse into GI ∈ P.
>
> **★ NON-VACUITY EARNED (2026-07-13).** The capstone alone is satisfiable by a degenerate refiner that flags on
> **every** graph (the constant refiner is `RefineEquivariant` by `rfl`). Now closed: **`canonForm?_ne_none`** —
> with a genuinely-refining refiner (`RefineSplits`) and a proper resolver (`NarrowProper`), the descent **always
> reaches a leaf**. So the object is a canonizer that *computes*, fuel-exhaustion is a pure depth bound, and `none`
> is free for its real (Stage 4) mutual-stall meaning.
>
> **★ SIGNATURE HARDENING (same pass).** `Resolver` now takes the **`AdjMatrix`** (neither intended instance was
> writable without it — `matchOracle` verifies automorphisms, the rigid solver does linear algebra), and **both**
> `Refiner` and `Resolver` are in **`CostM`** (so `descentCost` charges refinement + resolver work, not just node
> count — without this ② could not be a theorem about *this* definition, §1.4).
>
> **▶▶ THE REFINER IS INSTANTIATED — ① IS NOW HYPOTHESIS-FREE EXCEPT FOR THE RESOLVER (2026-07-13,
> `ChainDescent/Refine.lean`, in `build.sh`, axiom-clean, no `sorry`, full build green).** `encodeFree` — the
> **encode-free structural round** — discharges **both** refiner obligations: **`refineEquivariant_encodeFree`**
> (the hypothesis all of `①b` was carrying) and **`refineSplits_encodeFree`** (which discharges *totality*). Payoff:
> **`Refine.exhaustive_canonizer`** — *the exhaustive descent is **unconditionally** a canonical form **and**
> unconditionally **answers***. **No carried hypotheses whatsoever.** Every resolver added from here only narrows,
> shrinking the flagged residue, and can never break this.
>
> **★ A CORRECTED FINDING — "renumber the round's output" was NOT the fix (cost-model D7).** The old diagnosis was
> *cross-round compounding* (`encode ∘ encode ∘ …`) with the cure being rank-renumbering the output
> (`vertexRankNat ∘ refineStep`, the `ScratchRenumber` primitive). **Measured: a SINGLE `refineStep` at `n = 3`
> already fails to `#eval`** — the `Encodable.encode` *value* is infeasible after **one** round, before any
> compounding, so renumbering the output cannot help. The real round **drops `Encodable.encode` entirely**: `sigKey`
> is already a canonically-sorted `List Nat`, and `Descend.lexLeList` is already proved a **total order**, so the
> round ranks the **keys themselves** and never forms a `Nat` encoding. Colours land in `0..n-1` by construction.
>
> **★ THE EXECUTABLE RUNS — and the sharing trap is ROOT-CAUSED AND FIXED (2026-07-13).** Exhaustive canonization of
> `C₃…C₇` completes in **well under a second per graph** (`ChainDescent/PerformanceTest.lean`, now **in `build.sh` as a
> regression gate**: it `#guard`s iso-invariance under relabelling *and* that non-isomorphic graphs get different
> forms, so a regression **fails the build**). Before the fix, `C₃` alone took ~10 minutes and `C₅` never terminated.
>
> **The root cause (worth knowing — it will recur).** Lean's code generator **eta-expands every definition to the
> arity of its TYPE**. `Colouring n` unfolds to `Fin n → Nat`, so *any* definition of type `… → Colouring n` is
> compiled at full arity: `f adj χ v = <body> v`. Hence `f adj χ` is a **partial application** that stores its
> arguments and **re-runs `<body>` on every colour lookup** — the materialised vector is never shared, and since each
> descent level's colouring closes over its parent's, the cost *multiplies per level*. Measured (20 000 lookups,
> `n = 5`): depth 1 ≈ 1 ms/lookup, depth 2 ≈ 4 ms, depth 3 → does not finish. **`@[noinline]` does not fix it** (it
> blocks inlining, not eta-expansion), nor does eta-reducing the body, nor passing the vector as an argument.
> **The cure: return a value whose type is NOT a function** — `warmRefineVec` returns a `ColData` *structure*, so it
> is compiled at its true arity and forced **once**; `ColData.col` then closes over the already-forced vector and
> lookups are genuine `O(1)` array reads. **No signature change to `descend` was needed after all.**
>
> **Two measurement traps that cost real time here:** (i) a **top-level `def` colouring IS cached**, so testing the
> descent's levels in isolation looks fast and hides the bug completely — it only appears *inside* `descend`;
> (ii) `lean` **discards all `#eval` output on timeout**, so one slow `#eval` late in a file silently swallows the
> earlier results. Bisect with one `#eval` per file, and time the bare-import baseline.
>
> **▶▶▶ STAGE 3 — THE ORACLE RESOLVER IS LANDED (2026-07-14, `ChainDescent/Consume.lean`, in `build.sh`,
> axiom-clean, no `sorry`, full build green).** `consume` keeps **one representative per orbit** of the branch cell
> and discards the rest — the **`Covering`** route.
>
> **★ THE ORACLE IS UNTRUSTED — the resolver VERIFIES.** `consume` is parameterized by an arbitrary **`Supply`**
> (in the real system: `matchOracle` / the cascade oracle / the solver kernel) which carries **no proof obligation
> whatsoever**. The resolver filters it through a *decidable* automorphism-and-colour check (`IsColAut`) and uses
> only the survivors. Hence **`coveringAt_consume` holds for EVERY supply — even a malicious or buggy one**, and
> the capstone **`consume_canonizer`** gives `①a`/`①b`/`①c` **plus totality** with *no hypothesis on the oracle at
> all*. This is the project's own rule — *never merge two vertices into one orbit without a proof, verified
> edge-by-edge* — as a Lean contract. It puts the oracle's **completeness** entirely on the **②/firing** side of the
> ledger and **nothing** on the ① soundness side. (⚠ Relocation is not elimination: a supply that never fires is
> sound but useless — the descent then branches exhaustively and flags.)
>
> **★ `CoveringAt` — the fuel-graded covering — is what made this provable.** `consume` does *not* satisfy the
> unconditional `Covering`: its covering witness is an automorphism `α`, and "the discarded branch and the kept one
> have the same `descend` value" **is `descend_transport` at `σ = α`**. Not circular (it descends on fuel), but the
> hypothesis has to be able to *use the induction hypothesis* — so `CoveringAt` threads `TransportAt rf R fuel` in,
> exactly as `NarrowTransport` does. **This is the graded form every real resolver instance should target.** Also
> new: **`aggregate_congr_mem`** (the aggregate depends only on the *set* of branch results, not the multiset) —
> needed because consume genuinely *drops* branches.
>
> **★ IT PRUNES, AND IT STAYS RIGHT (`PerformanceTest.lean`, now a build-gating regression).** With a rotation
> supply on cycles: `descentCost` **C₅ 2016 → 804, C₆ 4123 → 1372, C₇ 7568 → 2160**, and `#guard`s that the
> oracle-driven form **equals the exhaustive form exactly** (the covering property — consume is *value-invisible*)
> while still distinguishing non-isomorphic graphs and staying iso-invariant. The oracle fires at the root (constant
> colouring ⟹ rotation verifies ⟹ one orbit ⟹ one branch instead of `n`) and correctly **defers** one level down,
> where individualization breaks the symmetry and the rotation fails verification.
>
> **▶▶▶ STAGE 3 IS COMPLETE — THE FORCE RESOLVER IS LANDED (2026-07-14, `ChainDescent/Force.lean`, in `build.sh`,
> axiom-clean, no `sorry`, full build green).** Built as a **combinator, not a hard-wired solver**:
> **`forceBy key`** keeps the branches of **least key**, where a `Key` is any vertex invariant.
>
> **★ THE ENTIRE ① OBLIGATION OF A FORCE RESOLVER IS `KeyEquivariant`** — *the key commutes with relabelling*, i.e.
> it never breaks ties by vertex index (the same discipline that makes `indivOne` index-free). Given that,
> **`narrowEquivariant_forceBy`** discharges the resolver contract and **`force_canonizer`** gives ①a/①b/①c **plus
> totality**, unconditionally. **The rigid solver (Algorithm R) drops in here as a stronger `key` and owes nothing
> else.** This is the concrete cash-out of the §11.12 re-basing: **P1/P3 are not ① obligations** — a weak key
> narrows less, which is *sound*. ⚠ **But relocation is not elimination:** narrowing less ⟹ more branching ⟹ budget
> exhaustion ⟹ flag. **A key that never separates is a canonizer that flags everything.** P1/P3 keep their full
> content as **②/firing** obligations — they are exactly *how much the key sees*.
>
> **★★ THE COMPLEMENTARY-FIRING-DOMAIN THEOREM, NOW OBSERVED.** `forceBy_no_narrowing_on_orbit` (a specialization of
> `narrow_eq_branches_of_orbit`): force **cannot fire on a cell that is an orbit**. Measured with the concrete
> `lookaheadKey` (individualize → refine → rank by the *leaf reached*):
> - **rigid** 3-regular `F12` (1-WL leaves one cell of all 12; cells are **not** orbits): root fan-out **12 → 1**,
>   `descentCost` **22477 → 5186**.
> - **vertex-transitive** `C₇` (every cell **is** an orbit): narrows **7 → 7**, i.e. *cannot fire at all*, and merely
>   pays for its key (`descentCost` 7568 → 10312). **That is not a defect — it is the theorem, observed**, and it is
>   exactly why `consume` exists. The two routes cover disjoint ground; graphs where **neither** fires are the residue.
>
> **⚠ A false start worth not repeating:** ranking by the **cell-size histogram** after individualization separates
> **nothing** on a rigid graph (individualizing *any* vertex discretizes ⟹ every histogram is all-ones; measured: it
> narrowed 12 → 12). The **leaf matrix** is what separates them — usable precisely because `leafMatrix_transport`
> proves the emitted matrix is *literally equal* under relabelling. (Also: `lookData` must return `ColData`, not
> `Colouring` — the eta-expansion sharing trap again, and it cost ~10⁴×.)
>
> **▶ NEXT:** **② — the cost + the real mutual-stall flag** (the old `n⁴` bound used the single-path `nbud = n` and
> does **NOT** transfer; `descend`'s fuel-exhaustion `none` is still a **placeholder**), then **③**. Both resolver
> instances now exist to cost against.

**The Lean canonizer today is a SINGLE DETERMINISTIC PATH — it cannot represent a mixed residue.** Verified
from source (2026-07-10):

- `canonForm?` runs `spineCappedCanonizer`: `defaultSpineChain` individualizes `sel χ` via `IndivStep.default`
  and the descent step is only `k ↦ k+1` to a discrete leaf (`Spine.lean:439-446`, `CostModel.lean:477-479`,
  `defaultSpineChain_reaches_leaf` `Spine.lean:648`). There is **no fan-out over cell representatives.**
- The only `Finset.min'` (`canonForm`, `Spine.lean:1254`) is a lex-min over the **order-label `DirAssignment`
  layer of the ONE reached leaf** — not a min over leaves/branches.
- The descent **calls no oracle** and carries **no consume/defer disposition.** `matchOracle` /
  `CascadeOracleSpec` (`CascadeOracle.lean:148,1095`) are a *separate* interface never invoked by the
  `canonForm?` descent; the `Phase` type (`CostModel.lean:231`) is only a flag-tag, never read to choose an
  action.

So the current model is exactly the **all-symmetric single-path pole**: it is valid precisely when every
selected cell is one orbit (the confinement `SelectedCellIsOrbit`, so any individualization order gives an
iso-equivalent leaf). On a mixed graph it individualizes real-decision cells as if symmetric — the very case
it cannot canonicalize by a single path. (It is also not yet proven iso-invariant even on the pole — the "X3"
cut, endgame §STATUS.) **The oracle, the two phases, and the branching all exist only as separate substrate
to be wired in here.**

---

## 1. The target — the object and its spec (REVISED 2026-07-13)

> **⚠ The `canonMin` (min-over-all-leaves) anchor is RETIRED.** The earlier target was "prove
> `canonizer adj = canonMin adj`", i.e. show the descent computes the global lex-min over the full IR tree.
> That is the wrong target twice over: (a) it is **not the spec** — deferral fixes each leaf's numbering, so the
> descent produces a *different but still iso-invariant* form, which is all correctness needs; and (b) it forces
> every pruning argument to be stated against a **pre-existing "true" answer**, which reintroduces the exponential
> reference object and, for the rigid solver, the very "which branch wins" knowledge we cannot have. See §1.3.

### 1.1 The spec — Sound ∧ IsoInvariant, and nothing else

The canonizer's theorem is `C G = C H ↔ Iso G H`, and that needs exactly two things:

- **(←) Sound** — the output is a relabelling of the input: `C G = some c → ∃ π, c = labelledAdj π G`.
- **(→) IsoInvariant** — `C (relabelAdj σ G) = C G`.
- **the flag** — `none ⟺ every resolver stalled`. Since each resolver is equivariant, "all stalled" is
  equivariant, so **①c (flag iso-invariance) is free**.

Completeness then follows with **no further work** from Stage 0a's `complete_of_isCanonicalForm`
(`Sound ∧ IsoInvariant ⟹ complete`), which is **construction-agnostic** — it never asks *which* leaf you land on.
**The descent DEFINES the canonical form; it does not search for a pre-existing one.** Do not reify a candidate
set and do not chase "which answer" in order to prove "always the same answer".

*(Consequence: the `lexMin`/`isCanonicalForm_lexMin` combinator of Stage 0a is a valid but **optional** technique,
not the route. A deterministic `List` min under `MatrixLex` still appears **inside** the definition to aggregate
deferred branches — but it is definitional, generates no separate proof obligation, and must be computable (see §1.4).)*

### 1.2 The object — ONE computable descent, parameterized over resolvers

```
descend : AdjMatrix n → CostM (Option Matrix)          -- one definition
```

At each node: refine, pick the target cell (equivariant selector `selCell`), form the branch list `B` over the
cell's representatives, then ask the resolvers. A resolver may **narrow** `B` to a nonempty `B' ⊆ B`; if none
narrows, the node **defers** — branch over all of `B` and aggregate. Leaves emit `labelledAdj (rankPerm χ) G`.
The run flags (`none`) at **mutual stall**.

### 1.3 The `Resolver` contract — **TWO routes, complementary firing domains** (HARDENED 2026-07-13)

> **⛔ The one-contract "branch covering" design is RETIRED — it was too strong, and provably so.**
> `canonForm?_eq_deferAll_of_covering` (`Descend.lean` §11, axiom-clean) proves that a **covering** resolver is
> **value-invisible**: it computes *exactly* the same answer as the exhaustive `descend deferAll`. So demanding
> covering of every resolver **pins the object to the exhaustive branch-min — i.e. re-imports the `canonMin`
> anchor §1 had just retired**, through the back door of the contract. And a **force** resolver in a *rigid*
> medium narrows to a branch whose leaf differs from the discarded branches' leaves, so it can satisfy covering
> **only if the rigid solver already computes the global lex-min — only if it KNOWS THE ANSWER.** Covering did not
> dodge the known-answer problem; it *encoded* it. (Tell: the only resolver that satisfied it was `deferAll`,
> by `rfl`.)

What the induction actually needs is strictly weaker — **the narrowed-branch aggregate transports**:

> **`NarrowTransport rf R`** — for every `fuel`, *given the descent's iso-invariance at that fuel* (the IH,
> threaded in explicitly), the aggregate over the **narrowed** branches is the same at `(adj, χ)` and at
> `(σ·adj, σ·χ)`.

It does **not** demand that narrowing preserve the aggregate — only that whatever aggregate the narrowing
produces is the *same* on `G` and `σ·G`. That is exactly what lets **force change the canonical form** (to a
different, equally valid one) instead of having to reproduce the exhaustive min. Two independent sufficient
conditions feed it:

| route | narrowing is | discards are | aggregate | instance |
|---|---|---|---|---|
| **`Covering`** | *non*-equivariant (pick **any** orbit rep) | **redundant** — a verified path-fixing automorphism maps them onto a kept branch (the C#'s `CoveredByPathFixingAut`) | **preserved** | **consume** (oracle) |
| **`NarrowEquivariant`** | **equivariant** (a structural function of `(adj, χ)`; no tie-break by vertex index) | genuinely **different** | **changes — consistently** | **force** (rigid solver) |
| *(defer)* | `B' = B` | — | preserved | `deferAll` (both routes) |

Lemmas: `narrowTransport_of_covering`, `narrowTransport_of_narrowEquivariant`. The **fuel-grading is load-bearing**:
consume's covering witness is an automorphism `α`, so its proof *is* `descend_transport` at `σ = α`, one fuel level
down — the hypothesis must be able to *consume* the IH or the instance is circular.

**★★ WHY THIS DOES NOT COLLAPSE INTO GI ∈ P** (`narrow_eq_branches_of_orbit`, proved). If any equivariant nonempty
narrowing were sound, why not narrow to one branch always? Because **equivariant narrowing is impossible on a cell
that is an orbit.** Let `α` be a colouring-preserving automorphism: then `α·adj = adj` and `α·χ = χ`, so
equivariance at `σ = α` gives `narrow = α · narrow` — the narrowed set is invariant under the *whole*
colouring-preserving automorphism group, and a nonempty invariant subset of a single orbit **is the whole orbit**.
So:

> **force provably cannot fire on a symmetric cell, and consume fires exactly there.** The two routes have
> **complementary, non-overlapping firing domains.** Equivariant narrowing is available only where the cell is
> genuinely *not* an orbit **and** the resolver can structurally see the distinction (the linear/ring structure).
> **Graphs where neither route fires are the residue.** That is the architecture, and now it is a theorem.

This also makes the contract **checkable**: a narrowing is equivariant iff it is a pure function of `(adj, χ)` that
never breaks ties by vertex index — the same discipline that makes `indivOne` index-free.

A resolver that narrows too little is still sound (it only costs a branch) — the project's own "over-splitting is
safe" rule, now a Lean contract. **A future unhandled-residue solver is just another instance of one of the two
routes**, and adding it shrinks the flagged residue *without touching ①*. ⚠ But *sound* is not *useful*: see
Stage 3 — a solver that never fires is a canonizer that flags everything.

### 1.4 The executable is a PROJECTION, not a second object

Write the descent **once**, computably, in the cost monad; take three views of the same definition:

| view | is |
|---|---|
| **executable** | the definition itself (`#eval`-able) |
| **① correctness** | theorems about its `value` |
| **② cost** | theorems about its `cost` |

This is the cost model's own **D1** decision ("cost carried *with* the value, tied to the code; not a parallel
bookkeeping function"), already realized in `costedWarmRefine`. It supersedes an earlier proposal to build a
correctness object and a cost object separately with a bridge — that would have orphaned the executable as a
*third* thing. Note this is **why §1.1's rejection of a reified candidate set matters structurally**: `Finset.min'`
+ `Classical` is *noncomputable*, so a set-based correctness object would be incompatible with the executable by
construction. See [`chain-descent-executable-track.md`](./chain-descent-executable-track.md).

**Five constraints to bake in NOW** (not to build now — only to not foreclose):
1. **The definition is computable.** No `Classical.choice` / `Finset.min'` / `noncomputable` in the *definition*;
   branch aggregation is a `List` fold under `MatrixLex`. Proofs may be as classical as they like; code may not.
2. **`Resolver.decide` is a computable function**; `sound`/`isoInvariant` are `Prop` fields.
3. **Use the encode-free / renumbering `refineStep` (cost-model D7 fork ii) from day one**, with `@[csimp]` — *not*
   `@[implemented_by]` (which can assert false equations). The `Encodable.encode` colour blow-up is the known
   `#eval` staller and it is a **definitional** choice: defining the descent over the encoding `refineStep` stalls
   the executable *by construction*. **This is the one item to lock now** — it is the only constraint whose later
   change means redefining the object everything else is proved about.
4. **Decidable equality + order on the leaf type**, so the fold and the flag test compute.
5. **Resolvers stay a first-class list**, so an added solver shrinks the residue without re-proving ①.

### 1.5 The engine is an interleaved fixpoint

Because almost every residue is *fused*, consumption and forcing **interleave** — `… ∘ phase2 ∘ phase1 …`, one
pairwise relation at a time, the rigid solve's kernel feeding *de-fused* symmetry back into consumption (IR §11.11).
A single `phase2 ∘ phase1` append is the **fusion-free special case**. Crucially the fixpoint's *dynamics never enter
①*: correctness is a property of the terminal output, proved by induction over `descend`, so **a bad schedule costs
an unnecessary-but-sound branch, never correctness** — which is precisely the robustness the interleaved design
promises, and the reason the spec must be §1.1's and not `canonMin`'s.

---

## 2. Why mixed is the priority (over the Cameron-visible families)

The two poles are both **unrepresentative** of a real residue:

- **Pure symmetric (single path, all consumed)** — the confinement `CertifiedSinglePath`. Real only for a
  vertex-transitive residue with no genuine decisions.
- **Pure rigid (all branch, nothing consumed)** — the multipede. Real only for a trivial-`Aut` WL-hard core.

The measured **sum-not-product** result (`[[project_rru_cost_probe_2026-07-10]]`: A⊔B, deferral ON → union
harvest = 113 = sum, OFF → 1808 = product) shows the C# already composes the two cleanly. The Lean models
**neither** the composition **nor** even the rigid pole (no branching). So the representative case — consume
some, branch the rest — is exactly the hole. The Cameron-visible forms families (Route C / the certified
assume-VT path) are a *different* enlargement of the handled set and are **deprioritized** here: they widen
what Phase 1 consumes, but the composition must work regardless of how much Phase 1 consumes.

---

## 3. The stages (what is new vs. reusable) — REVISED 2026-07-13 for the §1 object

★ = new build · ○ = reuse existing substrate.

**Stage 0 — the spec + the object (★, foundational).**
- **0a — the correctness framework (LANDED 2026-07-11, `ChainDescent/CanonicalForm.lean`).** `IsCanonicalForm`
  = sound ∧ iso-invariant; **`complete_of_isCanonicalForm`** gives completeness for free, and is
  **construction-agnostic** — it is the whole payoff and it survives the object change untouched. *(The `lexMin` /
  `isCanonicalForm_lexMin` combinator is now **optional**, not the route: §1.1 retires the reified candidate set.)*
  **★ THE `Option` LIFT — LANDED (2026-07-13, `CanonicalForm.lean`, in `build.sh`, axiom-clean, full build green).**
  The flagging type `AdjMatrix n → Option (Labelled n)` — the shape `Publication.canonForm?` actually has — is now the
  spec surface, so every later stage is proved against the real type:
  - `SoundOpt C := ∀ G c, C G = some c → ∃ π, c = labelledAdj π G` — *literally* `Publication.canon_sound` (①a).
  - `IsoInvariantOpt C := ∀ σ G, C (relabelAdj σ G) = C G` — **one** equation on `Option`s, so it carries the output
    invariance **and** the flag invariance together. There is **no separate flag obligation.**
  - `IsCanonicalFormOpt := SoundOpt ∧ IsoInvariantOpt` — **the complete spec of the mixed canonizer.**
  - **`complete_of_isCanonicalFormOpt`** = `Publication.canon_complete` (**①b, FREE**);
    **`flag_iso_invariant_of_isoInvariantOpt`** = `Publication.flag_iso_invariant` (**①c, FREE**);
    both via `eq_of_graphIso` (isomorphic inputs get the *same answer* — value or flag).
  - **`isCanonicalFormOpt_guardBy`** proves the flag mechanism claim: a canonical form gated by an **iso-invariant
    "handled" predicate** is a flagging canonical form ⟹ *`none ⟺ stalled` contributes no obligation beyond the
    **equivariance of "stalled"***. `isCanonicalFormOpt_some` embeds the total theory.
  - Axioms: core payoffs need only `[Quot.sound]`; `guardBy` `[propext, Classical.choice, Quot.sound]` (deciding an
    arbitrary `P`) — tighter than the project bar.

  **So ①a/①b/①c now reduce, with no remaining framework work, to exactly two facts about `descend`: it is `SoundOpt`
  and it is `IsoInvariantOpt`.** That is Stage 2.
- **0b — the object (★) — SKELETON LANDED (2026-07-13, `ChainDescent/Descend.lean`, in `build.sh`, axiom-clean,
  full build green 95s; it RUNS).**
  `descend refine R adj fuel χ : CostM (Option (Labelled n))` — refine → equivariant target cell → branch list →
  resolver narrows (or defers) → recurse → aggregate; leaf emits the rank-relabelled matrix; `none` on fuel
  exhaustion (the placeholder for the stall flag). Top-level `canonForm?` + `descentCost` are the **`value` / `cost`
  projections of the one definition**, and the definition itself is the executable. Landed pieces:
  - **Computable leaf emit.** `Colouring.rankPerm` is `noncomputable` (`Equiv.ofBijective`), so the emit goes via
    **`rankInv`** (rank → vertex, by search) + **`leafMatrix`**, with **`leafMatrix_eq_labelledAdj`** proving it
    *equals* `labelledAdj (rankPerm χ h) adj` ⟹ **`leafMatrix_sound` = `①a` at the leaf** (the base case of `SoundOpt`).
  - **Index-free individualization `indivOne`** (the X3 cut): mark the branch vertex with a **parity bit** on its
    existing colour (`2·χv+1` vs `2·χu`), **never `v.val`** — unlike `IndivStep.default`, which encodes `χ v * n +
    v.val` and would leak the *labelling* into the leaf, making iso-invariance impossible. `indivOne_singleton` +
    `indivOne_refines_off` proved.
  - **Equivariant target cell**: least non-singleton **colour value** (`targetColour`/`cellOf`) — a function of the
    colouring alone, so the branch set transports. No vertex index is read.
  - **Bake-ins honoured:** the definition is **computable** (no `Classical` in code; `Finset.toList` is
    noncomputable ⟹ the branch collection is a `List`), and **`refine` is a PARAMETER** ⟹ the `Encodable.encode`
    `refineStep` staller is *not* baked in; the encode-free round drops in as the instance (its equivariance becomes
    a Stage-2 hypothesis).
  - **Resolvers STUBBED**: `Resolver n := Colouring n → List (Fin n) → Option (List (Fin n))` + `deferAll` (never
    narrows) ⟹ `descend deferAll` is the honest exhaustive-branching object. Stages 0–2 are written against the
    **type**, so they don't wait on the instances.
  - **It runs** (`#eval`, identity refinement): `K3 → [[0,1,1],[1,0,1],[1,1,0]]`, path `→ [[0,0,1],[0,0,1],[1,1,0]]`;
    **all 9 relabellings of the path give the identical form** (iso-invariance smoke test) and K3/path are
    distinguished.
  - **Remaining for 0b:** swap the fuel-flag for the real stall test (Stage 4), and instantiate `refine` with the
    encode-free round.

**Stage 1 — the `Resolver` contract (★, small; generalizes `Phase2.Solver`).** One structure: computable `decide`
narrowing `B → B'`, plus `Prop` fields **equivariance** and **covering** (`cov : B \ B' → B'` with
`descend (cov b) = descend b`) — §1.3. Consume and force are two *instances*, not two constructors. Reuse:
`Phase2Handoff.Phase2.Solver`/`Sound`/`IsoInvariant` (`Phase2Handoff.lean:74-86`) is the shape to generalize.

**Stage 2 — the ONE hard theorem: `descend` is Sound ∧ IsoInvariant (★, substrate ○). — ✅ DONE (2026-07-13,
`Descend.lean`, in `build.sh`, axiom-clean, no `sorry`, full build green).**

> **★★★ CAPSTONE: `isCanonicalFormOpt_canonForm?` — the descent IS a canonical form.** Sound ∧ iso-invariant, hence
> (Stage 0a) a *complete* isomorphism invariant with an iso-invariant flag. **`①a`, `①b`, `①c` are all discharged for
> the real object**, modulo exactly **two carried hypotheses**: `RefineEquivariant` (the refinement parameter) and
> `Covering` (the resolver contract). Corollaries in the `Publication.lean` shapes:
> **`soundOpt_canonForm?`** (= `canon_sound`), **`canonForm?_complete`** (= `canon_complete`),
> **`canonForm?_flag_iso_invariant`** (= `flag_iso_invariant`). `covering_deferAll` is proved by `rfl`, so the
> exhaustive-branching object satisfies the whole thing with **no resolver obligation at all**.

**★★ LANDED (2026-07-13, `Descend.lean`, axiom-clean, build green):**
- **`soundOpt_canonForm?` = `①a` DISCHARGED on the real object** (via `descend_sound`, induction on fuel;
  `aggregate_mem` + `lexMin?_mem`). Note it holds for **ANY `refine` and ANY resolver** — narrowing only *removes*
  branches and every survivor is still a relabelling. **This is why a mis-narrowing resolver costs a branch and
  never correctness.**
- **The transport layer** (the road to `①b`): `transportColouring σ χ := χ ∘ σ⁻¹` and
  `discrete_transport` · `vertexRank_transport` · **`indivOne_transport`** · `cellOf_card_transport` ·
  `image_transport` · `targetColour_transport` · **`leafMatrix_transport`**.
- **★ THE HEART OF `①b`, PROVED: `leafMatrix (relabelAdj σ G) (χ∘σ⁻¹) = leafMatrix G χ` — the emitted matrices are
  LITERALLY EQUAL, not merely correspondent.** The `σ` cancels because the output is indexed by colour-**ranks**, not
  by vertices. (`indivOne_transport` is where the *index-free* individualization pays: an index-dependent one would
  fail this outright.)
- **★★ THE TWO ROUTES (corrected 2026-07-13; supersedes the earlier "equivariance is NOT needed, only COVERING").**
  The original discovery was half right and half fatal. **Right:** covering licenses **consume**'s "pick any orbit
  representative" — a choice that is genuinely *not* equivariant (orbit members are indistinguishable to refinement);
  only its *result* transports, because the discarded branches are covered. **Fatal:** covering was then imposed on
  *every* resolver, and `canonForm?_eq_deferAll_of_covering` proves that makes a resolver **value-invisible** ⟹ it
  pins the object to the exhaustive branch-min (= the retired `canonMin`) and **force can satisfy it only by knowing
  the answer.** The fix is §1.3's **two routes** into the weaker **`NarrowTransport`**: `Covering` (consume) and
  `NarrowEquivariant` (force). `narrow_eq_branches_of_orbit` proves their firing domains are **complementary** —
  equivariant narrowing is *impossible* on an orbit cell — so the design does not collapse into GI ∈ P.
  `covering_deferAll` **and** `narrowEquivariant_deferAll` both hold ⟹ the exhaustive object carries **no** resolver
  obligation on either route.

**★ Both remaining items CLOSED (2026-07-13):**
- **(i) `aggregate_perm` — the aggregate is PERMUTATION-INVARIANT.** The obligation created by `branches` being an
  index-ordered `List` (forced: `Finset.toList` is noncomputable). Discharged by making `lexLe` a genuine **total
  order**: `flatten` was restructured over an explicit `allPairs` list so **`flatten_injective`** is a one-liner, then
  `lexLeList_{refl,total,trans,antisymm}` ⟹ `lexLe_antisymm` ⟹ `lexMin?_le` + `lexMin?_perm` ⟹ `aggregate_perm`. So
  the labelling-dependent branch *order* provably never leaks into the output.
- **(ii) `descend_transport`** — induction on fuel. Leaf case: the emitted matrices are *literally equal*
  (`leafMatrix_transport`). Branch case: **covering** rewrites each side to its FULL-branch aggregate;
  `branches_transport_perm` makes the two full lists permutation-related; `indivOne_transport` + `RefineEquivariant`
  + the IH make the per-branch values agree pointwise; `aggregate_perm` closes it. ⟹ **`isoInvariantOpt_canonForm?`**.

*(Original plan, still the shape:)* By induction over the descent (well-founded on undiscretized vertices):
- **Sound** (easy): leaves are `labelledAdj (rankPerm χ) G`; the aggregate of relabellings is a relabelling;
  narrowing keeps leaves as leaves.
- **IsoInvariant** (the real work): `selCell` is equivariant ⟹ the **branch list transports**; each resolver is
  equivariant ⟹ narrowing transports; the aggregator is deterministic; the leaf matrix **absorbs σ** via `rankPerm`.
  Substrate (built, single-path): `labelledAdj_rankPerm_cross`, `descentColouring_transport`, `selCell_transport`
  (`ScratchConfinementX3*`), `warm_6_2` (`ChainDescent.lean:700`), `spine_branch_independent` (`Spine.lean:350`).
  **The genuinely new part is the branch-list transport** — the set of defer-branches is iso-invariant because
  `selCell` is and the reps are taken over an iso-invariant cell.
- Note the **mutual induction**: consume's covering witness uses `descend`'s iso-invariance at greater depth. It is
  well-founded (each step discretizes at least one vertex), but state the induction measure explicitly.
- ⟹ **completeness (①b) and flag-invariance (①c) are then FREE** via 0a. *(This stage replaces the old
  "composition = `phase2 ∘ phase1`" stage: with the covering contract, composition is not a separate theorem — the
  fold over alternation depth is subsumed by the induction. `coversOrbits_append` (`Cascade.lean:1122`) remains the
  harvest-side substrate for the consume instance's covering witness.)*

**Stage 3 — the resolver INSTANCES (★, the two witnesses) — one per route (§1.3).**
- **consume** — `matchOracle` / `CascadeOracleSpec` (`CascadeOracle.lean:148,1095`) narrows to one orbit rep;
  takes the **`Covering`** route, witnessed by a verified path-fixing automorphism (the C#'s
  `CoveredByPathFixingAut`); soundness of deferral by `real_stays_real` (`CascadeOracle.lean:74`). Substrate:
  `Confinement.SelectedCellIsOrbit` (`Confinement.lean:41`), `coversOrbits_of_realizers`. **The fuel-graded
  `NarrowTransport` is what makes this instance provable at all** — its covering witness is an automorphism `α`, so
  its proof is `descend_transport` at `σ = α`, one fuel level down.
- **force** — **Algorithm R** (the rigid solver); takes the **`NarrowEquivariant`** route: the narrowing is a
  structural function of `(adj, χ)` (the linear/ring solve), so it transports — *no* covering witness, *no* global
  lex-min, **no knowledge of the answer**. It yields a **different but equally valid** canonical form, which is
  legitimate for exactly the reason deferral always was. This is the separate IR track (§11.12; Lean **not started**;
  the C# `Option2Solver.cs` is **complete for handoff** and is its runtime reference).
- ⚠ **The obligations do not vanish — they RELOCATE from ① to ②.** Under the resolver contract, a solver that
  extracts too little or solves too weakly is *sound* (it just defers more). But **relocation is not elimination**:
  deferring more ⟹ more branching ⟹ budget exhaustion ⟹ flag ⟹ the input lands in `UnhandledResidue`. **A solver
  that is sound but never fires is a canonizer that flags everything: correct, and worthless.** So the rigid seal's
  **P1** (extraction generates the row-space) and **P3** (solve/canonical-form correctness) keep their full content —
  they are now **②/firing obligations** (how much residue is actually handled), not ① soundness obligations. That is
  a re-basing of §11.12, not a deletion of it.
- Stages 0–2 proceed with the resolver **abstract**, so this does not gate them.

**Stage 3 — plug in the rigid solver as the `phase2` witness (★ = the IR track, separate).** `phase2` must
satisfy `Phase2.Sound`/`IsoInvariant` (`Phase2Handoff.lean:78,86`) — witnessed by **Algorithm R**
(`chain-descent-ir-blindspot-solver.md` §11.12). This is a *dependency*, not part of this framework: the
composition is stated against the `Phase2.Solver` **contract**, so Stages 0–2 proceed with `phase2` abstract
and the solver drops in when built. **Status (2026-07-12): the C# side is BUILT + WIRED + ROBUST, COMPLETE for handoff** —
`Option2Solver.cs` (recover→solve→emit→verify, ring-general), wired in `ChainDescent.Search` at the **root** (`depth == 0`,
behind `EnableRigidSolver`, default ON). **Every planned B-step is LANDED** (§11.12): B1a/b/c, B2, B3, **B4 incl. the general
`s`-fold cover**, B5, B6, and all three B1d items (SolveOverA affine-frame emit closing the m≥8 stall + the large-`|A|`
exponential; general arity ≥ 3; try-both-sides). **39 Option2Solver tests, 94 combined**, regression-clean. Bounded rigid-side
open items (fold covers `s > 6`, harvesting the fold `Aut`, the deferred solve-speed perf) are off the critical path — IR-doc
PICK-UP-HERE banner "OPEN / NEXT". So **Stage 3's C# dependency is satisfied**; what remains for Stage 3 is the **Lean witness
(P1–P4), not started** — the C# solver is its runtime reference (build-first). Detail = §11.12 + the IR-doc PICK-UP-HERE banner.

**Stage 4 — poly-or-flag: the `cost` PROJECTION (★, no bridge needed).** Because `descend` is written in `CostM`
(§1.4), ② is a theorem about the **same definition's** `cost` — *not* a separate object plus a bridge lemma. Content:
- **Per-node work** `w`: refinement + resolver cost — reuse `costedWarmRefine` (co-defined) + the oracle summand
  (`CostModel.lean`); the per-node **cap** keeps ② unconditional by construction (`min(trueCost, w)`).
- **Node count**: the `nbud = n` single-path justification is **retired** (it was assume-VT `leaves = 1`). The poly
  guarantee is the **verify-consume monovariant** — each covering-narrowing strictly reduces residual symmetry, each
  force reduces free relations, each defer is bounded by the branching bound — plus the **fusion-severity look-ahead**
  (IR §11.11). Measured **sum-not-product** (`[[project_rru_cost_probe_2026-07-10]]`): consume work does not multiply
  force branching.
- **The flag is MUTUAL STALL**, not `base > baseMax`. The threshold-gated assume-VT flag is retired (it could misprune
  a fused rigid residue); consumption is verify-gated, so a rigid residue *stalls* rather than being pruned.
- ⟹ ③: `stalled ⟹ residueHiddenJohnson ∨ residueRigidObstruction` (D1 ∨ D2), shrinking as resolvers are added.

---

## 4. Dependencies, sequencing, first step

```
Stage 0a (Option-lift) ─→ Stage 0b (the object: computable CostM descend) ─┬─→ Stage 2 (Sound ∧ IsoInvariant) ─→ ①a/①b/①c
                                                                            │      (THE hard theorem)
                          Stage 1 (Resolver contract: narrowing + covering) ┘
                                                                            └─→ Stage 4 (cost projection) ─→ ② / ③

Stage 3 instances (independent): consume (matchOracle + CoveredByPathFixingAut) · force (rigid seal P1–P4, IR §11.12)
```

- **✅ DONE:** Stage 0a (spec + `Option`-lift), Stage 0b (the object), Stage 1 (the **hardened**
  `Refiner`/`Resolver`/`NarrowTransport` contract, §1.3), **Stage 2 (the whole of ①)**, plus **totality**
  (`canonForm?_ne_none` ⟹ the capstone is non-vacuous) and the **non-collapse** theorem
  (`narrow_eq_branches_of_orbit`). Critical path 0a → 0b → 2 is complete.
- **▶ NEXT / critical path:** **instantiate `refine`** with the encode-free round (+ its `RefineEquivariant` **and**
  `RefineSplits` — the latter is what discharges totality for the real refiner), then **Stage 4** (② cost + the real
  mutual-stall flag). These two are what a fresh reader should pick up.
- **Start-anytime, independent:** the rigid solver's **P1** (extraction soundness, standalone,
  `chain-descent-ir-blindspot-solver.md` §11.12).
- **Not gating anything:** Stage 3's instances — ① is proved against the resolver **contract**, so correctness waits on
  neither the oracle's nor the rigid solver's Lean witness, and **a resolver can only ever shrink the flagged residue,
  never break ①**. This is what makes a future unhandled-residue solver plug in with **no re-proof**.
- **Locked (§1.4 item 3):** `refine` is a **parameter**, so the `Encodable.encode` staller is not baked in. Instantiate
  it with the encode-free / renumbering round; that is the only choice whose later change would mean redefining the
  object everything else is proved about.
- **Stage 0a DONE (2026-07-11), NEXT STEP = Stage 0b.** 0a (the correctness framework: `IsCanonicalForm`,
  `complete_of_isCanonicalForm`, `lexMin`/`isCanonicalForm_lexMin`) is landed in `ChainDescent/CanonicalForm.lean`
  (namespace `ChainDescent.CanonSpec`), in `build.sh`, axiom-clean — it *simplifies* ①b/①c (see §5) and gives the
  true spec surface for `Publication.canonForm?` (an `opaque` stub today). **0b** = build the branching
  consume/branch descent so its reached-leaf matrix set instantiates the `cand G` of `isCanonicalForm_lexMin`,
  then discharge its two hypotheses: (i) each reached leaf is a relabelling [easy, via `labelledAdj (rankPerm χ)`,
  cf. `SpineChain.canonAdj`], and (ii) `cand (relabelAdj σ G) = cand G` [the X3-hard iso-invariance — holds
  because a leaf's matrix is a function of the σ-invariant abstract refinement colouring, not the input labelling].

## 5. Strategic note — the min-over-leaves spec makes ①b/①c nearly free

The single-path `canonForm?` put the iso-invariance difficulty in the wrong place: it is *false* as stated
(the "X3" cut — `DirAssignment` never re-orders index-coloured committed vertices, so the lex-min cannot wash
out the individualization order; endgame §STATUS). Against `canonMin` the picture inverts:

- **①b/①c (iso-invariance, completeness) become nearly free** — a relabelling is a bijection on the leaf set,
  so `min` is invariant; equal mins ⟺ isomorphic is immediate.
- **All difficulty concentrates in `algorithm = canonMin`** — i.e. the poly computation equals the spec — which
  is where it *belongs* (it is the ②-side content: pruning + rigid solve reproduce the exponential min).

So adopting `canonMin` is not just cleaner for mixed handling — it relocates the open weight from a false ①b
onto the genuine ②/composition, matching where the endgame already says the weight is.

## 6. Relationship to the existing objects (the stepping stones)

- **Confinement `CertifiedSinglePath` / `SelectedCellIsOrbit`** — the **all-symmetric pole** and the
  **consume-soundness substrate** (Stage 1). Not superseded; it is one leg of the composition.
- **The conditional RRU** (`phase1 stops at ¬IsBase D ⟹ UnhandledResidue`, remaining-work §6 note) — the
  **Phase-1 deliverable** (Stage 2's `phase1`), stated correctly (not the content-free `RRU.rru`).
- **The certified-order flag** — Stage 4's largeness certificate; fixes the vacuous `hflag`.
- **`Phase2Handoff` (`Phase2.Solver`/`Sound`/`IsoInvariant`, `RRU.reachesRigid`)** — the **contract seam**
  Stage 3 fills; already stated in `labelledAdj`/`relabelAdj` shape to compose with ①.
- **Rigid seal (Algorithm R, IR §11.12)** — the `phase2` witness (Stage 3).

The flag and the RRU object are useful stepping stones exactly as the user notes — they are the Phase-1 side
and the safety valve — but the **priority deliverable is the composition** (Stages 0–2), because the
representative residue is mixed.
