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
> construction-agnostic and survives untouched. **NEXT:** Stage 0a's `Option`-lift → **Stage 0b** (define `descend`)
> → **Stage 2** (`Sound ∧ IsoInvariant` by induction = the one hard theorem).

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

### 1.3 The `Resolver` contract — consume and force are ONE thing: **branch covering**

Consume and force perform the *same operation* (shrink the branch set) for *different reasons*, and the reason is
where the earlier framing went wrong. Stating soundness as "the discarded branches lose under the aggregate"
presupposes the aggregate-over-all-branches is the answer (= `canonMin`) and needs the answer to know which branch
is kept. The correct statement is **redundancy, not victory**:

> **Resolver soundness = BRANCH COVERING.** `decide node = some B'` requires `B' ⊆ B` nonempty **and** a map
> `cov : B \ B' → B'` with `descend (cov b) = descend b` for every discarded `b`.
>
> **Resolver equivariance.** `decide` commutes with relabelling.

Every output reachable through a discarded branch is *already reachable through a kept one*, so
`aggregate (B'.map descend) = aggregate (B.map descend)` holds because the **value sets are equal** — for **any**
deterministic aggregator, with no reference to which branch wins and **no knowledge of the final answer**.

| resolver | narrows to | `cov` witnessed by |
|---|---|---|
| **consume** (oracle) | one orbit representative | a **verified path-fixing automorphism** ⟹ the discarded subproblem is isomorphic to the kept one ⟹ equal `descend` values (via `descend`'s own iso-invariance — a well-founded mutual induction, descending on undiscretized vertices). This is exactly the C#'s `CoveredByPathFixingAut`. |
| **force** (rigid solver) | the determined choice / the swept frame set | the **solve's determinacy**: a discarded individualization yields a labelling already produced by a kept frame. This is the rigid seal's **P3** (coset-min canonicity) — an existing obligation, not a new one. |
| **defer** | `B' = B` (no-op) | trivial |

"Structural ⟹ always discards the same branch" is then a **consequence**, not an assumption: the covering map is
structural (an automorphism / a solve), so it transports under σ, so narrowing is equivariant, so `descend` is.
A resolver that narrows too little is still sound (it only costs a branch) — the project's own "over-splitting is
safe" rule, now a Lean contract. **A future unhandled-residue solver is just another covering witness**, and adding
it shrinks the flagged residue *without touching ①*.

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
  **Small remaining lift:** the flagging **`Option`** version — "on the handled sub-domain, `Sound ∧ IsoInvariant ⟹
  complete`, and `stalled` equivariant ⟹ the flag transports". Short, and it pins the `Option` type the whole object
  rides on — do it first.
- **0b — the object (★, THE conceptual leap, NEXT).** Define `descend : AdjMatrix n → CostM (Option Matrix)` (§1.2):
  refine → equivariant `selCell` → branch list `B` → resolvers narrow, else defer-and-aggregate → leaf emits
  `labelledAdj (rankPerm χ) G`; flag at mutual stall. **Computable, in `CostM`, over the encode-free `refineStep`**
  (§1.4 constraints 1–4). Reuse: `SpineChain`/`rankPerm`/`canonAdj`, `selCell` (`ScratchConfinementX3Sel`),
  `MatrixLex` (`Spine.lean:1199`), `CostM` + `costedWarmRefine` (`CostModel.lean`), `refineStepR` (`ScratchRenumber.lean`).

**Stage 1 — the `Resolver` contract (★, small; generalizes `Phase2.Solver`).** One structure: computable `decide`
narrowing `B → B'`, plus `Prop` fields **equivariance** and **covering** (`cov : B \ B' → B'` with
`descend (cov b) = descend b`) — §1.3. Consume and force are two *instances*, not two constructors. Reuse:
`Phase2Handoff.Phase2.Solver`/`Sound`/`IsoInvariant` (`Phase2Handoff.lean:74-86`) is the shape to generalize.

**Stage 2 — the ONE hard theorem: `descend` is Sound ∧ IsoInvariant (★, substrate ○).** By induction over the
descent (well-founded on undiscretized vertices):
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

**Stage 3 — the resolver INSTANCES (★, the two witnesses).**
- **consume** — `matchOracle` / `CascadeOracleSpec` (`CascadeOracle.lean:148,1095`) narrows to one orbit rep;
  covering witnessed by a verified path-fixing automorphism (the C#'s `CoveredByPathFixingAut`); soundness of
  deferral by `real_stays_real` (`CascadeOracle.lean:74`). Substrate: `Confinement.SelectedCellIsOrbit`
  (`Confinement.lean:41`), `coversOrbits_of_realizers`.
- **force** — **Algorithm R** (the rigid solver); covering witnessed by the solve's determinacy = the rigid seal's
  **P3** (coset-min canonicity). This is the separate IR track (§11.12 **P1–P4**, Lean **not started**; the C# solver
  `Option2Solver.cs` is **complete for handoff** and is its runtime reference). Stages 0–2 proceed with the resolver
  list **abstract**, so this does not gate them.

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

- **Start-anytime, independent:** Stage 0a's `Option`-lift; the `Resolver` contract (Stage 1); the rigid solver's
  **P1** (extraction soundness, standalone, `chain-descent-ir-blindspot-solver.md` §11.12).
- **Critical path:** 0a → 0b → 2. Stage 2 is the whole of ①.
- **Not gating:** Stage 3's instances — Stages 0–2 are proved against the resolver **contract**, so the descent's
  correctness does not wait on either the oracle's or the rigid solver's Lean witness. This is also what makes the
  residue shrinkable later (add a resolver, re-prove nothing).
- **Lock now (§1.4 item 3):** the encode-free / renumbering `refineStep`. It is the only choice whose later change
  means redefining the object everything else is proved about.
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
