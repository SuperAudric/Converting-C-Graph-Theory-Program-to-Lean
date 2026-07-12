# Mixed rigid + symmetric handling — the Lean composition track

> **What this is.** The scoping plan for pointing the **Lean** canonizer at the case that actually
> dominates: a residue with **both** symmetric decisions (consumed by Phase 1) **and** rigid decisions
> (solved by Phase 2) — i.e. `canonForm? = phase2 ∘ phase1`, proven correct on **mixed** inputs. It is the
> concrete content of the endgame's **Runtime Phase** (`chain-descent-endgame-spec.md` §3 "Runtime Phase",
> §4.3 "the consumption bridge"), sharpened by the 2026-07-10 finding that *almost every real residue is
> mixed*, so neither the pure-symmetric pole (the confinement `CertifiedSinglePath`) nor the pure-rigid pole
> (the multipede) is representative. Companion measurements + design corrections:
> `[[project_rru_cost_probe_2026-07-10]]`, `[[project_confinement_bundle_vacuity_2026-07-10]]`.

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
> holds because a reached leaf's matrix is a function of the σ-invariant abstract refinement). **NEXT (Stage 0
> cont. → Stage 1):** instantiate `cand G` = the reached-leaf matrices of the consume/branch descent, and begin
> discharging (i)+(ii); the branching descent model itself is the remaining Stage-0 build.

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

## 1. The target — the min-over-leaves spec, factored through two phases

**Adopt the textbook spec as the correctness anchor** (a strategic shift the mixed/branching setting makes
natural — see §5):

```
canonMin adj  :=  min over all discrete leaves ℓ of the IR tree  of  labelledAdj (π_ℓ) adj
```

the IR tree branching on every non-singleton cell over all representatives. `canonMin` is **iso-invariant and
complete BY CONSTRUCTION** (a relabelling permutes the leaf set; the min is unchanged), and obviously
exponential. The entire algorithm is: *compute `canonMin` without enumerating all leaves.* Two moves do that,
and they are exactly the two phases:

- **Phase 1 — consume (prune orbit-related branches).** Sibling branches related by an automorphism (the
  selected cell is one orbit) contribute the **same** value to the min, so all but one representative are
  pruned. Sound because `labelledAdj` is Aut-invariant on an orbit. Output: the **rigid residue** — the
  sub-tree whose remaining branches are all *real* decisions.
- **Phase 2 — solve (min over the rigid residue's leaves).** The rigid solver (Algorithm R,
  `chain-descent-ir-blindspot-solver.md` §11) computes that min in poly time for a **linear-over-ring**
  residue (multipede/CFI/`Z_{2^k}`), or flags (`residueRigidObstruction`).

**The mixed-handling theorem is the equality `canonizer adj = canonMin adj` (or a flag), factored as
`phase2 ∘ phase1`.** Phase 1's pruning preserves the min (consume-soundness); Phase 2 computes the residue's
min; the composition equals `canonMin`. This is the object the whole track builds toward.

> **Refinement (2026-07-11): the factorization is an *alternating fixpoint*, not a single two-phase split.**
> Because almost every residue is *fused* (a real decision hides a symmetry, or vice-versa), Phase 1 and Phase 2
> **interleave** — `… ∘ phase2 ∘ phase1 ∘ phase2 ∘ phase1 …`, resolving **one pairwise relation at a time**, the
> rigid solve's kernel feeding *de-fused* symmetry back into Phase-1 consumption
> (`chain-descent-ir-blindspot-solver.md` §11.11 engine + STATUS). This is **stronger** than `phase2 ∘ phase1`
> and does **not** disturb Stage 0: `complete_of_isCanonicalForm` is construction-agnostic, so `Sound ∧
> IsoInvariant ⟹ Complete` covers the fixpoint unchanged (it only constrains `cand G`, not how it is produced).
> It does reshape **Stage 2** (below): the composition lemma becomes a **fold of `coversOrbits_append` over the
> interleaving steps** — an induction on alternation depth — not one append. The operative correctness condition
> is **local rigidity at the relation being forced** (a consume-before-force schedule); soundness + iso-invariance
> come from per-step verification + `cl_up` confluence, so a bad schedule costs only an unnecessary-but-sound
> branch, never correctness. A single `phase2 ∘ phase1` append is the *fusion-free special case*.

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

## 3. The stages (what is new vs. reusable)

★ = new build · ○ = reuse existing substrate.

**Stage 0 — the correctness framework + the branching descent (★, foundational).** Two sub-parts:
- **0a — the correctness framework (LANDED 2026-07-11, `ChainDescent/CanonicalForm.lean`).** `IsCanonicalForm`
  = sound ∧ iso-invariant; **`complete_of_isCanonicalForm`** gives completeness for free; the `lexMin` selection
  combinator (`isCanonicalForm_lexMin`) reduces a canonizer's correctness to (i) each candidate is a relabelling,
  (ii) `cand (relabelAdj σ G) = cand G`. Spec is **NOT** the global lex-min (deferral gives a different
  iso-invariant form). Supersedes the single-path `canonForm?` as the spec surface (the single-path object stays
  valid for the all-symmetric pole / confinement).
- **0b — the branching descent model (★, remaining).** Model the consume/branch IR descent so that its
  reached-leaf matrix set instantiates `cand G` and (i)+(ii) become dischargeable. *This is the piece the Lean
  has nothing like today (single-path, no branching/oracle/phases); it is the "biggest conceptual leap".*

**Stage 1 — consume-soundness: orbit-pruning preserves the min (★, substrate ○).** If the selected cell is one
`Aut_D`-orbit, the sibling leaf-sets are Aut-images of each other, so their mins coincide and pruning to one
representative preserves `canonMin`. Substrate: `Confinement.SelectedCellIsOrbit` (`Confinement.lean:41`) +
`labelledAdj` Aut-invariance + direction-invariance (`warm_6_2` `ChainDescent.lean:700`, `warmRefine_swap`
`:789`). This is the correctness of the CONSUME disposition.

**Stage 2 — the composition `canonMin = phase2 ∘ phase1` (★, substrate ○).** `phase1` iterates Stage-1
pruning to the rigid residue (a node where no cell is a consumable orbit = `IsBase`-of-the-consumed-group);
`phase2` is the residue's leaf-min. Prove the composition equals `canonMin`. Substrate: **`coversOrbits_append`
(`Cascade.lean:1122`) — the base-sequence PHASE SPLIT** (partial coverage on `bs₁` glued to full coverage on
`bs₂`) is exactly "resolve the symmetric phase, then the rigid phase" as one ordering;
`stabilizerAt_eq_closure_gensAt_of_coversOrbits` (`Cascade.lean:1090`) = harvest completeness;
`Phase2Handoff.handoffBase_relabel` (`Phase2Handoff.lean:60`) = residue iso-invariance;
`spine_branch_independent` (`Spine.lean:350`) = the partition substrate the sub-descents share.
**Interleaving (2026-07-11):** since fused residues alternate the phases (`… ∘ phase2 ∘ phase1 …`, §1
refinement), Stage 2 is the *iterated* form — a **fold of `coversOrbits_append` over the alternation**, inducting
on interleaving depth; a single append is the fusion-free special case. Stage 0's completeness payoff is
unaffected (construction-agnostic).

**Stage 3 — plug in the rigid solver as the `phase2` witness (★ = the IR track, separate).** `phase2` must
satisfy `Phase2.Sound`/`IsoInvariant` (`Phase2Handoff.lean:78,86`) — witnessed by **Algorithm R**
(`chain-descent-ir-blindspot-solver.md` §11.12). This is a *dependency*, not part of this framework: the
composition is stated against the `Phase2.Solver` **contract**, so Stages 0–2 proceed with `phase2` abstract
and the solver drops in when built. **Status (2026-07-11): the C# side is BUILT + WIRED end-to-end** — `Option2Solver.cs`
(recover→solve→emit→verify, ring-general; §11.12 B1a/b/c + B2 + B5 + the B1d `SolveOverA` affine-frame emit LANDED, 28
tests) wired in `ChainDescent.Search` at the **root** (`depth == 0`, behind `EnableRigidSolver`, default ON). The emit
now closes the m≥8 completeness stall AND the large-`|A|` exponential (poly for bounded rank); remaining C# = B1d general
arity + try-both-sides + the solve-speed follow-on, and B4 (σ-fold, the mixed/pinned-prefix residue). The **Lean witness
(P1–P4) is not started** — that is the Stage-3 Lean obligation proper (the C# solver is its runtime reference, per
build-first). Detail = §11.12 + the IR-doc PICK-UP-HERE banner.

**Stage 4 — poly-or-flag for the composition (★, = the cost bridge).** `phase1` poly (bounded consume path:
`defaultSpineChain_reaches_leaf` ≤ n nodes, per-node `descentCost_le` ≤ n⁴) + `phase2` poly-or-flag ⟹ the
composition is poly-or-flag. This is the endgame **consumption bridge** (§4.3) specialized to the composed
object, and it is where the **certified-order flag** (`|⟨harvested path-fixing gens⟩| > 2^baseMax(n)`,
Schreier–Sims-computable; replaces the vacuous `hflag`, `[[project_confinement_bundle_vacuity_2026-07-10]]`)
supplies P1's largeness certificate soundly.

---

## 4. Dependencies, sequencing, first step

```
Stage 0 (canonMin spec) ──┬─→ Stage 1 (consume-sound) ──→ Stage 2 (composition) ──┬─→ Stage 4 (poly-or-flag) ─→ mixed canonizer
                          │                                                        │
Rigid solver (IR §11.12) ─┴────────────────────────────→ Stage 3 (phase2 witness)─┘
```

- **Start-anytime, independent:** Stage 0 (the spec is self-contained), and the rigid solver's P1 (extraction
  soundness, `chain-descent-ir-blindspot-solver.md` §11.12).
- **Gated:** Stage 2 on Stages 0+1; Stage 3 on the rigid solver; Stage 4 on the cost bridge + the certified
  flag.
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
