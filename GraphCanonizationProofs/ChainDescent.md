# Chain-descent canonizer — Lean proving guide

Self-contained companion to [`ChainDescent.lean`](./ChainDescent.lean). Everything
needed to work on the proofs is here: what the C# implementation does, how the
Lean model relates to it, the modelling decisions, the current proof state, the
hardness map, and the open work. This file is meant to contain the information
from the `docs/` files, however if you do need them they are available at
`docs/chain-descent-calculator.md`
`docs/chain-descent-strategy.md`
`docs/chain-descent-simplified-overview.md`

---

## 1. The project in one paragraph

**Chain descent** is a candidate polynomial-time graph canonizer: a budget-bounded
recursive descent of the individualization–refinement (IR) tree that returns the
lex-smallest leaf adjacency matrix as the canonical form. A canonical form is an
`S_n`-orbit minimum, so a polynomial bound here would imply GI ∈ P — an open
problem. The project does not claim to close it; it *isolates* the hard part
behind one component (the oracle) and proves the surrounding structural
invariants. `ChainDescent.lean` is that proof effort. Its centrepiece is
**invariant 6.2** (`warm_6_2`): the two directions of a genuine ordering decision
induce the *same cell partition*.

---

## 2. The C# implementation being modelled

The canonizer is `GraphCanonizationProject/ChainDescent.cs` together with
`CanonGraphOrdererChainDescent.cs`. Structure:

- **`CanonGraphOrdererChainDescent`** — Tier-0 component decomposition (a disjoint
  union's `Aut` factors over components), then dispatch each connected component
  to the harness.
- **`ChainDescent` (the harness)** — `Search`: warm-refine the partition (1-WL);
  if discrete, emit a leaf; else pick the lowest-cell-id non-singleton cell (the
  *target cell*, iso-invariant), ask the oracle which vertices to branch on, and
  recurse. `Branch`: individualize a vertex `v` (write `v < w` into the
  partial-order matrix `P` for every cell-mate `w`), transitively close, recurse.
  `HandleLeaf`: build the permuted matrix, keep the lex-min, harvest verified
  automorphisms from coinciding leaves into a `PermutationGroup`.
- **Budget / flag.** The descent carries a polynomial node budget; exceeding it
  raises `CanonizationFlaggedException`. A flag is an honest "not handled" — never
  a wrong answer, never an exponential run.
- **`ITransversalOracle` / `CascadeOracle`** — the *T-C seam* (§8). Phase-1
  `CascadeOracle` certifies nothing a priori, so the harness behaves as a
  budget-bounded IR search; a future linear oracle is what would supply a-priori
  transversals.
- **`WarmPartition`** (`WarmPartition.cs`) — 1-WL colour refinement,
  warm-started from the carried `CellOf`. Each vertex's new colour is the
  lex-rank of its signature `[own-colour, sorted multiset of
  (neighbour-colour, adjacency-value, P-relation)]`.

---

## 3. Lean ↔ C# correspondence

| Lean (`ChainDescent.lean`)        | C# counterpart                              | Faithful? |
|-----------------------------------|---------------------------------------------|-----------|
| `refineStep` / `signature` / `refineStep_iff` | `WarmPartition.RefineRound` | **Yes** — `refineStep_iff` (equal new colour ⟺ equal old colour ∧ equal signature multiset) is exactly `RefineRound` |
| `warmRefine` (iterate `refineStep` `n×`) | `WarmPartition.Refine` (iterate to fixpoint) | **Yes** — same partition; `n` rounds always reach fixpoint |
| `applyGuess P a b dir` (writes one entry pair) | `Branch` (writes `v < w` for the whole cell) | **Simplification** — single-pair models a 2-element target cell `{e,f}`, i.e. one genuine decision |
| `closeStep` / `transitiveClose`   | `TransitiveClose`                            | **Diverges** — but TC is *relegated* (§4), so absent from the proof path |
| fresh-colour individualisation (`χι` hypotheses) | refinement separating the individualized vertex | **Model choice** (§5) — true by construction vs. by refinement |

`adj` is `AdjMatrix n` (a `Fin n → Fin n → Nat` wrapper); `P : PMatrix n`;
`χ : Colouring n`.

---

## 4. TC relegation — the central modelling decision

The C# `TransitiveClose` is a Floyd–Warshall closure of the `less` relation that
**returns `false`** on a cycle (`i == j`) or a direction conflict
(`cur == GREATER`); `Branch` then **prunes** that child (`if (!TransitiveClose) return;`).

The Lean model **relegates** transitive closure entirely: a guess is just
`applyGuess` writing a single `(a,b)`/`(b,a)` entry pair — no closure in the
refinement loop. An inconsistent partial order is treated as a *lex-min ranking*
criterion, not a pruning step.

**Why this is equivalent to the C# (no refactor needed).** A non-lex-min branch is
never chosen, so "pruned" and "kept but ranked worse and discarded by lex-min" are
observationally identical for the canonical output. Concretely: (a) a consistent
partial order always extends to a linear order, so a *valid* leaf always exists
below any consistent node; (b) an inconsistent/cyclic configuration ranks
strictly worse than any valid one. Hence the lex-min leaf is valid either way —
eager pruning (C#) and relegation (Lean) produce the same canonical form.

**Consequence for proofs.** The post-guess matrix is exactly `applyGuess P₀ a b dir`,
which differs from `P₀` at *only* the `(a,b)` and `(b,a)` entries. This is the
fact that makes invariant 6.2 provable (§7).

**Caveat, resolved.** The unconditional lemma "`transitiveClose` commutes with the
`less ↔ greater` swap" is **false** (`closeStep`'s `less`-first tie-break is not
σ-symmetric — machine-checked by `transitiveClose_swap_false`, witness
`conflictMatrix`). But `conflictMatrix` is a *conflicted* matrix — exactly the
kind the C# `TransitiveClose` rejects. Under TC relegation that whole question is
moot; the refutation is kept only as a record of a dead route.

---

## 5. Fresh-colour individualisation

`warm_6_2` and its relatives take a starting colouring `χι` in which the guessed
vertices `a`, `b` are **singletons** (hypotheses `ha`/`hb`: no other vertex shares
their colour). This models standard IR individualisation — assigning the
individualized vertex a fresh, unique cell id.

This is **equivalent to a design assumption already in force**: the canonizer's
oracle (its transposition pre-check) is justified by "the guessed pair `A`, `B` are
always singletons after refinement." The C# realises that via refinement
separating the vertex by its `P`-signature; the Lean model makes it true by
construction. On the design's intended domain the two coincide — and the
fresh-colour model closes the gap the C#'s refinement-based separation leaves
(a guessed vertex could in principle collide with an outside vertex by signature
coincidence; the fresh colour rules that out).

---

## 6. The model objects and the one axiom

- `POE` — partial-order entry: `less` | `unknown` | `greater`, with the
  involution `POE.swap` (`less ↔ greater`, `unknown` fixed).
- `PMatrix n := Fin n → Fin n → POE` — the partial-order matrix.
- `Colouring n := Fin n → Nat` — a vertex colouring.
- `applyGuess P a b dir` — set `P(a,b) := dir`, `P(b,a) := neg dir`, else `P`.
- `signature adj P χ v` — the multiset of `(χ u, adj v u, P v u)` over all `u ≠ v`.
- `refineStep` — **the one axiom.** One round of 1-WL refinement, characterised by
  `refineStep_iff`:
  > `refineStep adj P χ v = refineStep adj P χ w  ↔  χ v = χ w ∧ signature adj P χ v = signature adj P χ w`.

  It is axiomatised, not defined, because the colour *encoding* (how
  `(old colour, signature)` injects into `Nat`) is irrelevant to partition-level
  reasoning. Every proof uses **only** `refineStep_iff` — never the encoding. This
  is the sole modelling axiom; everything else is a concrete `def`.
- `warmRefine adj P χ := (refineStep adj P)^[n] χ` — warm refinement (`n` rounds
  always suffice to reach fixpoint).
- `samePartition χ χ' := ∀ i j, χ i = χ j ↔ χ' i = χ' j` — same cell partition;
  an equivalence relation (`samePartition.refl/symm/trans`).

---

## 7. Proof state

All results below are **proved with no `sorry`** and depend only on
`propext`, the modelling axioms `refineStep` / `refineStep_iff`,
`Classical.choice`, `Quot.sound` — in particular **no `native_decide`**
(machine-checked refutations use kernel `decide`).

**Proved:**

- `warm_6_2` — **invariant 6.2.** For a guessed pair `(a,b)` and a starting
  colouring `χι` with `a,b` singletons, warm refinement after `a < b` and after
  `b < a` induce the *same partition*. Proof: `applyGuess` differs only inside
  `{a,b}`, so off `{a,b}` the signature cannot see the guess direction; `a,b`
  stay singletons; induction on the refinement round.
- `warmRefine_refines` — warm refinement is split-only (never merges cells).
- `warmRefine_swap` / `warmRefine_applyGuess_swap` — direction-blindness:
  `warmRefine` commutes with `PMatrix.swap` at the partition level. (It
  *co-swaps the base matrix*, so it relates `(P₀, less)` to `(swap P₀, greater)` —
  not a fixed-`P₀` `<`/`>` antisymmetry beyond `warm_6_2`.)
- `applyGuess_comm` — guesses on distinct pairs commute (disjoint entry writes);
  the descent state for a fixed guess set is order-independent.
- `warmRefine_agree_off` — **the cross-branch-sharing theorem.** If `P` and `Q`
  agree on every entry with an endpoint outside a vertex set `D`, and `D` is
  all-`χι`-singletons, then `warmRefine` gives the same partition. Generalises
  `warm_6_2` from one decision to a set: all `2^d` guess-states over a
  `d`-decision set carry *one* partition. The residual exponential then lives
  entirely in the order-labels (a `Z₂^d` optimisation).
- `warmRefine_agree_off'` — **the composable form.** As above but the two
  starting colourings need only be `samePartition`-equal, not literally equal.
  This is the version that *chains across descent levels* (`warmRefine_agree_off`
  is the `χ = χ'` special case) and is the inductive engine of the spine (§11).
- `PartitionInvariant`, `target_direction_blind`, `target_agree_off` — the
  target-cell layer. A selector is *partition-invariant* if it reads only the
  partition; `target_direction_blind` (one decision) and `target_agree_off`
  (a decision set, composable) then say the *next branch target* is shared —
  the per-level step of the spine argument (§11).
- Supporting lemmas: `refineStep_preserves_singleton`,
  `iterate_refineStep_preserves_singleton`, `signature_applyGuess_off`,
  `signature_eq_of_samePartition`, `signature_swap`, `signature_agree_off`.

**Orbit recovery — §16/§17/§18 (added 2026-05-26):**

- §16 — **Shared infrastructure:** `individualizedColouring`,
  `FixesPointwise`, `signature_invariant_of_isAut`,
  `warmRefine_invariant_of_isAut`, and the **partition-level
  predicate `OrbitPartition adj P S`** with its equivalence-relation
  lemmas (`refl`/`symm`/`trans`).
- `OrbitPartition.subset_warmRefine` — **the trivial direction**:
  orbits refine 1-WL cells. Axiom-clean, the load-bearing half of
  both tiers' squeeze.
- §17 — **Tier 1 (CFI):**
  - `aut_trivial_of_discrete_warmRefine` (Fact B, axiom-free),
    `orbit_iff_eq_of_discrete_warmRefine` (axiom-free).
  - `CascadesAt adj P k` predicate + `cascadesAt_univ` theorem (every
    graph cascades at depth `n`, axiom-free).
  - **`theorem_1_HOR_at_depth`** — the depth-parametrised core, **proved
    axiom-free**. Takes `CascadesAt adj P k`, returns orbit recovery
    at `|S| ≤ k`. All Tier-1 specialisations (`theorem_1_HOR_at_n`,
    legacy `theorem_1_HOR`, `theorem_1_HOR_pointwise`) are axiom-free
    corollaries.
  - CFI placeholder axioms: `IsCFI` (abstract Prop), `cfi_depth_bound :
    Nat → Nat`, `cfi_depth_bound_le`, `cfi_cascades_polynomially` (the
    Tier-1 Fact A). `theorem_1_HOR_cfi` (proved): CFI orbit recovery at
    polynomial depth, conditional on the three placeholders.
- §18 — **Tier 2 (schurian schemes):** `SchemeProfile` bundled
  structure (with Step 1 / Step 2 fields), `SchemeProfile.warm_iff_profile`
  (derived squeeze), and **`theorem_2_HOR`** conditional on the
  Tier-2 Fact A analogue `schurian_scheme_profile_exists` +
  abstract predicate `IsSchurianSchemeGraph`.

**Polynomial-depth restructure (2026-05-26).** The original Tier-1
existential axiom `cfi_cascade_exists` (no depth bound — trivially
true via `S = univ`) has been replaced with the depth-parametrised
`CascadesAt` predicate plus the three CFI placeholders above. Net
effect: the structural orbit-recovery theorems (`theorem_1_HOR_at_depth`
and its existential corollaries) are **axiom-free**; the
CFI-polynomial-depth claim layers the Fact-A axiom on top.

The Tier 1 / Tier 2 parallel is now strict — each tier has:
1. An abstract Prop predicate (`IsCFI` / `IsSchurianSchemeGraph`).
2. A single Fact-A-shaped existence axiom (`cfi_cascades_polynomially`
   / `schurian_scheme_profile_exists`).

The structural assembly is identical between tiers.

**CFI infrastructure — split into `ChainDescent/CFI.lean` (2026-05-26).**
The CFI construction lives in
[`ChainDescent/CFI.lean`](./ChainDescent/CFI.lean), a sub-module of
the same `ChainDescent` library (built via `defaultTargets =
["ChainDescent", "ChainDescent.CFI"]` in `lakefile.toml`). Split to
keep `ChainDescent.lean` under ~4000 lines as CFI work scales.

*Stage 1 (foundations):* `CFIBase`, neighbours/degree, gadget vertex
count, `evenSubsetsOfNeighbors`, `triangleBase` smoke test.

*Stage 2.1 (vertex type):* `SubsetVertex`, `EndpointVertex`,
`CFIVertex` as `Σ + Subtype + ⊕`. Explicit `Fintype` + `DecidableEq`
instances via `inferInstanceAs` (auto-synthesis fails on the nested
Sigma-of-Subtype-of-Finset-mem). `triangleBase_cfiVertex_card = 18`
verified via `native_decide`.

*Stage 2.2 (adjacency):* `cfiAdj : CFIVertex H → CFIVertex H → Nat`
encoding intra-gadget `(w ∈ S) ⊕ b` and inter-gadget untwisted bridge
rules; `cfiAdj_symm` and `cfiAdj_loopless` proved.

*Stage 2.3 (lift to AdjMatrix + concrete IsCFI):*
`cfiAdjMatrix : CFIBase m → AdjMatrix (Fintype.card H.CFIVertex)`
(noncomputable, via `Fintype.equivFin`); `cfiAdjMatrix_symm` /
`cfiAdjMatrix_loopless` proved; `IsCFI' : AdjMatrix n → Prop`
concrete predicate; `cfiAdjMatrix_is_cfi` self-witness. Smoke test on
`triangleBase` confirms `IsCFI' triangleBase.cfiAdjMatrix` holds.

*Tier-1 CFI form relocated (§10 of `CFI.lean`):*
`cfi_depth_bound`, `cfi_depth_bound_le`, `cfi_cascades_polynomially`,
and `theorem_1_HOR_cfi` now live in `CFI.lean` and use the concrete
`IsCFI'` predicate. The abstract `axiom IsCFI` is retired (was in
`ChainDescent.lean §17.4`). Tier-1 axiom budget: 2 placeholders
(down from 3). Tier 2 still uses its abstract Prop (pending its
concrete predicate).

*Depth-bound API tightened (2026-05-26):* `IsCFI'` is now a
`structure` in `Type` with projections `m`, `H`, `e`, `matching`
(was `∃` in `Prop`). The depth function takes the witness:
`cfi_depth_bound : IsCFI' adj → Nat`, with the bound axiom
`cfi_depth_bound h ≤ h.baseSize` (= `h.m`). New connector
`IsCFI'.six_baseSize_le : 6 * h.baseSize ≤ n` (axiom-clean) chains
through the cardinality identity `card CFIVertex = ∑ gadgetSize ≥ 6m`.
Combined: `cfi_depth_bound h ≤ n / 6`, strictly tighter than the
axiom-free `theorem_1_HOR_at_n`'s `≤ n`. Corollaries
`theorem_1_HOR_cfi_baseSize` and `theorem_1_HOR_cfi_n_bound` expose
the simpler bound forms. The CFI placeholder axioms now carry
content over `cascadesAt_univ`.

*Stage 4 / M1 — depth-bound concretized (2026-05-26):*
`cfi_depth_bound` is now `def cfi_depth_bound h := h.baseSize` (was
axiom); `cfi_depth_bound_le := Nat.le_refl _` (was axiom). Tier-1
axiom budget **3 → 1** — only `cfi_cascades_polynomially` (the actual
cascade lemma) remains. M2 (gadget-level lemmas), M3 (bridge
propagation), M4 (cascade assembly) are pending multi-week tracks
that together discharge the cascade axiom.

*Stage 4 / M2 — gadget-level distinguishability (2026-05-26):* §13 of
`ChainDescent/CFI.lean`. The first cascade lemma:
`IsCFI'.refineStep_endpoint_false_ne_true` — with `a_∅^v` individualized,
one refineStep round distinguishes v's b=0 endpoints from v's b=1
endpoints. Build-up:

- §13.1-2: `CFIBase.aEmpty v`, `CFIBase.endpoint hw b`, plus
  `cfiAdj_aEmpty_endpoint_false/true` evaluation lemmas (a_∅^v
  adjacent to e^b iff b = true).
- §13.3-4: Fin-n extractors `IsCFI'.seedVertex` / `endpointVertex`
  via `h.e.symm`; adjacency facts `IsCFI'.adj_seed_endpoint_false/true`
  transported through `h.matching`.
- §13.5: generic singleton-individualization lemmas
  (`individualizedColouring_singleton_eq_seed_iff` is the key
  uniqueness fact).
- §13.6: `IsCFI'.signature_endpoint_false_ne_true` — signature
  multisets differ. Witness tuple `(χ seed, 1, P endpoint_true seed)`
  in et's signature but not ef's.
- §13.7: M2 headline `IsCFI'.refineStep_endpoint_false_ne_true` via
  `refineStep_iff`.

All M2 lemmas axiom-clean (depends only on `refineStep`,
`refineStep_iff`, and standard basis).

*Stage 4 / M3.A + M3.B — multi-seed cascade setup (2026-05-26):*
§13.8-§13.9 of `ChainDescent/CFI.lean`.

§13.8 / M3.A:
- `IsCFI'.allSeeds := Finset.univ.image h.seedVertex` — the cascade
  individualization (one seed per base vertex).
- `IsCFI'.seedVertex_injective` (via `aEmpty` injectivity through
  Sigma.fst + h.e Equiv).
- `IsCFI'.allSeeds_card : |allSeeds| = h.baseSize`.
- `individualizedColouring_eq_iff_of_mem` — generic: for `v ∈ S`,
  `χ_S u = χ_S v ↔ u = v`.

§13.9 / M3.B:
- `IsCFI'.signature_endpoint_false_ne_true_allSeeds` and
  `IsCFI'.refineStep_endpoint_false_ne_true_allSeeds` — M2's endpoint
  split under the multi-seed colouring `χ_{allSeeds}`. Witness tuple
  unchanged; multi-seed uniqueness replaces singleton uniqueness.

All axiom-clean. The cascade individualization witness is now
constructible and size-bounded; M3.C-M3.E (bridge propagation step
lemma, subset distinction, per-type signature classification) and M4
(cascade assembly via multi-round refinement induction) remain.

*Stage 4 / M3.C — b=true endpoint inter-gadget distinction
(2026-05-26):* §13.10 of `ChainDescent/CFI.lean`. First inter-gadget
cascade lemma: under `χ_{allSeeds}`, one `refineStep` round
distinguishes `e^1_{v→w}` from `e^1_{v'→w'}` for v ≠ v'.

Argument parallels M3.B but uses cross-gadget non-adjacency
(`CFIBase.cfiAdj_aEmpty_endpoint_diff_gadget`, lifted to
`IsCFI'.adj_endpoint_seed_diff_gadget`) in place of within-gadget
parity-mismatch. Witness `(c_v, 1, P · seed_v)` is present in
`e^1_{v→w}`'s signature (seed_v in same gadget, adj=1) but not in
`e^1_{v'→w'}`'s (cross-gadget, adj=0).

The b=0 inter-gadget case is NOT covered: neither b=0 endpoint is
adjacent to its own seed, so signatures coincide at round 1.
b=0 inter-gadget distinction requires multi-round bridge propagation
(deferred). All M3.C lemmas axiom-clean.

*Stage 4 / M3.D Phase 1 — local bridge propagation step lemma
(2026-05-26):* §13.11 of `ChainDescent/CFI.lean`. The inductive
engine for cascade: given arbitrary χ with bridge partners
distinguished (P1) and the bridge-partner colour not appearing at any
adj=1 neighbour of the second endpoint (P2), one `refineStep`
distinguishes the original endpoint pair.

Prereqs: `CFIBase.cfiAdj_bridge` (cfiAdj=1 for bridge edges, §13.2),
`IsCFI'.adj_bridge` (Fin n lift, §13.4), `IsCFI'.endpointVertex_ne_bridge`
(distinctness via loopless ⟹ v ≠ w ⟹ Sigma.fst, §13.4).

Headline: `IsCFI'.refineStep_bridge_step` — refineStep distinguishes
endpoints given P1, P2. Witness tuple `(χ bp, 1, P ev bp)` from
bridge partner. All axiom-clean.

**Phase 2 (deferred multi-week):** the multi-round driver that
iterates the step lemma, maintaining (P2) round-by-round via base-
graph distance accounting. Requires connectedness of H.

*Stage 4 / Phase 2.0 + 2.1 (2026-05-26):* first cascade step beyond
round 1. §13.12 / §13.13.

§13.12: structural helpers.
- `adj_endpointVertex_eq_one_iff` — bridge condition formula.
- `adj_seedVertex_eq_one_iff` — adj=1 to seed iff b=1 endpoint at
  the seed's gadget (case analysis on `h.e u`).

§13.13: first concrete cascade step.
- `refineStep_endpoint_true_intra_gadget_partner` — at round 2,
  b=true endpoints at the same gadget toward different partners
  get distinct colours. Proof applies `refineStep_bridge_step`
  with χ = round-1 colouring, (P1) from M3.C, (P2) via signature
  tuple presence (the seed_w-marked tuple distinguishes).

Validates the Phase 1 + Phase 2 architecture: arbitrary cascade
cases can be discharged via the step lemma + (P2) verification.

*Stage 4 / Phase 2.3 (2026-05-26):* subset-vertex inter-gadget
distinction at round 2 — the **first cascade step for subset
vertices**. §13.14-§13.17 of `CFI.lean`.

§13.14: subset vertex infrastructure.
- `CFIBase.subset hS` — general subset constructor (generalises
  `aEmpty v`, which is the S=∅ case).
- `IsCFI'.subsetVertex hS` — Fin-n extractor; `seedVertex v` is the
  empty-subset specialisation.
- `adj_subsetVertex_endpoint_*` — Fin-n adjacency facts (same-gadget
  parity-mismatch = adj=1; diff-gadget always adj=0).
- `adj_subsetVertex_eq_one_iff` — characterisation parallel to
  `adj_seedVertex_eq_one_iff` (which is its S'=∅ specialisation).

§13.15: M3.B+ generalised parity distinction.
- `signature_endpoint_b0_ne_b1_general_allSeeds` /
  `refineStep_endpoint_b0_ne_b1_general_allSeeds` — strengthens
  M3.B from "same gadget" to "b=0 endpoint at any gadget v' vs b=1
  endpoint at gadget v are distinguished at round 1." Same witness
  tuple as M3.B+M3.C; the absence argument case-splits v = v' vs
  v ≠ v'.

§13.16: factored Approach-3 subset step lemma.
- `signature_subset_step` / `refineStep_subset_step` — generic over
  χ. Parallel to `refineStep_bridge_step` for bridges. Preconditions
  `hwS` (w ∉ S, witness endpoint exists) + `hno_match` (witness
  colour absent at adj=1 neighbours of the other subset). Conclusion:
  the two subset vertices get distinct refineStep colours.

§13.16.5: `IsCFI'.adj_symm` — `adj.adj i j = adj.adj j i` via
`h.matching` + `cfiAdj_symm`. Bridges signature/iff conventions.

§13.17: Phase 2.3 headline.
- `refineStep_subset_inter_gadget_round2` — at round 2 under
  χ_{allSeeds}, subset vertices at gadgets v ≠ v' get distinct
  colours, provided the LHS has w ∈ N(v) \ S as witness. Proof
  applies §13.16's step lemma with χ = χ_1; verifies hno_match by
  cases on b'' (b''=false → M3.B+; b''=true → M3.C).

**Hypothesis qualifier**: The `w ∉ S` precondition is essential —
deg-even bases (Rook3x3) admit the degenerate `S = N(v)` case which
has no b=1 adjacent endpoint witness. That case is deferred to a
later cascade round (post-Phase 2.2).

All Phase 2.3 lemmas axiom-clean (`refineStep` + `refineStep_iff` +
standard basis).

*Stage 4 / M4 (cascade discharge for OddDegree CFI) — DONE 2026-05-26.*
§13.21-§13.24 of `CFI.lean`. **Tier-1 cascade axiom discharged**
for OddDegree H (every base vertex has odd degree, ≥ 3 — covers
K₄, K₃,₃, Petersen).

§13.21: `IsCFI'.OddDegree` predicate + `exists_witness_of_oddDegree`
(even subsets always have a non-element) + `exists_phase22_witness`
(construct a `{v, x_other}` even subset for Phase 2.2 invocations).

§13.22: Phase 2.X — b=0 within-gadget partner at round 4 via bridge
step + Phase 2.2 + cross-type lift (OddDegree provides all witnesses
automatically).

§13.23: Phase 2.4 — subset by S at same gadget at round 5 via
direct signature argument using b=0 endpoint witness + Phase 2.X +
M3.B+ lifted χ_1 → χ_4.

§13.24: iteration helpers (`refineStep_iter_le_eq`,
`warmRefine_eq_iter_eq`) + **`cfi_cascades_polynomially_oddDeg`**:
case-analysis on `(h.e i, h.e j)` with 10 sub-cases. Each invokes a
phase lemma at the appropriate round (1-5) and lifts to warmRefine.
Discharges `cfi_cascades_polynomially` for OddDegree + n ≥ 5.

**`theorem_1_HOR_cfi_oddDeg`** — Theorem 1 (CFI form) **axiom-free**
for OddDegree H. Depends only on `refineStep` + `refineStep_iff` +
standard basis. No CFI-specific axioms in dependency closure.

**`5 ≤ n` side condition — DISCHARGED 2026-05-26.** The earlier
`hn_ge_5 : 5 ≤ n` parameter is gone. `cfi_cascades_polynomially_oddDeg`
now case-splits on the base-size dichotomy: `h.m = 0 → n = 0`
(via `card_CFIVertex`-collapses-to-zero on the empty index, so
`CascadesAt` holds with `S = ∅`); `h.m ≥ 1 → 6 ≤ n` (via
`six_baseSize_le`), hence `5 ≤ n`. `theorem_1_HOR_cfi_oddDeg` drops
the hypothesis correspondingly and remains axiom-clean.

**Remaining caveat**: general-degree case (Rook3×3) still uses the
original axiom — saturated subsets need more cascade rounds.

*Stage 4 / Phase 2.2 (2026-05-26):* b=0 endpoint inter-gadget at
round 3 — first b=0 cascade step. §13.18-§13.20 of `CFI.lean`.

§13.18: M3.B++ prereq.
- `adj_subsetVertex_seedVertex` — subset-subset adj=0 helper.
- `signature_subsetVertex_ne_endpoint_true_allSeeds` /
  `refineStep_subsetVertex_ne_endpoint_true_allSeeds` — subset
  (any) vs b=1 endpoint at v distinguished at round 1. Cleaner
  than M3.B+: multi-seed forces u=seed_v but subsets have no
  subset adjacencies (including to seeds), instant contradiction.

§13.19: cross-type round-2 prereq.
- `signature_subsetVertex_ne_endpoint_false_round2` /
  `refineStep_subsetVertex_ne_endpoint_false_round2` — at χ_2,
  subset with witness (x ∈ N(v) \ S) vs b=0 endpoint (any gadget)
  distinguished. Witness `(χ_1 (e^1_{v→x}), 1, ?)`. Case analysis
  on u adj=1 to the b=0 endpoint: subset case → M3.B++; endpoint
  (bridge partner) case → M3.B+.

§13.20: Phase 2.2 headline.
- `refineStep_endpoint_false_inter_gadget_round3` — at round 3, b=0
  endpoints at v ≠ v' distinguished, given witness subset (S, x) at
  gadget v with w ∈ S and x ∈ N(v) \ S. Direct signature argument:
  witness `(χ_2 (a_S^v), 1, ?)`. Case on u adj=1 to RHS b=0 endpoint:
  subset → Phase 2.3 with LHS witness; bridge partner → cross-type.

**Hypothesis qualifier**: Witness (S, x) requires `deg(v) ≥ 3`
(so a 2-element even subset with witness exists). For deg(v) = 2,
no witness — that degenerate case needs more cascade rounds (subset
propagation through neighbouring gadgets).

All Phase 2.2 lemmas axiom-clean (`refineStep` + `refineStep_iff` +
standard basis).

*Combinatorial identity (§11 of `CFI.lean`):*
`Finset.card_powerset_filter_even` (private) proves "even subsets of
a nonempty `d`-element set = `2^(d-1)`", via Mathlib's alternating
sum lemma. Lifted through `Fintype.card_sigma` / `card_sum` /
`card_coe` to give `card_CFIVertex : Fintype.card H.CFIVertex =
H.cfiVertexCount`. All axiom-clean (standard basis only).

*Pending:* Stage 3 (Aut structure). Stage 4 (cascade lemma).

**Tier 2 Lean — Stage T2.1 DONE 2026-05-26.** New module
[`ChainDescent/Scheme.lean`](./ChainDescent/Scheme.lean) (default
build target alongside `ChainDescent` and `ChainDescent.CFI`).
Iteration helpers `refineStep_iter_le_eq` /
`warmRefine_eq_iter_eq` relocated from `CFI.lean §13.24` to
`ChainDescent.lean §16.4` (tier-agnostic, used by both Tier 1's
M4 and Tier 2's planned Step 2 induction).

`Scheme.lean` contents:
- §1 `AssociationScheme n` structure: `rank`, `rel`,
  `rel_zero_iff_eq`, `rel_symm`, `rel_partition` (`∃!`),
  `intersectionNumber`, `intersectionNumber_well_defined`.
  Helpers: `relOfPair` + `rel_relOfPair`, `relOfPair_unique`,
  `rel_iff_relOfPair`, `relOfPair_symm`, `relOfPair_self`,
  `relOfPair_eq_zero_iff`.
- §2 `IsSchemeAut S π` predicate, with `refl`/`trans`/`symm`
  group structure and `relOfPair_eq` (scheme-Aut preserves
  `relOfPair`). `SchurianScheme n` extends `AssociationScheme`
  with the `schurian` field.
- §3 Smoke test: `trivialScheme : AssociationScheme 1` and
  `trivialSchurianScheme : SchurianScheme 1`.

All T2.1 declarations axiom-clean (`propext` + `Classical.choice`
+ `Quot.sound`; no `refineStep`).

**Tier 2 Lean — Stages T2.2 + T2.3 infrastructure DONE 2026-05-26.**
Same `Scheme.lean` module extended (~700 lines total now).

- §4 — **T2.2 v-profile + Step 1 (algebraic, scheme-Aut form):**
  `vProfile S v` (noncomputable Colouring n) with helpers
  `vProfile_self`, `vProfile_eq_iff`, `vProfile_eq_zero_iff`,
  `vProfile_ne_self_of_ne` (= `SchemeProfile.v_singleton`).
  `SchemeOrbitPartition` (v-stabilized scheme-Aut orbits) with
  refl/symm/trans. Step 1: `vProfile_aut_invariant`,
  `SchurianScheme.vProfile_eq_imp_schemeOrbit`,
  `SchurianScheme.vProfile_iff_schemeOrbit`.
- §5 — **SchemeGraph structure:** `scheme + J + zero_notMem_J`
  bundle, derived `adj : AdjMatrix n` (noncomputable), plus
  `adj_eq_one_iff`/`_zero_iff`/`_self`/`_symm`/`_zero_or_one`.
- §6 — **SchurianSchemeGraph:** extends SchemeGraph with two
  schurian fields w.r.t. graph-Aut (`schurian_transitive` and
  `isAut_imp_isSchemeAut`); provides graph-Aut `relOfPair_aut_eq`
  and `vProfile_aut_invariant`.
- §7 — **Step 1 in graph-Aut terms:** `GraphOrbitFixing adj v w u`
  (refl/symm/trans). Headlines `vProfile_eq_imp_graphOrbit`,
  `graphOrbit_imp_vProfile_eq`, `vProfile_iff_graphOrbit`. This is
  the `SchemeProfile.profile_iff_orbit`-shaped statement (modulo
  P-preservation bridge for arbitrary P).

All T2.2 + T2.3 prerequisites axiom-clean.

- §8.a — **S2.a: round-1 lemma — DONE 2026-05-27** (~70 lines,
  axiom-clean). Generic round-1 distinguishability: for any
  `adj`, `P`, `v`, if `refineStep adj P χ_v w = refineStep adj P
  χ_v u` for `w, u ≠ v`, then `adj w v = adj u v` (and `P w v =
  P u v`). Three forms: `refineStep_round1_pair_eq` (full),
  `refineStep_round1_adj_eq` (adj-only), and the SchemeGraph
  specialisation `SchemeGraph.refineStep_round1_J_eq` (round-1
  equality ↔ matching J-class of `relOfPair v ·`). Plus helper
  `individualizedColouring_singleton_eq_v_iff`.

**Remaining for full Step 2:** S2.b (inductive
intersection-number refinement), S2.c (convergence at depth
≤ rank + 1), S2.d (lift via `warmRefine_eq_iter_eq`). Then T2.M4
(SchemeProfile constructor + P-preservation bridge + discharge
`schurian_scheme_profile_exists`).

- §8.b — **S2.b infrastructure + count bridge + partial result —
  DONE 2026-05-27** (~280 lines, axiom-clean). Three layers:
  - §8.b.1 iteration framework: `iterSignature`,
    `iter_succ_eq_iff`, `AssociationScheme.intersectionCount_via_w`,
    `intersectionCount_eq_of_vProfile_eq`, `Step2_target`.
  - §8.b.2 count bridge: `signature_count_eq_card` and the
    general `signature_countP_eq_card` (Multiset.count → Finset.card
    via `Multiset.count_map` + `Finset.filter_val` +
    `Finset.filter_filter`); plus the iter[k+1]-applied versions
    `signature_eq_card_eq`, `signature_eq_countP_eq`,
    `iter_succ_count_eq`, `iter_succ_countP_eq`,
    `iter_succ_colour_count_eq`. The workhorse for the inductive
    step.
  - §8.b.3 partial Step 2: `iter_succ_adj_eq` (S2.a lifted to any
    depth ≥ 1), `warmRefine_adj_eq`,
    **`SchurianSchemeGraph.warmRefine_J_eq`** — warmRefine cells
    refine the J-class partition of `vProfile`. First concrete
    Step 2 partial theorem.

- §9 — **T2.M4 assembly + concrete predicate + Theorem 2 instances
  — DONE 2026-05-27** (~250 lines, axiom-clean):
  - §9 `SchurianSchemeGraph.toSchemeProfile` — the SchemeProfile
    constructor parameterised by P-invariance + `Step2_target`
    hypotheses. Plus `toSchemeProfile_trivialP` for the trivial-P
    case (P-invariance automatic).
  - §9.1 `trivialPMatrix` + `trivialPMatrix_invariant`.
  - §9.2 **`IsSchurianSchemeGraph'`** concrete predicate replacing
    the abstract `IsSchurianSchemeGraph` axiom from `§18`.
    **`theorem_2_HOR_concrete`**: the `theorem_2_HOR`-shaped
    statement derivable from concrete + P-invariance + Step2.
  - §9.3 **`theorem_2_HOR_trivial`**: end-to-end unconditional
    Theorem 2 instance for the trivial 1-vertex scheme. **First
    fully discharged Theorem 2 instance.**
  - §9.4 **`step2_of_rank_le_one`** + **`theorem_2_HOR_concrete_rank_le_one`**:
    Step 2 and unconditional Theorem 2 for all schurian scheme
    graphs with `rank ≤ 1` (covers `K_n`).

  Remaining: the inductive Step 2 proof for `rank ≥ 2` schemes
  (Johnson, Petersen, Hamming, distance-transitive DRGs).

- §10 — **Step 2 inductive step + convergence framework — DONE
  2026-05-27** (~280 lines, axiom-clean). **Major milestone**:
  the technical heart of S2.b's intersection-number induction is
  proved.
  - `Step2_at_depth G P v k` + `step2_of_step2_at_depth`: framework
    for depth-k discharge → `Step2_target`.
  - `schemePart_at G P v k` (noncomputable, recursive): partition
    predicate. Equivalence relation lemmas (`refl`/`symm`/`trans`).
  - **`iter_refines_schemePart_at` (PROVED)**: `iter[k] χ_v` refines
    `schemePart_at G P v k`. Proof via the inductive intersection-
    number step using `iter_succ_eq_iff` + `signature_eq_countP_eq`
    + the IH-derived equivalence.
  - `Step2_converges_at G P v k`: convergence statement (the
    remaining open content piece).
  - `step2_of_converges_at`: convergence + inductive step →
    `Step2_target`.
  - `step2_converges_at_zero_of_rank_le_one`: sanity check that
    the framework recovers the rank-≤-1 case at depth 0.

  **Remaining for full Tier 2**: prove `Step2_converges_at G P v
  (rank+1)` for schurian schemes — the classical coherent algebra
  content. Once discharged, every schurian scheme graph gets an
  unconditional `theorem_2_HOR_concrete` instance.

**Refuted (machine-checked, kept as record of dead routes):**

- `transitiveClose_swap` — false; `closeStep`'s `less`-first tie-break breaks
  σ-symmetry. Witness `conflictMatrix`. Moot under TC relegation (§4).
- `cell_split_uniform` — false; it claimed cell-mates keep *equal* post-guess
  signatures ("no split"). A guess on an individual vertex *does* split a cell.
  Witness `witnessP0`. The honest claim — same *partition*, not no-split — is
  `warm_6_2`.

**Open** — see §10.

---

## 8. The hardness map — why the polynomial bound is open

Canonization hardness has two axes: **cascade** (does individualizing one vertex
make refinement reach single-orbit cells?) and the **composition factors** of the
residual automorphism group. Three regimes:

- **Cascade → polynomial**, regardless of the group (cycles, strongly regular
  graphs, all Johnson graphs, CFI over cycles).
- **No cascade + abelian factors** (CFI's `Z₂^m`) **→ polynomial** via linear
  algebra (Gaussian elimination over `Z₂`).
- **No cascade + a non-abelian-simple (`A_k`-on-subsets) factor → the wall**
  (Tier 2). Quasipolynomial (Babai); polynomial is open, ≡ GI ∈ P.

**Tiers:** 0 = disjoint/decomposable; 1 = 1-WL-blind but cascade resolves;
2 = the wall.

The cost of the canonizer (modelled as lex-leader descent of a stabilizer chain)
factors as `(#levels) × (transversal size) × (work per level)`, pinned by three
theorems:

- **T-A** — polynomial-size representation. *Free* (computational group theory:
  store generators, not elements).
- **T-B** — polynomially many levels. *Free* (a base of a subgroup of `S_n` has
  `≤ n` points).
- **T-C** — polynomial work per level. **The single open hurdle**: discover each
  stabilizer-chain level's transversal — the new coset representatives — when
  refinement does not expose it. Polynomial on the easy side (cascade / abelian);
  the open problem otherwise.

---

## 9. What the model does NOT capture (gaps)

- **Partition-only.** The model speaks of `samePartition` — *which* cells form,
  never *which cell is "less"*. `warm_6_2` proves "same partition", not "order
  mirrored". The order-label half of invariant 6.2 is unmodelled.
- **Single-pair guesses.** `applyGuess` models a 2-element target cell (one
  genuine decision). A `k > 2` target cell is not directly modelled.
- **No transitive closure.** Relegated (§4) — correct for 6.2, but the model
  cannot state anything about TC-derived relations.
- **No automorphism action.** There is no σ-action / equivariance, so the
  "branch on one representative per orbit" reduction is unjustified in-model.
- **No linear / `Z₂` structure.** The residual `Z^d` label-optimisation that the
  linear oracle would solve is unmodelled.
- **The `refineStep` axiom** is faithful only insofar as `refineStep_iff`
  captures 1-WL; the colour encoding is abstracted away (deliberately, §6).

---

## 10. Future work (in proving terms)

1. **Spine theorem — PROVED (§15).** `spine_branch_independent` /
   `SpineChain.branch_independent`. Existential individualisation
   (`IndivStep`) was the modelling choice taken; concrete-witness
   construction is a separate follow-on (polynomial, not blocking). The
   all-`less` corollary and the leaf/`Z₂^d` reduction are out of scope
   for the first cut; see the §15 Lean docstring for what's deferred.
2. **The linear oracle** — the bound-reduction lever for the abelian/CFI case.
   Needs a model layer: order labels + the `Z₂`-affine structure of forced
   relations. `warmRefine_agree_off` is the reduction that makes this well-posed
   (it hands the oracle one fixed partition and a clean `Z₂^d` to optimise over).
3. **Tier-2 exclusion** — the near-theorem: if `Aut(G)` *is* a Johnson group then
   `G`'s edges are `S_k`-invariant ⇒ `G` is an association-scheme graph ⇒
   refinement computes the scheme ⇒ individualization cascades. I.e. *you cannot
   hide a Johnson group as the full `Aut(G)`*. Pure graph theory (association
   schemes); rules the wall *out* rather than solving it. Caveat: the general
   "all automorphisms are revealed in the first pass" is **circular** (= GI ∈ P) —
   only the full-`Aut` version is a real theorem. Written up rigorously in
   `docs/chain-descent-hidden-johnson.md`: Pieces A and B (a visible Johnson's
   edges are forced to be an overlap-scheme) **proved**, Piece C (that scheme
   then cascades) **scoped** — and that doc delimits what it does *not* cover:
   only the *visible* Johnson is ruled out, not the encoded one.
4. **Automorphism-equivariance of `warmRefine`** — refinement commutes with a
   graph automorphism. The rigorous justification for "branch one per orbit".
5. **The Tier-1 polynomial proof** — T-C for the cascade class; would pin the
   node budget `B(n)`.
6. **Propagation-closure as a matroid** — open working investigation written up
   in [`../docs/Archive/ChainDescent/chain-descent-matroid.md`](../docs/Archive/ChainDescent/chain-descent-matroid.md).
   Models warm-refinement's forced-relation structure as a closure operator on
   pair-guesses. The next concrete Lean step (item 2 of that doc's §9) is
   proving the matroid **exchange axiom** for this closure — the load-bearing
   claim that decides whether the matroid framing is viable. M0–M2
   (monotone / extensive / idempotent) are essentially free from existing
   lemmas; M3 needs a chain-reversal induction. Three possible outcomes
   (proved / proved-with-extra-hypothesis / refuted-with-witness), all
   informative.

---

## 11. The descent spine — cross-branch sharing

`warm_6_2` / `warmRefine_agree_off` share the *partition* across guess
directions. Pushing that through the descent recursion gives the central
IR-resistant work-sharing result.

**Setup.** Chain descent is a binary tree: each node warm-refines, picks a
target cell, branches on its two orderings, recurses. Write `D_k` for the set
of vertices individualized down to level `k`, and `π_k` / `T_k` for the
partition and target cell at level `k`.

**Spine theorem (informal — Lean status below).** *If target-cell selection is
partition-invariant, then `D_k`, `π_k`, `T_k` are identical for every branch at
level `k`.* The tree of **partitions** is therefore not a tree but a **path** —
the *spine* — of length `m ≤ n`; the `2^m`-way branching is entirely in the
order labels overlaid on it.

*Proof.* Induction on `k`. Level 0: one root, shared trivially. Level `k→k+1`:
by IH all branches share `π_k`, hence (partition-invariant selection)
`T_k = `target`(π_k)`, hence `D_{k+1} = D_k ∪ T_k`. Any two branch matrices
agree off `D_{k+1}` — every guess writes only inside the decision set — and the
two level-`k+1` start colourings are `samePartition`-equal (IH, plus
individualizing the same cell `T_k`). `warmRefine_agree_off'` then gives
`π_{k+1}` shared. ∎

Every *step* of this induction is a proved Lean lemma: `warmRefine_agree_off'`
(the partition composes across levels — note it accepts `samePartition` start
colourings, which is what the IH supplies) and `target_direction_blind` /
`target_agree_off` (the target composes).

**Status — `spine_branch_independent` is proved (§15 of `ChainDescent.lean`).**
The recursion stringing the per-level lemmas through the descent is now in Lean.
Modelling pieces:

* `IndivStep χ T` — an *existential* witness of one descent-step's
  individualisation: a colouring `χ'` that singletons `T` and refines `χ`
  outside `T`. Two axioms (`singletons_T`, `refines_off_T`); not committed
  to a concrete encoding.
* `DescentTrace adj P₀ χι₀ sel k D P χι` — an inductive predicate (Type)
  recording "the level-`k` state `(D, P, χι)` is reachable from
  `(P₀, χι₀)` by `k` descent steps." `succ` carries an `IndivStep` on the
  *refined* partition `warmRefine adj P χι` (matching the descent's
  operational order: refine → pick target → individualise) and a fresh
  matrix `P'` agreeing with `P₀` off the enlarged `D ∪ sel π_k`.
* `SpineChain ... k` — a bundle of trace + derived `(D, P, χι)` fields,
  plus a `.partition` accessor (= `warmRefine adj P χι`).

Headline result: `spine_branch_independent` (trace form) /
`SpineChain.branch_independent` (chain form). Statement: two traces /
chains at the same level `k` agree on `D` (literal equality) and on
their level-`k` partition (`samePartition`). The proof is induction on
`k` chaining `warmRefine_agree_off'`, `IndivStep.samePartition_het`, and
trace's `singletons` / `P_agrees` invariants. Axiom-clean against the
file's existing axiom basis (`refineStep` + `refineStep_iff` + the four
standard).

**Constructive existence (added 2026-05-25).** The first wave of
follow-ons is now in:

* `IndivStep.default` — concrete witness with base-`n` encoding (parity
  bit for T-membership; `χ v * n + v.val` for the within-T tag). Both
  axioms discharged by `omega` + Nat.div one-liners. Used to give the
  `instance : Nonempty (IndivStep χ T)`.
* `defaultColouring` / `defaultD` / `defaultTrace` — recursive concrete
  construction of a level-`k` trace using `IndivStep.default` and
  `P = P₀` throughout (the simplest matrix that agrees with `P₀` off
  every `D`). Proves `DescentTrace` is non-vacuous at every level.
* `defaultSpineChain` — the bundled chain.
* **`SpineChain.eq_default`** — the reference corollary: every chain at
  level `k` has the same `D` and the same partition as
  `defaultSpineChain`. There is a *canonical* level-`k` partition,
  computable by one deterministic descent.

The "all-`less` corollary" mentioned in earlier notes is subsumed: with
the existential `IndivStep` model and arbitrary `P'` agreeing off `D`,
the natural reference is "no guesses written, default
individualisation." An all-`less` matrix is just a different choice
inside the same equivalence class — same partition by spine.

**Leaf characterisation + order-label space (added 2026-05-25, §15.1
and §15.2).** Phases A and B of the deferred follow-on:

§15.1 — leaf characterisation:
* `Discrete χ` — colouring is injective (every cell singleton);
  `samePartition`-invariant; warm refinement preserves it.
* `SpineChain.IsLeaf chain` — chain's partition is discrete;
  spine-invariant via `SpineChain.isLeaf_iff_default`.
* `TargetsNonsingletonCell sel` and `NonemptyOnNonDiscrete sel` —
  reasonable termination hypotheses on the selector.
* **`defaultSpineChain_reaches_leaf`** — under these hypotheses, the
  default descent reaches a leaf within `n` levels. Proof: by
  contradiction, with `|defaultD i|` strictly growing on every non-leaf
  step (`defaultD_grows_if_not_leaf`); at `i = n` the set must be
  `Finset.univ`, hence the chain is a leaf (`defaultD_univ_isLeaf`).

§15.2 — order-label space:
* `DirAssignment P₀ D` — an antisymmetric `PMatrix` agreeing with `P₀`
  outside `D × D`. The *space of guess-direction choices*.
* `DirAssignment.default` — when `P₀` is antisymmetric, `P₀` itself is
  a trivial DirAssignment; ensures non-emptiness.
* **`DirAssignment.samePartition_pair`** — any two DirAssignments over
  the same `(P₀, D)`, refined against a `D`-singletoning colouring,
  induce the same partition.
* **`DirAssignment.samePartition_chain`** — any DirAssignment over a
  chain's decision set, refined against the chain's colouring, induces
  the chain's partition. *The order-label residual is exactly the
  choice of DirAssignment; the partition is fixed.*

**Z₂ flip action (added 2026-05-25, §15.2.1).** Phase C of the
deferred follow-on:

* `DirAssignment.flipPair σ a b` — flip a single pair's direction;
  antisymmetry and `agrees_off` preserved. The **Z₂ generator** acting
  on direction choices.
* **`flipPair_idempotent`** — flip twice = identity.
* **`flipPair_partition_invariant`** — flipping preserves the spine
  partition (corollary of `samePartition_pair`).
* **`flipPair_comm`** — flips on disjoint pairs commute (the action is
  abelian on disjoint generators).

The full `Z₂^d` quotient — the orbit structure of `DirAssignment` under
the full flip group — is *not* formalised; it would need
`Finset`-indexed flip-products and quotient construction. The four
results above are the load-bearing pieces (single flip + group axioms
for generators).

**Graph automorphisms / labelled adjacency (added 2026-05-25, §15.3).**
Phase D foundations:

* `IsAut π adj` — predicate: `Fin n`-permutation `π` preserves adjacency
  edge-by-edge.
* `IsAut.refl` / `IsAut.trans` / `IsAut.symm` — the group structure.
* `labelledAdj π adj` — adjacency relabelled by `π`
  (`[i][j] = adj.adj (π⁻¹ i) (π⁻¹ j)`).
* **`labelledAdj_eq_of_isAut`** and **`isAut_of_labelledAdj_eq`** —
  `IsAut π adj ↔ labelledAdj π adj = adj.adj`. The two characterisations
  match; this is what the descent's verifier uses to reject
  non-automorphism candidate twists.

These are axiom-cleaner than the spine work — only depend on
`Quot.sound` (no `refineStep` axioms), since the theory lives entirely
at the labelled-permutation level, not on warm refinement.

**Rank bijection + leaf canonical adjacency (added 2026-05-25, §15.4
and §15.5).** Phase D' parts 1 and 2:

§15.4 — Rank bijection:
* `Colouring.vertexRankNat χ v` — count of `u` with `χ u < χ v`
  (no `Discrete` required for the definition).
* `Colouring.vertexRankNat_lt_n` — `v` itself is excluded, so the count
  is `< n`.
* `Colouring.vertexRank χ v : Fin n` — the wrapped rank.
* `Colouring.vertexRank_strict_mono` — `χ v < χ w → vertexRank v < vertexRank w`.
* `Colouring.vertexRank_injective` — on `Discrete χ`, injective via
  strict-mono in both directions.
* `Colouring.vertexRank_bijective` — pigeonhole on `Fin n → Fin n`.
* **`Colouring.rankPerm χ h : Equiv.Perm (Fin n)`** — the rank
  bijection (vertex ↦ its colour-rank). Via `Equiv.ofBijective`.

§15.5 — Leaf canonical adjacency:
* **`SpineChain.canonAdj chain isLeaf σ`** — given a chain reaching a
  leaf and a `DirAssignment σ` over `chain.D`, the canonical labelled
  adjacency at this leaf: `labelledAdj (rankPerm (warmRefine adj σ.σ
  chain.χι) _) adj`. The `Discrete` proof is discharged via
  `samePartition_chain` + `isLeaf`.

Different `DirAssignment`s give different `canonAdj` matrices in
general — the lex-min over `DirAssignment`s (Phase D'4, deferred) is
the canonical form.

**Matrix lex order + Fintype + canonForm + linear-oracle interface
(added 2026-05-25, §15.6–§15.8).** Phase D' parts 3, 4, 5:

§15.6 — Lex order on matrices:
* `matrixLT M₁ M₂` — row-major lex strict less-than: a first cell
  `(i, j)` where the matrices disagree, with `M₁ i j < M₂ i j`.
* **`matrixLT_irrefl`** — no matrix is `<` itself.
* **`matrixLT_asymm`** — `M₁ < M₂ → ¬ M₂ < M₁` (asymmetry). The full
  strict order — transitivity, decidable totality — and the
  derived `LinearOrder` instance needed to invoke `Finset.min'` is the
  remaining piece (see "canonForm placeholder" note below).

§15.7 — Fintype + `canonForm`:
* `instance PMatrix.fintype` — `Fin n → Fin n → POE` is finite (added
  `Fintype POE` instance + `Mathlib.Data.Fintype.Pi` import).
* `instance DirAssignment.fintype` — `Fintype (DirAssignment P₀ D)` via
  `Fintype.ofInjective` on the σ-field (`noncomputable` since
  `Fintype.ofInjective` is).
* **`canonForm chain isLeaf`** (placeholder) — currently picks *any*
  `DirAssignment` via `Classical.choice` (requires a `Nonempty`
  hypothesis). The intended lex-min via `Finset.min'` requires a
  `LinearOrder` instance on `Fin n → Fin n → Nat`, which is the
  remaining work — `matrixLT` is defined and the asymmetry is proved,
  but transitivity + totality + decidability for the `LinearOrder`
  instance is left for a follow-on.

§15.8 — Linear oracle interface:
* **`LinearOracleSpec adj P₀ χι₀ sel`** — function type from
  `(chain : SpineChain ...)` + `chain.IsLeaf` + `DirAssignment` to
  `Option { π : Equiv.Perm (Fin n) // IsAut π adj }`. The output bundles
  the verified automorphism with its `IsAut` proof.
* **`some_isAut`** — when the oracle returns `some result`, the
  permutation is an automorphism. Automatic from the bundled subtype;
  recorded for clarity.
* **`LeafTwistSpec oracle`** — the meaningful validity predicate: when
  the oracle returns `some result`, the returned `π` *relates* the
  branch `σ`'s canonical adjacency to *some other* `DirAssignment σ'`'s
  via `relabelMatrix`. This is what justifies pruning the σ' branch.
  Existence of σ' is existential; the oracle's actual implementation
  (the twist-discovery algorithm) lives in the C# side per
  `docs/chain-descent-calculator.md` §6.
* `relabelMatrix` — generic matrix relabelling helper for the
  `LeafTwistSpec` statement (parallels `labelledAdj` but operates on
  bare `Fin n → Fin n → Nat` rather than `AdjMatrix`).

**Real `canonForm` via Pi.Lex (added 2026-05-25, §15.7 + §15.8 update).**
Phase D'' part 1:

* `MatrixLex n := Lex (Fin n → Lex (Fin n → Nat))` — Lex-wrapped matrix
  type; gets `LinearOrder` automatically from `Pi.Lex.linearOrder`
  applied twice (no manual proof of `matrixLT` transitivity/totality
  needed).
* `toMatrixLex` / `ofMatrixLex` — identity coercions (Lex is a type
  synonym).
* `canonFormImages chain isLeaf` — extracted helper Finset of Lex'd
  `canonAdj` values; used by both the def and the spec proofs to avoid
  `let`-in-body unfolding issues.
* `canonFormImages_nonempty` — nonempty under `[Nonempty
  (DirAssignment P₀ chain.D)]`.
* **`canonForm`** (real) — `ofMatrixLex` of `(canonFormImages
  ...).min'`. Replaces the earlier placeholder. The `Nonempty` instance
  is satisfied by `DirAssignment.default` when `P₀` is antisymmetric.
* **`canonForm_mem_image`** — `canonForm = canonAdj σ` for some `σ`.
* **`canonForm_le_canonAdj`** — `toMatrixLex (canonForm) ≤ toMatrixLex
  (canonAdj σ)` for every `σ` (the lex-min spec, stated via the
  `MatrixLex` order).

Imports added: `Mathlib.Order.PiLex` (for `Pi.Lex.linearOrder`) and
`Mathlib.Data.Finset.Max` (for `Finset.min'` / `min'_mem` /
`min'_le`).

**Remaining genuine work (Phase D''' and beyond):**
* Prove specific `LinearOracleSpec` instances satisfy `LeafTwistSpec`.
  This requires modelling specific linear-oracle implementations —
  out of scope until at least the cascade oracle's Lean model is in
  place. The spec is precise enough to use as a *correctness
  contract* for any concrete oracle.
* Tie everything back: prove that a descent guided by a valid
  `LinearOracleSpec` produces the same `canonForm` as a brute-force
  search over all `DirAssignment`s. This is the descent's
  high-level correctness theorem.
* Connect `flipPair` (§15.2.1) to the descent's branch-pruning: each
  flip generates a binary decision, and the `Z₂^d` orbit of
  `canonForm` under the flip group describes the residual
  exponential the linear oracle defuses.

**Consequences.**

- *The spine is the all-`less` descent.* Any direction choice yields the same
  `π_k` (`warmRefine_agree_off`), so running the descent with every guess set to
  `less` — one **non-branching**, polynomial pass — computes the whole spine
  `D_0 ⊂ … ⊂ D_m`, `π_0,…,π_m`, `T_0,…,T_m`.
- *Refinement work is `O(n)` refinements, not `O(2^n)`.* All `2^m` branches
  reuse the one spine; refinement is never redone per node.
- *Cascade is direction-blind.* "Refinement resolves cell `C`" is a partition
  property, so a sub-decision forced (cascaded) in the `a<b` branch is forced
  identically in `b<a`. The set of genuine (non-forced) decisions is a function
  of `D` alone — a decision is never free in one branch and forced in its
  mirror.
- *Algorithm restructuring.* The descent splits into **Phase 1** — compute the
  spine (poly, no branching) — and **Phase 2** — optimise the order labels over
  the fixed spine. Phase 2 is the `2^m` residual and the linear oracle's domain.

**What the spine does *not* do.** It shares the internal/refinement work, not
the **leaves**. Each leaf is a distinct linear order on `D_m`; for a rigid
graph (multipede) all `2^m` leaves give distinct matrices and must still be
evaluated. The spine converts "exponentially many refinements" into
"polynomially many refinements + exponentially many leaf evaluations", and
hands the leaf/label optimisation a *single fixed partition backdrop*. Breaking
that residual is the linear oracle (Tier-1 abelian) or the open wall (Tier-2) —
the spine isolates the exponential, it does not remove it.

**Implementation findings (for the C#).**

1. *Target selection must be partition-invariant.* Across the `a<b` / `b<a`
   branches the refined colour **values** diverge — already at round 1, a
   non-`D` vertex's signature is lex-ranked among *all* vertices, including the
   `D`-vertices whose colours differ by direction. A "lowest raw colour id"
   target rule can therefore pick *different cells* in the two branches even
   though the partition is identical, silently breaking the sharing. Selection
   must read partition structure (cell sizes, signature multisets, …), not raw
   ids. This is *not* a correctness bug in the current non-sharing descent — it
   is a precondition for adding the sharing optimisation.
2. *Memoise by the decision set `D`, not by the colouring.* The partition is a
   function of `D` (`warmRefine_agree_off`); colourings diverge. The reuse key
   for cross-branch sharing is the *set of individualized vertices*. Better
   still — by the first consequence above — skip memoisation and compute the
   spine directly as the all-`less` pass.
