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
   in [`../docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md).
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

**Still out of scope (Phases C, D for a future round):** the `Z₂` flip
action on DirAssignments and the `Z₂^d` residual quotient (Phase C);
the labelled-adjacency function + lex-min canonical form + linear-oracle
interface (Phase D).

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
