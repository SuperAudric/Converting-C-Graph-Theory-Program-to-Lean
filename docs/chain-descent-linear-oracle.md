# Chain descent — the linear oracle (spec + design)

The **linear oracle** is the second `ITransversalOracle` implementation:
the component that resolves **genuine-decision cells** (false symmetry)
for the **abelian** case, by discovering a verified automorphism
("twist") from a single branch's propagation pattern. The cascade
oracle handles true-symmetry cells; the linear oracle handles the
abelian sub-case of false-symmetry cells; the rest flags.

This doc is the linear oracle's consolidated spec. Most of the
surrounding machinery is already fixed (a Lean-backed interface, a
provenance state, a proved partition backdrop). The **one genuinely
unspecified piece** — the *candidate-twist construction predicate*,
turning a propagation pattern into a vertex permutation — is the
subject of §4, and the reason this doc exists.

For the algorithm that calls the oracle:
[`chain-descent-strategy.md`](./chain-descent-strategy.md). For the
oracle / cost model framing:
[`chain-descent-calculator.md`](./chain-descent-calculator.md) §6
(the prose spec this doc makes precise). For where the oracle is now
load-bearing:
[`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
§10.4 and
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
§5.

> **Constraint status (read first).** The constraints below come from
> several docs of varying currency. This doc marks each as **firm**
> (Lean-backed or proved — do not change without re-proving),
> **reshapeable** (a design choice that can be revised), or
> **historical** (recorded but not binding — notably the matroid
> framing, which is closed). See §9.

> **Lean status (2026-05-30) — the construction gap is resolved at the leaf
> level; read §8.2 then this doc.** The "one genuinely unspecified piece" framing
> below (the candidate-twist *construction*, §4) is the **C# / online / decision-node**
> view. The Lean contract operates at **leaves**, and there the construction is
> **forced, not searched**: `canonAdj σ = labelledAdj (rankPerm π_σ) adj`, so the two
> branches' leaves differ by exactly the rank rebasing `candidateTwist`, which always
> realises the flip — soundness is fully discharged (`canonicalTwistOracle` satisfies
> `LeafTwistSpec`), and only the §4.5 edge-check is runtime content.
> [`ChainDescent/LinearOracle.lean`](../GraphCanonizationProofs/ChainDescent/LinearOracle.lean)
> (§L.1–§L.3), detail in §8.2 below. So §4's prose is the *design intent* (and the
> decision-node behaviour the C# implements); the Lean *soundness* no longer depends on
> resolving §4.2's matching — it is determined. What remains open is **completeness**
> (does the forced candidate verify exactly when the decision is a real abelian
> symmetry) and the `canonForm` lex-min tie — see §8.2.

---

## 1. Purpose and scope

### 1.1 What the linear oracle does

A **genuine decision** is a target cell that 1-WL cannot split but the
graph treats as ≥ 2 orbits. The simplest case: a cell `{e, f}` where
individualizing `e` (commit `e < f`) and individualizing `f` (commit
`f < e`) are the two directions of one ordering decision.

The linear oracle's mechanism ([calculator §6](./chain-descent-calculator.md)):

1. **Explore** one branch (individualize a representative, commit
   `e < f`), and **warm-refine**; refinement (not transitive closure)
   propagates the decision by splitting cells.
2. **Delineate** the *coupled component* — the cells that split as a
   consequence, read from the **refinement footprint** (parent↔child
   partition diff, §3).
3. **Construct** a candidate twist `t : V → V` by matching the explored
   branch's refined sub-cells to the mirror branch's by canonical id
   (§4 — the open piece, sound via verification).
4. **Verify** `t ∈ Aut(G)` edge-by-edge.
5. **Prune** branch-`f` (and every decision coupled to `t`) without
   exploring it.

The discovered twists generate the residual group; orbit pruning with
them turns each coupled decision into a `k = 1` step, collapsing the
descent to a single path. For CFI, the `2^d` IR tree becomes a path of
length `d`, each node `O(n²)`.

### 1.2 The boundary (what it does *not* do)

The oracle works **iff one branch's pattern determines a unique
candidate twist**:

- **Unique candidate** (`Z_2`: a single involution swaps `e, f` within
  the coupled component) → verify and consume. CFI's `Z_2^d` is `d`
  such decisions.
- **No unique candidate** (a large non-abelian action — `A_k`, hidden
  Johnson) → one branch's pattern can't single one out; the budget
  flags.

The boundary *is* the abelian/non-abelian split, the same line as
Babai's split-or-Johnson obstruction. §4.3 makes the uniqueness test
precise.

### 1.3 What this doc fixes vs. consolidates

- **Consolidates** (already specified elsewhere): the contract (§2),
  the required state (§3, now the refinement footprint), the partition
  backdrop (the descent spine), the lex-min objective.
- **Fixes** (the gap): the candidate-twist construction predicate
  (§4) — input format, the canonical-id matching construction, the
  uniqueness test, the verification protocol, the polynomial bound.

---

## 2. The firm contract (Lean-backed)

The interface and its obligations are machine-checked in
[`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
§15.8. **Firm** — any implementation must satisfy these; changing them
means re-proving the descent's correctness contract.

### 2.1 Input — `DirAssignment`

```
structure DirAssignment (P₀ : PMatrix n) (D : Finset (Fin n)) where
  σ : PMatrix n
  antisym : PMatrix.Antisymmetric σ
  agrees_off : ∀ x y, (x ∉ D ∨ y ∉ D) → σ x y = P₀ x y
```

An antisymmetric order assignment agreeing with the base matrix `P₀`
everywhere outside the decision set `D × D`. A branch *is* a choice of
order labels on `D`, with everything off `D` fixed. The decision set
`D` is the chain's accumulated genuine-decision vertices.

### 2.2 Interface — `LinearOracleSpec`

```
def LinearOracleSpec adj P₀ χι₀ sel : Type :=
  ∀ {k} (chain : SpineChain adj P₀ χι₀ sel k), chain.IsLeaf →
    DirAssignment P₀ chain.D →
    Option { π : Equiv.Perm (Fin n) // IsAut π adj }
```

Given a spine chain reaching a leaf and the current branch's
`DirAssignment`, return `none` (no twist) or `some` automorphism `π`
**bundled with its `IsAut` proof**.

### 2.3 Obligations

- **`some_isAut`** — a returned `π` is a genuine automorphism.
  Automatic from the bundled subtype.
- **`LeafTwistSpec`** — the meaningful validity predicate: when the
  oracle returns `some result`, the returned `π` relabels this
  branch's canonical adjacency to *some other* `DirAssignment σ'`'s:

  ```
  relabelMatrix result.val (chain.canonAdj σ) = chain.canonAdj σ'
  ```

  This is what justifies pruning σ' — the two branches give the same
  canonical form modulo a known automorphism.

**What's missing in Lean.** No concrete `LinearOracleSpec` instance is
yet proved to satisfy `LeafTwistSpec`. The discovery algorithm (§4) is
existential in the spec. This doc's §4 is what a concrete instance
would implement; proving it satisfies `LeafTwistSpec` is the Lean
deliverable.

### 2.4 The objective — lex-min over `DirAssignment`s

`canonForm` ([ChainDescent.lean](../GraphCanonizationProofs/ChainDescent.lean)
§15.7) is the `Pi.Lex`-min of `canonAdj σ` over all `σ : DirAssignment`.
The linear oracle's job is to reach this min without enumerating all
`2^|D|` assignments — by discovering the symmetry that makes most of
them equivalent.

---

## 3. Required state — the refinement footprint

> **Correction (2026-05-28, from the C# build branch).** An earlier
> version of this section took the coupled component from the
> transitive-closure provenance of [strategy §10](./chain-descent-strategy.md)
> (`DERIVED`/`driver` records). That mechanism is **inert** for the
> linear oracle's target: under relegated TC (the model `warm_6_2` is
> proved in) there is no in-loop closure at all, and in the C# harness
> a within-cell decision on a uniform-type graph gives TC *nothing to
> chain* (cellmates are unordered among themselves; other cells are
> P-incomparable) — measured zero derived entries. The propagation that
> actually carries the cascade is **1-WL refinement**, so the coupled
> component is read from the **refinement footprint**, not from TC.

**What the oracle reads.** The propagation of a decision is the set of
cells that **split as a consequence of individualizing the
representative** — read from the **parent↔child partition diff**:

- compute the partition before the decision (parent) and after
  individualizing the representative + warm-refining (child);
- the **coupled component `K`** is the set of cells that newly split
  between parent and child — exactly the cells the decision propagated
  to;
- the sub-cell structure of `K` in the child partition is the
  direction-dependent data the twist mirrors.

This is the same mechanism the orbit-recovery program uses (refinement,
not TC) — `theorem_1_HOR_cfi_oddDeg` and the Tier-1/Tier-2 cascade are
all `refineStep`/`warmRefine` results. The linear oracle reads the same
footprint those theorems reason about.

**Why no TC provenance.** TC-provenance (`DERIVED`/`driver`, invariant
6.4) is still meaningful where TC genuinely chains — **between-cell
ordering guesses** (e.g. the `2K2`-style case where distinct components
must be ordered). That is *not* the linear oracle's CFI target, which is
**within-cell** parity decisions propagated by refinement. So the
oracle's required state is the refinement footprint; TC provenance is
not on its critical path.

**Reshapeable choices:**
- Whether the footprint is computed by diffing full partitions or by
  tracking which cells changed during the warm-refine rounds.
- Whether it is computed lazily (on oracle call) or recorded as the
  child refinement runs.

---

## 4. The construction predicate (the gap)

This is the unspecified piece ([calculator §9 item 4](./chain-descent-calculator.md):
"turning a propagation pattern into a vertex permutation — the one
genuinely unspecified piece and the main implementation risk").

### 4.1 Input

The harness branches over a target cell's representatives `[r_1, r_2, …]`
by individualizing one below its cellmates (whole-cell branching, not
single-pair — see §0 note below and the build brief §3). For the
explored representative `r_1`:

- **Coupled component `K`** — the cells that split between the parent
  partition and `r_1`'s child partition (the refinement footprint, §3).
- **`r_1`'s child sub-cell structure** — the partition of `K` after
  individualizing `r_1` and warm-refining. By the spine fact
  (`warm_6_2` for a size-2 cell; `warmRefine_agree_off'` for larger
  decision sets), the partition under any other representative `r_j` is
  the same up to the `r_1 ↔ r_j` relabelling — so we do *not* re-explore
  `r_j`; its structure is the mirror of `r_1`'s.

> **§0 note — whole-cell branching, not single pairs.** The substrate
> model of [strategy §9](./chain-descent-strategy.md) is single-pair
> guesses with two directions; the *implementation* individualizes a
> representative below its whole cell. For a **size-2** cell, branching
> on `r_1` vs `r_2` *is* the two directions of one pair — `warm_6_2`
> applies directly and the proof is clean. For **size-`k`** cells the
> clean `warm_6_2` backing does not transfer (branching on `r_i` is `k`
> different individualizations); the general backing is the spine
> (`warmRefine_agree_off'`), which proves partition-sharing but not the
> automorphism property — that is closed operationally by verification
> (§4.5). See §4.3.

### 4.2 The construction (canonical-id sub-cell matching)

> **Correction (2026-05-28).** An earlier version constructed the twist
> from *order labels* on sub-cells (`C_1 < C_2 < … < C_r`). Those order
> labels **do not exist in the harness**: warm refinement is split-only
> and never writes `P`, and TC is inert (§3). The construction instead
> matches sub-cells by their **canonical-id structure** in the refined
> partition, and is **sound via verification (§4.5)**, not via the
> order-label argument.

The candidate twist `t : V → V` carrying `r_1 ↦ r_j`:

1. For each cell `C` in the coupled component `K`, take `r_1`'s child
   sub-cells of `C` and `r_j`'s child sub-cells of `C` (the latter known
   to be the `r_1 ↔ r_j` mirror by the spine fact, not re-explored).
2. Match `r_1`'s sub-cells to `r_j`'s by canonical-id structure
   (same refined-colour signature). Within matched sub-cells, match
   vertices by canonical id.
3. `t` is the resulting vertex map (identity outside `K`). It must be
   **path-fixing** by construction (fix every individualized path
   vertex — see §6) so the existing pruning machinery can consume it.

For this to define a permutation, matched sub-cells must have equal
size; the clean case is when every sub-cell is a **singleton**, giving a
forced matching and `r_1 ↦ r_j` directly.

> **The all-singletons gate is principled, not just convenient
> ([viability plan](./chain-descent-extended-twist-viability.md)).** A
> non-singleton sub-cell is a *cell* — its vertices share one refined
> colour, so they are refinement-indistinguishable, and **there is no
> iso-invariant way to match a specific vertex to a specific image**
> within it. A direct (index-based) match would be *sound* (verification
> still gates it) but would make twist discovery — and hence the
> node-count / flag verdict — depend on the input labelling, breaking
> flag iso-invariance ([strategy §15 gap 2](./chain-descent-strategy.md)).
> So the direct construction is well-defined **only for all-singleton
> footprints**; the principled handling of non-singleton sub-cells is
> *recursion*, not an arbitrary match (§4.4).

**CFI specialization.** In CFI, `K` is a cycle of the base graph's
cycle space; individualizing a parity rep splits each gadget on the
cycle into its two parities; `t` flips all parities on the cycle. Each
parity class is a singleton after the decision propagates, so the
matching is forced. This is the `Z_2` twist — "flip the coupled cycle."

### 4.3 The boundary — uniqueness vs. the wall

The candidate is **unique** when the canonical-id matching in §4.2 is
forced — when every sub-cell of the coupled component is a **singleton**.

- **All singletons** → forced matching → a single candidate `t` →
  **construct, verify, prune**.
- **Some sub-cell has ≥ 2 vertices** → the within-sub-cell matching is
  ambiguous → no single candidate → **fall back / flag** (§4.4).

> **Conjectural, not proven.** That "all sub-cells singleton ⟺
> abelian / non-singleton ⟺ the non-abelian wall" is the
> **Tier-3 / orbit-recovery open content**, not a proved theorem. What
> *is* sound, unconditionally, is the **behaviour**: the singleton case
> yields a unique candidate the verifier can check; the non-singleton
> case has no unique candidate and the descent falls back to
> budget-bounded search (always correct, §6.3). Implement the behaviour;
> do not assert the boundary characterization as established. It is a
> *localized cascade check* whose connection to the abelian/wall split
> is the orbit-recovery conjecture ([orbit-recovery](./chain-descent-orbit-recovery.md)),
> the same line as calculator §6's "size of the per-decision residual
> symmetry."
>
> **Distinct from the above conjecture: the all-singletons gate itself is
> principled, not heuristic.** Independently of whether singleton ⟺
> abelian, the gate is *forced* by iso-invariance — a non-singleton
> sub-cell admits no iso-invariant direct match (§4.2 note,
> [viability plan](./chain-descent-extended-twist-viability.md)). So
> "construct directly only when all-singleton, else recurse" is the
> sound *and* iso-invariant rule regardless of how the abelian/wall
> conjecture resolves.

### 4.4 Non-singleton sub-cells — recursion, not direct matching

When sub-cells are *not* all singletons, the
[viability analysis](./chain-descent-extended-twist-viability.md)
settles what to do — and rules one option out:

- **Direct (index-based) matching is ruled out.** It is sound
  (verification gates it) but **not iso-invariant** (§4.2 note): a
  refinement-indistinguishable sub-cell has no canonical within-cell
  vertex order, so the discovered twist — and the node-count / flag
  verdict — would depend on the labelling. Not the principled route.
- **Recursion is the principled extension.** Individualize within the
  non-singleton sub-cell and re-refine — which is just letting the
  *normal descent* branch on it (iso-invariant, because it branches over
  the whole sub-cell). The footprint refines; the oracle re-fires at the
  deeper level once the sub-cell has cascaded to singletons. **This is
  literally orbit recovery applied to the sub-cell**, and it provably
  terminates on the cascade class: `≤ tw(H)` levels for CFI
  (`theorem_1_HOR_cfi_oddDeg`), depth 1 for rank-≤2 schurian schemes
  (`theorem_2_HOR_concrete_rank_two_J_singleton`).
- **Flag is the bounded-budget fallback.** If the sub-cell has *not*
  cascaded to singletons by the orbit-recovery depth, it is either a
  rigid IR blind spot ([strategy §15 gap 5](./chain-descent-strategy.md))
  or the non-abelian wall — neither yields a harvestable twist, and the
  budget flags. Sound; not a wrong answer.

So the construction's behaviour is **all-singletons → construct directly;
else → fall back to the normal `k`-way branch (recursion), re-firing the
oracle deeper; else (no cascade within the bound) → flag**. The old
"cross-branch triangulation" option is *not* pursued — calculator §6 notes
it "itself branches — exponential," and recursion subsumes its intent
iso-invariantly.

**Decision.** Phase 1: direct construction on all-singleton footprints;
recursion (the existing descent branch) on non-singleton sub-cells; flag
on budget exhaustion. The Lean discharge is scoped to the all-singletons
abelian case (§8.2); recursion's termination is inherited from the
orbit-recovery theorems.

### 4.5 Verification protocol

**Firm** (mandatory for soundness, [calculator §6](./chain-descent-calculator.md) step 3):

Given a constructed candidate `t`, verify `t ∈ Aut(G)` by checking
`adj(t(u), t(v)) = adj(u, v)` for all pairs `(u, v)`. `O(n²)`.

Invariant 6.2 gives the partition symmetry but **not** that `t` is an
automorphism — the edge check is what makes the step sound. A candidate
that fails verification means the pattern suggested a twist that isn't
real; the oracle returns `none` (no twist), and the descent treats the
cell as a genuine `k`-way branch.

### 4.6 Polynomial bound

Per decision:
- Delineate coupled component from the refinement footprint: `O(n²)`
  (diff parent vs child partition).
- Construct candidate via canonical-id sub-cell matching: `O(n²)` (one
  pass over the component's cells).
- Uniqueness test: `O(n²)` (check sub-cell sizes).
- Verify: `O(n²)`.

Total `O(n²)` per decision, `≤ n` decisions → `O(n³)` per descent path,
matching calculator §6's "each node `O(n²)`" with the path factor.

---

## 5. Worked example — CFI over a cycle

Take `G = CFI(C_m)` (the cycle `C_m` as base). `Aut(G) = Z_2^{β} ⋊ Aut(C_m)`
with `β = 1` (a cycle has cycle rank 1).

1. After refinement, the gadgets are cells; 1-WL cannot fix the global
   parity (the single `Z_2` gauge).
2. The target cell is a gadget's parity-ambiguous pair `{e, f}` (the
   two parity representatives). Decision: commit `e < f`.
3. Propagate via warm refinement. The parity choice splits the adjacent
   gadget's cell, which splits the next, around the whole cycle —
   the refinement footprint.
4. Coupled component `K` = all gadgets on the cycle (the cells that
   split between parent and child). Each splits into its two parity
   classes; each class is a singleton (one parity rep per gadget after
   propagation).
5. Uniqueness test: all sub-cells singletons → unique candidate.
6. Construct `t` = flip every gadget's parity on the cycle. Verify
   edge-by-edge: `t` preserves all CFI adjacencies (parity flip is the
   defining gauge symmetry). ✓
7. `t` is harvested; branch-`f` pruned. The `2^1` decision collapses to
   one path.

For `CFI(H)` with `β > 1`, there are `β` independent decisions, each
with its own coupled cycle; the `β` twists generate `Z_2^β`. Each is
discovered the same way, in sequence.

---

## 6. Interface and online behavior

### 6.1 The seam

**Reshapeable.** The linear oracle is a second `ITransversalOracle`
([ITransversalOracle.cs](../GraphCanonizationProject/ITransversalOracle.cs)),
or a layer wired alongside the cascade oracle. Its `Classify` returns a
short representative list (one per certified orbit) instead of the whole
cell.

But note the linear oracle is **online** — it can't certify orbits
*before* branching, because the symmetry it needs is the one refinement
missed. So its integration differs from the cascade oracle's a-priori
`Classify`:

- The cascade oracle (current) returns representatives *before* the
  harness branches.
- The linear oracle must *explore one branch, read the pattern, then
  decide*. This is a different control flow — the oracle and the search
  are one process.

**Design implication.** Either (a) the `ITransversalOracle` interface
extends to permit a "explore-then-classify" mode, or (b) the linear
oracle lives in the harness's branch loop rather than behind the
pre-branch `Classify` seam. Option (b) matches calculator §6's "this is
the oracle, not a pre-pass." Recommended: the harness calls the linear
oracle *after* exploring the first branch of a genuine decision, before
exploring the rest.

### 6.2 The explore-read-verify-prune loop

```
on target cell [r_1, r_2, …] at a node:
    explore r_1 (individualize below cellmates, warm-refine → child)
    K        := refinement_footprint(parent, child)   // cells that split
    if not all_subcells_singleton(K):                 // uniqueness test
        fall through to k-way branch                  // sound; may flag later
    for each unexplored r_j:
        t    := construct_twist(K, r_1, r_j)           // canonical-id match
        if t is path-fixing and verify_automorphism(t, adj):  // O(n²)
            harvest t into PermutationGroup            // CoveredByPathFixingAut
    // existing a-posteriori pruning now skips the covered r_j
```

The harvested `t` folds into the same `PermutationGroup` chain the
cascade oracle's a-posteriori pruning already consumes — so downstream
the two oracles share the residual-group machinery.

### 6.3 Failure → graceful degradation

Per the §7 correction in
[`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md):
if the linear oracle returns `none` (no unique twist, or verification
fails), the harness treats the cell as a genuine `k`-way branch and
proceeds as budget-bounded IR search. The budget catches a stacked
exponential as a flag. So a missing twist is never a wrong answer — only
a slower (or flagged) run.

---

## 7. Soundness

The pruning is sound because of `LeafTwistSpec` (§2.3): a verified `t`
witnesses that branch-`e` and branch-`f` reach the same canonical form
modulo `t`. Concretely:

1. `t ∈ Aut(G)` (verified, §4.5).
2. `t` is path-fixing and carries the explored representative `r_1` to
   the unexplored `r_j` (the canonical-id matching, §4.2).
3. So `canonAdj(r_1-branch)` and `canonAdj(r_j-branch)` are related by
   `relabelMatrix t` — exactly `LeafTwistSpec`.
4. Hence the lex-min over `{r_1-branch, r_j-branch}` is achieved by
   either; pruning `r_j` cannot miss the minimum.

The soundness rests *only* on the edge-by-edge verification (1) — not
on `warm_6_2`/the spine, which give the *candidate* but not its
correctness. This is why verification is mandatory and non-negotiable,
and why the construction (§4.2) may be heuristic.

---

## 8. Implementation plan

### 8.1 C# (empirical first)

1. **Refinement-footprint extraction** (replaces the abandoned
   TC-provenance plumbing, §3). Diff the parent partition against the
   child partition (after individualizing the representative + warm
   refining) to get the coupled component — the cells that split.
   ~150 lines.
2. **Twist construction + uniqueness test.** §4.2 (canonical-id
   sub-cell matching) + §4.3 (all-singleton check). ~200 lines.
3. **Verification.** `O(n²)` edge check — reuse
   [`IsAutomorphism`](../GraphCanonizationProject/ChainDescent.cs#L246).
   ~20 lines of glue.
4. **Harness integration.** The explore-read-verify-prune loop (§6.2),
   harness-loop placement (option b). Harvest into `Automorphisms`
   before the branch loop reaches unexplored reps, so the existing
   [`CoveredByPathFixingAut`](../GraphCanonizationProject/ChainDescent.cs#L181)
   prunes them. ~200 lines.

**Status — built and measured (2026-05-28).** Steps 1–4 are implemented
(`RefinementFootprint`, `TwistConstruction`, `HarvestTwists` in
`ChainDescent`, default-on `EnableLinearOracle`); `_seen` now keys on a
64-bit hash so memory is `O(leaves·n)`. Validated correctness-preserving
through CFI(K7), incl. exhaustive size-5/6 canonical-uniqueness.

The construction goal is **met**: every all-singleton decision yields a
twist passing `IsAutomorphism` (the empirical `LeafTwistSpec`, §2.3).
Leaf count drops off→on: K4 16→12, K6 378→76, **K7 6531→941** (~7× at
β≥10). **But the `O(β)` path-collapse is not reached** — and the
attribution is decisive: on CFI(K7), **100 % of the residual branching
(555/555 nodes, all 940 extra reps) sits at non-singleton footprints**,
where the oracle can't construct a twist; at all-singleton footprints it
collapses the node completely (0 branching, 941 twists). **The linear
oracle is *starved*, not weak.** The leaf growth is decisions whose
coupled component still carries unresolved residual symmetry — for CFI
always resolvable (`theorem_1_HOR_cfi`, no wall), but the descent resolves
it *a-posteriori* (branching) rather than *a-priori* (one rep per orbit).
So the binding constraint is the **a-priori cascade oracle** (§5/§9 of
[calculator](./chain-descent-calculator.md)), which would feed clean
footprints to the now-working linear oracle. See build brief §M6 results.
Specified in [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md)
as this oracle's harvest core wrapped in a bounded-depth recursion.

### 8.2 Lean (contract discharge)

1. **Model the construction** as a concrete `LinearOracleSpec` instance
   for the abelian case. ~500 lines. **DONE 2026-05-30 (B2.1)** —
   `ChainDescent/LinearOracle.lean`: `twistOracle`, a concrete
   `LinearOracleSpec` instance parameterised by an abstracted discovery
   function (the canonical-id matching stays C#-side, exactly as the
   interface abstracts discovery); `RealizesFlip` + `TwistWitness` carry
   the verified-twist data (the §4.5 edge-check lives in `TwistWitness.isAut`).
2. **Prove it satisfies `LeafTwistSpec`** — the deliverable §2.3 names
   as missing. Uses `warm_6_2` (partition symmetry) + the verification
   (automorphism). **DONE 2026-05-30 (B2.1 + B2.2/B2.3).** Two layers:
   - *B2.1* — `twistOracle_leafTwist` discharges `LeafTwistSpec` for any
     verified-twist discovery, with the explicit witness `σ' = flipPair σ`.
   - *B2.2/B2.3* — the construction is **forced, not searched**:
     `canonAdj_rebase` shows relabelling `σ`'s leaf by the **rank rebasing**
     `rankPerm π_flip * (rankPerm π_σ)⁻¹` (`candidateTwist`) *always* realises
     the flip (`candidateTwist_realizesFlip`) — this is the `warm_6_2`/spine →
     `canonAdj` bridge (via `samePartition_chain`, which generalises `warm_6_2`,
     making both branch leaves discrete). So the entire oracle collapses to one
     edge-check: `twistWitness_of_isAut` (verify ⟹ witness) and the concrete
     `canonicalTwistOracle` (compute forced candidate, return iff `IsAut`).
     `candidateTwist_unique` discharges the iso-invariance gate (§15 gap 2) at
     the leaf level — the candidate is a function of iso-invariant rank data.
3. **Tie to `canonForm`** — a descent guided by the verified oracle
   reaches the same lex-min as brute force over `DirAssignment`s. The
   descent's high-level correctness theorem (ChainDescent.md §15.8
   "remaining genuine work"). ~1000 lines. (B2.4 — remaining.)

4. **Completeness / effectiveness (§L.4 — characterised 2026-05-30).** Built in
   `ChainDescent/LinearOracle.lean` §L.4 (axiom-clean): the oracle **fires iff the
   forced candidate is an automorphism** (`canonicalTwistOracle_isSome_iff`),
   equivalently iff a *rank-aligned* automorphism exists
   (`isAut_candidateTwist_iff_aligned`); when it fires the branches are **genuinely
   `Aut(adj)`-equivalent** (`realizableFlip_of_isAut_candidateTwist`); firing is
   **`Z₂`-direction-consistent** (`candidateTwist_flipBack_isAut`). **Key structural
   finding:** completeness is *not* unconditional and is not meant to be — a genuine
   automorphism realising the flip need only agree with the forced (rank-aligned)
   candidate up to `Aut(canonAdj σ)` (a conjugate of `Aut(adj)`), so "branches
   `Aut`-equivalent" implies "forced candidate ∈ Aut" **exactly in the abelian
   (unique-candidate) regime** — the [calculator §6](./chain-descent-calculator.md)
   split-or-Johnson boundary. The remaining open core is the **abelian-sufficiency
   lemma**: forced candidate ∈ Aut(adj) for genuine abelian decisions, via the
   `warm_6_2` rank machinery (the orbit-recovery connection).

**Net (2026-05-30):** soundness of the linear oracle is fully discharged in
Lean — `canonicalTwistOracle` is a concrete, verification-gated `LinearOracleSpec`
satisfying `LeafTwistSpec`, with the twist construction *forced* (rank rebasing),
not heuristic. The construction risk §4.2/§10 flagged ("turning a propagation
pattern into a vertex permutation") dissolves at the leaf level: the permutation
is determined; only the §4.5 edge-check is runtime content. **Completeness is now
characterised (§L.4): the oracle fires ⟺ forced candidate ∈ Aut, complete exactly on
the abelian regime; firing is semantically justified and direction-consistent.**
Remaining: the `canonForm` lex-min tie (B2.4) and the abelian-sufficiency lemma (the
open core of completeness — forced candidate verifies for real abelian decisions).

### 8.3 Order

C# first (empirical validation that twist discovery works on CFI),
then Lean (contract discharge). The C# implementation will surface
whether §4.2's canonical-id matching is the right construction before
the Lean effort is committed.

---

## 9. Constraint status — firm / reshapeable / historical

| Constraint | Status | Note |
|---|---|---|
| `DirAssignment` input type | **Firm** | Lean §15.8; models branch = order labels on `D` |
| `LinearOracleSpec` interface | **Firm** | Lean §15.8; output bundles `IsAut` proof |
| `LeafTwistSpec` validity | **Firm** | Lean §15.8; the pruning-justification contract |
| `some_isAut` soundness | **Firm** | Automatic from subtype |
| `warm_6_2` (invariant 6.2) | **Firm (size-2)** | Proved; the partition-mirror for one pair's two directions. Backs the construction cleanly only for size-2 decision cells (§4.1 §0 note). |
| Descent spine (`warmRefine_agree_off'`) | **Firm** | Proved; partition-sharing over a decision set (size-`k`). Gives the *candidate* for larger cells, not the automorphism property — verification closes that. |
| Edge-by-edge verification (§4.5) | **Firm** | Mandatory for soundness — the unconditional gate. Everything upstream may be heuristic. |
| Coupled component = **refinement footprint** (§3) | **Firm** | Parent↔child partition diff. *Replaces* the TC-provenance model, which is inert for the within-cell cascade (measured 0). |
| TC-provenance (`DERIVED`/`driver`, invariant 6.4) | **Not on critical path** | Meaningful only where TC genuinely chains (between-cell ordering). Inert for the linear oracle's within-cell CFI target. |
| Footprint computation (full-diff vs. round-tracking; lazy vs. eager) | **Reshapeable** | Implementation choice. |
| `ITransversalOracle` integration | **Reshapeable** | Online behavior needs harness-loop placement (§6.1), not the pre-branch `Classify` seam. |
| Canonical-id matching construction (§4.2) | **Reshapeable (heuristic)** | Sound *via verification*, not proven. C# validation on CFI confirms or revises. |
| Non-singleton handling (§4.4) | **Firm (recurse, not index-match)** | Direct index-match is ruled out (not iso-invariant); recurse via the normal descent branch (iso-invariant), flag past the orbit-recovery depth. See [viability plan](./chain-descent-extended-twist-viability.md). |
| "All sub-cells singleton ⟺ abelian / wall" (§4.3) | **Conjectural** | Tier-3 / orbit-recovery open content. The *behaviour* (fall-back on non-singleton) is sound; the boundary characterization is not proven. |
| "Output IS a binary matroid / IS the Tier-2 detector" | **Historical** | [matroid §8.4, §9](./chain-descent-matroid.md). The matroid framework is **closed** — neither closure operator is a matroid. The linear oracle's output is a set of `Z_2` generators; viewing it as a binary matroid is *optional commentary*, not a design requirement. Do not treat as binding. |

**On the matroid framing specifically:** the matroid memo speculated
that the linear oracle's output, viewed as a binary matroid, *would be*
the Tier-2 detector. Since the matroid framework on commit-set closures
is closed, this is recorded as historical motivation only. The linear
oracle's actual deliverable is `Z_2` generators + the uniqueness test
(§4.3); the uniqueness test *is* the abelian/wall boundary, which is
what the matroid framing was reaching for — but it's a localized cascade
check, not a matroid-representability test.

---

## 10. Risks and open questions

1. **Construction correctness (§4.2).** Canonical-id sub-cell matching
   is correct for CFI (worked example), but whether it is the right
   construction for *all* abelian cases is unconfirmed. Verification
   (§4.5) keeps it *sound* regardless — a wrong candidate just fails the
   edge-check. The risk is *effectiveness* (does it construct twists
   that pass verification often enough to collapse the descent?), not
   soundness. C# validation on CFI variants is the first check. **Main
   implementation risk**, as calculator §9 flagged.
2. **Size-`k>2` cells lack clean proof backing.** `warm_6_2` backs
   size-2 cleanly; larger cells lean on the spine
   (`warmRefine_agree_off'`, partition-sharing) plus verification for
   the automorphism property. Sound to *attempt* at any size (verify
   gates); the *Lean* discharge (§8.2) should scope Phase 1 to size-2.
3. **Within-sub-cell matching when sub-cells aren't singletons.** §4.4
   resolves this: no iso-invariant direct match exists, so recurse (the
   normal descent branch) rather than index-match; the
   [viability plan](./chain-descent-extended-twist-viability.md) shows
   recursion is viable on the cascade class and flags otherwise. Whether
   a genuinely abelian decision over non-singleton sub-cells resolves
   below the orbit-recovery depth is the §4.3 conjecture.
4. **Online interface placement (§6.1).** Harness-loop placement
   (option b) is recommended; it must preserve iso-invariance of the
   flag/canonical verdict.
5. **Iso-invariance of twist discovery (undischarged).** Flag
   iso-invariance ([strategy §15 gap 2](./chain-descent-strategy.md))
   requires twist-discovery to be a deterministic function of
   iso-invariant cell ids. `WarmPartition` ids are iso-invariant, so it
   *should* hold by construction — but the obligation is **not
   discharged**; treat it as an open proof obligation, not a given.
6. **Empirical bar is leaf-count, not flag.** Small CFI already
   canonizes under budget (no flag); the signal is the leaf/node-count
   collapse toward a path. See §8.1 and the build brief M6.

---

## 11. Cross-references

- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §6 —
  the prose spec this doc makes precise; §9 item 4 (the construction
  gap).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §10
  (closure-as-guess / TC provenance — *not* on the linear oracle's
  critical path; see §3), §12 (`warm_6_2` + spine — the partition
  backdrop the construction reads), §15 (flag iso-invariance
  obligation).
- [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
  §15.8 — the firm interface (`DirAssignment`, `LinearOracleSpec`,
  `LeafTwistSpec`); §15.7 (`canonForm`).
- [`ChainDescent.md`](../GraphCanonizationProofs/ChainDescent.md)
  §15.8, §11 — the spine / Phase-2 framing; "remaining genuine work"
  (the `LeafTwistSpec` discharge this doc plans).
- [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §5 (sub-claim 1, abelian-stripping — the linear oracle is the
  mechanism); §7 (graceful degradation).
- [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
  §4.5, §10.4 — implicit-discovery depends on the linear oracle as a
  formal object.
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) —
  the uniqueness test (§4.3) is a localized cascade check, tying to the
  orbit-recovery program.
- [`chain-descent-matroid.md`](./chain-descent-matroid.md) §8.4, §9 —
  **closed** framework; the "output is a binary matroid" framing is
  historical (§9 of this doc).
