# Chain descent — the a-priori cascade oracle (spec + design)

The **a-priori cascade oracle** is the genuine version of the
component that resolves **true-symmetry cells**: given a target cell,
certify which representatives are in the same automorphism orbit and
return one per orbit **before** the harness branches. The shipped
Phase-1 cascade oracle certifies nothing a-priori; this doc specifies
the version that does.

This doc exists because the linear oracle — built and validated
2026-05-28 ([linear-oracle.md §8.1](./chain-descent-linear-oracle.md)) —
is **starved, not weak**: on CFI(K7), 100% of residual branching sits
at *non-singleton footprints*, where no forced twist exists. The
a-priori cascade oracle is what resolves the residual symmetry at those
footprints, feeding clean (all-singleton) footprints to the linear
oracle. It is the next lever and the path to polynomial CFI.

> **Central design claim.** The a-priori cascade oracle is **not a new
> construction**. It is the linear oracle's already-built
> *construct-footprint-map → verify → harvest-before-branch* core
> ([linear-oracle.md §4](./chain-descent-linear-oracle.md)), wrapped in
> a **bounded-depth recursion** that turns a non-singleton footprint
> into all-singleton ones before harvesting. The per-level construction
> is identical to the linear oracle's; the new content is the recursion,
> and its termination is the orbit-recovery theorems. See §1.4.

> **Constraint status convention** (as in the linear oracle doc):
> **firm** (Lean-backed or proved — do not change without re-proving),
> **reshapeable** (a design choice), **historical** (recorded, not
> binding). See §9.

For the algorithm that calls the oracle:
[`chain-descent-strategy.md`](./chain-descent-strategy.md). For the
prose spec and cost model: [`chain-descent-calculator.md`](./chain-descent-calculator.md)
§5 (cascade oracle) and §9 item 2 (the certification gap this doc
closes). For the shared mechanism:
[`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md).
For the non-singleton recursion:
[`chain-descent-extended-twist-viability.md`](./chain-descent-extended-twist-viability.md).
For the correctness foundation:
[`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md).

---

## 1. Purpose and scope

### 1.1 What the a-priori cascade oracle does

A **true-symmetry cell** is a target cell that 1-WL cannot split and
whose vertices are genuinely interchangeable — the cell is a single
orbit (or splits into a few orbits each of size > 1) under the residual
stabilizer. The cascade oracle's job:

1. **Explore** one representative `r_1` (individualize below its
   cellmates, warm-refine → child partition).
2. **Read the refinement footprint** — the cells that split between the
   parent and child partitions (§3 of the linear oracle doc).
3. If the footprint is **all-singleton**: for each other representative
   `r_j`, **construct** the orbit-map `r_1 ↦ r_j` (canonical-id sub-cell
   matching, identical to the linear oracle's twist construction),
   **verify** it edge-by-edge, and on success **harvest** it before the
   branch loop reaches `r_j`.
4. If the footprint is **non-singleton**: **recurse** — descend one
   level into a non-singleton sub-cell (individualize one of its
   vertices, warm-refine), and re-attempt at the deeper level. The
   footprint refines; by orbit recovery it reaches all-singleton within
   bounded depth (§3, §4.4).
5. Return **one representative per certified orbit**; the harvested
   generators let the existing `CoveredByPathFixingAut` prune the rest.

The effect: the descent explores **one representative per orbit per
level**, not every vertex. Combined with the linear oracle (which
finishes the all-singleton decisions), the `2^d` IR tree collapses
toward the depth-bounded single path.

### 1.2 The boundary (the cascade class)

The oracle certifies **iff the recursion reaches all-singleton
footprints within a polynomial depth bound**:

- **Cascade class** — CFI(H) for **any** `tw(H)` (`theorem_1_HOR_cfi_oddDeg`,
  depth ≤ `tw(H) ≤ n`), schurian scheme graphs
  (`theorem_2_HOR_concrete_rank_two_J_singleton`, depth 1), and their
  compositions (Theorem 3a). Because single-path cost is `O(depth · n²)`
  (§4.6), *unbounded* `tw(H)` is fine — the depth is polynomial in `n`,
  not a branching exponent. The recursion bottoms out; certification
  succeeds. (This is strictly broader than orbit-recovery Corollary 1's
  *"fixed `tw`"* a-posteriori bound — see §4.6.)
- **Off the cascade class** — a rigid IR blind spot
  ([strategy §15 gap 5](./chain-descent-strategy.md)) or the non-abelian
  wall (hidden Johnson). The recursion does not bottom out by the depth
  bound, *or* the mirror-read finds no unique candidate; the budget
  flags. Sound — never a wrong answer.

This is the same boundary as "cell *is* a single orbit, cheaply
certifiable" ([calculator §5](./chain-descent-calculator.md)) and the
same line as the linear oracle's abelian/non-abelian split — the two
oracles share it.

### 1.3 What this doc fixes vs. consolidates

- **Consolidates** (already fixed elsewhere): the `ITransversalOracle`
  contract (§2), the refinement-footprint state (§3, from the linear
  oracle doc), the construction + verification (§4.2, §4.5, from the
  linear oracle doc), the correctness foundation (§3, the orbit-recovery
  theorems).
- **Fixes** (the gap, [calculator §9 item 2](./chain-descent-calculator.md):
  "the cascade oracle's exact certification predicate … is undefined
  design work"): the **certification predicate** as a *bounded-depth
  recursion* over the shared construction (§4.3–§4.4), its termination
  argument (orbit recovery), and the online integration (§6).

### 1.4 Relationship to the linear oracle — one mechanism, two faces

The gather ([prior session]) surfaced that the linear and cascade
oracles are the **same Phase-2 operation**:

> construct a footprint-matching permutation `r_1 ↦ r_j`, verify it
> edge-by-edge, harvest it before branching so `CoveredByPathFixingAut`
> prunes `r_j`.

The difference is *only what the verified permutation turns out to be*:

| | Linear oracle | A-priori cascade oracle |
|---|---|---|
| Cell type | False symmetry (genuine decision) | True symmetry (one orbit) |
| Verified `r_1 ↦ r_j` is | an abelian twist (Z_2 flip) | an orbit map (interchangeable reps) |
| Footprint handled | all-singleton only | all-singleton **+ bounded-depth recursion** to reach it |
| Construction | `TwistConstruction.TryConstruct` | the **same** construction, applied at each recursion level |

So the **all-singleton case is already built** — the linear oracle's
`HarvestTwists` constructs and verifies the footprint map regardless of
whether it is a twist or an orbit map. The genuinely new content of the
a-priori cascade oracle is the **bounded-depth recursion** that resolves
a non-singleton footprint into all-singleton sub-problems, where the
shared construction then applies.

**Design decision to confirm in build (§10):** whether to ship this as
*one unified component* ("a-priori symmetry harvesting" = shared
construction + recursion, the linear oracle being the depth-0 special
case) or as a *separate cascade oracle* that calls the shared
construction. This doc specifies the mechanism; the packaging is
reshapeable.

---

## 2. The firm contract

### 2.1 The seam and the soundness obligation

**[FIRM]** The oracle plugs into `ITransversalOracle`
([ITransversalOracle.cs](../GraphCanonizationProject/ITransversalOracle.cs)),
the same seam as the cascade and (future) linear oracles. Its one
non-negotiable behavioral contract:

> **Soundness.** The returned representatives **must cover every orbit**
> of the target cell. Over-splitting (more than one rep per orbit) is
> sound — it only costs branches. Under-merging (dropping an orbit) is
> fatal — it can skip the lex-min. The oracle may be over-cautious,
> never over-confident.

The a-priori cascade oracle satisfies this by **certifying a merge only
via a verified automorphism** (§4.5): two representatives are declared
the same orbit *only* when an edge-checked automorphism maps one to the
other. An unverifiable candidate ⟹ keep both as separate reps (sound
over-split).

### 2.2 The online nuance — explore-one-then-certify

**[RESHAPEABLE, load-bearing]** The genuine cascade oracle is **online**
([linear-oracle.md §6.1](./chain-descent-linear-oracle.md)): it cannot
certify orbits by a pure pre-branch `Classify`, because the symmetry it
needs is the one refinement missed — it is only visible *after*
exploring one representative and reading the propagation footprint.

So its control flow is **explore `r_1` → read footprint → certify the
rest (possibly via recursion) → harvest before exploring them** — the
*same* control flow as the linear oracle (`HarvestTwists` runs after the
first representative is explored, [ChainDescent.cs ~178-216](../GraphCanonizationProject/ChainDescent.cs#L178)),
**not** the current `CascadeOracle.Classify`-returns-before-any-exploration
shape. The integration (§6) therefore lives in the harness branch loop,
not behind the pre-branch `Classify` seam.

### 2.3 Verification — the only soundness anchor

**[FIRM]** A constructed orbit-map candidate `t` is harvested **only
after** `IsAutomorphism(t)` passes — the O(n²) edge-by-edge check
([ChainDescent.cs ~331](../GraphCanonizationProject/ChainDescent.cs#L331)).
The spine / mirror gives the *candidate*; it does **not** give that `t`
is an automorphism. Verification is mandatory and non-negotiable;
everything upstream (construction, recursion) may be heuristic because a
wrong candidate simply fails the check and the reps stay separate.

### 2.4 The objective

**[FIRM]** Return one representative per certified orbit, in canonical
order, so the descent's lex-min over branches is unchanged. Coverage
(§2.1) guarantees the lex-min is preserved; the oracle only removes
provably-redundant branches.

### 2.5 What is missing in Lean

**[GAP]** There is no Lean `CascadeOracleSpec`. Only the linear oracle
has a Lean contract (`LinearOracleSpec`/`LeafTwistSpec`/`DirAssignment`,
[ChainDescent.lean §15.8 ~3254-3296](../GraphCanonizationProofs/ChainDescent.lean)).
A parallel `CascadeOracleSpec` would mirror it: given a spine chain and
a target cell, return certified orbit representatives + the generators
witnessing the merges, with a validity predicate analogous to
`LeafTwistSpec`. The correctness foundation (§3) already exists; the
Lean deliverable is the constructive oracle + its discharge (§8.2).

---

## 3. Correctness foundation — why a-priori certification is sound on the cascade class

The orbit-recovery program is precisely the proof that a-priori
certification is **possible** on the cascade class:

- **[FIRM] Tier 1 (CFI)** — `theorem_1_HOR_cfi_oddDeg`
  ([CFI.lean](../GraphCanonizationProofs/ChainDescent/CFI.lean),
  axiom-free): 1-WL after ≤ `tw(H)` fresh-colour individualizations
  recovers `Aut_S`-orbits. So a recursion of depth ≤ `tw(H)` reaches
  all-singleton footprints.
- **[FIRM] Tier 2 (schemes)** — `theorem_2_HOR_concrete_rank_two_J_singleton`
  ([Scheme.lean](../GraphCanonizationProofs/ChainDescent/Scheme.lean)):
  depth 1 suffices.
- **[FIRM] The depth-parametrized core** — `theorem_1_HOR_at_depth`
  ([ChainDescent.lean ~3732](../GraphCanonizationProofs/ChainDescent.lean)):
  `CascadesAt adj P k` ⟹ orbit partition = warm-refine partition at some
  `S` with `|S| ≤ k`. **Its `∃ S` is existential**; the a-priori cascade
  oracle is the *constructive* version — it produces the `S` (the
  recursion's individualization sequence) and the orbit maps.
- **[FIRM] The trivial direction** — `OrbitPartition.subset_warmRefine`:
  orbits ⊆ cells, always. So a certified merge (cells coincide) plus
  this give cells = orbits.

The gap between "orbit recovery exists" (Tier 1/2) and "the oracle
certifies a-priori" is exactly: turn the existential bounded-depth
discretization into a constructive, online, per-level orbit-map harvest.
That is §4.

---

## 4. The certification predicate (the gap)

### 4.1 Input

At a target cell with representatives `[r_1, r_2, …]` and the current
descent state `(adj, P, χ)`:

- **`r_1`'s child partition** — individualize `r_1` below its cellmates,
  warm-refine. **[REUSE]** same as `HarvestTwists` step 1.
- **Refinement footprint `K`** — cells that split between the parent and
  `r_1`'s child partition. **[REUSE]** `RefinementFootprint.Compute`
  ([RefinementFootprint.cs](../GraphCanonizationProject/RefinementFootprint.cs)),
  with `AllSingletons` gate and `CoupledVertices()`.

By the spine fact (`warm_6_2` for size-2, `warmRefine_agree_off'` for
size-`k`), the partition under any other representative `r_j` is the
`r_1 ↔ r_j` mirror of `r_1`'s — so `r_j` is **not re-explored** for the
construction; its structure is known from `r_1`'s.

### 4.2 The orbit-map construction (shared with the linear oracle)

**[REUSE]** When the footprint `K` is all-singleton, the candidate
`t : V → V` carrying `r_1 ↦ r_j` is built by **canonical-id sub-cell
matching** — `TwistConstruction.TryConstruct`
([TwistConstruction.cs](../GraphCanonizationProject/TwistConstruction.cs)),
unchanged:

1. For each split cell `C ∈ K`, match `r_1`'s child sub-cells of `C` to
   `r_j`'s by refined-colour signature; within matched singletons, the
   vertex map is forced.
2. `t` is the resulting map (identity off `K`), **path-fixing** by
   construction.

This is identical to the linear oracle. Whether `t` is an abelian twist
(false symmetry) or an orbit map (true symmetry) is *not decided here* —
it is whatever the forced matching produces, and §4.5 verifies it.

### 4.3 The all-singleton boundary

**[FIRM behavior, CONJECTURAL characterization]** The candidate is forced
(unique) **iff every sub-cell of `K` is a singleton**:

- **All singletons** → forced matching → construct, verify (§4.5),
  harvest.
- **Some sub-cell ≥ 2** → matching ambiguous → **recurse** (§4.4).

The behavior is sound unconditionally. The *characterization* "all
singleton ⟺ orbit cleanly certifiable / non-singleton ⟺ deeper residual"
ties to the orbit-recovery conjecture and is not asserted as proven —
implement the behavior, not the boundary
([linear-oracle.md §4.3](./chain-descent-linear-oracle.md)). The
all-singleton gate itself is **principled, not heuristic**: a
non-singleton sub-cell is refinement-indistinguishable, so it admits **no
iso-invariant within-cell vertex match**
([extended-twist-viability.md §1](./chain-descent-extended-twist-viability.md));
a direct index match would be sound but break flag iso-invariance.

### 4.4 Bounded-depth recursion — the new content

When the footprint is non-singleton, the a-priori cascade oracle does
what the linear oracle cannot: **resolve the residual symmetry by
descending, one representative per level**, instead of falling through to
a-posteriori branching.

```
certify_orbits(cell, depth):           // EXPLORATORY — on copies, not committed
    explore r_1   // ONE representative — individualize, warm-refine → child
    K := refinement_footprint(parent, child)
    if all_singletons(K):
        for each other rep r_j:                        // NOT explored —
            t := construct_orbit_map(K, r_1, r_j)      //   read off r_1's
            if verify_automorphism(t): harvest(t)      //   mirror (spine)
        return one rep per harvested-orbit
    else if depth < depth_bound:
        C := iso_invariant_nonsingleton_subcell(K)
        certify_orbits(C, depth + 1)                   // recurse on ONE
                                                       //   sub-cell rep only
        retry construct/verify/harvest on refined K    // C now singletons
    else:
        return all reps unmerged    // give up a-priori → over-split (sound);
                                    //   harness branches; budget flags if it stacks
```

> **⚠ Single-path is the whole point — it must NOT branch over
> representatives.** At every level the oracle explores **exactly one**
> representative (`r_1`, then one rep of `C`, …) and reads all cellmates
> off that branch's **mirror** (the spine fact, §4.1). It descends a
> *single path* of length ≤ `depth_bound`, never a tree. This is what
> makes the cost a **sum** `O(depth · n²)`, not a **product**
> `cell_size^depth`. See §4.6 — a branching recursion would be
> exponential in depth and is exactly the thing this oracle exists to
> replace.

**Termination and the flag.** Each recursion level individualizes one
more vertex, so the recursion *always* bottoms out at discreteness
within ≤ `n` levels — termination is never the issue. `depth_bound` is
the **give-up cutoff**, not a termination bound: on the cascade class,
orbit recovery (§3) makes footprints all-singleton within ≤ `tw(H)` (CFI)
or 1 (schemes) levels, so certification succeeds well before the cutoff.
Off the cascade class, the cutoff is reached with the footprint still
non-singleton (or the forced candidate fails verification); the oracle
then **returns the reps unmerged (over-split)** and the harness branches
on them. The recursion itself never flags — the flag is **downstream**,
from the budget when those real branches stack (§6.4). The recursion is
**exploratory** (run on copies to read footprints and harvest verified
generators), so its single-path cost is separate from, and does not
itself drive, the harness's branching.

**Why one representative suffices (the mirror-read).** The oracle does
*not* explore the cellmates `r_2, …, r_k` or the sub-cell's other
vertices. By the spine fact, individualizing `r_1` vs. `r_j` gives
*mirror* partitions, so the generator carrying `r_1 ↦ r_j` is read off
`r_1`'s single branch and verified — without exploring `r_j`'s subtree.
Orbit recovery (§3) guarantees that, on the cascade class, *all* the
orbit generators are visible this way, so single-path discovers a
complete generating set. The a-posteriori descent, by contrast,
explores every `r_j` and harvests from leaf collisions — that is the
`cell_size^depth` product (orbit-recovery Corollary 1) the a-priori
oracle replaces.

**Iso-invariance of the recursion.** Picking the non-singleton sub-cell
`C` must be a function of iso-invariant cell ids (`WarmPartition.CellOf`).
The explored rep `c_1` need *not* be canonical, because the **mirror-read
covers every cellmate** regardless of which `c_1` is chosen: a different
`c_1` yields a different generating *set* but the **same generated
group** (the orbit of `C`), and the verdict (canonical form / flag)
depends only on the group, not the chosen generators. So the choice of
`c_1` does not bias the verdict — *not* because the descent branches over
the whole sub-cell (single-path does not), but because the mirror-read is
choice-symmetric. The remaining obligation — that the harvested *group*,
hence the verdict, is a function of iso-invariant ids — is the §10
flag-iso-invariance obligation, **undischarged**.

> **This recursion is literally "orbit recovery applied to the
> sub-cell"** ([linear-oracle.md §4.4](./chain-descent-linear-oracle.md)),
> and it is what makes the a-priori cascade oracle the constructive form
> of `theorem_1_HOR_at_depth`'s existential `∃ S`.

### 4.5 Verification protocol

**[FIRM]** Identical to the linear oracle ([linear-oracle.md §4.5](./chain-descent-linear-oracle.md)):
check `adj(t(u), t(v)) = adj(u, v)` for all pairs, O(n²). Only verified
maps are harvested; a failure means the reps stay separate (sound
over-split). Verification is the sole soundness anchor — the recursion
and construction may be heuristic.

### 4.6 Polynomial bound — single-path vs. branching (the crux)

This is the load-bearing complexity argument, and the whole design
hinges on it. There are two ways the recursion could run:

- **Branching** — explore `b` representatives per level, `d` levels →
  **`b^d` nodes**. Exponential in depth. With `d = tw(H)` (graph-
  dependent, unbounded), this is super-polynomial. **This is exactly
  the a-posteriori descent**: orbit-recovery Corollary 1 bounds it as
  `cell_size^{tw(H)}`, which is why that corollary needs the *"for fixed
  `tw(H)`"* qualifier.
- **Single-path** (§4.4) — explore **one** representative per level,
  read cellmates off the mirror, `d` levels → **`O(d · n²)`**. Per
  level: footprint diff O(n²) + construction O(n²) + verify O(n²). With
  `d ≤ depth_bound ≤ tw(H) ≤ n`, the total per descent path is
  **`O(n³)`** — polynomial for **any** polynomial depth, including
  *unbounded* `tw(H)`.

**The depth bound is not a complexity bottleneck for single-path.**
Because the cost is `d · n²` (a sum), any polynomial `d` is fine — the
trivial `d = n` gives `O(n³)`. The tight `tw(H)` bound is a smaller
constant, not a requirement for polynomiality. (Contrast branching,
where only *constant* `d` is polynomial — which is why the a-posteriori
Corollary 1 is restricted to fixed `tw`.)

**So the a-priori cascade oracle, *if single-path is effective*, removes
Corollary 1's fixed-`tw` restriction**: it would canonize all CFI —
including unbounded-treewidth bases — in polynomial time, by replacing
the `cell_size^{tw}` product with a `tw · n²` sum. That strengthening
*is* the deliverable.

**The open question is effectiveness, not soundness.** Single-path is
sound regardless: if it misses a generator it over-splits (more reps
than orbits — the safe direction), never over-merges. Whether the
mirror-read finds a *complete* generating set without branching (so the
descent fully collapses) is guaranteed by orbit recovery *on the
cascade class* (§3) and is the empirical question the build's leaf-
collapse bar (§8.1 M5) answers. The all-singleton case is already
demonstrated single-path (the linear oracle harvested 941 K7 twists
a-priori, 0 branching at those nodes); the unproven part is the
non-singleton recursion.

---

## 5. Worked example — CFI(K7) non-singleton footprint (the starvation case)

The measured starvation case ([linear-oracle.md §8.1](./chain-descent-linear-oracle.md)):
CFI(K7), β=15, the linear oracle harvests 941 twists at all-singleton
footprints but 555 nodes branch at non-singleton footprints.

Take one such node:

1. Target cell, individualize `r_1`, warm-refine. The footprint `K` has
   a sub-cell `C` with `|C| = 2` (two gadget vertices 1-WL cannot
   separate even after this decision — residual symmetry).
2. **Linear oracle today:** `AllSingletons(K)` is false → no twist
   constructed → fall through to a-posteriori `k`-way branch. (One of
   the 940 extra reps.)
3. **A-priori cascade oracle:** recurse into `C` — individualize one
   vertex `c_1 ∈ C`, warm-refine. By `theorem_1_HOR_cfi_oddDeg`, this
   further splits the gadget structure; within ≤ `tw(K7) = 6` levels
   the footprint discretizes.
4. At the all-singleton level, construct the orbit map `r_1 ↦ r_j` for
   each unexplored `r_j` (shared construction), verify edge-by-edge,
   harvest. The CFI parity automorphisms pass verification.
5. Harvested generators flow into the `PermutationGroup`;
   `CoveredByPathFixingAut` prunes the `r_j` the node would otherwise
   have branched on.

Effect: the 555 non-singleton branching nodes are resolved a-priori by
bounded-depth recursion; the footprints feed clean into the harvest;
the K7 leaf count collapses from 941 toward the depth-bounded path.
This is the measured-bottleneck → fix correspondence.

---

## 6. Interface and online behavior

### 6.1 The seam

**[RESHAPEABLE]** Because the oracle is online (§2.2), it lives in the
harness branch loop, not behind the pre-branch `Classify`. Recommended:
extend the existing `HarvestTwists` placement
([ChainDescent.cs ~178](../GraphCanonizationProject/ChainDescent.cs#L178))
— after exploring `r_1`, before the loop reaches unexplored reps — to
run the bounded-depth recursion when the footprint is non-singleton.
This is the unification packaging (§1.4): one harvest entry point,
all-singleton handled directly, non-singleton handled by recursion.

### 6.2 The explore-certify-recurse-prune loop

```
on target cell [r_1, r_2, …] at a node, depth d:
    explore r_1 (individualize below cellmates, warm-refine → child)
    K := refinement_footprint(parent, child)
    if all_singletons(K):
        for each unexplored r_j:
            t := construct_orbit_map(K, r_1, r_j)        // §4.2 (shared)
            if verify_automorphism(t): AddGenerator(t)   // §4.5
    else if d < depth_bound:
        C := iso_invariant_nonsingleton_subcell(K)       // §4.4
        certify_orbits(C, d + 1)                          // recurse
        retry harvest on the refined footprint
    else:
        // residual not resolved within the bound: off cascade class
        fall through to k-way branch (budget will flag if it stacks)
    // existing CoveredByPathFixingAut now skips covered reps
```

The harvested generators fold into the same `PermutationGroup` the
cascade oracle's a-posteriori pruning and the linear oracle already
consume — so downstream nothing changes.

### 6.3 Interaction with the linear oracle

The two oracles are the same harvest mechanism (§1.4). Operationally:
the cascade recursion **resolves residual symmetry** so footprints
become all-singleton; the shared construction then **harvests the maps**
(orbit maps and abelian twists alike). There is no ordering hazard
(Tier 3 sub-claim 3 / [tier3-decomposability §7](./chain-descent-tier3-decomposability.md)):
the cascade oracle's failure mode is the same graceful k-way branch, so
the two compose by simply alternating until both run out of progress.

### 6.4 Failure → graceful degradation

**[FIRM]** If the recursion exceeds the orbit-recovery depth bound
without reaching all-singleton footprints (off the cascade class), the
oracle returns the cell's reps unmerged (sound over-split) and the
harness proceeds as budget-bounded IR search. A stacked exponential is
caught by the budget as a flag — never a wrong answer
([tier3-decomposability §7](./chain-descent-tier3-decomposability.md)).

---

## 7. Soundness

The merge of two representatives into one orbit is sound because of the
verified automorphism (§4.5), exactly as for the linear oracle:

1. `t ∈ Aut(G)` (verified edge-by-edge).
2. `t` is path-fixing and carries `r_1 ↦ r_j` (construction, §4.2).
3. So branch-`r_1` and branch-`r_j` reach the same canonical form modulo
   `t`; pruning `r_j` cannot miss the lex-min.

Soundness rests **only** on verification — not on the spine, the
footprint, or the recursion, all of which produce candidates that
verification gates. The coverage half (§2.1) is preserved because an
unverifiable candidate leaves the reps separate (over-split, never
under-merge).

---

## 8. Implementation plan

> A harness-grounded, milestone-by-milestone build order — tagged by
> proof-defensibility (which milestones produce proof-backed artifacts
> vs. empirical-only de-risking) — is in
> [`chain-descent-cascade-oracle-build-brief.md`](./chain-descent-cascade-oracle-build-brief.md)
> (temporary, delete after build). The summary below is the spec-level
> version.

### 8.1 C# (empirical first)

Building on the linear oracle's shipped pieces (`RefinementFootprint`,
`TwistConstruction`, `HarvestTwists`, `CoveredByPathFixingAut`):

1. **Orbit-map harvest = the existing all-singleton harvest.** Confirm
   `HarvestTwists` already certifies true-symmetry orbit maps (it
   constructs+verifies the footprint map regardless of type). Likely
   ~0 new lines — validate it harvests orbit maps, not just twists. M1.
2. **Bounded-depth recursion.** The new content (§4.4): when
   `AllSingletons(K)` is false, descend one level into an
   iso-invariantly-chosen non-singleton sub-cell, re-refine, re-attempt.
   Track recursion depth against `depth_bound`. ~200-300 lines.
   M2.
3. **Iso-invariant sub-cell selection.** Choose `C` by canonical
   `CellOf` id; `c_1` need not be canonical (mirror-read is
   choice-symmetric, §4.4). Reuse the harness's iso-invariant
   target-cell logic. M3.
4. **Depth-bound + flag.** Wire `depth_bound` (start with a
   generous `n`; tighten to `tw(H)` when the CFI base is identifiable);
   flag past the bound. M4.
5. **Empirical bar (M5).** CFI(K4…K7): non-singleton footprints resolve
   a-priori; leaf count collapses from the linear-oracle baseline
   (K7: 941) toward the depth-bounded path (~`O(β)`). Correctness/|Aut|/
   Even≠Odd preserved throughout.

### 8.2 Lean (contract discharge)

1. **`CascadeOracleSpec`** — a Lean type parallel to `LinearOracleSpec`:
   given a spine chain + target cell, return certified orbit reps +
   witnessing generators. ~400 lines.
2. **Validity predicate** — analogue of `LeafTwistSpec`: each merge is
   witnessed by a verified automorphism mapping rep to rep. ~300 lines.
3. **Constructive discharge from `theorem_1_HOR_at_depth`** — turn the
   existential `∃ S` into the recursion's constructive `S`, scoped to
   the cascade class (CFI OddDegree, rank-≤2 schemes). The recursion's
   termination is `theorem_1_HOR_cfi_oddDeg` /
   `theorem_2_HOR_concrete_rank_two_J_singleton`. ~1000-1500 lines.

### 8.3 Order

C# first (empirical: does the recursion collapse the K7 leaves?), then
Lean. The C# build will confirm whether bounded-depth recursion is the
right mechanism before the Lean effort is committed — exactly the
de-risking path the linear oracle followed.

---

## 9. Constraint status — firm / reshapeable / historical

| Constraint | Status | Note |
|---|---|---|
| `ITransversalOracle` seam | **Firm** | The oracle plugs in here; online behavior needs harness-loop placement (§6.1), not pre-branch `Classify`. |
| Soundness: cover every orbit (over-split OK, under-merge fatal) | **Firm** | `ITransversalOracle` contract; satisfied by verify-before-merge. |
| Edge-by-edge verification (§4.5) | **Firm** | The sole soundness anchor; mandatory. Everything upstream may be heuristic. |
| Orbit-map construction (§4.2) | **Reshapeable (heuristic)** | The *same* code as `TwistConstruction`; sound via verification. C# validates effectiveness. |
| Bounded-depth recursion (§4.4) | **Reshapeable (the new content)** | Termination from orbit recovery; depth bound `tw(H)` / 1. The genuine design contribution. |
| Recursion termination on cascade class | **Firm (foundation)** | `theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_concrete_rank_two_J_singleton`, `theorem_1_HOR_at_depth`. |
| Refinement footprint = coupled component (§4.1) | **Firm** | Parent↔child partition diff. Reused from the linear oracle; TC provenance is inert (below). |
| All-singleton gate principled (no iso-invariant match in non-singleton sub-cell) | **Firm** | [extended-twist-viability.md §1](./chain-descent-extended-twist-viability.md); forces recursion over index-match. |
| Path-fixing pruning | **Firm** | Only path-fixing automorphisms may prune (`CoveredByPathFixingAut`). |
| Iso-invariant target-cell + sub-cell selection | **Firm** | Canonical `CellOf` ids. Explored rep need not be canonical (mirror-read choice-symmetric, §4.4). |
| Flag iso-invariance of certification (§4.4, §10) | **Firm obligation, UNDISCHARGED** | [strategy §15 gap 2](./chain-descent-strategy.md); online discovery must be a function of iso-invariant ids. |
| Budget / soundness handshake | **Firm** | [strategy §15 gap 1](./chain-descent-strategy.md); interrupt mid-certification ⟹ flag, never partial unsound. |
| Bounded work or flag | **Firm** | [strategy §5](./chain-descent-strategy.md). |
| Unification (one component vs. separate cascade oracle) | **Reshapeable** | §1.4; the build decides packaging. |
| `depth_bound` value | **Reshapeable** | Start `n`; tighten to `tw(H)` when CFI base identifiable. |
| Lean `CascadeOracleSpec` | **Not yet built** | §2.5, §8.2; parallel to `LinearOracleSpec`. |
| TC provenance (`DERIVED`/`driver`, invariant 6.4) | **Historical / not on critical path** | Inert for within-cell cascade (measured 0); the footprint is refinement-based. |
| Matroid framing / "Tier-2 detector" | **Historical** | [matroid §8.4](./chain-descent-matroid.md), closed. Certification is a localized cascade check, not a matroid test. |
| Boolean-class certification | **Historical** | [calculator §10.2](./chain-descent-calculator.md), closed. |

---

## 10. Risks and open questions

1. **Recursion effectiveness (§4.4).** The bound is *sound* regardless
   (flag past it), but whether bounded-depth recursion actually collapses
   the CFI(K7) starvation footprints is the empirical question M5
   answers. **Main implementation risk** — the analogue of the linear
   oracle's construction-correctness risk.
2. **Iso-invariance of the recursion (§4.4).** The non-singleton
   sub-cell `C` must be picked by iso-invariant cell id. The explored
   rep `c_1` need not be canonical (the mirror-read is choice-symmetric:
   different `c_1`, same generated group). The undischarged obligation is
   that the harvested *group* — hence the canonical/flag verdict — is a
   function of iso-invariant ids, not the labelling
   ([strategy §15 gap 2](./chain-descent-strategy.md)).
3. **`depth_bound` without identifying the CFI base.** The tight
   bound is `tw(H)`, but the oracle may not know `H` from the graph
   alone. A generous bound (`n`) is always sound (the budget catches
   stacking); tightening is an optimization, not a correctness need.
4. **Unification packaging (§1.4).** One component or two? The build
   should confirm the all-singleton harvest is genuinely identical
   before committing to a unified API.
5. **Unbounded `tw(H)` is NOT a flag (single-path).** Earlier framings
   (and orbit-recovery Corollary 1) treated high-treewidth CFI as
   needing a fixed-`tw` restriction — true for the *branching*
   a-posteriori descent (`cell_size^{tw}`). For *single-path* (§4.6),
   depth `tw(H) ≤ n` is a polynomial *factor*, not an exponent, so
   unbounded-`tw` CFI is `O(n³)` and canonizes — *provided single-path
   is effective* (risk 1). The genuine flag cases are the non-abelian
   wall and IR blind spots, not high treewidth.
6. **Empirical bar is leaf-count collapse, not flag.** Small CFI already
   canonizes ([calculator §9 item 4](./chain-descent-calculator.md)); the
   signal is leaf/node collapse toward the path, the metric the linear
   oracle's M6 set up.

---

## 11. Cross-references

- [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) —
  the shared construct/verify/harvest core (§4) the cascade oracle
  reuses; §8.1 (the starvation finding that motivates this doc).
- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §5
  (cascade oracle prose), §9 item 2 (the certification gap this doc
  closes), §6 (cost model).
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) —
  Tier 1/Tier 2 theorems: the recursion's termination and the
  correctness foundation (§3).
- [`chain-descent-extended-twist-viability.md`](./chain-descent-extended-twist-viability.md) —
  the no-iso-invariant-order obstruction (§4.3) and why recursion (not
  index-match) is the principled non-singleton handling (§4.4).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §5 (oracle
  contract), §12 (spine / `warm_6_2` / `warmRefine_agree_off'`), §15
  (gap 1 budget handshake, gap 2 flag iso-invariance, gap 5 IR blind
  spots).
- [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
  §15.8 (`LinearOracleSpec` to parallel), `CascadesAt`,
  `theorem_1_HOR_at_depth`; [CFI.lean](../GraphCanonizationProofs/ChainDescent/CFI.lean)
  (`theorem_1_HOR_cfi_oddDeg`); [Scheme.lean](../GraphCanonizationProofs/ChainDescent/Scheme.lean)
  (`theorem_2_HOR_concrete_rank_two_J_singleton`).
- [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
  §10.4, [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  §2, §7 — where the a-priori cascade oracle is the next lever and how
  it composes with the linear oracle.
- [`chain-descent-deferred-decisions.md`](./chain-descent-deferred-decisions.md) —
  the scheduling layer to be picked up *after* this oracle: defer real
  decisions, consume symmetry first, hand off the rigid residue whole.
- C#: [ITransversalOracle.cs](../GraphCanonizationProject/ITransversalOracle.cs),
  [CascadeOracle.cs](../GraphCanonizationProject/CascadeOracle.cs),
  [ChainDescent.cs](../GraphCanonizationProject/ChainDescent.cs),
  [RefinementFootprint.cs](../GraphCanonizationProject/RefinementFootprint.cs),
  [TwistConstruction.cs](../GraphCanonizationProject/TwistConstruction.cs).
