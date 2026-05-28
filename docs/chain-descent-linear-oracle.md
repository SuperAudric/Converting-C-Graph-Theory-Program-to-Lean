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

---

## 1. Purpose and scope

### 1.1 What the linear oracle does

A **genuine decision** is a target cell that 1-WL cannot split but the
graph treats as ≥ 2 orbits. The simplest case: a cell `{e, f}` where
individualizing `e` (commit `e < f`) and individualizing `f` (commit
`f < e`) are the two directions of one ordering decision.

The linear oracle's mechanism ([calculator §6](./chain-descent-calculator.md)):

1. **Explore** one branch (commit `e < f`), propagate via warm
   refinement; the propagation forces a chain of derived order
   relations.
2. **Delineate** the *coupled component* — the cells whose splits are
   driven by this decision (read from the provenance record, §3).
3. **Construct** a candidate twist `t : V → V` from the
   reverse-symmetric propagation pattern (§4 — the open piece).
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
  the provenance state (§3), the partition backdrop (the descent
  spine), the lex-min objective.
- **Fixes** (the gap): the candidate-twist construction predicate
  (§4) — input format, the abelian construction, the uniqueness test,
  the verification protocol, the polynomial bound.

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

## 3. Required state — provenance

**Firm-but-reshapeable.** The provenance *content* is required
(invariant 6.4); the exact data structure is an implementation choice.

From [strategy §10](./chain-descent-strategy.md): after a guess writes
a `P` entry, transitive closure derives further entries. Each derived
entry carries:

- a **`DERIVED` record** marking it as closure-derived (not a primary
  guess);
- a **`driver` pointer** — the index of the primary guess whose write
  completed the chain.

**Why required (invariant 6.4).** The coupled component is exactly the
set of derived relations sharing a driver. Without driver tracking, an
`O(n)`-long derived chain all traces to one guess and the component
can't be delineated. At most `n(n−1)` `DERIVED` records exist at once →
polynomial.

**What the oracle reads.** For the current decision's primary guess
`g`:
- the set of `P` entries with `driver = g` (the coupled component's
  edges);
- the cells those entries split (the coupled component's vertices);
- the order labels on each split (the direction-dependent data the
  twist mirrors).

**Reshapeable choices:**
- Whether provenance is stored as per-entry records or as a separate
  driver→entries index (the latter is faster for component lookup).
- Whether the coupled component is computed lazily (on oracle call) or
  maintained incrementally during closure.

---

## 4. The construction predicate (the gap)

This is the unspecified piece ([calculator §9 item 4](./chain-descent-calculator.md):
"turning a propagation pattern into a vertex permutation — the one
genuinely unspecified piece and the main implementation risk").

### 4.1 Input

For the decision pair `(e, f)` with primary guess `g` (commit
`e < f`):
- **Coupled component `K`** — the cells split by relations with
  `driver = g`, read from provenance (§3).
- **The two order-label patterns** — by invariant 6.2 (`warm_6_2`,
  proved), branch-`e` and branch-`f` produce the *same partition* of
  `K`, differing only in order labels. We have branch-`e`'s labels;
  branch-`f`'s are the mirror (we do *not* re-explore branch-`f` —
  that's the point).

### 4.2 The abelian construction

For the abelian case, the candidate twist is determined by
**mirror-matching within each split cell**:

1. For each cell `C` in the coupled component, branch-`e` splits `C`
   into ordered sub-cells `C = C_1 < C_2 < … < C_r` (by the
   direction-dependent order labels).
2. Branch-`f`, by invariant 6.2, splits `C` into the *same* sub-cells
   with *reversed* order: `C_r < C_{r-1} < … < C_1`.
3. The candidate twist `t` maps each sub-cell `C_i` to its mirror
   `C_{r+1−i}`, matching vertices by their position within the
   sub-cell.

For this to define a *permutation* (not just a cell-to-cell map), each
sub-cell `C_i` and its mirror `C_{r+1−i}` must have the **same size**,
and the within-sub-cell matching must be forced. The clean abelian case
is when every sub-cell is a **singleton** — then `t` is the unique
order-reversing involution on `C`, and `e ↦ f` falls out as the `r = 2`
case.

**CFI specialization.** In CFI, `K` is a cycle of the base graph's
cycle space; each gadget on the cycle splits into its two parities; `t`
flips all parities on the cycle. The mirror-matching is forced because
each parity class is a singleton after the decision propagates. This is
the `Z_2` twist, and the construction is exactly "flip the coupled
cycle."

### 4.3 The uniqueness test (the boundary)

The candidate twist is **unique** iff the mirror-matching in §4.2 is
forced — equivalently:

> Every sub-cell `C_i` of every cell in the coupled component is a
> **singleton** (or, weakly: `C_i` and its mirror `C_{r+1−i}` are both
> singletons, with fixed points allowed in the middle).

- **All singletons** → unique involution → abelian (`Z_2`) → **proceed**
  (construct `t`, verify, prune).
- **Some sub-cell has ≥ 2 vertices** → the within-sub-cell matching is
  ambiguous → multiple candidate twists → non-abelian residual →
  **flag**.

This is the precise form of calculator §6's "size of the per-decision
residual symmetry." A sub-cell of size ≥ 2 that the decision cannot
resolve is exactly a hidden non-abelian action on that sub-cell — the
wall.

**Connection to orbit recovery.** "Sub-cells are singletons" is the
statement that the decision, propagated, *cascades to discreteness*
within the coupled component. So the uniqueness test is a localized
cascade check — tying the linear oracle's boundary to the orbit-recovery
program ([orbit-recovery](./chain-descent-orbit-recovery.md)).

### 4.4 General-case design options (open)

When sub-cells are *not* all singletons, the construction is
ambiguous. Three design options, in priority order:

1. **Flag immediately.** Treat any non-singleton sub-cell as the wall.
   Simplest, sound, and correct for the Phase-1 abelian target. Cost:
   may flag some graphs that a smarter construction could handle. This
   is the recommended Phase-1 behavior.
2. **Recurse with more individualizations.** Individualize within the
   ambiguous sub-cell and re-run — effectively pushing the decision
   one level deeper. Sound, but risks the exponential the oracle exists
   to avoid unless the recursion provably terminates polynomially
   (which is the cascade-class question again).
3. **Cross-branch triangulation.** Explore a second branch to
   disambiguate the matching. This is what calculator §6 explicitly
   warns "itself branches — exponential." Out of scope for the abelian
   oracle; would only make sense for a future non-abelian oracle.

**Decision:** Phase 1 ships option 1 (flag on non-singleton sub-cell).
Options 2-3 are recorded for a future non-abelian successor, not built.

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
- Delineate coupled component from provenance: `O(n²)` (scan derived
  records).
- Construct candidate via mirror-matching: `O(n²)` (one pass over the
  component's cells).
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
3. Propagate. The parity choice forces the adjacent gadget's parity,
   which forces the next, around the whole cycle. The provenance: every
   derived parity relation has `driver = g` (the original commit).
4. Coupled component `K` = all gadgets on the cycle. Each splits into
   its two parity classes; each class is a singleton (one parity rep
   per gadget after propagation).
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
on genuine decision {e, f, …} at a node:
    explore branch-e (commit e < f, propagate)
    K        := coupled_component(driver = this_commit)   // from provenance
    if not all_subcells_singleton(K):                     // uniqueness test
        flag (or fall through to k-way branch)
    t        := construct_twist(K)                         // mirror-match
    if not verify_automorphism(t, adj):                    // O(n²) edge check
        fall through to k-way branch
    harvest t into PermutationGroup
    prune all branches coupled to t
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
2. `t` maps branch-`e`'s order assignment to branch-`f`'s (it's the
   mirror-matching, §4.2).
3. So `canonAdj(branch-e)` and `canonAdj(branch-f)` are related by
   `relabelMatrix t` — exactly `LeafTwistSpec`.
4. Hence the lex-min over `{branch-e, branch-f}` is achieved by either;
   pruning branch-`f` cannot miss the minimum.

The soundness rests *only* on the edge-by-edge verification (1) — not
on invariant 6.2, which gives the *candidate* but not its correctness.
This is why verification is mandatory and non-negotiable.

---

## 8. Implementation plan

### 8.1 C# (empirical first)

1. **Provenance plumbing.** Add `DERIVED`/`driver` records to the
   `P`-matrix closure in the harness (if not already present). Index
   by driver for component lookup. ~200 lines.
2. **Coupled-component extraction.** `coupled_component(driver)` from
   provenance. ~100 lines.
3. **Twist construction + uniqueness test.** §4.2 + §4.3. ~200 lines.
4. **Verification.** `O(n²)` edge check (likely already exists in the
   harness's automorphism harvesting). ~50 lines.
5. **Harness integration.** The explore-read-verify-prune loop (§6.2),
   in option-(b) form. ~200 lines.

**Empirical bar.** `CFI(K_4)`, `CFI(K_3,3)`, `CFI(Petersen)`,
`CFI(C_m)` for several `m` — all should canonize *without flagging*
(currently they flag, since only the cascade oracle ships). Node count
should drop from exponential to `O(n · β)`.

### 8.2 Lean (contract discharge)

1. **Model the construction** as a concrete `LinearOracleSpec` instance
   for the abelian case. ~500 lines.
2. **Prove it satisfies `LeafTwistSpec`** — the deliverable §2.3 names
   as missing. Uses `warm_6_2` (partition symmetry) + the verification
   (automorphism). ~1000 lines.
3. **Tie to `canonForm`** — a descent guided by the verified oracle
   reaches the same lex-min as brute force over `DirAssignment`s. The
   descent's high-level correctness theorem (ChainDescent.md §15.8
   "remaining genuine work"). ~1000 lines.

### 8.3 Order

C# first (empirical validation that twist discovery works on CFI),
then Lean (contract discharge). The C# implementation will surface
whether §4.2's mirror-matching is the right construction before the
Lean effort is committed.

---

## 9. Constraint status — firm / reshapeable / historical

| Constraint | Status | Note |
|---|---|---|
| `DirAssignment` input type | **Firm** | Lean §15.8; models branch = order labels on `D` |
| `LinearOracleSpec` interface | **Firm** | Lean §15.8; output bundles `IsAut` proof |
| `LeafTwistSpec` validity | **Firm** | Lean §15.8; the pruning-justification contract |
| `some_isAut` soundness | **Firm** | Automatic from subtype |
| `warm_6_2` (invariant 6.2) | **Firm** | Proved; gives partition symmetry / mirror pattern |
| Descent spine (`warmRefine_agree_off'`) | **Firm** | Proved; single fixed partition backdrop |
| Edge-by-edge verification (§4.5) | **Firm** | Mandatory for soundness |
| Provenance content (invariant 6.4) | **Firm** | Required to delineate coupled component |
| Provenance *data structure* | **Reshapeable** | Per-record vs. driver-indexed; lazy vs. incremental |
| `ITransversalOracle` integration | **Reshapeable** | Online behavior may need interface extension or harness-loop placement (§6.1) |
| Mirror-matching construction (§4.2) | **Reshapeable** | The proposed construction; C# validation will confirm or revise |
| Non-singleton handling (§4.4) | **Reshapeable** | Phase 1 flags; options 2-3 for a future successor |
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

1. **Mirror-matching correctness (§4.2).** The proposed construction is
   correct for CFI (validated by the worked example), but whether it's
   the right construction for *all* abelian cases is unconfirmed. C#
   validation on CFI variants is the first check. **Main implementation
   risk**, as calculator §9 flagged.
2. **Within-sub-cell matching when sub-cells aren't singletons.** §4.4
   option 1 (flag) sidesteps this; a graph with a genuinely abelian
   decision over non-singleton sub-cells (if such exists) would be
   flagged unnecessarily. Whether such graphs exist is open.
3. **Online interface placement (§6.1).** Whether to extend
   `ITransversalOracle` or place the oracle in the harness loop is a
   design decision with correctness implications (the harness must
   still be iso-invariant). Recommended: harness-loop (option b), but
   needs the iso-invariance argument.
4. **Provenance completeness.** Whether the current harness's closure
   already records enough provenance, or needs the §8.1 plumbing, is an
   implementation audit item.
5. **Iso-invariance of twist discovery.** Flag iso-invariance
   ([strategy §15 gap 2](./chain-descent-strategy.md)) requires the
   oracle's traversal and twist-discovery to be deterministic functions
   of iso-invariant cell ids. The construction (§4.2) reads from
   canonical-id-ordered cells, so this should hold by construction —
   but it's a proof obligation.

---

## 11. Cross-references

- [`chain-descent-calculator.md`](./chain-descent-calculator.md) §6 —
  the prose spec this doc makes precise; §9 item 4 (the construction
  gap).
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §10
  (provenance / closure-as-guess), §12 (`warm_6_2` + spine), §15
  (flag iso-invariance obligation).
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
